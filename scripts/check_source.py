#!/usr/bin/env python3
"""Check release structure and source hygiene; Lean performs the actual proof audit."""
import argparse
import hashlib
import json
import re
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent


def lean_code(text):
    """Discard nested Lean comments and string literals before token checks."""
    out, i, depth = [], 0, 0
    while i < len(text):
        if text.startswith('/-', i):
            depth += 1
            out.append(' ')
            i += 2
        elif depth and text.startswith('-/', i):
            depth -= 1
            i += 2
        elif depth:
            out.append('\n' if text[i] == '\n' else ' ')
            i += 1
        elif text.startswith('--', i):
            end = text.find('\n', i)
            i = len(text) if end < 0 else end
        elif text[i] == '"':
            out.append(' ')
            i += 1
            while i < len(text):
                if text[i] == '\\':
                    i += 2
                elif text[i] == '"':
                    i += 1
                    break
                else:
                    i += 1
        else:
            out.append(text[i])
            i += 1
    if depth:
        raise ValueError('Unterminated Lean comment')
    return ''.join(out)


def source_digest():
    """Hash release files, excluding the self-referential recorded run."""
    paths = [ROOT / name for name in (
        '.gitignore', 'README.md', 'LICENSE', 'NOTICE', 'CITATION.cff',
        'lakefile.toml', 'lake-manifest.json', 'lean-toolchain', 'OptimalQLS.lean')]
    for directory in ('OptimalQLS', 'Verification', 'vendor', 'scripts', 'docs', '.github'):
        paths.extend(path for path in (ROOT / directory).rglob('*')
                     if path.is_file() and '__pycache__' not in path.parts
                     and path != ROOT / 'docs/verification.json')
    inventory = dict(sorted(
        (path.relative_to(ROOT).as_posix(), hashlib.sha256(path.read_bytes()).hexdigest())
        for path in paths))
    payload = ''.join(f'{name}\0{value}\n' for name, value in inventory.items())
    digest = hashlib.sha256(payload.encode()).hexdigest()
    output = ROOT / '.lake/verification'
    output.mkdir(parents=True, exist_ok=True)
    (output / 'source-files.json').write_text(json.dumps(inventory, indent=2) + '\n')
    return digest, len(inventory)


def inspect(check_audit=False):
    files = [ROOT / 'OptimalQLS.lean']
    files += sorted((ROOT / 'OptimalQLS').rglob('*.lean'))
    vendor = ROOT / 'vendor/first-paper'
    files += sorted((vendor / 'QuantumChannelStein').rglob('*.lean'))
    files += sorted((ROOT / 'Verification').glob('*.lean'))
    modules, errors = {}, []
    for path in files:
        relative = path.relative_to(vendor if path.is_relative_to(vendor) else ROOT)
        module = '.'.join(relative.with_suffix('').parts)
        code = lean_code(path.read_text())
        modules[module] = (path, code)
        forbidden = r'\b(sorry|admit|axiom|unsafe|native_decide|implemented_by)\b'
        if module == 'Verification.Challenge':
            if len(re.findall(r'\bsorry\b', code)) != 4:
                errors.append('Challenge must have exactly four explicit proof placeholders')
            forbidden = r'\b(admit|axiom|unsafe|native_decide|implemented_by)\b'
        if re.search(forbidden, code):
            errors.append(f'Forbidden proof token in {relative}')
        if re.search(r'\b(debug\.skipKernelTC|trustLevel)\b', code):
            errors.append(f'Forbidden trust setting in {relative}')
        if module != 'Verification.Audit' and re.search(r'\b(run_cmd|initialize|elab_rules|macro_rules)\b', code):
            errors.append(f'Unexpected metaprogramming in {relative}')
        if re.search('[\u3400-\u9fff]', path.read_text()):
            errors.append(f'Non-English prose in {relative}')

    def closure(module, seen=None):
        seen = set() if seen is None else seen
        if module in seen or module not in modules:
            return seen
        seen.add(module)
        for line in re.findall(r'^import (.+)$', modules[module][1], re.M):
            for dep in line.split():
                closure(dep, seen)
        return seen

    proof_modules = {m for m in modules if m.startswith(('OptimalQLS', 'QuantumChannelStein'))}
    missing = proof_modules - closure('OptimalQLS')
    if missing:
        errors.append(f'Proof modules omitted from public entry point: {sorted(missing)}')
    statement_imports = closure('Verification.Statements')
    for forbidden in ('OptimalQLS.Reduction.Theorem57', 'OptimalQLS.LowerBounds.Physical.Theorem61',
                      'OptimalQLS.PhysicalRobustness.GeneralProgram.Promise', 'Verification.Solution',
                      'Verification.Challenge'):
        if forbidden in statement_imports:
            errors.append(f'Specification imports its endpoint proof: {forbidden}')
    if 'Verification.Challenge' in closure('Verification.Solution'):
        errors.append('Solution imports trusted challenge')

    records = json.loads((ROOT / 'docs/paper-map.json').read_text())
    if len(records) != 36 or len({r['number'] for r in records}) != 36:
        errors.append('Expected exactly 36 distinct numbered paper items')
    substantive = [r for r in records if r['kind'] in ('lemma', 'proposition', 'theorem')
                   and r['number'] not in ('1.1', '1.2')]
    if len(substantive) != 29:
        errors.append('Expected exactly 29 substantive proof statements')
    for record in records:
        for reference in record['references']:
            file, _, name = reference.partition(':')
            path = ROOT / file
            if not path.is_file():
                errors.append(f'Missing reference: {reference}')
                continue
            if name and not re.search(r'\b(?:theorem|def|abbrev|structure)\s+' + re.escape(name) +
                                      r'(?=[\s.{(:])', lean_code(path.read_text())):
                errors.append(f'Missing declaration: {reference}')
    provenance = json.loads((vendor / 'PROVENANCE.json').read_text())
    for name, expected in provenance['source_files'].items():
        if hashlib.sha256((vendor / name).read_bytes()).hexdigest() != expected:
            errors.append(f'Vendored source differs from provenance: {name}')
    if check_audit:
        report = json.loads((ROOT / '.lake/verification/axioms.json').read_text())
        expected = closure('Verification.Solution')
        actual = set(report['modules'])
        if actual != expected:
            errors.append(f'Audit module coverage mismatch: missing={sorted(expected - actual)}, '
                          f'unexpected={sorted(actual - expected)}')
    if errors:
        raise SystemExit('\n'.join(errors))
    print(f'SOURCE_CHECK_PASS proof_modules={len(proof_modules)} paper_items=36 substantive_results=29')
    if check_audit:
        print(f'AUDIT_COVERAGE_PASS modules={len(expected)}')
    digest, count = source_digest()
    print(f'SOURCE_DIGEST sha256={digest} files={count}')


if __name__ == '__main__':
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument('--check-audit', action='store_true',
                        help='also match the generated axiom report to the full import closure')
    inspect(parser.parse_args().check_audit)
