#!/usr/bin/env python3
"""Download and verify the exact arXiv source used for the correspondence review."""
import hashlib
import json
from pathlib import Path
import urllib.request

root = Path(__file__).resolve().parent.parent
source = json.loads((root / 'docs/paper-source.json').read_text())
target = root / '.lake/paper/source.tar'
target.parent.mkdir(parents=True, exist_ok=True)
data = urllib.request.urlopen(source['source_url'], timeout=60).read()
if hashlib.sha256(data).hexdigest() != source['source_sha256']:
    raise SystemExit('Source checksum mismatch; refusing to accept a different paper version.')
target.write_bytes(data)
print(f'Verified {source["arxiv_id"]}: {target}')
