import OptimalQLS.TransducerCompiler.BinaryClock.Gates
import Mathlib.Tactic

/-! # Physical-wire injection for reversible primitive programs -/
namespace OptimalQLS.PolynomialTransform.DirtyAncilla
open OptimalQLS.TransducerCompiler.BinaryClock
variable {ι κ : Type*} [DecidableEq ι] [DecidableEq κ]

def mapGate (f : ι → κ) (hf : Function.Injective f) : Gate ι → Gate κ
  | .x t => .x (f t)
  | .cx c t h => .cx (f c) (f t) (fun he => h (hf he))
  | .ccx c d t hc hd => .ccx (f c) (f d) (f t) (fun he => hc (hf he)) (fun he => hd (hf he))

def mapProgram (f : ι → κ) (hf : Function.Injective f) (c : Program ι) : Program κ :=
  c.map (mapGate f hf)

theorem mapGate_pullback (f : ι → κ) (hf : Function.Injective f) (g : Gate ι) (b : κ → Bool) :
    (mapGate f hf g).act b ∘ f=g.act (b ∘ f) := by
  cases g <;> ext i <;> simp [mapGate,Gate.act,Function.comp_def,Function.update_apply,hf.eq_iff]

theorem mapProgram_pullback (f : ι → κ) (hf : Function.Injective f) (c : Program ι) (b : κ → Bool) :
    run (mapProgram f hf c) b ∘ f=run c (b ∘ f) := by
  induction c generalizing b with
  | nil => rfl
  | cons g c ih =>
    simp only [mapProgram,List.map_cons,run_cons]
    change run (mapProgram f hf c) ((mapGate f hf g).act b) ∘ f=run c (g.act (b ∘ f))
    rw [ih,mapGate_pullback]

theorem mapGate_outside (f : ι → κ) (hf : Function.Injective f) (g : Gate ι) (b : κ → Bool)
    (j : κ) (hj : j ∉ Set.range f) : (mapGate f hf g).act b j=b j := by
  have hn : ∀ i, j ≠ f i := by intro i hi; exact hj ⟨i,hi.symm⟩
  cases g <;> simp [mapGate,Gate.act,Function.update_apply,hn]

theorem mapProgram_outside (f : ι → κ) (hf : Function.Injective f) (c : Program ι) (b : κ → Bool)
    (j : κ) (hj : j ∉ Set.range f) : run (mapProgram f hf c) b j=b j := by
  induction c generalizing b with
  | nil => rfl
  | cons g c ih =>
    simp only [mapProgram,List.map_cons,run_cons]
    change run (mapProgram f hf c) ((mapGate f hf g).act b) j=b j
    rw [ih,mapGate_outside f hf g b j hj]

/-- The exact one-target action survives a physical wire injection; every
spectator wire is untouched, not merely restored on a chosen input. -/
theorem mapProgram_target (f : ι → κ) (hf : Function.Injective f) (c : Program ι)
    (t : ι) (action : (ι → Bool) → Bool)
    (hc : ∀ b, run c b=Function.update b t (action b)) (b : κ → Bool) :
    run (mapProgram f hf c) b=Function.update b (f t) (action (b ∘ f)) := by
  ext j
  by_cases hj : j ∈ Set.range f
  · obtain ⟨i,rfl⟩ := hj
    have h := congrFun (mapProgram_pullback f hf c b) i
    rw [hc] at h
    simpa [Function.comp_def,Function.update_apply,hf.eq_iff] using h
  · rw [mapProgram_outside f hf c b j hj]
    have hn : j ≠ f t := fun h => hj ⟨t,h.symm⟩
    simp [Function.update_apply,hn]

@[simp] theorem mapProgram_length (f : ι → κ) (hf : Function.Injective f) (c : Program ι) :
    (mapProgram f hf c).length=c.length := List.length_map ..

end OptimalQLS.PolynomialTransform.DirtyAncilla
