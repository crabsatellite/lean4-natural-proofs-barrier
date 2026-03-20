/-
Shannon counting: most Boolean functions require large circuits.
-/
import CircuitComplexity.Circuit
import Mathlib.Data.Set.Finite.Basic
import Mathlib.Data.Set.Finite.Range
import Mathlib.Data.Finite.Prod

namespace CircuitComplexity

/-- Circuits of bounded size form a finite set. -/
theorem finite_bounded_circuit (n s : ℕ) :
    Set.Finite {c : Circuit n | c.size ≤ s} := by
  induction s with
  | zero =>
    apply ((Set.finite_range (Circuit.var (n := n))).union
           (Set.finite_range (Circuit.const (n := n)))).subset
    intro c hc
    cases c with
    | var i => exact Or.inl ⟨i, rfl⟩
    | const b => exact Or.inr ⟨b, rfl⟩
    | and _ _ => simp [Circuit.size] at hc
    | or _ _ => simp [Circuit.size] at hc
    | not _ => simp [Circuit.size] at hc
  | succ s ih =>
    apply ((ih.union ((ih.prod ih).image fun p : Circuit n × Circuit n =>
              Circuit.and p.1 p.2)).union
           (((ih.prod ih).image fun p : Circuit n × Circuit n =>
              Circuit.or p.1 p.2).union (ih.image Circuit.not))).subset
    intro c hc
    cases c with
    | var _ =>
      left; left
      show (Circuit.var _).size ≤ s
      simp [Circuit.size]
    | const _ =>
      left; left
      show (Circuit.const _).size ≤ s
      simp [Circuit.size]
    | and c₁ c₂ =>
      change c₁.size + c₂.size + 1 ≤ s + 1 at hc
      left; right
      refine ⟨⟨c₁, c₂⟩, ⟨?_, ?_⟩, rfl⟩
      · show c₁.size ≤ s; omega
      · show c₂.size ≤ s; omega
    | or c₁ c₂ =>
      change c₁.size + c₂.size + 1 ≤ s + 1 at hc
      right; left
      refine ⟨⟨c₁, c₂⟩, ⟨?_, ?_⟩, rfl⟩
      · show c₁.size ≤ s; omega
      · show c₂.size ≤ s; omega
    | not c =>
      change c.size + 1 ≤ s + 1 at hc
      right; right
      refine ⟨c, ?_, rfl⟩
      show c.size ≤ s; omega

/-- Functions computable by bounded-size circuits form a finite set. -/
theorem finite_computable_bounded (n s : ℕ) :
    Set.Finite {f : BoolFn n | ∃ c : Circuit n, c.computes f ∧ c.size ≤ s} :=
  ((finite_bounded_circuit n s).image fun c : Circuit n => c.eval).subset
    fun _ ⟨c, hcomp, hsize⟩ => ⟨c, hsize, funext hcomp⟩

/-- Shannon counting: if bounded-size circuits compute fewer functions than exist,
    some function requires large circuits. -/
theorem exists_hard_function {n s : ℕ}
    (hcard : (finite_computable_bounded n s).toFinset.card < Fintype.card (BoolFn n)) :
    ∃ f : BoolFn n, ∀ c : Circuit n, c.computes f → s < c.size := by
  by_contra hall
  push_neg at hall
  have hsub : Finset.univ ⊆ (finite_computable_bounded n s).toFinset := by
    intro f _
    rw [Set.Finite.mem_toFinset]
    exact hall f
  have h := Finset.card_le_card hsub
  rw [Finset.card_univ] at h
  omega

end CircuitComplexity
