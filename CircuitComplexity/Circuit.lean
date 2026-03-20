/-
Boolean circuits over the standard basis {AND, OR, NOT}.
Evaluation, gate count, and depth.
-/
import CircuitComplexity.Basic
import Mathlib.Data.Fin.VecNotation

namespace CircuitComplexity

/-- Boolean circuit with `n` input variables.
    Tree representation; DAG sharing is structural. -/
inductive Circuit (n : ℕ) where
  | var   : Fin n → Circuit n
  | const : Bool → Circuit n
  | and   : Circuit n → Circuit n → Circuit n
  | or    : Circuit n → Circuit n → Circuit n
  | not   : Circuit n → Circuit n
  deriving Inhabited

variable {n : ℕ}

/-- Evaluate a circuit on an input assignment. -/
def Circuit.eval : Circuit n → (Fin n → Bool) → Bool
  | .var i,      x => x i
  | .const b,    _ => b
  | .and c₁ c₂, x => c₁.eval x && c₂.eval x
  | .or c₁ c₂,  x => c₁.eval x || c₂.eval x
  | .not c,      x => !(c.eval x)

/-- Gate count. Inputs and constants contribute 0. -/
def Circuit.size : Circuit n → ℕ
  | .var _       => 0
  | .const _     => 0
  | .and c₁ c₂  => c₁.size + c₂.size + 1
  | .or c₁ c₂   => c₁.size + c₂.size + 1
  | .not c       => c.size + 1

/-- Depth: longest root-to-leaf path through gates. -/
def Circuit.depth : Circuit n → ℕ
  | .var _       => 0
  | .const _     => 0
  | .and c₁ c₂  => max c₁.depth c₂.depth + 1
  | .or c₁ c₂   => max c₁.depth c₂.depth + 1
  | .not c       => c.depth + 1

/-- Reindex circuit variables along a map. -/
def Circuit.mapVars {m : ℕ} (σ : Fin n → Fin m) : Circuit n → Circuit m
  | .var i     => .var (σ i)
  | .const b   => .const b
  | .and c₁ c₂ => .and (c₁.mapVars σ) (c₂.mapVars σ)
  | .or c₁ c₂  => .or (c₁.mapVars σ) (c₂.mapVars σ)
  | .not c     => .not (c.mapVars σ)

/-- Circuit `c` computes `f` when they agree on all inputs. -/
def Circuit.computes (c : Circuit n) (f : BoolFn n) : Prop :=
  ∀ x : Fin n → Bool, c.eval x = f x

/-- NOT is involutive on evaluation. -/
theorem Circuit.eval_not_not (c : Circuit n) (x : Fin n → Bool) :
    (Circuit.not (Circuit.not c)).eval x = c.eval x := by
  simp [eval, Bool.not_not]

theorem Circuit.eval_mapVars {m : ℕ} (σ : Fin n → Fin m) (c : Circuit n)
    (x : Fin m → Bool) : (c.mapVars σ).eval x = c.eval (x ∘ σ) := by
  induction c with
  | var i     => simp [mapVars, eval]
  | const b   => simp [mapVars, eval]
  | and _ _ ih₁ ih₂ => simp [mapVars, eval, ih₁, ih₂]
  | or _ _ ih₁ ih₂  => simp [mapVars, eval, ih₁, ih₂]
  | not _ ih  => simp [mapVars, eval, ih]

/-- Completeness: every Boolean function has a circuit (Shannon decomposition). -/
theorem exists_circuit (f : BoolFn n) : ∃ c : Circuit n, c.computes f := by
  induction n with
  | zero =>
    exact ⟨.const (f Fin.elim0), fun x => by
      simp [Circuit.eval]; congr 1; exact funext fun i => i.elim0⟩
  | succ n ih =>
    obtain ⟨c₀, h₀⟩ := ih (fun x => f (Fin.cons false x))
    obtain ⟨c₁, h₁⟩ := ih (fun x => f (Fin.cons true x))
    refine ⟨.or (.and (.var 0) (c₁.mapVars Fin.succ))
                (.and (.not (.var 0)) (c₀.mapVars Fin.succ)), fun x => ?_⟩
    simp only [Circuit.eval, Circuit.eval_mapVars]
    rw [h₁, h₀]
    have hrecons := Fin.cons_self_tail x
    cases hb : x 0
    · simp; congr 1; rw [hb.symm]; exact hrecons
    · simp; congr 1; rw [hb.symm]; exact hrecons

end CircuitComplexity
