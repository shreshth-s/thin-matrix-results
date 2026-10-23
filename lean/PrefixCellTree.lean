import GraphWindowPermutations

set_option autoImplicit false

/-! Retained ternary coefficient trees. Construction evaluates its input once
per leaf and retains every column. Function denotations are used in proofs;
the data representation consists of nested vectors of binary cells. -/
namespace ThinMatrix.PrefixCellTree
open BinaryCell BinaryGroupedCoordinates BinaryGroupedPreparation CroppedGroupedSuffix
open scoped BigOperators

def Data (C : ℕ) : ℕ → Type
  | 0 => Vector Cell C
  | n+1 => Vector (Data C n) 3

def read {C : ℕ} : {n : ℕ} → Data C n → Word n → Fin C → Cell
  | 0, X, _, c => X.get c
  | _+1, X, w, c => read (X.get (w 0)) (fun i => w i.succ) c

def build {C : ℕ} : (n : ℕ) → (Word n → Run (Vector Cell C)) → Run (Data C n)
  | 0, f => let out := f (fun i => Fin.elim0 i); ⟨out.value,out.bitSteps,out.control+8⟩
  | n+1, f =>
      let out := tabulate (Vector.replicate 3 ()) (fun a => build n (fun w => f (Fin.cons a w)))
      ⟨out.value,out.bitSteps,out.control+8⟩

theorem build_read {C n : ℕ} (f : Word n → Run (Vector Cell C)) (w : Word n) (c : Fin C) :
    read (build n f).value w c=(f w).value.get c := by
  induction n with
  | zero =>
    have h : (fun i : Fin 0 => (Fin.elim0 i : Fin 3))=w := Subsingleton.elim _ _
    simp only [build,read,h]
  | succ n ih =>
    simp only [build,read,tabulate_get,ih]
    congr 3
    exact Fin.cons_self_tail w

theorem build_bits {C n B : ℕ} (f : Word n → Run (Vector Cell C)) (hf : ∀ w, (f w).bitSteps≤B) :
    (build n f).bitSteps≤3^n*B := by
  induction n with
  | zero => simpa [build] using hf (fun i => Fin.elim0 i)
  | succ n ih =>
    have h := tabulate_bits (Vector.replicate 3 ()) (fun a => build n (fun w => f (Fin.cons a w)))
      (fun a => ih _ (fun w => hf (Fin.cons a w)))
    simpa only [build,pow_succ,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using h

theorem build_control {C n W : ℕ} (f : Word n → Run (Vector Cell C)) (hf : ∀ w, (f w).control≤W) :
    (build n f).control≤3^n*(W+200*(n+1)) := by
  induction n with
  | zero => have h := hf (fun i => Fin.elim0 i); simp only [build,pow_zero,one_mul]; omega
  | succ n ih =>
    have h := tabulate_control (Vector.replicate 3 ()) (fun a => build n (fun w => f (Fin.cons a w)))
      (fun a => ih _ (fun w => hf (Fin.cons a w)))
    have hp : 0<(3:ℕ)^n := pow_pos (by decide) _
    simp only [build,pow_succ]
    nlinarith

def Bound {C n : ℕ} (X : Data C n) (A : ℕ) : Prop := ∀ w c, (view (read X w c)).natAbs≤A

theorem build_bound {C n A : ℕ} (f : Word n → Run (Vector Cell C))
    (hf : ∀ w c, (view ((f w).value.get c)).natAbs≤A) : Bound (build n f).value A := by
  intro w c
  rw [build_read]
  exact hf w c

def cells {C : ℕ} : {n : ℕ} → Data C n → ℕ
  | 0, X => X.toArray.size
  | _+1, X => (X.toList.map (fun child => cells child)).sum

theorem cells_eq {C n : ℕ} (X : Data C n) : cells X=3^n*C := by
  induction n with
  | zero => simp [cells]
  | succ n ih =>
    simp only [cells,ih,List.map_const',Vector.length_toList,List.sum_replicate,smul_eq_mul,pow_succ]
    ring

#print axioms build_read
#print axioms build_bits
#print axioms build_control
#print axioms build_bound
#print axioms cells_eq
end ThinMatrix.PrefixCellTree
