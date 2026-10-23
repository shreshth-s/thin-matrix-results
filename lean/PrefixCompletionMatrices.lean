import GraphPrefixTensor

set_option autoImplicit false

/-! Copy every retained prefix leaf into a concrete support-by-coefficient
matrix. Four-way matrix trees preserve prefix sharing and all columns. The
original prefix traces remain retained by the enclosing program. -/
namespace ThinMatrix.PrefixCompletionMatrices
open BinaryCell BinaryGroupedCoordinates BinaryGroupedPreparation
open scoped BigOperators

abbrev Matrix (S C : ℕ) := Vector (Vector Cell C) S

def Tree (S C : ℕ) : ℕ → Type
  | 0 => Matrix S C
  | n+1 => Vector (Tree S C n) 4

def read {S C : ℕ} : {n : ℕ} → Tree S C n → (Fin n → Fin 4) → Matrix S C
  | 0, X, _ => X
  | _+1, X, q => read (X.get (q 0)) (fun i => q i.succ)

def build {S C : ℕ} : (n : ℕ) → Vector (RetainedPrefixEncoder.Trace C n) S → Run (Tree S C n)
  | 0, xs => tabulate xs (fun j => tabulate (xs.get j) (fun c =>
      let out := copy ((xs.get j).get c)
      ⟨out.value,out.bitSteps,8⟩))
  | n+1, xs =>
      let children := tabulate (Vector.replicate 4 ()) (fun a =>
        let picked := tabulate xs (fun j => (⟨((xs.get j).2.get a),0,8⟩ : Run (RetainedPrefixEncoder.Trace C n)))
        let child := build n picked.value
        ⟨child.value,picked.bitSteps+child.bitSteps,picked.control+child.control+8⟩)
      ⟨children.value,children.bitSteps,children.control+8⟩

theorem build_read {S C n : ℕ} (xs : Vector (RetainedPrefixEncoder.Trace C n) S)
    (q : Fin n → Fin 4) (j : Fin S) (c : Fin C) :
    view (((read (build n xs).value q).get j).get c)=view (RetainedPrefixEncoder.output (xs.get j) q c) := by
  induction n with
  | zero => simp [build,read,RetainedPrefixEncoder.output,tabulate_get]
  | succ n ih =>
    simp only [build,read,tabulate_get,ih,RetainedPrefixEncoder.output]

def LeafBound {S C n : ℕ} (xs : Vector (RetainedPrefixEncoder.Trace C n) S) (A : ℕ) : Prop :=
  ∀ j q c, (view (RetainedPrefixEncoder.output (xs.get j) q c)).natAbs≤A

def bitBudget (n S C A : ℕ) : ℕ := 4^n*(S*(C*BackendScalarBits.backendScalarUnit A.size))
def controlBudget (n S C : ℕ) : ℕ := (n+1)*4^n*(S*(40*C+100)+100)

theorem build_bits {S C n : ℕ} (xs : Vector (RetainedPrefixEncoder.Trace C n) S)
    (A : ℕ) (ha : LeafBound xs A) : (build n xs).bitSteps≤bitBudget n S C A := by
  induction n with
  | zero =>
    simp only [build,bitBudget,pow_zero,Nat.one_mul]
    apply tabulate_bits; intro j
    apply tabulate_bits; intro c
    exact copy_price _ _ (Nat.size_le_size (ha j (fun i => Fin.elim0 i) c))
  | succ n ih =>
    have h := tabulate_bits (Vector.replicate 4 ()) (fun a =>
      let picked := tabulate xs (fun j => (⟨((xs.get j).2.get a),0,8⟩ : Run (RetainedPrefixEncoder.Trace C n)))
      let child := build n picked.value
      (⟨child.value,picked.bitSteps+child.bitSteps,picked.control+child.control+8⟩ : Run (Tree S C n)))
      (W:=bitBudget n S C A) (by
        intro a
        simp only [tabulate_bits_eq,Finset.sum_const_zero,Nat.zero_add]
        apply ih
        intro j q c
        simpa only [tabulate_get,RetainedPrefixEncoder.output,Fin.cons_zero,Fin.cons_succ] using
          ha j (Fin.cons a q) c)
    simpa only [build,bitBudget,pow_succ,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using h

theorem build_control {S C n : ℕ} (xs : Vector (RetainedPrefixEncoder.Trace C n) S) :
    (build n xs).control≤controlBudget n S C := by
  induction n with
  | zero =>
    have h := tabulate_control xs (fun j => tabulate (xs.get j) (fun c =>
      (⟨(copy ((xs.get j).get c)).value,(copy ((xs.get j).get c)).bitSteps,8⟩ : Run Cell)))
      (fun j => tabulate_control (xs.get j) _ (W:=8) (by intro c; rfl))
    simp only [build,controlBudget,pow_zero]
    nlinarith
  | succ n ih =>
    have hp (a : Fin 4) := tabulate_control xs
      (fun j => (⟨((xs.get j).2.get a),0,8⟩ : Run (RetainedPrefixEncoder.Trace C n))) (W:=8) (by intro j; rfl)
    have h := tabulate_control (Vector.replicate 4 ()) (fun a =>
      let picked := tabulate xs (fun j => (⟨((xs.get j).2.get a),0,8⟩ : Run (RetainedPrefixEncoder.Trace C n)))
      let child := build n picked.value
      (⟨child.value,picked.bitSteps+child.bitSteps,picked.control+child.control+8⟩ : Run (Tree S C n)))
      (W:=40*S+controlBudget n S C+16) (by
        intro a
        have hc := ih (tabulate xs (fun j => (⟨((xs.get j).2.get a),0,8⟩ : Run (RetainedPrefixEncoder.Trace C n)))).value
        have hh := hp a
        dsimp only
        omega)
    have hpos : 0<(4:ℕ)^n := pow_pos (by decide) _
    have hK : 40*S+52≤4^n*(S*(40*C+100)+100) := by
      have hk := Nat.le_mul_of_pos_left (S*(40*C+100)+100) hpos
      nlinarith
    change _+8≤_
    unfold controlBudget at h ⊢
    rw [pow_succ]
    nlinarith

def cells {S C : ℕ} : {n : ℕ} → Tree S C n → ℕ
  | 0, X => (X.toList.map (fun row => row.toArray.size)).sum
  | _+1, X => (X.toList.map (fun child => cells child)).sum

theorem cells_eq {S C n : ℕ} (X : Tree S C n) : cells X=4^n*S*C := by
  induction n with
  | zero => simp [cells]
  | succ n ih =>
    simp only [cells,ih,List.map_const',Vector.length_toList,List.sum_replicate,smul_eq_mul,pow_succ]
    ring

abbrev Prepared (P ell r C : ℕ) := Vector (Tree (CappedSubsetList.count ell r) C P) (2^ell)

def prepare {P ell r C : ℕ} (xs : CappedPrefixProgram.Prepared P ell r C) : Run (Prepared P ell r C) :=
  tabulate xs.traces (fun p => build P (xs.traces.get p))

theorem prepare_get {P ell r C : ℕ} (xs : CappedPrefixProgram.Prepared P ell r C)
    (p : Fin (2^ell)) (q : Fin P → Fin 4) (j : Fin (CappedSubsetList.count ell r)) (c : Fin C) :
    view (((read ((prepare xs).value.get p) q).get j).get c)=
      view (RetainedPrefixEncoder.output ((xs.traces.get p).get j) q c) := by
  simp only [prepare,tabulate_get,build_read]

theorem prepare_bits {P ell r C : ℕ} (xs : CappedPrefixProgram.Prepared P ell r C)
    (A : ℕ) (ha : ∀ p, LeafBound (xs.traces.get p) A) :
    (prepare xs).bitSteps≤2^ell*bitBudget P (CappedSubsetList.count ell r) C A :=
  tabulate_bits _ _ (fun p => build_bits _ A (ha p))

theorem prepare_control {P ell r C : ℕ} (xs : CappedPrefixProgram.Prepared P ell r C) :
    (prepare xs).control≤2^ell*(controlBudget P (CappedSubsetList.count ell r) C+32)+8 :=
  tabulate_control _ _ (fun _ => build_control _)

#print axioms build_read
#print axioms build_bits
#print axioms build_control
#print axioms cells_eq
#print axioms prepare_get
#print axioms prepare_bits
#print axioms prepare_control
end ThinMatrix.PrefixCompletionMatrices
