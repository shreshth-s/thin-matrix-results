import BinaryPrefixContraction

set_option autoImplicit false

/-! Shared four-branch prefix encoding. Each parent is contracted once for each
local form; all resulting arrays remain in the trace. No whole tensor query is
executed separately for a leaf. The full tensor sum is a proved specification. -/
namespace ThinMatrix.RetainedPrefixEncoder
open BinaryCell BinaryGroupedCoordinates BinaryGroupedPreparation CroppedGroupedSuffix PrefixCellTree
open scoped BigOperators

def Trace (C : ℕ) : ℕ → Type
  | 0 => Vector Cell C
  | n+1 => Data C (n+1) × Vector (Trace C n) 4

def output {C : ℕ} : {n : ℕ} → Trace C n → (Fin n → Fin 4) → Fin C → Cell
  | 0, X, _, c => X.get c
  | _+1, trace, q, c => output (trace.2.get (q 0)) (fun i => q i.succ) c

def run {C : ℕ} : (n : ℕ) → Data C n → Run (Trace C n)
  | 0, X => ⟨X,0,4⟩
  | n+1, X =>
      let children := tabulate (Vector.replicate 4 ()) (fun q =>
        let contracted := BinaryPrefixContraction.execute q X
        let child := run n contracted.value
        ⟨child.value,contracted.bitSteps+child.bitSteps,contracted.control+child.control+8⟩)
      ⟨(X,children.value),children.bitSteps,children.control+8⟩

theorem run_value {C n : ℕ} (X : Data C n) (q : Fin n → Fin 4) (c : Fin C) :
    view (output (run n X).value q c)=EncoderCorrectness.tensorSum (fun _ : Fin n => 3)
      (fun i => BinaryPrefixContraction.form (q i)) (fun w => view (read X w c)) := by
  induction n with
  | zero => simp [run,output,EncoderCorrectness.tensorSum,PrefixCellTree.read]
  | succ n ih =>
    simp only [run,output,tabulate_get,ih]
    rw [EncoderCorrectness.tensorSum_succ]
    congr 1
    funext w
    exact BinaryPrefixContraction.execute_value _ _ w c

theorem run_bound {C n : ℕ} (X : Data C n) (A : ℕ) (ha : Bound X A)
    (q : Fin n → Fin 4) (c : Fin C) :
    (view (output (run n X).value q c)).natAbs≤2^n*A := by
  induction n generalizing A with
  | zero => simpa [run,output,PrefixCellTree.read] using ha (fun i => Fin.elim0 i) c
  | succ n ih =>
    have h := ih (BinaryPrefixContraction.execute (q 0) X).value (2*A)
      (BinaryPrefixContraction.execute_bound _ _ A ha) (fun i => q i.succ)
    simpa only [run,output,tabulate_get,pow_succ,Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using h

def unit (A : ℕ) : ℕ := 5*BackendScalarBits.backendScalarUnit A.size

theorem unit_mono {A B : ℕ} (h : A≤B) : unit A≤unit B := by
  have hs := Nat.size_le_size h
  unfold unit BackendScalarBits.backendScalarUnit BackendScalarBits.scalarUnit
  gcongr

def bitBudget (n C A : ℕ) : ℕ := n*4^n*C*unit (2^n*A)
def controlBudget (n C : ℕ) : ℕ := (n+1)*4^n*(112*C+1000*(n+1)^2)

theorem run_bits {C n : ℕ} (X : Data C n) (A : ℕ) (ha : Bound X A) :
    (run n X).bitSteps≤bitBudget n C A := by
  induction n generalizing A with
  | zero => simp [run,bitBudget]
  | succ n ih =>
    have hc (q : Fin 4) := BinaryPrefixContraction.execute_bits q X A ha
    have hr (q : Fin 4) := ih (BinaryPrefixContraction.execute q X).value (2*A)
      (BinaryPrefixContraction.execute_bound _ _ A ha)
    have hs := tabulate_bits (Vector.replicate 4 ()) (fun q =>
      let contracted := BinaryPrefixContraction.execute q X
      let child := run n contracted.value
      (⟨child.value,contracted.bitSteps+child.bitSteps,contracted.control+child.control+8⟩ : Run (Trace C n)))
      (fun q => Nat.add_le_add (hc q) (hr q))
    have hp : 3^n≤(4:ℕ)^n := Nat.pow_le_pow_left (by decide) n
    have hA : 2*A≤2^(n+1)*A := by
      have h : (2:ℕ)^1≤2^(n+1) := Nat.pow_le_pow_right (by decide) (by omega)
      simpa using Nat.mul_le_mul_right A h
    have hu := unit_mono hA
    have hl : BinaryPrefixContraction.bitBudget n C A≤4^n*C*unit (2^(n+1)*A) := by
      unfold BinaryPrefixContraction.bitBudget
      change 3^n*(C*unit (2*A))≤_
      calc
        _ ≤ 4^n*(C*unit (2^(n+1)*A)) := Nat.mul_le_mul hp (Nat.mul_le_mul_left C hu)
        _ = _ := by ring
    have he : 2^n*(2*A)=2^(n+1)*A := by ring
    change (run (n+1) X).bitSteps≤_ at hs
    calc
      _ ≤ 4*(BinaryPrefixContraction.bitBudget n C A+bitBudget n C (2*A)) := hs
      _ ≤ 4*(4^n*C*unit (2^(n+1)*A)+bitBudget n C (2*A)) := by omega
      _ = bitBudget (n+1) C A := by unfold bitBudget; rw [he,pow_succ]; ring

theorem run_control {C n : ℕ} (X : Data C n) : (run n X).control≤controlBudget n C := by
  induction n with
  | zero => simp [run,controlBudget]
  | succ n ih =>
    have hs := tabulate_control (Vector.replicate 4 ()) (fun q =>
      let contracted := BinaryPrefixContraction.execute q X
      let child := run n contracted.value
      (⟨child.value,contracted.bitSteps+child.bitSteps,contracted.control+child.control+8⟩ : Run (Trace C n)))
      (fun q => Nat.add_le_add_right (Nat.add_le_add (BinaryPrefixContraction.execute_control q X)
        (ih (BinaryPrefixContraction.execute q X).value)) 8)
    have hp : 3^n≤(4:ℕ)^n := Nat.pow_le_pow_left (by decide) n
    have hpos : 0<(4:ℕ)^n := pow_pos (by decide) _
    have hl : BinaryPrefixContraction.controlBudget n C≤4^n*(112*C+12*n^2+224*n+244) := by
      unfold BinaryPrefixContraction.controlBudget
      calc
        _ = 3^n*(112*C+12*n^2+224*n+244) := by ring
        _ ≤ _ := Nat.mul_le_mul_right _ hp
    change (run (n+1) X).control≤_
    simp only [run,controlBudget,pow_succ]
    unfold controlBudget at hs
    nlinarith

def cells {C : ℕ} : {n : ℕ} → Trace C n → ℕ
  | 0, X => X.toArray.size
  | _+1, trace => PrefixCellTree.cells trace.1+(trace.2.toList.map (fun t => cells t)).sum

theorem cells_bound {C n : ℕ} (trace : Trace C n) : cells trace≤(n+1)*4^n*C := by
  induction n with
  | zero => simp [cells]
  | succ n ih =>
    rcases trace with ⟨X,children⟩
    have hs : (children.toList.map (fun t => cells t)).sum≤4*((n+1)*4^n*C) := by
      have h := List.sum_le_card_nsmul (children.toList.map (fun t => cells t)) ((n+1)*4^n*C) (by
        intro v hv; obtain ⟨t,_,rfl⟩ := List.mem_map.mp hv; exact ih t)
      simpa using h
    have hp : 3^(n+1)≤(4:ℕ)^(n+1) := Nat.pow_le_pow_left (by decide) _
    simp only [cells,PrefixCellTree.cells_eq]
    calc
      _ ≤ 4^(n+1)*C+4*((n+1)*4^n*C) := Nat.add_le_add (Nat.mul_le_mul_right C hp) hs
      _ = _ := by rw [pow_succ]; ring

#print axioms run_value
#print axioms run_bound
#print axioms unit_mono
#print axioms run_bits
#print axioms run_control
#print axioms cells_bound
end ThinMatrix.RetainedPrefixEncoder
