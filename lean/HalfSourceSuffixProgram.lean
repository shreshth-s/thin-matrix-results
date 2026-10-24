import HalfSourcePascal
import BinaryMatrixAddress

set_option autoImplicit false
set_option maxHeartbeats 1200000

/-! Exact binary suffix selection. Cumulative binomial rows are produced by
retained Pascal additions; radius multiplication/division and count comparison
are actual binary routines. The setup retains its rows and every tested flag. -/
namespace ThinMatrix.HalfSourceSuffixProgram
open BinaryGroupedCoordinates BinaryGroupedPreparation
open BinaryControllerExecution (NatCell nview)
open HalfSourcePascal

def rowAt {K : ℕ} : {n : ℕ} → History K n → (i : ℕ) → i ≤ n → Run (Row K)
  | 0,rows,_,_ => ⟨rows,0,8⟩
  | n+1,rows,i,hi =>
    if h : i=n+1 then ⟨rows.2,0,8⟩
    else
      let out := rowAt rows.1 i (by omega)
      ⟨out.value,out.bitSteps,out.control+8⟩

theorem rowAt_value (K n i : ℕ) (hi : i ≤ n) (j : Fin (K+1)) :
    nview ((rowAt (build K n).value i hi).value.get j)=CappedSubsetList.count i j.val := by
  induction n with
  | zero =>
    have hi0 : i=0 := by omega
    subst i
    simpa [rowAt,current] using build_value K 0 j
  | succ n ih =>
    simp only [build,rowAt]
    split_ifs with h
    · subst i; exact build_value K (n+1) j
    · exact ih (by omega)

theorem rowAt_bits {K n : ℕ} (rows : History K n) (i : ℕ) (hi : i ≤ n) :
    (rowAt rows i hi).bitSteps=0 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [rowAt]; split_ifs <;> simp [ih]

theorem rowAt_control {K n : ℕ} (rows : History K n) (i : ℕ) (hi : i ≤ n) :
    (rowAt rows i hi).control ≤ 8*(n+1) := by
  induction n with
  | zero => simp [rowAt]
  | succ n ih =>
    simp only [rowAt]
    split_ifs
    · dsimp only; omega
    · dsimp only
      have h := ih rows.1 (by omega)
      omega

def radiusRun (k rare ell : ℕ) : Run ℕ :=
  if k=0 then ⟨0,0,8⟩ else
    let product := BinaryMatrixAddress.join rare ell 0
    let quotient := BinaryMatrixAddress.split k product.value
    ⟨quotient.value.1,product.bitSteps+quotient.bitSteps,16⟩

theorem radius_value (k rare ell : ℕ) :
    (radiusRun k rare ell).value=HalfSourceSuffixChoice.radius k rare ell := by
  unfold radiusRun
  split_ifs with hk
  · simp [HalfSourceSuffixChoice.radius,hk]
  · have hkpos : 0<k := by omega
    simp only [BinaryMatrixAddress.join_value,Nat.zero_add,BinaryMatrixAddress.split_value k (rare*ell) hkpos,HalfSourceSuffixChoice.radius]

def test {K : ℕ} (rare : ℕ) (_hr : rare ≤ K) (cap : NatCell)
    (rows : History K K) (ell : Fin (K+1)) : Run Bool :=
  let radius := radiusRun K rare ell.val
  let row := rowAt rows ell.val (by omega)
  let count := row.value.get ⟨min radius.value K,by omega⟩
  let out := BinaryControllerExecution.le count cap
  ⟨out.value,radius.bitSteps+row.bitSteps+out.bitSteps,radius.control+row.control+16⟩

theorem test_value (K rare : ℕ) (hr : rare ≤ K) (cap : NatCell) (ell : Fin (K+1)) :
    (test rare hr cap (build K K).value ell).value=
      decide (CappedSubsetList.count ell.val (HalfSourceSuffixChoice.radius K rare ell.val) ≤ nview cap) := by
  simp only [test,BinaryControllerExecution.le_value,rowAt_value,radius_value]
  rw [Nat.min_eq_left ((HalfSourceSuffixChoice.radius_le K rare ell.val hr).trans (by omega))]

def flags (K rare : ℕ) (hr : rare ≤ K) (cap : NatCell) (rows : History K K) : Run (Vector Bool (K+1)) :=
  tabulate (Vector.replicate (K+1) ()) (fun ell => test rare hr cap rows ell)

def scan {K : ℕ} (flags : Vector Bool K) : (n : ℕ) → n ≤ K → Run ℕ
  | 0,_ => ⟨0,0,8⟩
  | n+1,hn =>
    let old := scan flags n (by omega)
    ⟨if flags.get ⟨n,by omega⟩ then n else old.value,old.bitSteps,old.control+16⟩

theorem scan_bound {K : ℕ} (flags : Vector Bool K) (n : ℕ) (hn : n ≤ K) :
    (scan flags n hn).value ≤ n := by
  induction n with
  | zero => simp [scan]
  | succ n ih => simp only [scan]; split_ifs <;> have := ih (by omega) <;> omega

theorem scan_sup {K : ℕ} (flags : Vector Bool K) (n : ℕ) (hn : n ≤ K) :
    (scan flags n hn).value = ((Finset.range n).filter (fun i => if hi : i<K then flags.get ⟨i,hi⟩=true else False)).sup id := by
  induction n with
  | zero => simp [scan]
  | succ n ih =>
    simp only [scan,Finset.range_add_one,Finset.filter_insert]
    have hnk : n<K := by omega
    simp only [hnk,dif_pos]
    by_cases hf : flags.get ⟨n,hnk⟩=true
    · simp only [hf,ite_true,Finset.sup_insert,id_eq]
      rw [← ih (by omega),Nat.max_eq_left (scan_bound flags n (by omega))]
    · simp only [hf]
      exact ih (by omega)

def execute (K rare cap : ℕ) (hr : rare ≤ K) : Run (History K K × Vector Bool (K+1) × ℕ) :=
  let rows := build K K
  let bound := BinaryControllerExecution.fromPublic cap
  let tests := flags K rare hr bound.value rows.value
  let out := scan tests.value (K+1) (by omega)
  ⟨(rows.value,tests.value,out.value),rows.bitSteps+bound.bitSteps+tests.bitSteps+out.bitSteps,
    rows.control+bound.controlSites+tests.control+out.control+16⟩

theorem execute_value (K rare cap : ℕ) (hr : rare ≤ K) :
    (execute K rare cap hr).value.2.2=HalfSourceSuffixChoice.choose K rare cap := by
  simp only [execute,scan_sup,HalfSourceSuffixChoice.choose,HalfSourceSuffixChoice.candidates]
  apply congrArg (fun s : Finset ℕ => s.sup id)
  ext i
  simp only [Finset.mem_filter,Finset.mem_range]
  constructor
  · rintro ⟨hi,h⟩
    simp only [hi,dif_pos,flags,tabulate_get,test_value,BinaryControllerExecution.fromPublic_nview,decide_eq_true_eq] at h
    exact ⟨hi,h⟩
  · rintro ⟨hi,h⟩
    refine ⟨hi,?_⟩
    simpa only [hi,dif_pos,flags,tabulate_get,test_value,BinaryControllerExecution.fromPublic_nview,decide_eq_true_eq] using h

theorem size_le_self (a : ℕ) : a.size ≤ a := Nat.size_le.mpr Nat.lt_two_pow_self

def radiusBudget (K : ℕ) : ℕ := 4224*(K*K+2)^2

theorem radius_bits (K rare ell : ℕ) (hr : rare ≤ K) (he : ell ≤ K) :
    (radiusRun K rare ell).bitSteps ≤ radiusBudget K := by
  have hw : K ≤ K*K+1 := by nlinarith
  have hp : rare*ell ≤ K*K := Nat.mul_le_mul hr he
  have hj := BinaryMatrixAddress.join_bits rare ell 0 (K*K+1)
    ((size_le_self rare).trans (by omega)) ((size_le_self ell).trans (by omega)) (by simp)
  have hd := BinaryMatrixAddress.split_bits K (rare*ell) (K*K+1)
    ((size_le_self K).trans hw) ((size_le_self (rare*ell)).trans (by omega))
  unfold radiusRun
  split_ifs
  · simp [radiusBudget]
  · simp only [BinaryMatrixAddress.join_value,Nat.zero_add]
    unfold radiusBudget
    simp only [Nat.add_assoc,show 1+1=2 by decide] at hj hd
    omega

theorem radius_control (K rare ell : ℕ) : (radiusRun K rare ell).control ≤ 16 := by
  unfold radiusRun
  split_ifs <;> simp

def testBudget (K W : ℕ) : ℕ := radiusBudget K+BackendScalarBits.backendScalarUnit (K+W+1)

theorem test_bits (K rare : ℕ) (hr : rare ≤ K) (cap : NatCell) (ell : Fin (K+1)) :
    (test rare hr cap (build K K).value ell).bitSteps ≤ testBudget K (nview cap).size := by
  have hrb := radius_bits K rare ell.val hr (by omega)
  let row := rowAt (build K K).value ell.val (by omega)
  have hwidth : (nview (row.value.get ⟨min (radiusRun K rare ell.val).value K,by omega⟩)).size ≤ K+1 := by
    dsimp only [row]
    rw [rowAt_value]
    change (CappedSubsetList.count ell.val (min (radiusRun K rare ell.val).value K)).size ≤ K+1
    have h := Nat.size_le_size (count_le_power ell.val (min (radiusRun K rare ell.val).value K))
    simp only [Nat.size_pow] at h
    omega
  have hb := BinaryControllerExecution.le_price (K+(nview cap).size+1)
    (row.value.get ⟨min (radiusRun K rare ell.val).value K,by omega⟩) cap (hwidth.trans (by omega)) (by omega)
  have hz := rowAt_bits (build K K).value ell.val (by omega)
  change _+_+_≤_
  unfold testBudget
  dsimp only [row,BinaryControllerExecution.unit] at hb
  omega

theorem test_control {K : ℕ} (rare : ℕ) (hr : rare ≤ K) (cap : NatCell)
    (rows : History K K) (ell : Fin (K+1)) :
    (test rare hr cap rows ell).control ≤ 8*(K+1)+32 := by
  have hh := rowAt_control rows ell.val (by omega)
  have hr := radius_control K rare ell.val
  change _+_+16≤_
  omega

theorem scan_bits {K : ℕ} (flags : Vector Bool K) (n : ℕ) (hn : n ≤ K) :
    (scan flags n hn).bitSteps=0 := by
  induction n with
  | zero => rfl
  | succ n ih => exact ih (by omega)

theorem scan_control {K : ℕ} (flags : Vector Bool K) (n : ℕ) (hn : n ≤ K) :
    (scan flags n hn).control=16*n+8 := by
  induction n with
  | zero => rfl
  | succ n ih => simp only [scan,ih]; ring

def bitBudget (K W : ℕ) : ℕ := K*(K+1)*BackendScalarBits.backendScalarUnit (K+1)+(K+1)*testBudget K W

def controlBudget (K W : ℕ) : ℕ :=
  (K+1)*(64*(K+1)+16)+(8*W+3)+((K+1)*(8*(K+1)+64)+8)+(16*(K+1)+8)+16

theorem execute_bits (K rare cap : ℕ) (hr : rare ≤ K) :
    (execute K rare cap hr).bitSteps ≤ bitBudget K cap.size := by
  have hb := build_bits K K (by omega)
  have hf := tabulate_bits (Vector.replicate (K+1) ())
    (fun ell => test rare hr (BinaryControllerExecution.fromPublic cap).value (build K K).value ell)
    (W:=testBudget K cap.size) (by intro ell; simpa only [BinaryControllerExecution.fromPublic_nview] using test_bits K rare hr (BinaryControllerExecution.fromPublic cap).value ell)
  have hs := scan_bits (flags K rare hr (BinaryControllerExecution.fromPublic cap).value (build K K).value).value (K+1) (by omega)
  have hp : (BinaryControllerExecution.fromPublic cap).bitSteps=0 := by
    exact (BinaryControllerExecution.publicBits_zero_bits cap).1
  simp only [execute,bitBudget,flags] at hf hs ⊢
  omega

theorem execute_control (K rare cap : ℕ) (hr : rare ≤ K) :
    (execute K rare cap hr).control ≤ controlBudget K cap.size := by
  have hb := build_control K K
  have hf := tabulate_control (Vector.replicate (K+1) ())
    (fun ell => test rare hr (BinaryControllerExecution.fromPublic cap).value (build K K).value ell)
    (W:=8*(K+1)+32) (fun ell => test_control rare hr _ _ ell)
  have hs := scan_control (flags K rare hr (BinaryControllerExecution.fromPublic cap).value (build K K).value).value (K+1) (by omega)
  have hp := BinaryControllerExecution.fromPublic_control cap
  simp only [execute,controlBudget,flags] at hf hs ⊢
  simp only [Nat.add_assoc,show 32+32=64 by decide] at hf
  omega

#print axioms size_le_self
#print axioms radius_bits
#print axioms radius_control
#print axioms test_bits
#print axioms test_control
#print axioms scan_bits
#print axioms scan_control
#print axioms execute_bits
#print axioms execute_control
#print axioms rowAt_value
#print axioms rowAt_bits
#print axioms rowAt_control
#print axioms radius_value
#print axioms test_value
#print axioms scan_bound
#print axioms scan_sup
#print axioms execute_value
end ThinMatrix.HalfSourceSuffixProgram
