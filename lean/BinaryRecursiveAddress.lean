import BinaryPowerAddress
import BinaryChunkAddress

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! Consumed binary addresses for the matrix-pair tensor words used by the
actual retained CW recursion. Pair flattening and splitting operate on stored
bits at every letter; no native pair quotient is used for the returned value. -/
namespace ThinMatrix.BinaryRecursiveAddress
open BinaryCell
open PolynomialDegeneration RecursiveTable
variable {a b : ℕ}

def pairRank (i : Fin a×Fin b) : Result (Fin (a*b)) :=
  let out := BinaryMatrixAddress.join b i.1.val i.2.val
  ⟨⟨out.value,by rw [BinaryMatrixAddress.join_layout];exact (finProdFinEquiv i).isLt⟩,out.bitSteps+4⟩

theorem pairRank_value (i : Fin a×Fin b) : (pairRank i).value=finProdFinEquiv i :=
  Fin.ext (BinaryMatrixAddress.join_layout i)

def pairUnrank (i : Fin (a*b)) : Result (Fin a×Fin b) :=
  let out := BinaryMatrixAddress.split b i.val
  have hv := BinaryMatrixAddress.split_layout i
  ⟨(⟨out.value.1,by rw [hv];exact (finProdFinEquiv.symm i).1.isLt⟩,
    ⟨out.value.2,by rw [hv];exact (finProdFinEquiv.symm i).2.isLt⟩),out.bitSteps+4⟩

theorem pairUnrank_value (i : Fin (a*b)) : (pairUnrank i).value=finProdFinEquiv.symm i := by
  apply Prod.ext <;> apply Fin.ext <;> simp only [pairUnrank,BinaryMatrixAddress.split_layout]

def flatten : (k : ℕ) → PowerIndex (Fin a×Fin b) k → Result (PowerIndex (Fin (a*b)) k)
  | 0,_ => ⟨PUnit.unit,1⟩
  | k+1,x =>
    let head := pairRank x.1
    let tail := flatten k x.2
    ⟨(head.value,tail.value),head.bitSteps+tail.bitSteps+8⟩

def expand : (k : ℕ) → PowerIndex (Fin (a*b)) k → Result (PowerIndex (Fin a×Fin b) k)
  | 0,_ => ⟨PUnit.unit,1⟩
  | k+1,x =>
    let head := pairUnrank x.1
    let tail := expand k x.2
    ⟨(head.value,tail.value),head.bitSteps+tail.bitSteps+8⟩

theorem expand_flatten (k : ℕ) (x : PowerIndex (Fin a×Fin b) k) :
    (expand k (flatten k x).value).value=x := by
  induction k with
  | zero => cases x; rfl
  | succ k ih =>
    simp only [flatten,expand,pairUnrank_value,pairRank_value,Equiv.symm_apply_apply,ih]
    cases x; rfl

theorem flatten_expand (k : ℕ) (x : PowerIndex (Fin (a*b)) k) :
    (flatten k (expand k x).value).value=x := by
  induction k with
  | zero => cases x; rfl
  | succ k ih =>
    simp only [flatten,expand,pairUnrank_value,pairRank_value,Equiv.apply_symm_apply,ih]
    cases x; rfl

theorem flatten_layout (k : ℕ) (x : PowerIndex (Fin a×Fin b) k) :
    ((power (fin (a*b)) k).index (flatten k x).value).val=
      ((power (prod (fin a) (fin b)) k).index x).val := by
  induction k with
  | zero => rfl
  | succ k ih =>
    simp only [flatten,pairRank_value]
    change ((power (fin (a*b)) k).index (flatten k x.2).value).val+
      (power (fin (a*b)) k).size*(finProdFinEquiv x.1).val=
      ((power (prod (fin a) (fin b)) k).index x.2).val+
        (power (prod (fin a) (fin b)) k).size*(finProdFinEquiv x.1).val
    rw [ih]
    simp only [power_size,prod,fin]

def rank (k : ℕ) (x : PowerIndex (Fin a×Fin b) k) : Result ℕ :=
  let word := flatten k x
  let address := BinaryPowerAddress.rank (a*b) k word.value
  ⟨address.value,word.bitSteps+address.bitSteps+4⟩

theorem rank_value (k : ℕ) (x : PowerIndex (Fin a×Fin b) k) :
    (rank k x).value=((power (prod (fin a) (fin b)) k).index x).val := by
  simp only [rank,BinaryPowerAddress.rank_value,flatten_layout]

def unrank (ha : 0<a) (hb : 0<b) (k : ℕ) (i : Fin ((a*b)^k)) : Result (PowerIndex (Fin a×Fin b) k) :=
  let word := BinaryPowerAddress.unrank (a*b) (Nat.mul_pos ha hb) k i
  let address := expand k word.value
  ⟨address.value,word.bitSteps+address.bitSteps+4⟩

theorem rank_unrank (ha : 0<a) (hb : 0<b) (k : ℕ) (i : Fin ((a*b)^k)) :
    (rank k (unrank ha hb k i).value).value=i.val := by
  simp only [rank,unrank,flatten_expand,BinaryPowerAddress.rank_unrank]

theorem unrank_value (ha : 0<a) (hb : 0<b) (k : ℕ) (i : Fin ((a*b)^k)) :
    (unrank ha hb k i).value=(power (prod (fin a) (fin b)) k).index.symm (Fin.cast (by simp [prod,fin]) i) := by
  apply (power (prod (fin a) (fin b)) k).index.injective
  apply Fin.ext
  rw [←rank_value,rank_unrank]
  simp

theorem flatten_bits (k W : ℕ) (hW : (a*b).size≤W) (ha : 0<a) (hb : 0<b)
    (x : PowerIndex (Fin a×Fin b) k) : (flatten k x).bitSteps≤4110*(k+1)*(W+1)^2 := by
  have hAw : a.size≤W := (Nat.size_le_size (Nat.le_mul_of_pos_right a hb)).trans hW
  have hBw : b.size≤W := (Nat.size_le_size (Nat.le_mul_of_pos_left b ha)).trans hW
  induction k with
  | zero => simp only [flatten,zero_add,mul_one];nlinarith
  | succ k ih =>
    have hh := BinaryMatrixAddress.join_bits b x.1.1.val x.1.2.val W hBw
      ((Nat.size_le_size x.1.1.isLt.le).trans hAw) ((Nat.size_le_size x.1.2.isLt.le).trans hBw)
    have ht := ih x.2
    simp only [flatten,pairRank]
    nlinarith

theorem expand_bits (k W : ℕ) (hW : (a*b).size≤W) (ha : 0<a)
    (x : PowerIndex (Fin (a*b)) k) : (expand k x).bitSteps≤142*(k+1)*(W+1)^2 := by
  have hBw : b.size≤W := (Nat.size_le_size (Nat.le_mul_of_pos_left b ha)).trans hW
  induction k with
  | zero => simp only [expand,zero_add,mul_one];nlinarith
  | succ k ih =>
    have hh := BinaryMatrixAddress.split_bits b x.1.val W hBw
      ((Nat.size_le_size x.1.isLt.le).trans hW)
    have ht := ih x.2
    simp only [expand,pairUnrank]
    nlinarith

theorem rank_bits (k W : ℕ) (ha : 0<a) (hb : 0<b) (hW : (a*b).size≤W)
    (hpow : ((a*b)^k).size≤W) (x : PowerIndex (Fin a×Fin b) k) :
    (rank k x).bitSteps≤16384*(k+1)^2*(W+1)^2 := by
  have hf := flatten_bits k W hW ha hb x
  have hr := BinaryPowerAddress.rank_bits (a*b) k W (Nat.mul_pos ha hb) hW hpow (flatten k x).value
  simp only [rank]
  nlinarith

theorem unrank_bits (k W : ℕ) (ha : 0<a) (hb : 0<b) (hW : (a*b).size≤W)
    (hpow : ((a*b)^k).size≤W) (i : Fin ((a*b)^k)) :
    (unrank ha hb k i).bitSteps≤16384*(k+1)^2*(W+1)^2 := by
  have hu := BinaryPowerAddress.unrank_bits (a*b) k W (Nat.mul_pos ha hb) hW hpow i
  have he := expand_bits k W hW ha (BinaryPowerAddress.unrank (a*b) (Nat.mul_pos ha hb) k i).value
  simp only [unrank]
  nlinarith

#print axioms pairRank_value
#print axioms pairUnrank_value
#print axioms expand_flatten
#print axioms flatten_expand
#print axioms flatten_layout
#print axioms rank_value
#print axioms rank_unrank
#print axioms unrank_value
#print axioms flatten_bits
#print axioms expand_bits
#print axioms rank_bits
#print axioms unrank_bits
end ThinMatrix.BinaryRecursiveAddress
