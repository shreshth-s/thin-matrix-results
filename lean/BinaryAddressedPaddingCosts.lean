import BinaryAddressedPadding

set_option autoImplicit false
set_option maxHeartbeats 1800000
set_option maxRecDepth 5000
set_option backward.isDefEq.respectTransparency false

namespace ThinMatrix.BinaryAddressedPaddingCosts
open scoped BigOperators
open BinaryCell BinaryGroupedCoordinates
open RecursiveTable (Table prod fin power)
open PolynomialDegeneration RetainedEqualCopy
open BinaryAddressedRecursion BinaryAddressedCosts BinaryAddressedPadding
variable {a b c r t n m p : ℕ}

theorem component_widths (ha : 0<a) (hb : 0<b) (K W k : ℕ) (h : Fits a b r t K W) (hk : k≤K) :
    (a^k).size≤W ∧ (b^k).size≤W := by
  constructor
  · exact (Nat.size_le_size (Nat.pow_le_pow_left (Nat.le_mul_of_pos_right a hb) k)).trans (h.words k hk)
  · exact (Nat.size_le_size (Nat.pow_le_pow_left (Nat.le_mul_of_pos_left b ha) k)).trans (h.words k hk)

theorem padEntry_bits (ha : 0<a) (hb : 0<b) (k W : ℕ)
    (haW : a.size≤W) (hbW : b.size≤W) (htW : t.size≤W)
    (hpa : (a^k).size≤W) (hpb : (b^k).size≤W) (hn : n.size≤W) (hm : m.size≤W)
    (x : Table (PaddedMatrix.matrix n m) Cell) (z : Fin t×PowerIndex (Fin a×Fin b) k) :
    (padEntry k x z).bitSteps≤32768*(k+1)^2*(W+1)^2 := by
  let coordinates := MatrixPowerReindex.unpair k z.2
  have hr := BinaryPowerAddress.rank_bits a k W ha haW hpa coordinates.1
  have hc := BinaryPowerAddress.rank_bits b k W hb hbW hpb coordinates.2
  have hrange := BinaryPowerAddress.rank_lt a k coordinates.1
  have crange := BinaryPowerAddress.rank_lt b k coordinates.2
  have hw : 1≤W := by
    have hp : 1≤t.size := Nat.size_pos.mpr ((Nat.zero_le _).trans_lt z.1.isLt)
    omega
  have hf := BinaryChunkAddress.less_bits z.1.val 1 W ((Nat.size_le_size z.1.isLt.le).trans htW) (by simpa using hw)
  have hrr := BinaryChunkAddress.less_bits (BinaryPowerAddress.rank a k coordinates.1).value n W
    ((Nat.size_le_size hrange.le).trans hpa) hn
  have hcc := BinaryChunkAddress.less_bits (BinaryPowerAddress.rank b k coordinates.2).value m W
    ((Nat.size_le_size crange.le).trans hpb) hm
  have hkunit : 1≤(k+1)^2 := one_le_pow₀ (by omega)
  have hwunit : 1≤(W+1)^2 := one_le_pow₀ (by omega)
  have hku : k+1≤(k+1)^2 := by
    have hh : 1≤k+1 := by omega
    simpa using Nat.pow_le_pow_right hh (show 1≤2 by decide)
  have hstruct := Nat.mul_le_mul_right ((W+1)^2) hku
  have hbase := Nat.mul_le_mul_right ((W+1)^2) hkunit
  have hsmall := Nat.mul_le_mul_left (k+1) hwunit
  have hbudget : (BinaryPowerAddress.rank a k coordinates.1).bitSteps+
      (BinaryPowerAddress.rank b k coordinates.2).bitSteps+
      (BinaryChunkAddress.less z.1.val 1).bitSteps+
      (BinaryChunkAddress.less (BinaryPowerAddress.rank a k coordinates.1).value n).bitSteps+
      (BinaryChunkAddress.less (BinaryPowerAddress.rank b k coordinates.2).value m).bitSteps+
      8*(k+1)+4100*(W+1)^2≤32768*(k+1)^2*(W+1)^2 := by
    nlinarith only [hr,hc,hf,hrr,hcc,hstruct,hbase,hsmall]
  dsimp only [padEntry]
  split_ifs with h0 hi hj
  · have hread := BinaryChunkAddress.matrixRead_bits x
      ⟨(BinaryPowerAddress.rank a k coordinates.1).value,(BinaryChunkAddress.less_true _ _).mp hi⟩
      ⟨(BinaryPowerAddress.rank b k coordinates.2).value,(BinaryChunkAddress.less_true _ _).mp hj⟩ W hn hm
    exact (Nat.add_le_add_left hread _).trans hbudget
  all_goals exact (Nat.le_add_right _ (4100*(W+1)^2)).trans hbudget

theorem pad_bits (ha : 0<a) (hb : 0<b) (k W : ℕ) (h : Fits a b r t k W)
    (hn : n≤a^k) (hm : m≤b^k) (x : Table (PaddedMatrix.matrix n m) Cell) :
    (pad (t:=t) ha hb k x).bitSteps≤t*(a*b)^k*unit k W := by
  have hw := component_widths ha hb k W k h (by rfl)
  have hh := BinaryRecursiveTable.tabulate_bits ha hb k W h.pair (h.words k (by rfl))
    (h.copyCells k (by rfl)) (padEntry k x)
  rw [BinaryRecursiveDot.tabulate_bits] at hh
  have hs := Finset.sum_le_sum (fun z (_ : z∈Finset.univ) =>
    padEntry_bits ha hb k W h.first h.second h.copies hw.1 hw.2
      ((Nat.size_le_size hn).trans hw.1) ((Nat.size_le_size hm).trans hw.2) x z)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,powerIndex_card,smul_eq_mul] at hs
  change (BinaryRecursiveTable.tabulate ha hb k (padEntry k x)).bitSteps≤_
  unfold unit
  nlinarith

theorem cropEntry_bits (ha : 0<a) (hc : 0<c) (ht : 0<t) (k W : ℕ)
    (h : Fits c a r t k W) (hn : n≤a^k) (hp : p≤c^k) (x : Cells t c a k) (i : Fin (n*p)) :
    (cropEntry ha hc ht k hn hp x i).bitSteps≤unit k W := by
  have hw := component_widths hc ha k W k h (by rfl)
  have hnp : n*p≤(c*a)^k := by
    have hh := Nat.mul_le_mul hn hp
    simpa only [mul_pow,mul_comm] using hh
  have hi : i.val.size≤W := (Nat.size_le_size (i.isLt.le.trans hnp)).trans (h.words k (by rfl))
  have hpW : p.size≤W := (Nat.size_le_size hp).trans hw.1
  have hs := BinaryMatrixAddress.split_bits p i.val W hpW hi
  have hpp : 0<p := by nlinarith [i.isLt]
  let row : Fin n := ⟨(BinaryMatrixAddress.split p i.val).value.1,by
    rw [BinaryMatrixAddress.split_value _ _ hpp];exact (Nat.div_lt_iff_lt_mul hpp).mpr i.isLt⟩
  let col : Fin p := ⟨(BinaryMatrixAddress.split p i.val).value.2,by
    rw [BinaryMatrixAddress.split_value _ _ hpp];exact Nat.mod_lt _ hpp⟩
  have hr := BinaryPowerAddress.unrank_bits a k W ha h.second hw.2 ⟨row.val,row.isLt.trans_le hn⟩
  have hcol := BinaryPowerAddress.unrank_bits c k W hc h.first hw.1 ⟨col.val,col.isLt.trans_le hp⟩
  have hout := BinaryRecursiveTable.read_bits k W hc ha h.pair (h.words k (by rfl)) h.copies x
    (⟨0,ht⟩,FiniteMatrixPowers.pair k
      ((BinaryPowerAddress.unrank c hc k ⟨col.val,col.isLt.trans_le hp⟩).value,
       (BinaryPowerAddress.unrank a ha k ⟨row.val,row.isLt.trans_le hn⟩).value))
  have hku : k+1≤(k+1)^2 := by
    have hh : 1≤k+1 := by omega
    simpa using Nat.pow_le_pow_right hh (show 1≤2 by decide)
  have hwu : 1≤(W+1)^2 := one_le_pow₀ (by omega)
  have hwu' := Nat.mul_le_mul_left (k+1) hwu
  have hku' := Nat.mul_le_mul_right ((W+1)^2) hku
  dsimp only [cropEntry]
  dsimp only [row,col] at hr hcol hout
  unfold unit
  nlinarith

theorem crop_bits (ha : 0<a) (hc : 0<c) (ht : 0<t) (k W : ℕ)
    (h : Fits c a r t k W) (hn : n≤a^k) (hp : p≤c^k) (x : Cells t c a k) :
    (crop ha hc ht k hn hp x).bitSteps≤n*p*unit k W := by
  simp only [crop,Vector.toList_ofFn,List.map_ofFn,Function.comp_apply,List.sum_ofFn]
  have hh := Finset.sum_le_sum (fun i (_ : i∈Finset.univ) => cropEntry_bits ha hc ht k W h hn hp x i)
  simpa only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul] using hh

theorem pad_control (ha : 0<a) (hb : 0<b) (k : ℕ) (x : Table (PaddedMatrix.matrix n m) Cell) :
    (pad (t:=t) ha hb k x).control=t*(a*b)^k*(64+8*(k+1))+8 := by
  have hp (z : Fin t×PowerIndex (Fin a×Fin b) k) : (padEntry k x z).control=24+8*(k+1) := by
    simp only [padEntry]
    split_ifs <;> rfl
  simp only [pad,BinaryRecursiveTable.tabulate_control,BinaryRecursiveDot.tabulate_control,hp,
    Finset.sum_const,Finset.card_univ,Fintype.card_prod,Fintype.card_fin,powerIndex_card,
    smul_eq_mul,BinaryRecursiveTable.layout_size]
  ring

theorem crop_control (ha : 0<a) (hc : 0<c) (ht : 0<t) (k : ℕ)
    (hn : n≤a^k) (hp : p≤c^k) (x : Cells t c a k) :
    (crop ha hc ht k hn hp x).control=n*p*(56+8*(k+1))+8 := by
  simp only [crop,cropEntry,Vector.toList_ofFn,List.map_ofFn,Function.comp_apply,List.sum_ofFn,
    Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
  ring

#print axioms cropEntry_bits
#print axioms crop_bits
#print axioms pad_control
#print axioms crop_control

#print axioms component_widths
#print axioms padEntry_bits
#print axioms pad_bits
end ThinMatrix.BinaryAddressedPaddingCosts
