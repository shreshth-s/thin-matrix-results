import ResidualWindowSupport

set_option autoImplicit false

/-! Actual retained roots through binary channel-weight computation, full
coefficient copies and lossless first-window partition. The zero residual
case retains one copied component and does not run a window search. -/
namespace ThinMatrix.RetainedRootWindows
open WalshEmbedding BinaryCell BinaryGroupedCoordinates BinaryGroupedPreparation
open BinaryCroppedHighInput ResidualFamilyKeys RetainedResidualFamily
open scoped BigOperators

def count {m : ℕ} (v : Vector Bool m) : Run ℕ :=
  let counted := countBits v.toList
  let decoded := BinaryModularCell.decodeUnsigned counted.value
  ⟨decoded.value,counted.bitSteps+decoded.bitSteps,8*v.toArray.size+8⟩

theorem count_value {m : ℕ} (v : Vector Bool m) : (count v).value=ones v.get := by
  simp only [count,BinaryModularCell.decodeUnsigned_value,countBits_view,Int.natAbs_natCast,
    BinaryResidualDegreeSpace.toList_get,bitCount_ofFn]

def countBudget (m : ℕ) : ℕ := m*(BackendScalarBits.backendScalarUnit (m.size+1)+4)+1+8*(m.size+1)^2

theorem count_bits {m : ℕ} (v : Vector Bool m) : (count v).bitSteps≤countBudget m := by
  have hc := countBits_price v.toList m (by simp)
  have hd := BinaryModularCell.decodeUnsigned_price m.size (countBits v.toList).value (by
    rw [countBits_view,Int.natAbs_natCast]
    exact Nat.size_le_size (by simpa using bitCount_le v.toList))
  simp only [count,countBudget,Vector.length_toList] at *
  omega

theorem count_control {m : ℕ} (v : Vector Bool m) : (count v).control=8*m+8 := by simp [count]

def weights {m : ℕ} (c : Channel m) : Run (ℕ×ℕ) :=
  let a := count (normal c)
  let b := count (opposite c)
  ⟨(a.value,b.value),a.bitSteps+b.bitSteps,a.control+b.control+16*m+8⟩

theorem weights_value {m : ℕ} (c : Channel m) :
    (weights c).value=(ones (normal c).get,ones (opposite c).get) := by simp [weights,count_value]

theorem weights_bits {m : ℕ} (c : Channel m) : (weights c).bitSteps≤2*countBudget m := by
  have ha := count_bits (normal c)
  have hb := count_bits (opposite c)
  simp only [weights]
  omega

theorem weights_control {m : ℕ} (c : Channel m) : (weights c).control=32*m+24 := by
  simp only [weights,count_control]
  omega

def slots : ℕ → ℕ | 0 => 1 | k+1 => k+1

structure Partition (k C : ℕ) where
  owners : Option (Vector (Option (Fin k)) (3^(2*k)))
  components : Vector (BinaryWindowPartition.Source k C) (slots k)

def partition {C : ℕ} : {k : ℕ} → ℕ → ℕ → ℕ → ℕ → BinaryWindowPartition.Source k C → Run (Partition k C)
  | 0, _, _, _, _, X =>
      let out := BinaryWindowPartition.executeZero X
      ⟨⟨none,out.value⟩,out.bitSteps,out.control+8⟩
  | _+1, ell, cap, cn, co, X =>
      let out := BinaryWindowPartition.prepare ell cap cn co X
      ⟨⟨some out.value.owners,out.value.components⟩,out.bitSteps,out.control+8⟩

def Supported {k C : ℕ} (cap cn co : ℕ) (X : BinaryWindowPartition.Source k C) : Prop :=
  ∀ w c, BinaryWindowPartition.sourceValue X w c≠0 →
    CyclicLightWindow.count (BinaryWindowPartition.bits (decide (co≤cn)) w)≤cap-max cn co

theorem partition_reconstruct {k C : ℕ} (ell cap cn co : ℕ) (X : BinaryWindowPartition.Source k C)
    (hs : Supported cap cn co X) (w : CroppedGroupedSuffix.Word (2*k)) (c : Fin C) :
    (∑ s, BinaryWindowPartition.sourceValue ((partition ell cap cn co X).value.components.get s) w c)=
      BinaryWindowPartition.sourceValue X w c := by
  cases k with
  | zero =>
    simp only [partition,slots,Fintype.sum_unique]
    rw [show (default : Fin 1)=0 from Subsingleton.elim _ _]
    exact BinaryWindowPartition.executeZero_get X w c
  | succ k =>
    change (∑ s, BinaryWindowPartition.sourceValue ((BinaryWindowPartition.execute ell (cap-max cn co)
      (decide (co≤cn)) X).value.components.get s) w c)=_
    rw [BinaryWindowPartition.reconstruct]
    by_cases hz : BinaryWindowPartition.sourceValue X w c=0
    · simp [hz]
    · simp [hs w c hz]

theorem partition_supported {k C : ℕ} [NeZero k] (ell cap cn co : ℕ) (X : BinaryWindowPartition.Source k C)
    (s : Fin (slots k)) (w : CroppedGroupedSuffix.Word (2*k)) (c : Fin C)
    (h : (cap-max cn co)*ell/k<CyclicLightWindow.weight ell (BinaryWindowPartition.bits (decide (co≤cn)) w)
      ⟨s.val,by cases k with | zero => exact (NeZero.ne 0 rfl).elim | succ k => exact s.isLt⟩) :
    BinaryWindowPartition.sourceValue ((partition ell cap cn co X).value.components.get s) w c=0 := by
  cases k with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ k => exact BinaryWindowPartition.window_supported ell _ _ X s w c h

def partitionBitBudget (k C A : ℕ) : ℕ := slots k*3^(2*k)*(C*BackendScalarBits.backendScalarUnit A.size)
def partitionControlBudget (k C ell : ℕ) : ℕ := match k with
  | 0 => 36*C+64
  | k+1 => BinaryWindowPartition.controlBudget (k+1) C ell+16

theorem partition_bits {k C : ℕ} (ell cap cn co : ℕ) (X : BinaryWindowPartition.Source k C)
    (A : ℕ) (ha : BinaryWindowPartition.InputBound X A) :
    (partition ell cap cn co X).bitSteps≤partitionBitBudget k C A := by
  cases k with
  | zero => simpa only [partition,partitionBitBudget,slots,Nat.mul_zero,pow_zero,Nat.one_mul] using BinaryWindowPartition.executeZero_bits X A ha
  | succ k => exact BinaryWindowPartition.execute_bits ell _ _ X A ha

theorem partition_control {k C : ℕ} (ell cap cn co : ℕ) (X : BinaryWindowPartition.Source k C) :
    (partition ell cap cn co X).control≤partitionControlBudget k C ell := by
  cases k with
  | zero => exact Nat.add_le_add_right (BinaryWindowPartition.executeZero_control X) 8
  | succ k => exact Nat.add_le_add_right (Nat.add_le_add_right (BinaryWindowPartition.execute_control ell _ _ X) 8) 8

structure Prepared (L m C : ℕ) where
  counts : ℕ×ℕ
  source : BinaryWindowPartition.Source (L-m) ((m+1)*C)
  windows : Partition (L-m) ((m+1)*C)

def execute {L m C : ℕ} (ell : ℕ) (e : Entry L m C) : Run (Prepared L m C) :=
  let counts := weights e.channel
  let source := ResidualWindowSource.execute e
  let windows := partition ell (m/2) counts.value.1 counts.value.2 source.value
  ⟨⟨counts.value,source.value,windows.value⟩,counts.bitSteps+source.bitSteps+windows.bitSteps,
    counts.control+source.control+windows.control+12⟩

theorem produce_reconstruct {L m C : ℕ} [NeZero C] (ell : ℕ) (raw : BinarySourceFormation.RawStore L C)
    (a b : Mask L m) (c : Channel m) (w : CroppedGroupedSuffix.Word (2*(L-m))) (d : Fin (m+1)) (r : Fin C) :
    (∑ s, BinaryWindowPartition.sourceValue ((execute ell (produce raw a b c).value).value.windows.components.get s)
      w (finProdFinEquiv (d,r)))=
        BinaryResidualPolynomial.cellView ((ResidualWindowSource.rows (produce raw a b c).value).get
          (StoredGroupedCompletion.rawIndex _ w)) d r := by
  have hs := ResidualWindowSupport.selected_support raw a b c
  have h := partition_reconstruct ell (m/2) (ones (normal c).get) (ones (opposite c).get)
    (ResidualWindowSource.execute (produce raw a b c).value).value hs w (finProdFinEquiv (d,r))
  simpa only [execute,weights_value,produce,BinaryWindowPartition.sourceValue,ResidualWindowSource.execute_get] using h

def bitBudget (L m C A : ℕ) : ℕ :=
  2*countBudget m+ResidualWindowSource.bitBudget L m C A+partitionBitBudget (L-m) ((m+1)*C) A

def controlBudget (L m C ell : ℕ) : ℕ :=
  32*m+24+ResidualWindowSource.controlBudget L m C+partitionControlBudget (L-m) ((m+1)*C) ell+12

theorem execute_bits {L m C : ℕ} (ell : ℕ) (e : Entry L m C) (A : ℕ) (ha : ResidualWindowSource.BoundRows e A) :
    (execute ell e).bitSteps≤bitBudget L m C A := by
  have hc := weights_bits e.channel
  have hs := ResidualWindowSource.execute_bits e A ha
  have hw := partition_bits ell (m/2) (weights e.channel).value.1 (weights e.channel).value.2
    (ResidualWindowSource.execute e).value A (ResidualWindowSource.execute_bound e A ha)
  simp only [execute,bitBudget]
  omega

theorem execute_control {L m C : ℕ} (ell : ℕ) (e : Entry L m C) :
    (execute ell e).control≤controlBudget L m C ell := by
  have hs := ResidualWindowSource.execute_control e
  have hw := partition_control ell (m/2) (weights e.channel).value.1 (weights e.channel).value.2
    (ResidualWindowSource.execute e).value
  simp only [execute,controlBudget,weights_control]
  omega

theorem partition_magnitude {k C : ℕ} (ell cap cn co : ℕ) (X : BinaryWindowPartition.Source k C)
    (A : ℕ) (ha : BinaryWindowPartition.InputBound X A) (s : Fin (slots k)) :
    BinaryWindowPartition.InputBound ((partition ell cap cn co X).value.components.get s) A := by
  cases k with
  | zero =>
    change Fin 1 at s
    have he : s=0 := Subsingleton.elim _ _
    subst s
    intro i c
    have hh := BinaryWindowPartition.executeZero_get X ((StoredGroupedCompletion.rawIndex 0).symm i) c
    simp only [BinaryWindowPartition.sourceValue,Equiv.apply_symm_apply] at hh
    change (view ((((BinaryWindowPartition.executeZero X).value.get 0).get i).get c)).natAbs≤A
    rw [hh]
    exact ha i c
  | succ k => exact BinaryWindowPartition.execute_magnitude ell _ _ X A ha s

theorem execute_magnitude {L m C : ℕ} (ell : ℕ) (e : Entry L m C) (A : ℕ)
    (ha : ResidualWindowSource.BoundRows e A) (s : Fin (slots (L-m))) :
    BinaryWindowPartition.InputBound ((execute ell e).value.windows.components.get s) A :=
  partition_magnitude ell (m/2) _ _ _ A (ResidualWindowSource.execute_bound e A ha) s

theorem produce_contraction {L m C : ℕ} [NeZero C] (ell : ℕ) (raw : BinarySourceFormation.RawStore L C)
    (a b : Mask L m) (c : Channel m) (K : CroppedGroupedSuffix.Word (2*(L-m)) → ℤ)
    (d : Fin (m+1)) (r : Fin C) :
    (∑ s, ∑ w, K w*BinaryWindowPartition.sourceValue
      ((execute ell (produce raw a b c).value).value.windows.components.get s) w (finProdFinEquiv (d,r)))=
      ∑ w, K w*BinaryResidualPolynomial.cellView ((ResidualWindowSource.rows (produce raw a b c).value).get
        (StoredGroupedCompletion.rawIndex _ w)) d r := by
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum,produce_reconstruct]

/-- This includes the retained flat source as well as every window component.
The original block array remains in the enclosing graph-root record. -/
def coefficientCells {L m C : ℕ} (out : Prepared L m C) : ℕ :=
  (out.source.toList.map (fun row => row.toArray.size)).sum+
    (out.windows.components.toList.map (fun part => (part.toList.map (fun row => row.toArray.size)).sum)).sum

theorem coefficientCells_eq {L m C : ℕ} (out : Prepared L m C) :
    coefficientCells out=(1+slots (L-m))*3^(2*(L-m))*((m+1)*C) := by
  simp only [coefficientCells,Vector.size_toArray,List.map_const',Vector.length_toList,List.sum_replicate,smul_eq_mul]
  ring

theorem zero_owners {L m C : ℕ} (ell : ℕ) (e : Entry L m C) (hk : L-m=0) :
    (execute ell e).value.windows.owners=none := by
  have hz {k D : ℕ} (X : BinaryWindowPartition.Source k D) (cn co cap : ℕ) (h : k=0) :
      (partition ell cap cn co X).value.owners=none := by
    subst k
    rfl
  exact hz _ _ _ _ hk

#print axioms partition_magnitude
#print axioms execute_magnitude
#print axioms produce_contraction
#print axioms coefficientCells_eq
#print axioms zero_owners
#print axioms count_value
#print axioms count_bits
#print axioms count_control
#print axioms weights_value
#print axioms weights_bits
#print axioms weights_control
#print axioms partition_reconstruct
#print axioms partition_supported
#print axioms partition_bits
#print axioms partition_control
#print axioms produce_reconstruct
#print axioms execute_bits
#print axioms execute_control
end ThinMatrix.RetainedRootWindows
