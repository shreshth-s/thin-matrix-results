import WindowSuffixPermutation

set_option autoImplicit false

/-! Retained physical-coordinate tables and binary copies for window reindexing.
Table construction and traversal are indexed-register operations; only ternary
addresses and coefficient copies are priced in bit operations. -/
namespace ThinMatrix.RetainedWindowPermutation
open BinaryCell BinaryGroupedCoordinates BinaryGroupedPreparation CroppedGroupedSuffix OppositeWindowLayer
open scoped BigOperators

structure Layout (N : ℕ) where
  forward : Vector (Fin N) N
  backward : Vector (Fin N) N

def order : (k : ℕ) → ℕ → Bool → Fin (RetainedRootWindows.slots k) → Equiv.Perm (Fin (2*k))
  | 0, _, _, _ => Equiv.refl _
  | k+1, ell, normal, s => WindowSuffixPermutation.permutation (min ell (k+1)) normal s

/-- Each direction is evaluated once at each physical position and retained.
The fixed allowance includes the split, rotation/modulo, branch, array writes
and length arithmetic in this specific coordinate formula. -/
def build (k ell : ℕ) (normal : Bool) (s : Fin (RetainedRootWindows.slots k)) : Run (Layout (2*k)) :=
  let p := order k ell normal s
  ⟨⟨Vector.ofFn p,Vector.ofFn p.symm⟩,0,128*(2*k)+32⟩

@[simp] theorem build_forward (k ell : ℕ) (normal : Bool) (s : Fin (RetainedRootWindows.slots k)) (i : Fin (2*k)) :
    (build k ell normal s).value.forward.get i=order k ell normal s i := by simp [build]
@[simp] theorem build_backward (k ell : ℕ) (normal : Bool) (s : Fin (RetainedRootWindows.slots k)) (i : Fin (2*k)) :
    (build k ell normal s).value.backward.get i=(order k ell normal s).symm i := by simp [build]

def oldWord {N : ℕ} (layout : Layout N) (w : Word N) : Word N := fun i => w (layout.backward.get i)

def reindex {N : ℕ} (layout : Layout N) (w : Vector (Fin 3) N) : Vector (Fin 3) N :=
  GroupedPreparation.ofStoredFn layout.backward (fun i => w.get (layout.backward.get i))

@[simp] theorem reindex_get {N : ℕ} (layout : Layout N) (w : Vector (Fin 3) N) :
    (reindex layout w).get=oldWord layout w.get := by
  funext i
  simp [reindex,oldWord,GroupedPreparation.ofStoredFn_eq]

def row {N C : ℕ} (layout : Layout N) (X : OppositeWindowLayer.Source N C) (i : Fin (3^N)) : Run (Vector Cell C) :=
  let decoded := WindowSelection.decode N i.val
  let word := reindex layout decoded.value
  let address := TernaryWindowAddress.encode word
  let out := tabulate (X.get address.value) (fun c =>
    let copied := copy ((X.get address.value).get c)
    ⟨copied.value,copied.bitSteps,8⟩)
  ⟨out.value,address.bitSteps+out.bitSteps,decoded.work+8*layout.backward.toArray.size+address.control+out.control+16⟩

theorem row_value {N C : ℕ} (layout : Layout N) (X : OppositeWindowLayer.Source N C) (w : Word N) (c : Fin C) :
    view ((row layout X (StoredGroupedCompletion.rawIndex N w)).value.get c)=value X (oldWord layout w) c := by
  simp only [row,tabulate_get,copy_view,TernaryWindowAddress.encode_value,reindex_get,
    WindowSelection.decode_index,Equiv.symm_apply_apply,value]

def execute {N C : ℕ} (layout : Layout N) (X : OppositeWindowLayer.Source N C) : Run (OppositeWindowLayer.Source N C) :=
  tabulate X (fun i => row layout X i)

theorem execute_value {N C : ℕ} (layout : Layout N) (X : OppositeWindowLayer.Source N C) (w : Word N) (c : Fin C) :
    value (execute layout X).value w c=value X (oldWord layout w) c := by
  simp only [execute,value,tabulate_get,row_value]

def rowBitBudget (N C A : ℕ) : ℕ := addressBudget N+C*BackendScalarBits.backendScalarUnit A.size
def rowControlBudget (N C : ℕ) : ℕ := N*(6*N+16)+2+8*N+(40*N+18)+(40*C+8)+16

theorem row_bits {N C : ℕ} (layout : Layout N) (X : OppositeWindowLayer.Source N C) (i : Fin (3^N))
    (A : ℕ) (ha : Bound X A) : (row layout X i).bitSteps≤rowBitBudget N C A := by
  have hd := TernaryWindowAddress.encode_bits (reindex layout (WindowSelection.decode N i.val).value)
  have hc := tabulate_bits (X.get (TernaryWindowAddress.encode (reindex layout (WindowSelection.decode N i.val).value)).value)
    (fun c => let copied := copy ((X.get (TernaryWindowAddress.encode (reindex layout (WindowSelection.decode N i.val).value)).value).get c)
      (⟨copied.value,copied.bitSteps,8⟩ : Run Cell))
    (fun c => copy_price A.size _ (Nat.size_le_size (ha _ c)))
  change _+_≤_
  exact Nat.add_le_add hd hc

theorem row_control {N C : ℕ} (layout : Layout N) (X : OppositeWindowLayer.Source N C) (i : Fin (3^N)) :
    (row layout X i).control≤rowControlBudget N C := by
  have hd := WindowSelection.decode_work N i.val
  have hc := tabulate_control (X.get (TernaryWindowAddress.encode (reindex layout (WindowSelection.decode N i.val).value)).value)
    (fun c => let copied := copy ((X.get (TernaryWindowAddress.encode (reindex layout (WindowSelection.decode N i.val).value)).value).get c)
      (⟨copied.value,copied.bitSteps,8⟩ : Run Cell)) (W:=8) (by intro c; rfl)
  dsimp only at hc
  simp only [row,rowControlBudget,TernaryWindowAddress.encode_control,Vector.size_toArray]
  omega

def bitBudget (N C A : ℕ) : ℕ := 3^N*rowBitBudget N C A
def controlBudget (N C : ℕ) : ℕ := 3^N*(rowControlBudget N C+32)+8

theorem execute_bits {N C : ℕ} (layout : Layout N) (X : OppositeWindowLayer.Source N C) (A : ℕ) (ha : Bound X A) :
    (execute layout X).bitSteps≤bitBudget N C A := tabulate_bits _ _ (fun i => row_bits layout X i A ha)

theorem execute_control {N C : ℕ} (layout : Layout N) (X : OppositeWindowLayer.Source N C) :
    (execute layout X).control≤controlBudget N C := tabulate_control _ _ (fun i => row_control layout X i)

theorem execute_bound {N C : ℕ} (layout : Layout N) (X : OppositeWindowLayer.Source N C) (A : ℕ) (ha : Bound X A) :
    Bound (execute layout X).value A := by
  intro i c
  have h := execute_value layout X ((StoredGroupedCompletion.rawIndex N).symm i) c
  simp only [value,Equiv.apply_symm_apply] at h
  rw [h]
  exact ha _ c

structure Prepared (k C : ℕ) where
  layout : Layout (2*k)
  coefficients : OppositeWindowLayer.Source (2*k) C

def prepare {k C : ℕ} (ell : ℕ) (normal : Bool) (s : Fin (RetainedRootWindows.slots k))
    (X : OppositeWindowLayer.Source (2*k) C) : Run (Prepared k C) :=
  let layout := build k ell normal s
  let out := execute layout.value X
  ⟨⟨layout.value,out.value⟩,out.bitSteps,layout.control+out.control+8⟩

theorem prepare_value {k C : ℕ} (ell : ℕ) (normal : Bool) (s : Fin (RetainedRootWindows.slots k))
    (X : OppositeWindowLayer.Source (2*k) C) (w : Word (2*k)) (c : Fin C) :
    value (prepare ell normal s X).value.coefficients w c=value X (fun i => w ((order k ell normal s).symm i)) c := by
  change value (execute (build k ell normal s).value X).value w c=_
  rw [execute_value]
  congr 1
  funext i
  exact congrArg w (build_backward k ell normal s i)

theorem prepare_bound {k C : ℕ} (ell : ℕ) (normal : Bool) (s : Fin (RetainedRootWindows.slots k))
    (X : OppositeWindowLayer.Source (2*k) C) (A : ℕ) (ha : Bound X A) :
    Bound (prepare ell normal s X).value.coefficients A := execute_bound _ _ A ha

theorem prepare_bits {k C : ℕ} (ell : ℕ) (normal : Bool) (s : Fin (RetainedRootWindows.slots k))
    (X : OppositeWindowLayer.Source (2*k) C) (A : ℕ) (ha : Bound X A) :
    (prepare ell normal s X).bitSteps≤bitBudget (2*k) C A := execute_bits _ _ A ha

theorem prepare_control {k C : ℕ} (ell : ℕ) (normal : Bool) (s : Fin (RetainedRootWindows.slots k))
    (X : OppositeWindowLayer.Source (2*k) C) :
    (prepare ell normal s X).control≤128*(2*k)+40+controlBudget (2*k) C := by
  have h := execute_control (build k ell normal s).value X
  simp only [build] at h
  simp only [prepare,build]
  omega

/-- Exact rare-symbol suffix cap, with ell clamped by the executable program. -/
theorem prepare_support {k C : ℕ} [NeZero k] (ell cap : ℕ) (normal : Bool)
    (s : Fin (RetainedRootWindows.slots k)) (X : OppositeWindowLayer.Source (2*k) C)
    (hs : ∀ w c, cap<CyclicLightWindow.weight (min ell k) (BinaryWindowPartition.bits normal w)
      ⟨s.val,by cases k with | zero => exact (NeZero.ne 0 rfl).elim | succ k => exact s.isLt⟩ → value X w c=0)
    (w : Word (2*k)) (c : Fin C)
    (hw : cap<∑ j : Fin (min ell k), if w (WindowSuffixPermutation.suffixIndex
      ((Nat.min_le_right ell k).trans (by omega)) j)=2 then 1 else 0) :
    value (prepare ell normal s X).value.coefficients w c=0 := by
  rw [prepare_value]
  cases k with
  | zero => exact (NeZero.ne 0 rfl).elim
  | succ k =>
    change Fin (k+1) at s
    apply hs
    change cap<CyclicLightWindow.weight (min ell (k+1)) _ s
    simpa only [order,WindowSuffixPermutation.suffix_weight _ (Nat.min_le_right ell (k+1)) normal s w] using hw

def suffixRare (k ell : ℕ) (w : Word (2*k)) : ℕ :=
  ∑ j : Fin (min ell k), if w (WindowSuffixPermutation.suffixIndex
    ((Nat.min_le_right ell k).trans (by omega)) j)=2 then 1 else 0

/-- The actual partition, forward transform and retained permutation compose
without a support assumption, including the empty residual case. -/
theorem partition_support {k C : ℕ} (ell cap cn co : ℕ)
    (X : BinaryWindowPartition.Source k C) (s : Fin (RetainedRootWindows.slots k))
    (w : Word (2*k)) (c : Fin C)
    (hw : (cap-max cn co)*min ell k/k<suffixRare k ell w) :
    value (prepare ell (decide (co≤cn)) s (RetainedOppositeTransform.execute
      ((RetainedRootWindows.partition (min ell k) cap cn co X).value.components.get s)).value.result).value.coefficients w c=0 := by
  cases k with
  | zero =>
    have hz : suffixRare 0 ell w=0 := by
      unfold suffixRare
      apply Finset.sum_eq_zero
      intro j _
      have := j.isLt
      omega
    rw [hz] at hw
    omega
  | succ k =>
    apply prepare_support ell ((cap-max cn co)*min ell (k+1)/(k+1)) (decide (co≤cn)) s _ _ w c hw
    intro word col hp
    change (cap-max cn co)*min ell (k+1)/(k+1)<CyclicLightWindow.weight (min ell (k+1)) (BinaryWindowPartition.bits (decide (co≤cn)) word) s at hp
    have hs := RetainedOppositeTransform.window_supported (min ell (k+1)) cap cn co X s
    apply hs word col
    change ¬CyclicLightWindow.weight (min ell (k+1)) (BinaryWindowPartition.bits (decide (co≤cn)) word) s≤_
    omega

/-- Inverse reindexing recovers every transformed coefficient. -/
theorem prepare_recover {k C : ℕ} (ell : ℕ) (normal : Bool) (s : Fin (RetainedRootWindows.slots k))
    (X : OppositeWindowLayer.Source (2*k) C) (w : Word (2*k)) (c : Fin C) :
    value (prepare ell normal s X).value.coefficients (fun i => w ((prepare ell normal s X).value.layout.forward.get i)) c=
      value X w c := by
  rw [prepare_value]
  simp only [prepare,build_forward,Equiv.apply_symm_apply]

#print axioms partition_support
#print axioms prepare_recover
#print axioms build_forward
#print axioms build_backward
#print axioms reindex_get
#print axioms row_value
#print axioms execute_value
#print axioms row_bits
#print axioms row_control
#print axioms execute_bits
#print axioms execute_control
#print axioms execute_bound
#print axioms prepare_value
#print axioms prepare_bound
#print axioms prepare_bits
#print axioms prepare_control
#print axioms prepare_support
end ThinMatrix.RetainedWindowPermutation
