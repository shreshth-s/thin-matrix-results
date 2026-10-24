import SharedGroupedCompletion
import PrefixCompletionProgram

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! Shared completion on the production prefix-matrix representation. A batch
has common prefix/pair keys, support layout and coefficient width. All original
block columns are explicitly concatenated; no independent products are inferred
from a mask grid. Routing into these batches and the global rounded fit remain
separate obligations. -/
namespace ThinMatrix.PrefixBlockBatch
open scoped BigOperators
open BinaryCell BinaryGroupedCoordinates BinaryGroupedPreparation
open CappedBitPreparation GroupedPreparation
open RectangularBatch (Scheme)

variable {P ell r C B A Z : ℕ}

abbrev Banks (P ell r C B : ℕ) := Vector (PrefixCompletionMatrices.Prepared P ell r C) B

def prepare (xs : Vector (CappedPrefixProgram.Prepared P ell r C) B) : Run (Banks P ell r C B) :=
  tabulate xs (fun b => PrefixCompletionMatrices.prepare (xs.get b))

@[simp] theorem prepare_get (xs : Vector (CappedPrefixProgram.Prepared P ell r C) B) (b : Fin B) :
    (prepare xs).value.get b=(PrefixCompletionMatrices.prepare (xs.get b)).value := by
  simp only [prepare,tabulate_get]

def column (b : Fin B) (c : Fin C) : Fin (B*C) := finProdFinEquiv (b,c)

def data (banks : Banks P ell r C B) (pair : Fin (2^ell)) (digits : Vector (Fin 4) P) :
    Run (Vector (Vector Cell (B*C)) (CappedSubsetList.count ell r)) :=
  let chosen := tabulate banks (fun b =>
    (⟨PrefixCompletionMatrices.read ((banks.get b).get pair) digits.get,0,16*(P+1)^2+8⟩ :
      Run (PrefixCompletionMatrices.Matrix (CappedSubsetList.count ell r) C)))
  let out := tabulate (Vector.replicate (CappedSubsetList.count ell r) ()) (fun j =>
    tabulate (Vector.replicate (B*C) ()) (fun i =>
      let pos := finProdFinEquiv.symm i
      (⟨((chosen.value.get pos.1).get j).get pos.2,0,12⟩ : Run Cell)))
  ⟨out.value,out.bitSteps,chosen.control+out.control+8⟩

theorem data_get (banks : Banks P ell r C B) (pair : Fin (2^ell)) (digits : Vector (Fin 4) P)
    (j : Fin (CappedSubsetList.count ell r)) (b : Fin B) (c : Fin C) :
    (((data banks pair digits).value.get j).get (column b c))=
      ((PrefixCompletionMatrices.read ((banks.get b).get pair) digits.get).get j).get c := by
  simp only [data,tabulate_get,column,Equiv.symm_apply_apply]

theorem data_bits (banks : Banks P ell r C B) (pair : Fin (2^ell)) (digits : Vector (Fin 4) P) :
    (data banks pair digits).bitSteps=0 := by
  simp only [data,tabulate_bits_eq,Finset.sum_const_zero]

theorem data_control (banks : Banks P ell r C B) (pair : Fin (2^ell)) (digits : Vector (Fin 4) P) :
    (data banks pair digits).control=
      B*(16*(P+1)^2+40)+CappedSubsetList.count ell r*(44*(B*C)+40)+24 := by
  simp only [data,tabulate_control_eq,Finset.sum_const,Finset.card_univ,Fintype.card_fin,smul_eq_mul]
  ring

theorem data_prepared (xs : Vector (CappedPrefixProgram.Prepared P ell r C) B)
    (pair : Fin (2^ell)) (digits : Vector (Fin 4) P)
    (j : Fin (CappedSubsetList.count ell r)) (b : Fin B) (c : Fin C) :
    view (((data (prepare xs).value pair digits).value.get j).get (column b c))=
      view (RetainedPrefixEncoder.output (((xs.get b).traces.get pair).get j) digits.get c) := by
  rw [data_get,prepare_get,PrefixCompletionMatrices.prepare_get]

theorem data_bound (xs : Vector (CappedPrefixProgram.Prepared P ell r C) B)
    (H : ℕ) (hH : ∀ b pair, PrefixCompletionMatrices.LeafBound ((xs.get b).traces.get pair) H)
    (pair : Fin (2^ell)) (digits : Vector (Fin 4) P)
    (j : Fin (CappedSubsetList.count ell r)) (c : Fin (B*C)) :
    (view (((data (prepare xs).value pair digits).value.get j).get c)).natAbs≤H := by
  rcases finProdFinEquiv.surjective c with ⟨⟨b,d⟩,rfl⟩
  rw [show finProdFinEquiv (b,d)=column b d from rfl,data_prepared]
  exact hH b pair j digits.get d

theorem prepare_bits (xs : Vector (CappedPrefixProgram.Prepared P ell r C) B)
    (H : ℕ) (hH : ∀ b pair, PrefixCompletionMatrices.LeafBound ((xs.get b).traces.get pair) H) :
    (prepare xs).bitSteps≤B*(2^ell*PrefixCompletionMatrices.bitBudget P (CappedSubsetList.count ell r) C H) :=
  tabulate_bits xs _ (fun b => PrefixCompletionMatrices.prepare_bits _ H (hH b))

theorem prepare_control (xs : Vector (CappedPrefixProgram.Prepared P ell r C) B) :
    (prepare xs).control≤B*(2^ell*(PrefixCompletionMatrices.controlBudget P (CappedSubsetList.count ell r) C+32)+40)+8 := by
  have hh := tabulate_control xs _ (fun b => PrefixCompletionMatrices.prepare_control (xs.get b))
  simpa only [prepare,show 8+32=40 by decide,Nat.add_assoc] using hh

def complete (scheme : Scheme) (hD : 0<CappedSubsetList.count ell r) (hA : 0<A) (hZ : 0<Z)
    (hfirst : (A-1)^scheme.den≤(CappedSubsetList.count ell r)^scheme.num)
    (hlast : Z≤(CappedSubsetList.count ell r)^scheme.z)
    (keys : Vector (Key ell) (CappedSubsetList.count ell r))
    (banks : Banks P ell r C B) (pair : Fin (2^ell)) (digits : Vector (Fin 4) P)
    (requests : Array (Key ell)) : Run (Array (Vector Cell (B*C))) :=
  let masks := GroupedPreparation.selectors keys requests
  let matrix := data banks pair digits
  let out := SharedGroupedCompletion.complete scheme hD hA hZ hfirst hlast masks.value matrix.value
  ⟨out.value,matrix.bitSteps+out.bitSteps,masks.work+matrix.control+out.control+12⟩

@[simp] theorem complete_size (scheme : Scheme) (hD : 0<CappedSubsetList.count ell r) (hA : 0<A) (hZ : 0<Z)
    (hfirst : (A-1)^scheme.den≤(CappedSubsetList.count ell r)^scheme.num)
    (hlast : Z≤(CappedSubsetList.count ell r)^scheme.z)
    (keys : Vector (Key ell) (CappedSubsetList.count ell r))
    (banks : Banks P ell r C B) (pair : Fin (2^ell)) (digits : Vector (Fin 4) P)
    (requests : Array (Key ell)) :
    (complete scheme hD hA hZ hfirst hlast keys banks pair digits requests).value.size=requests.size := by
  simp [complete,SharedGroupedCompletion.complete_size]

theorem complete_value (scheme : Scheme) (hv : scheme.Valid)
    (hD : 0<CappedSubsetList.count ell r) (hA : 0<A) (hZ : 0<Z)
    (hfirst : (A-1)^scheme.den≤(CappedSubsetList.count ell r)^scheme.num)
    (hlast : Z≤(CappedSubsetList.count ell r)^scheme.z)
    (xs : Vector (CappedPrefixProgram.Prepared P ell r C) B)
    (keys : Vector (Key ell) (CappedSubsetList.count ell r))
    (hk : ∀ b, (xs.get b).grouped.keys=keys)
    (pair : Fin (2^ell)) (digits : Vector (Fin 4) P) (requests : Array (Key ell))
    (i : Fin requests.size) (b : Fin B) (c : Fin C) :
    view (((complete scheme hD hA hZ hfirst hlast keys (prepare xs).value pair digits requests).value[i.val]'(by simp)).get (column b c))=
      CappedPrefixProgram.query (xs.get b) pair digits.get (support requests[i.val]) c := by
  have hh := SharedGroupedCompletion.complete_correct scheme hv hD hA hZ hfirst hlast
    (GroupedPreparation.selectors keys requests).value (data (prepare xs).value pair digits).value
    ⟨i.val,by simpa only [GroupedPreparation.selectors_size] using i.isLt⟩ (column b c)
  change view _=_ at hh
  simp only [complete]
  rw [hh]
  unfold CappedPrefixProgram.query
  rw [hk b]
  apply Finset.sum_congr rfl
  intro j _
  rw [GroupedPreparation.selectors_get keys requests i.val i.isLt, data_prepared]
  simp

theorem complete_bits (scheme : Scheme)
    (hD : 0<CappedSubsetList.count ell r) (hA : 0<A) (hZ : 0<Z)
    (hfirst : (A-1)^scheme.den≤(CappedSubsetList.count ell r)^scheme.num)
    (hlast : Z≤(CappedSubsetList.count ell r)^scheme.z)
    (xs : Vector (CappedPrefixProgram.Prepared P ell r C) B)
    (keys : Vector (Key ell) (CappedSubsetList.count ell r))
    (H : ℕ) (hH : 1≤H) (hx : ∀ b pair, PrefixCompletionMatrices.LeafBound ((xs.get b).traces.get pair) H)
    (pair : Fin (2^ell)) (digits : Vector (Fin 4) P) (requests : Array (Key ell)) :
    (complete scheme hD hA hZ hfirst hlast keys (prepare xs).value pair digits requests).bitSteps≤
      CompactBlocks.blockCount requests.size A*CompactBlocks.blockCount (B*C) Z*
        RectangularBatch.scalarBudget scheme (CappedSubsetList.count ell r) H := by
  have hh := SharedGroupedCompletion.complete_bits scheme hD hA hZ hfirst hlast
    (GroupedPreparation.selectors keys requests).value (data (prepare xs).value pair digits).value
    H hH (data_bound xs H hx pair digits)
  simpa only [complete,data_bits,zero_add,GroupedPreparation.selectors_size] using hh

theorem complete_control (scheme : Scheme)
    (hD : 0<CappedSubsetList.count ell r) (hA : 0<A) (hZ : 0<Z)
    (hfirst : (A-1)^scheme.den≤(CappedSubsetList.count ell r)^scheme.num)
    (hlast : Z≤(CappedSubsetList.count ell r)^scheme.z)
    (keys : Vector (Key ell) (CappedSubsetList.count ell r))
    (banks : Banks P ell r C B) (pair : Fin (2^ell)) (digits : Vector (Fin 4) P)
    (requests : Array (Key ell)) :
    (complete scheme hD hA hZ hfirst hlast keys banks pair digits requests).control≤
      (SharedGroupedCompletion.complete scheme hD hA hZ hfirst hlast
        (GroupedPreparation.selectors keys requests).value (data banks pair digits).value).control+
      requests.size*(CappedSubsetList.count ell r*(26*ell+24)+20)+
      B*(16*(P+1)^2+40)+CappedSubsetList.count ell r*(44*(B*C)+40)+40 := by
  have hh := GroupedPreparation.selectors_work keys requests
  simp only [complete,data_control]
  omega

/-- The only long-axis supply used here is the actual B-by-C column array. -/
theorem independent_fit (M B C A Z : ℕ) (hA : 0<A) (hZ : 0<Z) (hfit : Z≤B*C) :
    CompactBlocks.blockCount M A*CompactBlocks.blockCount (B*C) Z*A*Z≤2*(M+A)*(B*C) :=
  RectangularBatch.batch_fit M (B*C) A Z hA hZ hfit

#print axioms prepare_get
#print axioms data_get
#print axioms data_bits
#print axioms data_control
#print axioms data_prepared
#print axioms data_bound
#print axioms prepare_bits
#print axioms prepare_control
#print axioms complete_size
#print axioms complete_value
#print axioms complete_bits
#print axioms complete_control
#print axioms independent_fit
end ThinMatrix.PrefixBlockBatch
