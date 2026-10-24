import SharedCompletionTile
import FullyRetainedRootBatch
import SharedFullyPrefixPrices

set_option autoImplicit false
set_option maxHeartbeats 1800000
namespace ThinMatrix.AutoFullyRetainedRootBatch
open BinaryCell BinaryGroupedCoordinates
open RectangularBatch (Scheme)
open FullyRetainedRootBatch (Bank Sources)
open scoped BigOperators

structure Tile (scheme : Scheme) (s : ℕ) where
  A : ℕ
  Z : ℕ
  hA : 0 < A
  hZ : 0 < Z
  first : (A-1)^scheme.den ≤ s^scheme.num
  last : Z ≤ s^scheme.z
  A_eq : A=SharedCompletionTile.row s
  Z_eq : Z=SharedCompletionTile.col s

/-- Binary tile setup is retained independently of source banks, so the
same per-support shape can be passed to every own-band root call. -/
def prepare (scheme : Scheme) (hnum : scheme.num=861) (hden : scheme.den=500)
    (hz : scheme.z=15) (s : ℕ) (hs : 0 < s) : Result (Tile scheme s) :=
  let out := SharedCompletionTile.execute s
  have hA : out.value.1=SharedCompletionTile.row s := congrArg Prod.fst (SharedCompletionTile.execute_value s)
  have hZ : out.value.2=SharedCompletionTile.col s := congrArg Prod.snd (SharedCompletionTile.execute_value s)
  let dims := SharedCompletionTile.dimensions s hs
  ⟨⟨out.value.1,out.value.2,by rw [hA];exact dims.1,by rw [hZ];exact dims.2.1,
    by rw [hA,hden,hnum];exact SharedCompletionTile.integer_fit s hs,
    by rw [hZ,hz];exact le_refl _,hA,hZ⟩,out.bitSteps+8⟩

theorem prepare_bits (scheme : Scheme) (hnum : scheme.num=861) (hden : scheme.den=500)
    (hz : scheme.z=15) (s : ℕ) (hs : 0 < s) :
    (prepare scheme hnum hden hz s hs).bitSteps ≤ SharedCompletionTile.bitBudget s+8 :=
  Nat.add_le_add_right (SharedCompletionTile.execute_bits s) 8

theorem prepare_absorbed (scheme : Scheme) (hnum : scheme.num=861) (hden : scheme.den=500)
    (hz : scheme.z=15) (s Q : ℕ) (hs : 0 < s) (hf : SharedCompletionTile.col s ≤ Q) :
    (prepare scheme hnum hden hz s hs).bitSteps ≤ 1000000000000000*Q*(s.size+2)^2+8 :=
  Nat.add_le_add_right (SharedCompletionTile.setup_absorbed s Q hs hf) 8

variable {k ell total cn co C B W : ℕ}

def executeWith (scheme : Scheme) (hD : 0 < WindowSharedCompletion.D k ell total cn co)
    (tile : Tile scheme (WindowSharedCompletion.D k ell total cn co))
    (banks : Vector (Bank k ell total cn co C B) W)
    (layouts : Vector (RetainedWindowPermutation.Layout (2*k)) W)
    (labels : Array (Vector (Fin 4) (2*k))) :=
  FullyRetainedRootBatch.execute scheme hD tile.hA tile.hZ tile.first tile.last banks layouts labels

def execute (scheme : Scheme) (hnum : scheme.num=861) (hden : scheme.den=500) (hz : scheme.z=15)
    (hD : 0 < WindowSharedCompletion.D k ell total cn co)
    (banks : Vector (Bank k ell total cn co C B) W)
    (layouts : Vector (RetainedWindowPermutation.Layout (2*k)) W)
    (labels : Array (Vector (Fin 4) (2*k))) :=
  let tile := prepare scheme hnum hden hz _ hD
  let out := executeWith scheme hD tile.value banks layouts labels
  { out with bitSteps := tile.bitSteps+out.bitSteps,control := out.control+16 }

theorem execute_value (scheme : Scheme) (hnum : scheme.num=861) (hden : scheme.den=500) (hz : scheme.z=15)
    (hD : 0 < WindowSharedCompletion.D k ell total cn co)
    (banks : Vector (Bank k ell total cn co C B) W)
    (layouts : Vector (RetainedWindowPermutation.Layout (2*k)) W)
    (labels : Array (Vector (Fin 4) (2*k))) :
    (execute scheme hnum hden hz hD banks layouts labels).value=
      (executeWith scheme hD (prepare scheme hnum hden hz _ hD).value banks layouts labels).value := rfl

theorem correct (scheme : Scheme) (hv : scheme.Valid)
    (hD : 0 < WindowSharedCompletion.D k ell total cn co)
    (tile : Tile scheme (WindowSharedCompletion.D k ell total cn co))
    (xs : Vector (Sources k ell total cn co C B) W)
    (banks : Vector (Bank k ell total cn co C B) W)
    (hb : ∀ s,banks.get s=(SharedPrefixSourceBank.prepare (xs.get s)).value)
    (hk : ∀ s b,((xs.get s).get b).grouped.keys=GroupedPreparation.keyVector
      (WindowPrefixProgram.length k ell) (WindowPrefixProgram.cap k ell total cn co))
    (hp : ∀ s b,((xs.get s).get b).grouped.pairs=GroupedPreparation.pairKeys (WindowPrefixProgram.length k ell))
    (layouts : Vector (RetainedWindowPermutation.Layout (2*k)) W)
    (labels : Array (Vector (Fin 4) (2*k))) (j : Fin labels.size) (b : Fin B) (c : Fin C) :
    view ((RootProductCollection.output (executeWith scheme hD tile banks layouts labels).value j).get
      (PrefixBlockBatch.column b c))=
      ∑ s,view ((PrefixCompletionProgram.row ((xs.get s).get b)
        (PrefixCompletionMatrices.prepare ((xs.get s).get b)).value
        ((WindowCompletionRequests.requests ell (layouts.get s) labels).value[j.val]'(by simp))).value.output.get c) :=
  FullyRetainedRootBatch.correct scheme hv hD tile.hA tile.hZ tile.first tile.last xs banks hb hk hp layouts labels j b c

theorem priced_setup (scheme : Scheme) (hnum : scheme.num=861) (hden : scheme.den=500) (hz : scheme.z=15)
    (hD : 0 < WindowSharedCompletion.D k ell total cn co)
    (banks : Vector (Bank k ell total cn co C B) W)
    (layouts : Vector (RetainedWindowPermutation.Layout (2*k)) W)
    (labels : Array (Vector (Fin 4) (2*k))) (price : ℕ) :
    (execute scheme hnum hden hz hD banks layouts labels).bitSteps+
      price*(execute scheme hnum hden hz hD banks layouts labels).control=
    (prepare scheme hnum hden hz _ hD).bitSteps+
      (executeWith scheme hD (prepare scheme hnum hden hz _ hD).value banks layouts labels).bitSteps+
      price*(executeWith scheme hD (prepare scheme hnum hden hz _ hD).value banks layouts labels).control+16*price := by
  simp only [execute]
  ring

theorem priced_children (scheme : Scheme) (hv : scheme.Valid)
    (hD : 0 < WindowSharedCompletion.D k ell total cn co)
    (tile : Tile scheme (WindowSharedCompletion.D k ell total cn co))
    (xs : Vector (Sources k ell total cn co C B) W)
    (banks : Vector (Bank k ell total cn co C B) W)
    (hb : ∀ s,banks.get s=(SharedPrefixSourceBank.prepare (xs.get s)).value)
    (hk : ∀ s b,((xs.get s).get b).grouped.keys=GroupedPreparation.keyVector
      (WindowPrefixProgram.length k ell) (WindowPrefixProgram.cap k ell total cn co))
    (hp : ∀ s b,((xs.get s).get b).grouped.pairs=GroupedPreparation.pairKeys (WindowPrefixProgram.length k ell))
    (H : ℕ) (hx : ∀ s b pair,PrefixCompletionMatrices.LeafBound (((xs.get s).get b).traces.get pair) H)
    (layouts : Vector (RetainedWindowPermutation.Layout (2*k)) W)
    (labels : Array (Vector (Fin 4) (2*k))) (price : ℕ) :
    (executeWith scheme hD tile banks layouts labels).bitSteps+
      price*(executeWith scheme hD tile banks layouts labels).control ≤
      (∑ s,((FullyRetainedWindowBatch.execute scheme hD tile.hA tile.hZ tile.first tile.last (banks.get s) (layouts.get s) labels).bitSteps+
        price*(FullyRetainedWindowBatch.execute scheme hD tile.hA tile.hZ tile.first tile.last (banks.get s) (layouts.get s) labels).control))+
      labels.size*(W*((B*C)*BackendScalarBits.backendScalarUnit (W*(WindowSharedCompletion.D k ell total cn co*H)).size))+
      price*SharedFullyPrefixPrices.rootExtra W labels.size (B*C) := by
  apply SharedFullyPrefixPrices.root_price
  intro s j c
  rw [hb s]
  exact FullyRetainedRootBatch.child_bound scheme hv hD tile.hA tile.hZ tile.first tile.last _ (hk s) (hp s) H (hx s) _ _ _ _

#print axioms prepare_bits
#print axioms prepare_absorbed
#print axioms execute_value
#print axioms correct
#print axioms priced_setup
#print axioms priced_children
end ThinMatrix.AutoFullyRetainedRootBatch
