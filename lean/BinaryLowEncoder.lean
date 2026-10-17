import BinaryCell
import CacheSchemaBitBounds
import BinaryLowQuery
import BinaryHighExecution

/-!
# Actual binary coefficient-array LOW encoder

Every coefficient is a canonical signed-bit cell. The thirteen local row
instructions consume bits read from the stored parent array and produce new
binary cells through charged binary arithmetic. Integer arrays are proof
projections only. Per-cell charges are stored beside the formed binary block,
so accumulating the final counter never reruns a coefficient operation.

Public finite-index control, native natural counters and nested vector/trie
addresses use the same controller as the native encoder. The returned ledger
combines actual scalar bit circuits with controller visits; translating these
visits to a complete machine execution remains a separate refinement.
-/
namespace ThinMatrix.BinaryLowEncoder
open CacheBounds CappedEnumeration SharedEncoder
open scoped BigOperators
set_option maxHeartbeats 3000000
set_option maxRecDepth 10000

namespace DenseRun
universe u v w

variable {A : Type u} {B : Type v} {C : Type w}

def mapDense (f : A → B) (n : ℕ) (dims : Fin n → ℕ)
    (input : SharedEncoder.Dense (R := A) n dims) : SharedEncoder.Dense (R := B) n dims :=
  SharedEncoder.materialize n dims (fun x => f (SharedEncoder.read n dims input x))

@[simp] theorem read_mapDense (f : A → B) (n : ℕ) (dims : Fin n → ℕ)
    (input : SharedEncoder.Dense (R := A) n dims) (x : Coordinates dims) :
    SharedEncoder.read n dims (mapDense f n dims input) x =
      f (SharedEncoder.read n dims input x) :=
  SharedEncoder.read_materialize n dims _ x

theorem mapDense_id (n : ℕ) (dims : Fin n → ℕ)
    (input : SharedEncoder.Dense (R := A) n dims) : mapDense id n dims input = input := by
  apply CacheDenseLowering.dense_ext
  intro x
  simp

theorem mapDense_comp (f : A → B) (g : B → C) (n : ℕ) (dims : Fin n → ℕ)
    (input : SharedEncoder.Dense (R := A) n dims) :
    mapDense g n dims (mapDense f n dims input) = mapDense (g ∘ f) n dims input := by
  apply CacheDenseLowering.dense_ext
  intro x
  simp

def mapNode (f : A → B) {N n : ℕ} (dims : Fin n → ℕ)
    (node : SharedEncoder.Node (R := A) N n dims) : SharedEncoder.Node (R := B) N n dims :=
  ⟨node.word, mapDense f n dims node.data⟩

@[simp] theorem mapNode_word (f : A → B) {N n : ℕ} (dims : Fin n → ℕ)
    (node : SharedEncoder.Node (R := A) N n dims) :
    (mapNode f dims node).word = node.word := rfl

@[simp] theorem read_mapNode (f : A → B) {N n : ℕ} (dims : Fin n → ℕ)
    (node : SharedEncoder.Node (R := A) N n dims) (x : Coordinates dims) :
    SharedEncoder.read n dims (mapNode f dims node).data x =
      f (SharedEncoder.read n dims node.data x) := read_mapDense f n dims node.data x

theorem mapNode_comp (f : A → B) (g : B → C) {N n : ℕ} (dims : Fin n → ℕ)
    (node : SharedEncoder.Node (R := A) N n dims) :
    mapNode g dims (mapNode f dims node) = mapNode (g ∘ f) dims node := by
  cases node
  simp only [mapNode, mapDense_comp]

def mapStored (f : A → B) {N : ℕ} (s : SharedEncoder.Stored A N) : SharedEncoder.Stored B N :=
  ⟨s.depth, s.remaining, s.dims, mapNode f s.dims s.node⟩

@[simp] theorem mapStored_depth (f : A → B) {N : ℕ} (s : SharedEncoder.Stored A N) :
    (mapStored f s).depth = s.depth := rfl

@[simp] theorem mapStored_remaining (f : A → B) {N : ℕ} (s : SharedEncoder.Stored A N) :
    (mapStored f s).remaining = s.remaining := rfl

@[simp] theorem mapStored_word (f : A → B) {N : ℕ} (s : SharedEncoder.Stored A N) :
    (mapStored f s).node.word = s.node.word := rfl

@[simp] theorem mapStored_shape (f : A → B) {N : ℕ} (s : SharedEncoder.Stored A N)
    (L : ℕ) (side : Bool) :
    Shape L side (mapStored f s).depth (mapStored f s).remaining (mapStored f s).dims ↔
      Shape L side s.depth s.remaining s.dims := Iff.rfl

def mapResult (f : A → B) {N : ℕ} (r : SharedEncoder.Result A N) : SharedEncoder.Result B N :=
  { leaves := r.leaves.map (fun leaf => (leaf.1, f leaf.2))
    formed := r.formed.map (mapStored f)
    coefficientWork := r.coefficientWork
    capWork := r.capWork
    coefficientCells := r.coefficientCells }

@[simp] theorem mapResult_leaves (f : A → B) {N : ℕ} (r : SharedEncoder.Result A N) :
    (mapResult f r).leaves = r.leaves.map (fun leaf => (leaf.1, f leaf.2)) := rfl

@[simp] theorem mapResult_formed (f : A → B) {N : ℕ} (r : SharedEncoder.Result A N) :
    (mapResult f r).formed = r.formed.map (mapStored f) := rfl

@[simp] theorem mapResult_coefficientWork (f : A → B) {N : ℕ} (r : SharedEncoder.Result A N) :
    (mapResult f r).coefficientWork = r.coefficientWork := rfl

@[simp] theorem mapResult_capWork (f : A → B) {N : ℕ} (r : SharedEncoder.Result A N) :
    (mapResult f r).capWork = r.capWork := rfl

@[simp] theorem mapResult_coefficientCells (f : A → B) {N : ℕ} (r : SharedEncoder.Result A N) :
    (mapResult f r).coefficientCells = r.coefficientCells := rfl

@[simp] theorem mapResult_leaf_keys (f : A → B) {N : ℕ} (r : SharedEncoder.Result A N) :
    (mapResult f r).leaves.map Prod.fst = r.leaves.map Prod.fst := by
  simp only [mapResult, List.map_map, Function.comp_def]

@[simp] theorem mapResult_trace_words (f : A → B) {N : ℕ} (r : SharedEncoder.Result A N) :
    (mapResult f r).formed.map (fun s => s.node.word) = r.formed.map (fun s => s.node.word) := by
  simp only [mapResult, List.map_map, Function.comp_def, mapStored_word]

/-- A payload-specific executable local array step, with no algebraic typeclass. -/
abbrev LocalContract (A : Type u) :=
  (d : ℕ) → Label → {n : ℕ} → (dims : Fin (n+1) → ℕ) →
    SharedEncoder.Dense (R := A) (n+1) dims →
    SharedEncoder.Dense (R := A) n (fun i => dims i.succ)

def nodeChildren (step : LocalContract A) (L m t d n : ℕ) (hd : d < 2*L)
    (dims : Fin (n+1) → ℕ) (parent : SharedEncoder.Node (R := A) (2*L) (n+1) dims) :
    List (SharedEncoder.Node (R := A) (2*L) n (fun i => dims i.succ)) :=
  (List.finRange 6).filterMap (fun row =>
    let word := put d hd parent.word row
    if capTest L m t word then some ⟨word, step d row dims parent.data⟩ else none)

def nextLayer (step : LocalContract A) (L m t d n : ℕ) (hd : d < 2*L)
    (dims : Fin (n+1) → ℕ) (parents : List (SharedEncoder.Node (R := A) (2*L) (n+1) dims)) :
    List (SharedEncoder.Node (R := A) (2*L) n (fun i => dims i.succ)) :=
  parents.flatMap (nodeChildren step L m t d n hd dims)

/-- The actual shape loop and finite counters, parameterized only by local execution. -/
def run (step : LocalContract A) (L m t q width : ℕ) :
    (n : ℕ) → (dims : Fin n → ℕ) → ℕ →
      List (SharedEncoder.Node (R := A) (2*L) n dims) → SharedEncoder.Result A (2*L)
  | 0,dims,d,parents =>
      { leaves := parents.map (fun node => (node.word,node.data))
        formed := parents.map (fun node => ⟨d,0,dims,node⟩)
        coefficientWork := 84*q*width*parents.length*volume 0 dims
        capWork := 0
        coefficientCells := q*width*parents.length*volume 0 dims }
  | n+1,dims,d,parents =>
      if hd : d < 2*L then
        let children := nextLayer step L m t d n hd dims parents
        let tail := run step L m t q width n (fun i => dims i.succ) (d+1) children
        { tail with
          formed := parents.map (fun node => ⟨d,n+1,dims,node⟩) ++ tail.formed
          coefficientWork := 84*q*width*parents.length*volume (n+1) dims +tail.coefficientWork
          capWork := 6*parents.length*(1+3*(2*L))+tail.capWork
          coefficientCells := q*width*parents.length*volume (n+1) dims+tail.coefficientCells }
      else
        { leaves := []
          formed := parents.map (fun node => ⟨d,n+1,dims,node⟩)
          coefficientWork := 84*q*width*parents.length*volume (n+1) dims
          capWork := 0
          coefficientCells := q*width*parents.length*volume (n+1) dims }

theorem nodeChildren_map (f : A → B) (stepA : LocalContract A) (stepB : LocalContract B)
    (hstep : ∀ d row n (dims : Fin (n+1) → ℕ) input,
      mapDense f n (fun i => dims i.succ) (stepA d row dims input) =
        stepB d row dims (mapDense f (n+1) dims input))
    (L m t d n : ℕ) (hd : d < 2*L) (dims : Fin (n+1) → ℕ)
    (parent : SharedEncoder.Node (R := A) (2*L) (n+1) dims) :
    (nodeChildren stepA L m t d n hd dims parent).map (mapNode f _) =
      nodeChildren stepB L m t d n hd dims (mapNode f dims parent) := by
  simp only [nodeChildren, List.map_filterMap]
  apply List.filterMap_congr
  intro row _
  simp only [mapNode]
  split
  · simp only [Option.map_some, Option.some.injEq, mapNode]
    congr 1
    exact hstep d row n dims parent.data
  · rfl

theorem nextLayer_map (f : A → B) (stepA : LocalContract A) (stepB : LocalContract B)
    (hstep : ∀ d row n (dims : Fin (n+1) → ℕ) input,
      mapDense f n (fun i => dims i.succ) (stepA d row dims input) =
        stepB d row dims (mapDense f (n+1) dims input))
    (L m t d n : ℕ) (hd : d < 2*L) (dims : Fin (n+1) → ℕ)
    (parents : List (SharedEncoder.Node (R := A) (2*L) (n+1) dims)) :
    (nextLayer stepA L m t d n hd dims parents).map (mapNode f _) =
      nextLayer stepB L m t d n hd dims (parents.map (mapNode f dims)) := by
  simp only [nextLayer, List.map_flatMap, List.flatMap_map]
  apply List.flatMap_congr
  intro parent _
  exact nodeChildren_map f stepA stepB hstep L m t d n hd dims parent

theorem run_map (f : A → B) (stepA : LocalContract A) (stepB : LocalContract B)
    (hstep : ∀ d row n (dims : Fin (n+1) → ℕ) input,
      mapDense f n (fun i => dims i.succ) (stepA d row dims input) =
        stepB d row dims (mapDense f (n+1) dims input))
    (L m t q width n : ℕ) (dims : Fin n → ℕ) (d : ℕ)
    (parents : List (SharedEncoder.Node (R := A) (2*L) n dims)) :
    mapResult f (run stepA L m t q width n dims d parents) =
      run stepB L m t q width n dims d (parents.map (mapNode f dims)) := by
  induction n generalizing d with
  | zero =>
      simp [run,mapResult,mapStored,mapNode,mapDense,SharedEncoder.materialize,
        SharedEncoder.read,List.map_map,Function.comp_def]
  | succ n ih =>
      simp only [run]
      split
      · rename_i hd
        rw [← nextLayer_map f stepA stepB hstep L m t d n hd dims]
        rw [← ih]
        simp [mapResult,mapStored,mapNode,List.map_map,Function.comp_def]
      · simp [mapResult,mapStored,mapNode,List.map_map,Function.comp_def]

def cacheStep (q width L : ℕ) (side : Bool) : LocalContract (CacheDenseLowering.Block q width) :=
  fun d row _ dims input => CacheDenseLowering.contract L side d row dims input

theorem run_cacheStep (L m t q width : ℕ) (side : Bool) (n : ℕ) (dims : Fin n → ℕ)
    (d : ℕ) (parents : List (CacheDenseLowering.DataNode q width (2*L) n dims)) :
    run (cacheStep q width L side) L m t q width n dims d parents =
      CacheDenseLowering.run L m t q width side n dims d parents := by
  induction n generalizing d with
  | zero => rfl
  | succ n ih =>
      simp only [run, CacheDenseLowering.run]
      split
      · rename_i hd
        have hnext : nextLayer (cacheStep q width L side) L m t d n hd dims parents =
            CacheDenseLowering.nextLayer L m t d n q width side hd dims parents := rfl
        rw [hnext, ih]
      · rfl

/-- A supplied local binary-to-integer proof lifts to every formed array,
every leaf, and exactly equal finite counters of the actual dense run. -/
theorem run_projects_cache (L m t q width : ℕ) (side : Bool)
    (f : A → CacheDenseLowering.Block q width) (step : LocalContract A)
    (hstep : ∀ d row n (dims : Fin (n+1) → ℕ) input,
      mapDense f n (fun i => dims i.succ) (step d row dims input) =
        CacheDenseLowering.contract L side d row dims (mapDense f (n+1) dims input))
    (n : ℕ) (dims : Fin n → ℕ) (d : ℕ)
    (parents : List (SharedEncoder.Node (R := A) (2*L) n dims)) :
    mapResult f (run step L m t q width n dims d parents) =
      CacheDenseLowering.run L m t q width side n dims d (parents.map (mapNode f dims)) := by
  rw [← run_cacheStep]
  exact run_map f step (cacheStep q width L side) hstep L m t q width n dims d parents

/-- Collect already-stored payload metadata once per suffix cell. This never
calls the local contraction or re-executes a coefficient primitive. -/
def sumDense (cost : A → ℕ) :
    (n : ℕ) → (dims : Fin n → ℕ) → SharedEncoder.Dense (R := A) n dims → ℕ
  | 0, _, data => cost data
  | n+1, dims, data => ∑ a : Fin (dims 0),
      sumDense cost n (fun i => dims i.succ) (data.get a)

def PayloadBound (cost : A → ℕ) (M : ℕ) (n : ℕ) (dims : Fin n → ℕ)
    (data : SharedEncoder.Dense (R := A) n dims) : Prop :=
  ∀ x, cost (SharedEncoder.read n dims data x) ≤ M

theorem sumDense_le (cost : A → ℕ) (M n : ℕ) (dims : Fin n → ℕ)
    (data : SharedEncoder.Dense (R := A) n dims) (h : PayloadBound cost M n dims data) :
    sumDense cost n dims data ≤ M * volume n dims := by
  induction n with
  | zero =>
      simpa [sumDense,volume,PayloadBound,SharedEncoder.read] using
        h (fun i => Fin.elim0 i)
  | succ n ih =>
      calc
        sumDense cost (n+1) dims data ≤
            ∑ _a : Fin (dims 0), M * volume n (fun i => dims i.succ) := by
          apply Finset.sum_le_sum
          intro a _
          apply ih
          intro rest
          exact h (Fin.cons a rest)
        _ = M * volume (n+1) dims := by
          simp [CacheDenseLowering.volume_succ,Nat.mul_left_comm]

def NodePayloadBound (cost : A → ℕ) (M : ℕ) {N n : ℕ} (dims : Fin n → ℕ)
    (node : SharedEncoder.Node (R := A) N n dims) : Prop :=
  PayloadBound cost M n dims node.data

def StoredPayloadBound (cost : A → ℕ) (M : ℕ) {N : ℕ} (s : SharedEncoder.Stored A N) : Prop :=
  NodePayloadBound cost M s.dims s.node

def storedCost (cost : A → ℕ) {N : ℕ} (s : SharedEncoder.Stored A N) : ℕ :=
  sumDense cost s.remaining s.dims s.node.data

def sumFormed (cost : A → ℕ) {N : ℕ} (formed : List (SharedEncoder.Stored A N)) : ℕ :=
  (formed.map (storedCost cost)).sum

def sumFormedVolume {N : ℕ} (formed : List (SharedEncoder.Stored A N)) : ℕ :=
  (formed.map (fun s => volume s.remaining s.dims)).sum

theorem sumFormed_le (cost : A → ℕ) (M : ℕ) {N : ℕ}
    (formed : List (SharedEncoder.Stored A N))
    (h : ∀ s ∈ formed, StoredPayloadBound cost M s) :
    sumFormed cost formed ≤ M * sumFormedVolume formed := by
  induction formed with
  | nil => simp [sumFormed,sumFormedVolume]
  | cons s ss ih =>
      have hh := sumDense_le cost M s.remaining s.dims s.node.data (h s (by simp))
      have ht := ih (fun a ha => h a (by simp [ha]))
      simp only [sumFormed,sumFormedVolume,List.map_cons,List.sum_cons] at ht ⊢
      simpa only [storedCost,Nat.mul_add] using Nat.add_le_add hh ht

/-- Payload charge propagation needs only the supplied semantic Width fact
for each actual formed parent. Child Width is supplied globally at the next
induction call, and is not an assumption of the local preservation proof. -/
theorem run_payload_bound (step : LocalContract A) (cost : A → ℕ) (M : ℕ)
    (L m t q width : ℕ)
    (Width : (d n : ℕ) → (dims : Fin n → ℕ) →
      SharedEncoder.Node (R := A) (2*L) n dims → Prop)
    (hstep : ∀ d n (hd : d < 2*L) dims parent,
      Width d (n+1) dims parent → NodePayloadBound cost M dims parent →
      ∀ child ∈ nodeChildren step L m t d n hd dims parent,
        NodePayloadBound cost M (fun i => dims i.succ) child)
    (n : ℕ) (dims : Fin n → ℕ) (d : ℕ)
    (parents : List (SharedEncoder.Node (R := A) (2*L) n dims))
    (hp : ∀ parent ∈ parents, NodePayloadBound cost M dims parent)
    (hwidth : ∀ s ∈ (run step L m t q width n dims d parents).formed,
      Width s.depth s.remaining s.dims s.node) :
    ∀ s ∈ (run step L m t q width n dims d parents).formed,
      StoredPayloadBound cost M s := by
  induction n generalizing d with
  | zero =>
      intro s hs
      obtain ⟨parent,hparent,rfl⟩ := List.mem_map.mp hs
      exact hp parent hparent
  | succ n ih =>
      simp only [run] at hwidth ⊢
      by_cases hd : d < 2*L
      · simp only [dif_pos hd] at hwidth ⊢
        have hpwidth : ∀ parent ∈ parents, Width d (n+1) dims parent := by
          intro parent hparent
          apply hwidth ⟨d,n+1,dims,parent⟩
          apply List.mem_append.mpr
          exact Or.inl (List.mem_map.mpr ⟨parent,hparent,rfl⟩)
        have hchildren : ∀ child ∈ nextLayer step L m t d n hd dims parents,
            NodePayloadBound cost M (fun i => dims i.succ) child := by
          intro child hc
          obtain ⟨parent,hparent,hchild⟩ := List.mem_flatMap.mp hc
          exact hstep d n hd dims parent (hpwidth parent hparent) (hp parent hparent) child hchild
        have htailwidth : ∀ s ∈
            (run step L m t q width n (fun i => dims i.succ) (d+1)
              (nextLayer step L m t d n hd dims parents)).formed,
            Width s.depth s.remaining s.dims s.node := by
          intro s hs
          exact hwidth s (List.mem_append.mpr (Or.inr hs))
        intro s hs
        obtain hs | hs := List.mem_append.mp hs
        · obtain ⟨parent,hparent,rfl⟩ := List.mem_map.mp hs
          exact hp parent hparent
        · exact ih _ _ _ hchildren htailwidth s hs
      · simp only [dif_neg hd] at hwidth ⊢
        intro s hs
        obtain ⟨parent,hparent,rfl⟩ := List.mem_map.mp hs
        exact hp parent hparent

theorem run_payload_bound_of_width (step : LocalContract A) (cost : A → ℕ) (M : ℕ)
    (L m t q width : ℕ)
    (Width : (d n : ℕ) → (dims : Fin n → ℕ) →
      SharedEncoder.Node (R := A) (2*L) n dims → Prop)
    (hstep : ∀ d n (hd : d < 2*L) dims parent,
      Width d (n+1) dims parent →
      ∀ child ∈ nodeChildren step L m t d n hd dims parent,
        NodePayloadBound cost M (fun i => dims i.succ) child)
    (n : ℕ) (dims : Fin n → ℕ) (d : ℕ)
    (parents : List (SharedEncoder.Node (R := A) (2*L) n dims))
    (hp : ∀ parent ∈ parents, NodePayloadBound cost M dims parent)
    (hwidth : ∀ s ∈ (run step L m t q width n dims d parents).formed,
      Width s.depth s.remaining s.dims s.node) :
    ∀ s ∈ (run step L m t q width n dims d parents).formed,
      StoredPayloadBound cost M s :=
  run_payload_bound step cost M L m t q width Width
    (fun d n hd dims parent hw _ => hstep d n hd dims parent hw)
    n dims d parents hp hwidth

/-- The finite coefficient-cell ledger equals one q*width charge for every
raw suffix payload in every actually retained array, including the root. -/
theorem run_cells_eq_sumFormedVolume (step : LocalContract A) (L m t q width n : ℕ)
    (dims : Fin n → ℕ) (d : ℕ)
    (parents : List (SharedEncoder.Node (R := A) (2*L) n dims)) :
    (run step L m t q width n dims d parents).coefficientCells =
      q * width * sumFormedVolume (run step L m t q width n dims d parents).formed := by
  induction n generalizing d with
  | zero => simp [run,sumFormedVolume,List.map_map,Function.comp_def,Nat.mul_assoc]
  | succ n ih =>
      simp only [run]
      split
      · rw [ih]
        simp [sumFormedVolume,List.map_map,Function.comp_def,Nat.mul_add,Nat.mul_assoc]
      · simp [sumFormedVolume,List.map_map,Function.comp_def,Nat.mul_assoc]

theorem run_sumFormed_le (step : LocalContract A) (cost : A → ℕ) (M : ℕ)
    (L m t q width n : ℕ) (dims : Fin n → ℕ) (d : ℕ)
    (parents : List (SharedEncoder.Node (R := A) (2*L) n dims))
    (h : ∀ s ∈ (run step L m t q width n dims d parents).formed,
      StoredPayloadBound cost M s) :
    sumFormed cost (run step L m t q width n dims d parents).formed ≤
      M * sumFormedVolume (run step L m t q width n dims d parents).formed :=
  sumFormed_le cost M _ h

/-- A bound of `scale*q*width` on each stored raw-payload tag converts
directly to scale times coefficientCells, including q=0 or width=0. -/
theorem run_sumFormed_le_cells (step : LocalContract A) (cost : A → ℕ) (scale : ℕ)
    (L m t q width n : ℕ) (dims : Fin n → ℕ) (d : ℕ)
    (parents : List (SharedEncoder.Node (R := A) (2*L) n dims))
    (h : ∀ s ∈ (run step L m t q width n dims d parents).formed,
      StoredPayloadBound cost (scale*q*width) s) :
    sumFormed cost (run step L m t q width n dims d parents).formed ≤
      scale * (run step L m t q width n dims d parents).coefficientCells := by
  have hs := sumFormed_le cost (scale*q*width) _ h
  rw [run_cells_eq_sumFormedVolume]
  simpa only [Nat.mul_assoc] using hs

/-- Direct joint-tag budget: semantic Width is a fact about the complete
actual trace; local rows establish only the charge on their newly stored
payloads. Parent tags are not accumulated again by the local step. -/
theorem run_sumFormed_le_cells_of_width (step : LocalContract A) (cost : A → ℕ)
    (scale L m t q width : ℕ)
    (Width : (d n : ℕ) → (dims : Fin n → ℕ) →
      SharedEncoder.Node (R := A) (2*L) n dims → Prop)
    (hstep : ∀ d n (hd : d < 2*L) dims parent,
      Width d (n+1) dims parent →
      ∀ child ∈ nodeChildren step L m t d n hd dims parent,
        NodePayloadBound cost (scale*q*width) (fun i => dims i.succ) child)
    (n : ℕ) (dims : Fin n → ℕ) (d : ℕ)
    (parents : List (SharedEncoder.Node (R := A) (2*L) n dims))
    (hp : ∀ parent ∈ parents, NodePayloadBound cost (scale*q*width) dims parent)
    (hwidth : ∀ s ∈ (run step L m t q width n dims d parents).formed,
      Width s.depth s.remaining s.dims s.node) :
    sumFormed cost (run step L m t q width n dims d parents).formed ≤
      scale * (run step L m t q width n dims d parents).coefficientCells := by
  apply run_sumFormed_le_cells
  exact run_payload_bound_of_width step cost (scale*q*width)
    L m t q width Width hstep n dims d parents hp hwidth


end DenseRun

abbrev Cell := BinaryCell.Cell
abbrev Block (q width : ℕ) := Vector (Vector Cell q) width
abbrev ChargedBlock (q width : ℕ) := Block q width × ℕ
abbrev Data (q width n : ℕ) (dims : Fin n → ℕ) := SharedEncoder.Dense (R := ChargedBlock q width) n dims

/-- Proof projection, never called by a binary encoder operation. -/
def blockView {q width : ℕ} (block : Block q width) : SparseLocalForms.DenseVector q width :=
  block.map (fun row => row.map BinaryCell.view)

def payloadView {q width : ℕ} (block : ChargedBlock q width) := blockView block.1

@[simp] theorem blockView_read {q width : ℕ} (block : Block q width) (d : Fin width) (r : Fin q) :
    SparseLocalForms.denseRead (blockView block) d r = BinaryCell.view ((block.get d).get r) := by
  simp only [blockView,SparseLocalForms.denseRead,Vector.get_map]

def zeroBlock (q width : ℕ) : Block q width := Vector.replicate width (Vector.replicate q BinaryCell.zero)

@[simp] theorem zeroBlock_view (q width : ℕ) : blockView (zeroBlock q width) = CachedLowQuery.zeroBlock q width := by
  apply CacheDenseLowering.block_ext
  intro d r
  rw [blockView_read]
  simp [zeroBlock,CachedLowQuery.zeroBlock,SparseLocalForms.denseRead]

def readCell {q width : ℕ} (normal : Bool) (row : Fin 6) (children : Fin 4 → Block q width)
    (col : Fin 4) (degree : Fin width) (residue : Fin q) : Cell :=
  if SparseLocalForms.shifted normal row col then
    if h : 0 < degree.val then (children col).get ⟨degree.val-1,by omega⟩ |>.get residue
    else BinaryCell.zero
  else ((children col).get degree).get residue

@[simp] theorem readCell_view {q width : ℕ} (normal : Bool) (row : Fin 6)
    (children : Fin 4 → Block q width) (col : Fin 4) (d : Fin width) (r : Fin q) :
    BinaryCell.view (readCell normal row children col d r) =
      SparseLocalForms.readCell normal row (fun c => SparseLocalForms.denseRead (blockView (children c))) col d r := by
  simp only [readCell,SparseLocalForms.readCell,blockView_read]
  split
  · split <;> rfl
  · rfl

structure Registers where
  temporary : Cell := BinaryCell.zero
  accumulator : Cell := BinaryCell.zero
  output : Cell := BinaryCell.zero

def Registers.view (s : Registers) : SparseLocalForms.Registers :=
  ⟨BinaryCell.view s.temporary,BinaryCell.view s.accumulator,BinaryCell.view s.output⟩

inductive Instruction where
  | read (col : Fin 4)
  | scale (col : Fin 4)
  | add
  | write

def nativeInstruction (normal : Bool) (row : Fin 6) : Instruction → SparseLocalForms.Instruction
  | .read col => .read col
  | .scale col => .scale (SparseLocalForms.rowCoefficients normal row col)
  | .add => .add
  | .write => .write

/-- Every operand below is taken from the preceding stored binary state. -/
def instruction (normal : Bool) (row : Fin 6) (read : Fin 4 → Cell) :
    Instruction → Registers → BinaryCell.Result Registers
  | .read col,s => let r := BinaryCell.copy (read col); ⟨{s with temporary:=r.value},r.bitSteps⟩
  | .scale col,s => let r := BinaryCell.mul (BinaryCell.coefficient normal row col) s.temporary
                   ⟨{s with temporary:=r.value},r.bitSteps⟩
  | .add,s => let r := BinaryCell.add s.accumulator s.temporary
              ⟨{s with accumulator:=r.value},r.bitSteps⟩
  | .write,s => let r := BinaryCell.copy s.accumulator; ⟨{s with output:=r.value},r.bitSteps⟩

@[simp] theorem instruction_view (normal : Bool) (row : Fin 6) (read : Fin 4 → Cell)
    (op : Instruction) (s : Registers) :
    ((instruction normal row read op s).value).view =
      SparseLocalForms.executeInstruction (fun c => BinaryCell.view (read c)) (nativeInstruction normal row op) s.view := by
  cases op <;> simp [instruction,nativeInstruction,Registers.view,SparseLocalForms.executeInstruction]

/-- Fixed thirteen-instruction sparse row, with literal finite coefficient ROM. -/
def program : List Instruction :=
  [.read 0,.scale 0,.add,.read 1,.scale 1,.add,.read 2,.scale 2,.add,.read 3,.scale 3,.add,.write]

@[simp] theorem program_length : program.length = 13 := rfl
@[simp] theorem program_native (normal : Bool) (row : Fin 6) :
    program.map (nativeInstruction normal row) = SparseLocalForms.cellProgram normal row := rfl

def runInstructions (normal : Bool) (row : Fin 6) (read : Fin 4 → Cell) :
    List Instruction → Registers → BinaryCell.Result Registers
  | [],s => ⟨s,0⟩
  | op::ops,s =>
      let head := instruction normal row read op s
      let tail := runInstructions normal row read ops head.value
      ⟨tail.value,head.bitSteps+tail.bitSteps⟩

theorem runInstructions_view (normal : Bool) (row : Fin 6) (read : Fin 4 → Cell)
    (ops : List Instruction) (s : Registers) :
    (runInstructions normal row read ops s).value.view =
      (ops.map (nativeInstruction normal row)).foldl
        (fun state op => SparseLocalForms.executeInstruction (fun c => BinaryCell.view (read c)) op state) s.view := by
  induction ops generalizing s with
  | nil => rfl
  | cons op ops ih => simp only [runInstructions,ih,List.map_cons,List.foldl_cons,instruction_view]

def cell {q width : ℕ} (normal : Bool) (row : Fin 6) (children : Fin 4 → Block q width)
    (d : Fin width) (r : Fin q) : BinaryCell.Result Cell :=
  let result := runInstructions normal row (fun col => readCell normal row children col d r) program {}
  ⟨result.value.output,result.bitSteps⟩

@[simp] theorem cell_view {q width : ℕ} (normal : Bool) (row : Fin 6) (children : Fin 4 → Block q width)
    (d : Fin width) (r : Fin q) :
    BinaryCell.view (cell normal row children d r).value =
      SparseLocalForms.localRow normal row (fun c => SparseLocalForms.denseRead (blockView (children c))) d r := by
  have h := runInstructions_view normal row (fun col => readCell normal row children col d r) program {}
  rw [program_native] at h
  have ho := congrArg SparseLocalForms.Registers.output h
  have he : BinaryCell.view (cell normal row children d r).value =
      (SparseLocalForms.executeCell normal row
        (fun c => SparseLocalForms.denseRead (blockView (children c))) d r).output := by
    simpa only [cell,Registers.view,readCell_view,SparseLocalForms.executeCell,BinaryCell.zero_view] using ho
  exact he.trans (SparseLocalForms.executeCell_correct normal row _ d r)


/-- Materialized joint results: value and counter are projected from the
same stored row-cell executions. -/
def rowBlock {q width : ℕ} (normal : Bool) (row : Fin 6) (children : Fin 4 → Block q width) : ChargedBlock q width :=
  let cells := Vector.ofFn (fun d => Vector.ofFn (fun r => cell normal row children d r))
  (cells.map (fun line => line.map (fun c => c.value)),
    (cells.toList.map (fun line => (line.toList.map (fun c => c.bitSteps)).sum)).sum+8*q*width)

@[simp] theorem rowBlock_view {q width : ℕ} (normal : Bool) (row : Fin 6) (children : Fin 4 → Block q width) :
    payloadView (rowBlock normal row children) =
      SparseLocalForms.denseLocalRow normal row (fun c => blockView (children c)) := by
  apply CacheDenseLowering.block_ext
  intro d r
  simp only [payloadView,rowBlock,blockView_read,Vector.get_map,Vector.get_ofFn,cell_view,
    SparseLocalForms.denseLocalRow_correct]


/-- A deliberately coarse bound handles all thirteen transient states,
without relying on cancellation in a completed row. -/
def RegisterBound (M : ℕ) (s : Registers) : Prop :=
  |BinaryCell.view s.temporary| ≤ (M:ℤ) ∧
  |BinaryCell.view s.accumulator| ≤ (M:ℤ) ∧ |BinaryCell.view s.output| ≤ (M:ℤ)

theorem cell_size_of_abs (a : Cell) (W : ℕ) (ha : |BinaryCell.view a| ≤ ((2:ℕ)^W:ℤ)) :
    (BinaryCell.view a).natAbs.size ≤ W+1 := by
  rw [←Int.natCast_natAbs] at ha
  have hn : (BinaryCell.view a).natAbs ≤ 2^W := by exact_mod_cast ha
  exact (Nat.size_le_size hn).trans_eq Nat.size_pow

theorem instruction_growth (normal : Bool) (row : Fin 6) (read : Fin 4 → Cell)
    (M : ℕ) (hr : ∀ c, |BinaryCell.view (read c)| ≤ (M:ℤ)) (op : Instruction) (s : Registers)
    (hs : RegisterBound M s) : RegisterBound (2*M) (instruction normal row read op s).value := by
  rcases hs with ⟨ht,ha,ho⟩
  have hM : (0:ℤ) ≤ M := Nat.cast_nonneg M
  cases op with
  | read c =>
      simp only [RegisterBound,instruction,BinaryCell.copy_view,Nat.cast_mul,Nat.cast_ofNat]
      exact ⟨(hr c).trans (by nlinarith),ha.trans (by nlinarith),ho.trans (by nlinarith)⟩
  | scale c =>
      have hp : |SparseLocalForms.rowCoefficients normal row c*BinaryCell.view s.temporary| ≤ 2*(M:ℤ) := by
        rw [abs_mul]
        exact mul_le_mul (SparseLocalForms.rowCoefficients_bound normal row c) ht (abs_nonneg _) (by norm_num)
      simp only [RegisterBound,instruction,BinaryCell.mul_view,BinaryCell.coefficient_view,Nat.cast_mul,Nat.cast_ofNat]
      exact ⟨hp,ha.trans (by nlinarith),ho.trans (by nlinarith)⟩
  | add =>
      have hp := abs_add_le (BinaryCell.view s.accumulator) (BinaryCell.view s.temporary)
      simp only [RegisterBound,instruction,BinaryCell.add_view,Nat.cast_mul,Nat.cast_ofNat]
      exact ⟨ht.trans (by nlinarith),hp.trans (by nlinarith),ho.trans (by nlinarith)⟩
  | write =>
      simp only [RegisterBound,instruction,BinaryCell.copy_view,Nat.cast_mul,Nat.cast_ofNat]
      exact ⟨ht.trans (by nlinarith),ha.trans (by nlinarith),ha.trans (by nlinarith)⟩

theorem instruction_price (normal : Bool) (row : Fin 6) (read : Fin 4 → Cell)
    (W B : ℕ) (hW : W+1 ≤ B) (hB : 2 ≤ B)
    (hr : ∀ c, |BinaryCell.view (read c)| ≤ ((2:ℕ)^W:ℤ))
    (op : Instruction) (s : Registers) (hs : RegisterBound (2^W) s) :
    (instruction normal row read op s).bitSteps ≤ BackendScalarBits.backendScalarUnit B := by
  have ht := (cell_size_of_abs s.temporary W hs.1).trans hW
  have ha := (cell_size_of_abs s.accumulator W hs.2.1).trans hW
  cases op with
  | read c => exact BinaryCell.copy_price B _ ((cell_size_of_abs _ W (hr c)).trans hW)
  | scale c => exact BinaryCell.mul_price B _ _ ((BinaryCell.coefficient_size normal row c).trans hB) ht
  | add => exact BinaryCell.add_price B _ _ ha ht
  | write => exact BinaryCell.copy_price B _ ha

theorem runInstructions_price (normal : Bool) (row : Fin 6) (read : Fin 4 → Cell)
    (ops : List Instruction) (W : ℕ) (s : Registers)
    (hr : ∀ c, |BinaryCell.view (read c)| ≤ ((2:ℕ)^W:ℤ)) (hs : RegisterBound (2^W) s) :
    (runInstructions normal row read ops s).bitSteps ≤
      ops.length*BackendScalarBits.backendScalarUnit (W+ops.length+2) := by
  induction ops generalizing W s with
  | nil => simp [runInstructions]
  | cons op ops ih =>
      have hh := instruction_price normal row read W (W+(op::ops).length+2) (by simp;omega) (by omega) hr op s hs
      have hg := instruction_growth normal row read (2^W) hr op s hs
      have he : 2*(2:ℕ)^W = 2^(W+1) := by rw [pow_succ]; ring
      rw [he] at hg
      have hr' : ∀ c, |BinaryCell.view (read c)| ≤ ((2:ℕ)^(W+1):ℤ) := by
        intro c
        exact (hr c).trans (by exact_mod_cast Nat.pow_le_pow_right (by norm_num : 1≤(2:ℕ)) (by omega : W≤W+1))
      have ht := ih (W+1) (instruction normal row read op s).value hr' hg
      have hb : W+1+ops.length+2 = W+(op::ops).length+2 := by simp;omega
      rw [hb] at ht
      exact (Nat.add_le_add hh ht).trans_eq (by simp only [List.length_cons]; ring)

theorem cell_price {q width : ℕ} (normal : Bool) (row : Fin 6)
    (children : Fin 4 → Block q width) (W : ℕ)
    (hc : ∀ c d r, |BinaryCell.view (((children c).get d).get r)| ≤ ((2:ℕ)^W:ℤ))
    (d : Fin width) (r : Fin q) :
    (cell normal row children d r).bitSteps ≤ 13*BackendScalarBits.backendScalarUnit (W+15) := by
  have hr : ∀ c, |BinaryCell.view (readCell normal row children c d r)| ≤ ((2:ℕ)^W:ℤ) := by
    intro c
    unfold readCell
    split
    · split
      · exact hc _ _ _
      · simp
    · exact hc _ _ _
  have hs : RegisterBound (2^W) ({} : Registers) := by simp [RegisterBound]
  exact runInstructions_price normal row _ program W {} hr hs

theorem rowBlock_work_eq {q width : ℕ} (normal : Bool) (row : Fin 6) (children : Fin 4 → Block q width) :
    (rowBlock normal row children).2 =
      (∑ d : Fin width, ∑ r : Fin q, (cell normal row children d r).bitSteps)+8*q*width := by
  simp [rowBlock,Vector.toList_ofFn,List.map_ofFn,List.sum_ofFn]

theorem rowBlock_price {q width : ℕ} (normal : Bool) (row : Fin 6)
    (children : Fin 4 → Block q width) (W : ℕ)
    (hc : ∀ c d r, |BinaryCell.view (((children c).get d).get r)| ≤ ((2:ℕ)^W:ℤ)) :
    (rowBlock normal row children).2 ≤ 32*q*width*BackendScalarBits.backendScalarUnit (W+15) := by
  have hcell : (∑ d : Fin width, ∑ r : Fin q, (cell normal row children d r).bitSteps) ≤
      width*q*(13*BackendScalarBits.backendScalarUnit (W+15)) := by
    calc
      _ ≤ ∑ _d : Fin width, ∑ _r : Fin q, 13*BackendScalarBits.backendScalarUnit (W+15) := by
        apply Finset.sum_le_sum
        intro d _
        exact Finset.sum_le_sum (fun r _ => cell_price normal row children W hc d r)
      _ = _ := by simp;ring
  have hu : 1 ≤ BackendScalarBits.backendScalarUnit (W+15) := by
    have hp : 1 ≤ (W+15+1)^2 := Nat.one_le_pow 2 (W+15+1) (by omega)
    unfold BackendScalarBits.backendScalarUnit BackendScalarBits.scalarUnit
    nlinarith
  have hi : 8*q*width ≤ 8*q*width*BackendScalarBits.backendScalarUnit (W+15) :=
    Nat.le_mul_of_pos_right _ hu
  rw [rowBlock_work_eq]
  calc
    _ ≤ width*q*(13*BackendScalarBits.backendScalarUnit (W+15))+8*q*width := Nat.add_le_add_right hcell _
    _ ≤ width*q*(13*BackendScalarBits.backendScalarUnit (W+15))+
        8*q*width*BackendScalarBits.backendScalarUnit (W+15) := Nat.add_le_add_left hi _
    _ = 21*q*width*BackendScalarBits.backendScalarUnit (W+15) := by ring
    _ ≤ _ := by gcongr; norm_num


/-- The absent fourth opposite coordinate shares one literal zero block. -/
def gather {q width n : ℕ} (dims : Fin (n+1) → ℕ) (input : Data q width (n+1) dims)
    (zero : Block q width) (rest : Coordinates (fun i : Fin n => dims i.succ)) : Fin 4 → Block q width :=
  fun col => if hc : col.val < dims 0 then
    (SharedEncoder.read (n+1) dims input (Fin.cons ⟨col.val,hc⟩ rest)).1 else zero

/-- Each retained child materializes each raw suffix block once. Charges
are stored next to the actual computed binary block, without inherited charges. -/
def contract {q width n : ℕ} (L : ℕ) (side : Bool) (d : ℕ) (row : Label)
    (dims : Fin (n+1) → ℕ) (input : Data q width (n+1) dims) :
    Data q width n (fun i => dims i.succ) :=
  let zero := zeroBlock q width
  SharedEncoder.materialize n (fun i => dims i.succ) (fun rest =>
    rowBlock (CacheDenseLowering.normalHere L side d) row (gather dims input zero rest))

theorem contract_view {q width n : ℕ} (L : ℕ) (side : Bool) (d : ℕ) (row : Label)
    (dims : Fin (n+1) → ℕ) (input : Data q width (n+1) dims) :
    DenseRun.mapDense payloadView n (fun i => dims i.succ) (contract L side d row dims input) =
      CacheDenseLowering.contract L side d row dims (DenseRun.mapDense payloadView (n+1) dims input) := by
  apply CacheDenseLowering.dense_ext
  intro rest
  rw [DenseRun.read_mapDense,contract,SharedEncoder.read_materialize,rowBlock_view,
    CacheDenseLowering.contract,SharedEncoder.read_materialize]
  congr 1
  funext col
  unfold gather CacheDenseLowering.gather
  split
  · rw [DenseRun.read_mapDense]
    rfl
  · exact zeroBlock_view q width

def step (q width L : ℕ) (side : Bool) : DenseRun.LocalContract (ChargedBlock q width) :=
  fun d row _ dims input => contract L side d row dims input

def run (L m t q width : ℕ) (side : Bool) (n : ℕ) (dims : Fin n → ℕ) (d : ℕ)
    (parents : List (SharedEncoder.Node (R := ChargedBlock q width) (2*L) n dims)) :=
  DenseRun.run (step q width L side) L m t q width n dims d parents

/-- Projection includes every materialized intermediate, every leaf, and
exactly the same scalar/control ledger as the native retained-prefix loop. -/
theorem run_view (L m t q width : ℕ) (side : Bool) (n : ℕ) (dims : Fin n → ℕ) (d : ℕ)
    (parents : List (SharedEncoder.Node (R := ChargedBlock q width) (2*L) n dims)) :
    DenseRun.mapResult payloadView (run L m t q width side n dims d parents) =
      CacheDenseLowering.run L m t q width side n dims d (parents.map (DenseRun.mapNode payloadView dims)) :=
  DenseRun.run_projects_cache L m t q width side payloadView (step q width L side)
    (fun d row _n dims input => contract_view L side d row dims input) n dims d parents

def NodeWidth {q width N n : ℕ} (W : ℕ) (dims : Fin n → ℕ)
    (node : SharedEncoder.Node (R := ChargedBlock q width) N n dims) : Prop :=
  ∀ a d r, (SparseLocalForms.denseRead (payloadView (SharedEncoder.read n dims node.data a)) d r).natAbs.size ≤ W

theorem abs_of_cell_size (a : Cell) (W : ℕ) (ha : (BinaryCell.view a).natAbs.size ≤ W) :
    |BinaryCell.view a| ≤ ((2:ℕ)^W:ℤ) := by
  have hn : (BinaryCell.view a).natAbs ≤ 2^W :=
    (Nat.lt_size_self _).le.trans (Nat.pow_le_pow_right (by norm_num) ha)
  rw [←Int.natCast_natAbs]
  exact_mod_cast hn

theorem contract_charge {q width n : ℕ} (L : ℕ) (side : Bool) (d : ℕ) (row : Label)
    (dims : Fin (n+1) → ℕ) (input : Data q width (n+1) dims) (W : ℕ)
    (hw : ∀ a degree residue,
      (SparseLocalForms.denseRead (payloadView (SharedEncoder.read (n+1) dims input a)) degree residue).natAbs.size ≤ W) :
    DenseRun.PayloadBound Prod.snd (32*q*width*BackendScalarBits.backendScalarUnit (W+15))
      n (fun i => dims i.succ) (contract L side d row dims input) := by
  intro rest
  rw [contract,SharedEncoder.read_materialize]
  apply rowBlock_price
  intro col degree residue
  unfold gather
  split
  · apply abs_of_cell_size
    simpa only [payloadView,blockView_read] using hw (Fin.cons _ rest) degree residue
  · simp [zeroBlock]

theorem child_charge {q width : ℕ} (L m t d n : ℕ) (side : Bool) (hd : d < 2*L)
    (dims : Fin (n+1) → ℕ) (W : ℕ)
    (parent : SharedEncoder.Node (R := ChargedBlock q width) (2*L) (n+1) dims)
    (hp : NodeWidth W dims parent) :
    ∀ child ∈ DenseRun.nodeChildren (step q width L side) L m t d n hd dims parent,
      DenseRun.NodePayloadBound Prod.snd
        (32*BackendScalarBits.backendScalarUnit (W+15)*q*width) (fun i => dims i.succ) child := by
  intro child hc
  obtain ⟨row,_,hr⟩ := List.mem_filterMap.mp hc
  dsimp only [DenseRun.nodeChildren] at hr
  split at hr
  · simp only [Option.some.injEq] at hr
    subst child
    have h := contract_charge L side d row dims parent.data W hp
    simpa only [step,DenseRun.NodePayloadBound, Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using h
  · simp at hr

/-- Exact copied scalar ledger, independently of payload arithmetic. -/
theorem run_work_eq_cells (L m t q width : ℕ) (side : Bool) (n : ℕ) (dims : Fin n → ℕ) (d : ℕ)
    (parents : List (SharedEncoder.Node (R := ChargedBlock q width) (2*L) n dims)) :
    (run L m t q width side n dims d parents).coefficientWork =
      84*(run L m t q width side n dims d parents).coefficientCells := by
  unfold run
  induction n generalizing d with
  | zero => simp [DenseRun.run];ring
  | succ n ih =>
      simp only [DenseRun.run]
      split
      · rw [ih];ring
      · ring

/-- Actual bit operations are collected from stored tags. The extra eight
scalar visits per raw payload pay collecting those tags and retained metadata. -/
def bitWork {q width N : ℕ} (W : ℕ) (result : SharedEncoder.Result (ChargedBlock q width) N) : ℕ :=
  DenseRun.sumFormed Prod.snd result.formed +
    (8*DenseRun.sumFormedVolume result.formed+result.capWork)*BackendScalarBits.backendScalarUnit (W+15)

theorem run_bitWork_le (L m t q width : ℕ) (side : Bool) (n : ℕ) (dims : Fin n → ℕ) (d W : ℕ)
    (parents : List (SharedEncoder.Node (R := ChargedBlock q width) (2*L) n dims))
    (hq : 1 ≤ q) (hw : 1 ≤ width)
    (hp : ∀ parent ∈ parents, DenseRun.NodePayloadBound Prod.snd
      (32*BackendScalarBits.backendScalarUnit (W+15)*q*width) dims parent)
    (hwidth : ∀ s ∈ (run L m t q width side n dims d parents).formed,
      NodeWidth W s.dims s.node) :
    bitWork W (run L m t q width side n dims d parents) ≤
      ((run L m t q width side n dims d parents).coefficientWork+
       (run L m t q width side n dims d parents).capWork)*BackendScalarBits.backendScalarUnit (W+15) := by
  have hc := DenseRun.run_sumFormed_le_cells_of_width (step q width L side) Prod.snd
    (32*BackendScalarBits.backendScalarUnit (W+15)) L m t q width
    (fun _ _ dims node => NodeWidth W dims node)
    (fun d n hd dims parent hp => child_charge L m t d n side hd dims W parent hp)
    n dims d parents hp hwidth
  have he := DenseRun.run_cells_eq_sumFormedVolume (step q width L side) L m t q width n dims d parents
  have hqw : 1 ≤ q*width := by nlinarith
  have hv : DenseRun.sumFormedVolume (run L m t q width side n dims d parents).formed ≤
      (run L m t q width side n dims d parents).coefficientCells := by
    change _ ≤ (DenseRun.run (step q width L side) L m t q width n dims d parents).coefficientCells
    rw [he]
    exact Nat.le_mul_of_pos_left _ hqw
  have hs := run_work_eq_cells L m t q width side n dims d parents
  unfold bitWork
  change DenseRun.sumFormed Prod.snd (run L m t q width side n dims d parents).formed ≤
    32*BackendScalarBits.backendScalarUnit (W+15)*(run L m t q width side n dims d parents).coefficientCells at hc
  have hvscaled := Nat.mul_le_mul_left (8*BackendScalarBits.backendScalarUnit (W+15)) hv
  nlinarith

/-- A raw binary source array is a stored array of cyclic vectors. -/
abbrev Raw (L q : ℕ) (side : Bool) :=
  SharedEncoder.Dense (R := Vector Cell q) (2*L) (rootDims L side)

/-- Integer denotation is used only in proofs. -/
def rawView {L q : ℕ} {side : Bool} (input : Raw L q side) :=
  DenseRun.mapDense (fun v : Vector Cell q => v.map BinaryCell.view)
    (2*L) (rootDims L side) input

/-- Form degree zero from the stored source vector and all higher degrees
from the shared literal zero. No integer denotation is evaluated. -/
def constantInput {q width : ℕ} (n : ℕ) (dims : Fin n → ℕ)
    (input : SharedEncoder.Dense (R := Vector Cell q) n dims) : Data q width n dims :=
  SharedEncoder.materialize n dims (fun a =>
    let source := SharedEncoder.read n dims input a
    (Vector.ofFn (fun d : Fin width => if d.val=0 then source else Vector.replicate q BinaryCell.zero),q*width))

theorem constantInput_view {q width : ℕ} (n : ℕ) (dims : Fin n → ℕ)
    (input : SharedEncoder.Dense (R := Vector Cell q) n dims) :
    DenseRun.mapDense payloadView n dims (constantInput (width := width) n dims input) =
      CacheDenseLowering.constantInput (width := width) n dims
        (DenseRun.mapDense (fun v : Vector Cell q => v.map BinaryCell.view) n dims input) := by
  apply CacheDenseLowering.dense_ext
  intro a
  rw [DenseRun.read_mapDense,constantInput,SharedEncoder.read_materialize,
    CacheDenseLowering.constantInput,SharedEncoder.read_materialize,DenseRun.read_mapDense]
  apply CacheDenseLowering.block_ext
  intro d r
  simp only [payloadView,blockView,Vector.get_ofFn,CacheDenseLowering.constantBlock,
    SparseLocalForms.denseRead,Vector.get_map]
  split_ifs <;> simp [BinaryCell.zero,BinaryCell.view]

/-- Public computable entry point. Each raw suffix array and each retained
child array is formed once, and all local charges remain stored beside it. -/
def encodeVectors (L m t q width : ℕ) (side : Bool) (input : Raw L q side) :=
  run L m t q width side (2*L) (rootDims L side) 0
    [⟨zeroWord (2*L),constantInput (width := width) (2*L) (rootDims L side) input⟩]

theorem encodeVectors_view (L m t q width : ℕ) (side : Bool) (input : Raw L q side) :
    DenseRun.mapResult payloadView (encodeVectors L m t q width side input) =
      CacheDenseLowering.encodeVectors L m t q width side (rawView input) := by
  unfold encodeVectors
  rw [run_view]
  simp only [List.map_cons,List.map_nil,DenseRun.mapNode,constantInput_view]
  rfl

/-- Every actual binary parent cell inherits the width of its native
projection, including the root and all retained intermediate arrays. -/
theorem encoded_width (L m t q width W : ℕ) (side : Bool) (input : Raw L q side)
    (hwidth : ∀ s ∈ (CacheDenseLowering.encodeVectors L m t q width side (rawView input)).formed,
      ∀ a d r, (SparseLocalForms.denseRead (SharedEncoder.read s.remaining s.dims s.node.data a) d r).natAbs.size ≤ W) :
    ∀ s ∈ (encodeVectors L m t q width side input).formed, NodeWidth W s.dims s.node := by
  intro s hs a d r
  have hm : DenseRun.mapStored payloadView s ∈
      (CacheDenseLowering.encodeVectors L m t q width side (rawView input)).formed := by
    rw [←encodeVectors_view]
    exact List.mem_map.mpr ⟨s,hs,rfl⟩
  simpa only [DenseRun.mapStored,DenseRun.mapNode,DenseRun.read_mapDense]
    using hwidth _ hm a d r

theorem encodeVectors_bitWork_le (L m t q width W : ℕ) (side : Bool) (input : Raw L q side)
    (hq : 1 ≤ q) (hw : 1 ≤ width)
    (hwidth : ∀ s ∈ (CacheDenseLowering.encodeVectors L m t q width side (rawView input)).formed,
      ∀ a d r, (SparseLocalForms.denseRead (SharedEncoder.read s.remaining s.dims s.node.data a) d r).natAbs.size ≤ W) :
    bitWork W (encodeVectors L m t q width side input) ≤
      ((CacheDenseLowering.encodeVectors L m t q width side (rawView input)).coefficientWork+
       (CacheDenseLowering.encodeVectors L m t q width side (rawView input)).capWork)*
        BackendScalarBits.backendScalarUnit (W+15) := by
  have hu : 1 ≤ BackendScalarBits.backendScalarUnit (W+15) := by
    unfold BackendScalarBits.backendScalarUnit BackendScalarBits.scalarUnit
    have := Nat.one_le_pow 2 (W+15+1) (by omega)
    nlinarith
  have hp : ∀ parent ∈ [⟨zeroWord (2*L),constantInput (width := width) (2*L) (rootDims L side) input⟩],
      DenseRun.NodePayloadBound Prod.snd (32*BackendScalarBits.backendScalarUnit (W+15)*q*width)
        (rootDims L side) parent := by
    intro parent hparent
    simp only [List.mem_singleton] at hparent
    subst parent
    intro a
    rw [constantInput,SharedEncoder.read_materialize]
    dsimp only
    have hs : 1 ≤ 32*BackendScalarBits.backendScalarUnit (W+15) := by omega
    simpa only [Nat.mul_assoc,Nat.one_mul] using Nat.mul_le_mul_right (q*width) hs
  have h := run_bitWork_le L m t q width side (2*L) (rootDims L side) 0 W _ hq hw hp
    (encoded_width L m t q width W side input hwidth)
  have hv := encodeVectors_view L m t q width side input
  have hc := congrArg SharedEncoder.Result.coefficientWork hv
  have ht := congrArg SharedEncoder.Result.capWork hv
  simp only [DenseRun.mapResult_coefficientWork] at hc
  simp only [DenseRun.mapResult_capWork] at ht
  simpa only [encodeVectors,←hc,←ht] using h

/-- Source correctness discharges the width premise from the already proved
uniform coefficient invariant. The source ordering equation is erased. -/
theorem source_encode_bitWork_le {q L m t A : ℕ} [NeZero q]
    (hA : 1 ≤ A) (width : ℕ) (hw : 1 ≤ width) (side : Bool)
    (X : CompleteThinProduct.SourceWord L → CyclicRing.Cyclic q)
    (hX : ∀ a, CoefficientBounds.CoeffBound (X a) (2^(L+m)*A))
    (input : Raw L q side) (hinput : rawView input = CacheDenseLowering.sourceVectorInput side X)
    (n degree cL cm cq : ℕ) (hL : L ≤ cL*n.size) (hm : m ≤ cm*n.size)
    (hq : q ≤ 2^(cq*n.size)) (hAb : A ≤ n^degree) (ht : t ≤ 2*m) :
    bitWork (AdaptiveBitBounds.commonBitWidth n degree cL cm cq)
        (encodeVectors L m t q width side input) ≤
      ((CacheDenseLowering.encodeVectors L m t q width side (rawView input)).coefficientWork+
       (CacheDenseLowering.encodeVectors L m t q width side (rawView input)).capWork)*
        BackendScalarBits.backendScalarUnit (AdaptiveBitBounds.commonBitWidth n degree cL cm cq+15) := by
  apply encodeVectors_bitWork_le L m t q width _ side input (NeZero.one_le) hw
  rw [hinput]
  exact CacheSchemaBitBounds.source_formed_size_common hA width side X hX n degree cL cm cq hL hm hq hAb ht

namespace TrieProjection
open CacheBounds StoredHighDP

/-- Payload projection is specified only through actual trie reads. -/
def ReadRel {A B : Type*} (f : A → B) (binary : Trie A) (native : Trie B) : Prop :=
  ∀ key, (binary.read key).map f = native.read key

theorem read_empty {A : Type*} (key : List Label) :
    (Trie.empty : Trie A).read key = none := by
  induction key with
  | nil => rfl
  | cons a key _ => simp [Trie.read,Trie.child,Trie.children]

theorem ReadRel.empty {A B : Type*} (f : A → B) :
    ReadRel f (Trie.empty : Trie A) (Trie.empty : Trie B) := by
  intro key
  simp only [read_empty,Option.map_none]

theorem ReadRel.write {A B : Type*} (f : A → B) {binary : Trie A} {native : Trie B}
    (h : ReadRel f binary native) (key : List Label) (value : A) :
    ReadRel f (binary.write key value) (native.write key (f value)) := by
  intro other
  by_cases he : other = key
  · subst other
    simp only [Trie.read_write_same,Option.map_some]
  · rw [Trie.read_write_other binary key other value he,
      Trie.read_write_other native key other (f value) he]
    exact h other

theorem ReadRel.writeCounted {A B : Type*} (f : A → B)
    {binary : Trie A} {native : Trie B} (h : ReadRel f binary native)
    (key : List Label) (value : A) :
    ReadRel f (binary.writeCounted key value).1
      (native.writeCounted key (f value)).1 := by
  simp only [Trie.writeCounted_value]
  exact h.write f key value

/-- Batch insertion projection holds with repeated keys and any initial tables. -/
theorem ReadRel.storePairs {A B : Type*} {N : ℕ} (f : A → B)
    (rows : List (Word N × A)) {binary : Trie A} {native : Trie B}
    (h : ReadRel f binary native) :
    ReadRel f (CachedLowQuery.storePairs rows binary).1
      (CachedLowQuery.storePairs (rows.map (fun row => (row.1,f row.2))) native).1 := by
  induction rows generalizing binary native with
  | nil => exact h
  | cons row rows ih =>
    rcases row with ⟨word,value⟩
    simpa only [CachedLowQuery.storePairs,List.map_cons] using
      ih (h.writeCounted f (StoredHighDP.key word) value)

theorem storePairs_work_projection {A B : Type*} {N : ℕ} (f : A → B)
    (rows : List (Word N × A)) (binary : Trie A) (native : Trie B) :
    (CachedLowQuery.storePairs rows binary).2 =
      (CachedLowQuery.storePairs (rows.map (fun row => (row.1,f row.2))) native).2 := by
  simp only [CachedLowQuery.storePairs_work,List.length_map]

theorem option_getD_projection {A B : Type*} (f : A → B)
    (binary : Option A) (native : Option B) (zeroA : A) (zeroB : B)
    (h : binary.map f = native) (hz : f zeroA = zeroB) :
    f (binary.getD zeroA) = native.getD zeroB := by
  rw [← h]
  cases binary <;> simp [hz]

theorem ReadRel.getD {A B : Type*} (f : A → B)
    {binary : Trie A} {native : Trie B} (h : ReadRel f binary native)
    (key : List Label) (zeroA : A) (zeroB : B) (hz : f zeroA = zeroB) :
    f ((binary.read key).getD zeroA) = (native.read key).getD zeroB :=
  option_getD_projection f _ _ zeroA zeroB (h key) hz

theorem ReadRel.readBlock {A : Type*} {N q width : ℕ}
    (f : A → SparseLocalForms.DenseVector q width)
    {binary : Trie A} {native : CachedLowQuery.Prepared N q width}
    (h : ReadRel f binary native) (word : Word N) (zeroA : A)
    (hz : f zeroA = CachedLowQuery.zeroBlock q width) :
    f ((binary.read (StoredHighDP.key word)).getD zeroA) =
      CachedLowQuery.readBlock native word := by
  exact h.getD f (StoredHighDP.key word) zeroA (CachedLowQuery.zeroBlock q width) hz


end TrieProjection

/-- Strip only the already stored local bit-charge tag. -/
def leafPairs {q width N : ℕ} (encoded : SharedEncoder.Result (ChargedBlock q width) N) :
    List (Word N × Block q width) := encoded.leaves.map (fun leaf => (leaf.1,leaf.2.1))

theorem leafPairs_view (L m t q width : ℕ) (side : Bool) (input : Raw L q side) :
    (leafPairs (encodeVectors L m t q width side input)).map
        (fun leaf => (leaf.1,blockView leaf.2)) =
      (CacheDenseLowering.encodeVectors L m t q width side (rawView input)).leaves := by
  have h := congrArg SharedEncoder.Result.leaves (encodeVectors_view L m t q width side input)
  simpa only [leafPairs,DenseRun.mapResult_leaves,List.map_map,Function.comp_def,payloadView] using h

structure Prepared (L q width : ℕ) where
  encoding : SharedEncoder.Result (ChargedBlock q width) (2*L)
  table : BinaryLowQuery.Cache (2*L) q width
  bitSteps : ℕ

/-- Literal insertion consumes the actual binary leaves. The charge
collector reads stored numeric tags; it never invokes a bit primitive again. -/
def prepareVectors {L m t q width : ℕ} (W : ℕ) (side : Bool) (input : Raw L q side) :
    Prepared L q width :=
  let encoded := encodeVectors L m t q width side input
  let rows := leafPairs encoded
  let stored := CachedLowQuery.storePairs rows .empty
  ⟨encoded,stored.1,bitWork W encoded+
    (stored.2+rows.length*(q*width))*BackendScalarBits.backendScalarUnit (W+15)⟩

theorem prepareVectors_readRel {L m t q width : ℕ} (W : ℕ) (side : Bool) (input : Raw L q side) :
    TrieProjection.ReadRel blockView (prepareVectors (m := m) (t := t) (width := width) W side input).table
      (CacheDenseLowering.prepareVectors (m := m) (t := t) (width := width) side (rawView input)).1 := by
  have h := TrieProjection.ReadRel.storePairs blockView
    (leafPairs (encodeVectors L m t q width side input)) (TrieProjection.ReadRel.empty blockView)
  rw [leafPairs_view] at h
  exact h

/-- The concrete binary trie is directly consumable by the actual binary
LOW query. This closes its cache-projection premise for these produced leaves. -/
theorem prepareVectors_cacheRefines {L m t q width : ℕ} (W : ℕ) (side : Bool) (input : Raw L q side) :
    BinaryLowQuery.CacheRefines (prepareVectors (m := m) (t := t) (width := width) W side input).table
      (CacheDenseLowering.prepareVectors (m := m) (t := t) (width := width) side (rawView input)).1 := by
  intro key
  have h := (prepareVectors_readRel (m := m) (t := t) W side input).getD blockView
    (StoredHighDP.key (ArrayKeys.toWord key)) (zeroBlock q width)
    (CachedLowQuery.zeroBlock q width) (zeroBlock_view q width)
  have hz : BinaryLowQuery.zeroBlock q width = zeroBlock q width := by
    apply Vector.ext
    intro i hi
    simp [BinaryLowQuery.zeroBlock,zeroBlock,BinaryCell.zero]
  change blockView ((ArrayKeys.read (prepareVectors (m := m) (t := t) (width := width) W side input).table key).1.getD
      (BinaryLowQuery.zeroBlock q width)) = _
  rw [hz]
  simpa only [CachedLowQuery.readKeyBlockCounted,ArrayKeys.read_value] using h

theorem prepareVectors_bitWork_le {L m t q width : ℕ} (W : ℕ) (side : Bool) (input : Raw L q side)
    (hq : 1 ≤ q) (hw : 1 ≤ width)
    (hwidth : ∀ s ∈ (CacheDenseLowering.encodeVectors L m t q width side (rawView input)).formed,
      ∀ a d r, (SparseLocalForms.denseRead (SharedEncoder.read s.remaining s.dims s.node.data a) d r).natAbs.size ≤ W) :
    (prepareVectors (m := m) (t := t) (width := width) W side input).bitSteps ≤
      (CacheDenseLowering.prepareVectors (m := m) (t := t) (width := width) side (rawView input)).2*
        BackendScalarBits.backendScalarUnit (W+15) := by
  have h := encodeVectors_bitWork_le L m t q width W side input hq hw hwidth
  have hs := TrieProjection.storePairs_work_projection blockView
    (leafPairs (encodeVectors L m t q width side input))
    (StoredHighDP.Trie.empty : StoredHighDP.Trie (Block q width))
    (StoredHighDP.Trie.empty : StoredHighDP.Trie (SparseLocalForms.DenseVector q width))
  rw [leafPairs_view] at hs
  have hl := congrArg List.length (leafPairs_view L m t q width side input)
  simp only [List.length_map] at hl
  change bitWork W (encodeVectors L m t q width side input)+
      ((CachedLowQuery.storePairs (leafPairs (encodeVectors L m t q width side input)) .empty).2+
        (leafPairs (encodeVectors L m t q width side input)).length*(q*width))*
          BackendScalarBits.backendScalarUnit (W+15) ≤ _
  rw [hs,hl]
  unfold CacheDenseLowering.prepareVectors CacheDenseLowering.prepare
  change _ ≤ ((CacheDenseLowering.encodeVectors L m t q width side (rawView input)).coefficientWork+
    (CacheDenseLowering.encodeVectors L m t q width side (rawView input)).capWork+
    (CachedLowQuery.storePairs (CacheDenseLowering.encodeVectors L m t q width side (rawView input)).leaves .empty).2+
    (CacheDenseLowering.encodeVectors L m t q width side (rawView input)).leaves.length*(q*width))*_
  nlinarith

/-- Fully source-instantiated bit price, with no assumed encoder-time bound
and no intermediate conversion of native integers back to binary cells. -/
theorem source_prepare_bitWork_le {q L m t A : ℕ} [NeZero q]
    (hA : 1 ≤ A) (width : ℕ) (hw : 1 ≤ width) (side : Bool)
    (X : CompleteThinProduct.SourceWord L → CyclicRing.Cyclic q)
    (hX : ∀ a, CoefficientBounds.CoeffBound (X a) (2^(L+m)*A))
    (input : Raw L q side) (hinput : rawView input = CacheDenseLowering.sourceVectorInput side X)
    (n degree cL cm cq : ℕ) (hL : L ≤ cL*n.size) (hm : m ≤ cm*n.size)
    (hq : q ≤ 2^(cq*n.size)) (hAb : A ≤ n^degree) (ht : t ≤ 2*m) :
    (prepareVectors (m := m) (t := t) (width := width) (AdaptiveBitBounds.commonBitWidth n degree cL cm cq) side input).bitSteps ≤
      (CacheDenseLowering.prepareVectors (m := m) (t := t) (width := width) side (rawView input)).2*
        BackendScalarBits.backendScalarUnit (AdaptiveBitBounds.commonBitWidth n degree cL cm cq+15) := by
  apply prepareVectors_bitWork_le _ side input NeZero.one_le hw
  rw [hinput]
  exact CacheSchemaBitBounds.source_formed_size_common hA width side X hX n degree cL cm cq hL hm hq hAb ht

/-- The shared raw-source initializer executes binary copies and literal
source-letter decoding. Its integer source ordering occurs only in this proof. -/
theorem rawInput_view {L q : ℕ} (side : Bool) (raw : BinarySourceFormation.RawStore L q) :
    rawView (BinaryHighExecution.rawInput side raw).value =
      CacheDenseLowering.sourceVectorInput side
        (ThinMatrixBackend.sourceValue (BinarySourceFormation.viewRaw raw)) := by
  apply CacheDenseLowering.dense_ext
  intro a
  rw [rawView,DenseRun.read_mapDense]
  have h := congrArg (fun data => SharedEncoder.read (2*L) (rootDims L side) data a)
    (BinaryHighExecution.rawInput_view side raw)
  change SharedEncoder.read (2*L) (HighBaseEncoder.rootDims L side)
    (BinaryHighExecution.denseView (2*L) (HighBaseEncoder.rootDims L side)
      (BinaryHighExecution.rawInput side raw).value) a = _ at h
  rw [BinaryHighExecution.read_denseView] at h
  cases side <;> exact h

/-- Actual raw-source-to-cache entry point, with auxiliary width `2m+1`.
Both the initial copies and the subsequent encoder counter are retained. -/
def prepareRawSource {L m t q : ℕ} (W : ℕ) (side : Bool)
    (raw : BinarySourceFormation.RawStore L q) : Prepared L q (2*m+1) :=
  let input := BinaryHighExecution.rawInput side raw
  let prepared := prepareVectors (m := m) (t := t) (width := 2*m+1) W side input.value
  { prepared with bitSteps := input.bitSteps+prepared.bitSteps }

theorem prepareRawSource_cacheRefines {L m t q : ℕ} (W : ℕ) (side : Bool)
    (raw : BinarySourceFormation.RawStore L q) :
    BinaryLowQuery.CacheRefines (prepareRawSource (m := m) (t := t) W side raw).table
      (CacheDenseLowering.prepareSource (m := m) (t := t) (width := 2*m+1) side
        (ThinMatrixBackend.sourceValue (BinarySourceFormation.viewRaw raw))).1 := by
  have h := prepareVectors_cacheRefines (m := m) (t := t) (width := 2*m+1) W side
    (BinaryHighExecution.rawInput side raw).value
  rw [rawInput_view] at h
  exact h

/-- The encoder portion of raw-source preparation has its closed common
width price; the independently executed source-copy counter is explicit. -/
theorem source_prepareRaw_bitWork_le {q L m t A : ℕ} [NeZero q]
    (hA : 1 ≤ A) (side : Bool) (raw : BinarySourceFormation.RawStore L q)
    (hX : ∀ a, CoefficientBounds.CoeffBound
      (ThinMatrixBackend.sourceValue (BinarySourceFormation.viewRaw raw) a) (2^(L+m)*A))
    (n degree cL cm cq : ℕ) (hL : L ≤ cL*n.size) (hm : m ≤ cm*n.size)
    (hq : q ≤ 2^(cq*n.size)) (hAb : A ≤ n^degree) (ht : t ≤ 2*m) :
    (prepareRawSource (m := m) (t := t) (AdaptiveBitBounds.commonBitWidth n degree cL cm cq) side raw).bitSteps ≤
      (BinaryHighExecution.rawInput side raw).bitSteps+
      (CacheDenseLowering.prepareSource (m := m) (t := t) (width := 2*m+1) side
        (ThinMatrixBackend.sourceValue (BinarySourceFormation.viewRaw raw))).2*
        BackendScalarBits.backendScalarUnit (AdaptiveBitBounds.commonBitWidth n degree cL cm cq+15) := by
  have h := source_prepare_bitWork_le hA (2*m+1) (by omega) side
    (ThinMatrixBackend.sourceValue (BinarySourceFormation.viewRaw raw)) hX
    (BinaryHighExecution.rawInput side raw).value (rawInput_view side raw)
    n degree cL cm cq hL hm hq hAb ht
  rw [rawInput_view] at h
  exact Nat.add_le_add_left h _

namespace RawPrice
open CacheBounds SharedEncoder

/-- The native ledger includes the full initial layer before any recursive work. -/
theorem run_root_work_strong (L m t q width : ℕ) (side : Bool)
    (n : ℕ) (dims : Fin n → ℕ) (d : ℕ)
    (parents : List (CacheDenseLowering.DataNode q width (2*L) n dims)) :
    84*q*width*parents.length*volume n dims ≤
      (CacheDenseLowering.run L m t q width side n dims d parents).coefficientWork := by
  cases n with
  | zero => exact le_refl _
  | succ n =>
    simp only [CacheDenseLowering.run]
    split
    · exact Nat.le_add_right _ _
    · exact le_refl _

theorem run_root_work (L m t q width : ℕ) (side : Bool)
    (n : ℕ) (dims : Fin n → ℕ) (d : ℕ)
    (parents : List (CacheDenseLowering.DataNode q width (2*L) n dims)) :
    q*width*parents.length*volume n dims ≤
      (CacheDenseLowering.run L m t q width side n dims d parents).coefficientWork := by
  calc
    _ ≤ 84*(q*width*parents.length*volume n dims) := by omega
    _ = 84*q*width*parents.length*volume n dims := by ring
    _ ≤ _ := run_root_work_strong L m t q width side n dims d parents

theorem encodeVectors_root_work {L m t q width : ℕ} (hw : 1 ≤ width) (side : Bool)
    (input : SharedEncoder.Dense (R := Vector ℤ q) (2*L) (rootDims L side)) :
    q*volume (2*L) (rootDims L side) ≤
      (CacheDenseLowering.encodeVectors L m t q width side input).coefficientWork := by
  have hroot := run_root_work L m t q width side (2*L) (rootDims L side) 0
    [⟨CappedEnumeration.zeroWord (2*L),
      CacheDenseLowering.constantInput (2*L) (rootDims L side) input⟩]
  simp only [List.length_singleton,Nat.mul_one] at hroot
  change q*width*volume (2*L) (rootDims L side) ≤
    (CacheDenseLowering.encodeVectors L m t q width side input).coefficientWork at hroot
  calc
    _ ≤ q*width*volume (2*L) (rootDims L side) := by
      simpa only [Nat.mul_one] using
        Nat.mul_le_mul_right (volume (2*L) (rootDims L side)) (Nat.mul_le_mul_left q hw)
    _ ≤ _ := hroot

theorem prepareVectors_root_work {L m t q width : ℕ} (hw : 1 ≤ width) (side : Bool)
    (input : SharedEncoder.Dense (R := Vector ℤ q) (2*L) (rootDims L side)) :
    q*volume (2*L) (rootDims L side) ≤
      (CacheDenseLowering.prepareVectors (m := m) (t := t) (width := width) side input).2 := by
  calc
    _ ≤ (CacheDenseLowering.encodeVectors L m t q width side input).coefficientWork :=
      encodeVectors_root_work hw side input
    _ ≤ _ := by
      simp only [CacheDenseLowering.prepareVectors,CacheDenseLowering.prepare,
        CacheDenseLowering.encodeVectors]
      omega

theorem source_size_le_common (n degree L m A cL cm cq : ℕ)
    (hL : L ≤ cL*n.size) (hm : m ≤ cm*n.size) (hA : A ≤ n^degree) :
    (2^(L+m)*A).size ≤ AdaptiveBitBounds.commonBitWidth n degree cL cm cq := by
  have hbound := Nat.mul_le_mul_left (2^(L+m))
    (AdaptiveBitBounds.original_power_bound n degree A hA)
  rw [← pow_add] at hbound
  have hsize := (Nat.size_le_size hbound).trans_eq Nat.size_pow
  have hexp : L+m+degree*n.size+1 ≤ (cL+cm+degree+1)*(n.size+1) := by nlinarith
  have hconst : cL+cm+degree+1 ≤
      CoefficientBudget.budgetConstant cL cm cq degree+2*(4*cm+2)^2+20 := by
    unfold CoefficientBudget.budgetConstant
    omega
  have hp : n.size+1 ≤ (n.size+1)^2 := by nlinarith
  calc
    (2^(L+m)*A).size ≤ L+m+degree*n.size+1 := hsize
    _ ≤ (cL+cm+degree+1)*(n.size+1) := hexp
    _ ≤ (CoefficientBudget.budgetConstant cL cm cq degree+2*(4*cm+2)^2+20)*(n.size+1) :=
      Nat.mul_le_mul_right _ hconst
    _ ≤ (CoefficientBudget.budgetConstant cL cm cq degree+2*(4*cm+2)^2+20)*(n.size+1)^2 :=
      Nat.mul_le_mul_left _ hp
    _ = AdaptiveBitBounds.commonBitWidth n degree cL cm cq := rfl


end RawPrice

/-- The common scalar adapter remains a fixed polynomial in the input
bit length; its constants depend only on the fixed phase parameters. -/
def scalarConstant (degree cL cm cq : ℕ) : ℕ :=
  CoefficientBudget.budgetConstant cL cm cq degree+2*(4*cm+2)^2+35

theorem commonScalarUnit_le (n degree cL cm cq : ℕ) :
    BackendScalarBits.backendScalarUnit (AdaptiveBitBounds.commonBitWidth n degree cL cm cq+15) ≤
      800*(scalarConstant degree cL cm cq+1)^2*(n.size+1)^4 := by
  apply BackendScalarBits.backendScalarUnit_le_quartic
  have hp : 1 ≤ (n.size+1)^2 := Nat.one_le_pow 2 (n.size+1) (by omega)
  unfold AdaptiveBitBounds.commonBitWidth scalarConstant
  nlinarith

theorem rawScalarFactor_quartic (n degree L cL cm cq : ℕ) (hL : L ≤ cL*n.size) :
    2*BackendScalarBits.backendScalarUnit
        (AdaptiveBitBounds.commonBitWidth n degree cL cm cq+15)+6*L+3 ≤
      (1600*(scalarConstant degree cL cm cq+1)^2+6*cL+3)*
        (n.size+1)^4 := by
  have hs := commonScalarUnit_le n degree cL cm cq
  have hp : n.size+1 ≤ (n.size+1)^4 := by
    simpa only [pow_one] using
      (Nat.pow_le_pow_right (by omega : 0 < n.size+1) (by omega : 1 ≤ 4))
  have hp' : 1 ≤ (n.size+1)^4 := by omega
  have hL' : L ≤ cL*(n.size+1)^4 :=
    hL.trans (Nat.mul_le_mul_left cL (by omega))
  have hrest : 6*L+3 ≤ (6*cL+3)*(n.size+1)^4 := by nlinarith
  calc
    _ ≤ 2*(800*(scalarConstant degree cL cm cq+1)^2*(n.size+1)^4)+
        (6*cL+3)*(n.size+1)^4 := by nlinarith only [hs,hrest]
    _ = _ := by ring


/-- The genuine source coefficient cap is exactly the raw binary read
cap needed by the shared initializer; integer views remain proof-only. -/
theorem rawBound_of_sourceBound {L q A : ℕ} (raw : BinarySourceFormation.RawStore L q)
    (hX : ∀ a, CoefficientBounds.CoeffBound
      (ThinMatrixBackend.sourceValue (BinarySourceFormation.viewRaw raw) a) A) :
    BinaryHighExecution.RawBound raw A := by
  intro normal opposite r
  have h := hX (normal,opposite) r
  change |SourceFormation.readRaw (BinarySourceFormation.viewRaw raw) normal opposite r| ≤ (A:ℤ) at h
  rw [BinarySourceFormation.readRaw_view] at h
  exact h

/-- Initial source copies are charged to the already allocated native
LOW root layer. There is no free initialization or assumed copy oracle. -/
theorem source_rawInput_bitWork_le {q L m t A : ℕ} [NeZero q]
    (side : Bool) (raw : BinarySourceFormation.RawStore L q)
    (hX : ∀ a, CoefficientBounds.CoeffBound
      (ThinMatrixBackend.sourceValue (BinarySourceFormation.viewRaw raw) a) (2^(L+m)*A))
    (n degree cL cm cq : ℕ) (hL : L ≤ cL*n.size) (hm : m ≤ cm*n.size) (hAb : A ≤ n^degree) :
    (BinaryHighExecution.rawInput side raw).bitSteps ≤
      (CacheDenseLowering.prepareSource (m := m) (t := t) (width := 2*m+1) side
        (ThinMatrixBackend.sourceValue (BinarySourceFormation.viewRaw raw))).2*
      (BackendScalarBits.backendScalarUnit (AdaptiveBitBounds.commonBitWidth n degree cL cm cq+15)+6*L+3) := by
  let W := AdaptiveBitBounds.commonBitWidth n degree cL cm cq
  have hs := RawPrice.source_size_le_common n degree L m A cL cm cq hL hm hAb
  have hu : BackendScalarBits.backendScalarUnit (2^(L+m)*A).size ≤
      BackendScalarBits.backendScalarUnit (W+15) := by
    unfold BackendScalarBits.backendScalarUnit BackendScalarBits.scalarUnit
    dsimp only [W]
    gcongr
    omega
  have h := BinaryHighExecution.rawInput_bit_price side raw (2^(L+m)*A)
    (rawBound_of_sourceBound raw hX)
  have hroot := RawPrice.prepareVectors_root_work (m := m) (t := t) (width := 2*m+1)
    (by omega) side (CacheDenseLowering.sourceVectorInput side
      (ThinMatrixBackend.sourceValue (BinarySourceFormation.viewRaw raw)))
  have hc : q*(BackendScalarBits.backendScalarUnit (2^(L+m)*A).size+2*L+3)+4*L ≤
      q*(BackendScalarBits.backendScalarUnit (W+15)+6*L+3) := by
    have hq : 1 ≤ q := NeZero.one_le
    nlinarith
  apply h.trans
  apply (Nat.mul_le_mul_left _ hc).trans
  change SharedEncoder.volume (2*L) (rootDims L side)*
    (q*(BackendScalarBits.backendScalarUnit (W+15)+6*L+3)) ≤ _
  calc
    _ = (q*SharedEncoder.volume (2*L) (rootDims L side))*
      (BackendScalarBits.backendScalarUnit (W+15)+6*L+3) := by ring
    _ ≤ _ := Nat.mul_le_mul_right _ hroot

/-- The complete raw binary source to stored LOW cache has a closed bit
price against the native cache ledger. Both source initialization and every
local binary operation are included. -/
theorem source_prepareRaw_closed_bitWork_le {q L m t A : ℕ} [NeZero q]
    (hA : 1 ≤ A) (side : Bool) (raw : BinarySourceFormation.RawStore L q)
    (hX : ∀ a, CoefficientBounds.CoeffBound
      (ThinMatrixBackend.sourceValue (BinarySourceFormation.viewRaw raw) a) (2^(L+m)*A))
    (n degree cL cm cq : ℕ) (hL : L ≤ cL*n.size) (hm : m ≤ cm*n.size)
    (hq : q ≤ 2^(cq*n.size)) (hAb : A ≤ n^degree) (ht : t ≤ 2*m) :
    (prepareRawSource (m := m) (t := t) (AdaptiveBitBounds.commonBitWidth n degree cL cm cq) side raw).bitSteps ≤
      (CacheDenseLowering.prepareSource (m := m) (t := t) (width := 2*m+1) side
        (ThinMatrixBackend.sourceValue (BinarySourceFormation.viewRaw raw))).2*
      (2*BackendScalarBits.backendScalarUnit (AdaptiveBitBounds.commonBitWidth n degree cL cm cq+15)+6*L+3) := by
  have hp := source_prepareRaw_bitWork_le hA side raw hX n degree cL cm cq hL hm hq hAb ht
  have hi := source_rawInput_bitWork_le (m := m) (t := t) side raw hX n degree cL cm cq hL hm hAb
  nlinarith

/-- Explicit polynomial-logarithmic overhead for the whole binary
source-to-LOW-cache execution, including initial physical source copies. -/
theorem source_prepareRaw_polylog {q L m t A : ℕ} [NeZero q]
    (hA : 1 ≤ A) (side : Bool) (raw : BinarySourceFormation.RawStore L q)
    (hX : ∀ a, CoefficientBounds.CoeffBound
      (ThinMatrixBackend.sourceValue (BinarySourceFormation.viewRaw raw) a) (2^(L+m)*A))
    (n degree cL cm cq : ℕ) (hL : L ≤ cL*n.size) (hm : m ≤ cm*n.size)
    (hq : q ≤ 2^(cq*n.size)) (hAb : A ≤ n^degree) (ht : t ≤ 2*m) :
    (prepareRawSource (m := m) (t := t) (AdaptiveBitBounds.commonBitWidth n degree cL cm cq) side raw).bitSteps ≤
      (CacheDenseLowering.prepareSource (m := m) (t := t) (width := 2*m+1) side
        (ThinMatrixBackend.sourceValue (BinarySourceFormation.viewRaw raw))).2*
      (1600*(scalarConstant degree cL cm cq+1)^2+6*cL+3)*(n.size+1)^4 := by
  have h := source_prepareRaw_closed_bitWork_le hA side raw hX n degree cL cm cq hL hm hq hAb ht
  have hf := rawScalarFactor_quartic n degree L cL cm cq hL
  calc
    _ ≤ _ := h
    _ ≤ _ := by
      have hh := Nat.mul_le_mul_left
        ((CacheDenseLowering.prepareSource (m := m) (t := t) (width := 2*m+1) side
          (ThinMatrixBackend.sourceValue (BinarySourceFormation.viewRaw raw))).2) hf
      simpa only [Nat.mul_assoc] using hh

/-- Canonical stored binary magnitudes satisfy the same width invariant,
so the array storage bound counts actual Boolean cells. -/
theorem encoded_cell_length {L m t q width W : ℕ} (side : Bool) (input : Raw L q side)
    (hwidth : ∀ s ∈ (CacheDenseLowering.encodeVectors L m t q width side (rawView input)).formed,
      ∀ a d r, (SparseLocalForms.denseRead (SharedEncoder.read s.remaining s.dims s.node.data a) d r).natAbs.size ≤ W)
    (s : SharedEncoder.Stored (ChargedBlock q width) (2*L))
    (hs : s ∈ (encodeVectors L m t q width side input).formed)
    (a : Coordinates s.dims) (d : Fin width) (r : Fin q) :
    (((SharedEncoder.read s.remaining s.dims s.node.data a).1.get d).get r).bits.magnitude.length ≤ W := by
  rw [BinaryCell.canonical]
  simpa only [NodeWidth,payloadView,blockView_read] using
    encoded_width L m t q width W side input hwidth s hs a d r

/- Finite execution smoke check: thirty-five retained leaves, including
actual dense binary row arithmetic and trie insertion. -/
#eval let input : Raw 1 1 true := SharedEncoder.materialize 2 (rootDims 1 true)
        (fun _ => Vector.replicate 1 (BinaryCell.coefficient true 0 0))
      let prepared := prepareVectors (m := 1) (t := 1) (width := 3) 8 true input
      (prepared.encoding.leaves.length,prepared.bitSteps)

#print axioms runInstructions_view
#print axioms rowBlock_view
#print axioms contract_view
#print axioms run_view
#print axioms encodeVectors_view
#print axioms encodeVectors_bitWork_le
#print axioms prepareVectors_readRel
#print axioms prepareVectors_cacheRefines
#print axioms prepareVectors_bitWork_le
#print axioms source_prepare_bitWork_le
#print axioms encoded_cell_length
#print axioms commonScalarUnit_le
#print axioms rawInput_view
#print axioms prepareRawSource_cacheRefines
#print axioms source_prepareRaw_bitWork_le
#print axioms rawBound_of_sourceBound
#print axioms source_rawInput_bitWork_le
#print axioms source_prepareRaw_closed_bitWork_le
#print axioms rawScalarFactor_quartic
#print axioms source_prepareRaw_polylog

end ThinMatrix.BinaryLowEncoder
