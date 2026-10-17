import BitArraySimulation
import BinaryArrayFFT
import CachedLowQuery
import BackendScalarBits
import BinaryQueryWeights
import BinaryLowBounds

/-!
Actual signed-bit LOW contractions over already stored binary cache leaves.
The runtime query contains no semantic integer or polynomial arithmetic:
coefficient reads copy Boolean magnitudes, products and sums use canonical
binary primitives, and auxiliary/cyclic indices are kept separate. Native
cache values below are proof-only projections.
-/

set_option maxRecDepth 10000
set_option maxHeartbeats 2000000

namespace ThinMatrix.BinaryLowQuery
open scoped BigOperators
open BitArraySimulation ToomCook

abbrev Block (q width : ℕ) := Vector (Vector BinaryArrayFFT.Integer q) width
abbrev Cache (_N q width : ℕ) := StoredHighDP.Trie (Block q width)
abbrev SourceCaches (L q width : ℕ) := Cache (2*L) q width × Cache (2*L) q width
abbrev RunCaches (L m q width : ℕ) := Vector (SourceCaches L q width) (2*m+1)

def blockView {q width : ℕ} (a : Block q width) : SparseLocalForms.DenseVector q width :=
  a.map (fun row => row.map BinaryArrayFFT.Integer.view)

def zeroBlock (q width : ℕ) : Block q width :=
  Vector.ofFn (fun _ : Fin width => Vector.replicate q BinaryArrayFFT.zeroInteger)

theorem blockView_zero (q width : ℕ) :
    blockView (zeroBlock q width)=CachedLowQuery.zeroBlock q width := by
  apply Vector.ext
  intro i hi
  apply Vector.ext
  intro r hr
  simp [blockView,zeroBlock,CachedLowQuery.zeroBlock]

def normalizeCell (a : BinaryArrayFFT.Integer) : Counted Signed :=
  let normalized := IntegerArithmetic.normalizeSignedCounted a.bits
  ⟨⟨normalized.1,by
    dsimp only [normalized]
    simp only [Canonical,IntegerArithmetic.normalizeSignedCounted_value,
      IntegerArithmetic.ofInt_correct]⟩,normalized.2⟩

theorem normalizeCell_value (a : BinaryArrayFFT.Integer) :
    denote (normalizeCell a).value=a.view := by
  simp only [normalizeCell,denote,IntegerArithmetic.normalizeSignedCounted_value,
    IntegerArithmetic.ofInt_correct,BinaryArrayFFT.Integer.view]

def readCoefficient {q width : ℕ} (a : Block q width) (degree : ℕ) (residue : Fin q) :
    Counted Signed :=
  if hd : degree<width then
    let copied := normalizeCell ((a.get ⟨degree,hd⟩).get residue)
    ⟨copied.value,copied.operations+degree.size+residue.val.size+3⟩
  else ⟨zero,degree.size+2⟩

theorem readCoefficient_value {q width : ℕ} (a : Block q width) (degree : ℕ)
    (residue : Fin q) :
    denote (readCoefficient a degree residue).value=
      CachedLowQuery.blockCoeff (blockView a) degree residue := by
  simp only [readCoefficient,CachedLowQuery.blockCoeff]
  split_ifs with hd
  · simp only [normalizeCell_value,blockView,Vector.get_map]
  · rfl

/-- Each callback, recursive tail and arithmetic result is evaluated once. -/
def sumValues {ι : Type*} (f : ι → Counted Signed) : List ι → Counted Signed
  | [] => ⟨zero,1⟩
  | i::is =>
    let head := f i
    let tail := sumValues f is
    let result := BitArraySimulation.add head.value tail.value
    ⟨result.value,head.operations+tail.operations+result.operations+2⟩

theorem sumValues_value {ι : Type*} (f : ι → Counted Signed) (is : List ι) :
    denote (sumValues f is).value=(is.map (fun i => denote (f i).value)).sum := by
  induction is with
  | nil => rfl
  | cons i is ih => simp only [sumValues,add_value,ih,List.map_cons,List.sum_cons]

theorem sumValues_cost {ι : Type*} (f : ι → Counted Signed) (is : List ι) (A n : ℕ) :
    is.length ≤ n →
    (∀ i ∈ is, |denote (f i).value| ≤ (A:ℤ)) →
    (sumValues f is).operations ≤
      (is.map (fun i => (f i).operations)).sum+
      is.length*(50*(max A.size (n*A).size+1)+2)+1 := by
  induction is with
  | nil => intro _ _; simp [sumValues]
  | cons i is ih =>
    intro hlen hf
    have htail : is.length ≤ n := by simpa only [List.length_cons] using Nat.le_trans (Nat.le_succ _) hlen
    have hftail : ∀ j ∈ is, |denote (f j).value| ≤ (A:ℤ) :=
      fun j hj => hf j (List.mem_cons_of_mem i hj)
    have hhead : (denote (f i).value).natAbs ≤ A := by
      have h := hf i (by simp)
      rw [←Int.natCast_natAbs] at h
      exact_mod_cast h
    have ht : (denote (sumValues f is).value).natAbs ≤ n*A := by
      have h := BinaryLowBounds.list_partial_bound is (fun i => denote (f i).value) A n htail hftail
      rw [←sumValues_value f is,←Int.natCast_natAbs] at h
      exact_mod_cast h
    have hheadsize : (denote (f i).value).natAbs.size ≤ A.size := Nat.size_le_size hhead
    have htailsize : (denote (sumValues f is).value).natAbs.size ≤ (n*A).size := Nat.size_le_size ht
    have hsumcost : (BitArraySimulation.add (f i).value (sumValues f is).value).operations ≤
        50*(max A.size (n*A).size+1) := by
      rw [BitArraySimulation.add_cost]
      apply (ToomBitCost.bitPrimitive_add_cost _ _).trans
      gcongr
    have hi := ih htail hftail
    simp only [sumValues,List.map_cons,List.sum_cons,List.length_cons,Nat.add_mul]
    omega


def selectedDot {q width : ℕ} [NeZero q] (left right : Block q width)
    (leftDegree rightDegree : ℕ) (target : Fin q) : Counted Signed :=
  let rows := sumValues (fun r : Fin q =>
    BitArraySimulation.bind (readCoefficient left leftDegree r) (fun x =>
      BitArraySimulation.bind (readCoefficient right rightDegree (target-r)) (fun y =>
        let product := BitArraySimulation.mul x y
        ⟨product.value,product.operations+4*(q.size+1)^2⟩))) (List.finRange q)
  ⟨rows.value,rows.operations+2*q*(q.size+1)⟩

theorem selectedDot_value {q width : ℕ} [NeZero q] (left right : Block q width)
    (leftDegree rightDegree : ℕ) (target : Fin q) :
    denote (selectedDot left right leftDegree rightDegree target).value=
      (CachedLowQuery.selectedDot (CachedLowQuery.blockCoeff (blockView left) leftDegree)
        (CachedLowQuery.blockCoeff (blockView right) rightDegree) target).1 := by
  simp only [selectedDot,sumValues_value,BitArraySimulation.bind,mul_value,
    readCoefficient_value,CachedLowQuery.selectedDot]

def polynomialDot {q width : ℕ} [NeZero q] (left right : Block q width)
    (degree : ℕ) (target : Fin q) : Counted Signed :=
  let rows := sumValues (fun a => selectedDot left right a (degree-a) target)
    (List.range (degree+1))
  ⟨rows.value,rows.operations+2*(degree+1)*(degree.size+1)⟩

theorem polynomialDot_value {q width : ℕ} [NeZero q] (left right : Block q width)
    (degree : ℕ) (target : Fin q) :
    denote (polynomialDot left right degree target).value=
      (CachedLowQuery.polynomialDot (blockView left) (blockView right) degree target).1 := by
  simp only [polynomialDot,sumValues_value,selectedDot_value,CachedLowQuery.polynomialDot,
    List.map_map,Function.comp_def]

structure WeightProgram where
  run : ℕ → ℕ → ℕ → Counted Signed
  correct : ∀ k t degree, denote (run k t degree).value=(CachedLowQuery.weightCounted k t degree).1

def actualWeights : WeightProgram :=
  ⟨BinaryQueryWeights.weight,BinaryQueryWeights.weight_value⟩

def lowTerm {q width : ℕ} [NeZero q] (weights : WeightProgram) (k t : ℕ)
    (left right : Block q width) (channelCard degree : ℕ) (target : Fin q) : Counted Signed :=
  if channelCard≤degree then
    let dot := polynomialDot left right (degree-channelCard) target
    let weight := weights.run k t degree
    let result := BitArraySimulation.mul weight.value dot.value
    ⟨result.value,dot.operations+weight.operations+result.operations+
      4*(channelCard.size+degree.size+1)^2⟩
  else ⟨zero,4*(channelCard.size+degree.size+1)^2⟩

theorem lowTerm_value {q width : ℕ} [NeZero q] (weights : WeightProgram) (k t : ℕ)
    (left right : Block q width) (channelCard degree : ℕ) (target : Fin q) :
    denote (lowTerm weights k t left right channelCard degree target).value=
      (CachedLowQuery.lowTerm k t (blockView left) (blockView right) channelCard degree target).1 := by
  simp only [lowTerm,CachedLowQuery.lowTerm]
  split_ifs
  · simp only [mul_value,polynomialDot_value,weights.correct]
  · rfl

def readBlock {N q width : ℕ} (table : Cache N q width) (key : ArrayKeys.Key N) :
    Block q width × ℕ :=
  let found := ArrayKeys.read table key
  (found.1.getD (zeroBlock q width),found.2+N+1+3*q*width)

/-- A proof-only relation between binary payloads and an existing cache.
It asserts scalar equality on actual trie lookups, with no runtime `ofInt`. -/
def CacheRefines {N q width : ℕ} (binary : Cache N q width)
    (native : CachedLowQuery.Prepared N q width) : Prop :=
  ∀ key, blockView (readBlock binary key).1=(CachedLowQuery.readKeyBlockCounted native key).1

def channelQuery {N q width : ℕ} [NeZero q] (weights : WeightProgram) (k t : ℕ)
    (left right : Cache N q width) (key : ArrayKeys.Key N) (channelCard : ℕ)
    (target : Fin q) : Counted Signed :=
  let a := readBlock left key
  let b := readBlock right key
  let rows := sumValues (fun degree => lowTerm weights k t a.1 b.1 channelCard degree target)
    (List.range t)
  ⟨rows.value,a.2+b.2+rows.operations+2*t*(t.size+1)⟩

theorem channelQuery_value {N q width : ℕ} [NeZero q] (weights : WeightProgram) (k t : ℕ)
    (left right : Cache N q width) (nativeLeft nativeRight : CachedLowQuery.Prepared N q width)
    (hl : CacheRefines left nativeLeft) (hr : CacheRefines right nativeRight)
    (key : ArrayKeys.Key N) (channelCard : ℕ) (target : Fin q) :
    denote (channelQuery weights k t left right key channelCard target).value=
      (CachedLowQuery.channelKeyQuery k t nativeLeft nativeRight key channelCard target).1 := by
  simp only [channelQuery,sumValues_value,lowTerm_value,hl key,hr key,
    CachedLowQuery.channelKeyQuery,List.map_map,Function.comp_def]

def querySources {L k q width : ℕ} [NeZero q] (weights : WeightProgram) (t : ℕ)
    (channels : List (List (Fin k))) (embedding : Vector (Fin (2*L)) k)
    (ordinary : Vector (Fin 4) (2*L)) (cache : SourceCaches L q width) (target : Fin q) :
    Counted Signed :=
  sumValues (fun cs =>
    let key := CachedLowQuery.physicalKey embedding ordinary cs
    let answer := channelQuery weights k t cache.1 cache.2 key.1 cs.length target
    ⟨answer.value,key.2+answer.operations⟩) channels

theorem querySources_value {L k q width : ℕ} [NeZero q] (weights : WeightProgram) (t : ℕ)
    (channels : List (List (Fin k))) (embedding : Vector (Fin (2*L)) k)
    (ordinary : Vector (Fin 4) (2*L)) (cache : SourceCaches L q width)
    (native : CachedLowQuery.SourceCaches L q width)
    (hl : CacheRefines cache.1 native.1) (hr : CacheRefines cache.2 native.2) (target : Fin q) :
    denote (querySources weights t channels embedding ordinary cache target).value=
      (CachedLowQuery.querySources t channels embedding ordinary native target).1 := by
  simp only [querySources,sumValues_value,CachedLowQuery.querySources,
    CachedLowQuery.physicalQueryChannels,List.map_map,Function.comp_def]
  apply congrArg List.sum
  apply List.map_congr_left
  intro cs _
  exact channelQuery_value weights k t _ _ _ _ hl hr _ _ _

def queryRuns {L m k q width : ℕ} [NeZero q] (weights : WeightProgram) (t : ℕ)
    (channels : List (List (Fin k))) (embedding : Vector (Fin (2*L)) k)
    (ordinary : Vector (Fin 4) (2*L)) (caches : RunCaches L m q width) (target : Fin q) :
    Counted Signed :=
  let answer := sumValues (fun i : Fin (2*m+1) =>
    let result := querySources weights t channels embedding ordinary (caches.get i) target
    ⟨result.value,result.operations+i.val.size+2⟩) (List.finRange (2*m+1))
  ⟨answer.value,answer.operations+2*(2*m+1)*((2*m+1).size+1)⟩

theorem queryRuns_value {L m k q width : ℕ} [NeZero q] (weights : WeightProgram) (t : ℕ)
    (channels : List (List (Fin k))) (embedding : Vector (Fin (2*L)) k)
    (ordinary : Vector (Fin 4) (2*L)) (caches : RunCaches L m q width)
    (native : CachedLowQuery.RunCaches L m q width)
    (hcache : ∀ i, CacheRefines (caches.get i).1 (native.get i).1 ∧
      CacheRefines (caches.get i).2 (native.get i).2) (target : Fin q) :
    denote (queryRuns weights t channels embedding ordinary caches target).value=
      (CachedLowQuery.queryRuns t channels embedding ordinary native target).1 := by
  simp only [queryRuns,sumValues_value,CachedLowQuery.queryRuns,List.map_map,Function.comp_def]
  apply congrArg List.sum
  apply List.map_congr_left
  intro i _
  exact querySources_value weights t channels embedding ordinary _ _ (hcache i).1 (hcache i).2 target

def queryLowRuns {L m k q width : ℕ} [NeZero q] (weights : WeightProgram) (t : ℕ)
    (embedding : Vector (Fin (2*L)) k) (ordinary : Vector (Fin 4) (2*L))
    (caches : RunCaches L m q width) (target : Fin q) : Counted Signed :=
  let generated := LowChannelEnumeration.generate (List.finRange k) t
  let answer := queryRuns weights t generated.members embedding ordinary caches target
  ⟨answer.value,8*k+generated.work+answer.operations⟩

theorem queryLowRuns_value {L m k q width : ℕ} [NeZero q] (weights : WeightProgram) (t : ℕ)
    (embedding : Vector (Fin (2*L)) k) (ordinary : Vector (Fin 4) (2*L))
    (caches : RunCaches L m q width) (native : CachedLowQuery.RunCaches L m q width)
    (hcache : ∀ i, CacheRefines (caches.get i).1 (native.get i).1 ∧
      CacheRefines (caches.get i).2 (native.get i).2) (target : Fin q) :
    denote (queryLowRuns weights t embedding ordinary caches target).value=
      (CachedLowQuery.queryLowRuns t embedding ordinary native target).1 := by
  exact queryRuns_value weights t _ embedding ordinary caches native hcache target

/-- Division is applied once to the complete LOW plus HIGH numerator. -/
def normalizeComplete (L : ℕ) (low : Counted Signed)
    (high : Counted BinaryArrayFFT.Integer) : Counted Signed :=
  let upper := normalizeCell high.value
  let numerator := BitArraySimulation.add low.value upper.value
  let denominator := BackendScalarBits.powerTwoBits (2*L)
  let result := BitArraySimulation.divide denominator.1 numerator.value
  ⟨result.value,low.operations+high.operations+upper.operations+numerator.operations+
    denominator.2+result.operations+2⟩

theorem powerTwoBits_eq_bits (k : ℕ) :
    (BackendScalarBits.powerTwoBits k).1=(2^k).bits := by
  induction k with
  | zero => simp [BackendScalarBits.powerTwoBits]
  | succ k ih =>
    simp only [BackendScalarBits.powerTwoBits,List.replicate_succ,List.cons_append]
    rw [pow_succ',Nat.bit0_bits _ (by positivity)]
    exact congrArg (List.cons false) ih

theorem divide_projection (D : ℕ) (x : Signed) :
    denote (BitArraySimulation.divide D.bits x).value=
      (IntegerArithmetic.binaryExactDivCounted D (denote x)).1 := by
  rw [divide_value D x D.bits rfl]
  simp only [ToomBitCost.bitPrimitives,IntegerArithmetic.normalizedDivideCounted,
    IntegerArithmetic.normalizeResult_value,IntegerArithmetic.ofInt_correct,
    IntegerArithmetic.binaryExactDivCounted]

theorem normalizeComplete_value (L : ℕ) (low : Counted Signed)
    (high : Counted BinaryArrayFFT.Integer) :
    denote (normalizeComplete L low high).value=
      (IntegerArithmetic.binaryExactDivCounted (4^L) (denote low.value+high.value.view)).1 := by
  have hden : (BackendScalarBits.powerTwoBits (2*L)).1=(4^L).bits := by
    rw [powerTwoBits_eq_bits,show (4:ℕ)=2^2 by norm_num,←pow_mul]
  simp only [normalizeComplete,hden,divide_projection,add_value,normalizeCell_value]

theorem normalizeComplete_exact (L : ℕ) (low : Counted Signed)
    (high : Counted BinaryArrayFFT.Integer) (answer : ℤ)
    (hnum : denote low.value+high.value.view=((4^L:ℕ):ℤ)*answer) :
    denote (normalizeComplete L low high).value=answer := by
  rw [normalizeComplete_value]
  exact IntegerArithmetic.binaryExactDivCounted_exact _ _ _ (by positivity) hnum

def queryComplete {L m k q width : ℕ} [NeZero q] (t : ℕ)
    (embedding : Vector (Fin (2*L)) k) (ordinary : Vector (Fin 4) (2*L))
    (caches : RunCaches L m q width) (target : Fin q)
    (high : Counted BinaryArrayFFT.Integer) : Counted Signed :=
  normalizeComplete L (queryLowRuns actualWeights t embedding ordinary caches target) high

theorem queryComplete_value {L m k q width : ℕ} [NeZero q] (t : ℕ)
    (embedding : Vector (Fin (2*L)) k) (ordinary : Vector (Fin 4) (2*L))
    (caches : RunCaches L m q width) (native : CachedLowQuery.RunCaches L m q width)
    (hcache : ∀ i, CacheRefines (caches.get i).1 (native.get i).1 ∧
      CacheRefines (caches.get i).2 (native.get i).2) (target : Fin q)
    (high : Counted BinaryArrayFFT.Integer) :
    denote (queryComplete t embedding ordinary caches target high).value=
      (IntegerArithmetic.binaryExactDivCounted (4^L)
        ((CachedLowQuery.queryLowRuns t embedding ordinary native target).1+high.value.view)).1 := by
  rw [queryComplete,normalizeComplete_value,queryLowRuns_value actualWeights t
    embedding ordinary caches native hcache target]

theorem normalizeComplete_cost (L : ℕ) (low : Counted Signed)
    (high : Counted BinaryArrayFFT.Integer) (M H B : ℕ)
    (hl : |denote low.value|≤(M:ℤ)) (hh : |high.value.view|≤(H:ℤ))
    (hM : M.size≤B) (hH : H.size≤B) (hnum : (M+H).size≤B) (hD : 2*L+1≤B) :
    (normalizeComplete L low high).operations≤
      low.operations+high.operations+1000*(B+1)^2 := by
  have hlNat : (denote low.value).natAbs≤M := by
    rw [←Int.natCast_natAbs] at hl
    exact_mod_cast hl
  have hhNat : high.value.view.natAbs≤H := by
    rw [←Int.natCast_natAbs] at hh
    exact_mod_cast hh
  have hlSize := (Nat.size_le_size hlNat).trans hM
  have hhSize := (Nat.size_le_size hhNat).trans hH
  have hn : (denote low.value+high.value.view).natAbs≤M+H := by
    have ha := (abs_add_le (denote low.value) high.value.view).trans (add_le_add hl hh)
    rw [←Int.natCast_natAbs] at ha
    exact_mod_cast ha
  have hnSize := (Nat.size_le_size hn).trans hnum
  have hnorm := IntegerArithmetic.normalizeSignedCounted_steps high.value.bits
  rw [high.value.canonical] at hnorm
  have hadd := BinaryQueryWeights.add_price B low.value (normalizeCell high.value).value
    hlSize (by rw [normalizeCell_value];exact hhSize)
  let numerator := BitArraySimulation.add low.value (normalizeCell high.value).value
  have hnl : numerator.value.val.magnitude.length≤B := by
    rw [magnitude_length,add_value,normalizeCell_value]
    exact hnSize
  let divisor := (BackendScalarBits.powerTwoBits (2*L)).1
  have hdl : divisor.length≤B := by simpa only [divisor,BackendScalarBits.powerTwoBits_length] using hD
  have hdiv := IntegerArithmetic.normalizedDivideCounted_steps divisor numerator.value.val
  have hcopy := BitArraySimulation.copyBits_cost divisor
  have hdCost : (BitArraySimulation.divide divisor numerator.value).operations≤
      70*(B+1)^2 := by
    simp only [BitArraySimulation.divide,copyBits_value]
    rw [hcopy]
    have hhdiv : 30*(numerator.value.val.magnitude.length+1)*
        (numerator.value.val.magnitude.length+divisor.length+1)+4≤
          30*(B+1)*(2*B+1)+4 := by gcongr; omega
    nlinarith
  have hp : (BackendScalarBits.powerTwoBits (2*L)).2≤2*B := by
    dsimp [BackendScalarBits.powerTwoBits]
    omega
  change low.operations+high.operations+(normalizeCell high.value).operations+
    numerator.operations+(BackendScalarBits.powerTwoBits (2*L)).2+
    (BitArraySimulation.divide divisor numerator.value).operations+2≤_
  change numerator.operations≤BackendScalarBits.scalarUnit B at hadd
  unfold BackendScalarBits.scalarUnit at hadd
  dsimp only [normalizeCell]
  change (IntegerArithmetic.normalizeSignedCounted high.value.bits).2≤8*high.value.view.natAbs.size+8 at hnorm
  nlinarith


theorem readCoefficient_cost_probe {q width : ℕ} (a : Block q width) (A : ℕ)
    (ha : ∀ i : Fin width, ∀ r : Fin q, ((a.get i).get r).view.natAbs ≤ A)
    (degree : ℕ) (residue : Fin q) :
    (readCoefficient a degree residue).operations ≤ 8*A.size+degree.size+q.size+11 := by
  unfold readCoefficient
  split_ifs with hd
  · have hc := IntegerArithmetic.normalizeSignedCounted_steps ((a.get ⟨degree,hd⟩).get residue).bits
    rw [((a.get ⟨degree,hd⟩).get residue).canonical] at hc
    have hv := Nat.size_le_size (ha ⟨degree,hd⟩ residue)
    have hr := Nat.size_le_size (Nat.le_of_lt residue.isLt)
    change _ + _ + _ + 3 ≤ _
    dsimp only [normalizeCell,BinaryArrayFFT.Integer.view] at *
    omega
  · dsimp only
    omega

 theorem readCoefficient_bound_probe {q width : ℕ} (a : Block q width) (A : ℕ)
    (ha : ∀ i : Fin width, ∀ r : Fin q, ((a.get i).get r).view.natAbs ≤ A)
    (degree : ℕ) (residue : Fin q) :
    (denote (readCoefficient a degree residue).value).natAbs ≤ A := by
  unfold readCoefficient
  split_ifs with hd
  · simpa only [normalizeCell_value] using ha ⟨degree,hd⟩ residue
  · simp only [denote_zero,Int.natAbs_zero]; exact Nat.zero_le _


 theorem selectedDot_cost_probe {q width : ℕ} [NeZero q] (left right : Block q width)
    (A B leftDegree rightDegree : ℕ) (target : Fin q)
    (hl : ∀ i : Fin width, ∀ r : Fin q, ((left.get i).get r).view.natAbs ≤ A)
    (hr : ∀ i : Fin width, ∀ r : Fin q, ((right.get i).get r).view.natAbs ≤ A)
    (hA : A.size ≤ B) (hld : leftDegree.size ≤ B) (hrd : rightDegree.size ≤ B)
    (hq : q.size ≤ B) (hp : (A^2).size ≤ B) (htotal : (q*A^2).size ≤ B) :
    (selectedDot left right leftDegree rightDegree target).operations ≤ 400*q*(B+1)^2 := by
  let f := fun r : Fin q =>
    BitArraySimulation.bind (readCoefficient left leftDegree r) (fun x =>
      BitArraySimulation.bind (readCoefficient right rightDegree (target-r)) (fun y =>
        let product := BitArraySimulation.mul x y
        ⟨product.value,product.operations+4*(q.size+1)^2⟩))
  have hf : ∀ r : Fin q, (f r).operations ≤ 300*(B+1)^2 := by
    intro r
    have ha := readCoefficient_cost_probe left A hl leftDegree r
    have hb := readCoefficient_cost_probe right A hr rightDegree (target-r)
    have hx := (Nat.size_le_size (readCoefficient_bound_probe left A hl leftDegree r)).trans hA
    have hy := (Nat.size_le_size (readCoefficient_bound_probe right A hr rightDegree (target-r))).trans hA
    have hm := BinaryQueryWeights.mul_price B
      (readCoefficient left leftDegree r).value (readCoefficient right rightDegree (target-r)).value hx hy
    have hmod : 4*(q.size+1)^2 ≤ 4*(B+1)^2 := by gcongr
    dsimp only [f,BitArraySimulation.bind]
    unfold BackendScalarBits.scalarUnit at hm
    nlinarith
  have hv : ∀ r : Fin q, |denote (f r).value| ≤ (A^2:ℕ) := by
    intro r
    have hx := readCoefficient_bound_probe left A hl leftDegree r
    have hy := readCoefficient_bound_probe right A hr rightDegree (target-r)
    have hm := Nat.mul_le_mul hx hy
    simp only [f,BitArraySimulation.bind,mul_value,←Int.natCast_natAbs,Int.natAbs_mul]
    exact_mod_cast (show (denote (readCoefficient left leftDegree r).value).natAbs*
        (denote (readCoefficient right rightDegree (target-r)).value).natAbs ≤ A^2 by
      simpa only [pow_two] using hm)
  have hs := sumValues_cost f (List.finRange q) (A^2) q (by simp)
    (fun r _ => hv r)
  have hfSum : ((List.finRange q).map (fun r => (f r).operations)).sum ≤ q*(300*(B+1)^2) := by
    calc
      _ ≤ ((List.finRange q).map (fun _ => 300*(B+1)^2)).sum := by
        apply List.sum_le_sum; intro r _; exact hf r
      _ = _ := by simp
  have hmax : max (A^2).size (q*A^2).size ≤ B := max_le hp htotal
  have hqs : 1 ≤ q := Nat.pos_of_neZero q
  simp only [List.length_finRange] at hs
  change (sumValues f (List.finRange q)).operations+2*q*(q.size+1) ≤ _
  have hadd : q*(50*(max (A^2).size (q*A^2).size+1)+2) ≤ q*(50*(B+1)+2) := by
    apply Nat.mul_le_mul_left; omega
  have hindex : 2*q*(q.size+1) ≤ 2*q*(B+1) := by gcongr
  have hs' : (sumValues f (List.finRange q)).operations ≤
      q*(300*(B+1)^2)+q*(50*(B+1)+2)+1 := by omega
  calc
    _ ≤ q*(300*(B+1)^2)+q*(50*(B+1)+2)+1+2*q*(B+1) := add_le_add hs' hindex
    _ ≤ q*(300*(B+1)^2)+q*(50*(B+1)+2)+q+2*q*(B+1) := by omega
    _ = q*(300*(B+1)^2+52*(B+1)+3) := by ring
    _ ≤ q*(400*(B+1)^2) := by apply Nat.mul_le_mul_left; nlinarith
    _ = _ := by ring


/-- Uniform callback version useful for the degree, channel, and run
loops. The endpoint width (n*A).size is arithmetic on public magnitudes;
all actual partial accumulator widths are derived inside sumValues_cost. -/
theorem sumValues_cost_uniform {ι : Type*} (f : ι → Counted Signed) (is : List ι)
    (A n B P : ℕ) (hlen : is.length ≤ n)
    (hf : ∀ i ∈ is, |denote (f i).value| ≤ (A:ℤ))
    (hA : A.size ≤ B) (htotal : (n*A).size ≤ B)
    (hcallback : ∀ i ∈ is, (f i).operations ≤ P) :
    (sumValues f is).operations ≤ n*(P+52*(B+1)^2)+1 := by
  have hs := sumValues_cost f is A n hlen hf
  have hsum : (is.map (fun i => (f i).operations)).sum ≤ is.length*P := by
    calc
      _ ≤ (is.map (fun _ => P)).sum := List.sum_le_sum hcallback
      _ = _ := by simp
  have hunit : 50*(max A.size (n*A).size+1)+2 ≤ 52*(B+1)^2 := by
    have hm := max_le hA htotal
    nlinarith
  have hu := Nat.mul_le_mul_left is.length hunit
  have hn := Nat.mul_le_mul_right (P+52*(B+1)^2) hlen
  nlinarith

/-- Convolution degree loop, including derived magnitudes for every tail
of its actual canonical binary sum. The selected-dot hypothesis can be
instantiated with the separately verified literal read/multiply loop. -/
theorem polynomialDot_cost_of_selectedCost {q width : ℕ} [NeZero q]
    (left right : Block q width) (A degree B : ℕ)
    (hl : ∀ d r, |SparseLocalForms.denseRead (blockView left) d r| ≤ (A:ℤ))
    (hr : ∀ d r, |SparseLocalForms.denseRead (blockView right) d r| ≤ (A:ℤ))
    (hterm : (q*A^2).size ≤ B) (htotal : ((degree+1)*(q*A^2)).size ≤ B)
    (hdegree : degree.size ≤ B) (target : Fin q)
    (hselected : ∀ a ∈ List.range (degree+1),
      (selectedDot left right a (degree-a) target).operations ≤ 400*q*(B+1)^2) :
    (polynomialDot left right degree target).operations ≤
      600*(degree+1)*q*(B+1)^2 := by
  let f := fun a => selectedDot left right a (degree-a) target
  have hf : ∀ a ∈ List.range (degree+1), |denote (f a).value| ≤ (q*A^2:ℕ) := by
    intro a _
    dsimp only [f]
    rw [selectedDot_value]
    exact BinaryLowBounds.selectedDot_bound _ _ target A
      (fun r => BinaryLowBounds.blockCoeff_bound (blockView left) A hl a r)
      (fun r => BinaryLowBounds.blockCoeff_bound (blockView right) A hr (degree-a) r)
  have hs := sumValues_cost f (List.range (degree+1)) (q*A^2) (degree+1)
    (by simp) hf
  have hcallback : ((List.range (degree+1)).map (fun a => (f a).operations)).sum ≤
      (degree+1)*(400*q*(B+1)^2) := by
    calc
      _ ≤ ((List.range (degree+1)).map (fun _ => 400*q*(B+1)^2)).sum := by
        exact List.sum_le_sum hselected
      _ = _ := by simp
  have hq : 1 ≤ q := NeZero.one_le
  have hunit : 50*(max (q*A^2).size ((degree+1)*(q*A^2)).size+1)+2 ≤ 52*(B+1)^2 := by
    have hm := max_le hterm htotal
    nlinarith
  have hsum : (degree+1)*(50*(max (q*A^2).size ((degree+1)*(q*A^2)).size+1)+2) ≤
      52*(degree+1)*q*(B+1)^2 := by
    calc
      _ ≤ (degree+1)*(52*(B+1)^2) := Nat.mul_le_mul_left _ hunit
      _ ≤ (degree+1)*(52*(B+1)^2)*q := Nat.le_mul_of_pos_right _ hq
      _ = _ := by ring
  have haddrs : 2*(degree+1)*(degree.size+1) ≤ 2*(degree+1)*q*(B+1)^2 := by
    have hdp : degree.size+1 ≤ (B+1)^2 := by nlinarith
    calc
      _ ≤ 2*(degree+1)*(B+1)^2 := Nat.mul_le_mul_left _ hdp
      _ ≤ 2*(degree+1)*(B+1)^2*q := Nat.le_mul_of_pos_right _ hq
      _ = _ := by ring
  have hone : 1 ≤ (degree+1)*q*(B+1)^2 := by
    have hpos : 0 < (degree+1)*q*(B+1)^2 := by positivity
    omega
  simp only [List.length_range] at hs
  change (sumValues f (List.range (degree+1))).operations+2*(degree+1)*(degree.size+1) ≤ _
  nlinarith

 theorem lowTerm_cost_probe {q width : ℕ} [NeZero q] (left right : Block q width)
    (k t A B channelCard degree : ℕ) (target : Fin q)
    (hl : ∀ d r, |SparseLocalForms.denseRead (blockView left) d r| ≤ (A:ℤ))
    (hr : ∀ d r, |SparseLocalForms.denseRead (blockView right) d r| ≤ (A:ℤ))
    (hcard : channelCard ≤ k) (hdegree : degree < t)
    (hA : A.size ≤ B) (hq : q.size ≤ B)
    (hqdot : (q*A^2).size ≤ B)
    (hpoly : ((degree-channelCard+1)*q*A^2).size ≤ B)
    (hw : CachedLowQuery.weightBitWidth k t ≤ B) (hparam : k+t+2 ≤ B) :
    (lowTerm actualWeights k t left right channelCard degree target).operations ≤
      (100000*(B+1)^3)*(CachedLowQuery.lowTerm k t (blockView left) (blockView right)
        channelCard degree target).2 := by
  have hlcell : ∀ i : Fin width, ∀ r : Fin q, ((left.get i).get r).view.natAbs ≤ A := by
    intro i r
    have h := hl i r
    simp only [SparseLocalForms.denseRead,blockView,Vector.get_map,←Int.natCast_natAbs] at h
    exact_mod_cast h
  have hrcell : ∀ i : Fin width, ∀ r : Fin q, ((right.get i).get r).view.natAbs ≤ A := by
    intro i r
    have h := hr i r
    simp only [SparseLocalForms.denseRead,blockView,Vector.get_map,←Int.natCast_natAbs] at h
    exact_mod_cast h
  have hdegsize : degree.size ≤ B :=
    (Nat.size_le.mpr (Nat.lt_two_pow_self (n:=degree))).trans (by omega)
  have hcardsize : channelCard.size ≤ B :=
    (Nat.size_le.mpr (Nat.lt_two_pow_self (n:=channelCard))).trans (by omega)
  have hcontrol : 4*(channelCard.size+degree.size+1)^2 ≤ 16*(B+1)^2 := by
    have hsum : channelCard.size+degree.size+1 ≤ 2*(B+1) := by omega
    calc
      _ ≤ 4*(2*(B+1))^2 := by gcongr
      _ = _ := by ring
  unfold lowTerm CachedLowQuery.lowTerm
  split_ifs with hbranch
  · have hprod : (A^2).size ≤ B :=
      (Nat.size_le_size (Nat.le_mul_of_pos_left _ (Nat.pos_of_neZero q))).trans hqdot
    have hd : (degree-channelCard).size ≤ B :=
      (Nat.size_le_size (Nat.sub_le degree channelCard)).trans hdegsize
    have hpoly' : ((degree-channelCard+1)*(q*A^2)).size ≤ B := by
      simpa only [Nat.mul_assoc] using hpoly
    have hdot := polynomialDot_cost_of_selectedCost left right A (degree-channelCard) B hl hr hqdot
      hpoly' hd target (by
        intro a ha
        have ha' : a ≤ degree-channelCard := by have := List.mem_range.mp ha; omega
        exact selectedDot_cost_probe left right A B a (degree-channelCard-a) target hlcell hrcell
          hA ((Nat.size_le_size ha').trans hd)
          ((Nat.size_le_size (Nat.sub_le _ _)).trans hd) hq hprod hqdot)
    have hdotmag : (denote (polynomialDot left right (degree-channelCard) target).value).natAbs.size ≤ B := by
      have h := BinaryLowBounds.polynomialDot_bound (blockView left) (blockView right) A
        (degree-channelCard) hl hr target
      rw [←polynomialDot_value,←Int.natCast_natAbs] at h
      have hn : (denote (polynomialDot left right (degree-channelCard) target).value).natAbs ≤
          (degree-channelCard+1)*q*A^2 := by exact_mod_cast h
      exact (Nat.size_le_size hn).trans hpoly
    have hmul := BinaryQueryWeights.mul_price B (BinaryQueryWeights.weight k t degree).value
      (polynomialDot left right (degree-channelCard) target).value
      ((BinaryQueryWeights.weight_width k t degree).trans hw) hdotmag
    have hweight : (BinaryQueryWeights.weight k t degree).operations ≤ 10000*(B+1)^3 := by
      calc
        _ ≤ 100*(k+t+2)*BackendScalarBits.scalarUnit (CachedLowQuery.weightBitWidth k t) :=
          BinaryQueryWeights.weight_cost k t degree
        _ ≤ 100*(B+1)*(100*(B+1)^2) := by
          apply Nat.mul_le_mul
          · exact Nat.mul_le_mul_left 100 (by omega : k+t+2 ≤ B+1)
          · unfold BackendScalarBits.scalarUnit
            exact Nat.mul_le_mul_left 100 (Nat.pow_le_pow_left (Nat.add_le_add_right hw 1) 2)
        _ = _ := by ring
    have hdot' : (polynomialDot left right (degree-channelCard) target).operations ≤
        (100000*(B+1)^3)*(5*q*(degree-channelCard+1)) := by
      calc
        _ ≤ 600*(degree-channelCard+1)*q*(B+1)^2 := hdot
        _ = (5*q*(degree-channelCard+1))*(120*(B+1)^2) := by ring
        _ ≤ (5*q*(degree-channelCard+1))*(100000*(B+1)^3) := by
          apply Nat.mul_le_mul_left
          nlinarith [show 1 ≤ B+1 by omega]
        _ = _ := by ring
    have hrest : (BinaryQueryWeights.weight k t degree).operations+
        (BitArraySimulation.mul (BinaryQueryWeights.weight k t degree).value
          (polynomialDot left right (degree-channelCard) target).value).operations+
        4*(channelCard.size+degree.size+1)^2 ≤ 4*(100000*(B+1)^3) := by
      unfold BackendScalarBits.scalarUnit at hmul
      nlinarith [show (B+1)^2 ≤ (B+1)^3 by nlinarith [show 1 ≤ B+1 by omega]]
    simp only [actualWeights,CachedLowQuery.polynomialDot_work]
    nlinarith
  · dsimp only
    nlinarith [show (B+1)^2 ≤ (B+1)^3 by nlinarith [show 1 ≤ B+1 by omega]]

 theorem channelQuery_cost_probe {N q width : ℕ} [NeZero q] (k t A B channelCard : ℕ)
    (left right : Cache N q width) (nativeLeft nativeRight : CachedLowQuery.Prepared N q width)
    (hleft : CacheRefines left nativeLeft) (hright : CacheRefines right nativeRight)
    (key : ArrayKeys.Key N) (target : Fin q)
    (hl : ∀ d r, |SparseLocalForms.denseRead (blockView (readBlock left key).1) d r| ≤ (A:ℤ))
    (hr : ∀ d r, |SparseLocalForms.denseRead (blockView (readBlock right key).1) d r| ≤ (A:ℤ))
    (hcard : channelCard ≤ k) (hA : A.size ≤ B) (hq : q.size ≤ B)
    (hqdot : (q*A^2).size ≤ B)
    (hM : (2^k*t*q*A^2).size ≤ B) (hTM : (t*(2^k*t*q*A^2)).size ≤ B)
    (hw : CachedLowQuery.weightBitWidth k t ≤ B) (hparam : k+t+2 ≤ B) :
    (channelQuery actualWeights k t left right key channelCard target).operations ≤
      4*(100000*(B+1)^3)*(CachedLowQuery.channelKeyQuery k t nativeLeft nativeRight key
        channelCard target).2 := by
  let a := readBlock left key
  let b := readBlock right key
  let f := fun degree => lowTerm actualWeights k t a.1 b.1 channelCard degree target
  let g := fun degree => CachedLowQuery.lowTerm k t
    (CachedLowQuery.readKeyBlockCounted nativeLeft key).1
    (CachedLowQuery.readKeyBlockCounted nativeRight key).1 channelCard degree target
  let P := 100000*(B+1)^3
  let M := 2^k*t*q*A^2
  have hf : ∀ d ∈ List.range t, |denote (f d).value| ≤ (M:ℤ) := by
    intro d hd
    dsimp only [f]
    rw [lowTerm_value]
    exact BinaryLowBounds.lowTerm_bound k t A (blockView a.1) (blockView b.1)
      hl hr channelCard d (List.mem_range.mp hd) target
  have hfcost : ∀ d ∈ List.range t, (f d).operations ≤ P*(g d).2 := by
    intro d hd
    have hd' := List.mem_range.mp hd
    have hpoly : ((d-channelCard+1)*q*A^2).size ≤ B := by
      have hdim : d-channelCard+1 ≤ t := by omega
      have hpow : 1 ≤ 2^k := Nat.one_le_pow k 2 (by decide)
      have hbound : (d-channelCard+1)*q*A^2 ≤ 2^k*t*q*A^2 := by
        calc
          _ ≤ t*q*A^2 := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hdim)
          _ = 1*t*q*A^2 := by ring
          _ ≤ _ := by gcongr
      exact (Nat.size_le_size hbound).trans hM
    have h := lowTerm_cost_probe a.1 b.1 k t A B channelCard d target hl hr hcard hd'
      hA hq hqdot hpoly hw hparam
    dsimp only [f,P]
    dsimp only [g]
    rw [←hleft key,←hright key]
    exact h
  have hs := sumValues_cost f (List.range t) M t (by simp) hf
  have hsum : ((List.range t).map (fun d => (f d).operations)).sum ≤
      P*((List.range t).map (fun d => (g d).2)).sum := by
    calc
      _ ≤ ((List.range t).map (fun d => P*(g d).2)).sum := List.sum_le_sum hfcost
      _ = _ := List.sum_map_mul_left (List.range t) (fun d => (g d).2) P
  have htsize : t.size ≤ B :=
    (Nat.size_le.mpr (Nat.lt_two_pow_self (n:=t))).trans (by omega)
  have hmax : max M.size (t*M).size ≤ B := max_le hM hTM
  have hunit : 50*(max M.size (t*M).size+1)+2+2*(t.size+1) ≤ P := by
    dsimp only [P]
    nlinarith [show (B+1)^2 ≤ (B+1)^3 by nlinarith [show 1 ≤ B+1 by omega]]
  have hunit' := Nat.mul_le_mul_left t hunit
  have hrows : (sumValues f (List.range t)).operations+2*t*(t.size+1) ≤
      P*(((List.range t).map (fun d => (g d).2)).sum+t)+1 := by
    simp only [List.length_range] at hs
    nlinarith
  have hread : a.2+b.2 ≤ 4*((CachedLowQuery.readKeyBlockCounted nativeLeft key).2+
      (CachedLowQuery.readKeyBlockCounted nativeRight key).2) := by
    simp only [a,b,readBlock,CachedLowQuery.readKeyBlockCounted,ArrayKeys.read_work]
    nlinarith
  have hP : 4 ≤ P := by
    have hp : 0 < (B+1)^3 := by positivity
    dsimp only [P]
    omega
  have hread' : a.2+b.2 ≤ P*((CachedLowQuery.readKeyBlockCounted nativeLeft key).2+
      (CachedLowQuery.readKeyBlockCounted nativeRight key).2) :=
    hread.trans (Nat.mul_le_mul_right _ hP)
  have hreadspos : 1 ≤ (CachedLowQuery.readKeyBlockCounted nativeLeft key).2+
      (CachedLowQuery.readKeyBlockCounted nativeRight key).2 := by
    simp only [CachedLowQuery.readKeyBlockCounted,ArrayKeys.read_work]
    omega
  simp only [channelQuery,CachedLowQuery.channelKeyQuery,List.map_map,Function.comp_def]
  change a.2+b.2+(sumValues f (List.range t)).operations+2*t*(t.size+1) ≤
    4*P*((CachedLowQuery.readKeyBlockCounted nativeLeft key).2+
      (CachedLowQuery.readKeyBlockCounted nativeRight key).2+t+
      ((List.range t).map (fun d => (g d).2)).sum)
  nlinarith

theorem list_length_le_cost_sum {ι : Type*} (is : List ι) (g : ι → ℕ)
    (hg : ∀ i ∈ is, 1 ≤ g i) : is.length ≤ (is.map g).sum := by
  calc
    _ = (is.map (fun _ => 1)).sum := by simp
    _ ≤ _ := List.sum_le_sum hg

theorem sumValues_cost_refinement {ι : Type*} (f : ι → Counted Signed)
    (g : ι → ℕ) (is : List ι) (A n B R : ℕ) (hlen : is.length ≤ n)
    (hf : ∀ i ∈ is, |denote (f i).value| ≤ (A:ℤ))
    (hA : A.size ≤ B) (htotal : (n*A).size ≤ B)
    (hcallback : ∀ i ∈ is, (f i).operations ≤ R*g i)
    (hg : ∀ i ∈ is, 1 ≤ g i) :
    (sumValues f is).operations ≤
      (R+52*(B+1)^2)*(is.map g).sum+1 := by
  have hs := sumValues_cost f is A n hlen hf
  have hsum : (is.map (fun i => (f i).operations)).sum ≤ R*(is.map g).sum := by
    calc
      _ ≤ (is.map (fun i => R*g i)).sum := List.sum_le_sum hcallback
      _ = _ := List.sum_map_mul_left is g R
  have hunit : 50*(max A.size (n*A).size+1)+2 ≤ 52*(B+1)^2 := by
    have hm := max_le hA htotal
    nlinarith
  have hu := Nat.mul_le_mul_left is.length hunit
  have hl := list_length_le_cost_sum is g hg
  have hm := Nat.mul_le_mul_right (52*(B+1)^2) hl
  nlinarith

/-- Positive native calls pay for the initial zero and every actual binary
sum operation; nonempty generation makes the final extra one unnecessary. -/
theorem sumValues_cost_refinement_nonempty {ι : Type*} (f : ι → Counted Signed)
    (g : ι → ℕ) (is : List ι) (A n B R : ℕ) (hne : is ≠ []) (hlen : is.length ≤ n)
    (hf : ∀ i ∈ is, |denote (f i).value| ≤ (A:ℤ))
    (hA : A.size ≤ B) (htotal : (n*A).size ≤ B)
    (hcallback : ∀ i ∈ is, (f i).operations ≤ R*g i)
    (hg : ∀ i ∈ is, 1 ≤ g i) :
    (sumValues f is).operations ≤ (R+54*(B+1)^2)*(is.map g).sum := by
  have hs := sumValues_cost_refinement f g is A n B R hlen hf hA htotal hcallback hg
  have hl := list_length_le_cost_sum is g hg
  have hpos : 1 ≤ (is.map g).sum := by
    have hlenpos : 0 < is.length := List.length_pos_iff.mpr hne
    omega
  have hp : 1 ≤ (B+1)^2 := by nlinarith
  nlinarith

/-- An explicit native allocation/initialization charge can alternatively
pay for sumValues even when the callback list is empty or callback costs
can be zero. -/
theorem sumValues_cost_refinement_allocated {ι : Type*} (f : ι → Counted Signed)
    (g : ι → ℕ) (is : List ι) (A n B R nativeTotal : ℕ) (hlen : is.length ≤ n)
    (hf : ∀ i ∈ is, |denote (f i).value| ≤ (A:ℤ))
    (hA : A.size ≤ B) (htotal : (n*A).size ≤ B)
    (hcallback : ∀ i ∈ is, (f i).operations ≤ R*g i)
    (hallocated : (is.map g).sum+is.length+1 ≤ nativeTotal) :
    (sumValues f is).operations ≤ (R+54*(B+1)^2)*nativeTotal := by
  have hs := sumValues_cost f is A n hlen hf
  have hsum : (is.map (fun i => (f i).operations)).sum ≤ R*(is.map g).sum := by
    calc
      _ ≤ (is.map (fun i => R*g i)).sum := List.sum_le_sum hcallback
      _ = _ := List.sum_map_mul_left is g R
  have hunit : 50*(max A.size (n*A).size+1)+2 ≤ 52*(B+1)^2 := by
    have hm := max_le hA htotal
    nlinarith
  have hu := Nat.mul_le_mul_left is.length hunit
  have hcostnative : (is.map g).sum ≤ nativeTotal := by omega
  have hallocnative : is.length+1 ≤ nativeTotal := by omega
  have hR := Nat.mul_le_mul_left R hcostnative
  have hU := Nat.mul_le_mul_left (52*(B+1)^2+1) hallocnative
  have hp : 1 ≤ (B+1)^2 := by nlinarith
  have hM := Nat.mul_le_mul_right nativeTotal (by nlinarith : 52*(B+1)^2+1 ≤ 54*(B+1)^2)
  nlinarith

theorem native_channelKeyQuery_pos {N q width : ℕ} [NeZero q] (k t : ℕ)
    (left right : CachedLowQuery.Prepared N q width) (key : ArrayKeys.Key N)
    (channelCard : ℕ) (target : Fin q) :
    1 ≤ (CachedLowQuery.channelKeyQuery k t left right key channelCard target).2 := by
  rw [CachedLowQuery.channelKeyQuery_eq]
  simp only [CachedLowQuery.channelQuery,CachedLowQuery.readBlockCounted_work]
  omega

/-- Exact comparison with the native physical-key query counter. The same
key construction is charged once on both sides; actual binary additions
are paid using the derived partial sums of channel results. -/
theorem querySources_cost_of_channelCost {L k q width : ℕ} [NeZero q]
    (weights : WeightProgram) (t : ℕ) (channels : List (List (Fin k)))
    (embedding : Vector (Fin (2*L)) k) (ordinary : Vector (Fin 4) (2*L))
    (cache : SourceCaches L q width) (native : CachedLowQuery.SourceCaches L q width)
    (target : Fin q) (M B R : ℕ) (hR : 1 ≤ R)
    (hne : channels ≠ []) (hlen : channels.length ≤ 2^k)
    (hM : M.size ≤ B) (htotal : (2^k*M).size ≤ B)
    (hvalue : ∀ cs ∈ channels,
      |denote (channelQuery weights k t cache.1 cache.2
        (CachedLowQuery.physicalKey embedding ordinary cs).1 cs.length target).value| ≤ (M:ℤ))
    (hchannel : ∀ cs ∈ channels,
      (channelQuery weights k t cache.1 cache.2
        (CachedLowQuery.physicalKey embedding ordinary cs).1 cs.length target).operations ≤
        R*(CachedLowQuery.channelKeyQuery k t native.1 native.2
          (CachedLowQuery.physicalKey embedding ordinary cs).1 cs.length target).2) :
    (querySources weights t channels embedding ordinary cache target).operations ≤
      (R+54*(B+1)^2)*(CachedLowQuery.querySources t channels embedding ordinary native target).2 := by
  let f := fun cs : List (Fin k) =>
    let key := CachedLowQuery.physicalKey embedding ordinary cs
    let answer := channelQuery weights k t cache.1 cache.2 key.1 cs.length target
    (⟨answer.value,key.2+answer.operations⟩ : Counted Signed)
  let g := fun cs : List (Fin k) =>
    let key := CachedLowQuery.physicalKey embedding ordinary cs
    key.2+(CachedLowQuery.channelKeyQuery k t native.1 native.2 key.1 cs.length target).2
  have hf : ∀ cs ∈ channels, |denote (f cs).value| ≤ (M:ℤ) := by
    intro cs hcs
    exact hvalue cs hcs
  have hg : ∀ cs ∈ channels, 1 ≤ g cs := by
    intro cs _
    have hp := native_channelKeyQuery_pos k t native.1 native.2
      (CachedLowQuery.physicalKey embedding ordinary cs).1 cs.length target
    dsimp only [g]
    omega
  have hcallback : ∀ cs ∈ channels, (f cs).operations ≤ R*g cs := by
    intro cs hcs
    have hc := hchannel cs hcs
    have hk := Nat.mul_le_mul_right (CachedLowQuery.physicalKey embedding ordinary cs).2 hR
    simp only [one_mul] at hk
    dsimp only [f,g]
    nlinarith
  have hs := sumValues_cost_refinement_nonempty f g channels M (2^k) B R
    hne hlen hf hM htotal hcallback hg
  simpa only [querySources,CachedLowQuery.querySources,CachedLowQuery.physicalQueryChannels,
    List.map_map,Function.comp_def,f,g] using hs

theorem native_querySources_pos {L k q width : ℕ} [NeZero q] (t : ℕ)
    (channels : List (List (Fin k))) (hne : channels ≠ [])
    (embedding : Vector (Fin (2*L)) k) (ordinary : Vector (Fin 4) (2*L))
    (native : CachedLowQuery.SourceCaches L q width) (target : Fin q) :
    1 ≤ (CachedLowQuery.querySources t channels embedding ordinary native target).2 := by
  let g := fun cs : List (Fin k) =>
    let key := CachedLowQuery.physicalKey embedding ordinary cs
    key.2+(CachedLowQuery.channelKeyQuery k t native.1 native.2 key.1 cs.length target).2
  have hg : ∀ cs ∈ channels, 1 ≤ g cs := by
    intro cs _
    have hp := native_channelKeyQuery_pos k t native.1 native.2
      (CachedLowQuery.physicalKey embedding ordinary cs).1 cs.length target
    dsimp only [g]
    omega
  have hl := list_length_le_cost_sum channels g hg
  have hpos : 0 < channels.length := List.length_pos_iff.mpr hne
  have hs : 1 ≤ (channels.map g).sum := by omega
  simpa only [CachedLowQuery.querySources,CachedLowQuery.physicalQueryChannels,
    List.map_map,Function.comp_def,g] using hs

/-- Exact comparison with the native same-run query counter, including
binary accumulator additions, vector-index reads, and enumeration. -/
theorem queryRuns_cost_of_sourcesCost {L m k q width : ℕ} [NeZero q]
    (weights : WeightProgram) (t : ℕ) (channels : List (List (Fin k)))
    (embedding : Vector (Fin (2*L)) k) (ordinary : Vector (Fin 4) (2*L))
    (caches : RunCaches L m q width) (native : CachedLowQuery.RunCaches L m q width)
    (target : Fin q) (M B R : ℕ) (hne : channels ≠ [])
    (hM : M.size ≤ B) (htotal : ((2*m+1)*M).size ≤ B) (hindex : (2*m+1).size ≤ B)
    (hvalue : ∀ i, |denote (querySources weights t channels embedding ordinary (caches.get i) target).value| ≤ (M:ℤ))
    (hsource : ∀ i, (querySources weights t channels embedding ordinary (caches.get i) target).operations ≤
      R*(CachedLowQuery.querySources t channels embedding ordinary (native.get i) target).2) :
    (queryRuns weights t channels embedding ordinary caches target).operations ≤
      (R+60*(B+1)^2)*(CachedLowQuery.queryRuns t channels embedding ordinary native target).2 := by
  let f := fun i : Fin (2*m+1) =>
    let result := querySources weights t channels embedding ordinary (caches.get i) target
    (⟨result.value,result.operations+i.val.size+2⟩ : Counted Signed)
  let g := fun i : Fin (2*m+1) =>
    (CachedLowQuery.querySources t channels embedding ordinary (native.get i) target).2
  have hf : ∀ i ∈ List.finRange (2*m+1), |denote (f i).value| ≤ (M:ℤ) := by
    intro i _
    exact hvalue i
  have hg : ∀ i ∈ List.finRange (2*m+1), 1 ≤ g i := by
    intro i _
    exact native_querySources_pos t channels hne embedding ordinary (native.get i) target
  have hcallback : ∀ i ∈ List.finRange (2*m+1), (f i).operations ≤ (R+B+2)*g i := by
    intro i hi
    have hs := hsource i
    have hip : i.val.size ≤ B :=
      (Nat.size_le_size (by omega : i.val ≤ 2*m+1)).trans hindex
    have hp := hg i hi
    have hc := Nat.mul_le_mul_left (B+2) hp
    dsimp only [f,g] at *
    nlinarith
  have hs := sumValues_cost_refinement_nonempty f g (List.finRange (2*m+1)) M (2*m+1) B (R+B+2)
    (by simp) (by simp) hf hM htotal hcallback hg
  let nativeSum := ((List.finRange (2*m+1)).map g).sum
  have htotalcost : 2*m+1+nativeSum=
      (CachedLowQuery.queryRuns t channels embedding ordinary native target).2 := by
    simp only [CachedLowQuery.queryRuns,List.map_map,Function.comp_def,nativeSum,g]
  have hp : 1 ≤ (B+1)^2 := by nlinarith
  have hcounter : nativeSum ≤ (CachedLowQuery.queryRuns t channels embedding ordinary native target).2 := by
    omega
  have hcounter' : 2*m+1 ≤ (CachedLowQuery.queryRuns t channels embedding ordinary native target).2 := by
    omega
  have hscale := Nat.mul_le_mul_left (R+B+2+54*(B+1)^2) hcounter
  have haddress : 2*(2*m+1)*((2*m+1).size+1) ≤
      2*(B+1)*(CachedLowQuery.queryRuns t channels embedding ordinary native target).2 := by
    calc
      _ ≤ 2*(2*m+1)*(B+1) := Nat.mul_le_mul_left _ (by omega)
      _ = 2*(B+1)*(2*m+1) := by ring
      _ ≤ _ := Nat.mul_le_mul_left _ hcounter'
  have hpoly : B+2+54*(B+1)^2+2*(B+1) ≤ 60*(B+1)^2 := by nlinarith
  have hfinal := Nat.mul_le_mul_right
    (CachedLowQuery.queryRuns t channels embedding ordinary native target).2 hpoly
  change (sumValues f (List.finRange (2*m+1))).operations+2*(2*m+1)*((2*m+1).size+1) ≤ _
  change (sumValues f (List.finRange (2*m+1))).operations ≤ (R+B+2+54*(B+1)^2)*nativeSum at hs
  nlinarith

/-- Channel-result magnitudes derived from the literal binary cache
payloads, not from an assumed width of its degree-sum accumulator. -/
theorem channelQuery_magnitude {N q width : ℕ} [NeZero q]
    (weights : WeightProgram) (k t A : ℕ) (left right : Cache N q width)
    (key : ArrayKeys.Key N) (channelCard : ℕ) (target : Fin q)
    (hl : ∀ d r, |SparseLocalForms.denseRead (blockView (readBlock left key).1) d r| ≤ (A:ℤ))
    (hr : ∀ d r, |SparseLocalForms.denseRead (blockView (readBlock right key).1) d r| ≤ (A:ℤ)) :
    |denote (channelQuery weights k t left right key channelCard target).value| ≤
      (t*(2^k*t*q*A^2):ℕ) := by
  simp only [channelQuery,sumValues_value]
  apply BinaryLowBounds.list_partial_bound (List.range t) _ (2^k*t*q*A^2) t (by simp)
  intro d hd
  rw [lowTerm_value]
  exact BinaryLowBounds.lowTerm_bound k t A _ _ hl hr channelCard d (List.mem_range.mp hd) target

theorem querySources_magnitude {L k q width : ℕ} [NeZero q]
    (weights : WeightProgram) (t A : ℕ) (channels : List (List (Fin k)))
    (embedding : Vector (Fin (2*L)) k) (ordinary : Vector (Fin 4) (2*L))
    (cache : SourceCaches L q width) (target : Fin q) (hlen : channels.length ≤ 2^k)
    (hl : ∀ cs ∈ channels, ∀ d r,
      |SparseLocalForms.denseRead (blockView (readBlock cache.1
        (CachedLowQuery.physicalKey embedding ordinary cs).1).1) d r| ≤ (A:ℤ))
    (hr : ∀ cs ∈ channels, ∀ d r,
      |SparseLocalForms.denseRead (blockView (readBlock cache.2
        (CachedLowQuery.physicalKey embedding ordinary cs).1).1) d r| ≤ (A:ℤ)) :
    |denote (querySources weights t channels embedding ordinary cache target).value| ≤
      (2^(2*k)*t^2*q*A^2:ℕ) := by
  have hf : ∀ cs ∈ channels,
      |denote (channelQuery weights k t cache.1 cache.2
        (CachedLowQuery.physicalKey embedding ordinary cs).1 cs.length target).value| ≤
        (t*(2^k*t*q*A^2):ℕ) := by
    intro cs hcs
    exact channelQuery_magnitude weights k t A cache.1 cache.2 _ cs.length target
      (hl cs hcs) (hr cs hcs)
  have hs := BinaryLowBounds.channel_sum_partial_bound channels
    (fun cs => denote (channelQuery weights k t cache.1 cache.2
      (CachedLowQuery.physicalKey embedding ordinary cs).1 cs.length target).value)
    k t q A hlen hf
  simpa only [querySources,sumValues_value] using hs

/-- Matching-run result sum, with every source value already derived from
its actual read blocks by querySources_magnitude. -/
theorem queryRuns_magnitude {L m k q width : ℕ} [NeZero q]
    (weights : WeightProgram) (t A : ℕ) (channels : List (List (Fin k)))
    (embedding : Vector (Fin (2*L)) k) (ordinary : Vector (Fin 4) (2*L))
    (caches : RunCaches L m q width) (target : Fin q)
    (hsource : ∀ i,
      |denote (querySources weights t channels embedding ordinary (caches.get i) target).value| ≤
      (2^(2*k)*t^2*q*A^2:ℕ)) :
    |denote (queryRuns weights t channels embedding ordinary caches target).value| ≤
      ((2*m+1)*(2^(2*k)*t^2*q*A^2):ℕ) := by
  have hs := BinaryLowBounds.run_sum_partial_bound (List.finRange (2*m+1))
    (fun i => denote (querySources weights t channels embedding ordinary (caches.get i) target).value)
    m k t q A (by simp) (fun i _ => hsource i)
  simpa only [queryRuns,sumValues_value] using hs

def queryWidth (L m k t q A : ℕ) : ℕ :=
  (BinaryLowBounds.lowMagnitude m k t q A).size+
    CachedLowQuery.weightBitWidth k t+k+t+q.size+(2*m+1).size+2*L+10

theorem queryWidth_of_cap (L m k t q A value : ℕ)
    (hvalue : value ≤ BinaryLowBounds.lowMagnitude m k t q A) :
    value.size ≤ queryWidth L m k t q A := by
  have h := Nat.size_le_size hvalue
  unfold queryWidth
  omega

theorem queryWidth_small (L m k t q A : ℕ) :
    CachedLowQuery.weightBitWidth k t ≤ queryWidth L m k t q A ∧
    k+t+2 ≤ queryWidth L m k t q A ∧
    q.size ≤ queryWidth L m k t q A ∧
    (2*m+1).size ≤ queryWidth L m k t q A ∧
    2*L ≤ queryWidth L m k t q A := by
  unfold queryWidth
  omega

theorem queryWidth_index (L m k t q A i : ℕ) (hi : i ≤ k+t+2) :
    i.size ≤ queryWidth L m k t q A := by
  have hsize : i.size ≤ i := Nat.size_le.mpr Nat.lt_two_pow_self
  exact hsize.trans (hi.trans (queryWidth_small L m k t q A).2.1)

theorem queryWidth_A (L m k t q A : ℕ) : A.size ≤ queryWidth L m k t q A :=
  queryWidth_of_cap L m k t q A A (BinaryLowBounds.intermediate_caps m k t q A 0 (by omega)).1

theorem queryWidth_A_sq (L m k t q A : ℕ) : (A^2).size ≤ queryWidth L m k t q A :=
  queryWidth_of_cap L m k t q A (A^2) (BinaryLowBounds.intermediate_caps m k t q A 0 (by omega)).2.1

theorem queryWidth_qdot (L m k t q A : ℕ) : (q*A^2).size ≤ queryWidth L m k t q A :=
  queryWidth_of_cap L m k t q A (q*A^2) (BinaryLowBounds.intermediate_caps m k t q A 0 (by omega)).2.2.1

theorem queryWidth_polyDot (L m k t q A degree card : ℕ) (hdegree : degree < t) :
    ((degree-card+1)*(q*A^2)).size ≤ queryWidth L m k t q A := by
  have hp := (BinaryLowBounds.intermediate_caps m k t q A (degree-card) (by omega)).2.2.2.1
  apply queryWidth_of_cap L m k t q A
  simpa only [Nat.mul_assoc] using hp

/-- The source/channel/run magnitude endpoints themselves are all below
one explicitly derived cap, so their Nat.size assumptions in the cost
refinements do not become hypotheses about an execution's intermediates. -/
theorem queryWidth_sum_endpoints (L m k t q A : ℕ) :
    (t*(2^k*t*q*A^2)).size ≤ queryWidth L m k t q A ∧
    (2^k*(t*(2^k*t*q*A^2))).size ≤ queryWidth L m k t q A ∧
    (2^(2*k)*t^2*q*A^2).size ≤ queryWidth L m k t q A ∧
    ((2*m+1)*(2^(2*k)*t^2*q*A^2)).size ≤ queryWidth L m k t q A := by
  let channel := t*(2^k*t*q*A^2)
  let source := 2^(2*k)*t^2*q*A^2
  have he : 2^k*channel=source := by
    dsimp only [channel,source]
    rw [show 2*k=k+k by omega,pow_add]
    ring
  have hrun := BinaryLowBounds.low_run_cap m k t q A
  have hsource : source ≤ BinaryLowBounds.lowMagnitude m k t q A := by
    have hmult := Nat.mul_le_mul_right source (by omega : 1 ≤ 2*m+1)
    simpa only [one_mul,source] using hmult.trans hrun
  have hchannel : channel ≤ BinaryLowBounds.lowMagnitude m k t q A := by
    have hmult := Nat.mul_le_mul_right channel (Nat.one_le_pow k 2 (by decide))
    simpa only [one_mul,he] using hmult.trans (by simpa only [he] using hsource)
  have h2 : 2^k*(t*(2^k*t*q*A^2)) ≤ BinaryLowBounds.lowMagnitude m k t q A := by
    change 2^k*channel ≤ _
    rw [he]
    exact hsource
  exact ⟨queryWidth_of_cap L m k t q A _ hchannel,
    queryWidth_of_cap L m k t q A _ h2,
    queryWidth_of_cap L m k t q A _ hsource,
    queryWidth_of_cap L m k t q A _ hrun⟩

theorem generated_channels_nonempty (k t : ℕ) : LowChannelEnumeration.members k t ≠ [] := by
  exact List.ne_nil_of_mem (LowChannelEnumeration.nil_mem_generate (List.finRange k) t)

theorem generated_channels_length_le (k t : ℕ) :
    (LowChannelEnumeration.members k t).length ≤ 2^k := by
  calc
    _ = (LowChannelEnumeration.sets k t).toFinset.card := by
      rw [List.toFinset_card_of_nodup (LowChannelEnumeration.sets_nodup k t)]
      simp only [LowChannelEnumeration.sets,List.length_map]
    _ ≤ (Finset.univ : Finset (Finset (Fin k))).card := by
      simpa only [Finset.card_univ] using Finset.card_le_univ (LowChannelEnumeration.sets k t).toFinset
    _ = _ := by simp

theorem nat_size_succ_bound (n : ℕ) : (n+1).size ≤ n.size+1 := by
  apply Nat.size_le.mpr
  have h := Nat.lt_size_self n
  have hp : 0 < 2^n.size := by positivity
  rw [pow_succ]
  omega

/-- The common endpoint allowance grows quadratically in physical query
parameters and linearly in the binary lengths of q and the leaf magnitude.
It never introduces a power of the cyclic dimension into a query bound. -/
theorem queryWidth_polynomial (L m k t q A : ℕ) :
    queryWidth L m k t q A ≤
      2*(k+t+2)^2+3*k+3*t+4*m+2*L+2*q.size+2*A.size+20 := by
  have hlo := BinaryLowBounds.lowMagnitude_size m k t q A
  have hrun : (2*m+1).size ≤ 2*m+1 := Nat.size_le.mpr Nat.lt_two_pow_self
  have ht : (t+1).size ≤ t+1 := Nat.size_le.mpr Nat.lt_two_pow_self
  have hq := nat_size_succ_bound q
  have hA := nat_size_succ_bound A
  unfold queryWidth BinaryLowBounds.lowBitWidth at *
  unfold CachedLowQuery.weightBitWidth
  omega

def completeWidth (L m k t q A H : ℕ) : ℕ := queryWidth L m k t q A+H.size+2

theorem size_add (a b : ℕ) : (a+b).size≤a.size+b.size+1 := by
  apply Nat.size_le.mpr
  calc
    a+b<2^a.size+2^b.size := Nat.add_lt_add (Nat.lt_size_self a) (Nat.lt_size_self b)
    _≤2^(a.size+b.size+1) := by
      have ha : 2^a.size≤2^(a.size+b.size) := Nat.pow_le_pow_right (by decide) (by omega)
      have hb : 2^b.size≤2^(a.size+b.size) := Nat.pow_le_pow_right (by decide) (by omega)
      rw [pow_succ]
      omega

theorem completeWidth_caps (L m k t q A H : ℕ) :
    (BinaryLowBounds.lowMagnitude m k t q A).size≤completeWidth L m k t q A H ∧
    H.size≤completeWidth L m k t q A H ∧
    (BinaryLowBounds.lowMagnitude m k t q A+H).size≤completeWidth L m k t q A H ∧
    2*L+1≤completeWidth L m k t q A H := by
  have hs := size_add (BinaryLowBounds.lowMagnitude m k t q A) H
  unfold completeWidth queryWidth
  omega

def signedCell (a : Signed) : BinaryArrayFFT.Integer :=
  ⟨a.val,by simpa only [denote] using magnitude_length a⟩

theorem signedCell_view (a : Signed) : (signedCell a).view=denote a := rfl

/-- The returned common binary cell reuses the normalized result's bits;
it performs no semantic integer conversion at the backend boundary. -/
def queryCell {L m k q width : ℕ} [NeZero q] (t : ℕ)
    (embedding : Vector (Fin (2*L)) k) (ordinary : Vector (Fin 4) (2*L))
    (caches : RunCaches L m q width) (target : Fin q)
    (high : Counted BinaryArrayFFT.Integer) : Counted BinaryArrayFFT.Integer :=
  let output := queryComplete t embedding ordinary caches target high
  ⟨signedCell output.value,output.operations+1⟩

theorem queryCell_value {L m k q width : ℕ} [NeZero q] (t : ℕ)
    (embedding : Vector (Fin (2*L)) k) (ordinary : Vector (Fin 4) (2*L))
    (caches : RunCaches L m q width) (native : CachedLowQuery.RunCaches L m q width)
    (hcache : ∀ i, CacheRefines (caches.get i).1 (native.get i).1 ∧
      CacheRefines (caches.get i).2 (native.get i).2) (target : Fin q)
    (high : Counted BinaryArrayFFT.Integer) :
    (queryCell t embedding ordinary caches target high).value.view=
      (IntegerArithmetic.binaryExactDivCounted (4^L)
        ((CachedLowQuery.queryLowRuns t embedding ordinary native target).1+high.value.view)).1 := by
  exact queryComplete_value t embedding ordinary caches native hcache target high

theorem queryCell_exact {L m k q width : ℕ} [NeZero q] (t : ℕ)
    (embedding : Vector (Fin (2*L)) k) (ordinary : Vector (Fin 4) (2*L))
    (caches : RunCaches L m q width) (native : CachedLowQuery.RunCaches L m q width)
    (hcache : ∀ i, CacheRefines (caches.get i).1 (native.get i).1 ∧
      CacheRefines (caches.get i).2 (native.get i).2) (target : Fin q)
    (high : Counted BinaryArrayFFT.Integer) (answer : ℤ)
    (hnum : (CachedLowQuery.queryLowRuns t embedding ordinary native target).1+
      high.value.view=((4^L:ℕ):ℤ)*answer) :
    (queryCell t embedding ordinary caches target high).value.view=answer := by
  rw [queryCell_value t embedding ordinary caches native hcache target high]
  exact IntegerArithmetic.binaryExactDivCounted_exact _ _ _ (by positivity) hnum

def CacheBound {N q width : ℕ} (table : Cache N q width) (A : ℕ) : Prop :=
  ∀ key d r, |SparseLocalForms.denseRead (blockView (readBlock table key).1) d r| ≤ (A:ℤ)

def RunBound {L m q width : ℕ} (caches : RunCaches L m q width) (A : ℕ) : Prop :=
  ∀ i, CacheBound (caches.get i).1 A ∧ CacheBound (caches.get i).2 A

/-- Complete executable LOW query bound against the exact native counter.
Only the original stored leaf coefficient bound is a magnitude hypothesis;
all arithmetic and accumulator width endpoints are derived from it. -/
theorem queryLowRuns_cost_of_bound {L m k q width : ℕ} [NeZero q]
    (t A : ℕ) (embedding : Vector (Fin (2*L)) k)
    (ordinary : Vector (Fin 4) (2*L)) (caches : RunCaches L m q width)
    (native : CachedLowQuery.RunCaches L m q width)
    (hcache : ∀ i, CacheRefines (caches.get i).1 (native.get i).1 ∧
      CacheRefines (caches.get i).2 (native.get i).2)
    (hbound : RunBound caches A) (target : Fin q) :
    (queryLowRuns actualWeights t embedding ordinary caches target).operations ≤
      500000*(queryWidth L m k t q A+1)^3*
        (CachedLowQuery.queryLowRuns t embedding ordinary native target).2 := by
  let B := queryWidth L m k t q A
  let P := 100000*(B+1)^3
  let channels := LowChannelEnumeration.members k t
  let C := t*(2^k*t*q*A^2)
  let S := 2^(2*k)*t^2*q*A^2
  have hsmall := queryWidth_small L m k t q A
  have hend := queryWidth_sum_endpoints L m k t q A
  have hM : (2^k*t*q*A^2).size ≤ B := by
    apply queryWidth_of_cap L m k t q A
    apply le_trans _ (BinaryLowBounds.data_cap m k t q A)
    gcongr
    omega
  have hP : 1 ≤ 4*P := by
    have hp : 0 < (B+1)^3 := by positivity
    dsimp only [P]
    omega
  have hnonempty : channels ≠ [] := generated_channels_nonempty k t
  have hlength : channels.length ≤ 2^k := generated_channels_length_le k t
  have hsourcevalue : ∀ i,
      |denote (querySources actualWeights t channels embedding ordinary (caches.get i) target).value| ≤ (S:ℤ) := by
    intro i
    exact querySources_magnitude actualWeights t A channels embedding ordinary (caches.get i)
      target hlength (fun _ _ => (hbound i).1 _) (fun _ _ => (hbound i).2 _)
  have hsourcecost : ∀ i,
      (querySources actualWeights t channels embedding ordinary (caches.get i) target).operations ≤
      (4*P+54*(B+1)^2)*
        (CachedLowQuery.querySources t channels embedding ordinary (native.get i) target).2 := by
    intro i
    apply querySources_cost_of_channelCost actualWeights t channels embedding ordinary
      (caches.get i) (native.get i) target C B (4*P) hP hnonempty hlength hend.1 hend.2.1
    · intro cs _
      exact channelQuery_magnitude actualWeights k t A (caches.get i).1 (caches.get i).2
        _ cs.length target ((hbound i).1 _) ((hbound i).2 _)
    · intro cs hcs
      exact channelQuery_cost_probe k t A B cs.length (caches.get i).1 (caches.get i).2
        (native.get i).1 (native.get i).2 (hcache i).1 (hcache i).2 _ target
        ((hbound i).1 _) ((hbound i).2 _)
        (LowChannelEnumeration.member_length_le_dimension k t cs hcs)
        (queryWidth_A L m k t q A) hsmall.2.2.1 (queryWidth_qdot L m k t q A)
        hM hend.1 hsmall.1 hsmall.2.1
  have hruns := queryRuns_cost_of_sourcesCost actualWeights t channels embedding ordinary
    caches native target S B (4*P+54*(B+1)^2) hnonempty hend.2.2.1 hend.2.2.2
    hsmall.2.2.2.1 hsourcevalue hsourcecost
  have hpoly : 4*P+54*(B+1)^2+60*(B+1)^2 ≤ 500000*(B+1)^3 := by
    have hp : (B+1)^2 ≤ (B+1)^3 := by nlinarith [show 1 ≤ B+1 by omega]
    dsimp only [P]
    nlinarith
  have hruns' := hruns.trans (Nat.mul_le_mul_right
    (CachedLowQuery.queryRuns t channels embedding ordinary native target).2 hpoly)
  have hfactor : 1 ≤ 500000*(B+1)^3 := by
    have hp : 0 < (B+1)^3 := by positivity
    omega
  have hgen := Nat.mul_le_mul_right
    (8*k+(LowChannelEnumeration.generate (List.finRange k) t).work) hfactor
  simp only [one_mul] at hgen
  change 8*k+(LowChannelEnumeration.generate (List.finRange k) t).work+
    (queryRuns actualWeights t channels embedding ordinary caches target).operations ≤
    500000*(B+1)^3*(8*k+(LowChannelEnumeration.generate (List.finRange k) t).work+
      (CachedLowQuery.queryRuns t channels embedding ordinary native target).2)
  nlinarith

/-- Complete LOW value bound from actual stored leaf coefficients. -/
theorem queryLowRuns_magnitude_of_bound {L m k q width : ℕ} [NeZero q]
    (weights : WeightProgram) (t A : ℕ) (embedding : Vector (Fin (2*L)) k)
    (ordinary : Vector (Fin 4) (2*L)) (caches : RunCaches L m q width)
    (hbound : RunBound caches A) (target : Fin q) :
    |denote (queryLowRuns weights t embedding ordinary caches target).value| ≤
      (BinaryLowBounds.lowMagnitude m k t q A:ℤ) := by
  have hlength := generated_channels_length_le k t
  have hs := queryRuns_magnitude weights t A (LowChannelEnumeration.members k t)
    embedding ordinary caches target (by
      intro i
      exact querySources_magnitude weights t A _ embedding ordinary (caches.get i)
        target hlength (fun _ _ => (hbound i).1 _) (fun _ _ => (hbound i).2 _))
  apply hs.trans
  exact_mod_cast BinaryLowBounds.low_run_cap m k t q A

/-- Closed coefficient arithmetic and normalization cost. The supplied
binary HIGH lookup retains its own actual counter; no HIGH time bound is
postulated in this theorem. -/
theorem queryCell_cost {L m k q width : ℕ} [NeZero q]
    (t A H : ℕ) (embedding : Vector (Fin (2*L)) k)
    (ordinary : Vector (Fin 4) (2*L)) (caches : RunCaches L m q width)
    (native : CachedLowQuery.RunCaches L m q width)
    (hcache : ∀ i, CacheRefines (caches.get i).1 (native.get i).1 ∧
      CacheRefines (caches.get i).2 (native.get i).2)
    (hbound : RunBound caches A) (target : Fin q)
    (high : Counted BinaryArrayFFT.Integer) (hh : |high.value.view|≤(H:ℤ)) :
    (queryCell t embedding ordinary caches target high).operations ≤
      500000*(queryWidth L m k t q A+1)^3*
        (CachedLowQuery.queryLowRuns t embedding ordinary native target).2+
      high.operations+1000*(completeWidth L m k t q A H+1)^2+1 := by
  have hl := queryLowRuns_magnitude_of_bound actualWeights t A embedding ordinary caches hbound target
  have hc := queryLowRuns_cost_of_bound t A embedding ordinary caches native hcache hbound target
  have hw := completeWidth_caps L m k t q A H
  have hn := normalizeComplete_cost L (queryLowRuns actualWeights t embedding ordinary caches target)
    high (BinaryLowBounds.lowMagnitude m k t q A) H (completeWidth L m k t q A H)
    hl hh hw.1 hw.2.1 hw.2.2.1 hw.2.2.2
  change (normalizeComplete L (queryLowRuns actualWeights t embedding ordinary caches target) high).operations+1≤_
  omega

theorem queryCell_cost_polynomial {L m k q width : ℕ} [NeZero q]
    (t A H : ℕ) (embedding : Vector (Fin (2*L)) k)
    (ordinary : Vector (Fin 4) (2*L)) (caches : RunCaches L m q width)
    (native : CachedLowQuery.RunCaches L m q width)
    (hcache : ∀ i, CacheRefines (caches.get i).1 (native.get i).1 ∧
      CacheRefines (caches.get i).2 (native.get i).2)
    (hbound : RunBound caches A) (target : Fin q)
    (high : Counted BinaryArrayFFT.Integer) (hh : |high.value.view|≤(H:ℤ)) :
    (queryCell t embedding ordinary caches target high).operations ≤
      1000000*(completeWidth L m k t q A H+1)^3*
        ((CachedLowQuery.queryLowRuns t embedding ordinary native target).2+high.operations+1) := by
  have hc := queryCell_cost t A H embedding ordinary caches native hcache hbound target high hh
  have hw : queryWidth L m k t q A+1≤completeWidth L m k t q A H+1 := by
    unfold completeWidth
    omega
  have hp := Nat.pow_le_pow_left hw 3
  have hs : (completeWidth L m k t q A H+1)^2≤(completeWidth L m k t q A H+1)^3 := by
    apply Nat.pow_le_pow_right (by omega)
    decide
  have h1 : 1≤(completeWidth L m k t q A H+1)^3 :=
    Nat.one_le_pow _ _ (by omega)
  have hl := Nat.mul_le_mul_right (CachedLowQuery.queryLowRuns t embedding ordinary native target).2
    (Nat.mul_le_mul_left 500000 hp)
  have hh' := Nat.mul_le_mul_right high.operations h1
  have hn := Nat.mul_le_mul_left 1000 hs
  nlinarith

end ThinMatrix.BinaryLowQuery

#print axioms ThinMatrix.BinaryLowQuery.normalizeCell_value
#print axioms ThinMatrix.BinaryLowQuery.sumValues_cost
#print axioms ThinMatrix.BinaryLowQuery.selectedDot_value
#print axioms ThinMatrix.BinaryLowQuery.lowTerm_value
#print axioms ThinMatrix.BinaryLowQuery.queryLowRuns_value
#print axioms ThinMatrix.BinaryLowQuery.normalizeComplete_value
#print axioms ThinMatrix.BinaryLowQuery.normalizeComplete_exact
#print axioms ThinMatrix.BinaryLowQuery.normalizeComplete_cost
#print axioms ThinMatrix.BinaryLowQuery.queryWidth_polynomial
#print axioms ThinMatrix.BinaryLowQuery.queryLowRuns_cost_of_bound
#print axioms ThinMatrix.BinaryLowQuery.queryCell_exact
#print axioms ThinMatrix.BinaryLowQuery.queryCell_cost_polynomial
