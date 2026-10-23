import DistinguishedResidualSupport

set_option autoImplicit false

/-! The original first-scan masks imply the normal cap, so the normal crop
in the distinguished-root support proof is redundant on both actual Walsh
sources. The resulting remaining cap makes the first-window crop lossless.
This closes the finite source-support obligation; retained binary polynomial
root arrays, the opposite forward map, and the shared prefix encoder remain
separate implementation obligations. -/
namespace ThinMatrix.ExactHalfResidualWindow
open WalshEmbedding GoodSetConstruction GoodMapEmbedding
open ExactHalfCroppedEmbedding MaskedLightSources DistinguishedResidualSupport
open scoped BigOperators
variable {R : Type*} [CommRing R]
noncomputable section

def leftSource {L m : ℕ} (X : RawLeftInput L m (L-m) R)
    (r s : Fin (shifts m).length) (run : ℤ) :
    (Fin L → NormalLetter) → (Fin L → OppositeLetter) → R :=
  rawLeftSource (leftInput X (scanPick L m) (shifts m).get r s)
    (goodSlots L m) (cubeMap (constructGoodMaps L m).1) (cubeMap (constructGoodMaps L m).2) run

def rightSource {L m : ℕ} (Y : RawRightInput L m (L-m) R)
    (r s : Fin (shifts m).length) (run : ℤ) :
    (Fin L → NormalLetter) → (Fin L → OppositeLetter) → R :=
  rawRightSource (rightInput Y (scanPick L m) (shifts m).get r s)
    (goodSlots L m) (cubeMap (constructGoodMaps L m).1) (cubeMap (constructGoodMaps L m).2) run

theorem left_normal_cap {L m : ℕ} (X : RawLeftInput L m (L-m) R)
    (r s : Fin (shifts m).length) (run : ℤ) (n : Fin L → NormalLetter) (o : Fin L → OppositeLetter)
    (h : m/2<ones (normalP2Bits n)) : leftSource X r s run n o=0 :=
  MaskedLightSources.left_normal_cap (m/2) X (scanPick L m) (shifts m).get (weight L m)
    (goodSlots L m) (cubeMap (constructGoodMaps L m).1) (cubeMap (constructGoodMaps L m).2)
    (fun Q _ => scanPick_valid L m Q) (normal_weight L m) r s run n o h

theorem right_normal_cap {L m : ℕ} (Y : RawRightInput L m (L-m) R)
    (r s : Fin (shifts m).length) (run : ℤ) (n : Fin L → NormalLetter) (o : Fin L → OppositeLetter)
    (h : m/2<ones (normalP2Bits n)) : rightSource Y r s run n o=0 :=
  MaskedLightSources.right_normal_cap (m/2) Y (scanPick L m) (shifts m).get (weight L m)
    (goodSlots L m) (cubeMap (constructGoodMaps L m).1) (cubeMap (constructGoodMaps L m).2)
    (fun Q _ => scanPick_valid L m Q) (normal_weight L m) r s run n o h

theorem left_crop_eq {L m : ℕ} (X : RawLeftInput L m (L-m) R)
    (r s : Fin (shifts m).length) (run : ℤ) :
    cropBoth (m/2) (leftSource X r s run) = CroppedSourceContraction.crop (m/2) (leftSource X r s run) :=
  cropBoth_eq_crop _ _ (left_normal_cap X r s run)

theorem right_crop_eq {L m : ℕ} (Y : RawRightInput L m (L-m) R)
    (r s : Fin (shifts m).length) (run : ℤ) :
    cropBoth (m/2) (rightSource Y r s run) = CroppedSourceContraction.crop (m/2) (rightSource Y r s run) :=
  cropBoth_eq_crop _ _ (right_normal_cap Y r s run)

def packedRoot {L m k : ℕ} (eN eO : Layout L m k) (cn co : Cube m) (z : R)
    (cap : ℕ) (source : (Fin L → NormalLetter) → (Fin L → OppositeLetter) → R)
    (w : CroppedGroupedSuffix.Word (2*k)) : R :=
  root eN eO cn co z cap source
    (fun i => w (BinaryWindowPartition.halfIndex true i))
    (fun i => w (BinaryWindowPartition.halfIndex false i))

theorem selected_cap {L m k : ℕ} (eN eO : Layout L m k) (cn co : Cube m) (z : R)
    (cap : ℕ) (source : (Fin L → NormalLetter) → (Fin L → OppositeLetter) → R)
    (w : CroppedGroupedSuffix.Word (2*k)) (h : packedRoot eN eO cn co z cap source w≠0) :
    CyclicLightWindow.count (BinaryWindowPartition.bits (decide (ones co≤ones cn)) w) ≤ cap-max (ones cn) (ones co) := by
  have hc := remaining_caps eN eO cn co z cap source
    (fun i => w (BinaryWindowPartition.halfIndex true i))
    (fun i => w (BinaryWindowPartition.halfIndex false i)) h
  simp only [rareCount,ones_count] at hc
  have hcn := ones_count cn
  have hco := ones_count co
  by_cases hn : ones co≤ones cn
  · simp only [hn,decide_true,Nat.max_eq_left hn]
    change CyclicLightWindow.count (fun i => decide (w (BinaryWindowPartition.halfIndex true i)=2))≤_
    omega
  · have ho : ones cn≤ones co := by omega
    simp only [hn,decide_false,Nat.max_eq_right ho]
    change CyclicLightWindow.count (fun i => decide (w (BinaryWindowPartition.halfIndex false i)=2))≤_
    omega

/-- The selected global crop used by BinaryWindowPartition is now proved
redundant for a distinguished root, with normal-half ties and all zero roots. -/
theorem selected_crop_eq {L m k : ℕ} (eN eO : Layout L m k) (cn co : Cube m) (z : R)
    (cap : ℕ) (source : (Fin L → NormalLetter) → (Fin L → OppositeLetter) → R)
    (w : CroppedGroupedSuffix.Word (2*k)) :
    (if CyclicLightWindow.count (BinaryWindowPartition.bits (decide (ones co≤ones cn)) w)≤cap-max (ones cn) (ones co)
     then packedRoot eN eO cn co z cap source w else 0) = packedRoot eN eO cn co z cap source w := by
  by_cases h : packedRoot eN eO cn co z cap source w=0
  · simp [h]
  · simp [selected_cap eN eO cn co z cap source w h]

theorem window_reconstruction {L m k : ℕ} [NeZero k] (ell : ℕ)
    (eN eO : Layout L m k) (cn co : Cube m) (z : R) (cap : ℕ)
    (source : (Fin L → NormalLetter) → (Fin L → OppositeLetter) → R)
    (w : CroppedGroupedSuffix.Word (2*k)) :
    (∑ s, CyclicLightWindow.component ell (cap-max (ones cn) (ones co))
      (BinaryWindowPartition.bits (decide (ones co≤ones cn)) w) s
      (packedRoot eN eO cn co z cap source w)) = packedRoot eN eO cn co z cap source w := by
  rw [CyclicLightWindow.component_sum,selected_crop_eq]

/-- Reconstruction remains exact after an arbitrary entangled linear query.
Each input's windows are summed before any residual product. -/
theorem window_contraction {L m k : ℕ} [NeZero k] (ell : ℕ)
    (eN eO : Layout L m k) (cn co : Cube m) (z : R) (cap : ℕ)
    (source : (Fin L → NormalLetter) → (Fin L → OppositeLetter) → R)
    (K : CroppedGroupedSuffix.Word (2*k) → R) :
    (∑ s, ∑ w, K w*CyclicLightWindow.component ell (cap-max (ones cn) (ones co))
      (BinaryWindowPartition.bits (decide (ones co≤ones cn)) w) s
      (packedRoot eN eO cn co z cap source w)) = ∑ w, K w*packedRoot eN eO cn co z cap source w := by
  rw [Finset.sum_comm]
  simp_rw [← Finset.mul_sum,window_reconstruction]

/-- Every formal degree and every cyclic residue is retained by reconstruction.
No selected-coefficient or evaluation-at-one projection is used. -/
theorem coefficient_window_reconstruction {L m k q : ℕ} [NeZero k] [NeZero q] (ell : ℕ)
    (eN eO : Layout L m k) (cn co : Cube m) (cap : ℕ)
    (source : (Fin L → NormalLetter) → (Fin L → OppositeLetter) → Polynomial (CyclicRing.Cyclic q))
    (w : CroppedGroupedSuffix.Word (2*k)) (degree : ℕ) (residue : Fin q) :
    (∑ s, ((CyclicLightWindow.component ell (cap-max (ones cn) (ones co))
      (BinaryWindowPartition.bits (decide (ones co≤ones cn)) w) s
      (packedRoot eN eO cn co Polynomial.X cap source w)).coeff degree) residue) =
      ((packedRoot eN eO cn co Polynomial.X cap source w).coeff degree) residue := by
  have h := congrArg (fun p : Polynomial (CyclicRing.Cyclic q) => (p.coeff degree) residue)
    (window_reconstruction ell eN eO cn co Polynomial.X cap source w)
  simpa only [Polynomial.finsetSum_coeff,CyclicRing.sum_coeff] using h

#print axioms left_normal_cap
#print axioms right_normal_cap
#print axioms left_crop_eq
#print axioms right_crop_eq
#print axioms selected_cap
#print axioms selected_crop_eq
#print axioms window_reconstruction
#print axioms window_contraction
#print axioms coefficient_window_reconstruction
end
end ThinMatrix.ExactHalfResidualWindow
