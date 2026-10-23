import RetainedChannelPowerset

set_option autoImplicit false
set_option maxHeartbeats 800000

/-! The shifted physical pencil, with the opposite halves crossed between
inputs, equals the weighted sum over the actual retained strict channel list.
This is over arbitrary commutative coefficient rings, including cyclic rings. -/
namespace ThinMatrix.ShiftedLowChannelFormula
open WalshEmbedding DistinguishedResidualRoot ResidualFamilyKeys TensorContraction
open scoped BigOperators
variable {R A B : Type*} [CommRing R] [Fintype A] [Fintype B]

noncomputable def leftFactor {m : ℕ} (c : Channel m) (X : A → Polynomial R)
    (n : A → Fin m → NormalLetter) (o : A → Fin m → OppositeLetter) : Polynomial R :=
  ∑ a, X a*(kernel (normal c).get Polynomial.X (n a)*(∏ i, oppositeFactor ((opposite c).get i) (o a i)))

noncomputable def rightFactor {m : ℕ} (c : Channel m) (Y : B → Polynomial R)
    (n : B → Fin m → NormalLetter) (o : B → Fin m → OppositeLetter) : Polynomial R :=
  leftFactor (ResidualChannelTranspose.swap c) Y n o

noncomputable def leftH {m : ℕ} (n : A → Fin m → NormalLetter) (o : A → Fin m → OppositeLetter)
    (i : Fin (m+m)) (a : A) : Polynomial R :=
  Fin.addCases (fun j => normalFactor false Polynomial.X (n a j)) (fun j => oppositeFactor false (o a j)) i

noncomputable def leftU {m : ℕ} (n : A → Fin m → NormalLetter) (o : A → Fin m → OppositeLetter)
    (i : Fin (m+m)) (a : A) : Polynomial R :=
  Fin.addCases (fun j => normalFactor true Polynomial.X (n a j)) (fun j => oppositeFactor true (o a j)) i

noncomputable def rightH {m : ℕ} (n : B → Fin m → NormalLetter) (o : B → Fin m → OppositeLetter)
    (i : Fin (m+m)) (b : B) : Polynomial R :=
  Fin.addCases (fun j => oppositeFactor false (o b j)) (fun j => normalFactor false Polynomial.X (n b j)) i

noncomputable def rightU {m : ℕ} (n : B → Fin m → NormalLetter) (o : B → Fin m → OppositeLetter)
    (i : Fin (m+m)) (b : B) : Polynomial R :=
  Fin.addCases (fun j => oppositeFactor true (o b j)) (fun j => normalFactor true Polynomial.X (n b j)) i

theorem selected_product {N : ℕ} (c : Vector Bool N) (h u : Fin N → Polynomial R) :
    ((∏ i∈CappedBitPreparation.support c, u i)*(∏ i∈Finset.univ\CappedBitPreparation.support c, h i))=
      ∏ i, if c.get i then u i else h i := by
  classical
  rw [Finset.prod_ite]
  congr 1
  congr 1
  ext i
  simp [CappedBitPreparation.support]

theorem left_cache {m : ℕ} (c : Channel m) (X : A → Polynomial R)
    (n : A → Fin m → NormalLetter) (o : A → Fin m → OppositeLetter) :
    leftCache Finset.univ (CappedBitPreparation.support c) X (leftH n o) (leftU n o)=leftFactor c X n o := by
  classical
  unfold leftCache leftFactor
  apply Finset.sum_congr rfl
  intro a _
  rw [selected_product]
  congr 1
  rw [Fin.prod_univ_add]
  simp only [leftH,leftU,Fin.addCases_left,Fin.addCases_right,kernel,normal,opposite,Vector.get_ofFn]
  congr 1
  · apply Finset.prod_congr rfl; intro i _
    cases c.get (Fin.castAdd _ i) <;> rfl
  · apply Finset.prod_congr rfl; intro i _
    cases c.get (Fin.natAdd _ i) <;> rfl

theorem right_cache {m : ℕ} (c : Channel m) (Y : B → Polynomial R)
    (n : B → Fin m → NormalLetter) (o : B → Fin m → OppositeLetter) :
    rightCache Finset.univ (CappedBitPreparation.support c) Y (rightH n o) (rightU n o)=rightFactor c Y n o := by
  classical
  unfold rightCache rightFactor leftFactor
  simp only [ResidualChannelTranspose.normal_swap,ResidualChannelTranspose.opposite_swap]
  apply Finset.sum_congr rfl
  intro b _
  rw [selected_product]
  congr 1
  rw [Fin.prod_univ_add,mul_comm]
  simp only [rightH,rightU,Fin.addCases_left,Fin.addCases_right,kernel,normal,opposite,Vector.get_ofFn]
  congr 1
  · apply Finset.prod_congr rfl; intro i _
    cases c.get (Fin.natAdd _ i) <;> rfl
  · apply Finset.prod_congr rfl; intro i _
    cases c.get (Fin.castAdd _ i) <;> rfl

noncomputable def localPencil (n : NormalLetter) (o : OppositeLetter) : Polynomial R :=
  Polynomial.C (ShiftedSourceEmbedding.privateNormal n*ShiftedSourceEmbedding.privateOpposite o)+
    Polynomial.X*Polynomial.C (innerCoefficient n o)

theorem local_pencil (n : NormalLetter) (o : OppositeLetter) :
    normalFactor false Polynomial.X n*oppositeFactor false o+
      (Polynomial.X : Polynomial R)*normalFactor true Polynomial.X n*oppositeFactor true o=localPencil n o := by
  cases n <;> cases o <;>
    simp [localPencil,normalFactor,oppositeFactor,oppositeLetter,oppositeScale,
      ShiftedSourceEmbedding.privateNormal,ShiftedSourceEmbedding.privateOpposite,innerCoefficient, map_ofNat]
  all_goals ring

noncomputable def pencil {m : ℕ} (X : A → Polynomial R) (Y : B → Polynomial R)
    (nL : A → Fin m → NormalLetter) (oR : A → Fin m → OppositeLetter)
    (nR : B → Fin m → NormalLetter) (oL : B → Fin m → OppositeLetter) : Polynomial R :=
  bilinear X Y (fun a b => (∏ i, localPencil (nL a i) (oL b i))*(∏ i, localPencil (nR b i) (oR a i)))

theorem pencil_channels {m : ℕ} (X : A → Polynomial R) (Y : B → Polynomial R)
    (nL : A → Fin m → NormalLetter) (oR : A → Fin m → OppositeLetter)
    (nR : B → Fin m → NormalLetter) (oL : B → Fin m → OppositeLetter) :
    bilinear X Y (tensorKernel Finset.univ (fun i a b =>
      leftH nL oR i a*rightH nR oL i b+Polynomial.X*leftU nL oR i a*rightU nR oL i b))=
      pencil X Y nL oR nR oL := by
  unfold pencil
  congr 1
  funext a b
  unfold tensorKernel
  rw [Fin.prod_univ_add]
  simp only [leftH,rightH,leftU,rightU,Fin.addCases_left,Fin.addCases_right]
  congr 1
  · apply Finset.prod_congr rfl; intro i _
    exact local_pencil _ _
  · apply Finset.prod_congr rfl; intro i _
    rw [mul_comm (oppositeFactor false _),show Polynomial.X*oppositeFactor true (oR a i)*normalFactor true Polynomial.X (nR b i)=
      Polynomial.X*normalFactor true Polynomial.X (nR b i)*oppositeFactor true (oR a i) by ring]
    exact local_pencil _ _

theorem weighted_channels {m t : ℕ} (keys : Vector (Channel m) (channelCount m t))
    (hk : keys.toList=(channels m t).value) (X : A → Polynomial R) (Y : B → Polynomial R)
    (nL : A → Fin m → NormalLetter) (oR : A → Fin m → OppositeLetter)
    (nR : B → Fin m → NormalLetter) (oL : B → Fin m → OppositeLetter) :
    weightedLow (2*m) t (pencil X Y nL oR nR oL)=
      ∑ c, ∑ d∈Finset.range t,
        if (CappedBitPreparation.support (keys.get c)).card≤d then
          residualWeight (2*m) t d*((leftFactor (keys.get c) X nL oR*rightFactor (keys.get c) Y nR oL).coeff (d-(CappedBitPreparation.support (keys.get c)).card)) else 0 := by
  rw [← pencil_channels,weighted_low_uses_small_channel_sets]
  rw [← RetainedChannelPowerset.sum_support keys hk]
  simp only [left_cache,right_cache]

#print axioms selected_product
#print axioms left_cache
#print axioms right_cache
#print axioms local_pencil
#print axioms pencil_channels
#print axioms weighted_channels
end ThinMatrix.ShiftedLowChannelFormula
