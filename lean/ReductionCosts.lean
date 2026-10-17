import ThinProductCosts
import PhaseGeometry
import CompositeAlgorithm
import ArithmeticSlack

/-!
# Counted block preparation and the six phase terms

The finite counter below executes both shared input encoders, the high-box
schedule and one selected-coefficient query per outer pair per block. Formation
visits every coefficient of both packed inputs. Primitive coefficient and full
cyclic multiplication costs are explicit; this module never treats unbounded
integer multiplication as a unit operation.
-/
namespace ThinMatrix.ReductionCosts

noncomputable section
open scoped BigOperators
open ThinProductCosts PhaseGeometry EntropyBounds
open Filter Asymptotics
set_option maxRecDepth 10000
set_option maxHeartbeats 8000000

/-- Two packed N by D inputs, with all q coefficient cells visited. -/
def formationCost (N D q unit : ℕ) : ℕ :=
  ∑ _side : Fin 2, ∑ _row : Fin N, ∑ _inner : Fin D, ∑ _r : Fin q, unit

@[simp] theorem formationCost_eq (N D q unit : ℕ) :
    formationCost N D q unit = 2*N*D*q*unit := by
  simp [formationCost, mul_assoc]

/-- Materialized encoder inputs for one compact middle block. -/
structure BlockData (R : Type*) (c : ℝ) (N m : ℕ) where
  leftForms : Fin (TilingCosts.bandCount N (gridSide (Nat.ceil (c*(m:ℝ))) m)) →
    SharedEncoder.LocalForms R
  rightForms : Fin (TilingCosts.bandCount N (gridSide (Nat.ceil (c*(m:ℝ))) m)) →
    SharedEncoder.LocalForms R
  leftInput : Fin (TilingCosts.bandCount N (gridSide (Nat.ceil (c*(m:ℝ))) m)) →
    SharedEncoder.Dense (R := R) (2*Nat.ceil (c*(m:ℝ)))
      (SharedEncoder.rootDims (Nat.ceil (c*(m:ℝ))) true)
  rightInput : Fin (TilingCosts.bandCount N (gridSide (Nat.ceil (c*(m:ℝ))) m)) →
    SharedEncoder.Dense (R := R) (2*Nat.ceil (c*(m:ℝ)))
      (SharedEncoder.rootDims (Nat.ceil (c*(m:ℝ))) false)

/-- A block is prepared once and answers Q folded coefficient requests.
The degree width is separate from the cyclic coefficient width q. -/
def blockCost {R : Type*} [CommSemiring R] (c theta : ℝ)
    (N Q m q width linearUnit fullMultiply lookupUnit formationUnit : ℕ)
    (data : BlockData R c N m) : ℕ :=
  let L := Nat.ceil (c*(m:ℝ))
  let t := Nat.ceil (2*theta*(m:ℝ))
  formationCost N (4^m) q formationUnit +
    TilingCosts.executionCost
      (implementedLoopCosts (TilingCosts.bandCount N (gridSide L m)) Q L m t q width
        linearUnit fullMultiply lookupUnit data.leftForms data.rightForms
        data.leftInput data.rightInput)

/-- This sum shares each block's preparation across its outer-pair requests. -/
def blockScheduleCost {R : Type*} [CommSemiring R] (c theta : ℝ)
    (blocks N Q m q width linearUnit fullMultiply lookupUnit formationUnit : ℕ)
    (data : Fin blocks → BlockData R c N m) : ℕ :=
  ∑ j, blockCost c theta N Q m q width linearUnit fullMultiply lookupUnit formationUnit (data j)

theorem blockCost_le {R : Type*} [CommSemiring R] (c theta : ℝ)
    (N Q m q width linearUnit fullMultiply lookupUnit formationUnit : ℕ)
    (data : BlockData R c N m)
    (hc : 5 < c) (ht0 : 0 < theta) (ht1 : theta < 1/2) (hm : 0 < m)
    (hq : 1 ≤ q) (hwidth : Nat.ceil (2*theta*(m:ℝ)) ≤ width)
    (hgeometry : gridSide (Nat.ceil (c*(m:ℝ))) m ≤ N) :
    (blockCost c theta N Q m q width linearUnit fullMultiply lookupUnit formationUnit data : ℝ) ≤
      2*N*((4:ℝ)^m)*q*formationUnit +
        powerBound c theta N Q m q width linearUnit fullMultiply lookupUnit := by
  have h := implemented_rounded_power c theta N Q m q width linearUnit fullMultiply lookupUnit
    hc ht0 ht1 hm hq hwidth hgeometry data.leftForms data.rightForms data.leftInput data.rightInput
  simpa only [blockCost, formationCost_eq, Nat.cast_add, Nat.cast_mul, Nat.cast_pow,
    Nat.cast_ofNat, add_comm] using add_le_add_left h (2*N*((4:ℝ)^m)*q*formationUnit)

theorem blockScheduleCost_le {R : Type*} [CommSemiring R] (c theta : ℝ)
    (blocks N Q m q width linearUnit fullMultiply lookupUnit formationUnit : ℕ)
    (data : Fin blocks → BlockData R c N m)
    (hc : 5 < c) (ht0 : 0 < theta) (ht1 : theta < 1/2) (hm : 0 < m)
    (hq : 1 ≤ q) (hwidth : Nat.ceil (2*theta*(m:ℝ)) ≤ width)
    (hgeometry : gridSide (Nat.ceil (c*(m:ℝ))) m ≤ N) :
    (blockScheduleCost c theta blocks N Q m q width linearUnit fullMultiply lookupUnit
      formationUnit data : ℝ) ≤
      blocks*(2*N*((4:ℝ)^m)*q*formationUnit +
        powerBound c theta N Q m q width linearUnit fullMultiply lookupUnit) := by
  unfold blockScheduleCost
  push_cast
  calc
    (∑ j : Fin blocks, (blockCost c theta N Q m q width linearUnit fullMultiply lookupUnit
      formationUnit (data j) : ℝ)) ≤
        ∑ _j : Fin blocks, (2*N*((4:ℝ)^m)*q*formationUnit +
          powerBound c theta N Q m q width linearUnit fullMultiply lookupUnit) :=
      Finset.sum_le_sum (fun j _ => blockCost_le c theta N Q m q width linearUnit
        fullMultiply lookupUnit formationUnit (data j) hc ht0 ht1 hm hq hwidth hgeometry)
    _ = _ := by simp; ring

/-- Raw product/query/encoder/formation monomials before inserting n-scales.
The fifth slot is available for a separate high-base encoder. Reusing the low
cache's degree-zero values executes no additional fifth-slot work. -/
def rawTerm (c theta : ℝ) (n N D q : ℝ) (i : Fin 6) : ℝ :=
  ![q*N^2*D^(-HighBoxEntropy.boxSaving c theta),
    n^2*q*D^(channelExponent theta),
    n^2*D^(highQueryExponent theta),
    q*N*D^(sourceExponent c theta),
    q*N*D^(tileExponent c-HighBoxEntropy.boxSaving c theta),
    q*N*D] i

/-- All local finite-control and rounded entropy factors are explicit. -/
def localFactor (c theta : ℝ) (m width : ℕ) : ℝ :=
  2 + 4*(encoderPolynomial (Nat.ceil (c*(m:ℝ))) : ℝ)*width*
      encoderTailFactor c theta m*gridRoundingFactor c +
    8*boxFactor c theta m + 5*(width:ℝ)^2*channelFactor theta m +
    4*channelFactor theta m

lemma localFactor_nonneg (c theta : ℝ) (m width : ℕ) :
    0 ≤ localFactor c theta m width := by
  unfold localFactor encoderTailFactor channelFactor gridRoundingFactor boxFactor
  positivity

lemma rawTerm_nonneg (c theta n N D q : ℝ)
    (_hn : 0 ≤ n) (hN : 0 ≤ N) (hD : 0 ≤ D) (hq : 0 ≤ q) (i : Fin 6) :
    0 ≤ rawTerm c theta n N D q i := by
  fin_cases i <;> norm_num [rawTerm] <;> positivity

/-- A precise arithmetic interface: linear/read/formation units cost at most A;
full multiplication costs at most q*A. A may contain the proved Toom q^epsilon
factor and bit-length polynomials. -/
theorem blockPower_le_raw (c theta : ℝ)
    (n N m q width linearUnit fullMultiply lookupUnit formationUnit : ℕ) (A : ℝ)
    (hA : 0 ≤ A)
    (hlin : (linearUnit:ℝ) ≤ A) (hlookup : (lookupUnit:ℝ) ≤ A)
    (hformation : (formationUnit:ℝ) ≤ A) (hfull : (fullMultiply:ℝ) ≤ (q:ℝ)*A) :
    2*N*((4:ℝ)^m)*q*formationUnit +
      powerBound c theta N (n^2) m q width linearUnit fullMultiply lookupUnit ≤
      A*localFactor c theta m width * ∑ i : Fin 6, rawTerm c theta n N ((4:ℝ)^m) q i := by
  let Cs := 4*(encoderPolynomial (Nat.ceil (c*(m:ℝ))) : ℝ)*width*
      encoderTailFactor c theta m*gridRoundingFactor c
  let Cb := 8*boxFactor c theta m
  let Cl := 5*(width:ℝ)^2*channelFactor theta m
  let Ch := 4*channelFactor theta m
  have hs : 0 ≤ Cs := by dsimp [Cs]; unfold encoderTailFactor channelFactor gridRoundingFactor; positivity
  have hb : 0 ≤ Cb := by dsimp [Cb]; unfold boxFactor; positivity
  have hl : 0 ≤ Cl := by dsimp [Cl]; unfold channelFactor; positivity
  have hh : 0 ≤ Ch := by dsimp [Ch]; unfold channelFactor; positivity
  have hf : (q:ℝ)*linearUnit+fullMultiply ≤ 2*(q:ℝ)*A := by
    have h := mul_le_mul_of_nonneg_left hlin (Nat.cast_nonneg q)
    linarith
  have h0 : 0 ≤ rawTerm c theta n N ((4:ℝ)^m) q 0 := rawTerm_nonneg _ _ _ _ _ _
    (Nat.cast_nonneg n) (Nat.cast_nonneg N) (by positivity) (Nat.cast_nonneg q) 0
  have h1 : 0 ≤ rawTerm c theta n N ((4:ℝ)^m) q 1 := rawTerm_nonneg _ _ _ _ _ _
    (Nat.cast_nonneg n) (Nat.cast_nonneg N) (by positivity) (Nat.cast_nonneg q) 1
  have h2 : 0 ≤ rawTerm c theta n N ((4:ℝ)^m) q 2 := rawTerm_nonneg _ _ _ _ _ _
    (Nat.cast_nonneg n) (Nat.cast_nonneg N) (by positivity) (Nat.cast_nonneg q) 2
  have h3 : 0 ≤ rawTerm c theta n N ((4:ℝ)^m) q 3 := rawTerm_nonneg _ _ _ _ _ _
    (Nat.cast_nonneg n) (Nat.cast_nonneg N) (by positivity) (Nat.cast_nonneg q) 3
  have h4 : 0 ≤ rawTerm c theta n N ((4:ℝ)^m) q 4 := rawTerm_nonneg _ _ _ _ _ _
    (Nat.cast_nonneg n) (Nat.cast_nonneg N) (by positivity) (Nat.cast_nonneg q) 4
  have h5 : 0 ≤ rawTerm c theta n N ((4:ℝ)^m) q 5 := rawTerm_nonneg _ _ _ _ _ _
    (Nat.cast_nonneg n) (Nat.cast_nonneg N) (by positivity) (Nat.cast_nonneg q) 5
  have hsum (i : Fin 6) : rawTerm c theta n N ((4:ℝ)^m) q i ≤
      ∑ j : Fin 6, rawTerm c theta n N ((4:ℝ)^m) q j :=
    Finset.single_le_sum (fun j _ => rawTerm_nonneg _ _ _ _ _ _
      (Nat.cast_nonneg n) (Nat.cast_nonneg N) (by positivity) (Nat.cast_nonneg q) j) (Finset.mem_univ i)
  have hd : 0 ≤ ((4:ℝ)^m) := by positivity
  have hc0 : 0 ≤ channelFactor theta m := by unfold channelFactor; positivity
  have hc1 : 0 ≤ boxFactor c theta m := by unfold boxFactor; positivity
  have hc2 : 0 ≤ encoderTailFactor c theta m := by unfold encoderTailFactor channelFactor; positivity
  have hc3 : 0 ≤ gridRoundingFactor c := by unfold gridRoundingFactor; positivity
  have hfirst : 2*N*((4:ℝ)^m)*q*formationUnit ≤ A*2*rawTerm c theta n N ((4:ℝ)^m) q 5 := by
    have h := mul_le_mul_of_nonneg_left hformation
      (show (0:ℝ) ≤ 2*N*((4:ℝ)^m)*q by positivity)
    simpa [rawTerm, mul_assoc, mul_left_comm, mul_comm] using h
  have hp : powerBound c theta N (n^2) m q width linearUnit fullMultiply lookupUnit ≤
      A*Cb*rawTerm c theta n N ((4:ℝ)^m) q 0 +
      A*Cl*rawTerm c theta n N ((4:ℝ)^m) q 1 +
      A*Ch*rawTerm c theta n N ((4:ℝ)^m) q 2 +
      A*Cs*rawTerm c theta n N ((4:ℝ)^m) q 3 := by
    have hbox := mul_le_mul_of_nonneg_left hf
      (show (0:ℝ) ≤ 4*(N:ℝ)^2*boxFactor c theta m*((4:ℝ)^m)^(-HighBoxEntropy.boxSaving c theta) by positivity)
    have hsource := mul_le_mul_of_nonneg_left hlin
      (show (0:ℝ) ≤ 4*(N:ℝ)*encoderPolynomial (Nat.ceil (c*(m:ℝ)))*q*width*
        encoderTailFactor c theta m*gridRoundingFactor c*((4:ℝ)^m)^(sourceExponent c theta) by positivity)
    have hlow := mul_le_mul_of_nonneg_left hlin
      (show (0:ℝ) ≤ (n:ℝ)^2*5*(width:ℝ)^2*q*channelFactor theta m*((4:ℝ)^m)^(channelExponent theta) by positivity)
    have hhigh := mul_le_mul_of_nonneg_left hlookup
      (show (0:ℝ) ≤ (n:ℝ)^2*4*channelFactor theta m*((4:ℝ)^m)^(highQueryExponent theta) by positivity)
    dsimp [powerBound, rawTerm, Cs, Cb, Cl, Ch]
    push_cast
    nlinarith only [hbox, hsource, hlow, hhigh]
  calc
    _ ≤ A*2*rawTerm c theta n N ((4:ℝ)^m) q 5 +
      (A*Cb*rawTerm c theta n N ((4:ℝ)^m) q 0 +
      A*Cl*rawTerm c theta n N ((4:ℝ)^m) q 1 +
      A*Ch*rawTerm c theta n N ((4:ℝ)^m) q 2 +
      A*Cs*rawTerm c theta n N ((4:ℝ)^m) q 3) := add_le_add hfirst hp
    _ ≤ A*2*(∑ i : Fin 6, rawTerm c theta n N ((4:ℝ)^m) q i) +
      (A*Cb*(∑ i : Fin 6, rawTerm c theta n N ((4:ℝ)^m) q i) +
      A*Cl*(∑ i : Fin 6, rawTerm c theta n N ((4:ℝ)^m) q i) +
      A*Ch*(∑ i : Fin 6, rawTerm c theta n N ((4:ℝ)^m) q i) +
      A*Cs*(∑ i : Fin 6, rawTerm c theta n N ((4:ℝ)^m) q i)) := by
      gcongr <;> exact hsum _
    _ = _ := by dsimp [localFactor, Cs, Cb, Cl, Ch]; ring

/-- Canonical entropy expressions agree with the analytic certificate. -/
theorem channelExponent_eq_q1 : channelExponent RealCertificate.theta = RealCertificate.q1 := by
  unfold channelExponent RealCertificate.q1 RealCertificate.entropy Real.binEntropy
  simp only [Real.log_inv]
  ring

theorem highQueryExponent_eq_q2 : highQueryExponent RealCertificate.theta = RealCertificate.q2 := by
  rw [RealCertificate.q2Identity, ← channelExponent_eq_q1]
  rfl

theorem sourceExponent_eq_Esource :
    sourceExponent RealCertificate.c RealCertificate.theta = RealCertificate.Esource := by
  unfold sourceExponent RealCertificate.Esource
  rw [tileExponent_eq_T, channelExponent_eq_q1]

theorem boxSaving_eq_G :
    HighBoxEntropy.boxSaving RealCertificate.c RealCertificate.theta = RealCertificate.G := by
  unfold HighBoxEntropy.boxSaving RealCertificate.G RealCertificate.entropy Real.binEntropy
  simp only [Real.log_inv]
  ring

def outerDegree (i : Fin 6) : ℕ := ![2,0,0,1,1,1] i
def cyclicDegree (i : Fin 6) : ℕ := ![1,1,0,1,1,1] i
def pairDegree (i : Fin 6) : ℕ := ![0,2,2,0,0,0] i
def innerExponent (i : Fin 6) : ℝ :=
  ![-RealCertificate.G, RealCertificate.q1, RealCertificate.q2,
    RealCertificate.Esource, RealCertificate.Ebox, 1] i

lemma rawTerm_canonical (n N D q : ℝ) (i : Fin 6) :
    rawTerm RealCertificate.c RealCertificate.theta n N D q i =
      n^(pairDegree i)*q^(cyclicDegree i)*N^(outerDegree i)*D^(innerExponent i) := by
  fin_cases i <;>
    simp [rawTerm, pairDegree, cyclicDegree, outerDegree, innerExponent,
      channelExponent_eq_q1, highQueryExponent_eq_q2, sourceExponent_eq_Esource,
      boxSaving_eq_G, tileExponent_eq_T, RealCertificate.Ebox, Real.rpow_one]

lemma innerExponent_nonneg (i : Fin 6) (hi : i ≠ 0) : 0 ≤ innerExponent i := by
  have ht := RealCertificate.TEnclosure
  have hg := RealCertificate.GEnclosure
  have hq := RealCertificate.q1Enclosure
  fin_cases i <;> simp_all [innerExponent, RealCertificate.Esource, RealCertificate.Ebox,
    RealCertificate.q2Identity, RealCertificate.theta] <;> linarith

/-- Fixed logarithmic factors obtained by inserting the actual padded D. -/
def innerConstant (R : ℕ) (i : Fin 6) : ℝ :=
  if i = 0 then 1 else (24*(16:ℝ)^R)^(innerExponent i)

def innerLogDegree (R k : ℕ) (i : Fin 6) : ℕ :=
  if i = 0 then 0 else Nat.ceil ((k*R:ℕ)*innerExponent i)

def phaseConstant (R : ℕ) (i : Fin 6) : ℝ :=
  32*((16:ℝ)^R)^(cyclicDegree i+outerDegree i)*4^(outerDegree i)*innerConstant R i

def phaseLogDegree (R k : ℕ) (i : Fin 6) : ℕ :=
  k+(k*R)*(cyclicDegree i+outerDegree i)+innerLogDegree R k i

lemma monomial_normalization (n : ℝ) (hn : 0 < n)
    (ell H CD a s w e : ℝ) (k r o p d : ℕ) :
    (16*ell^k*n^AsymptoticCosts.eta)*(2*n^(1-AsymptoticCosts.b))*n^p*(H*n^w)^r*
      (4*H*n^(1+s/2))^o*(CD*ell^d*n^(a*e)) =
    (32*H^(r+o)*4^o*CD)*ell^(k+d)*
      n^(AsymptoticCosts.eta+(1-AsymptoticCosts.b)+(p:ℝ)+(r:ℝ)*w+
        (o:ℝ)*(1+s/2)+a*e) := by
  have hn0 := hn.le
  simp only [mul_pow]
  rw [← Real.rpow_natCast n p, ← Real.rpow_mul_natCast hn0 w r,
    ← Real.rpow_mul_natCast hn0 (1+s/2) o]
  rw [pow_add H r o, pow_add ell k d]
  rw [show AsymptoticCosts.eta+(1-AsymptoticCosts.b)+(p:ℝ)+(r:ℝ)*w+
      (o:ℝ)*(1+s/2)+a*e =
    (((AsymptoticCosts.eta+(1-AsymptoticCosts.b))+(p:ℝ))+(w*(r:ℝ)))+
      ((1+s/2)*(o:ℝ))+a*e by ring]
  simp only [Real.rpow_add hn]
  ring

lemma degree_exponent_identity (s w : ℝ) (i : Fin 6) :
    AsymptoticCosts.eta+(1-AsymptoticCosts.b)+(pairDegree i:ℝ)+(cyclicDegree i:ℝ)*w+
      (outerDegree i:ℝ)*(1+s/2)+(AsymptoticCosts.b+s)*innerExponent i =
        phaseCostExponent s w i := by
  fin_cases i <;> norm_num [phaseCostExponent, pairDegree, cyclicDegree, outerDegree,
    innerExponent] <;> ring

/-- Actual D-powers: the box saving uses D's lower bound; all positive
powers use the padded upper bound. -/
theorem actual_inner_power_bound (R S n k : ℕ) (hn : 3 ≤ n)
    (call : PhaseCall R (primeScale n AsymptoticCosts.eta k)) (i : Fin 6) :
    (innerDimension n call S:ℝ)^(innerExponent i) ≤
      innerConstant R i*(Real.log (n:ℝ))^(innerLogDegree R k i)*
        (n:ℝ)^((AsymptoticCosts.b+foldExponent S call.factors.length)*innerExponent i) := by
  have hd := actual_inner_bounds R S n k hn call
  have hnpos : 0 < (n:ℝ) := by exact_mod_cast (show 0<n by omega)
  by_cases hi : i = 0
  · subst i
    have hg : 0 ≤ RealCertificate.G := by linarith [RealCertificate.GEnclosure.1]
    have h := Real.rpow_le_rpow_of_nonpos
      (Real.rpow_pos_of_pos hnpos (AsymptoticCosts.b+foldExponent S call.factors.length))
      hd.1 (neg_nonpos.mpr hg)
    simpa [innerExponent, innerConstant, innerLogDegree, ← Real.rpow_mul hnpos.le] using h
  · have h := poweredLogBound (k*R) (Nat.cast_nonneg (innerDimension n call S))
      (show 0 ≤ 24*(16:ℝ)^R by positivity) hnpos.le (one_le_log_nat n hn)
      (innerExponent_nonneg i hi) hd.2
    simpa only [innerConstant, innerLogDegree, if_neg hi] using h

/-- Insert all actual finite counts, including the candidate pool. There is
one q factor in full-vector preprocessing and LOW, and no q factor in HIGH reads. -/
theorem actual_rawTerm_bound (R S n k : ℕ) (hn : 3 ≤ n)
    (call : PhaseCall R (primeScale n AsymptoticCosts.eta k))
    (hs : 0 ≤ foldExponent S call.factors.length) (i : Fin 6) :
    ((PrimePool.candidates (primeScale n AsymptoticCosts.eta k)).card:ℝ)*
      (blockCount n AsymptoticCosts.b:ℝ)*
      rawTerm RealCertificate.c RealCertificate.theta n (outerSize call S n)
        (innerDimension n call S) (call.cyclic S) i ≤
      phaseConstant R i*(Real.log (n:ℝ))^(phaseLogDegree R k i)*
        (n:ℝ)^(phaseCostExponent (foldExponent S call.factors.length)
          (ringExponent S call.factors.length) i) := by
  have hnpos : 0 < (n:ℝ) := by exact_mod_cast (show 0<n by omega)
  have hp := actual_candidate_count n k hn
  have hb := blockCount_upper n AsymptoticCosts.b (by omega)
    (by norm_num [AsymptoticCosts.b, AlignedCertificate.b])
  have hq := (actual_cyclic_bounds R S n k hn call).2
  have hN := (actual_outer_bounds R S n k hn call hs).2
  have hD := actual_inner_power_bound R S n k hn call i
  rw [rawTerm_canonical]
  calc
    _ = ((PrimePool.candidates (primeScale n AsymptoticCosts.eta k)).card:ℝ)*
      (blockCount n AsymptoticCosts.b:ℝ)*(n:ℝ)^(pairDegree i)*
      (call.cyclic S:ℝ)^(cyclicDegree i)*(outerSize call S n:ℝ)^(outerDegree i)*
      (innerDimension n call S:ℝ)^(innerExponent i) := by ring
    _ ≤ (16*(Real.log (n:ℝ))^k*(n:ℝ)^AsymptoticCosts.eta)*
        (2*(n:ℝ)^(1-AsymptoticCosts.b))*(n:ℝ)^(pairDegree i)*
        (phaseOverhead R k n*(n:ℝ)^(ringExponent S call.factors.length))^(cyclicDegree i)*
        (4*phaseOverhead R k n*(n:ℝ)^(1+foldExponent S call.factors.length/2))^(outerDegree i)*
        (innerConstant R i*(Real.log (n:ℝ))^(innerLogDegree R k i)*
          (n:ℝ)^((AsymptoticCosts.b+foldExponent S call.factors.length)*innerExponent i)) := by
      have hpp : 0 ≤ phaseOverhead R k n := by
        have := phaseOverhead_ge_one R k n hn; linarith
      have hcc : 0 ≤ innerConstant R i := by unfold innerConstant; split_ifs <;> positivity
      gcongr
    _ = _ := by
      rw [monomial_normalization (n:ℝ) hnpos, degree_exponent_identity]
      unfold phaseOverhead phaseConstant phaseLogDegree
      rw [mul_pow, pow_mul, pow_add, pow_add]
      ring


namespace Overhead
open AsymptoticCosts
 theorem logarithmicIndex_bound (m K n : ℕ) (C a : ℝ)
    (hn : 3 ≤ n) (hC : 1 ≤ C)
    (hD : ((4:ℝ)^m) ≤ C * (Real.log (n:ℝ))^K * (n:ℝ)^a) :
    (m:ℝ) ≤ ((Real.log C + (K:ℝ) + a) / Real.log 4) * Real.log (n:ℝ) := by
  have hnpos : 0 < (n:ℝ) := by exact_mod_cast (show 0<n by omega)
  have hl : 1 ≤ Real.log (n:ℝ) := one_le_log_nat n hn
  have hlpos : 0 < Real.log (n:ℝ) := by linarith
  have hCpos : 0 < C := by linarith
  have hlogC : 0 ≤ Real.log C := Real.log_nonneg hC
  have hloglog : Real.log (Real.log (n:ℝ)) ≤ Real.log (n:ℝ) :=
    (Real.log_le_sub_one_of_pos hlpos).trans (by linarith)
  have hh := Real.log_le_log (by positivity : 0 < (4:ℝ)^m) hD
  rw [Real.log_pow, Real.log_mul (by positivity) ((Real.rpow_pos_of_pos hnpos a).ne'),
    Real.log_mul hCpos.ne' (by positivity), Real.log_pow, Real.log_rpow hnpos] at hh
  have h1 : Real.log C ≤ Real.log C * Real.log (n:ℝ) := by
    nlinarith
  have h2 : (K:ℝ)*Real.log (Real.log (n:ℝ)) ≤ (K:ℝ)*Real.log (n:ℝ) :=
    mul_le_mul_of_nonneg_left hloglog (Nat.cast_nonneg K)
  have hlog4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  apply (mul_le_mul_iff_left₀ hlog4).mp
  calc
    (m:ℝ)*Real.log 4 ≤ Real.log C + (K:ℝ)*Real.log (Real.log (n:ℝ)) + a*Real.log (n:ℝ) := hh
    _ ≤ (Real.log C + (K:ℝ) + a)*Real.log (n:ℝ) := by nlinarith
    _ = (((Real.log C + (K:ℝ) + a) / Real.log 4) * Real.log (n:ℝ))*Real.log 4 := by field_simp


def indexConstant (k : ℕ) : ℝ :=
  (Real.log (24*(16:ℝ)^AlignedCertificate.R) + (k*AlignedCertificate.R:ℕ) + b+u) /
    Real.log 4

theorem actual_innerPower_le_log (n k : ℕ) (hn : 3 ≤ n)
    (call : PhaseCall AlignedCertificate.R (primeScale n eta k)) :
    (innerPower n call AlignedCertificate.S : ℝ) ≤ indexConstant k * Real.log (n:ℝ) := by
  have hdim := (actual_inner_bounds AlignedCertificate.R AlignedCertificate.S n k hn call).2
  have hs := (aligned_fold_exponent_range call.factors.length).2
  have hpow : (n:ℝ)^(b+foldExponent AlignedCertificate.S call.factors.length) ≤ (n:ℝ)^(b+u) :=
    Real.rpow_le_rpow_of_exponent_le
      (show (1:ℝ)≤n by exact_mod_cast (show 1≤n by omega)) (by linarith)
  have hpos : 0 ≤ (24*(16:ℝ)^AlignedCertificate.R)*(Real.log (n:ℝ))^(k*AlignedCertificate.R) := by positivity
  have hdim' := hdim.trans (mul_le_mul_of_nonneg_left hpow hpos)
  rw [innerDimension_eq_power, Nat.cast_pow, Nat.cast_ofNat] at hdim'
  have hC : (1:ℝ) ≤ 24*(16:ℝ)^AlignedCertificate.R := by
    have hp : (1:ℝ) ≤ 16^AlignedCertificate.R := one_le_pow₀ (by norm_num)
    linarith
  simpa only [indexConstant, add_assoc] using logarithmicIndex_bound _ _ _ _ _ hn hC hdim'


theorem ceilLinear_add_one (a : ℝ) (m : ℕ) (ha : 0 ≤ a) :
    (Nat.ceil (a*(m:ℝ))+1:ℝ) ≤ (a+2)*((m:ℝ)+1) := by
  have h := (Nat.ceil_lt_add_one (mul_nonneg ha (Nat.cast_nonneg m))).le
  nlinarith

theorem encoderPolynomial_le (L : ℕ) :
    (encoderPolynomial L : ℝ) ≤ 200*((L:ℝ)+1)^2 := by
  simp only [encoderPolynomial, capFactor, Nat.cast_add, Nat.cast_mul, Nat.cast_ofNat,
    Nat.cast_one]
  nlinarith [sq_nonneg (L:ℝ)]

theorem roundedLength_add_one (c : ℝ) (m : ℕ) (hc : 0 ≤ c) :
    (Nat.ceil (c*(m:ℝ)):ℝ)+1 ≤ (c+2)*((m:ℝ)+1) := by
  simpa using ceilLinear_add_one c m hc

theorem channelFactor_le_linear (theta : ℝ) (m : ℕ) (ht : 0 ≤ theta) :
    channelFactor theta m ≤
      ((2*theta+2)*Real.exp (Real.log (1-theta)-Real.log theta))*((m:ℝ)+1) := by
  have h := ceilLinear_add_one (2*theta) m (by positivity)
  have h' := mul_le_mul_of_nonneg_right h
    (Real.exp_pos (Real.log (1-theta)-Real.log theta)).le
  simpa only [channelFactor, mul_assoc, mul_left_comm, mul_comm] using h'

theorem boxFactor_le_fifth (c theta : ℝ) (m : ℕ) (hc : 0 ≤ c) :
    boxFactor c theta m ≤
      (22*(c+2)^5*Real.exp (HighBoxEntropy.roundingConstant c theta))*((m:ℝ)+1)^5 := by
  let L := Nat.ceil (c*(m:ℝ))
  have hL := roundedLength_add_one c m hc
  have hL0 : 0 ≤ (L:ℝ) := Nat.cast_nonneg L
  have hL1 : (2*L+1:ℝ) ≤ 2*((L:ℝ)+1) := by linarith
  calc
    boxFactor c theta m = 11*(2*L+1:ℝ)*((L:ℝ)+1)^4*
        Real.exp (HighBoxEntropy.roundingConstant c theta) := rfl
    _ ≤ 11*(2*((L:ℝ)+1))*((L:ℝ)+1)^4*
        Real.exp (HighBoxEntropy.roundingConstant c theta) := by gcongr
    _ = 22*((L:ℝ)+1)^5*Real.exp (HighBoxEntropy.roundingConstant c theta) := by ring
    _ ≤ 22*((c+2)*((m:ℝ)+1))^5*Real.exp (HighBoxEntropy.roundingConstant c theta) := by gcongr
    _ = _ := by ring



def combinedFactor (c theta : ℝ) (m : ℕ) : ℝ :=
  let L := Nat.ceil (c*(m:ℝ))
  let width : ℝ := Nat.ceil (2*theta*(m:ℝ))+1
  2 + 4*(encoderPolynomial L:ℝ)*width*encoderTailFactor c theta m*gridRoundingFactor c +
    8*boxFactor c theta m + 5*width^2*channelFactor theta m + 4*channelFactor theta m

def combinedConstant (c theta : ℝ) : ℝ :=
  let W := 2*theta+2
  let B := W*Real.exp (Real.log (1-theta)-Real.log theta)
  let F := B/(1-4/(c-1))^2
  let J := 22*(c+2)^5*Real.exp (HighBoxEntropy.roundingConstant c theta)
  2 + 800*(c+2)^2*W*F*gridRoundingFactor c + 8*J + 5*W^2*B + 4*B

theorem combinedConstant_nonneg (c theta : ℝ) (hc : 0 ≤ c) (ht : 0 ≤ theta) :
    0 ≤ combinedConstant c theta := by
  unfold combinedConstant gridRoundingFactor
  positivity

theorem combinedFactor_le_fifth (c theta : ℝ) (m : ℕ)
    (hc : 0 ≤ c) (ht : 0 ≤ theta) :
    combinedFactor c theta m ≤ combinedConstant c theta * ((m:ℝ)+1)^5 := by
  let M : ℝ := (m:ℝ)+1
  let L := Nat.ceil (c*(m:ℝ))
  let width : ℝ := Nat.ceil (2*theta*(m:ℝ))+1
  let W := 2*theta+2
  let B := W*Real.exp (Real.log (1-theta)-Real.log theta)
  let F := B/(1-4/(c-1))^2
  let J := 22*(c+2)^5*Real.exp (HighBoxEntropy.roundingConstant c theta)
  have hM : 1 ≤ M := by dsimp [M]; exact le_add_of_nonneg_left (Nat.cast_nonneg m)
  have hM0 : 0 ≤ M := by linarith
  have hW : 0 ≤ W := by dsimp [W]; positivity
  have hB : 0 ≤ B := by dsimp [B]; positivity
  have hF : 0 ≤ F := by dsimp [F]; positivity
  have hJ : 0 ≤ J := by dsimp [J]; positivity
  have hgrid : 0 ≤ gridRoundingFactor c := by unfold gridRoundingFactor; positivity
  have henc : (encoderPolynomial L:ℝ) ≤ 200*(c+2)^2*M^2 := by
    calc
      (encoderPolynomial L:ℝ) ≤ 200*((L:ℝ)+1)^2 := encoderPolynomial_le L
      _ ≤ 200*((c+2)*M)^2 := by gcongr; exact roundedLength_add_one c m hc
      _ = _ := by ring
  have hwidth : width ≤ W*M := by
    exact ceilLinear_add_one (2*theta) m (by positivity)
  have hchannel : channelFactor theta m ≤ B*M := channelFactor_le_linear theta m ht
  have htail : encoderTailFactor c theta m ≤ F*M := by
    calc
      encoderTailFactor c theta m = channelFactor theta m / (1-4/(c-1))^2 := rfl
      _ ≤ (B*M)/(1-4/(c-1))^2 := by gcongr
      _ = F*M := by dsimp [F]; ring
  have hbox : boxFactor c theta m ≤ J*M^5 := boxFactor_le_fifth c theta m hc
  have htail0 : 0 ≤ encoderTailFactor c theta m := by
    unfold encoderTailFactor channelFactor; positivity
  have hwidth0 : 0 ≤ width := by dsimp [width]; positivity
  have hchannel0 : 0 ≤ channelFactor theta m := by unfold channelFactor; positivity
  have h14 : M^4 ≤ M^5 := pow_le_pow_right₀ hM (by omega)
  have h13 : M^3 ≤ M^5 := pow_le_pow_right₀ hM (by omega)
  have h11 : M ≤ M^5 := by simpa using pow_le_pow_right₀ hM (show 1≤5 by omega)
  have h10 : 1 ≤ M^5 := one_le_pow₀ hM
  have hsource : 4*(encoderPolynomial L:ℝ)*width*encoderTailFactor c theta m*gridRoundingFactor c ≤
      (800*(c+2)^2*W*F*gridRoundingFactor c)*M^5 := by
    calc
      _ ≤ 4*(200*(c+2)^2*M^2)*(W*M)*(F*M)*gridRoundingFactor c := by gcongr
      _ = (800*(c+2)^2*W*F*gridRoundingFactor c)*M^4 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h14 (by positivity)
  have hlow : 5*width^2*channelFactor theta m ≤ (5*W^2*B)*M^5 := by
    calc
      _ ≤ 5*(W*M)^2*(B*M) := by gcongr
      _ = (5*W^2*B)*M^3 := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h13 (by positivity)
  have hhigh : 4*channelFactor theta m ≤ (4*B)*M^5 := by
    calc
      _ ≤ 4*(B*M) := by gcongr
      _ = (4*B)*M := by ring
      _ ≤ _ := mul_le_mul_of_nonneg_left h11 (by positivity)
  have hbox' : 8*boxFactor c theta m ≤ (8*J)*M^5 := by nlinarith
  dsimp only [combinedFactor, combinedConstant]
  change 2 + 4*(encoderPolynomial L:ℝ)*width*encoderTailFactor c theta m*gridRoundingFactor c +
    8*boxFactor c theta m + 5*width^2*channelFactor theta m + 4*channelFactor theta m ≤ _
  change _ ≤ (2+800*(c+2)^2*W*F*gridRoundingFactor c+8*J+5*W^2*B+4*B)*M^5
  nlinarith



def indexMajor (k : ℕ) : ℝ := max (indexConstant k) 0 + 1

theorem actual_innerPower_add_one_le_log (n k : ℕ) (hn : 3 ≤ n)
    (call : PhaseCall AlignedCertificate.R (primeScale n eta k)) :
    (innerPower n call AlignedCertificate.S:ℝ)+1 ≤ indexMajor k * Real.log (n:ℝ) := by
  have h := actual_innerPower_le_log n k hn call
  have hl := one_le_log_nat n hn
  have hm : indexConstant k * Real.log (n:ℝ) ≤
      max (indexConstant k) 0 * Real.log (n:ℝ) :=
    mul_le_mul_of_nonneg_right (le_max_left _ _) (by linarith)
  unfold indexMajor
  nlinarith

theorem actual_roundedLength_le_log (n k : ℕ) (hn : 3 ≤ n)
    (call : PhaseCall AlignedCertificate.R (primeScale n eta k)) :
    (Nat.ceil (RealCertificate.c*(innerPower n call AlignedCertificate.S:ℝ)):ℝ)+1 ≤
      (RealCertificate.c+2)*indexMajor k*Real.log (n:ℝ) := by
  have hc : 0 ≤ RealCertificate.c := by norm_num [RealCertificate.c]
  calc
    _ ≤ (RealCertificate.c+2)*((innerPower n call AlignedCertificate.S:ℝ)+1) :=
      roundedLength_add_one _ _ hc
    _ ≤ (RealCertificate.c+2)*(indexMajor k*Real.log (n:ℝ)) :=
      mul_le_mul_of_nonneg_left (actual_innerPower_add_one_le_log n k hn call) (by positivity)
    _ = _ := by ring

theorem actual_width_le_log (n k : ℕ) (hn : 3 ≤ n)
    (call : PhaseCall AlignedCertificate.R (primeScale n eta k)) :
    (Nat.ceil (2*RealCertificate.theta*(innerPower n call AlignedCertificate.S:ℝ))+1:ℝ) ≤
      (2*RealCertificate.theta+2)*indexMajor k*Real.log (n:ℝ) := by
  have ht : 0 ≤ RealCertificate.theta := by norm_num [RealCertificate.theta]
  calc
    _ ≤ (2*RealCertificate.theta+2)*((innerPower n call AlignedCertificate.S:ℝ)+1) :=
      ceilLinear_add_one _ _ (by positivity)
    _ ≤ (2*RealCertificate.theta+2)*(indexMajor k*Real.log (n:ℝ)) :=
      mul_le_mul_of_nonneg_left (actual_innerPower_add_one_le_log n k hn call) (by positivity)
    _ = _ := by ring

def phaseCoefficientConstant (k : ℕ) : ℝ :=
  combinedConstant RealCertificate.c RealCertificate.theta * (indexMajor k)^5

theorem phaseCoefficientConstant_nonneg (k : ℕ) : 0 ≤ phaseCoefficientConstant k := by
  unfold phaseCoefficientConstant
  have hc : 0 ≤ RealCertificate.c := by norm_num [RealCertificate.c]
  have ht : 0 ≤ RealCertificate.theta := by norm_num [RealCertificate.theta]
  have hB := combinedConstant_nonneg _ _ hc ht
  have hM : 0 ≤ indexMajor k := by unfold indexMajor; positivity
  positivity

theorem actual_combinedFactor_le_polylog (n k : ℕ) (hn : 3 ≤ n)
    (call : PhaseCall AlignedCertificate.R (primeScale n eta k)) :
    combinedFactor RealCertificate.c RealCertificate.theta (innerPower n call AlignedCertificate.S) ≤
      phaseCoefficientConstant k * (Real.log (n:ℝ))^5 := by
  have hc : 0 ≤ RealCertificate.c := by norm_num [RealCertificate.c]
  have ht : 0 ≤ RealCertificate.theta := by norm_num [RealCertificate.theta]
  have hB := combinedConstant_nonneg _ _ hc ht
  calc
    _ ≤ combinedConstant RealCertificate.c RealCertificate.theta *
        ((innerPower n call AlignedCertificate.S:ℝ)+1)^5 :=
      combinedFactor_le_fifth _ _ _ hc ht
    _ ≤ combinedConstant RealCertificate.c RealCertificate.theta *
        (indexMajor k * Real.log (n:ℝ))^5 := by
      gcongr
      exact actual_innerPower_add_one_le_log n k hn call
    _ = _ := by unfold phaseCoefficientConstant; ring

end Overhead

/-- Canonical degree width: all coefficients through the rounded threshold. -/
def phaseWidth (m : ℕ) : ℕ := Nat.ceil (2*RealCertificate.theta*(m:ℝ))+1

theorem actual_localFactor_le_polylog (n k : ℕ) (hn : 3 ≤ n)
    (call : PhaseCall AlignedCertificate.R (primeScale n AsymptoticCosts.eta k)) :
    localFactor RealCertificate.c RealCertificate.theta (innerPower n call AlignedCertificate.S)
      (phaseWidth (innerPower n call AlignedCertificate.S)) ≤
      Overhead.phaseCoefficientConstant k*(Real.log (n:ℝ))^5 := by
  simpa [localFactor, Overhead.combinedFactor, phaseWidth] using
    Overhead.actual_combinedFactor_le_polylog n k hn call

/-- Exact finite block scheduling with the explicit six-term arithmetic interface. -/
theorem blockScheduleCost_le_raw {R : Type*} [CommSemiring R] (c theta : ℝ)
    (blocks n N m q width linearUnit fullMultiply lookupUnit formationUnit : ℕ)
    (data : Fin blocks → BlockData R c N m)
    (hc : 5 < c) (ht0 : 0 < theta) (ht1 : theta < 1/2) (hm : 0 < m)
    (hq : 1 ≤ q) (hwidth : Nat.ceil (2*theta*(m:ℝ)) ≤ width)
    (hgeometry : gridSide (Nat.ceil (c*(m:ℝ))) m ≤ N)
    (A : ℝ) (hA : 0 ≤ A)
    (hlin : (linearUnit:ℝ) ≤ A) (hlookup : (lookupUnit:ℝ) ≤ A)
    (hformation : (formationUnit:ℝ) ≤ A) (hfull : (fullMultiply:ℝ) ≤ (q:ℝ)*A) :
    (blockScheduleCost c theta blocks N (n^2) m q width linearUnit fullMultiply lookupUnit
      formationUnit data : ℝ) ≤
      A*localFactor c theta m width * ∑ i : Fin 6,
        (blocks:ℝ)*rawTerm c theta n N ((4:ℝ)^m) q i := by
  have h := blockScheduleCost_le c theta blocks N (n^2) m q width linearUnit fullMultiply
    lookupUnit formationUnit data hc ht0 ht1 hm hq hwidth hgeometry
  have hp := mul_le_mul_of_nonneg_left
    (blockPower_le_raw c theta n N m q width linearUnit fullMultiply lookupUnit formationUnit A
      hA hlin hlookup hformation hfull) (Nat.cast_nonneg blocks)
  apply h.trans (hp.trans_eq ?_)
  rw [← Finset.mul_sum]
  ring

lemma actual_innerPower_pos (n k : ℕ) (hn : 3 ≤ n)
    (call : PhaseCall AlignedCertificate.R (primeScale n AsymptoticCosts.eta k)) :
    0 < innerPower n call AlignedCertificate.S := by
  have hp := (actual_folded_bounds AlignedCertificate.R AlignedCertificate.S n k hn call).1
  have hnpos : 0 < (n:ℝ) := by exact_mod_cast (show 0<n by omega)
  have hd : 0 < call.folded AlignedCertificate.S := by
    exact_mod_cast lt_of_lt_of_le (Real.rpow_pos_of_pos hnpos _) hp
  have hh := blockSize_pos n AsymptoticCosts.b (by omega)
  apply Nat.clog_pos (by norm_num)
  change 1 < blockSize n AsymptoticCosts.b * (3*call.folded AlignedCertificate.S)
  nlinarith

lemma actual_cyclic_pos (n k : ℕ) (hn : 3 ≤ n)
    (call : PhaseCall AlignedCertificate.R (primeScale n AsymptoticCosts.eta k)) :
    1 ≤ call.cyclic AlignedCertificate.S := by
  have hp := (actual_cyclic_bounds AlignedCertificate.R AlignedCertificate.S n k hn call).1
  have hnpos : 0 < (n:ℝ) := by exact_mod_cast (show 0<n by omega)
  have h : 0 < call.cyclic AlignedCertificate.S := by
    exact_mod_cast lt_of_lt_of_le (Real.rpow_pos_of_pos hnpos _) hp
  omega

abbrev PhaseBlockData (R : Type*) (n k : ℕ)
    (call : PhaseCall AlignedCertificate.R (primeScale n AsymptoticCosts.eta k)) :=
  Fin (blockCount n AsymptoticCosts.b) →
    BlockData R RealCertificate.c (outerSize call AlignedCertificate.S n)
      (innerPower n call AlignedCertificate.S)

/-- This is the actual sum of counted schedules, with n² requests per block.
Window/mask products and controller restarts multiply this sum externally. -/
def actualPhaseCost {R : Type*} [CommSemiring R] (n k : ℕ)
    (call : PhaseCall AlignedCertificate.R (primeScale n AsymptoticCosts.eta k))
    (linearUnit fullMultiply lookupUnit formationUnit : ℕ) (data : PhaseBlockData R n k call) : ℕ :=
  let m := innerPower n call AlignedCertificate.S
  blockScheduleCost RealCertificate.c RealCertificate.theta (blockCount n AsymptoticCosts.b)
    (outerSize call AlignedCertificate.S n) (n^2) m (call.cyclic AlignedCertificate.S)
    (phaseWidth m) linearUnit fullMultiply lookupUnit formationUnit data

/-- The phase ledger before the final fixed-logarithm absorption. Its six
exponents are obtained from actual moduli, packed dimensions and finite counts. -/
def roundedPhaseLedger (n k j : ℕ) : ℝ :=
  ∑ i : Fin 6, phaseConstant AlignedCertificate.R i*
    (Real.log (n:ℝ))^(phaseLogDegree AlignedCertificate.R k i)*
    (n:ℝ)^(phaseCostExponent (foldExponent AlignedCertificate.S j)
      (ringExponent AlignedCertificate.S j) i)

/-- Pointwise composition for an actual candidate call. The candidate count
is charged exactly once, not once per coefficient query. -/
theorem actualPhaseCost_bound {R : Type*} [CommSemiring R] (n k : ℕ) (hn : 3 ≤ n)
    (call : PhaseCall AlignedCertificate.R (primeScale n AsymptoticCosts.eta k))
    (linearUnit fullMultiply lookupUnit formationUnit : ℕ) (data : PhaseBlockData R n k call)
    (hgeometry : gridSide (Nat.ceil (RealCertificate.c*(innerPower n call AlignedCertificate.S:ℝ)))
      (innerPower n call AlignedCertificate.S) ≤ outerSize call AlignedCertificate.S n)
    (A : ℝ) (hA : 0 ≤ A)
    (hlin : (linearUnit:ℝ) ≤ A) (hlookup : (lookupUnit:ℝ) ≤ A)
    (hformation : (formationUnit:ℝ) ≤ A)
    (hfull : (fullMultiply:ℝ) ≤ (call.cyclic AlignedCertificate.S:ℝ)*A) :
    ((PrimePool.candidates (primeScale n AsymptoticCosts.eta k)).card:ℝ)*
      (actualPhaseCost n k call linearUnit fullMultiply lookupUnit formationUnit data:ℝ) ≤
      A*Overhead.phaseCoefficientConstant k*(Real.log (n:ℝ))^5*
        roundedPhaseLedger n k call.factors.length := by
  let m := innerPower n call AlignedCertificate.S
  have hs := (aligned_fold_exponent_range call.factors.length).1
  have h := blockScheduleCost_le_raw RealCertificate.c RealCertificate.theta
    (blockCount n AsymptoticCosts.b) n (outerSize call AlignedCertificate.S n) m
    (call.cyclic AlignedCertificate.S) (phaseWidth m) linearUnit fullMultiply lookupUnit
    formationUnit data (by norm_num [RealCertificate.c]) (by norm_num [RealCertificate.theta])
    (by norm_num [RealCertificate.theta]) (actual_innerPower_pos n k hn call)
    (actual_cyclic_pos n k hn call) (by unfold phaseWidth; omega) hgeometry A hA hlin hlookup
    hformation hfull
  have h' := mul_le_mul_of_nonneg_left h
    (Nat.cast_nonneg (PrimePool.candidates (primeScale n AsymptoticCosts.eta k)).card)
  have hraw : ∑ i : Fin 6,
      ((PrimePool.candidates (primeScale n AsymptoticCosts.eta k)).card:ℝ)*
        (blockCount n AsymptoticCosts.b:ℝ)*
          rawTerm RealCertificate.c RealCertificate.theta n (outerSize call AlignedCertificate.S n)
            ((4:ℝ)^m) (call.cyclic AlignedCertificate.S) i ≤
      roundedPhaseLedger n k call.factors.length := by
    apply Finset.sum_le_sum
    intro i _
    simpa only [innerDimension_eq_power, Nat.cast_pow, Nat.cast_ofNat, m] using
      actual_rawTerm_bound AlignedCertificate.R AlignedCertificate.S n k hn call hs i
  have hlocal := actual_localFactor_le_polylog n k hn call
  have hnonneg : 0 ≤ roundedPhaseLedger n k call.factors.length := by
    unfold roundedPhaseLedger phaseConstant innerConstant
    apply Finset.sum_nonneg
    intro i _
    split_ifs <;> positivity
  calc
    _ ≤ A*localFactor RealCertificate.c RealCertificate.theta m (phaseWidth m)*
      ∑ i : Fin 6, ((PrimePool.candidates (primeScale n AsymptoticCosts.eta k)).card:ℝ)*
        (blockCount n AsymptoticCosts.b:ℝ)*
          rawTerm RealCertificate.c RealCertificate.theta n (outerSize call AlignedCertificate.S n)
            ((4:ℝ)^m) (call.cyclic AlignedCertificate.S) i := by
      change ((PrimePool.candidates (primeScale n AsymptoticCosts.eta k)).card:ℝ)*
        (blockScheduleCost RealCertificate.c RealCertificate.theta (blockCount n AsymptoticCosts.b)
          (outerSize call AlignedCertificate.S n) (n^2) m (call.cyclic AlignedCertificate.S)
          (phaseWidth m) linearUnit fullMultiply lookupUnit formationUnit data:ℝ) ≤ _
      apply h'.trans_eq
      simp only [← Finset.mul_sum]
      ring
    _ ≤ A*localFactor RealCertificate.c RealCertificate.theta m (phaseWidth m)*
      roundedPhaseLedger n k call.factors.length :=
        mul_le_mul_of_nonneg_left hraw (mul_nonneg hA (localFactor_nonneg _ _ _ _))
    _ ≤ _ := by
      have hh := mul_le_mul_of_nonneg_left hlocal hA
      simpa only [m, mul_assoc] using mul_le_mul_of_nonneg_right hh hnonneg

lemma phaseConstant_nonneg (R : ℕ) (i : Fin 6) : 0 ≤ phaseConstant R i := by
  unfold phaseConstant innerConstant
  split_ifs <;> positivity

lemma roundedPhaseLedger_nonneg (n k j : ℕ) (hn : 3 ≤ n) :
    0 ≤ roundedPhaseLedger n k j := by
  have hl : 0 ≤ Real.log (n:ℝ) := by linarith [one_le_log_nat n hn]
  apply Finset.sum_nonneg
  intro i _
  exact mul_nonneg (mul_nonneg (phaseConstant_nonneg _ _) (pow_nonneg hl _))
    (Real.rpow_nonneg (Nat.cast_nonneg n) _)

/-- All phases, including the unfilled start and final R-factor call. -/
def allPhaseLedger (n k : ℕ) : ℝ :=
  ∑ j : Fin (AlignedCertificate.R+1), roundedPhaseLedger n k j.val

lemma roundedPhaseLedger_le_all (n k j : ℕ) (hn : 3 ≤ n) (hj : j ≤ AlignedCertificate.R) :
    roundedPhaseLedger n k j ≤ allPhaseLedger n k := by
  let idx : Fin (AlignedCertificate.R+1) := ⟨j, by omega⟩
  change roundedPhaseLedger n k idx.val ≤
    ∑ a : Fin (AlignedCertificate.R+1), roundedPhaseLedger n k a.val
  exact Finset.single_le_sum (fun (a : Fin (AlignedCertificate.R+1)) _ =>
    roundedPhaseLedger_nonneg n k a.val hn) (Finset.mem_univ idx)

/-- Finite resource cancellation. Charging p candidate trials once per round
and bounding p times each actual cost cancels that p exactly. -/
theorem counted_batch_bound (count p rounds : ℕ) (cost : Fin count → ℕ) (C : ℝ)
    (hC : 0 ≤ C) (hcount : count ≤ rounds*p)
    (hcost : ∀ i, (p:ℝ)*(cost i:ℝ) ≤ C) :
    (∑ i, cost i:ℕ) ≤ (rounds:ℝ)*C := by
  by_cases hp : p = 0
  · subst p
    have hc : count = 0 := by omega
    subst count
    simp only [Finset.univ_eq_empty, Finset.sum_empty, Nat.cast_zero]
    positivity
  · have hpR : 0 < (p:ℝ) := by exact_mod_cast (show 0<p by omega)
    apply (mul_le_mul_iff_right₀ hpR).mp
    have hs : (p:ℝ)*((∑ i, cost i:ℕ):ℝ) ≤ (count:ℝ)*C := by
      push_cast
      rw [Finset.mul_sum]
      calc
        _ ≤ ∑ _i : Fin count, C := Finset.sum_le_sum (fun i _ => hcost i)
        _ = _ := by simp
    have hc : (count:ℝ)*C ≤ ((rounds:ℝ)*(p:ℝ))*C := by
      apply mul_le_mul_of_nonneg_right _ hC
      exact_mod_cast hcount
    calc
      (p:ℝ)*((∑ i, cost i:ℕ):ℝ) ≤ (count:ℝ)*C := hs
      _ ≤ ((rounds:ℝ)*(p:ℝ))*C := hc
      _ = _ := by ring

/-- A trace carries actual factor lists, not a freely chosen exponent. -/
structure PhaseBatch (R : Type*) (n k count : ℕ) where
  phases : Fin count → PhaseCall AlignedCertificate.R (primeScale n AsymptoticCosts.eta k)
  linearUnit : Fin count → ℕ
  fullMultiply : Fin count → ℕ
  lookupUnit : Fin count → ℕ
  formationUnit : Fin count → ℕ
  data : (i : Fin count) → PhaseBlockData R n k (phases i)

def phaseBatchCost {R : Type*} [CommSemiring R] {n k count : ℕ}
    (batch : PhaseBatch R n k count) : ℕ :=
  ∑ i, actualPhaseCost n k (batch.phases i) (batch.linearUnit i) (batch.fullMultiply i)
    (batch.lookupUnit i) (batch.formationUnit i) (batch.data i)

/-- The only controller premise is its proved finite call-count bound.
All costs on the left are the concrete block schedules above. -/
theorem phaseBatchCost_bound {R : Type*} [CommSemiring R] {n k count : ℕ}
    (batch : PhaseBatch R n k count) (hn : 3 ≤ n) (rounds : ℕ)
    (hcount : count ≤ rounds*(PrimePool.candidates (primeScale n AsymptoticCosts.eta k)).card)
    (hgeometry : ∀ i, gridSide (Nat.ceil (RealCertificate.c*
      (innerPower n (batch.phases i) AlignedCertificate.S:ℝ)))
      (innerPower n (batch.phases i) AlignedCertificate.S) ≤ outerSize (batch.phases i) AlignedCertificate.S n)
    (A : ℝ) (hA : 0 ≤ A)
    (hlin : ∀ i, (batch.linearUnit i:ℝ) ≤ A)
    (hlookup : ∀ i, (batch.lookupUnit i:ℝ) ≤ A)
    (hformation : ∀ i, (batch.formationUnit i:ℝ) ≤ A)
    (hfull : ∀ i, (batch.fullMultiply i:ℝ) ≤
      ((batch.phases i).cyclic AlignedCertificate.S:ℝ)*A) :
    (phaseBatchCost batch:ℝ) ≤ (rounds:ℝ)*A*Overhead.phaseCoefficientConstant k*
      (Real.log (n:ℝ))^5*allPhaseLedger n k := by
  have hl : 0 ≤ Real.log (n:ℝ) := by linarith [one_le_log_nat n hn]
  have hcoef : 0 ≤ A*Overhead.phaseCoefficientConstant k*(Real.log (n:ℝ))^5 := by
    exact mul_nonneg (mul_nonneg hA (Overhead.phaseCoefficientConstant_nonneg k)) (pow_nonneg hl 5)
  have hall : 0 ≤ allPhaseLedger n k := Finset.sum_nonneg
    (fun j _ => roundedPhaseLedger_nonneg n k j.val hn)
  have h := counted_batch_bound count (PrimePool.candidates (primeScale n AsymptoticCosts.eta k)).card
    rounds (fun i => actualPhaseCost n k (batch.phases i) (batch.linearUnit i) (batch.fullMultiply i)
      (batch.lookupUnit i) (batch.formationUnit i) (batch.data i))
    (A*Overhead.phaseCoefficientConstant k*(Real.log (n:ℝ))^5*allPhaseLedger n k)
    (mul_nonneg hcoef hall) hcount (by
      intro i
      apply (actualPhaseCost_bound n k hn (batch.phases i) (batch.linearUnit i)
        (batch.fullMultiply i) (batch.lookupUnit i) (batch.formationUnit i) (batch.data i)
        (hgeometry i) A hA (hlin i) (hlookup i) (hformation i) (hfull i)).trans
      exact mul_le_mul_of_nonneg_left
        (roundedPhaseLedger_le_all n k (batch.phases i).factors.length hn (batch.phases i).length_le) hcoef)
  simpa only [phaseBatchCost, mul_assoc] using h

/-- Fixed finite envelopes for the six logarithmic degrees and constants. -/
def ledgerLogDegree (k : ℕ) : ℕ := ∑ i : Fin 6, phaseLogDegree AlignedCertificate.R k i
def ledgerConstant : ℝ := ∑ i : Fin 6, phaseConstant AlignedCertificate.R i

lemma ledgerConstant_nonneg : 0 ≤ ledgerConstant :=
  Finset.sum_nonneg (fun i _ => phaseConstant_nonneg _ i)

lemma phaseConstant_le_ledger (i : Fin 6) : phaseConstant AlignedCertificate.R i ≤ ledgerConstant :=
  Finset.single_le_sum (fun j _ => phaseConstant_nonneg _ j) (Finset.mem_univ i)

lemma phaseLogDegree_le_ledger (k : ℕ) (i : Fin 6) :
    phaseLogDegree AlignedCertificate.R k i ≤ ledgerLogDegree k :=
  Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)

lemma actual_stage_exponent_identity (j : Fin (AlignedCertificate.R+1)) (i : Fin 6) :
    phaseCostExponent (foldExponent AlignedCertificate.S j.val)
      (ringExponent AlignedCertificate.S j.val) i = 3-AsymptoticCosts.stageSaving j i := by
  by_cases hj : j.val ≤ AlignedCertificate.S
  · have hs : foldExponent AlignedCertificate.S j.val = (j.val:ℝ)*AsymptoticCosts.eta := by
      simp only [foldExponent, Nat.min_eq_right hj]
    have hw : ringExponent AlignedCertificate.S j.val = 0 := by
      simp only [ringExponent, Nat.sub_eq_zero_of_le hj, Nat.cast_zero, zero_mul]
    rw [hs, hw, phaseCostExponent_scalar]
    simp only [AsymptoticCosts.stageSaving, if_pos hj]
  · have hs : foldExponent AlignedCertificate.S j.val = AsymptoticCosts.u := by
      rw [foldExponent_frozen _ _ (by omega)]
      exact AsymptoticCosts.stageRelations.2.1.symm
    rw [hs, phaseCostExponent_cyclic]
    simp only [AsymptoticCosts.stageSaving, if_neg hj, ringExponent]

/-- The only extra power is the explicitly certified arithmetic charge. -/
lemma charged_term_bound (n k : ℕ) (hn : 3 ≤ n)
    (j : Fin (AlignedCertificate.R+1)) (i : Fin 6) :
    (n:ℝ)^(ArithmeticSlack.extra:ℝ)*
      (phaseConstant AlignedCertificate.R i*(Real.log (n:ℝ))^(phaseLogDegree AlignedCertificate.R k i)*
        (n:ℝ)^(phaseCostExponent (foldExponent AlignedCertificate.S j.val)
          (ringExponent AlignedCertificate.S j.val) i)) ≤
      ledgerConstant*(Real.log (n:ℝ))^(ledgerLogDegree k)*
        AsymptoticCosts.roundedPower (3-ArithmeticSlack.chargedSaving j i) n := by
  have hnpos : 0 < (n:ℝ) := by exact_mod_cast (show 0<n by omega)
  have hlog := pow_le_pow_right₀ (one_le_log_nat n hn) (phaseLogDegree_le_ledger k i)
  have hp : (n:ℝ)^(ArithmeticSlack.extra:ℝ)*
      (n:ℝ)^(phaseCostExponent (foldExponent AlignedCertificate.S j.val)
        (ringExponent AlignedCertificate.S j.val) i) =
      (n:ℝ)^(3-ArithmeticSlack.chargedSaving j i) := by
    rw [← Real.rpow_add hnpos, actual_stage_exponent_identity]
    congr 1
    unfold ArithmeticSlack.chargedSaving
    ring
  calc
    _ = phaseConstant AlignedCertificate.R i*(Real.log (n:ℝ))^(phaseLogDegree AlignedCertificate.R k i)*
        ((n:ℝ)^(ArithmeticSlack.extra:ℝ)*
          (n:ℝ)^(phaseCostExponent (foldExponent AlignedCertificate.S j.val)
            (ringExponent AlignedCertificate.S j.val) i)) := by ring
    _ = phaseConstant AlignedCertificate.R i*(Real.log (n:ℝ))^(phaseLogDegree AlignedCertificate.R k i)*
        (n:ℝ)^(3-ArithmeticSlack.chargedSaving j i) := by rw [hp]
    _ ≤ ledgerConstant*(Real.log (n:ℝ))^(ledgerLogDegree k)*
        AsymptoticCosts.roundedPower (3-ArithmeticSlack.chargedSaving j i) n := by
      have hr := Nat.le_ceil ((n:ℝ)^(3-ArithmeticSlack.chargedSaving j i))
      have hc := phaseConstant_le_ledger i
      have hc0 := phaseConstant_nonneg AlignedCertificate.R i
      have hledger := ledgerConstant_nonneg
      have hl0 : 0 ≤ Real.log (n:ℝ) := by linarith [one_le_log_nat n hn]
      change _ ≤ ledgerConstant*(Real.log (n:ℝ))^(ledgerLogDegree k)*
        (Nat.ceil ((n:ℝ)^(3-ArithmeticSlack.chargedSaving j i)):ℝ)
      gcongr

/-- A finite sum over the actual stages fits the rounded charged ledger.
No algorithmic time bound is a premise of this algebraic conversion. -/
theorem charged_allPhaseLedger_bound (n k : ℕ) (hn : 3 ≤ n) :
    (n:ℝ)^(ArithmeticSlack.extra:ℝ)*allPhaseLedger n k ≤
      ledgerConstant*(Real.log (n:ℝ))^(ledgerLogDegree k)*
        ∑ j : Fin (AlignedCertificate.R+1), ∑ i : Fin 6,
          AsymptoticCosts.roundedPower (3-ArithmeticSlack.chargedSaving j i) n := by
  unfold allPhaseLedger roundedPhaseLedger
  simp only [Finset.mul_sum]
  apply Finset.sum_le_sum
  intro j _
  apply Finset.sum_le_sum
  intro i _
  exact charged_term_bound n k hn j i

/-- Explicit final primitive/restart composition. The left side is a sum of
real counted block schedules. The premises bound only primitive arithmetic and
controller rounds; tile geometry is supplied by the proved actual phase fit. -/
theorem phaseBatchCost_le_chargedSum {R : Type*} [CommSemiring R] {n k count : ℕ}
    (batch : PhaseBatch R n k count) (hn : 3 ≤ n) (rounds : ℕ)
    (hcount : count ≤ rounds*(PrimePool.candidates (primeScale n AsymptoticCosts.eta k)).card)
    (hgeometry : ∀ i, gridSide (Nat.ceil (RealCertificate.c*
      (innerPower n (batch.phases i) AlignedCertificate.S:ℝ)))
      (innerPower n (batch.phases i) AlignedCertificate.S) ≤ outerSize (batch.phases i) AlignedCertificate.S n)
    (A Cbit Cround : ℝ) (bitLog roundLog : ℕ) (hA : 0 ≤ A)
    (hCbit : 0 ≤ Cbit) (hCround : 0 ≤ Cround)
    (hlin : ∀ i, (batch.linearUnit i:ℝ) ≤ A)
    (hlookup : ∀ i, (batch.lookupUnit i:ℝ) ≤ A)
    (hformation : ∀ i, (batch.formationUnit i:ℝ) ≤ A)
    (hfull : ∀ i, (batch.fullMultiply i:ℝ) ≤
      ((batch.phases i).cyclic AlignedCertificate.S:ℝ)*A)
    (harithmetic : A ≤ Cbit*(Real.log (n:ℝ))^bitLog*(n:ℝ)^(ArithmeticSlack.extra:ℝ))
    (hrounds : (rounds:ℝ) ≤ Cround*(Real.log (n:ℝ))^roundLog) :
    (phaseBatchCost batch:ℝ) ≤
      (Cround*Cbit*Overhead.phaseCoefficientConstant k*ledgerConstant)*
        (Real.log (n:ℝ))^(roundLog+bitLog+5+ledgerLogDegree k)*
        ∑ j : Fin (AlignedCertificate.R+1), ∑ i : Fin 6,
          AsymptoticCosts.roundedPower (3-ArithmeticSlack.chargedSaving j i) n := by
  have h := phaseBatchCost_bound batch hn rounds hcount hgeometry A hA hlin hlookup hformation hfull
  have hl : 0 ≤ Real.log (n:ℝ) := by linarith [one_le_log_nat n hn]
  have hc := Overhead.phaseCoefficientConstant_nonneg k
  have hall : 0 ≤ allPhaseLedger n k := Finset.sum_nonneg
    (fun j _ => roundedPhaseLedger_nonneg n k j.val hn)
  have hsum := charged_allPhaseLedger_bound n k hn
  calc
    _ ≤ (rounds:ℝ)*A*Overhead.phaseCoefficientConstant k*(Real.log (n:ℝ))^5*allPhaseLedger n k := h
    _ ≤ (Cround*(Real.log (n:ℝ))^roundLog)*
        (Cbit*(Real.log (n:ℝ))^bitLog*(n:ℝ)^(ArithmeticSlack.extra:ℝ))*
        Overhead.phaseCoefficientConstant k*(Real.log (n:ℝ))^5*allPhaseLedger n k := by
      have hrA := mul_le_mul hrounds harithmetic hA
        (mul_nonneg hCround (pow_nonneg hl roundLog))
      exact mul_le_mul_of_nonneg_right
        (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right hrA hc) (pow_nonneg hl 5)) hall
    _ = (Cround*Cbit*Overhead.phaseCoefficientConstant k)*
        (Real.log (n:ℝ))^(roundLog+bitLog+5)*
        ((n:ℝ)^(ArithmeticSlack.extra:ℝ)*allPhaseLedger n k) := by
      simp only [pow_add]
      ring
    _ ≤ (Cround*Cbit*Overhead.phaseCoefficientConstant k)*
        (Real.log (n:ℝ))^(roundLog+bitLog+5)*
        (ledgerConstant*(Real.log (n:ℝ))^(ledgerLogDegree k)*
          ∑ j : Fin (AlignedCertificate.R+1), ∑ i : Fin 6,
            AsymptoticCosts.roundedPower (3-ArithmeticSlack.chargedSaving j i) n) :=
      mul_le_mul_of_nonneg_left hsum
        (mul_nonneg (mul_nonneg (mul_nonneg hCround hCbit) hc)
          (pow_nonneg hl (roundLog+bitLog+5)))
    _ = _ := by rw [pow_add]; ring

lemma chargedSum_nonneg (n : ℕ) :
    0 ≤ ∑ j : Fin (AlignedCertificate.R+1), ∑ i : Fin 6,
      AsymptoticCosts.roundedPower (3-ArithmeticSlack.chargedSaving j i) n := by
  apply Finset.sum_nonneg
  intro j _
  apply Finset.sum_nonneg
  intro i _
  exact Nat.cast_nonneg _

/-- The complete charged ledger also includes scans and incidence bookkeeping. -/
theorem chargedSum_le_chargedCost (n K : ℕ) (hn : 3 ≤ n) :
    (Real.log (n:ℝ))^K*
      (∑ j : Fin (AlignedCertificate.R+1), ∑ i : Fin 6,
        AsymptoticCosts.roundedPower (3-ArithmeticSlack.chargedSaving j i) n) ≤
      ArithmeticSlack.chargedCost K n := by
  let S := ∑ j : Fin (AlignedCertificate.R+1), ∑ i : Fin 6,
    AsymptoticCosts.roundedPower (3-ArithmeticSlack.chargedSaving j i) n
  let scan := AsymptoticCosts.roundedPower 2 n
  let book := AsymptoticCosts.roundedPower (3-(AsymptoticCosts.b-AsymptoticCosts.eta)) n
  have hs : 0 ≤ S := chargedSum_nonneg n
  have hscan : 0 ≤ scan := Nat.cast_nonneg _
  have hbook : 0 ≤ book := Nat.cast_nonneg _
  have hlog := one_le_log_nat n hn
  have hl0 : 0 ≤ Real.log (n:ℝ) := by linarith
  have hp : (Real.log (n:ℝ))^K ≤ (Real.log (n:ℝ))^(K+AlignedCertificate.R+10) :=
    pow_le_pow_right₀ hlog (by omega)
  have hc : (1:ℝ) ≤ ((AlignedCertificate.R:ℝ)+1)^2 := by
    have h : (0:ℝ) ≤ AlignedCertificate.R := Nat.cast_nonneg _
    nlinarith
  change (Real.log (n:ℝ))^K*S ≤
    ((AlignedCertificate.R:ℝ)+1)^2*(Real.log (n:ℝ))^(K+AlignedCertificate.R+10)*(scan+book+S)
  calc
    _ ≤ (Real.log (n:ℝ))^(K+AlignedCertificate.R+10)*S := mul_le_mul_of_nonneg_right hp hs
    _ ≤ (Real.log (n:ℝ))^(K+AlignedCertificate.R+10)*(scan+book+S) :=
      mul_le_mul_of_nonneg_left (by linarith) (pow_nonneg hl0 _)
    _ ≤ ((AlignedCertificate.R:ℝ)+1)^2*
        ((Real.log (n:ℝ))^(K+AlignedCertificate.R+10)*(scan+book+S)) := by
      exact le_mul_of_one_le_left (mul_nonneg (pow_nonneg hl0 _) (by linarith)) hc
    _ = _ := by ring

/-- This is a direct finite-counter bound by the complete charged ledger;
there is no premise asserting time domination by that ledger. -/
theorem phaseBatchCost_le_chargedCost {R : Type*} [CommSemiring R] {n k count : ℕ}
    (batch : PhaseBatch R n k count) (hn : 3 ≤ n) (rounds : ℕ)
    (hcount : count ≤ rounds*(PrimePool.candidates (primeScale n AsymptoticCosts.eta k)).card)
    (hgeometry : ∀ i, gridSide (Nat.ceil (RealCertificate.c*
      (innerPower n (batch.phases i) AlignedCertificate.S:ℝ)))
      (innerPower n (batch.phases i) AlignedCertificate.S) ≤ outerSize (batch.phases i) AlignedCertificate.S n)
    (A Cbit Cround : ℝ) (bitLog roundLog : ℕ) (hA : 0 ≤ A)
    (hCbit : 0 ≤ Cbit) (hCround : 0 ≤ Cround)
    (hlin : ∀ i, (batch.linearUnit i:ℝ) ≤ A)
    (hlookup : ∀ i, (batch.lookupUnit i:ℝ) ≤ A)
    (hformation : ∀ i, (batch.formationUnit i:ℝ) ≤ A)
    (hfull : ∀ i, (batch.fullMultiply i:ℝ) ≤
      ((batch.phases i).cyclic AlignedCertificate.S:ℝ)*A)
    (harithmetic : A ≤ Cbit*(Real.log (n:ℝ))^bitLog*(n:ℝ)^(ArithmeticSlack.extra:ℝ))
    (hrounds : (rounds:ℝ) ≤ Cround*(Real.log (n:ℝ))^roundLog) :
    (phaseBatchCost batch:ℝ) ≤
      (Cround*Cbit*Overhead.phaseCoefficientConstant k*ledgerConstant)*
        ArithmeticSlack.chargedCost (roundLog+bitLog+5+ledgerLogDegree k) n := by
  apply (phaseBatchCost_le_chargedSum batch hn rounds hcount hgeometry A Cbit Cround bitLog
    roundLog hA hCbit hCround hlin hlookup hformation hfull harithmetic hrounds).trans
  have hp := chargedSum_le_chargedCost n (roundLog+bitLog+5+ledgerLogDegree k) hn
  have hc : 0 ≤ Cround*Cbit*Overhead.phaseCoefficientConstant k*ledgerConstant :=
    mul_nonneg (mul_nonneg (mul_nonneg hCround hCbit)
      (Overhead.phaseCoefficientConstant_nonneg k)) ledgerConstant_nonneg
  simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hp hc

/-- The concrete primitive arithmetic interface for one counted batch. -/
structure PrimitiveBudget {R : Type*} {n k count : ℕ} (batch : PhaseBatch R n k count) (A : ℝ) : Prop where
  nonneg : 0 ≤ A
  linear : ∀ i, (batch.linearUnit i:ℝ) ≤ A
  lookup : ∀ i, (batch.lookupUnit i:ℝ) ≤ A
  formation : ∀ i, (batch.formationUnit i:ℝ) ≤ A
  fullMultiply : ∀ i, (batch.fullMultiply i:ℝ) ≤
    ((batch.phases i).cyclic AlignedCertificate.S:ℝ)*A

lemma chargedCost_nonneg (K n : ℕ) (hn : 3 ≤ n) : 0 ≤ ArithmeticSlack.chargedCost K n := by
  have hl : 0 ≤ Real.log (n:ℝ) := by linarith [one_le_log_nat n hn]
  unfold ArithmeticSlack.chargedCost
  exact mul_nonneg
    (mul_nonneg (sq_nonneg _) (pow_nonneg hl _))
    (add_nonneg (add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) (chargedSum_nonneg n))

/-- Asymptotics of the actual counted schedules. Candidate-uniform original
grid geometry is proved by PhaseGeometry, rather than assumed here. The only
asymptotic premises concern precise primitive arithmetic and controller rounds. -/
theorem phaseBatchCost_bigO {R : Type*} [CommSemiring R]
    (k : ℕ) (count rounds : ℕ → ℕ) (batch : (n : ℕ) → PhaseBatch R n k (count n))
    (A : ℕ → ℝ) (Cbit Cround : ℝ) (bitLog roundLog : ℕ)
    (hCbit : 0 ≤ Cbit) (hCround : 0 ≤ Cround)
    (hresources : ∀ᶠ n : ℕ in atTop,
      count n ≤ rounds n*(PrimePool.candidates (primeScale n AsymptoticCosts.eta k)).card ∧
      PrimitiveBudget (batch n) (A n) ∧
      A n ≤ Cbit*(Real.log (n:ℝ))^bitLog*(n:ℝ)^(ArithmeticSlack.extra:ℝ) ∧
      (rounds n:ℝ) ≤ Cround*(Real.log (n:ℝ))^roundLog) :
    (fun n => (phaseBatchCost (batch n):ℝ)) =O[atTop]
      (fun n : ℕ => (n:ℝ)^(299294792/100000000:ℝ)) := by
  let K := roundLog+bitLog+5+ledgerLogDegree k
  let C := Cround*Cbit*Overhead.phaseCoefficientConstant k*ledgerConstant
  have hdom : ∀ᶠ n : ℕ in atTop,
      (phaseBatchCost (batch n):ℝ) ≤ C*ArithmeticSlack.chargedCost K n := by
    filter_upwards [hresources, all_actual_candidate_tiles_fit k,
      eventually_ge_atTop (3:ℕ)] with n hr hfit hn
    rcases hr with ⟨hcount, hp, ha, hrounds⟩
    apply phaseBatchCost_le_chargedCost (batch n) hn (rounds n) hcount
      (fun i => hfit ((batch n).phases i)) (A n) Cbit Cround bitLog roundLog
      hp.nonneg hCbit hCround hp.linear hp.lookup hp.formation hp.fullMultiply ha hrounds
  have hO : (fun n => (phaseBatchCost (batch n):ℝ)) =O[atTop]
      ArithmeticSlack.chargedCost K := by
    apply IsBigO.of_bound C
    filter_upwards [hdom, eventually_ge_atTop (3:ℕ)] with n hb hn
    simpa only [Real.norm_of_nonneg (Nat.cast_nonneg (phaseBatchCost (batch n))),
      Real.norm_of_nonneg (chargedCost_nonneg K n hn)] using hb
  exact hO.trans (ArithmeticSlack.chargedCostBigO K)

/-- The call-count premise of the batch bound is supplied by the actual
composite controller, independently of oracle correctness or its run time. -/
theorem actual_controller_call_count {X V Pair : Type*} [DecidableEq Pair]
    (O : CompositeAlgorithm.CountOracle X) (A : CompositeCertification.Instance X V)
    (pair : X → Pair) (lam depth stages n k : ℕ) (pool : Finset ℕ) (initial : Finset X)
    (hpool : pool ⊆ PrimePool.candidates (primeScale n AsymptoticCosts.eta k)) :
    (CompositeAlgorithm.solve O A pair lam depth stages pool initial).calls.length ≤
      (stages*(depth+1))*(PrimePool.candidates (primeScale n AsymptoticCosts.eta k)).card := by
  exact (CompositeAlgorithm.restarts_calls_bound O A pair lam depth pool stages initial ∅).trans
    (Nat.mul_le_mul_left (stages*(depth+1)) (Finset.card_le_card hpool))

/-- Recorded selector/table visits and original-integer tests remain distinct
from oracle calls. Their coefficient arithmetic cost is explicit. -/
def controllerCost {X Pair : Type*} (out : CompositeAlgorithm.Result X Pair) (unit : ℕ) : ℕ :=
  (out.bookkeeping + CompositeAlgorithm.tableCells out.calls + out.originalSumTests)*unit

/-- Resource composition for the exact returned controller. The final-scan
budget is a genuine original-sum test bound, not a time-ledger hypothesis. -/
theorem actual_controller_cost_le {X V Pair : Type*} [DecidableEq Pair]
    (O : CompositeAlgorithm.CountOracle X) (A : CompositeCertification.Instance X V)
    (pair : X → Pair) (lam depth stages : ℕ) (pool : Finset ℕ) (initial : Finset X)
    (unit scanBudget : ℕ)
    (hscan : (CompositeAlgorithm.solve O A pair lam depth stages pool initial).originalSumTests ≤ scanBudget) :
    controllerCost (CompositeAlgorithm.solve O A pair lam depth stages pool initial) unit ≤
      (17*(stages*(depth+1))*(pool.card+1)*(initial.card+1)+scanBudget)*unit := by
  have hb := CompositeAlgorithm.restarts_bookkeeping_bound O A pair lam depth pool stages initial ∅
  have ht := CompositeAlgorithm.restarts_tableCells_bound O A pair lam depth pool stages initial ∅
  have ht' : stages*(depth+1)*pool.card*initial.card ≤
      stages*(depth+1)*(pool.card+1)*(initial.card+1) := by gcongr <;> omega
  have hvisits : (CompositeAlgorithm.solve O A pair lam depth stages pool initial).bookkeeping +
      CompositeAlgorithm.tableCells (CompositeAlgorithm.solve O A pair lam depth stages pool initial).calls +
      (CompositeAlgorithm.solve O A pair lam depth stages pool initial).originalSumTests ≤
      17*(stages*(depth+1))*(pool.card+1)*(initial.card+1)+scanBudget := by
    change (CompositeAlgorithm.restarts O A pair lam depth pool stages initial ∅).bookkeeping +
      CompositeAlgorithm.tableCells (CompositeAlgorithm.restarts O A pair lam depth pool stages initial ∅).calls +
      (CompositeAlgorithm.solve O A pair lam depth stages pool initial).originalSumTests ≤ _
    nlinarith [ht.trans ht']
  exact Nat.mul_le_mul_right unit hvisits

/-- Candidate ceiling and the empty-pool unit are charged together. -/
lemma candidate_card_add_one_le (n k : ℕ) (hn : 3 ≤ n) :
    ((PrimePool.candidates (primeScale n AsymptoticCosts.eta k)).card+1:ℝ) ≤
      17*(Real.log (n:ℝ))^k*(n:ℝ)^AsymptoticCosts.eta := by
  have hp := actual_candidate_count n k hn
  have he0 := AsymptoticCosts.stageRelations.1
  have hlog := one_le_pow₀ (one_le_log_nat n hn) (n := k)
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (show 1≤n by omega)
  have hx := Real.one_le_rpow hn1 he0
  have hunit : (1:ℝ) ≤ (Real.log (n:ℝ))^k*(n:ℝ)^AsymptoticCosts.eta :=
    one_le_mul_of_one_le_of_one_le hlog hx
  nlinarith

/-- The incidence list can retain all signed windows, even when several
incidences have the same folded query answer. -/
lemma incidence_card_add_one_le (n windows : ℕ) (hn : 3 ≤ n) (incidences : ℕ)
    (hinc : incidences ≤ windows*queryCount n AsymptoticCosts.b) :
    (incidences+1:ℝ) ≤ (2*(windows:ℝ)+1)*(n:ℝ)^(3-AsymptoticCosts.b) := by
  have hq := queryCount_upper n AsymptoticCosts.b (by omega)
    (by norm_num [AsymptoticCosts.b, AlignedCertificate.b])
  have hn1 : (1:ℝ) ≤ n := by exact_mod_cast (show 1≤n by omega)
  have hexp : (0:ℝ) ≤ 3-AsymptoticCosts.b := by norm_num [AsymptoticCosts.b, AlignedCertificate.b]
  have hone := Real.one_le_rpow hn1 hexp
  have hincR : (incidences:ℝ) ≤ (windows:ℝ)*(queryCount n AsymptoticCosts.b:ℝ) := by exact_mod_cast hinc
  have hinc' := hincR.trans (mul_le_mul_of_nonneg_left hq (Nat.cast_nonneg windows))
  nlinarith

/-- Actual selector/table work has the canonical unexpanded bookkeeping
power. The final scan contributes n² original-integer tests. -/
theorem actual_controller_power_bound {X V Pair : Type*} [DecidableEq Pair]
    (O : CompositeAlgorithm.CountOracle X) (A : CompositeCertification.Instance X V)
    (pair : X → Pair) (lam depth stages n k windows unit : ℕ)
    (pool : Finset ℕ) (initial : Finset X) (hn : 3 ≤ n)
    (hpool : pool ⊆ PrimePool.candidates (primeScale n AsymptoticCosts.eta k))
    (hinc : initial.card ≤ windows*queryCount n AsymptoticCosts.b)
    (hscan : (CompositeAlgorithm.solve O A pair lam depth stages pool initial).originalSumTests ≤ n^2) :
    (controllerCost (CompositeAlgorithm.solve O A pair lam depth stages pool initial) unit:ℝ) ≤
      (289*(stages*(depth+1):ℕ)*(2*(windows:ℝ)+1)*(Real.log (n:ℝ))^k*
        (n:ℝ)^(3-(AsymptoticCosts.b-AsymptoticCosts.eta)) + (n:ℝ)^2)*(unit:ℝ) := by
  have hf := actual_controller_cost_le O A pair lam depth stages pool initial unit (n^2) hscan
  have hfR : (controllerCost (CompositeAlgorithm.solve O A pair lam depth stages pool initial) unit:ℝ) ≤
      (17*(stages*(depth+1):ℕ)*(pool.card+1:ℝ)*(initial.card+1:ℝ)+(n:ℝ)^2)*(unit:ℝ) := by
    exact_mod_cast hf
  have hp : (pool.card+1:ℝ) ≤ 17*(Real.log (n:ℝ))^k*(n:ℝ)^AsymptoticCosts.eta := by
    apply le_trans _ (candidate_card_add_one_le n k hn)
    exact_mod_cast Nat.add_le_add_right (Finset.card_le_card hpool) 1
  have hi := incidence_card_add_one_le n windows hn initial.card hinc
  have hnpos : 0 < (n:ℝ) := by exact_mod_cast (show 0<n by omega)
  calc
    _ ≤ (17*(stages*(depth+1):ℕ)*(pool.card+1:ℝ)*(initial.card+1:ℝ)+(n:ℝ)^2)*(unit:ℝ) := hfR
    _ ≤ (17*(stages*(depth+1):ℕ)*(17*(Real.log (n:ℝ))^k*(n:ℝ)^AsymptoticCosts.eta)*
        ((2*(windows:ℝ)+1)*(n:ℝ)^(3-AsymptoticCosts.b))+(n:ℝ)^2)*(unit:ℝ) := by gcongr
    _ = _ := by
      rw [show 3-(AsymptoticCosts.b-AsymptoticCosts.eta) = AsymptoticCosts.eta+(3-AsymptoticCosts.b) by ring,
        Real.rpow_add hnpos]
      ring

lemma bookScan_le_chargedCost (n K : ℕ) (hn : 3 ≤ n) :
    (Real.log (n:ℝ))^K*((n:ℝ)^2+
      (n:ℝ)^(3-(AsymptoticCosts.b-AsymptoticCosts.eta))) ≤ ArithmeticSlack.chargedCost K n := by
  let scan := AsymptoticCosts.roundedPower 2 n
  let book := AsymptoticCosts.roundedPower (3-(AsymptoticCosts.b-AsymptoticCosts.eta)) n
  let S := ∑ j : Fin (AlignedCertificate.R+1), ∑ i : Fin 6,
    AsymptoticCosts.roundedPower (3-ArithmeticSlack.chargedSaving j i) n
  have hs : 0 ≤ S := chargedSum_nonneg n
  have hscan : 0 ≤ scan := Nat.cast_nonneg _
  have hbook : 0 ≤ book := Nat.cast_nonneg _
  have hlog := one_le_log_nat n hn
  have hl0 : 0 ≤ Real.log (n:ℝ) := by linarith
  have hsc : (n:ℝ)^2 ≤ scan := by
    simpa only [scan, AsymptoticCosts.roundedPower, Real.rpow_two] using Nat.le_ceil ((n:ℝ)^(2:ℝ))
  have hbk : (n:ℝ)^(3-(AsymptoticCosts.b-AsymptoticCosts.eta)) ≤ book := Nat.le_ceil _
  have hp : (Real.log (n:ℝ))^K ≤ (Real.log (n:ℝ))^(K+AlignedCertificate.R+10) :=
    pow_le_pow_right₀ hlog (by omega)
  have hc : (1:ℝ) ≤ ((AlignedCertificate.R:ℝ)+1)^2 := by
    have h : (0:ℝ) ≤ AlignedCertificate.R := Nat.cast_nonneg _
    nlinarith
  change _ ≤ ((AlignedCertificate.R:ℝ)+1)^2*(Real.log (n:ℝ))^(K+AlignedCertificate.R+10)*(scan+book+S)
  calc
    _ ≤ (Real.log (n:ℝ))^K*(scan+book+S) :=
      mul_le_mul_of_nonneg_left (by linarith) (pow_nonneg hl0 _)
    _ ≤ (Real.log (n:ℝ))^(K+AlignedCertificate.R+10)*(scan+book+S) :=
      mul_le_mul_of_nonneg_right hp (by linarith)
    _ ≤ ((AlignedCertificate.R:ℝ)+1)^2*
        ((Real.log (n:ℝ))^(K+AlignedCertificate.R+10)*(scan+book+S)) :=
      le_mul_of_one_le_left (mul_nonneg (pow_nonneg hl0 _) (by linarith)) hc
    _ = _ := by ring

/-- The controller's real recorded counters, including all retained
incidences and final tests, fit the complete charged ledger. -/
theorem actual_controller_le_chargedCost {X V Pair : Type*} [DecidableEq Pair]
    (O : CompositeAlgorithm.CountOracle X) (A : CompositeCertification.Instance X V)
    (pair : X → Pair) (lam depth stages n k windows unit : ℕ)
    (pool : Finset ℕ) (initial : Finset X) (hn : 3 ≤ n)
    (hpool : pool ⊆ PrimePool.candidates (primeScale n AsymptoticCosts.eta k))
    (hinc : initial.card ≤ windows*queryCount n AsymptoticCosts.b)
    (hscan : (CompositeAlgorithm.solve O A pair lam depth stages pool initial).originalSumTests ≤ n^2)
    (Cunit Cround : ℝ) (unitLog roundLog : ℕ) (hCunit : 0 ≤ Cunit) (hCround : 0 ≤ Cround)
    (hunit : (unit:ℝ) ≤ Cunit*(Real.log (n:ℝ))^unitLog)
    (hrounds : (stages*(depth+1):ℕ) ≤ Cround*(Real.log (n:ℝ))^roundLog) :
    (controllerCost (CompositeAlgorithm.solve O A pair lam depth stages pool initial) unit:ℝ) ≤
      (Cunit*(289*Cround*(2*(windows:ℝ)+1)+1))*
        ArithmeticSlack.chargedCost (roundLog+k+unitLog) n := by
  have h := actual_controller_power_bound O A pair lam depth stages n k windows unit pool initial hn hpool hinc hscan
  let logn := Real.log (n:ℝ)
  let exponent := 3-(AsymptoticCosts.b-AsymptoticCosts.eta)
  let K := roundLog+k+unitLog
  let c := 289*Cround*(2*(windows:ℝ)+1)
  have hl : 0 ≤ logn := by dsimp [logn]; linarith [one_le_log_nat n hn]
  have hc : 0 ≤ c := by dsimp [c]; positivity
  have hpow : 0 ≤ (n:ℝ)^exponent := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hbig := bookScan_le_chargedCost n K hn
  have huLog : logn^unitLog ≤ logn^K := pow_le_pow_right₀ (one_le_log_nat n hn) (by dsimp [K]; omega)
  have hcommon : Cunit*c*logn^K*(n:ℝ)^exponent + Cunit*logn^unitLog*(n:ℝ)^2 ≤
      Cunit*(c+1)*logn^K*((n:ℝ)^2+(n:ℝ)^exponent) := by
    have hscanLog := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_left huLog hCunit) (sq_nonneg (n:ℝ))
    have hcoeff : Cunit*c ≤ Cunit*(c+1) := by nlinarith
    have hcoeff' : Cunit ≤ Cunit*(c+1) := by nlinarith
    have hb := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcoeff (pow_nonneg hl K)) hpow
    have hs := mul_le_mul_of_nonneg_right
      (mul_le_mul_of_nonneg_right hcoeff' (pow_nonneg hl K)) (sq_nonneg (n:ℝ))
    nlinarith
  calc
    _ ≤ (289*(stages*(depth+1):ℕ)*(2*(windows:ℝ)+1)*logn^k*(n:ℝ)^exponent+(n:ℝ)^2)*(unit:ℝ) := h
    _ ≤ (289*(Cround*logn^roundLog)*(2*(windows:ℝ)+1)*logn^k*(n:ℝ)^exponent+
        (n:ℝ)^2)*(Cunit*logn^unitLog) := by gcongr
    _ = Cunit*c*logn^K*(n:ℝ)^exponent + Cunit*logn^unitLog*(n:ℝ)^2 := by
      dsimp [c, K]
      simp only [pow_add]
      ring
    _ ≤ Cunit*(c+1)*logn^K*((n:ℝ)^2+(n:ℝ)^exponent) := hcommon
    _ ≤ Cunit*(c+1)*ArithmeticSlack.chargedCost K n := by
      simpa only [mul_assoc] using mul_le_mul_of_nonneg_left hbig (mul_nonneg hCunit (by linarith))

lemma chargedCost_mono (n K₁ K₂ : ℕ) (hn : 3 ≤ n) (hK : K₁ ≤ K₂) :
    ArithmeticSlack.chargedCost K₁ n ≤ ArithmeticSlack.chargedCost K₂ n := by
  have hl := one_le_log_nat n hn
  have hp := pow_le_pow_right₀ hl (Nat.add_le_add_right (Nat.add_le_add_right hK AlignedCertificate.R) 10)
  have hs := chargedSum_nonneg n
  unfold ArithmeticSlack.chargedCost
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hp (sq_nonneg _))
    (add_nonneg (add_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg _)) hs)

/-- Dense writing of the three n by n answer/count arrays. -/
def answerWriteCost (n unit : ℕ) : ℕ := ∑ _a : Fin 3, ∑ _i : Fin n, ∑ _j : Fin n, unit

@[simp] theorem answerWriteCost_eq (n unit : ℕ) : answerWriteCost n unit = 3*n^2*unit := by
  simp [answerWriteCost, pow_two, mul_assoc]

lemma answerWriteCost_le_chargedCost (n unit unitLog : ℕ) (hn : 3 ≤ n)
    (Cunit : ℝ) (hCunit : 0 ≤ Cunit) (hunit : (unit:ℝ) ≤ Cunit*(Real.log (n:ℝ))^unitLog) :
    (answerWriteCost n unit:ℝ) ≤ 3*Cunit*ArithmeticSlack.chargedCost unitLog n := by
  have hl : 0 ≤ Real.log (n:ℝ) := by linarith [one_le_log_nat n hn]
  have hb := bookScan_le_chargedCost n unitLog hn
  have hpow : 0 ≤ (n:ℝ)^(3-(AsymptoticCosts.b-AsymptoticCosts.eta)) := Real.rpow_nonneg (Nat.cast_nonneg n) _
  have hbase : (Real.log (n:ℝ))^unitLog*(n:ℝ)^2 ≤ ArithmeticSlack.chargedCost unitLog n := by
    apply le_trans _ hb
    exact mul_le_mul_of_nonneg_left (le_add_of_nonneg_right hpow) (pow_nonneg hl _)
  calc
    _ = 3*(n:ℝ)^2*unit := by rw [answerWriteCost_eq]; push_cast; rfl
    _ ≤ 3*(n:ℝ)^2*(Cunit*(Real.log (n:ℝ))^unitLog) :=
      mul_le_mul_of_nonneg_left hunit (by positivity)
    _ = 3*Cunit*((Real.log (n:ℝ))^unitLog*(n:ℝ)^2) := by ring
    _ ≤ _ := mul_le_mul_of_nonneg_left hbase (by positivity)

/-- Total counted oracle preparation/query work, actual controller visits,
and dense answer writes. -/
def completeCounter {R X Pair : Type*} [CommSemiring R] {n k count : ℕ}
    (batch : PhaseBatch R n k count) (out : CompositeAlgorithm.Result X Pair) (unit : ℕ) : ℕ :=
  phaseBatchCost batch+controllerCost out unit+answerWriteCost n unit

/-- The full finite counter is assembled from the recorded controller and
concrete block schedules. Geometry, incidence cardinality, final-scan budget,
primitive bit costs and logarithmic round counts have separate precise roles. -/
theorem actual_completeCounter_le_chargedCost {R X V Pair : Type*} [CommSemiring R] [DecidableEq Pair]
    (O : CompositeAlgorithm.CountOracle X) (A : CompositeCertification.Instance X V)
    (pair : X → Pair) (lam depth stages n k windows unit : ℕ)
    (pool : Finset ℕ) (initial : Finset X)
    (batch : PhaseBatch R n k (CompositeAlgorithm.solve O A pair lam depth stages pool initial).calls.length)
    (hn : 3 ≤ n)
    (hpool : pool ⊆ PrimePool.candidates (primeScale n AsymptoticCosts.eta k))
    (hinc : initial.card ≤ windows*queryCount n AsymptoticCosts.b)
    (hscan : (CompositeAlgorithm.solve O A pair lam depth stages pool initial).originalSumTests ≤ n^2)
    (hgeometry : ∀ i, gridSide (Nat.ceil (RealCertificate.c*
      (innerPower n (batch.phases i) AlignedCertificate.S:ℝ)))
      (innerPower n (batch.phases i) AlignedCertificate.S) ≤ outerSize (batch.phases i) AlignedCertificate.S n)
    (primitiveBound Cbit Cunit Cround : ℝ) (bitLog unitLog roundLog : ℕ)
    (hprimitive : PrimitiveBudget batch primitiveBound)
    (hCbit : 0 ≤ Cbit) (hCunit : 0 ≤ Cunit) (hCround : 0 ≤ Cround)
    (harithmetic : primitiveBound ≤ Cbit*(Real.log (n:ℝ))^bitLog*(n:ℝ)^(ArithmeticSlack.extra:ℝ))
    (hunit : (unit:ℝ) ≤ Cunit*(Real.log (n:ℝ))^unitLog)
    (hrounds : (stages*(depth+1):ℕ) ≤ Cround*(Real.log (n:ℝ))^roundLog) :
    let K := (roundLog+bitLog+5+ledgerLogDegree k)+(roundLog+k+unitLog)
    let C := Cround*Cbit*Overhead.phaseCoefficientConstant k*ledgerConstant +
      Cunit*(289*Cround*(2*(windows:ℝ)+1)+1)+3*Cunit
    (completeCounter batch (CompositeAlgorithm.solve O A pair lam depth stages pool initial) unit:ℝ) ≤
      C*ArithmeticSlack.chargedCost K n := by
  let K₁ := roundLog+bitLog+5+ledgerLogDegree k
  let K₂ := roundLog+k+unitLog
  let C₁ := Cround*Cbit*Overhead.phaseCoefficientConstant k*ledgerConstant
  let C₂ := Cunit*(289*Cround*(2*(windows:ℝ)+1)+1)
  have h₁ := phaseBatchCost_le_chargedCost batch hn (stages*(depth+1))
    (actual_controller_call_count O A pair lam depth stages n k pool initial hpool)
    hgeometry primitiveBound Cbit Cround bitLog roundLog hprimitive.nonneg hCbit hCround
    hprimitive.linear hprimitive.lookup hprimitive.formation hprimitive.fullMultiply harithmetic hrounds
  have h₂ := actual_controller_le_chargedCost O A pair lam depth stages n k windows unit
    pool initial hn hpool hinc hscan Cunit Cround unitLog roundLog hCunit hCround hunit hrounds
  have h₃ := answerWriteCost_le_chargedCost n unit unitLog hn Cunit hCunit hunit
  have hc₁ : 0 ≤ C₁ := mul_nonneg (mul_nonneg (mul_nonneg hCround hCbit)
    (Overhead.phaseCoefficientConstant_nonneg k)) ledgerConstant_nonneg
  have hc₂ : 0 ≤ C₂ := by dsimp [C₂]; positivity
  have hmono₁ := mul_le_mul_of_nonneg_left (chargedCost_mono n K₁ (K₁+K₂) hn (by omega)) hc₁
  have hmono₂ := mul_le_mul_of_nonneg_left (chargedCost_mono n K₂ (K₁+K₂) hn (by omega)) hc₂
  have hmono₃ := mul_le_mul_of_nonneg_left
    (chargedCost_mono n unitLog (K₁+K₂) hn (by dsimp [K₁, K₂]; omega))
    (show 0 ≤ 3*Cunit by positivity)
  dsimp only
  unfold completeCounter
  push_cast
  dsimp [C₁, C₂, K₁, K₂] at hmono₁ hmono₂ hmono₃
  nlinarith only [h₁.trans hmono₁, h₂.trans hmono₂, h₃.trans hmono₃]

end
end ThinMatrix.ReductionCosts

#print axioms ThinMatrix.ReductionCosts.formationCost_eq
#print axioms ThinMatrix.ReductionCosts.blockScheduleCost_le
#print axioms ThinMatrix.ReductionCosts.blockPower_le_raw
#print axioms ThinMatrix.ReductionCosts.actual_rawTerm_bound
#print axioms ThinMatrix.ReductionCosts.actual_localFactor_le_polylog
#print axioms ThinMatrix.ReductionCosts.actualPhaseCost_bound
#print axioms ThinMatrix.ReductionCosts.counted_batch_bound
#print axioms ThinMatrix.ReductionCosts.phaseBatchCost_bound
#print axioms ThinMatrix.ReductionCosts.charged_allPhaseLedger_bound
#print axioms ThinMatrix.ReductionCosts.phaseBatchCost_le_chargedCost
#print axioms ThinMatrix.ReductionCosts.phaseBatchCost_bigO
#print axioms ThinMatrix.ReductionCosts.actual_controller_call_count
#print axioms ThinMatrix.ReductionCosts.actual_controller_cost_le
#print axioms ThinMatrix.ReductionCosts.actual_controller_power_bound
#print axioms ThinMatrix.ReductionCosts.actual_controller_le_chargedCost
#print axioms ThinMatrix.ReductionCosts.actual_completeCounter_le_chargedCost
