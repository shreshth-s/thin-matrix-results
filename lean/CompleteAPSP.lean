import CompositeAlgorithm
import FoldedCounts
import PrimePool
import APSPAlgorithm

/-!
# Folded products, composite certification, and APSP correctness

The backend below is a matrix-product implementation, with ordinary exact
products as a concrete reference implementation. Actual signed middle labels
and the three integer windows -1,0,1 are retained in the incidence interface.
Scalar and coprime cyclic factorizations implement the same modular count.

The reusable composite theorem has explicit finite prime/power/cardinality
parameters. A separate large-prime reference configuration supplies an
unconditional correctness implementation. It makes no fast running-time claim.
In particular this module does not assume that execution cost is dominated by
the aligned asymptotic ledger, or claim to prove that domination.

The resource conclusions count composite table calls and returned cells.
The cached finite-block variant additionally stores one backend preparation
per block per positive-modulus table call. Source-formation costs and runtime
of Lean's function-valued matrix representation remain separate obligations.
The generic block interface retains the original middle type and zeroes
unused labels. Compact reindexing to a block-sized middle dimension is also a
separate obligation for a fast backend; no thin-product cost is claimed here.
-/

namespace ThinMatrix.CompleteAPSP
open scoped BigOperators
open ThinMatrix.CyclicRing
open Fin.CommRing

variable {I K J H : Type*}

/-- The backend contract concerns exact finite matrix multiplication, rather
than an assumed triangle-decision oracle. -/
structure ProductBackend (I K J : Type*) [Fintype K] where
  product : ∀ (d q : ℕ), [NeZero d] → [NeZero q] →
    Matrix (I × Fin (FoldedCounts.foldWidth d)) (K × ZMod d) (Cyclic q) →
    Matrix (K × ZMod d) (J × Fin (FoldedCounts.foldWidth d)) (Cyclic q) →
    Matrix (I × Fin (FoldedCounts.foldWidth d)) (J × Fin (FoldedCounts.foldWidth d)) (Cyclic q)
  correct : ∀ (d q : ℕ) [NeZero d] [NeZero q] A B, product d q A B = A*B

/-- Direct finite integer sums implement all coefficients; no complex or ring
operation is treated as an executable constant-time primitive. -/
def naiveProduct [Fintype K] (d q : ℕ) [NeZero d] [NeZero q]
    (A : Matrix (I × Fin (FoldedCounts.foldWidth d)) (K × ZMod d) (Cyclic q))
    (B : Matrix (K × ZMod d) (J × Fin (FoldedCounts.foldWidth d)) (Cyclic q)) :
    Matrix (I × Fin (FoldedCounts.foldWidth d)) (J × Fin (FoldedCounts.foldWidth d)) (Cyclic q) :=
  fun i j r => ∑ k, ∑ s : Fin q, A i k s * B k j (r-s)

theorem naiveProduct_correct [Fintype K] (d q : ℕ) [NeZero d] [NeZero q]
    (A : Matrix (I × Fin (FoldedCounts.foldWidth d)) (K × ZMod d) (Cyclic q))
    (B : Matrix (K × ZMod d) (J × Fin (FoldedCounts.foldWidth d)) (Cyclic q)) :
    naiveProduct d q A B = A*B := by
  funext i j r
  simp only [naiveProduct, Matrix.mul_apply, sum_coeff, mul_coeff]

def naiveBackend [Fintype K] : ProductBackend I K J :=
  ⟨naiveProduct, naiveProduct_correct⟩

structure Factorization (m : ℕ) where
  d : ℕ
  q : ℕ
  d_pos : 0 < d
  q_pos : 0 < q
  coprime : d.Coprime q
  product : d*q = m

abbrev FactorPlan := ∀ m : ℕ, m ≠ 0 → Factorization m

def scalarPlan : FactorPlan :=
  fun m hm => ⟨m, 1, Nat.pos_of_ne_zero hm, by decide, by simp, by simp⟩

/-- The fixed physical factor three is included in the folded modulus, and
is excluded from the cyclic factor by the explicit coprimality hypothesis. -/
def windowFactorization (d q : ℕ) (hd : 0 < d) (hq : 0 < q)
    (hc : d.Coprime q) (h₃ : Nat.Coprime 3 q) : Factorization (3*d*q) :=
  ⟨3*d, q, Nat.mul_pos (by decide) hd, hq,
    Nat.coprime_mul_iff_left.mpr ⟨h₃, hc⟩, rfl⟩

/-- Computational input entries, written coefficientwise to avoid the
noncomputable transported ring instance in the semantic source definitions. -/
def leftEncoded [DecidableEq K] (d q : ℕ) [NeZero d] [NeZero q]
    (active : Finset K) (A : I → K → ℤ) :
    Matrix (I × Fin (FoldedCounts.foldWidth d)) (K × ZMod d) (Cyclic q) :=
  fun i k r => if k.1 ∈ active ∧ k.2 = (A i.1 k.1 : ZMod d)+(i.2.val : ZMod d) ∧
    r = (A i.1 k.1 : Fin q) then 1 else 0

def rightEncoded (d q : ℕ) [NeZero d] [NeZero q] (B : K → J → ℤ) :
    Matrix (K × ZMod d) (J × Fin (FoldedCounts.foldWidth d)) (Cyclic q) :=
  fun k j r => if k.2 = -(B k.1 j.1 : ZMod d)-
    (FoldedCounts.foldWidth d : ZMod d)*(j.2.val : ZMod d) ∧
    r = (B k.1 j.1 : Fin q) then 1 else 0

theorem leftEncoded_eq [Fintype K] [DecidableEq K] (d q : ℕ) [NeZero d] [NeZero q]
    (active : Finset K) (A : I → K → ℤ) :
    leftEncoded d q active A = FoldedCounts.leftMatrix (d := d) (q := q) active A := by
  funext i k r
  simp only [leftEncoded, FoldedCounts.leftMatrix, FoldedCounts.leftEntry]
  split_ifs <;> simp_all [zero_coeff, monomial]

theorem rightEncoded_eq (d q : ℕ) [NeZero d] [NeZero q] (B : K → J → ℤ) :
    rightEncoded d q B = FoldedCounts.rightMatrix (d := d) (q := q) B (FoldedCounts.foldWidth d) := by
  funext k j r
  simp only [rightEncoded, FoldedCounts.rightMatrix, FoldedCounts.rightEntry]
  split_ifs <;> simp_all [zero_coeff, monomial]

def foldedCount [Fintype K] [DecidableEq K]
    (backend : ProductBackend I K J) {m : ℕ} (f : Factorization m)
    (active : Finset K) (A : I → K → ℤ) (B : K → J → ℤ) (T : I → J → ℤ) : I → J → ℕ := by
  letI : NeZero f.d := ⟨Nat.ne_of_gt f.d_pos⟩
  letI : NeZero f.q := ⟨Nat.ne_of_gt f.q_pos⟩
  let C := backend.product f.d f.q (leftEncoded f.d f.q active A) (rightEncoded f.d f.q B)
  exact fun i j => (C (i, FoldedCounts.residueLow (T i j : ZMod f.d))
    (j, FoldedCounts.residueHigh (T i j : ZMod f.d)) ((-T i j : ℤ) : Fin f.q)).toNat

theorem foldedCount_correct [Fintype K] [DecidableEq K]
    (backend : ProductBackend I K J) {m : ℕ} (f : Factorization m)
    (active : Finset K) (A : I → K → ℤ) (B : K → J → ℤ) (T : I → J → ℤ) (i : I) (j : J) :
    foldedCount backend f active A B T i j =
      (active.filter (fun k => (m : ℤ) ∣ A i k+B k j+T i j)).card := by
  letI : NeZero f.d := ⟨Nat.ne_of_gt f.d_pos⟩
  letI : NeZero f.q := ⟨Nat.ne_of_gt f.q_pos⟩
  have hc := FoldedCounts.canonical_folded_count f.coprime active A B T i j
  rw [f.product] at hc
  unfold foldedCount
  rw [backend.correct, leftEncoded_eq, rightEncoded_eq, hc, Int.toNat_natCast]

abbrev Incidence (I J H : Type*) := (I × J) × H × Fin 3
def windowValue (w : Fin 3) : ℤ := (w.val : ℤ)-1
def zeroWindow : Fin 3 := ⟨1, by decide⟩

theorem windowValue_zero : windowValue zeroWindow = 0 := by decide
theorem windowValue_range (w : Fin 3) : windowValue w ∈ ({-1,0,1} : Finset ℤ) := by
  fin_cases w <;> decide

theorem windowValue_abs_le (w : Fin 3) : (windowValue w).natAbs ≤ 1 := by
  fin_cases w <;> decide

/-- Floor refinement uses the target with the opposite sign. Every fine
signed-window witness has a coarse witness in the same three-element window. -/
theorem signed_window_backward (a b c : ℤ) (h : -1 ≤ a+b-c ∧ a+b-c ≤ 1) :
    -1 ≤ a/2+b/2-c/2 ∧ a/2+b/2-c/2 ≤ 1 := by
  have ha := MinPlusReduction.half_remainder a
  have hb := MinPlusReduction.half_remainder b
  have hc := MinPlusReduction.half_remainder c
  omega

theorem folded_signed_window_count [Fintype K] [DecidableEq K]
    (backend : ProductBackend I K J) (d q : ℕ) (hd : 0 < d) (hq : 0 < q)
    (hc : d.Coprime q) (h₃ : Nat.Coprime 3 q) (active : Finset K)
    (A : I → K → ℤ) (B : K → J → ℤ) (T : I → J → ℤ)
    (w : Fin 3) (i : I) (j : J) :
    foldedCount backend (windowFactorization d q hd hq hc h₃) active A B
      (fun a b => T a b-windowValue w) i j =
    (active.filter (fun k => ((3*d*q : ℕ) : ℤ) ∣ A i k+B k j+T i j-windowValue w)).card := by
  simpa only [add_sub_assoc] using foldedCount_correct backend
    (windowFactorization d q hd hq hc h₃) active A B (fun a b => T a b-windowValue w) i j

def incidenceInstance [DecidableEq K] (blocks : H → Finset K)
    (A : I → K → ℤ) (B : K → J → ℤ) (T : I → J → ℤ) :
    CompositeCertification.Instance (Incidence I J H) K where
  block x := blocks x.2.1
  value x k := A x.1.1 k+B k x.1.2+T x.1.1 x.1.2-windowValue x.2.2

/-- One returned cell is an exact modular count for the same original labels,
with the integer target shifted by its actual signed window. -/
def countOracle [Fintype K] [DecidableEq K]
    (backend : ProductBackend I K J) (plan : FactorPlan) (blocks : H → Finset K)
    (A : I → K → ℤ) (B : K → J → ℤ) (T : I → J → ℤ) :
    CompositeAlgorithm.CountOracle (Incidence I J H) where
  table m _active x := if hm : m = 0 then
      ((blocks x.2.1).filter (fun k => A x.1.1 k+B k x.1.2+T x.1.1 x.1.2-windowValue x.2.2 = 0)).card
    else foldedCount backend (plan m hm) (blocks x.2.1) A B
      (fun i j => T i j-windowValue x.2.2) x.1.1 x.1.2

theorem countOracle_correct [Fintype K] [DecidableEq K]
    (backend : ProductBackend I K J) (plan : FactorPlan) (blocks : H → Finset K)
    (A : I → K → ℤ) (B : K → J → ℤ) (T : I → J → ℤ) :
    (countOracle backend plan blocks A B T).Correct (incidenceInstance blocks A B T) := by
  intro m active x hx
  dsimp only [countOracle]
  split_ifs with hm
  · subst m
    simp [CompositeCertification.Instance.modCount, incidenceInstance]
  · rw [foldedCount_correct]
    simp only [CompositeCertification.Instance.modCount, incidenceInstance, add_sub_assoc]
    exact (Finset.sum_boole _ _).symm

/-! Finite composite parameters and the actual signed incidence correspondence. -/

structure Parameters (h U : ℕ) where
  pool : Finset ℕ
  P : ℕ
  lam : ℕ
  k : ℕ
  M : ℕ
  stages : ℕ
  prime : ∀ p ∈ pool, Nat.Prime p
  lower : ∀ p ∈ pool, P ≤ p
  P_pos : 1 ≤ P
  power : U < P^(lam+1)
  threshold : lam < M
  size : M+k ≤ pool.card
  rate : 2*h*lam^(k+1) ≤ (M-lam)*M^k

/-- The prime pool is actually enumerated by the proved trial-division
predicate. The remaining finite parameter conditions are explicit. -/
def enumeratedParameters (h U P lam k M stages : ℕ)
    (hP : 1 ≤ P) (hpower : U < P^(lam+1)) (hM : lam < M)
    (hsize : M+k ≤ (PrimePool.enumeratedCandidates P).card)
    (hrate : 2*h*lam^(k+1) ≤ (M-lam)*M^k) : Parameters h U where
  pool := PrimePool.enumeratedCandidates P
  P := P
  lam := lam
  k := k
  M := M
  stages := stages
  prime _p hp := PrimePool.candidate_prime (PrimePool.enumeratedCandidates_eq P ▸ hp)
  lower _p hp := PrimePool.candidate_lower (PrimePool.enumeratedCandidates_eq P ▸ hp)
  P_pos := hP
  power := hpower
  threshold := hM
  size := hsize
  rate := hrate

def magnitude {X V : Type*} [Fintype X] [Fintype V]
    (S : CompositeCertification.Instance X V) : ℕ :=
  Finset.univ.sup (fun xv : X × V => (S.value xv.1 xv.2).natAbs)

theorem magnitude_bound {X V : Type*} [Fintype X] [Fintype V]
    (S : CompositeCertification.Instance X V) (x : X) (v : V) :
    (S.value x v).natAbs ≤ magnitude S := by
  unfold magnitude
  exact Finset.le_sup (f := fun xv : X × V => (S.value xv.1 xv.2).natAbs)
    (b := (x,v)) (Finset.mem_univ _)

theorem triangle_magnitude_bound [Fintype I] [Fintype K] [Fintype J] [Fintype H]
    [DecidableEq K] (blocks : H → Finset K)
    (A : I → K → ℤ) (B : K → J → ℤ) (T : I → J → ℤ) (W : ℕ)
    (hA : ∀ i k, (A i k).natAbs ≤ W) (hB : ∀ k j, (B k j).natAbs ≤ W)
    (hT : ∀ i j, (T i j).natAbs ≤ W) :
    magnitude (incidenceInstance blocks A B T) ≤ 3*W+1 := by
  apply Finset.sup_le
  intro xv hx
  change (A xv.1.1.1 xv.2+B xv.2 xv.1.1.2+T xv.1.1.1 xv.1.1.2-windowValue xv.1.2.2).natAbs ≤ _
  calc
    _ ≤ (A xv.1.1.1 xv.2+B xv.2 xv.1.1.2+T xv.1.1.1 xv.1.1.2).natAbs+
        (windowValue xv.1.2.2).natAbs := Int.natAbs_sub_le _ _
    _ ≤ ((A xv.1.1.1 xv.2).natAbs+(B xv.2 xv.1.1.2).natAbs)+
        (T xv.1.1.1 xv.1.1.2).natAbs+1 := by
      exact Nat.add_le_add ((Int.natAbs_add_le _ _).trans
        (Nat.add_le_add_right (Int.natAbs_add_le _ _) _)) (windowValue_abs_le _)
    _ ≤ _ := by have h₁ := hA xv.1.1.1 xv.2; have h₂ := hB xv.2 xv.1.1.2; have h₃ := hT xv.1.1.1 xv.1.1.2; omega

def solveFolded [Fintype K] [DecidableEq K] {Pair : Type*} [DecidableEq Pair]
    (backend : ProductBackend I K J) (plan : FactorPlan) (blocks : H → Finset K)
    (A : I → K → ℤ) (B : K → J → ℤ) (T : I → J → ℤ)
    {h U : ℕ} (params : Parameters h U)
    (pair : Incidence I J H → Pair) (initial : Finset (Incidence I J H)) :
    CompositeAlgorithm.Result (Incidence I J H) Pair :=
  CompositeAlgorithm.solve (countOracle backend plan blocks A B T)
    (incidenceInstance blocks A B T) pair params.lam params.k params.stages params.pool initial

/-- This theorem instantiates the executed composite program with the actual
folded count implementation. Its outputs refer to original signed integer
labels, and its resource conclusions are finite calls/cells/visits/scans.
There is no premise assigning an unproved execution-cost ledger to a call. -/
theorem solveFolded_correct_and_resources [Fintype K] [DecidableEq K]
    {Pair : Type*} [DecidableEq Pair]
    (backend : ProductBackend I K J) (plan : FactorPlan) (blocks : H → Finset K)
    (A : I → K → ℤ) (B : K → J → ℤ) (T : I → J → ℤ)
    {h U : ℕ} (params : Parameters h U)
    (hmag : ∀ (x : Incidence I J H) (v : K), v ∈ blocks x.2.1 →
      (A x.1.1 v+B v x.1.2+T x.1.1 x.1.2-windowValue x.2.2).natAbs ≤ U)
    (pair : Incidence I J H → Pair) (initial : Finset (Incidence I J H))
    (hblock : ∀ b, (blocks b).card ≤ h)
    (budget : ℕ) (hbudget : h*initial.card ≤ 2^params.stages*budget) :
    let out := solveFolded backend plan blocks A B T params pair initial
    (∀ q, q ∈ out.answers ↔ ∃ x ∈ initial, pair x = q ∧
      ∃ v ∈ blocks x.2.1, A x.1.1 v+B v x.1.2+T x.1.1 x.1.2 = windowValue x.2.2) ∧
    out.calls.length ≤ params.stages*(params.k+1)*params.pool.card ∧
    CompositeAlgorithm.tableCells out.calls ≤ params.stages*(params.k+1)*params.pool.card*initial.card ∧
    out.bookkeeping ≤ 16*params.stages*(params.k+1)*(params.pool.card+1)*(initial.card+1) ∧
    out.originalSumTests ≤ budget := by
  have hdiv := (incidenceInstance blocks A B T).divisorBound_of_prime_power
    params.pool params.P U params.lam params.prime params.lower params.P_pos hmag params.power
  have hblock' : ∀ x ∈ initial, (blocks x.2.1).card ≤ h :=
    fun x _ => hblock x.2.1
  have hc := CompositeAlgorithm.solve_correct_and_resources
    (countOracle backend plan blocks A B T) (incidenceInstance blocks A B T)
    (countOracle_correct backend plan blocks A B T) pair initial params.pool
    params.k params.M params.lam h params.stages budget
    params.threshold params.size hdiv hblock' params.rate hbudget
  refine ⟨?_, hc.2⟩
  intro q
  simpa only [solveFolded, incidenceInstance, sub_eq_zero] using hc.1 q

def zeroIncidences [Fintype I] [Fintype J] [Fintype H] : Finset (Incidence I J H) :=
  Finset.univ.filter (fun x => x.2.2 = zeroWindow)

abbrev ParameterPolicy (h : ℕ) := ∀ U : ℕ, Parameters h U

def triangleOracle [Fintype I] [Fintype K] [Fintype J] [Fintype H]
    [DecidableEq I] [DecidableEq K] [DecidableEq J]
    (backend : ProductBackend I K J) (plan : FactorPlan) (blocks : H → Finset K)
    {h : ℕ} (policy : ParameterPolicy h) : MinPlusReduction.TriangleOracle I K J :=
  fun A B T =>
    let result := solveFolded backend plan blocks A B T
      (policy (magnitude (incidenceInstance blocks A B T))) Prod.fst zeroIncidences
    fun i j => decide ((i,j) ∈ result.answers)

/-- The triangle-oracle contract is derived here, not assumed. Covering the
middle labels is enough; blocks may be unequal or overlap. -/
theorem triangleOracle_correct [Fintype I] [Fintype K] [Fintype J] [Fintype H]
    [DecidableEq I] [DecidableEq K] [DecidableEq J]
    (backend : ProductBackend I K J) (plan : FactorPlan) (blocks : H → Finset K)
    (cover : ∀ k : K, ∃ b : H, k ∈ blocks b)
    {h : ℕ} (hblock : ∀ b, (blocks b).card ≤ h) (policy : ParameterPolicy h) :
    MinPlusReduction.OracleCorrect (triangleOracle backend plan blocks policy) := by
  intro A B T i j
  let params := policy (magnitude (incidenceInstance blocks A B T))
  have hp : 1 ≤ 2^params.stages := Nat.one_le_two_pow
  have hc := solveFolded_correct_and_resources backend plan blocks A B T params
    (fun x v _ => magnitude_bound (incidenceInstance blocks A B T) x v) Prod.fst zeroIncidences
    hblock (h*zeroIncidences.card)
    (by simpa using Nat.mul_le_mul_right (h*zeroIncidences.card) hp)
  simp only [triangleOracle, decide_eq_true_eq]
  rw [hc.1 (i,j)]
  constructor
  · rintro ⟨x, hx, he, k, hk, hz⟩
    have hw : x.2.2 = zeroWindow := (Finset.mem_filter.mp hx).2
    have hi := congrArg Prod.fst he
    have hj := congrArg Prod.snd he
    refine ⟨k, ?_⟩
    simpa only [hi, hj, hw, windowValue_zero] using hz
  · rintro ⟨k, hk⟩
    obtain ⟨b, hb⟩ := cover k
    refine ⟨((i,j),b,zeroWindow), ?_, rfl, k, hb, ?_⟩
    · simp [zeroIncidences]
    · simpa only [windowValue_zero] using hk

/-! Explicit correctness reference configuration. This intentionally uses a
possibly enormous prime and is not the aligned fast parameter choice. -/

def bigPrime (U : ℕ) : ℕ := (U.factorial+1).minFac

theorem bigPrime_prime (U : ℕ) : Nat.Prime (bigPrime U) := by
  apply Nat.minFac_prime
  have hp := Nat.factorial_pos U
  omega

theorem bigPrime_gt (U : ℕ) : U < bigPrime U := by
  have hp := bigPrime_prime U
  apply Nat.lt_of_not_ge
  intro h
  have hf : bigPrime U ∣ U.factorial := Nat.dvd_factorial hp.pos h
  have hd : bigPrime U ∣ U.factorial+1 := Nat.minFac_dvd _
  exact hp.not_dvd_one ((Nat.dvd_add_iff_right hf).mpr hd)

def referenceParameters (h U : ℕ) : Parameters h U where
  pool := {bigPrime U}
  P := bigPrime U
  lam := 0
  k := 0
  M := 1
  stages := 1
  prime p hp := by simpa using (Finset.mem_singleton.mp hp ▸ bigPrime_prime U)
  lower p hp := by simp_all
  P_pos := (bigPrime_prime U).one_lt.le
  power := by simpa using bigPrime_gt U
  threshold := by decide
  size := by simp
  rate := by simp

def Parameters.weaken {h U V : ℕ} (p : Parameters h U) (hV : V ≤ U) : Parameters h V :=
  { p with power := hV.trans_lt p.power }

/-- A finite configuration for a proved magnitude cap extends to a total
oracle using the correctness reference only outside that cap. -/
def boundedPolicy {h U : ℕ} (p : Parameters h U) : ParameterPolicy h :=
  fun V => if hV : V ≤ U then p.weaken hV else referenceParameters h V

theorem boundedPolicy_below {h U V : ℕ} (p : Parameters h U) (hV : V ≤ U) :
    (boundedPolicy p V).pool = p.pool ∧ (boundedPolicy p V).k = p.k ∧
    (boundedPolicy p V).lam = p.lam ∧ (boundedPolicy p V).M = p.M ∧
    (boundedPolicy p V).stages = p.stages := by
  simp [boundedPolicy, hV, Parameters.weaken]

def referenceTriangle [Fintype I] [Fintype K] [Fintype J]
    [DecidableEq I] [DecidableEq K] [DecidableEq J] : MinPlusReduction.TriangleOracle I K J :=
  triangleOracle naiveBackend scalarPlan (fun _ : Unit => Finset.univ) (referenceParameters (Fintype.card K))

theorem referenceTriangle_correct [Fintype I] [Fintype K] [Fintype J]
    [DecidableEq I] [DecidableEq K] [DecidableEq J] :
    MinPlusReduction.OracleCorrect (referenceTriangle (I := I) (K := K) (J := J)) := by
  apply triangleOracle_correct
  · intro k
    exact ⟨(), by simp⟩
  · intro block
    simp

def backendAPSP [Fintype K] [Fintype H] [DecidableEq K]
    (backend : ProductBackend K K K) (plan : FactorPlan) (blocks : H → Finset K)
    {h : ℕ} (policy : ParameterPolicy h) (w : APSPReduction.Graph K) (W : ℕ) :
    APSPReduction.Matrix K :=
  APSPAlgorithm.fastAPSP (triangleOracle backend plan blocks policy) w W

/-- The full min-plus/sentinel/squaring transfer for every valid finite
composite policy and exact product backend. This is a correctness theorem,
with no assumption about the triangle algorithm or its execution cost. -/
theorem backendAPSP_correct [Fintype K] [Fintype H] [DecidableEq K]
    (backend : ProductBackend K K K) (plan : FactorPlan) (blocks : H → Finset K)
    (cover : ∀ k : K, ∃ b : H, k ∈ blocks b)
    {h : ℕ} (hblock : ∀ b, (blocks b).card ≤ h) (policy : ParameterPolicy h) (w : APSPReduction.Graph K) (W : ℕ)
    (hw : APSPReduction.EdgeBound w W) (hno : APSPReduction.NoNegativeCycles w) :
    APSPReduction.IsAPSP w (backendAPSP backend plan blocks policy w W) :=
  APSPAlgorithm.fastAPSP_correct (triangleOracle backend plan blocks policy)
    (triangleOracle_correct backend plan blocks cover hblock policy) w W hw hno

theorem natAbs_of_symmetric {z : ℤ} {P : ℕ} (h : -(P : ℤ) ≤ z ∧ z ≤ P) :
    z.natAbs ≤ P := by
  have ha : |z| ≤ (P : ℤ) := abs_le.mpr h
  have hn : (z.natAbs : ℤ) ≤ (P : ℤ) := by simpa only [Int.natCast_natAbs] using ha
  exact_mod_cast hn

/-- The actual adaptive equality queries have a polynomial original-sum
magnitude bound, including all three signed-window shifts. The divisor-bound
parameter is therefore controlled by graph size and input weight, not assumed
as a property of a successful query sequence. -/
theorem backendAPSP_adaptive_magnitude [Fintype K] [Fintype H]
    [DecidableEq K] [Nonempty K]
    (backend : ProductBackend K K K) (plan : FactorPlan) (blocks : H → Finset K)
    (cover : ∀ k : K, ∃ b : H, k ∈ blocks b)
    {h : ℕ} (hblock : ∀ b, (blocks b).card ≤ h) (policy : ParameterPolicy h) (w : APSPReduction.Graph K) (W : ℕ)
    (hw : APSPReduction.EdgeBound w W) :
    ∀ q ∈ APSPAlgorithm.fastTrace (triangleOracle backend plan blocks policy) w
      (APSPAlgorithm.globalBound (Fintype.card K) W) (APSPReduction.rounds (Fintype.card K)),
    magnitude (incidenceInstance blocks q.1 q.2.1 q.2.2) ≤ 192*Fintype.card K*W+40 := by
  intro q hq
  have hb := APSPAlgorithm.fastTrace_weight_bound (triangleOracle backend plan blocks policy)
    (triangleOracle_correct backend plan blocks cover hblock policy) w W hw
    (APSPReduction.rounds (Fintype.card K)) (by rfl) q hq
  have hm := triangle_magnitude_bound blocks q.1 q.2.1 q.2.2
    (64*Fintype.card K*W+13)
    (fun i k => natAbs_of_symmetric (hb.1 i k))
    (fun k j => natAbs_of_symmetric (hb.2.1 k j))
    (fun i j => natAbs_of_symmetric (hb.2.2 i j))
  nlinarith

/-- A complete reference algorithm, using folded products and executed
composite certification for its equality tests at every bit-scaling stage. -/
def uncachedAPSP [Fintype K] [DecidableEq K] (w : APSPReduction.Graph K) (W : ℕ) :
    APSPReduction.Matrix K := APSPAlgorithm.fastAPSP referenceTriangle w W

theorem uncachedAPSP_correct [Fintype K] [DecidableEq K]
    (w : APSPReduction.Graph K) (W : ℕ) (hw : APSPReduction.EdgeBound w W)
    (hno : APSPReduction.NoNegativeCycles w) :
    APSPReduction.IsAPSP w (uncachedAPSP w W) :=
  APSPAlgorithm.fastAPSP_correct referenceTriangle referenceTriangle_correct w W hw hno

/-! An explicit finite array shares backend preparations across all windows
and all requested outer pairs in a count-table call. -/

def preparedProducts [Fintype K] [DecidableEq K]
    (backend : ProductBackend I K J) {m b : ℕ} (f : Factorization m)
    (blocks : Fin b → Finset K) (A : I → K → ℤ) (B : K → J → ℤ) :
    Array (Matrix (I × Fin (FoldedCounts.foldWidth f.d))
      (J × Fin (FoldedCounts.foldWidth f.d)) (Cyclic f.q)) := by
  letI : NeZero f.d := ⟨Nat.ne_of_gt f.d_pos⟩
  letI : NeZero f.q := ⟨Nat.ne_of_gt f.q_pos⟩
  let right := rightEncoded f.d f.q B
  exact Array.ofFn (fun h : Fin b => backend.product f.d f.q
    (leftEncoded f.d f.q (blocks h) A) right)

theorem preparedProducts_size [Fintype K] [DecidableEq K]
    (backend : ProductBackend I K J) {m b : ℕ} (f : Factorization m)
    (blocks : Fin b → Finset K) (A : I → K → ℤ) (B : K → J → ℤ) :
    (preparedProducts backend f blocks A B).size = b := Array.size_ofFn

def preparedTable [Fintype K] [DecidableEq K]
    (backend : ProductBackend I K J) {m b : ℕ} (f : Factorization m)
    (blocks : Fin b → Finset K) (A : I → K → ℤ) (B : K → J → ℤ) (T : I → J → ℤ) :
    Incidence I J (Fin b) → ℕ := by
  letI : NeZero f.d := ⟨Nat.ne_of_gt f.d_pos⟩
  letI : NeZero f.q := ⟨Nat.ne_of_gt f.q_pos⟩
  let products := preparedProducts backend f blocks A B
  exact fun x =>
    let target := T x.1.1 x.1.2-windowValue x.2.2
    let C := products[x.2.1.val]'(by
      simp only [products, preparedProducts_size]
      exact x.2.1.isLt)
    (C (x.1.1, FoldedCounts.residueLow (target : ZMod f.d))
      (x.1.2, FoldedCounts.residueHigh (target : ZMod f.d)) ((-target : ℤ) : Fin f.q)).toNat

theorem preparedTable_eq [Fintype K] [DecidableEq K]
    (backend : ProductBackend I K J) {m b : ℕ} (f : Factorization m)
    (blocks : Fin b → Finset K) (A : I → K → ℤ) (B : K → J → ℤ) (T : I → J → ℤ)
    (x : Incidence I J (Fin b)) :
    preparedTable backend f blocks A B T x = foldedCount backend f (blocks x.2.1) A B
      (fun i j => T i j-windowValue x.2.2) x.1.1 x.1.2 := by
  simp only [preparedTable, preparedProducts, Array.getElem_ofFn]
  rfl

def cachedCountOracle [Fintype K] [DecidableEq K] {b : ℕ}
    (backend : ProductBackend I K J) (plan : FactorPlan) (blocks : Fin b → Finset K)
    (A : I → K → ℤ) (B : K → J → ℤ) (T : I → J → ℤ) :
    CompositeAlgorithm.CountOracle (Incidence I J (Fin b)) where
  table m active := if hm : m = 0 then (countOracle backend plan blocks A B T).table m active
    else preparedTable backend (plan m hm) blocks A B T

theorem cachedCountOracle_eq [Fintype K] [DecidableEq K] {b : ℕ}
    (backend : ProductBackend I K J) (plan : FactorPlan) (blocks : Fin b → Finset K)
    (A : I → K → ℤ) (B : K → J → ℤ) (T : I → J → ℤ) :
    cachedCountOracle backend plan blocks A B T = countOracle backend plan blocks A B T := by
  apply congrArg CompositeAlgorithm.CountOracle.mk
  funext m active x
  dsimp only [cachedCountOracle, countOracle]
  split_ifs
  · rfl
  · exact preparedTable_eq backend _ blocks A B T x

def cachedSolveFolded [Fintype K] [DecidableEq K] {b : ℕ} {Pair : Type*} [DecidableEq Pair]
    (backend : ProductBackend I K J) (plan : FactorPlan) (blocks : Fin b → Finset K)
    (A : I → K → ℤ) (B : K → J → ℤ) (T : I → J → ℤ)
    {h U : ℕ} (params : Parameters h U)
    (pair : Incidence I J (Fin b) → Pair) (initial : Finset (Incidence I J (Fin b))) :
    CompositeAlgorithm.Result (Incidence I J (Fin b)) Pair :=
  CompositeAlgorithm.solve (cachedCountOracle backend plan blocks A B T)
    (incidenceInstance blocks A B T) pair params.lam params.k params.stages params.pool initial

theorem cachedSolveFolded_eq [Fintype K] [DecidableEq K] {b : ℕ} {Pair : Type*} [DecidableEq Pair]
    (backend : ProductBackend I K J) (plan : FactorPlan) (blocks : Fin b → Finset K)
    (A : I → K → ℤ) (B : K → J → ℤ) (T : I → J → ℤ)
    {h U : ℕ} (params : Parameters h U)
    (pair : Incidence I J (Fin b) → Pair) (initial : Finset (Incidence I J (Fin b))) :
    cachedSolveFolded backend plan blocks A B T params pair initial =
      solveFolded backend plan blocks A B T params pair initial := by
  simp only [cachedSolveFolded, cachedCountOracle_eq, solveFolded]

def preparationCalls {X : Type*} (b : ℕ) (calls : List (CompositeAlgorithm.Call X)) : ℕ :=
  CompositeAlgorithm.oracleWork (fun c => if c.modulus = 0 then 0 else b) calls

/-- The backend-preparation ledger is derived from the stored array length
for each table call. It assumes no bound on the cost of a preparation. -/
theorem cachedSolve_preparations [Fintype K] [DecidableEq K] {b : ℕ}
    {Pair : Type*} [DecidableEq Pair]
    (backend : ProductBackend I K J) (plan : FactorPlan) (blocks : Fin b → Finset K)
    (A : I → K → ℤ) (B : K → J → ℤ) (T : I → J → ℤ)
    {h U : ℕ} (params : Parameters h U)
    (pair : Incidence I J (Fin b) → Pair) (initial : Finset (Incidence I J (Fin b))) :
    preparationCalls b (cachedSolveFolded backend plan blocks A B T params pair initial).calls ≤
      params.stages*(params.k+1)*params.pool.card*b := by
  apply CompositeAlgorithm.solve_oracleWork_bound
  intro c hc
  split_ifs <;> omega

def cachedTriangleOracle [Fintype I] [Fintype K] [Fintype J] {b : ℕ}
    [DecidableEq I] [DecidableEq K] [DecidableEq J]
    (backend : ProductBackend I K J) (plan : FactorPlan) (blocks : Fin b → Finset K)
    {h : ℕ} (policy : ParameterPolicy h) : MinPlusReduction.TriangleOracle I K J :=
  fun A B T =>
    let result := cachedSolveFolded backend plan blocks A B T
      (policy (magnitude (incidenceInstance blocks A B T))) Prod.fst zeroIncidences
    fun i j => decide ((i,j) ∈ result.answers)

theorem cachedTriangleOracle_eq [Fintype I] [Fintype K] [Fintype J] {b : ℕ}
    [DecidableEq I] [DecidableEq K] [DecidableEq J]
    (backend : ProductBackend I K J) (plan : FactorPlan) (blocks : Fin b → Finset K)
    {h : ℕ} (policy : ParameterPolicy h) :
    cachedTriangleOracle backend plan blocks policy = triangleOracle backend plan blocks policy := by
  funext A B T i j
  simp only [cachedTriangleOracle, cachedSolveFolded_eq, triangleOracle]

def cachedBackendAPSP [Fintype K] [DecidableEq K] {b : ℕ}
    (backend : ProductBackend K K K) (plan : FactorPlan) (blocks : Fin b → Finset K)
    {h : ℕ} (policy : ParameterPolicy h) (w : APSPReduction.Graph K) (W : ℕ) :
    APSPReduction.Matrix K :=
  APSPAlgorithm.fastAPSP (cachedTriangleOracle backend plan blocks policy) w W

theorem cachedBackendAPSP_correct [Fintype K] [DecidableEq K] {b : ℕ}
    (backend : ProductBackend K K K) (plan : FactorPlan) (blocks : Fin b → Finset K)
    (cover : ∀ k : K, ∃ h : Fin b, k ∈ blocks h)
    {h : ℕ} (hblock : ∀ block, (blocks block).card ≤ h) (policy : ParameterPolicy h) (w : APSPReduction.Graph K) (W : ℕ)
    (hw : APSPReduction.EdgeBound w W) (hno : APSPReduction.NoNegativeCycles w) :
    APSPReduction.IsAPSP w (cachedBackendAPSP backend plan blocks policy w W) := by
  simpa only [cachedBackendAPSP, cachedTriangleOracle_eq, backendAPSP] using
    backendAPSP_correct backend plan blocks cover hblock policy w W hw hno

/-- The unconditional reference uses the cached program itself, with one
finite middle block and explicit naive cyclic products. -/
def completeAPSP [Fintype K] [DecidableEq K] (w : APSPReduction.Graph K) (W : ℕ) :
    APSPReduction.Matrix K := cachedBackendAPSP naiveBackend scalarPlan
      (fun _ : Fin 1 => Finset.univ) (referenceParameters (Fintype.card K)) w W

theorem completeAPSP_correct [Fintype K] [DecidableEq K]
    (w : APSPReduction.Graph K) (W : ℕ) (hw : APSPReduction.EdgeBound w W)
    (hno : APSPReduction.NoNegativeCycles w) :
    APSPReduction.IsAPSP w (completeAPSP w W) := by
  apply cachedBackendAPSP_correct
  · intro k
    exact ⟨0, by simp⟩
  · intro block
    simp
  · exact hw
  · exact hno

#print axioms naiveProduct_correct
#print axioms foldedCount_correct
#print axioms countOracle_correct
#print axioms folded_signed_window_count
#print axioms signed_window_backward
#print axioms triangle_magnitude_bound
#print axioms solveFolded_correct_and_resources
#print axioms triangleOracle_correct
#print axioms bigPrime_prime
#print axioms bigPrime_gt
#print axioms referenceTriangle_correct
#print axioms backendAPSP_correct
#print axioms backendAPSP_adaptive_magnitude
#print axioms completeAPSP_correct
#print axioms boundedPolicy_below
#print axioms preparedTable_eq
#print axioms cachedCountOracle_eq
#print axioms cachedSolve_preparations
#print axioms cachedBackendAPSP_correct

end ThinMatrix.CompleteAPSP
