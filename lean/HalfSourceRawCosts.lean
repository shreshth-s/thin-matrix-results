import HalfSourcePhaseCosts
import PhaseGeometry

/-! The seven concrete monomials underlying the exact-half phase costs.
Full cyclic vectors are charged in preprocessing, residual products and all
three encoders. Only stored coefficient queries omit the cyclic factor.
This is the size-to-ledger bridge; the production-counter domination is a
separate obligation. -/
namespace ThinMatrix.HalfSourceRawCosts
open HalfSourceParameters HalfSourcePhaseCosts
open scoped BigOperators
noncomputable section
set_option maxRecDepth 10000
set_option maxHeartbeats 4000000

def rawTerm (n N D q : ℝ) (i : Fin 7) : ℝ :=
  ![q*N^2*D^(-G), n^2*q*D^q1, n^2*D^q2,
    q*N*D^E, q*N*D^Ebox, q*N*D^Eroot, q*N*D] i

def outerDegree (i : Fin 7) : ℕ := ![2,0,0,1,1,1,1] i
def cyclicDegree (i : Fin 7) : ℕ := ![1,1,0,1,1,1,1] i
def pairDegree (i : Fin 7) : ℕ := ![0,2,2,0,0,0,0] i
def innerExponent (i : Fin 7) : ℝ := ![-G,q1,q2,E,Ebox,Eroot,1] i

theorem rawTerm_nonneg (n N D q : ℝ) (hN : 0 ≤ N) (hD : 0 ≤ D) (hq : 0 ≤ q)
    (i : Fin 7) : 0 ≤ rawTerm n N D q i := by
  fin_cases i <;> norm_num [rawTerm] <;> positivity

theorem rawTerm_canonical (n N D q : ℝ) (i : Fin 7) :
    rawTerm n N D q i=n^(pairDegree i)*q^(cyclicDegree i)*N^(outerDegree i)*D^(innerExponent i) := by
  fin_cases i <;> simp [rawTerm,pairDegree,cyclicDegree,outerDegree,innerExponent,Real.rpow_one]

theorem innerExponent_nonneg (i : Fin 7) (hi : i≠0) : 0 ≤ innerExponent i := by
  have ht := TEnclosure; have hg := GEnclosure; have hq := QEnclosure
  have ha := AEnclosure; have hr := ErootEnclosure
  fin_cases i <;> simp_all [innerExponent,q1,q2,E,Ebox,beta,zeta,theta] <;> linarith

def overhead (n : ℕ) : ℝ := (8192:ℝ)^R*(Real.log (n:ℝ))^(4*R)
def innerConstant (i : Fin 7) : ℝ := if i=0 then 1 else (24*(8192:ℝ)^R)^(innerExponent i)
def innerLogDegree (i : Fin 7) : ℕ := if i=0 then 0 else Nat.ceil ((4*R:ℕ)*innerExponent i)
def phaseConstant (i : Fin 7) : ℝ :=
  16384*((8192:ℝ)^R)^(cyclicDegree i+outerDegree i)*4^(outerDegree i)*innerConstant i
def phaseLogDegree (i : Fin 7) : ℕ :=
  4+(4*R)*(cyclicDegree i+outerDegree i)+innerLogDegree i

theorem overhead_nonneg (n : ℕ) (hn : 3 ≤ n) : 0 ≤ overhead n := by
  have h := PhaseGeometry.one_le_log_nat n hn
  unfold overhead
  positivity

theorem phaseConstant_nonneg (i : Fin 7) : 0 ≤ phaseConstant i := by
  unfold phaseConstant innerConstant
  split_ifs <;> positivity

theorem degree_exponent_identity (x z : ℝ) (i : Fin 7) :
    eta+(1-b)+(pairDegree i:ℝ)+(cyclicDegree i:ℝ)*z+
      (outerDegree i:ℝ)*(1+x/2)+(b+x)*innerExponent i=3-saving x z i := by
  fin_cases i <;> norm_num [saving,pairDegree,cyclicDegree,outerDegree,
    innerExponent,q1,E] <;> ring

/-- Nonpositive box powers use the lower dimension bound; every other
power uses the padded upper bound with its full fixed logarithmic degree. -/
theorem inner_power_bound (n : ℕ) (hn : 3 ≤ n) (D x : ℝ)
    (hD : 0 ≤ D)
    (hd : (n:ℝ)^(b+x) ≤ D ∧ D ≤ 24*overhead n*(n:ℝ)^(b+x)) (i : Fin 7) :
    D^(innerExponent i) ≤ innerConstant i*(Real.log (n:ℝ))^(innerLogDegree i)*
      (n:ℝ)^((b+x)*innerExponent i) := by
  have hnpos : 0 < (n:ℝ) := by exact_mod_cast (show 0<n by omega)
  by_cases hi : i=0
  · subst i
    have hg : 0 ≤ G := by linarith [GEnclosure.1]
    have h := Real.rpow_le_rpow_of_nonpos (Real.rpow_pos_of_pos hnpos (b+x)) hd.1
      (neg_nonpos.mpr hg)
    simpa [innerExponent,innerConstant,innerLogDegree,←Real.rpow_mul hnpos.le] using h
  · have hd' : D ≤ (24*(8192:ℝ)^R)*(Real.log (n:ℝ))^(4*R)*(n:ℝ)^(b+x) := by
      simpa only [overhead,mul_assoc] using hd.2
    have h := PhaseGeometry.poweredLogBound (4*R) hD
      (show 0 ≤ 24*(8192:ℝ)^R by positivity) hnpos.le
      (PhaseGeometry.one_le_log_nat n hn) (innerExponent_nonneg i hi) hd'
    simpa only [innerConstant,innerLogDegree,if_neg hi] using h

private theorem monomial_normalization (n : ℝ) (hn : 0 < n)
    (ell H CD x z ie : ℝ) (k r o p d : ℕ) :
    (8192*ell^k*n^eta)*(2*n^(1-b))*n^p*(H*n^z)^r*
      (4*H*n^(1+x/2))^o*(CD*ell^d*n^((b+x)*ie)) =
    (16384*H^(r+o)*4^o*CD)*ell^(k+d)*
      n^(eta+(1-b)+(p:ℝ)+(r:ℝ)*z+(o:ℝ)*(1+x/2)+(b+x)*ie) := by
  have hn0 := hn.le
  simp only [mul_pow]
  rw [←Real.rpow_natCast n p,←Real.rpow_mul_natCast hn0 z r,
    ←Real.rpow_mul_natCast hn0 (1+x/2) o]
  rw [pow_add H r o,pow_add ell k d]
  rw [show eta+(1-b)+(p:ℝ)+(r:ℝ)*z+(o:ℝ)*(1+x/2)+(b+x)*ie=
    (((eta+(1-b))+(p:ℝ))+(z*(r:ℝ)))+((1+x/2)*(o:ℝ))+(b+x)*ie by ring]
  simp only [Real.rpow_add hn]
  ring

/-- Insert all rounded dimensions and candidate counts, with separate
hypotheses for genuine geometric size bounds, not for an algorithm runtime. -/
theorem rawTerm_bound (n : ℕ) (hn : 3 ≤ n) (P B N D q x z : ℝ)
    (hP : 0 ≤ P) (hB : 0 ≤ B) (hN : 0 ≤ N) (hD : 0 ≤ D) (hq : 0 ≤ q)
    (hp : P ≤ 8192*(Real.log (n:ℝ))^4*(n:ℝ)^eta)
    (hb : B ≤ 2*(n:ℝ)^(1-b))
    (hnOuter : N ≤ 4*overhead n*(n:ℝ)^(1+x/2))
    (hd : (n:ℝ)^(b+x) ≤ D ∧ D ≤ 24*overhead n*(n:ℝ)^(b+x))
    (hc : q ≤ overhead n*(n:ℝ)^z) (i : Fin 7) :
    P*B*rawTerm n N D q i ≤ phaseConstant i*(Real.log (n:ℝ))^(phaseLogDegree i)*
      (n:ℝ)^(3-saving x z i) := by
  have hnpos : 0 < (n:ℝ) := by exact_mod_cast (show 0<n by omega)
  have hinner := inner_power_bound n hn D x hD hd i
  rw [rawTerm_canonical]
  calc
    _ = P*B*(n:ℝ)^(pairDegree i)*q^(cyclicDegree i)*N^(outerDegree i)*D^(innerExponent i) := by ring
    _ ≤ (8192*(Real.log (n:ℝ))^4*(n:ℝ)^eta)*(2*(n:ℝ)^(1-b))*(n:ℝ)^(pairDegree i)*
        (overhead n*(n:ℝ)^z)^(cyclicDegree i)*
        (4*overhead n*(n:ℝ)^(1+x/2))^(outerDegree i)*
        (innerConstant i*(Real.log (n:ℝ))^(innerLogDegree i)*
          (n:ℝ)^((b+x)*innerExponent i)) := by
      have hpb := mul_le_mul hp hb hB (hP.trans hp)
      have hpair := mul_le_mul_of_nonneg_right hpb (pow_nonneg (Nat.cast_nonneg n) (pairDegree i))
      have hqpow := pow_le_pow_left₀ hq hc (cyclicDegree i)
      have hNpow := pow_le_pow_left₀ hN hnOuter (outerDegree i)
      have hpair0 := mul_nonneg (mul_nonneg hP hB) (pow_nonneg (Nat.cast_nonneg n) (pairDegree i))
      have hqp := mul_le_mul hpair hqpow (pow_nonneg hq _) (hpair0.trans hpair)
      have hqp0 := mul_nonneg hpair0 (pow_nonneg hq (cyclicDegree i))
      have hnp := mul_le_mul hqp hNpow (pow_nonneg hN _) (hqp0.trans hqp)
      have hnp0 := mul_nonneg hqp0 (pow_nonneg hN (outerDegree i))
      exact mul_le_mul hnp hinner (Real.rpow_nonneg hD _) (hnp0.trans hnp)
    _ = _ := by
      rw [monomial_normalization (n:ℝ) hnpos,degree_exponent_identity]
      unfold overhead phaseConstant phaseLogDegree
      rw [mul_pow,pow_mul,pow_add,pow_add]
      ring

#print axioms rawTerm_canonical
#print axioms innerExponent_nonneg
#print axioms degree_exponent_identity
#print axioms inner_power_bound
#print axioms rawTerm_bound
end
end ThinMatrix.HalfSourceRawCosts
