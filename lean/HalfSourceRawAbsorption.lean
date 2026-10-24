import HalfSourceComputedCosts
import GraphHalfSourceOutputCost

namespace ThinMatrix.HalfSourceRawAbsorption
open HalfSourceParameters HalfSourceRawCosts
open scoped BigOperators
set_option autoImplicit false
set_option maxHeartbeats 2000000
noncomputable section

def total (n N D q B : ℝ) : ℝ := B*∑ i : Fin 7,rawTerm n N D q i

theorem total_eq (n N D q B : ℝ) : total n N D q B=
    B*(q*N^2*D^(-G)+n^2*q*D^q1+n^2*D^q2+q*N*D^E+q*N*D^Ebox+q*N*D^Eroot+q*N*D) := by
  simp only[total,Fin.sum_univ_succ,Fin.sum_univ_zero,rawTerm,Matrix.cons_val_zero,Matrix.cons_val_succ]
  ring

theorem term_le (n N D q B : ℝ) (hN : 0 ≤ N) (hD : 0 ≤ D) (hq : 0 ≤ q) (hB : 0 ≤ B) (i : Fin 7) :
    B*rawTerm n N D q i ≤ total n N D q B := by
  apply mul_le_mul_of_nonneg_left _ hB
  exact Finset.single_le_sum (fun j _=>rawTerm_nonneg n N D q hN hD hq j) (Finset.mem_univ i)

theorem nonneg (n N D q B : ℝ) (hN : 0 ≤ N) (hD : 0 ≤ D) (hq : 0 ≤ q) (hB : 0 ≤ B) :
    0 ≤ total n N D q B := mul_nonneg hB (Finset.sum_nonneg (fun i _=>rawTerm_nonneg n N D q hN hD hq i))

 theorem source (n N D q B : ℝ) (hN : 0 ≤ N) (hD : 0 ≤ D) (hq : 0 ≤ q) (hB : 0 ≤ B) :
    B*(q*N^2*D^(-G)+q*N*D^E+q*N*D^Eroot+q*N*D) ≤ total n N D q B := by
  rw[total_eq]
  have h1 : 0 ≤ B*(n^2*q*D^q1) := by positivity
  have h2 : 0 ≤ B*(n^2*D^q2) := by positivity
  have h3 : 0 ≤ B*(q*N*D^Ebox) := by positivity
  nlinarith only[h1,h2,h3]

theorem low (n N D q B : ℝ) (hN : 1 ≤ N) (hD : 1 ≤ D) (hq : 1 ≤ q) (hB : 1 ≤ B) :
    B*q*((3*n^2)*D^q1+N*D^E)+D ≤ 3*total n N D q B := by
  have ht1 := term_le n N D q B (by linarith) (by linarith) (by linarith) (by linarith) 1
  have ht3 := term_le n N D q B (by linarith) (by linarith) (by linarith) (by linarith) 3
  have ht6 := term_le n N D q B (by linarith) (by linarith) (by linarith) (by linarith) 6
  have hc : D ≤ B*q*N*D := by
    have hm : 1 ≤ B*q*N := by
      have hh : 1 ≤ B*q := by nlinarith[mul_nonneg (sub_nonneg.mpr hB) (sub_nonneg.mpr hq)]
      nlinarith[mul_nonneg (sub_nonneg.mpr hh) (sub_nonneg.mpr hN)]
    nlinarith only[mul_le_mul_of_nonneg_right hm (show 0 ≤ D by linarith)]
  rw[total_eq]
  have hb : 0 ≤ B*q*N^2*D^(-G) := by positivity
  have h2 : 0 ≤ B*n^2*D^q2 := by positivity
  have h3 : 0 ≤ B*q*N*D^E := by positivity
  have h4 : 0 ≤ B*q*N*D^Ebox := by positivity
  have h5 : 0 ≤ B*q*N*D^Eroot := by positivity
  have h6 : 0 ≤ B*q*N*D := by positivity
  nlinarith only[hc,hb,h2,h3,h4,h5,h6]

 theorem high (n N D q B : ℝ) (hN : 0 ≤ N) (hD : 0 ≤ D) (hq : 1 ≤ q) (hB : 0 ≤ B) :
    B*(q*N^2*D^(-G)+q*N*D^Ebox+(3*n^2)*D^q2) ≤ 3*total n N D q B := by
  rw[total_eq]
  have hb : 0 ≤ B*q*N^2*D^(-G) := by positivity
  have h1 : 0 ≤ B*n^2*q*D^q1 := by positivity
  have h3 : 0 ≤ B*q*N*D^E := by positivity
  have h4 : 0 ≤ B*q*N*D^Ebox := by positivity
  have h5 : 0 ≤ B*q*N*D^Eroot := by positivity
  have h6 : 0 ≤ B*q*N*D := by positivity
  nlinarith only[hb,h1,h3,h4,h5,h6]

 theorem target (n N D q B : ℝ) (hN : 0 ≤ N) (hD : 0 ≤ D) (hq : 1 ≤ q) (hB : 1 ≤ B) :
    B*(N*D^E+N^2*D^(-G))+(3*n^2)*D^q2 ≤ 3*total n N D q B := by
  have hE := mul_le_mul_of_nonneg_left hq (show 0 ≤ B*N*D^E by positivity)
  have hG := mul_le_mul_of_nonneg_left hq (show 0 ≤ B*N^2*D^(-G) by positivity)
  have hBq := mul_le_mul_of_nonneg_right hB (show 0 ≤ (3*n^2)*D^q2 by positivity)
  have hv := source n N D q B hN hD (by linarith) (by linarith)
  have hq2 := term_le n N D q B hN hD (by linarith) (by linarith) 2
  norm_num[rawTerm] at hq2
  rw[total_eq]
  have h1 : 0 ≤ B*n^2*q*D^q1 := by positivity
  have h3 : 0 ≤ B*q*N*D^E := by positivity
  have h4 : 0 ≤ B*q*N*D^Ebox := by positivity
  have h5 : 0 ≤ B*q*N*D^Eroot := by positivity
  have h6 : 0 ≤ B*q*N*D := by positivity
  have h0 : 0 ≤ B*q*N^2*D^(-G) := by positivity
  nlinarith only[hE,hG,hBq,h1,h3,h4,h5,h6,h0]

 theorem writes (n N D q B : ℝ) (hn : 1 ≤ n) (hN : 0 ≤ N) (hD : 1 ≤ D) (hq : 1 ≤ q) (hB : 1 ≤ B) :
    3*n^2*B+1 ≤ 4*total n N D q B := by
  have hex : 0 ≤ q1 := by unfold q1 beta zeta;linarith[QEnclosure.1]
  have hd : 1 ≤ D^q1 := Real.one_le_rpow hD hex
  have hq' : 1 ≤ q*D^q1 := by nlinarith[mul_nonneg (sub_nonneg.mpr hq) (sub_nonneg.mpr hd)]
  have hbn : 1 ≤ B*n^2 := by
    have hh : 1 ≤ n^2 := one_le_pow₀ hn
    nlinarith[mul_nonneg (sub_nonneg.mpr hB) (sub_nonneg.mpr hh)]
  have hp := mul_le_mul_of_nonneg_left hq' (show 0 ≤ B*n^2 by positivity)
  have ht := term_le n N D q B hN (by linarith) (by linarith) (by linarith) 1
  norm_num[rawTerm] at ht
  nlinarith only[hp,ht,hbn]

#print axioms total_eq
#print axioms term_le
#print axioms nonneg
#print axioms source
#print axioms low
#print axioms high
#print axioms target
#print axioms writes
end
end ThinMatrix.HalfSourceRawAbsorption
