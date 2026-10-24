import HalfSourcePhaseCosts

/-! All 61 strict real inequalities in the canonical exact-half numerical
certificate. The finite logarithm sums are kernel checked in the parameters
module, including their analytic tails. This is an arithmetic/analytic
certificate, not a theorem about an unconnected algorithm's runtime. -/
namespace ThinMatrix.HalfSourceCertificate
open HalfSourceParameters HalfSourcePhaseCosts
open scoped BigOperators
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

def rhot : ℝ := (1/2-theta)/(c-1)
def gammaPrime : ℝ := -Real.log ((1-rhot)/rhot)/((c-1)*Real.log 4)
def sourceDerivative : ℝ := 2*Real.log ((1-theta)/theta)/Real.log 4+
  zeta*gammaPrime/(2*gamt*gamt)

theorem sourceDerivative_positive : 0 < sourceDerivative := by
  have hg := gamtEnclosure
  have ht := logThetaRatio
  have hr := logRhotRatio
  have hg0 : 0 < gamt := by linarith [hg.1]
  have hc0 : 0 < c-1 := by norm_num [c]
  have hl4 : 0 < Real.log 4 := Real.log_pos (by norm_num)
  have ht0 : 0 < Real.log ((1-theta)/theta) := by
    norm_num [theta] at *
    linarith [ht.1]
  have hg2 : (134778033927/1000000000000:ℝ)^2 < gamt^2 := by
    nlinarith [hg.1]
  have hproduct : (134778033927/1000000000000:ℝ)^2*
      Real.log ((1-theta)/theta) < gamt^2*Real.log ((1-theta)/theta) :=
    mul_lt_mul_of_pos_right hg2 ht0
  have hnum : 0 < 4*(c-1)*gamt^2*Real.log ((1-theta)/theta)-
      zeta*Real.log ((1-rhot)/rhot) := by
    norm_num [c,theta,rhot,zeta] at *
    nlinarith only [hproduct,ht.1,hr.2]
  have he : sourceDerivative =
      (4*(c-1)*gamt^2*Real.log ((1-theta)/theta)-zeta*Real.log ((1-rhot)/rhot))/
        (2*(c-1)*Real.log 4*gamt^2) := by
    unfold sourceDerivative gammaPrime
    field_simp
    ring
  rw [he]
  exact div_pos hnum (by positivity)

def regimes (i : Fin 19) : ℝ :=
  ![(861/500:ℝ)-1,15-(861/500:ℝ),(861/500:ℝ),15-1,
    alpha,beta,c-5,theta,1/2-theta,
    (1/2)/(c-1),1/2-(1/2)/(c-1),zeta,suffix-zeta,
    1/2-2*theta,G,(S:ℝ),((R-S-1:ℕ):ℝ),1-b,1/2-2*theta] i

theorem regimes_positive (i : Fin 19) : 0 < regimes i := by
  have hs := suffix_fit
  have hg := GEnclosure
  fin_cases i <;> norm_num [regimes,c,theta,b,alpha,beta,zeta,R,S] at * <;> linarith

def cwMargin (i : Fin 3) : ℝ := CWTargetMarginals.entropy i+
  (4000/75249:ℝ)*(167220001/10000000:ℝ)*Real.log 16-Real.log 18

theorem cwMargin_positive (i : Fin 3) : 0 < cwMargin i := by
  have h := CW_allowance i
  unfold cwMargin
  linarith

def phaseMargin (p : Fin 4) (i : Fin 9) : ℝ :=
  ![batchFit (endpointX p) (endpointZ p),
    saving (endpointX p) (endpointZ p) 0-delta,
    saving (endpointX p) (endpointZ p) 1-delta,
    saving (endpointX p) (endpointZ p) 2-delta,
    saving (endpointX p) (endpointZ p) 3-delta,
    saving (endpointX p) (endpointZ p) 4-delta,
    saving (endpointX p) (endpointZ p) 5-delta,
    saving (endpointX p) (endpointZ p) 6-delta,
    geometry (endpointX p)] i

theorem phaseMargin_positive (p : Fin 4) (i : Fin 9) : 0 < phaseMargin p i := by
  have hb := endpointBatchFit p
  have hg := endpointGeometry p
  have h0 := endpointMargins p 0; have h1 := endpointMargins p 1
  have h2 := endpointMargins p 2; have h3 := endpointMargins p 3
  have h4 := endpointMargins p 4; have h5 := endpointMargins p 5
  have h6 := endpointMargins p 6
  have hs := slack_pos
  fin_cases i <;> norm_num [phaseMargin] <;> linarith

def checks : List ℝ :=
  List.ofFn cwMargin ++ [sourceDerivative] ++ List.ofFn regimes ++
    [3,b-eta-delta] ++ (List.ofFn (fun p : Fin 4 => List.ofFn (phaseMargin p))).flatten

theorem checkCount : checks.length=61 := by
  norm_num [checks,List.ofFn_succ]

theorem all61 : ∀ x ∈ checks, 0 < x := by
  intro x hx
  simp only [checks,List.mem_append,List.mem_cons,List.not_mem_nil,
    or_false,List.mem_ofFn,List.mem_flatten] at hx
  rcases hx with (((h | h) | h) | h) | h
  · obtain ⟨i,rfl⟩ := h
    exact cwMargin_positive i
  · subst x
    exact sourceDerivative_positive
  · obtain ⟨i,rfl⟩ := h
    exact regimes_positive i
  · rcases h with rfl | rfl
    · norm_num
    · have h := bookkeepingMargin
      linarith [slack_pos]
  · obtain ⟨l,⟨p,rfl⟩,hi⟩ := h
    obtain ⟨i,rfl⟩ := List.mem_ofFn.mp hi
    exact phaseMargin_positive p i

theorem exactWitnessIdentities :
    u+v=b ∧ e=b+u ∧ (R:ℝ)*eta=b ∧ (S:ℝ)*eta=u ∧
    3-delta=14963431313/5000000000 ∧
    (4000/75249:ℝ)=16/((16+2)*(15+861/500)) ∧
    alpha=861/500-1+beta ∧ 0 < (1/10000000:ℝ) := by
  norm_num [u,v,b,e,eta,R,S,delta,alpha,beta]

#print axioms sourceDerivative_positive
#print axioms regimes_positive
#print axioms cwMargin_positive
#print axioms phaseMargin_positive
#print axioms checkCount
#print axioms all61
#print axioms exactWitnessIdentities
end
end ThinMatrix.HalfSourceCertificate
