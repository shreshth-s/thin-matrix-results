import RealCertificate
import CWEntropyCertificate

/-! Actual logarithm and entropy bounds for the exact-half witness.
Finite atanh sums carry proved tails. Numerical endpoints are rational data,
recomputed by the Lean kernel; this module makes no algorithm-runtime claim. -/
namespace ThinMatrix.HalfSourceParameters
open scoped BigOperators
noncomputable section
set_option maxRecDepth 100000
set_option maxHeartbeats 16000000

def c : ℝ := 521145161597409/50000000000000
def theta : ℝ := 6568406426999/100000000000000
def b : ℝ := 244204721/5000000000
def eta : ℝ := 244204721/500000000000000000000000
def u : ℝ := 18749336972224883781997/500000000000000000000000
def v : ℝ := 5671135127775116218003/500000000000000000000000
def e : ℝ := 43169809072224883781997/500000000000000000000000
def delta : ℝ := 36568687/5000000000
def zeta : ℝ := 11/50
def alpha : ℝ := 3610001/5000000
def beta : ℝ := 1/5000000
def R : ℕ := 100000000000000
def S : ℕ := 76777127384957
abbrev entropy := RealCertificate.entropy

theorem logC : (-2344005618625841/1000000000000000:ℝ) < Real.log (50000000000000/521145161597409:ℝ) ∧
    Real.log (50000000000000/521145161597409:ℝ) < (-586001404656459/250000000000000:ℝ) := by
  have h := RealCertificate.atanhLogBounds (278854838402591/1321145161597409:ℝ) (by norm_num) (by norm_num) 20
  have hq : (8571662072278849/20000000000000000:ℝ) ≤ Real.log (800000000000000/521145161597409:ℝ) ∧
      Real.log (800000000000000/521145161597409:ℝ) ≤ (171433241445577/400000000000000:ℝ) := by
    norm_num [Finset.sum_range_succ] at h ⊢
    constructor <;> linarith [h.1,h.2]
  have h2 := RealCertificate.logTwo
  have he := Real.log_mul (by positivity : (2:ℝ)^4≠0)
    (by norm_num : (50000000000000/521145161597409:ℝ)≠0)
  rw [Real.log_pow] at he
  norm_num at he h2 ⊢
  constructor <;> linarith [hq.1,hq.2,h2.1,h2.2]

theorem logCComp : (-50431189400213/500000000000000:ℝ) < Real.log (471145161597409/521145161597409:ℝ) ∧
    Real.log (471145161597409/521145161597409:ℝ) < (-100862378800421/1000000000000000:ℝ) := by
  have h := RealCertificate.atanhLogBounds (421145161597409/1463435484792227:ℝ) (by norm_num) (by norm_num) 20
  have hq : (59228480175952209/100000000000000000:ℝ) ≤ Real.log (942290323194818/521145161597409:ℝ) ∧
      Real.log (942290323194818/521145161597409:ℝ) ≤ (29614240087976107/50000000000000000:ℝ) := by
    norm_num [Finset.sum_range_succ] at h ⊢
    constructor <;> linarith [h.1,h.2]
  have h2 := RealCertificate.logTwo
  have he := Real.log_mul (by positivity : (2:ℝ)^1≠0)
    (by norm_num : (471145161597409/521145161597409:ℝ)≠0)
  rw [Real.log_pow] at he
  norm_num at he h2 ⊢
  constructor <;> linarith [hq.1,hq.2,h2.1,h2.2]

theorem logD : (-602986563905893/250000000000000:ℝ) < Real.log (93431593573001/1042290323194818:ℝ) ∧
    Real.log (93431593573001/1042290323194818:ℝ) < (-2411946255623567/1000000000000000:ℝ) := by
  have h := RealCertificate.atanhLogBounds (226307586986599/1268597910181417:ℝ) (by norm_num) (by norm_num) 20
  have hq : (7212849332324229/20000000000000000:ℝ) ≤ Real.log (747452748584008/521145161597409:ℝ) ∧
      Real.log (747452748584008/521145161597409:ℝ) ≤ (721284933232423/2000000000000000:ℝ) := by
    norm_num [Finset.sum_range_succ] at h ⊢
    constructor <;> linarith [h.1,h.2]
  have h2 := RealCertificate.logTwo
  have he := Real.log_mul (by positivity : (2:ℝ)^4≠0)
    (by norm_num : (93431593573001/1042290323194818:ℝ)≠0)
  rw [Real.log_pow] at he
  norm_num at he h2 ⊢
  constructor <;> linarith [hq.1,hq.2,h2.1,h2.2]

theorem logDComp : (-9391587944357/100000000000000:ℝ) < Real.log (948858729621817/1042290323194818:ℝ) ∧
    Real.log (948858729621817/1042290323194818:ℝ) < (-18783175888713/200000000000000:ℝ) := by
  have h := RealCertificate.atanhLogBounds (213856784012204/735001945609613:ℝ) (by norm_num) (by norm_num) 20
  have hq : (14980782527909443/25000000000000000:ℝ) ≤ Real.log (948858729621817/521145161597409:ℝ) ∧
      Real.log (948858729621817/521145161597409:ℝ) ≤ (59923130111637777/100000000000000000:ℝ) := by
    norm_num [Finset.sum_range_succ] at h ⊢
    constructor <;> linarith [h.1,h.2]
  have h2 := RealCertificate.logTwo
  have he := Real.log_mul (by positivity : (2:ℝ)^1≠0)
    (by norm_num : (948858729621817/1042290323194818:ℝ)≠0)
  rw [Real.log_pow] at he
  norm_num at he h2 ⊢
  constructor <;> linarith [hq.1,hq.2,h2.1,h2.2]

theorem logTheta : (-680724733970123/250000000000000:ℝ) < Real.log (6568406426999/100000000000000:ℝ) ∧
    Real.log (6568406426999/100000000000000:ℝ) < (-2722898935880487/1000000000000000:ℝ) := by
  have h := RealCertificate.atanhLogBounds (318406426999/12818406426999:ℝ) (by norm_num) (by norm_num) 20
  have hq : (2484489317964579/50000000000000000:ℝ) ≤ Real.log (6568406426999/6250000000000:ℝ) ∧
      Real.log (6568406426999/6250000000000:ℝ) ≤ (4968978635929163/100000000000000000:ℝ) := by
    norm_num [Finset.sum_range_succ] at h ⊢
    constructor <;> linarith [h.1,h.2]
  have h2 := RealCertificate.logTwo
  have he := Real.log_mul (by positivity : (2:ℝ)^4≠0)
    (by norm_num : (6568406426999/100000000000000:ℝ)≠0)
  rw [Real.log_pow] at he
  norm_num at he h2 ⊢
  constructor <;> linarith [hq.1,hq.2,h2.1,h2.2]

theorem logThetaComp : (-33970318498867/500000000000000:ℝ) < Real.log (93431593573001/100000000000000:ℝ) ∧
    Real.log (93431593573001/100000000000000:ℝ) < (-67940636997729/1000000000000000:ℝ) := by
  have h := RealCertificate.atanhLogBounds (43431593573001/143431593573001:ℝ) (by norm_num) (by norm_num) 20
  have hq : (15630163589055357/25000000000000000:ℝ) ≤ Real.log (93431593573001/50000000000000:ℝ) ∧
      Real.log (93431593573001/50000000000000:ℝ) ≤ (62520654356221433/100000000000000000:ℝ) := by
    norm_num [Finset.sum_range_succ] at h ⊢
    constructor <;> linarith [h.1,h.2]
  have h2 := RealCertificate.logTwo
  have he := Real.log_mul (by positivity : (2:ℝ)^1≠0)
    (by norm_num : (93431593573001/100000000000000:ℝ)≠0)
  rw [Real.log_pow] at he
  norm_num at he h2 ⊢
  constructor <;> linarith [hq.1,hq.2,h2.1,h2.2]

theorem logRho : (-2936290420385363/1000000000000000:ℝ) < Real.log (25000000000000/471145161597409:ℝ) ∧
    Real.log (25000000000000/471145161597409:ℝ) < (-1468145210192679/500000000000000:ℝ) := by
  have h := RealCertificate.atanhLogBounds (328854838402591/1271145161597409:ℝ) (by norm_num) (by norm_num) 20
  have hq : (10588909648287313/20000000000000000:ℝ) ≤ Real.log (800000000000000/471145161597409:ℝ) ∧
      Real.log (800000000000000/471145161597409:ℝ) ≤ (5294454824143657/10000000000000000:ℝ) := by
    norm_num [Finset.sum_range_succ] at h ⊢
    constructor <;> linarith [h.1,h.2]
  have h2 := RealCertificate.logTwo
  have he := Real.log_mul (by positivity : (2:ℝ)^5≠0)
    (by norm_num : (25000000000000/471145161597409:ℝ)≠0)
  rw [Real.log_pow] at he
  norm_num at he h2 ⊢
  constructor <;> linarith [hq.1,hq.2,h2.1,h2.2]

theorem logRhoComp : (-54521871755161/1000000000000000:ℝ) < Real.log (446145161597409/471145161597409:ℝ) ∧
    Real.log (446145161597409/471145161597409:ℝ) < (-13630467938789/250000000000000:ℝ) := by
  have h := RealCertificate.atanhLogBounds (421145161597409/1363435484792227:ℝ) (by norm_num) (by norm_num) 20
  have hq : (1596563272011967/2500000000000000:ℝ) ≤ Real.log (892290323194818/471145161597409:ℝ) ∧
      Real.log (892290323194818/471145161597409:ℝ) ≤ (12772506176095737/20000000000000000:ℝ) := by
    norm_num [Finset.sum_range_succ] at h ⊢
    constructor <;> linarith [h.1,h.2]
  have h2 := RealCertificate.logTwo
  have he := Real.log_mul (by positivity : (2:ℝ)^1≠0)
    (by norm_num : (446145161597409/471145161597409:ℝ)≠0)
  rw [Real.log_pow] at he
  norm_num at he h2 ⊢
  constructor <;> linarith [hq.1,hq.2,h2.1,h2.2]

theorem logRhot : (-769281571757949/250000000000000:ℝ) < Real.log (43431593573001/942290323194818:ℝ) ∧
    Real.log (43431593573001/942290323194818:ℝ) < (-3077126287031791/1000000000000000:ℝ) := by
  have h := RealCertificate.atanhLogBounds (223760335570607/1166050658765425:ℝ) (by norm_num) (by norm_num) 20
  have hq : (19430480788396643/50000000000000000:ℝ) ≤ Real.log (694905497168016/471145161597409:ℝ) ∧
      Real.log (694905497168016/471145161597409:ℝ) ≤ (38860961576793291/100000000000000000:ℝ) := by
    norm_num [Finset.sum_range_succ] at h ⊢
    constructor <;> linarith [h.1,h.2]
  have h2 := RealCertificate.logTwo
  have he := Real.log_mul (by positivity : (2:ℝ)^5≠0)
    (by norm_num : (43431593573001/942290323194818:ℝ)≠0)
  rw [Real.log_pow] at he
  norm_num at he h2 ⊢
  constructor <;> linarith [hq.1,hq.2,h2.1,h2.2]

theorem logRhotComp : (-11796886344671/250000000000000:ℝ) < Real.log (898858729621817/942290323194818:ℝ) ∧
    Real.log (898858729621817/942290323194818:ℝ) < (-47187545378679/1000000000000000:ℝ) := by
  have h := RealCertificate.atanhLogBounds (213856784012204/685001945609613:ℝ) (by norm_num) (by norm_num) 20
  have hq : (32297981759063173/50000000000000000:ℝ) ≤ Real.log (898858729621817/471145161597409:ℝ) ∧
      Real.log (898858729621817/471145161597409:ℝ) ≤ (64595963518126351/100000000000000000:ℝ) := by
    norm_num [Finset.sum_range_succ] at h ⊢
    constructor <;> linarith [h.1,h.2]
  have h2 := RealCertificate.logTwo
  have he := Real.log_mul (by positivity : (2:ℝ)^1≠0)
    (by norm_num : (898858729621817/942290323194818:ℝ)≠0)
  rw [Real.log_pow] at he
  norm_num at he h2 ⊢
  constructor <;> linarith [hq.1,hq.2,h2.1,h2.2]

theorem logSuffix : (-324110001105909/100000000000000:ℝ) < Real.log (18431593573001/471145161597409:ℝ) ∧
    Real.log (18431593573001/471145161597409:ℝ) < (-648220002211817/200000000000000:ℝ) := by
  have h := RealCertificate.atanhLogBounds (118665832738623/1060956155933441:ℝ) (by norm_num) (by norm_num) 20
  have hq : (22463589174063853/100000000000000000:ℝ) ≤ Real.log (589810994336032/471145161597409:ℝ) ∧
      Real.log (589810994336032/471145161597409:ℝ) ≤ (11231794587031929/50000000000000000:ℝ) := by
    norm_num [Finset.sum_range_succ] at h ⊢
    constructor <;> linarith [h.1,h.2]
  have h2 := RealCertificate.logTwo
  have he := Real.log_mul (by positivity : (2:ℝ)^5≠0)
    (by norm_num : (18431593573001/471145161597409:ℝ)≠0)
  rw [Real.log_pow] at he
  norm_num at he h2 ⊢
  constructor <;> linarith [hq.1,hq.2,h2.1,h2.2]

theorem logSuffixComp : (-38971308519/976562500000:ℝ) < Real.log (452713568024408/471145161597409:ℝ) ∧
    Real.log (452713568024408/471145161597409:ℝ) < (-39906619923451/1000000000000000:ℝ) := by
  have h := RealCertificate.atanhLogBounds (434281974451407/1376572297646225:ℝ) (by norm_num) (by norm_num) 20
  have hq : (1020688375994519/1562500000000000:ℝ) ≤ Real.log (905427136048816/471145161597409:ℝ) ∧
      Real.log (905427136048816/471145161597409:ℝ) ≤ (65324056063649221/100000000000000000:ℝ) := by
    norm_num [Finset.sum_range_succ] at h ⊢
    constructor <;> linarith [h.1,h.2]
  have h2 := RealCertificate.logTwo
  have he := Real.log_mul (by positivity : (2:ℝ)^1≠0)
    (by norm_num : (452713568024408/471145161597409:ℝ)≠0)
  rw [Real.log_pow] at he
  norm_num at he h2 ⊢
  constructor <;> linarith [hq.1,hq.2,h2.1,h2.2]

theorem logThree : (1098612288668107/1000000000000000:ℝ) < Real.log (3:ℝ) ∧
    Real.log (3:ℝ) < (68663268041757/62500000000000:ℝ) := by
  have h := RealCertificate.atanhLogBounds (1/5:ℝ) (by norm_num) (by norm_num) 20
  have hq : (10136627702704109/25000000000000000:ℝ) ≤ Real.log (3/2:ℝ) ∧
      Real.log (3/2:ℝ) ≤ (40546510810816441/100000000000000000:ℝ) := by
    norm_num [Finset.sum_range_succ] at h ⊢
    constructor <;> linarith [h.1,h.2]
  have h2 := RealCertificate.logTwo
  have he := Real.log_mul (by positivity : (2:ℝ)^1≠0)
    (by norm_num : (3/2:ℝ)≠0)
  rw [Real.log_pow] at he
  norm_num at he h2 ⊢
  constructor <;> linarith [hq.1,hq.2,h2.1,h2.2]

theorem logThetaRatio : (663739574720689/250000000000000:ℝ) < Real.log (93431593573001/6568406426999:ℝ) ∧
    Real.log (93431593573001/6568406426999:ℝ) < (2654958298882761/1000000000000000:ℝ) := by
  have h := RealCertificate.atanhLogBounds (40884342157009/145978844988993:ℝ) (by norm_num) (by norm_num) 20
  have hq : (14387918930073067/25000000000000000:ℝ) ≤ Real.log (93431593573001/52547251415992:ℝ) ∧
      Real.log (93431593573001/52547251415992:ℝ) ≤ (57551675720292273/100000000000000000:ℝ) := by
    norm_num [Finset.sum_range_succ] at h ⊢
    constructor <;> linarith [h.1,h.2]
  have h2 := RealCertificate.logTwo
  have he := Real.log_mul (by positivity : (2:ℝ)^3≠0)
    (by norm_num : (93431593573001/52547251415992:ℝ)≠0)
  rw [Real.log_pow] at he
  norm_num at he h2 ⊢
  constructor <;> linarith [hq.1,hq.2,h2.1,h2.2]

theorem logRhotRatio : (3029938741653109/1000000000000000:ℝ) < Real.log (898858729621817/43431593573001:ℝ) ∧
    Real.log (898858729621817/43431593573001:ℝ) < (1514969370826557/500000000000000:ℝ) := by
  have h := RealCertificate.atanhLogBounds (203953232453801/1593764226789833:ℝ) (by norm_num) (by norm_num) 20
  have hq : (12867500970666529/50000000000000000:ℝ) ≤ Real.log (898858729621817/694905497168016:ℝ) ∧
      Real.log (898858729621817/694905497168016:ℝ) ≤ (25735001941333063/100000000000000000:ℝ) := by
    norm_num [Finset.sum_range_succ] at h ⊢
    constructor <;> linarith [h.1,h.2]
  have h2 := RealCertificate.logTwo
  have he := Real.log_mul (by positivity : (2:ℝ)^4≠0)
    (by norm_num : (898858729621817/694905497168016:ℝ)≠0)
  rw [Real.log_pow] at he
  norm_num at he h2 ⊢
  constructor <;> linarith [hq.1,hq.2,h2.1,h2.2]

theorem entropyC : (3160752796503/10000000000000:ℝ) < entropy (1/c) ∧
    entropy (1/c) < (6321505593007/20000000000000:ℝ) := by
  have h0 := logC; have h1 := logCComp
  unfold entropy RealCertificate.entropy
  norm_num [c,theta] at h0 h1 ⊢
  constructor <;> linarith [h0.1,h0.2,h1.1,h1.2]

theorem entropyD : (942830170903/3125000000000:ℝ) < entropy ((1-theta)/c) ∧
    entropy ((1-theta)/c) < (30170565468901/100000000000000:ℝ) := by
  have h0 := logD; have h1 := logDComp
  unfold entropy RealCertificate.entropy
  norm_num [c,theta] at h0 h1 ⊢
  constructor <;> linarith [h0.1,h0.2,h1.1,h1.2]

theorem entropyTheta : (12116454426783/50000000000000:ℝ) < entropy (theta) ∧
    entropy (theta) < (24232908853571/100000000000000:ℝ) := by
  have h0 := logTheta; have h1 := logThetaComp
  unfold entropy RealCertificate.entropy
  norm_num [c,theta] at h0 h1 ⊢
  constructor <;> linarith [h0.1,h0.2,h1.1,h1.2]

theorem entropyRho : (20743485821453/100000000000000:ℝ) < entropy ((1/2)/(c-1)) ∧
    entropy ((1/2)/(c-1)) < (10371742910729/50000000000000:ℝ) := by
  have h0 := logRho; have h1 := logRhoComp
  unfold entropy RealCertificate.entropy
  norm_num [c,theta] at h0 h1 ⊢
  constructor <;> linarith [h0.1,h0.2,h1.1,h1.2]

theorem entropyRhot : (18684202843903/100000000000000:ℝ) < entropy ((1/2-theta)/(c-1)) ∧
    entropy ((1/2-theta)/(c-1)) < (4671050710977/25000000000000:ℝ) := by
  have h0 := logRhot; have h1 := logRhotComp
  unfold entropy RealCertificate.entropy
  norm_num [c,theta] at h0 h1 ⊢
  constructor <;> linarith [h0.1,h0.2,h1.1,h1.2]

theorem entropySuffix : (8256999409993/50000000000000:ℝ) < entropy ((1/2-2*theta)/(c-1)) ∧
    entropy ((1/2-2*theta)/(c-1)) < (16513998819991/100000000000000:ℝ) := by
  have h0 := logSuffix; have h1 := logSuffixComp
  unfold entropy RealCertificate.entropy
  norm_num [c,theta] at h0 h1 ⊢
  constructor <;> linarith [h0.1,h0.2,h1.1,h1.2]

def CK : ℝ := c*entropy (1/c)/Real.log 4
def T : ℝ := CK+c-1
def G : ℝ := (c*entropy (1/c)-c*entropy ((1-theta)/c)-theta*Real.log 4)/Real.log 2
def Q : ℝ := 2*entropy theta/Real.log 4
def q1 : ℝ := Q+beta*zeta
def q2 : ℝ := Q+2*theta
def gamma : ℝ := entropy ((1/2)/(c-1))/Real.log 4
def gamt : ℝ := entropy ((1/2-theta)/(c-1))/Real.log 4
def A : ℝ := 1/(2*gamt)-1-alpha
def E : ℝ := T+Q-A*zeta
def Ebox : ℝ := T-G
def Eroot : ℝ := 2*CK+(2*c-1)*Real.log 3/Real.log 4+Q-T
def suffix : ℝ := (c-1)*entropy ((1/2-2*theta)/(c-1))/Real.log 4

theorem TEnclosure : (2949831602939/250000000000:ℝ) < T ∧ T < (11799326411761/1000000000000:ℝ) := by
  have h0 := RealCertificate.logTwo
  have h1 := entropyC
  have hp : 0 < (2*Real.log 2) := by positivity
  have he : T = (c*entropy (1/c))/(2*Real.log 2)+(c-1) := by
    unfold T CK
    rw [RealCertificate.logFour]
    ring
  have hl : ((2949831602939/250000000000:ℝ)-(c-1))*(2*Real.log 2) < c*entropy (1/c) := by
    norm_num [c,theta] at *
    linarith
  have hh : c*entropy (1/c) < ((11799326411761/1000000000000:ℝ)-(c-1))*(2*Real.log 2) := by
    norm_num [c,theta] at *
    linarith
  rw [he]
  constructor
  · have := (lt_div_iff₀ hp).2 hl
    linarith
  · have := (div_lt_iff₀ hp).2 hh
    linarith

theorem GEnclosure : (42354469717/500000000000:ℝ) < G ∧ G < (84708939439/1000000000000:ℝ) := by
  have h0 := RealCertificate.logTwo
  have h1 := entropyC
  have h2 := entropyD
  have hp : 0 < Real.log 2 := by positivity
  have he : G = (c*entropy (1/c)-c*entropy ((1-theta)/c)-theta*(2*Real.log 2))/Real.log 2+(0) := by
    unfold G
    rw [RealCertificate.logFour]
    ring
  have hl : ((42354469717/500000000000:ℝ)-(0))*Real.log 2 < c*entropy (1/c)-c*entropy ((1-theta)/c)-theta*(2*Real.log 2) := by
    norm_num [c,theta] at *
    linarith
  have hh : c*entropy (1/c)-c*entropy ((1-theta)/c)-theta*(2*Real.log 2) < ((84708939439/1000000000000:ℝ)-(0))*Real.log 2 := by
    norm_num [c,theta] at *
    linarith
  rw [he]
  constructor
  · have := (lt_div_iff₀ hp).2 hl
    linarith
  · have := (div_lt_iff₀ hp).2 hh
    linarith

theorem QEnclosure : (349606974291/1000000000000:ℝ) < Q ∧ Q < (43700871787/125000000000:ℝ) := by
  have h0 := RealCertificate.logTwo
  have h1 := entropyTheta
  have hp : 0 < (2*Real.log 2) := by positivity
  have he : Q = (2*entropy theta)/(2*Real.log 2)+(0) := by
    unfold Q
    rw [RealCertificate.logFour]
    ring
  have hl : ((349606974291/1000000000000:ℝ)-(0))*(2*Real.log 2) < 2*entropy theta := by
    norm_num [c,theta] at *
    linarith
  have hh : 2*entropy theta < ((43700871787/125000000000:ℝ)-(0))*(2*Real.log 2) := by
    norm_num [c,theta] at *
    linarith
  rw [he]
  constructor
  · have := (lt_div_iff₀ hp).2 hl
    linarith
  · have := (div_lt_iff₀ hp).2 hh
    linarith

theorem gammaEnclosure : (9352038789/62500000000:ℝ) < gamma ∧ gamma < (149632620629/1000000000000:ℝ) := by
  have h0 := RealCertificate.logTwo
  have h1 := entropyRho
  have hp : 0 < (2*Real.log 2) := by positivity
  have he : gamma = (entropy ((1/2)/(c-1)))/(2*Real.log 2)+(0) := by
    unfold gamma
    rw [RealCertificate.logFour]
    ring
  have hl : ((9352038789/62500000000:ℝ)-(0))*(2*Real.log 2) < entropy ((1/2)/(c-1)) := by
    norm_num [c,theta] at *
    linarith
  have hh : entropy ((1/2)/(c-1)) < ((149632620629/1000000000000:ℝ)-(0))*(2*Real.log 2) := by
    norm_num [c,theta] at *
    linarith
  rw [he]
  constructor
  · have := (lt_div_iff₀ hp).2 hl
    linarith
  · have := (div_lt_iff₀ hp).2 hh
    linarith

theorem gamtEnclosure : (134778033927/1000000000000:ℝ) < gamt ∧ gamt < (33694508483/250000000000:ℝ) := by
  have h0 := RealCertificate.logTwo
  have h1 := entropyRhot
  have hp : 0 < (2*Real.log 2) := by positivity
  have he : gamt = (entropy ((1/2-theta)/(c-1)))/(2*Real.log 2)+(0) := by
    unfold gamt
    rw [RealCertificate.logFour]
    ring
  have hl : ((134778033927/1000000000000:ℝ)-(0))*(2*Real.log 2) < entropy ((1/2-theta)/(c-1)) := by
    norm_num [c,theta] at *
    linarith
  have hh : entropy ((1/2-theta)/(c-1)) < ((33694508483/250000000000:ℝ)-(0))*(2*Real.log 2) := by
    norm_num [c,theta] at *
    linarith
  rw [he]
  constructor
  · have := (lt_div_iff₀ hp).2 hl
    linarith
  · have := (div_lt_iff₀ hp).2 hh
    linarith

theorem suffixEnclosure : (1122487526583/1000000000000:ℝ) < suffix ∧ suffix < (280621881647/250000000000:ℝ) := by
  have h0 := RealCertificate.logTwo
  have h1 := entropySuffix
  have hp : 0 < (2*Real.log 2) := by positivity
  have he : suffix = ((c-1)*entropy ((1/2-2*theta)/(c-1)))/(2*Real.log 2)+(0) := by
    unfold suffix
    rw [RealCertificate.logFour]
    ring
  have hl : ((1122487526583/1000000000000:ℝ)-(0))*(2*Real.log 2) < (c-1)*entropy ((1/2-2*theta)/(c-1)) := by
    norm_num [c,theta] at *
    linarith
  have hh : (c-1)*entropy ((1/2-2*theta)/(c-1)) < ((280621881647/250000000000:ℝ)-(0))*(2*Real.log 2) := by
    norm_num [c,theta] at *
    linarith
  rw [he]
  constructor
  · have := (lt_div_iff₀ hp).2 hl
    linarith
  · have := (div_lt_iff₀ hp).2 hh
    linarith

theorem ErootEnclosure : (2257639110769/250000000000:ℝ) < Eroot ∧ Eroot < (9030556443081/1000000000000:ℝ) := by
  have h0 := RealCertificate.logTwo
  have h1 := entropyC
  have h2 := entropyTheta
  have h3 := logThree
  have hp : 0 < (2*Real.log 2) := by positivity
  have he : Eroot = (c*entropy (1/c)+(2*c-1)*Real.log 3+2*entropy theta)/(2*Real.log 2)+(-(c-1)) := by
    unfold Eroot T Q CK
    rw [RealCertificate.logFour]
    ring
  have hl : ((2257639110769/250000000000:ℝ)-(-(c-1)))*(2*Real.log 2) < c*entropy (1/c)+(2*c-1)*Real.log 3+2*entropy theta := by
    norm_num [c,theta] at *
    linarith
  have hh : c*entropy (1/c)+(2*c-1)*Real.log 3+2*entropy theta < ((9030556443081/1000000000000:ℝ)-(-(c-1)))*(2*Real.log 2) := by
    norm_num [c,theta] at *
    linarith
  rw [he]
  constructor
  · have := (lt_div_iff₀ hp).2 hl
    linarith
  · have := (div_lt_iff₀ hp).2 hh
    linarith

theorem AEnclosure : (9939015683/5000000000:ℝ) < A ∧ A < (19878031371/10000000000:ℝ) := by
  have hg := gamtEnclosure
  have hg0 : 0 < 2*gamt := by linarith [hg.1]
  have hl : ((9939015683/5000000000:ℝ)+1+alpha)*(2*gamt)<1 := by norm_num [alpha]; nlinarith [hg.2]
  have hh : 1<((19878031371/10000000000:ℝ)+1+alpha)*(2*gamt) := by norm_num [alpha]; nlinarith [hg.1]
  have h1 := (lt_div_iff₀ hg0).2 hl
  have h2 := (div_lt_iff₀ hg0).2 hh
  unfold A
  constructor <;> linarith

theorem suffix_fit : zeta < suffix := by
  have h := suffixEnclosure
  norm_num [zeta] at *
  linarith

theorem CW_allowance (axis : Fin 3) :
    Real.log 18 < CWTargetMarginals.entropy axis+
      (4000/75249:ℝ)*(167220001/10000000:ℝ)*Real.log 16 :=
  CWEntropyCertificate.marginal_margin axis

#print axioms TEnclosure
#print axioms GEnclosure
#print axioms QEnclosure
#print axioms gammaEnclosure
#print axioms gamtEnclosure
#print axioms AEnclosure
#print axioms ErootEnclosure
#print axioms suffix_fit
#print axioms CW_allowance
end
end ThinMatrix.HalfSourceParameters
