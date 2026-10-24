import GraphHighScalarSchedule
import HalfSourceHighQueryCost
import HalfSourceEmptyRootCost

/-! The actual scalar HIGH schedule includes routing once, every stored
band pair and all translation/degree runs. Empty pair work fits the box
charge; physical queries pay q2 without an extra cyclic modulus factor. -/
namespace ThinMatrix.HalfSourceHighScheduleCost
open HalfSourceParameters HalfSourceAdaptiveFamilyCost
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
noncomputable section

def width (K L m q : ℕ) := L+m+q.size+(K*K).size+10

theorem budget_polynomial (K L m t M A q : ℕ) :
    GraphHighScalarSchedule.budget K L m t M A ≤
      100000000*(width K L m q)^10*
        (K*K+1+M*(SelectedHighQueries.rowBudget L m t A+32)) := by
  let P := width K L m q
  let U := SelectedHighQueries.rowBudget L m t A+32
  have hP : 1 ≤ P := by dsimp[P,width];omega
  have hU : 1 ≤ U := by dsimp[U];omega
  have hr : GraphHighScalarSchedule.readBudget K ≤ 100*P^3 := by
    have hp2 : P^2 ≤ P^3 := Nat.pow_le_pow_right hP (by decide)
    have hh : GraphHighScalarSchedule.readBudget K ≤ 16*P^2+64*P^3 := by
      unfold GraphHighScalarSchedule.readBudget;gcongr <;> dsimp[P,width] <;> omega
    omega
  have hroute : GraphHighScalarSchedule.routeBudget K L m M ≤
      24*(K*K+1)+1000*M*P^3+36 := by
    have hp0 : 1 ≤ P^3 := one_le_pow₀ hP
    have hp2 : P^2 ≤ P^3 := Nat.pow_le_pow_right hP (by decide)
    have hh : 16*((K*K).size+1)^2+64*((K*K).size+1)^3+
      128*((K*K).size+L+m+1)^3+36 ≤ 1000*P^3 := by
      have h1 : 16*((K*K).size+1)^2+64*((K*K).size+1)^3+
          128*((K*K).size+L+m+1)^3+36 ≤ 16*P^2+192*P^3+36 := by
        calc
          _ ≤ 16*P^2+64*P^3+128*P^3+36 := by gcongr <;> dsimp[P,width] <;> omega
          _ = _ := by ring
      omega
    unfold GraphHighScalarSchedule.routeBudget
    nlinarith only [Nat.mul_le_mul_left M hh]
  have hj := HalfSourceRootFamilyCosts.multiplicity_bound m
  have hshape : m+1 ≤ P := by dsimp[P,width];omega
  have hmult : (ExactHalfSourcePlan.J m)^2*(2*m+1) ≤ 8192*P^7 := by
    change (ExactHalfSourcePlan.J m)^2*(2*m+1) ≤ _ at hj
    calc
      _ ≤ (64*(m+1)^3)^2*(2*m+1) := hj
      _ ≤ (64*P^3)^2*(2*P) := by gcongr;omega
      _ = _ := by ring
  have h3 : P^3 ≤ P^10 := Nat.pow_le_pow_right hP (by decide)
  have h7 : P^7 ≤ P^10 := Nat.pow_le_pow_right hP (by decide)
  have h0 : 1 ≤ P^10 := one_le_pow₀ hP
  have hread : GraphHighScalarSchedule.readBudget K+40*(ExactHalfSourcePlan.J m)^2*(2*m+1)+16 ≤ 400000*P^10 := by
    nlinarith only [hr,hmult,h3,h7,h0]
  have hmU : M ≤ M*U := by nlinarith only [hU]
  have hmul : M*(ExactHalfSourcePlan.J m)^2*(2*m+1)*U ≤ 8192*P^10*(M*U) := by
    calc
      _ = (M*U)*((ExactHalfSourcePlan.J m)^2*(2*m+1)) := by ring
      _ ≤ (M*U)*(8192*P^7) := Nat.mul_le_mul_left _ hmult
      _ ≤ (M*U)*(8192*P^10) := by gcongr
      _ = _ := by ring
  have hpair := Nat.mul_le_mul_left (K*K) hread
  have hquery := Nat.mul_le_mul_right (1000*P^10) hmU
  have hthree := Nat.mul_le_mul_left (1000*M) h3
  have hone := Nat.mul_le_mul_left (24*(K*K+1)+44) h0
  unfold GraphHighScalarSchedule.budget
  change _ ≤ 100000000*P^10*(K*K+1+M*U)
  change M*(ExactHalfSourcePlan.J m)^2*(2*m+1)*(SelectedHighQueries.rowBudget L m t A+32) ≤ _ at hmul
  nlinarith only [hroute,hpair,hmul,hquery,hthree,hone]

theorem band_pairs (N m : ℕ) (hm : 0 < m) (hfit : ThinProductCosts.gridSide (L m) m ≤ N) :
    (TilingCosts.bandCount N (ThinMatrixBackend.tileWidth (L m) m):ℝ)^2+1 ≤
      8*(N:ℝ)^2*(m+1:ℝ)*(((4:ℝ)^m)^(-G)) := by
  let K := TilingCosts.bandCount N (ThinMatrixBackend.tileWidth (L m) m)
  have hg : 1 ≤ (GoodMapEmbedding.goodSlots (L m) m).card := by
    have hc := Nat.choose_pos (OptimizedFoldedPlan.ordinaryLength_lower m)
    have hd := GoodMapEmbedding.goodSlots_density (L m) m
    dsimp only[L] at *
    omega
  have hH := HalfSourceRootFamilyCosts.channel_positive m hm
  have hle : K*K ≤ HalfSourceEmptyRootCost.count N m := by
    unfold HalfSourceEmptyRootCost.count
    change K*K ≤ K^2*(GoodMapEmbedding.goodSlots (L m) m).card^2*ResidualFamilyKeys.channelCount m (t m)
    nlinarith only [Nat.mul_le_mul_left (K^2) (one_le_mul (one_le_pow₀ hg (n:=2)) hH)]
  have hK : 1 ≤ K := by
    have ht := ThinMatrixBackend.tileWidth_pos (L m) m (OptimizedFoldedPlan.ordinaryLength_lower m)
    have hgrid : 1 ≤ ThinProductCosts.gridSide (L m) m := by
      unfold ThinProductCosts.gridSide
      have hc := Nat.choose_pos (OptimizedFoldedPlan.ordinaryLength_lower m)
      exact one_le_mul hc (one_le_pow₀ (by decide))
    have hN : 0<N := by omega
    dsimp[K]
    exact TilingCosts.bandCount_pos N _ hN ht
  have hR : (K:ℝ)^2 ≤ (HalfSourceEmptyRootCost.count N m:ℝ) := by exact_mod_cast (show K^2 ≤ HalfSourceEmptyRootCost.count N m by simpa only[pow_two] using hle)
  have h1 : (1:ℝ) ≤ (K:ℝ)^2 := one_le_pow₀ (by exact_mod_cast hK)
  have hh := HalfSourceEmptyRootCost.count_bound N m hm hfit
  change (K:ℝ)^2+1 ≤ _
  linarith

def constant : ℝ := 800000000*(1+HalfSourceHighQueryCost.constant)

theorem budget_bound (N m M q : ℕ) (hm : 0 < m)
    (hfit : ThinProductCosts.gridSide (L m) m ≤ N) :
    let K := TilingCosts.bandCount N (ThinMatrixBackend.tileWidth (L m) m)
    (GraphHighScalarSchedule.budget K (L m) m (t m) M (HalfSourceHighQueryCost.table (L m) m q):ℝ) ≤
      constant*(width K (L m) m q:ℝ)^17*
        ((N:ℝ)^2*(((4:ℝ)^m)^(-G))+(M:ℝ)*(((4:ℝ)^m)^q2)) := by
  let K := TilingCosts.bandCount N (ThinMatrixBackend.tileWidth (L m) m)
  let P := (width K (L m) m q:ℝ)
  let U := (SelectedHighQueries.rowBudget (L m) m (t m) (HalfSourceHighQueryCost.table (L m) m q)+32:ℕ)
  have hP : 1 ≤ P := by dsimp[P];exact_mod_cast (show 1 ≤ width K (L m) m q by unfold width;omega)
  have hmP : (m+1:ℝ) ≤ P := by dsimp[P,width];push_cast;have := Nat.cast_nonneg (α:=ℝ) (L m);have := Nat.cast_nonneg (α:=ℝ) q.size;have := Nat.cast_nonneg (α:=ℝ) ((K*K).size);linarith
  have hw : (HalfSourceHighQueryCost.width (L m) m q:ℝ) ≤ P := by dsimp[P];exact_mod_cast (show HalfSourceHighQueryCost.width (L m) m q ≤ width K (L m) m q by unfold width HalfSourceHighQueryCost.width;omega)
  have hc : 0 ≤ HalfSourceHighQueryCost.constant := by unfold HalfSourceHighQueryCost.constant;positivity
  have hrow := HalfSourceHighQueryCost.row_bound m q hm
  have hrow' : (U:ℝ) ≤ HalfSourceHighQueryCost.constant*P^6*(((4:ℝ)^m)^q2) := by
    calc
      _ ≤ HalfSourceHighQueryCost.constant*(m+1:ℝ)*(HalfSourceHighQueryCost.width (L m) m q:ℝ)^5*(((4:ℝ)^m)^q2) := hrow
      _ ≤ HalfSourceHighQueryCost.constant*P*P^5*(((4:ℝ)^m)^q2) := by gcongr
      _ = _ := by ring
  have hpairs := band_pairs N m hm hfit
  have hbudget := budget_polynomial K (L m) m (t m) M (HalfSourceHighQueryCost.table (L m) m q) q
  have hbudgetR : (GraphHighScalarSchedule.budget K (L m) m (t m) M (HalfSourceHighQueryCost.table (L m) m q):ℝ) ≤
    100000000*P^10*((K:ℝ)^2+1+(M:ℝ)*(U:ℝ)) := by
    dsimp[P]
    exact_mod_cast (show GraphHighScalarSchedule.budget K (L m) m (t m) M (HalfSourceHighQueryCost.table (L m) m q) ≤ 100000000*(width K (L m) m q)^10*(K^2+1+M*U) by simpa only[pow_two,U] using hbudget)
  have h11 : P^11 ≤ P^17 := pow_le_pow_right₀ hP (by decide)
  have h16 : P^16 ≤ P^17 := pow_le_pow_right₀ hP (by decide)
  have hleft : 100000000*P^10*(8*(N:ℝ)^2*(m+1:ℝ)*(((4:ℝ)^m)^(-G))) ≤
      800000000*P^17*((N:ℝ)^2*(((4:ℝ)^m)^(-G))) := by
    calc
      _ ≤ 100000000*P^10*(8*(N:ℝ)^2*P*(((4:ℝ)^m)^(-G))) := by gcongr
      _ = 800000000*P^11*((N:ℝ)^2*(((4:ℝ)^m)^(-G))) := by ring
      _ ≤ _ := by gcongr
  have hright : 100000000*P^10*((M:ℝ)*(HalfSourceHighQueryCost.constant*P^6*(((4:ℝ)^m)^q2))) ≤
      100000000*HalfSourceHighQueryCost.constant*P^17*((M:ℝ)*(((4:ℝ)^m)^q2)) := by
    calc
      _ = 100000000*HalfSourceHighQueryCost.constant*P^16*((M:ℝ)*(((4:ℝ)^m)^q2)) := by ring
      _ ≤ _ := by gcongr
  calc
    _ ≤ 100000000*P^10*((K:ℝ)^2+1+(M:ℝ)*(U:ℝ)) := hbudgetR
    _ ≤ 100000000*P^10*(8*(N:ℝ)^2*(m+1:ℝ)*(((4:ℝ)^m)^(-G))+(M:ℝ)*(HalfSourceHighQueryCost.constant*P^6*(((4:ℝ)^m)^q2))) := by gcongr
    _ = 100000000*P^10*(8*(N:ℝ)^2*(m+1:ℝ)*(((4:ℝ)^m)^(-G)))+100000000*P^10*((M:ℝ)*(HalfSourceHighQueryCost.constant*P^6*(((4:ℝ)^m)^q2))) := by ring
    _ ≤ 800000000*P^17*((N:ℝ)^2*(((4:ℝ)^m)^(-G)))+100000000*HalfSourceHighQueryCost.constant*P^17*((M:ℝ)*(((4:ℝ)^m)^q2)) := add_le_add hleft hright
    _ ≤ _ := by
      change _ ≤ constant*P^17*_
      unfold constant
      nlinarith only [mul_nonneg hc (show 0 ≤ P^17*((N:ℝ)^2*(((4:ℝ)^m)^(-G))) by positivity),
        show 0 ≤ P^17*((M:ℝ)*(((4:ℝ)^m)^q2)) by positivity,
        mul_nonneg hc (show 0 ≤ P^17*((M:ℝ)*(((4:ℝ)^m)^q2)) by positivity)]

theorem actual {n h r M : ℕ} (f : CompactBlocks.PhysicalFactorization r)
    (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f)
    (block : Fin (CompactBlocks.blockCount n h)) (input : BinaryFoldedFormation.Inputs n)
    (hL : p.L=L p.m) (ht : p.t=t p.m) (hm : 0 < p.m)
    (hfit : ThinProductCosts.gridSide p.L p.m ≤ p.N)
    (ids : Vector ℕ (TilingCosts.bandCount p.N (ThinMatrixBackend.tileWidth (L p.m) p.m)))
    (sources : GraphRetainedHigh.Sources f p (K:=TilingCosts.bandCount p.N (ThinMatrixBackend.tileWidth (L p.m) p.m)))
    (hc : GraphRetainedHigh.Correct f p block input ids sources)
    (shape : ThinMatrixBackend.ShapePlan p.L p.m)
    (requests : Vector (GraphCompletionRequests.Physical p.L p.m f.cyclic) M)
    (hb : ∀ i,(requests.get i).bandL < TilingCosts.bandCount p.N (ThinMatrixBackend.tileWidth (L p.m) p.m) ∧
      (requests.get i).bandR < TilingCosts.bandCount p.N (ThinMatrixBackend.tileWidth (L p.m) p.m)) :
    ((GraphHighScalarSchedule.execute p.t shape requests hb (GraphHighPreparation.execute f p sources).value.2).operations:ℝ) ≤
      constant*(width (TilingCosts.bandCount p.N (ThinMatrixBackend.tileWidth (L p.m) p.m)) (L p.m) p.m f.cyclic:ℝ)^17*
        ((p.N:ℝ)^2*(((4:ℝ)^p.m)^(-G))+(M:ℝ)*(((4:ℝ)^p.m)^q2)) := by
  have hA : ∀ a b u v run,BinaryHighTable.Bounds.TableBound
      (CroppedHighQueries.tableMagnitude p.L f.cyclic (2^(p.L+p.m)))
      ((((((GraphHighPreparation.execute f p sources).value.2.get a).get b).get u).get v).get run) := by
    intro a b u v run
    dsimp only [GraphHighPreparation.execute]
    rw [GraphHighPreparation.tables_get]
    exact GraphSelectedHigh.table_bound f p block input ids sources hc a b u v run
  have hw := GraphHighScalarSchedule.execute_work p.t
    (CroppedHighQueries.tableMagnitude p.L f.cyclic (2^(p.L+p.m))) p.t_le shape requests hb
    (GraphHighPreparation.execute f p sources).value.2 hA
  have hwR : ((GraphHighScalarSchedule.execute p.t shape requests hb (GraphHighPreparation.execute f p sources).value.2).operations:ℝ) ≤
      (GraphHighScalarSchedule.budget (TilingCosts.bandCount p.N (ThinMatrixBackend.tileWidth (L p.m) p.m))
        p.L p.m p.t M (CroppedHighQueries.tableMagnitude p.L f.cyclic (2^(p.L+p.m))):ℝ) := by exact_mod_cast hw
  apply hwR.trans
  rw [hL,ht]
  exact budget_bound p.N p.m M f.cyclic hm (by simpa only[hL] using hfit)

#print axioms budget_polynomial
#print axioms band_pairs
#print axioms budget_bound
#print axioms actual
end
end ThinMatrix.HalfSourceHighScheduleCost
