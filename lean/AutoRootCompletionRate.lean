import AutoFullyRetainedRootBatch
import SharedCompletionProgramRate
import FullyRetainedWindowCosts
import RootCompletionRate

set_option autoImplicit false
set_option maxHeartbeats 2600000
namespace ThinMatrix.AutoRootCompletionRate
open scoped BigOperators
open BinaryCell BinaryGroupedCoordinates
open FullyRetainedRootBatch (Bank Sources)
open SharedCompletionRate

private theorem envelope (s M G Q W price L setup : ℕ) (hs : 1 ≤ s)
    (hG : 1 ≤ G) (hQ : 1 ≤ Q) (hW : 1 ≤ W) (hL : s.size+2 ≤ L)
    (hsetup : setup ≤ 1000000000000000*Q*(s.size+2)^2+8) :
    (setup:ℝ)+16*price ≤ 2000000000000000*(price+1)*W*(L:ℝ)^5*
      ((M:ℝ)*Q*(s:ℝ)^beta+(G:ℝ)*Q*(s:ℝ)^gamma) := by
  have hL1 : 1 ≤ L := by omega
  have hpow := Nat.pow_le_pow_left hL 2
  have hbase : 1 ≤ W*Q*(M+G) := Nat.mul_pos (Nat.mul_pos hW hQ) (by omega)
  have hWQ : Q ≤ W*Q*(M+G) := by nlinarith [Nat.mul_pos hW (show 1 ≤ M+G by omega)]
  have hnat : setup+16*price ≤ 2000000000000000*(price+1)*W*L^2*Q*(M+G) := by
    have h1 : 1 ≤ L^2 := one_le_pow₀ hL1
    have hb := Nat.mul_le_mul_right (L^2) hbase
    have hq := Nat.mul_le_mul hWQ hpow
    have hprice := Nat.mul_le_mul_left price hb
    nlinarith
  have hreal : (setup:ℝ)+16*price ≤ 2000000000000000*((price:ℝ)+1)*W*(L:ℝ)^2*Q*(M+G) := by exact_mod_cast hnat
  have hb : 1 ≤ (s:ℝ)^beta := Real.one_le_rpow (by exact_mod_cast hs) (by norm_num [beta])
  have hg : 1 ≤ (s:ℝ)^gamma := Real.one_le_rpow (by exact_mod_cast hs) (by norm_num [gamma])
  have hm := mul_le_mul_of_nonneg_left hb (show 0 ≤ (M:ℝ)*Q by positivity)
  have hgr := mul_le_mul_of_nonneg_left hg (show 0 ≤ (G:ℝ)*Q by positivity)
  have ht : (Q:ℝ)*(M+G) ≤ (M:ℝ)*Q*(s:ℝ)^beta+(G:ℝ)*Q*(s:ℝ)^gamma := by nlinarith
  have hl : (L:ℝ)^2 ≤ (L:ℝ)^5 := pow_le_pow_right₀ (by exact_mod_cast hL1) (by decide)
  have hh := mul_le_mul hl ht (by positivity) (by positivity)
  have hp := mul_le_mul_of_nonneg_left hh (show 0 ≤ (2000000000000000:ℝ)*(price+1)*W by positivity)
  nlinarith

/-- Complete actual root execution: binary per-support tile selection,
retained source routing, every window/prefix/chunk, original occurrence
scatter and full-coefficient accumulation. The source banks are supplied
and their construction is separately charged by the source encoder. -/
theorem exists_root_rate : ∃ scheme : RectangularBatch.Scheme,
    ∃ hnum : scheme.num=861, ∃ hden : scheme.den=500, ∃ hz : scheme.z=15,
    scheme.Valid ∧ ∃ K : ℝ, 0 < K ∧ ∀ k ell total cn co C B W : ℕ,
      ∀ hD : 0 < WindowSharedCompletion.D k ell total cn co,
      ∀ xs : Vector (Sources k ell total cn co C B) W,
      ∀ banks : Vector (Bank k ell total cn co C B) W,
      (∀ s,banks.get s=(SharedPrefixSourceBank.prepare (xs.get s)).value) →
      (∀ s b,((xs.get s).get b).grouped.keys=GroupedPreparation.keyVector
        (WindowPrefixProgram.length k ell) (WindowPrefixProgram.cap k ell total cn co)) →
      (∀ s b,((xs.get s).get b).grouped.pairs=GroupedPreparation.pairKeys (WindowPrefixProgram.length k ell)) →
      ∀ layouts : Vector (RetainedWindowPermutation.Layout (2*k)) W,
      ∀ labels : Array (Vector (Fin 4) (2*k)), ∀ H price L : ℕ,
      1 ≤ H → (∀ s b pair,PrefixCompletionMatrices.LeafBound (((xs.get s).get b).traces.get pair) H) →
      1 ≤ W → SharedCompletionTile.col (WindowSharedCompletion.D k ell total cn co) ≤ B*C →
      2*k+1 ≤ L →
      (SharedFullyAddressedBatch.addressSpan labels.size (WindowSharedCompletion.D k ell total cn co) (B*C)
        (SharedCompletionTile.row (WindowSharedCompletion.D k ell total cn co))
        (SharedCompletionTile.col (WindowSharedCompletion.D k ell total cn co))).size+1 ≤ L →
      scheme.q.size+(WindowSharedCompletion.D k ell total cn co).size+6 ≤ L →
      (WindowSharedCompletion.D k ell total cn co).size+H.size+6 ≤ L →
      W.size+(WindowSharedCompletion.D k ell total cn co).size+H.size+1 ≤ L →
      ((AutoFullyRetainedRootBatch.execute scheme hnum hden hz hD banks layouts labels).bitSteps+
        price*(AutoFullyRetainedRootBatch.execute scheme hnum hden hz hD banks layouts labels).control:ℝ) ≤
      K*(price+1)*W*(L:ℝ)^5*((labels.size:ℝ)*(B*C)*(WindowSharedCompletion.D k ell total cn co:ℝ)^beta+
        ((2^(WindowPrefixProgram.length k ell)*4^(WindowPrefixProgram.prefixLength k ell):ℕ):ℝ)*
          (B*C)*(WindowSharedCompletion.D k ell total cn co:ℝ)^gamma) := by
  obtain ⟨scheme,hvalid,hnum,hden,hz,K,hK,hcost⟩ := SharedCompletionProgramRate.exists_schedule_rate
  refine ⟨scheme,hnum,hden,hz,hvalid,K+512+2000+2000000000000000,by positivity,?_⟩
  intro k ell total cn co C B W hD xs banks hb hk hp layouts labels H price L hH hx hW hfit hkL hwL hqL hHL hsumL
  let s := WindowSharedCompletion.D k ell total cn co
  let P := WindowPrefixProgram.prefixLength k ell
  let len := WindowPrefixProgram.length k ell
  let r := WindowPrefixProgram.cap k ell total cn co
  let tileRun := AutoFullyRetainedRootBatch.prepare scheme hnum hden hz s hD
  let tile := tileRun.value
  let Q := B*C
  let M := labels.size
  let G := 2^len*4^P
  let V := (M:ℝ)*((B:ℝ)*(C:ℝ))*(s:ℝ)^beta+(G:ℝ)*((B:ℝ)*(C:ℝ))*(s:ℝ)^gamma
  have hs : 1 ≤ s := hD
  have hslog : s.size+H.size+6 ≤ L := hHL
  have hG : 1 ≤ G := Nat.mul_pos (show 1 ≤ 2^len from one_le_pow₀ (by decide))
    (show 1 ≤ 4^P from one_le_pow₀ (by decide))
  have hQ : 1 ≤ Q := (SharedCompletionTile.dimensions s hs).2.1.trans_le hfit
  have hL : 1 ≤ L := by omega
  have hlen : P+len+1 ≤ L := by
    dsimp only [P,len]
    rw [WindowPrefixProgram.dimension]
    exact hkL
  have hDA : s ≤ tile.A := by rw [tile.A_eq];exact (SharedCompletionTile.dimensions s hs).2.2.1
  have hDQ : s ≤ Q := (SharedCompletionTile.dimensions s hs).2.2.2.trans hfit
  have hB : B ≤ Q := Nat.le_mul_of_pos_right _ (show 0 < C by dsimp [Q] at hQ;nlinarith)
  have hfit' : tile.Z ≤ Q := by rw [tile.Z_eq];exact hfit
  have hZeq : tile.Z=s^15 := tile.Z_eq
  have hrows := SharedCompletionTile.row_bounds s hs
  have hAlo : (s:ℝ)^a ≤ (tile.A:ℝ) := by rw [tile.A_eq];exact hrows.1
  have hAhi : (tile.A:ℝ) ≤ 2*(s:ℝ)^a := by rw [tile.A_eq];exact hrows.2
  let width := (SharedFullyAddressedBatch.addressSpan M s Q tile.A tile.Z).size
  have hwidth : width+1 ≤ L := by
    dsimp only [width]
    rw [tile.A_eq,tile.Z_eq]
    exact hwL
  have hchild (i : Fin W) :
      ((FullyRetainedWindowBatch.execute scheme hD tile.hA tile.hZ tile.first tile.last (banks.get i) (layouts.get i) labels).bitSteps+
        price*(FullyRetainedWindowBatch.execute scheme hD tile.hA tile.hZ tile.first tile.last (banks.get i) (layouts.get i) labels).control:ℝ) ≤
      (K+512)*(price+1)*(L:ℝ)^5*V := by
    rw [hb i]
    let req := (WindowCompletionRequests.requests ell (layouts.get i) labels).value
    have hreq : req.size=M := WindowCompletionRequests.requests_size _ _ _
    have hr := hcost P len r B C tile.A tile.Z hD tile.hA tile.hZ tile.first tile.last
      (xs.get i) H width price L hH (hx i) req hfit' hZeq hAlo hAhi hDA hDQ hB hL hlen hwidth
      (by change s.size+3 ≤ L;omega) hqL hHL
      (fun pair j => by
        have hh := SharedFullyPrefixSchedule.uniform_address_fit (xs.get i) req tile.hA (Z:=tile.Z) pair j
        simpa only [hreq] using hh)
    have he := FullyRetainedWindowCosts.priced_from_schedule scheme hD tile.hA tile.hZ tile.first tile.last
      (xs.get i) (layouts.get i) labels price L hQ hL (by omega) hlen
    have her := FullyRetainedWindowCosts.overhead_rate (s:ℝ) M G Q L price
      (by exact_mod_cast hs) (by positivity) (by positivity) (by positivity) (by exact_mod_cast hL) (by positivity)
    simp only [hreq] at hr
    have heR :
        ((FullyRetainedWindowBatch.execute scheme hD tile.hA tile.hZ tile.first tile.last
          (SharedPrefixSourceBank.prepare (xs.get i)).value (layouts.get i) labels).bitSteps+
        price*(FullyRetainedWindowBatch.execute scheme hD tile.hA tile.hZ tile.first tile.last
          (SharedPrefixSourceBank.prepare (xs.get i)).value (layouts.get i) labels).control:ℝ) ≤
        ((SharedFullyPrefixSchedule.execute scheme hD tile.hA tile.hZ tile.first tile.last req
          (RoutedPrefixBatch.prepare (xs.get i) req).value).bitSteps+
          price*(SharedFullyPrefixSchedule.execute scheme hD tile.hA tile.hZ tile.first tile.last req
          (RoutedPrefixBatch.prepare (xs.get i) req).value).control:ℝ)+
          (price:ℝ)*(512*(L:ℝ)^2*Q*(M+G)) := by exact_mod_cast he
    simp only [Q,Nat.cast_mul] at heR
    change _ ≤ K*(price+1)*(L:ℝ)^5*V at hr
    simp only [Q,Nat.cast_mul] at her
    change _ ≤ 512*(price+1)*(L:ℝ)^5*V at her
    nlinarith
  have hroot := AutoFullyRetainedRootBatch.priced_children scheme hvalid hD tile xs banks hb hk hp H hx layouts labels price
  have hsum := Finset.sum_le_sum (fun i (_ : i∈Finset.univ) => hchild i)
  simp only [Finset.sum_const,Finset.card_univ,Fintype.card_fin,nsmul_eq_mul] at hsum
  have hextra := RootCompletionRate.extras_rate (s:ℝ) W s H M G Q L price
    (by exact_mod_cast hs) hW hG hQ hL hsumL
  have hsetup := envelope s M G Q W price L tileRun.bitSteps hs hG hQ hW (by omega)
    (AutoFullyRetainedRootBatch.prepare_absorbed scheme hnum hden hz s Q hD hfit)
  have heq := AutoFullyRetainedRootBatch.priced_setup scheme hnum hden hz hD banks layouts labels price
  have hrootR :
      ((AutoFullyRetainedRootBatch.executeWith scheme hD tile banks layouts labels).bitSteps+
        price*(AutoFullyRetainedRootBatch.executeWith scheme hD tile banks layouts labels).control:ℝ) ≤
      (∑ i : Fin W,((FullyRetainedWindowBatch.execute scheme hD tile.hA tile.hZ tile.first tile.last (banks.get i) (layouts.get i) labels).bitSteps+
        price*(FullyRetainedWindowBatch.execute scheme hD tile.hA tile.hZ tile.first tile.last (banks.get i) (layouts.get i) labels).control:ℝ))+
      (M*(W*(Q*BackendScalarBits.backendScalarUnit (W*(s*H)).size))+price*SharedFullyPrefixPrices.rootExtra W M Q:ℝ) := by
    norm_cast
    simpa only [Nat.add_assoc] using hroot
  have heqR :
      ((AutoFullyRetainedRootBatch.execute scheme hnum hden hz hD banks layouts labels).bitSteps+
        price*(AutoFullyRetainedRootBatch.execute scheme hnum hden hz hD banks layouts labels).control:ℝ)=
      (tileRun.bitSteps:ℝ)+
      ((AutoFullyRetainedRootBatch.executeWith scheme hD tile banks layouts labels).bitSteps+
        price*(AutoFullyRetainedRootBatch.executeWith scheme hD tile banks layouts labels).control:ℝ)+16*price := by
    norm_cast
    simpa only [Nat.add_assoc] using heq
  simp only [Q,Nat.cast_mul] at hextra hsetup hrootR
  change _ ≤ 2000*(price+1)*W*(L:ℝ)^5*V at hextra
  change _ ≤ 2000000000000000*(price+1)*W*(L:ℝ)^5*V at hsetup
  change _ ≤ (K+512+2000+2000000000000000)*(price+1)*W*(L:ℝ)^5*V
  nlinarith

#print axioms exists_root_rate
end ThinMatrix.AutoRootCompletionRate
