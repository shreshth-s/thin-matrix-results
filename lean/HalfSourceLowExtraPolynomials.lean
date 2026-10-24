import HalfSourceLowCollectionCosts

namespace ThinMatrix.HalfSourceLowExtraPolynomials
open ParameterExecution BinaryCell ResidualFamilyKeys
set_option autoImplicit false
set_option maxHeartbeats 4000000
set_option maxRecDepth 10000
variable {n h r : ℕ} (f : CompactBlocks.PhysicalFactorization r)
  (p : BinaryFoldedFactory.Plan (n:=n) (h:=h) f)

 def width (W A : ℕ) : ℕ := p.m+p.t+f.cyclic.size+W.size+A.size+(channelCount p.m p.t).size+16

 theorem product_extra (W A : ℕ) (hB : 1 ≤ CompactBlocks.blockCount n h) :
    HalfSourceLowProductCosts.extra f p W A ≤
      200000*(FoldedBackendExecution.windowQuerySize n*CompactBlocks.blockCount n h*f.cyclic+
        channelCount p.m p.t+1)*(width f p W A)^4 := by
  let P := width f p W A
  let M := FoldedBackendExecution.windowQuerySize n
  let B := CompactBlocks.blockCount n h
  let H := channelCount p.m p.t
  have hP : 1 ≤ P := by dsimp[P,width];omega
  have hm : p.m+1 ≤ P := by dsimp[P,width];omega
  have hsmall : HalfSourceSelectedRootCost.width (p.m+1) f.cyclic p.t W A ≤ P := by
    dsimp[P,width,HalfSourceSelectedRootCost.width];omega
  have hc := HalfSourceAdaptivePolynomials.count_bound p.m P hP hm
  have hp3 : P^3 ≤ P^4 := Nat.pow_le_pow_right hP (by decide)
  have hp1 : P ≤ P^4 := le_self_pow₀ hP (by decide)
  have hp0 : 1 ≤ P^4 := one_le_pow₀ hP
  have hM : M ≤ M*B*f.cyclic := by
    have hh := Nat.le_mul_of_pos_right M (Nat.mul_pos hB f.cyclic_pos)
    simpa only[Nat.mul_assoc] using hh
  have hMH := Nat.mul_le_mul hM hp0
  have hH := Nat.mul_le_mul_left H hp1
  have hsmall4 := Nat.mul_le_mul_left (102000*M*B*f.cyclic) (Nat.pow_le_pow_left hsmall 4)
  have hC : 2*RetainedRootWindows.countBudget p.m ≤ 8000*P^4 := by nlinarith[hc]
  have hrest : 32*p.m+80 ≤ 112*P^4 := by nlinarith
  have htrans : ResidualChannelTranspose.budget p.m H ≤ 32*H*P^4+40*P^4 := by
    unfold ResidualChannelTranspose.budget
    have hmH := Nat.mul_le_mul_right H (show p.m≤P by omega)
    nlinarith
  unfold HalfSourceLowProductCosts.extra
  change _ ≤ 200000*(M*B*f.cyclic+H+1)*P^4
  nlinarith only[hC,hrest,htrans,hsmall4,hMH,Nat.zero_le (M*B*f.cyclic*P^4),Nat.zero_le (H*P^4),Nat.zero_le (P^4)]

 theorem family_bound (W A : ℕ) : GraphOwnLowCollection.T f p ≤ 8192*(width f p W A)^7*channelCount p.m p.t := by
  have hh := HalfSourceRootFamilyCosts.multiplicity_bound p.m
  have hm : p.m+1 ≤ width f p W A := by unfold width;omega
  have ht : 2*p.m+1 ≤ 2*(p.m+1) := by omega
  have he : GraphOwnLowCollection.T f p=HalfSourceRootFamilyCosts.multiplicity p.m*channelCount p.m p.t := by
    unfold GraphOwnLowCollection.T HalfSourceRootFamilyCosts.multiplicity
    ring
  rw[he]
  calc
    _ ≤ ((64*(p.m+1)^3)^2*(2*(p.m+1)))*channelCount p.m p.t := Nat.mul_le_mul_right _ (hh.trans (Nat.mul_le_mul_left _ ht))
    _ = 8192*(p.m+1)^7*channelCount p.m p.t := by ring
    _ ≤ _ := by gcongr

 theorem family_size (W A : ℕ) : (GraphOwnLowCollection.T f p).size ≤ 32*width f p W A := by
  let P := width f p W A
  have ht := Nat.size_le_size (family_bound f p W A)
  have h1 := size_mul (8192*P^7) (channelCount p.m p.t)
  have h2 := size_mul 8192 (P^7)
  have h3 := size_pow P 7
  have hP : P.size ≤ P := size_le_self P
  have hH : (channelCount p.m p.t).size+16 ≤ P := by dsimp[P,width];omega
  norm_num only[show Nat.size 8192=14 by decide] at h2
  change _ ≤ 32*P
  change (GraphOwnLowCollection.T f p).size ≤ (8192*P^7*channelCount p.m p.t).size at ht
  omega

 theorem accumulation_unit (W A : ℕ) :
    BackendScalarBits.backendScalarUnit
      (GraphOwnLowCollection.T f p*(p.t*(W*SelectedRootProduct.productMagnitude f.cyclic p.t A))).size ≤
        2000000*(width f p W A)^2 := by
  let P := width f p W A
  have hT := family_size f p W A
  have ht := size_le_self p.t
  have hp := HalfSourceSelectedRootCost.product_size f.cyclic p.t A
  have h1 := size_mul (GraphOwnLowCollection.T f p) (p.t*(W*SelectedRootProduct.productMagnitude f.cyclic p.t A))
  have h2 := size_mul p.t (W*SelectedRootProduct.productMagnitude f.cyclic p.t A)
  have h3 := size_mul W (SelectedRootProduct.productMagnitude f.cyclic p.t A)
  have hh : (GraphOwnLowCollection.T f p*(p.t*(W*SelectedRootProduct.productMagnitude f.cyclic p.t A))).size+1 ≤ 40*P := by
    dsimp[P,width] at *
    omega
  unfold BackendScalarBits.backendScalarUnit BackendScalarBits.scalarUnit
  calc
    _ ≤ 8*(100*(40*P)^2) := by gcongr
    _ ≤ _ := by dsimp[P];nlinarith[Nat.zero_le ((width f p W A)^2)]

 theorem collection_extra (W A : ℕ) (hB : 1 ≤ CompactBlocks.blockCount n h)
    (hH : 1 ≤ channelCount p.m p.t) :
    HalfSourceLowCollectionCosts.extra f p W A ≤
      1000000000000*(width f p W A)^11*
        (FoldedBackendExecution.windowQuerySize n*CompactBlocks.blockCount n h*f.cyclic*channelCount p.m p.t+
          (channelCount p.m p.t)^2) := by
  let P := width f p W A
  let M := FoldedBackendExecution.windowQuerySize n
  let B := CompactBlocks.blockCount n h
  let H := channelCount p.m p.t
  let T := GraphOwnLowCollection.T f p
  let X := M*B*f.cyclic
  let U := BackendScalarBits.backendScalarUnit
    (T*(p.t*(W*SelectedRootProduct.productMagnitude f.cyclic p.t A))).size
  have hP : 1 ≤ P := by dsimp[P,width];omega
  have hX : M ≤ X := by
    have hh := Nat.le_mul_of_pos_right M (Nat.mul_pos hB f.cyclic_pos)
    simpa only[X,Nat.mul_assoc] using hh
  have hXB : M*B ≤ X := Nat.le_mul_of_pos_right _ f.cyclic_pos
  have hT : 1 ≤ T := by
    have hj := HalfSourceRootFamilyCosts.multiplicity_positive p.m
    have he : T=HalfSourceRootFamilyCosts.multiplicity p.m*H := by
      dsimp[T,H,GraphOwnLowCollection.T,HalfSourceRootFamilyCosts.multiplicity];ring
    rw[he]
    exact Nat.mul_pos hj hH
  have he := product_extra f p W A hB
  have hu := accumulation_unit f p W A
  have htb := family_bound f p W A
  change HalfSourceLowProductCosts.extra f p W A ≤ 200000*(X+H+1)*P^4 at he
  change U ≤ 2000000*P^2 at hu
  change T ≤ 8192*P^7*H at htb
  have h2 : P^2 ≤ P^4 := Nat.pow_le_pow_right hP (by decide)
  have h4 : 1 ≤ P^4 := one_le_pow₀ hP
  have hu4 : U ≤ 2000000*P^4 := hu.trans (Nat.mul_le_mul_left _ h2)
  have hread : M*(T*(B*U)) ≤ X*T*(2000000*P^4) := by
    calc
      _ = (M*B)*T*U := by ring
      _ ≤ X*T*(2000000*P^4) := Nat.mul_le_mul (Nat.mul_le_mul_right _ hXB) hu4
  have hcontrols : M*(T*(40*B+40)+3*B+47) ≤ 130*X*T := by
    have h1 := Nat.mul_le_mul_right (40*T) hXB
    have h2 := Nat.mul_le_mul_right (40*T) hX
    have h3 := Nat.mul_le_mul_right 3 hXB
    have h4 := Nat.mul_le_mul_right 47 hX
    have hxt : X ≤ X*T := Nat.le_mul_of_pos_right X hT
    nlinarith only[h1,h2,h3,h4,hxt]
  have hT4 : T ≤ T*(X+H+1)*P^4 := by
    have hh : 1 ≤ (X+H+1)*P^4 := Nat.mul_pos (by omega) h4
    simpa only[Nat.mul_assoc] using Nat.le_mul_of_pos_right T hh
  have hXT4 : X*T ≤ T*(X+H+1)*P^4 := by
    have hh : X ≤ (X+H+1)*P^4 := (show X≤X+H+1 by omega).trans (Nat.le_mul_of_pos_right _ h4)
    simpa only[Nat.mul_assoc,Nat.mul_comm,Nat.mul_left_comm] using Nat.mul_le_mul_left T hh
  have hXTH : X*T*P^4 ≤ T*(X+H+1)*P^4 := by
    rw[mul_comm X T]
    exact Nat.mul_le_mul_right _ (Nat.mul_le_mul_left T (by omega))
  have hbase : HalfSourceLowCollectionCosts.extra f p W A ≤ 3000000*T*(X+H+1)*P^4 := by
    have hep := Nat.mul_le_mul_left T he
    unfold HalfSourceLowCollectionCosts.extra
    change T*(HalfSourceLowProductCosts.extra f p W A+99)+36+
      M*(T*(B*U)+T*(40*B+40)+3*B+47) ≤ _
    nlinarith only[hep,hread,hcontrols,hT4,hXT4,hXTH,hT]
  have hHsq : H ≤ H^2 := le_self_pow₀ hH (by decide)
  have hvol : H*(X+H+1) ≤ 2*(X*H+H^2) := by nlinarith
  calc
    _ ≤ 3000000*T*(X+H+1)*P^4 := hbase
    _ ≤ 3000000*(8192*P^7*H)*(X+H+1)*P^4 := by gcongr
    _ = (3000000*8192)*P^11*(H*(X+H+1)) := by ring
    _ ≤ (3000000*8192)*P^11*(2*(X*H+H^2)) := Nat.mul_le_mul_left _ hvol
    _ ≤ _ := by dsimp[P,X,H];nlinarith[Nat.zero_le ((width f p W A)^11*(M*B*f.cyclic*channelCount p.m p.t+(channelCount p.m p.t)^2))]

#print axioms product_extra
#print axioms family_bound
#print axioms family_size
#print axioms accumulation_unit
#print axioms collection_extra
end ThinMatrix.HalfSourceLowExtraPolynomials
