import BinaryControllerExecution
import GlobalAddressBitBounds
import ParameterExecution
import AdaptiveQueryBitBounds
import BinaryAPSPCaller
import EndToEndAPSP

/-!
# Polynomial bounds for the binary controller and whole retained heap

Computed parameter fields, original input magnitudes, retained producer work,
and the actual controller/host schedules determine the scalar and address
widths. Heap majorants retain every block, callback, and host history and
charge bounded binary cell storage explicitly. They are finite layout bounds,
not a theorem about Lean persistent heap allocation.
-/


namespace ThinMatrix.ControllerCapPow
set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

/-- A fixed logarithmic coefficient for the scalar controller cap. -/
def capExponent (C K Cp k : ℕ) : ℕ := 3*C + K + Cp*(k+1) + 5

/-- All dimensions and scalar inputs are bounded by powers of the original
size parameter. The only exponentiation by the controller depth is charged
explicitly through the `Cp*(k+1)` term. -/
theorem controllerCap_le_pow (P I Q k lam stages X W pmax C K Cp s : ℕ)
    (hs : 1 ≤ s)
    (hP : P ≤ 2^(C*s)) (hI : I ≤ 2^(C*s))
    (hQ : Q ≤ 2^(C*s)) (hlam : lam ≤ 2^(C*s))
    (hstages : stages ≤ 2^(C*s)) (hX : X ≤ 2^(C*s))
    (hk : k+1 ≤ 2^(C*s)) (hW : W ≤ 2^(K*s))
    (hpmax : pmax ≤ 2^(Cp*s)) :
    DenseControllerExecution.controllerCap P I Q k lam stages X W pmax ≤
      2^(capExponent C K Cp k*s) := by
  let D := 3*C+K+Cp*(k+1)+1
  let T := 2^(D*s)
  have hbase : 2^(C*s) ≤ T := by
    dsimp [T]
    apply Nat.pow_le_pow_right (by norm_num)
    exact Nat.mul_le_mul_right s (by dsimp [D]; omega)
  have hprimebase : 2^(Cp*s) ≤ T := by
    dsimp [T]
    apply Nat.pow_le_pow_right (by norm_num)
    have hcp : Cp ≤ Cp*(k+1) := by
      simpa using Nat.mul_le_mul_left Cp (show 1 ≤ k+1 by omega)
    exact Nat.mul_le_mul_right s (by dsimp [D]; omega)
  have hone : 1 ≤ T := by dsimp [T]; exact one_le_pow₀ (by decide)
  have hX' : X ≤ T := hX.trans hbase
  have hP' : P ≤ T := hP.trans hbase
  have hI' : I ≤ T := hI.trans hbase
  have hQ' : Q ≤ T := hQ.trans hbase
  have hlam' : lam ≤ T := hlam.trans hbase
  have hstages' : stages ≤ T := hstages.trans hbase
  have hk' : k ≤ T := by omega
  have hpmax' : pmax ≤ T := hpmax.trans hprimebase
  have htwo : 2^(2*C*s) ≤ T := by
    dsimp [T]
    apply Nat.pow_le_pow_right (by norm_num)
    exact Nat.mul_le_mul_right s (by dsimp [D]; omega)
  have hIX : I*X ≤ T := by
    calc
      _ ≤ 2^(C*s)*2^(C*s) := Nat.mul_le_mul hI hX
      _ = 2^(2*C*s) := by rw [←pow_add]; congr 1; ring
      _ ≤ T := htwo
  have hlamX : lam*X ≤ T := by
    calc
      _ ≤ 2^(C*s)*2^(C*s) := Nat.mul_le_mul hlam hX
      _ = 2^(2*C*s) := by rw [←pow_add]; congr 1; ring
      _ ≤ T := htwo
  have hPX : P*X ≤ T := by
    calc
      _ ≤ 2^(C*s)*2^(C*s) := Nat.mul_le_mul hP hX
      _ = 2^(2*C*s) := by rw [←pow_add]; congr 1; ring
      _ ≤ T := htwo
  have hmod : pmax^(k+1) ≤ T := by
    calc
      _ ≤ (2^(Cp*s))^(k+1) := Nat.pow_le_pow_left hpmax _
      _ = 2^((Cp*(k+1))*s) := by rw [←pow_mul]; congr 1; ring
      _ ≤ T := by
        dsimp [T]
        apply Nat.pow_le_pow_right (by norm_num)
        exact Nat.mul_le_mul_right s (by dsimp [D]; omega)
  have hWplus : W+1 ≤ 2^(K*s+1) := by
    have hpos : 1 ≤ 2^(K*s) := one_le_pow₀ (by decide)
    calc
      _ ≤ 2^(K*s)+2^(K*s) := Nat.add_le_add hW hpos
      _ = 2^(K*s+1) := by rw [pow_succ]; ring
  have hbatch : stages*(k+1)*P*(W+1) ≤ T := by
    calc
      _ ≤ 2^(C*s)*2^(C*s)*2^(C*s)*2^(K*s+1) :=
        Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul hstages hk) hP) hWplus
      _ = 2^((3*C+K)*s+1) := by
        rw [←pow_add,←pow_add,←pow_add]
        congr 1
        ring
      _ ≤ T := by
        dsimp [T]
        apply Nat.pow_le_pow_right (by norm_num)
        calc
          _ ≤ (3*C+K)*s+s := Nat.add_le_add_left hs _
          _ = (3*C+K+1)*s := by ring
          _ ≤ D*s := Nat.mul_le_mul_right s (by dsimp [D]; omega)
  have hsum : DenseControllerExecution.controllerCap P I Q k lam stages X W pmax ≤
      14*T := by
    unfold DenseControllerExecution.controllerCap
    omega
  calc
    _ ≤ 14*T := hsum
    _ ≤ 16*T := by omega
    _ = 2^(D*s+4) := by
      dsimp [T]
      rw [pow_add]
      norm_num
      ring
    _ ≤ _ := by
      apply Nat.pow_le_pow_right (by norm_num)
      have hfour : 4 ≤ 4*s := by simpa using Nat.mul_le_mul_left 4 hs
      calc
        _ ≤ D*s+4*s := Nat.add_le_add_left hfour _
        _ = _ := by dsimp [D,capExponent]; ring

/-- Converting the concrete cap to a maintained binary width costs only a
fixed multiple of the original logarithmic size. -/
theorem controllerCap_size_le (P I Q k lam stages X W pmax C K Cp s : ℕ)
    (hs : 1 ≤ s)
    (hP : P ≤ 2^(C*s)) (hI : I ≤ 2^(C*s))
    (hQ : Q ≤ 2^(C*s)) (hlam : lam ≤ 2^(C*s))
    (hstages : stages ≤ 2^(C*s)) (hX : X ≤ 2^(C*s))
    (hk : k+1 ≤ 2^(C*s)) (hW : W ≤ 2^(K*s))
    (hpmax : pmax ≤ 2^(Cp*s)) :
    (DenseControllerExecution.controllerCap P I Q k lam stages X W pmax).size ≤
      (capExponent C K Cp k+1)*s := by
  have h := (Nat.size_le_size (controllerCap_le_pow P I Q k lam stages X W pmax
    C K Cp s hs hP hI hQ hlam hstages hX hk hW hpmax)).trans_eq Nat.size_pow
  calc
    _ ≤ capExponent C K Cp k*s+1 := h
    _ ≤ capExponent C K Cp k*s+s := Nat.add_le_add_left hs _
    _ = _ := by ring

end ThinMatrix.ControllerCapPow

namespace ThinMatrix.ControllerHeapPow

open ArrayCompositeAlgorithm (Flags Owners)
open BinaryControllerExecution

set_option maxHeartbeats 1000000
set_option maxRecDepth 10000

/-- Controller flags/count arrays, prime labels, and retained call history. -/
def metadataCells (P I Q callCapacity : ℕ) : ℕ :=
  16 * (P + I + Q + callCapacity + 1)

/-- All retained backend payloads, including controller metadata for all
blocks and host calls.  The `+1`s also cover currently live stack frames. -/
def heapCells (singlePayload blocks callbackCalls hostCalls P I Q callCapacity : ℕ) : ℕ :=
  64 * (singlePayload + 1) * (blocks + 1) * (callbackCalls + 1) * (hostCalls + 1) +
    metadataCells P I Q callCapacity * (blocks + 1) * (hostCalls + 1)

/-- A direct retained-layout count is below the majorant, including all
backend callbacks, and arrays and history belonging to every host/block. -/
theorem retained_layout_le_heap (singlePayload blocks callbackCalls hostCalls P I Q callCapacity : ℕ) :
    singlePayload * blocks * callbackCalls * hostCalls +
        (P + I + Q + callCapacity) * blocks * hostCalls ≤
      heapCells singlePayload blocks callbackCalls hostCalls P I Q callCapacity := by
  let X:=(singlePayload+1)*(blocks+1)*(callbackCalls+1)*(hostCalls+1)
  let Y:=(P+I+Q+callCapacity+1)*(blocks+1)*(hostCalls+1)
  have hp : singlePayload*blocks*callbackCalls*hostCalls ≤ X :=
    Nat.mul_le_mul (Nat.mul_le_mul (Nat.mul_le_mul (Nat.le_succ _) (Nat.le_succ _))
      (Nat.le_succ _)) (Nat.le_succ _)
  have hm : (P+I+Q+callCapacity)*blocks*hostCalls ≤ Y :=
    Nat.mul_le_mul (Nat.mul_le_mul (Nat.le_succ _) (Nat.le_succ _)) (Nat.le_succ _)
  calc
    _ ≤ X+Y := Nat.add_le_add hp hm
    _ ≤ 64*X+16*Y := Nat.add_le_add
      (Nat.le_mul_of_pos_left X (by decide)) (Nat.le_mul_of_pos_left Y (by decide))
    _ = _ := by dsimp [X,Y,heapCells,metadataCells];ring

/-- A positive logarithmic scale absorbs the additional live object. -/
theorem succ_le_pow_scale (x C s : ℕ) (hs : 1 ≤ s) (hx : x ≤ 2^(C*s)) :
    x + 1 ≤ 2^((C+1)*s) := by
  have hp : 1 ≤ 2^(C*s) := one_le_pow₀ (by decide)
  calc
    _ ≤ 2^(C*s) + 2^(C*s) := Nat.add_le_add hx hp
    _ = 2^(C*s+1) := by rw [pow_succ]; omega
    _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by nlinarith)

/-- A sum of the four metadata dimensions is bounded by their successor
product; this avoids any assumption that a single payload covers metadata. -/
theorem metadata_sum_le_product (P I Q callCapacity : ℕ) :
    P + I + Q + callCapacity + 1 ≤
      (P+1)*(I+1)*(Q+1)*(callCapacity+1) := by
  nlinarith [Nat.zero_le (P*I), Nat.zero_le (P*Q), Nat.zero_le (P*callCapacity),
    Nat.zero_le (I*Q), Nat.zero_le (I*callCapacity), Nat.zero_le (Q*callCapacity),
    Nat.zero_le (P*I*Q), Nat.zero_le (P*I*callCapacity),
    Nat.zero_le (P*Q*callCapacity), Nat.zero_le (I*Q*callCapacity),
    Nat.zero_le (P*I*Q*callCapacity)]

/-- Each factor has an exponential-in-bit-length bound.  Multiplying all
retained payloads and host/controller families still leaves linear address
bit length.  Callback count uses its separately justified capacity. -/
theorem heapCells_le_pow (n singlePayload blocks callbackCalls hostCalls P I Q callCapacity
    cs cb cc ch cP cI cQ : ℕ)
    (hn : 1 ≤ n.size)
    (hs : singlePayload ≤ 2^(cs*n.size))
    (hb : blocks ≤ 2^(cb*n.size))
    (hc : callbackCalls ≤ callCapacity)
    (hcap : callCapacity ≤ 2^(cc*n.size))
    (hh : hostCalls ≤ 2^(ch*n.size))
    (hP : P ≤ 2^(cP*n.size)) (hI : I ≤ 2^(cI*n.size)) (hQ : Q ≤ 2^(cQ*n.size)) :
    heapCells singlePayload blocks callbackCalls hostCalls P I Q callCapacity ≤
      2^((cs+cb+cc+ch+cP+cI+cQ+16)*n.size) := by
  have hs' := succ_le_pow_scale singlePayload cs n.size hn hs
  have hb' := succ_le_pow_scale blocks cb n.size hn hb
  have hc' := succ_le_pow_scale callbackCalls cc n.size hn (hc.trans hcap)
  have hh' := succ_le_pow_scale hostCalls ch n.size hn hh
  have hP' := succ_le_pow_scale P cP n.size hn hP
  have hI' := succ_le_pow_scale I cI n.size hn hI
  have hQ' := succ_le_pow_scale Q cQ n.size hn hQ
  have hcap' := succ_le_pow_scale callCapacity cc n.size hn hcap
  have hmeta : metadataCells P I Q callCapacity * (blocks+1)*(hostCalls+1) ≤
      2^((cP+cI+cQ+cc+cb+ch+10)*n.size) := by
    calc
      _ ≤ 16*((P+1)*(I+1)*(Q+1)*(callCapacity+1))*(blocks+1)*(hostCalls+1) := by
        unfold metadataCells
        gcongr
        exact metadata_sum_le_product P I Q callCapacity
      _ ≤ 16*(2^((cP+1)*n.size)*2^((cI+1)*n.size)*
          2^((cQ+1)*n.size)*2^((cc+1)*n.size))*2^((cb+1)*n.size)*2^((ch+1)*n.size) := by
        gcongr
      _ = 2^(4+(cP+1)*n.size+(cI+1)*n.size+(cQ+1)*n.size+
          (cc+1)*n.size+(cb+1)*n.size+(ch+1)*n.size) := by
        rw [show (16:ℕ)=2^4 by norm_num]
        simp only [←pow_add]
        congr 1
        ring
      _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  have hpay : 64*(singlePayload+1)*(blocks+1)*(callbackCalls+1)*(hostCalls+1) ≤
      2^((cs+cb+cc+ch+10)*n.size) := by
    calc
      _ ≤ 64*2^((cs+1)*n.size)*2^((cb+1)*n.size)*
          2^((cc+1)*n.size)*2^((ch+1)*n.size) := by gcongr
      _ = 2^(6+(cs+1)*n.size+(cb+1)*n.size+(cc+1)*n.size+(ch+1)*n.size) := by
        rw [show (64:ℕ)=2^6 by norm_num]
        simp only [←pow_add]
      _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by nlinarith)
  let C := cs+cb+cc+ch+cP+cI+cQ+10
  have hpC : 64*(singlePayload+1)*(blocks+1)*(callbackCalls+1)*(hostCalls+1) ≤ 2^(C*n.size) :=
    hpay.trans (Nat.pow_le_pow_right (by norm_num) (by dsimp [C]; nlinarith))
  have hmC : metadataCells P I Q callCapacity*(blocks+1)*(hostCalls+1) ≤ 2^(C*n.size) :=
    hmeta.trans (Nat.pow_le_pow_right (by norm_num) (by dsimp [C]; nlinarith))
  calc
    _ ≤ 2^(C*n.size)+2^(C*n.size) := Nat.add_le_add hpC hmC
    _ = 2^(C*n.size+1) := by rw [pow_succ]; omega
    _ ≤ _ := Nat.pow_le_pow_right (by norm_num) (by dsimp [C]; nlinarith)

/-- Any whole-heap address has linear bit length, even though the heap retains
all callbacks and host calls rather than only one backend preparation. -/
theorem heap_index_size (n singlePayload blocks callbackCalls hostCalls P I Q callCapacity
    cs cb cc ch cP cI cQ j : ℕ)
    (hn : 1 ≤ n.size)
    (hs : singlePayload ≤ 2^(cs*n.size))
    (hb : blocks ≤ 2^(cb*n.size))
    (hc : callbackCalls ≤ callCapacity)
    (hcap : callCapacity ≤ 2^(cc*n.size))
    (hh : hostCalls ≤ 2^(ch*n.size))
    (hP : P ≤ 2^(cP*n.size)) (hI : I ≤ 2^(cI*n.size)) (hQ : Q ≤ 2^(cQ*n.size))
    (hj : j < heapCells singlePayload blocks callbackCalls hostCalls P I Q callCapacity) :
    j.size ≤ (cs+cb+cc+ch+cP+cI+cQ+17)*n.size := by
  have hbound := heapCells_le_pow n singlePayload blocks callbackCalls hostCalls P I Q callCapacity
    cs cb cc ch cP cI cQ hn hs hb hc hcap hh hP hI hQ
  have hsize := (Nat.size_le_size ((Nat.le_of_lt hj).trans hbound)).trans_eq Nat.size_pow
  nlinarith

/-- The actual callback list of the binary controller, rather than a declared
number of callbacks, is bounded by its proved stage/round/prime capacity. -/
theorem restarts_heapCells_le_pow {P I Q : ℕ} {Payload : Type*}
    (O : Oracle I Payload) (owner : Owners I Q) (primes : Primes P)
    (blockSizes : Counts I) (remaining : Flags P) (k : ℕ) (lam : NatCell)
    (stages : ℕ) (active : Flags I) (marked : Flags Q)
    (n singlePayload blocks hostCalls cs cb ct ck ch cP cI cQ : ℕ)
    (hn : 1 ≤ n.size)
    (hs : singlePayload ≤ 2^(cs*n.size)) (hb : blocks ≤ 2^(cb*n.size))
    (ht : stages ≤ 2^(ct*n.size)) (hk : k+1 ≤ 2^(ck*n.size))
    (hh : hostCalls ≤ 2^(ch*n.size))
    (hP : P ≤ 2^(cP*n.size)) (hI : I ≤ 2^(cI*n.size)) (hQ : Q ≤ 2^(cQ*n.size)) :
    heapCells singlePayload blocks
        (restartsExec O owner primes blockSizes remaining k lam stages active marked).value.calls.length
        hostCalls P I Q (stages*(k+1)*P) ≤
      2^((cs+cb+(ct+ck+cP)+ch+cP+cI+cQ+16)*n.size) := by
  have hcap : stages*(k+1)*P ≤ 2^((ct+ck+cP)*n.size) := by
    calc
      _ ≤ 2^(ct*n.size)*2^(ck*n.size)*2^(cP*n.size) := by gcongr
      _ = _ := by rw [←pow_add,←pow_add]; congr 1; ring
  exact heapCells_le_pow n singlePayload blocks _ hostCalls P I Q _ cs cb (ct+ck+cP) ch cP cI cQ
    hn hs hb (restartsExec_calls_length O owner primes blockSizes remaining k lam stages active marked)
    hcap hh hP hI hQ

/-- The existing whole-grid payload bound has a linear `n.size` exponent once
`n` is nonzero.  No single-payload address theorem is substituted for the
whole retained heap theorem above. -/
theorem globalPayload_le_pow_size (n N L m q cN cL cm cq : ℕ)
    (hn : 1 ≤ n.size)
    (hN : N ≤ 2^(cN*n.size)) (hL : L ≤ cL*n.size)
    (hm : m ≤ cm*n.size) (hq : q ≤ 2^(cq*n.size)) :
    GlobalAddressBitBounds.globalAddressCells N L m q ≤
      2^((2*(2*cN+cq+12*cL+2*cm+9))*n.size) := by
  exact (GlobalAddressBitBounds.globalAddressCells_le_pow n N L m q cN cL cm cq hN hL hm hq).trans
    (Nat.pow_le_pow_right (by norm_num) (by nlinarith))

/-- Physical bit-cell storage, with a common bound for each retained scalar
or coefficient cell.  The extra unit covers signs, headers, and empty cells. -/
def heapBitCells (singlePayload blocks callbackCalls hostCalls P I Q callCapacity cellWidth : ℕ) : ℕ :=
  heapCells singlePayload blocks callbackCalls hostCalls P I Q callCapacity * (cellWidth+1)

/-- Flattening bounded-width cells does not change the linear address-width
conclusion; the cell-width bound is charged explicitly. -/
theorem heapBitCells_le_pow (n singlePayload blocks callbackCalls hostCalls P I Q callCapacity cellWidth
    cs cb cc ch cP cI cQ cw : ℕ)
    (hn : 1 ≤ n.size)
    (hs : singlePayload ≤ 2^(cs*n.size)) (hb : blocks ≤ 2^(cb*n.size))
    (hc : callbackCalls ≤ callCapacity) (hcap : callCapacity ≤ 2^(cc*n.size))
    (hh : hostCalls ≤ 2^(ch*n.size))
    (hP : P ≤ 2^(cP*n.size)) (hI : I ≤ 2^(cI*n.size)) (hQ : Q ≤ 2^(cQ*n.size))
    (hw : cellWidth ≤ 2^(cw*n.size)) :
    heapBitCells singlePayload blocks callbackCalls hostCalls P I Q callCapacity cellWidth ≤
      2^((cs+cb+cc+ch+cP+cI+cQ+cw+17)*n.size) := by
  have hheap := heapCells_le_pow n singlePayload blocks callbackCalls hostCalls P I Q callCapacity
    cs cb cc ch cP cI cQ hn hs hb hc hcap hh hP hI hQ
  have hw' := succ_le_pow_scale cellWidth cw n.size hn hw
  calc
    _ ≤ 2^((cs+cb+cc+ch+cP+cI+cQ+16)*n.size)*2^((cw+1)*n.size) :=
      Nat.mul_le_mul hheap hw'
    _ = _ := by rw [←pow_add]; congr 1; ring

/-- A physical bit address anywhere in the retained heap is linearly bounded. -/
theorem heap_bit_index_size (n singlePayload blocks callbackCalls hostCalls P I Q callCapacity cellWidth
    cs cb cc ch cP cI cQ cw j : ℕ)
    (hn : 1 ≤ n.size)
    (hs : singlePayload ≤ 2^(cs*n.size)) (hb : blocks ≤ 2^(cb*n.size))
    (hc : callbackCalls ≤ callCapacity) (hcap : callCapacity ≤ 2^(cc*n.size))
    (hh : hostCalls ≤ 2^(ch*n.size))
    (hP : P ≤ 2^(cP*n.size)) (hI : I ≤ 2^(cI*n.size)) (hQ : Q ≤ 2^(cQ*n.size))
    (hw : cellWidth ≤ 2^(cw*n.size))
    (hj : j < heapBitCells singlePayload blocks callbackCalls hostCalls P I Q callCapacity cellWidth) :
    j.size ≤ (cs+cb+cc+ch+cP+cI+cQ+cw+18)*n.size := by
  have hbound := heapBitCells_le_pow n singlePayload blocks callbackCalls hostCalls P I Q callCapacity
    cellWidth cs cb cc ch cP cI cQ cw hn hs hb hc hcap hh hP hI hQ hw
  have hsize := (Nat.size_le_size ((Nat.le_of_lt hj).trans hbound)).trans_eq Nat.size_pow
  nlinarith

/-- Concrete restart execution supplies the actual retained callback count.
All block/host multiplicities and per-cell bit widths remain visible. -/
theorem restarts_heapBitCells_le_pow {P I Q : ℕ} {Payload : Type*}
    (O : Oracle I Payload) (owner : Owners I Q) (primes : Primes P)
    (blockSizes : Counts I) (remaining : Flags P) (k : ℕ) (lam : NatCell)
    (stages : ℕ) (active : Flags I) (marked : Flags Q)
    (n singlePayload blocks hostCalls cellWidth cs cb ct ck ch cP cI cQ cw : ℕ)
    (hn : 1 ≤ n.size)
    (hs : singlePayload ≤ 2^(cs*n.size)) (hb : blocks ≤ 2^(cb*n.size))
    (ht : stages ≤ 2^(ct*n.size)) (hk : k+1 ≤ 2^(ck*n.size))
    (hh : hostCalls ≤ 2^(ch*n.size))
    (hP : P ≤ 2^(cP*n.size)) (hI : I ≤ 2^(cI*n.size)) (hQ : Q ≤ 2^(cQ*n.size))
    (hw : cellWidth ≤ 2^(cw*n.size)) :
    heapBitCells singlePayload blocks
        (restartsExec O owner primes blockSizes remaining k lam stages active marked).value.calls.length
        hostCalls P I Q (stages*(k+1)*P) cellWidth ≤
      2^((cs+cb+(ct+ck+cP)+ch+cP+cI+cQ+cw+17)*n.size) := by
  have hheap := restarts_heapCells_le_pow O owner primes blockSizes remaining k lam stages active marked
    n singlePayload blocks hostCalls cs cb ct ck ch cP cI cQ hn hs hb ht hk hh hP hI hQ
  have hw' := succ_le_pow_scale cellWidth cw n.size hn hw
  calc
    _ ≤ 2^((cs+cb+(ct+ck+cP)+ch+cP+cI+cQ+16)*n.size)*2^((cw+1)*n.size) :=
      Nat.mul_le_mul hheap hw'
    _ = _ := by rw [←pow_add]; congr 1; ring

end ThinMatrix.ControllerHeapPow



namespace ThinMatrix.BinaryControllerPolynomialBounds
open ComputableParameters
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

def basicConstant (κ : ℕ) : ℕ := κ+factorCount+16
def controllerConstant (κ K : ℕ) : ℕ :=
  3*basicConstant κ+K+14*factorCount+6

theorem pow_coeff_mono (s a b : ℕ) (hab : a≤b) : 2^(a*s)≤2^(b*s) :=
  Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_right s hab)

theorem eightScale_pow (n : ℕ) (hs : 1≤n.size) : 8*scale n≤2^(14*n.size) := by
  have h:=ParameterExecution.size_eight_mul (scale n)
  have ht:=ParameterExecution.scale_width n
  have hw : (8*scale n).size≤14*n.size := by omega
  exact (Nat.size_le.mp hw).le

theorem computed_pool_pow (n : ℕ) (hs : 1≤n.size) :
    (computedPool n).card≤2^(14*n.size) := by
  exact (ParameterExecution.pool_card_le (scale n)).trans (eightScale_pow n hs)

theorem blockCount_le_n (n h : ℕ) (hh : 0<h) : CompactBlocks.blockCount n h≤n := by
  unfold CompactBlocks.blockCount
  apply (ceilDiv_le_iff_le_mul hh).mpr
  exact Nat.le_mul_of_pos_left _ hh

theorem incidence_le_cube (n h : ℕ) (hh : 0<h) : EndToEndAPSP.incidenceSize n h≤3*n^3 := by
  unfold EndToEndAPSP.incidenceSize
  have hb:=blockCount_le_n n h hh
  calc
    _ ≤ (n*n)*(n*3) := Nat.mul_le_mul_left _ (Nat.mul_le_mul_right 3 hb)
    _ = _ := by ring

theorem incidence_pow (n h : ℕ) (hh : 0<h) (hs : 1≤n.size) :
    EndToEndAPSP.incidenceSize n h≤2^(5*n.size) := by
  calc
    _ ≤ 3*n^3 := incidence_le_cube n h hh
    _ ≤ 4*(2^n.size)^3 := Nat.mul_le_mul (by decide) (Nat.pow_le_pow_left (AdaptiveBitBounds.nat_le_pow_size n) 3)
    _ = 2^(3*n.size+2) := by rw [show (4:ℕ)=2^2 by decide,←pow_mul,←pow_add];congr 1;ring
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (by omega)

theorem stages_pow (n : ℕ) (hs : 1≤n.size) : (2*n).size≤2^(2*n.size) := by
  have hv : 2*n≤2^(n.size+1) := by
    calc
      _ ≤ 2*2^n.size := Nat.mul_le_mul_left 2 (AdaptiveBitBounds.nat_le_pow_size n)
      _ = _ := by rw [pow_succ];ring
  have hw : (2*n).size≤n.size+2 := by
    exact (Nat.size_le_size hv).trans_eq Nat.size_pow
  have ht : n.size+2≤2^(2*n.size) := by
    have hn : n.size<2^n.size := Nat.lt_two_pow_self
    have h2 : n.size+2≤2^(n.size+1) := by rw [pow_succ];omega
    exact h2.trans (Nat.pow_le_pow_right (by decide) (by omega))
  exact hw.trans ht

theorem input_size_bound (n U κ : ℕ) (hU : U≤n^κ) : U.size≤κ*n.size+1 :=
  (Nat.size_le_size hU).trans (ParameterExecution.size_pow n κ)

theorem lambda_power_width (n U κ R : ℕ) (hs : 1≤n.size) (hU : U≤n^κ) :
    (U.size^R).size≤(R*(κ+1)+1)*n.size := by
  have hu:=input_size_bound n U κ hU
  have hl:=ParameterExecution.size_pow U.size R
  have hsU:=ParameterExecution.size_le_self U.size
  nlinarith

/-- Uniform computed controller widths; the producer bound `W≤n^K` is the
pointwise interface later discharged by the closed backend cost theorem. -/
theorem computed_controller_width (n U W κ K : ℕ) (hn : 3≤n)
    (parameters : CompleteAPSP.Parameters (block n) U)
    (hp : program n U=some parameters) (hU : U≤n^κ) (hW : W≤n^K) :
    (DenseControllerExecution.controllerCap parameters.pool.card
      (EndToEndAPSP.incidenceSize n (block n)) (n*n) parameters.k parameters.lam
      parameters.stages (block n) W (8*scale n)).size ≤ controllerConstant κ K*n.size := by
  have hs : 1≤n.size := Nat.size_pos.mpr (by omega)
  rcases program_sound n U parameters hp with ⟨hpool,hscale,hlam,hk,hM,hstages⟩
  have hP : parameters.pool.card≤2^(basicConstant κ*n.size) := by
    rw [hpool]
    exact (computed_pool_pow n hs).trans (pow_coeff_mono n.size 14 (basicConstant κ) (by unfold basicConstant;omega))
  have hI : EndToEndAPSP.incidenceSize n (block n)≤2^(basicConstant κ*n.size) :=
    (incidence_pow n (block n) (EndToEndAPSP.block_pos n) hs).trans
      (pow_coeff_mono n.size 5 (basicConstant κ) (by unfold basicConstant;omega))
  have hQ : n*n≤2^(basicConstant κ*n.size) := by
    calc
      _ ≤ 2^n.size*2^n.size := Nat.mul_le_mul (AdaptiveBitBounds.nat_le_pow_size n) (AdaptiveBitBounds.nat_le_pow_size n)
      _ = 2^(2*n.size) := by rw [←pow_add];congr 1;omega
      _ ≤ _ := pow_coeff_mono n.size 2 (basicConstant κ) (by unfold basicConstant;omega)
  have hl : parameters.lam≤2^(basicConstant κ*n.size) := by
    rw [hlam]
    exact (ParameterExecution.size_le_self U).trans
      ((AdaptiveBitBounds.original_power_bound n κ U hU).trans
        (pow_coeff_mono n.size κ (basicConstant κ) (by unfold basicConstant;omega)))
  have ht : parameters.stages≤2^(basicConstant κ*n.size) := by
    rw [hstages]
    exact (stages_pow n hs).trans (pow_coeff_mono n.size 2 (basicConstant κ) (by unfold basicConstant;omega))
  have hX : block n≤2^(basicConstant κ*n.size) :=
    (block_le_n n (by omega)).trans ((AdaptiveBitBounds.nat_le_pow_size n).trans
      (by simpa only [Nat.one_mul] using pow_coeff_mono n.size 1 (basicConstant κ) (by unfold basicConstant;omega)))
  have hkp : parameters.k+1=factorCount := by rw [hk];norm_num [factorCount]
  have hround : parameters.k+1≤2^(basicConstant κ*n.size) := by
    rw [hkp]
    have hr : factorCount≤2^factorCount := (show factorCount<2^factorCount from Nat.lt_two_pow_self).le
    exact hr.trans (Nat.pow_le_pow_right (by decide) (by
      have hm : factorCount≤factorCount*n.size := Nat.le_mul_of_pos_right _ hs
      unfold basicConstant
      nlinarith))
  have hpmax:=eightScale_pow n hs
  have hWpow:=AdaptiveBitBounds.original_power_bound n K W hW
  have hc:=ControllerCapPow.controllerCap_size_le parameters.pool.card
    (EndToEndAPSP.incidenceSize n (block n)) (n*n) parameters.k parameters.lam
    parameters.stages (block n) W (8*scale n) (basicConstant κ) K 14 n.size
    hs hP hI hQ hl ht hX hround hWpow hpmax
  simpa only [ControllerCapPow.capExponent,hkp,controllerConstant] using hc

/-- Fixed quadratic prices follow from the proved common scalar/address
widths, rather than a final bound on an opaque execution. -/
theorem executionUnit_poly (n B A cb ca : ℕ) (hB : B≤cb*n.size) (hA : A≤ca*n.size) :
    BinaryControllerExecution.executionUnit B A≤
      (800*(cb+1)^2+100*(cb+ca+2)^2)*(n.size+1)^2 := by
  unfold BinaryControllerExecution.executionUnit BinaryControllerExecution.unit
    BackendScalarBits.backendScalarUnit BackendScalarBits.addressedUnit BackendScalarBits.scalarUnit
  have h₁ : B+1≤(cb+1)*(n.size+1) := by nlinarith
  have h₂ : B+A+2≤(cb+ca+2)*(n.size+1) := by nlinarith
  have hp₁:=Nat.pow_le_pow_left h₁ 2
  have hp₂:=Nat.pow_le_pow_left h₂ 2
  rw [mul_pow] at hp₁ hp₂
  nlinarith

end ThinMatrix.BinaryControllerPolynomialBounds

namespace ThinMatrix.BinaryControllerPolynomialBounds
noncomputable section
attribute [local irreducible] ComputableParameters.factorCount AlignedCertificate.R AlignedCertificate.S
  AdaptiveBitBounds.computedIndexConstant AdaptiveBitBounds.computedLengthConstant
  AdaptiveBitBounds.computedCyclicConstant GlobalAddressBitBounds.computedOuterConstant
open ComputableParameters AdaptiveBitBounds GlobalAddressBitBounds
open BinaryControllerExecution
open ArrayCompositeAlgorithm (Flags Owners)
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

def payloadConstant : ℕ :=
  2*(2*computedOuterConstant+computedCyclicConstant+12*computedLengthConstant+2*computedIndexConstant+9)

def coefficientWidthConstant (κ : ℕ) : ℕ :=
  CoefficientBudget.budgetConstant computedLengthConstant computedIndexConstant computedCyclicConstant κ+
    2*(4*computedIndexConstant+2)^2+20

def cellWidthConstant (κ K : ℕ) : ℕ :=
  coefficientWidthConstant κ+controllerConstant κ K+κ+17

def storedCellWidth (n κ K : ℕ) : ℕ :=
  commonBitWidth n κ computedLengthConstant computedIndexConstant computedCyclicConstant+
    controllerConstant κ K*n.size+(κ+1)*n.size+16

def singlePayloadMajorant (n : ℕ) : ℕ := 2^(payloadConstant*n.size)

def addressConstant (κ K hostExponent : ℕ) : ℕ :=
  payloadConstant+1+(2+factorCount+14)+hostExponent+14+5+2+(cellWidthConstant κ K+2)+18

def hostExponent (degree : ℕ) : ℕ := 2*degree+21
def publicScalarWidth (n κ K : ℕ) : ℕ := controllerConstant κ K*n.size
def publicAddressWidth (n κ K degree : ℕ) : ℕ := addressConstant κ K (hostExponent degree)*n.size

def publicUnitConstant (κ K degree : ℕ) : ℕ :=
  800*(controllerConstant κ K+1)^2+
    100*(controllerConstant κ K+addressConstant κ K (hostExponent degree)+2)^2

theorem public_units_poly (n κ K degree : ℕ) :
    executionUnit (publicScalarWidth n κ K) (publicAddressWidth n κ K degree)≤
      publicUnitConstant κ K degree*(n.size+1)^2 := by
  exact executionUnit_poly n _ _ _ _ le_rfl le_rfl


end
end ThinMatrix.BinaryControllerPolynomialBounds

#print axioms ThinMatrix.BinaryControllerPolynomialBounds.computed_controller_width
#print axioms ThinMatrix.BinaryControllerPolynomialBounds.executionUnit_poly
#print axioms ThinMatrix.ControllerHeapPow.restarts_heapBitCells_le_pow
#print axioms ThinMatrix.BinaryControllerPolynomialBounds.public_units_poly


namespace ThinMatrix.BinaryControllerPolynomialBounds
noncomputable section
attribute [local irreducible] ComputableParameters.factorCount AlignedCertificate.R AlignedCertificate.S
  AdaptiveBitBounds.computedIndexConstant AdaptiveBitBounds.computedLengthConstant
  AdaptiveBitBounds.computedCyclicConstant GlobalAddressBitBounds.computedOuterConstant
open ComputableParameters AdaptiveBitBounds GlobalAddressBitBounds BinaryControllerExecution
open ArrayCompositeAlgorithm (Flags Owners)
set_option maxHeartbeats 2000000
set_option maxRecDepth 10000

private theorem address_sub_one (a b c d : ℕ) :
    a+1+b+c+14+5+2+(d+2)+18-1=a+1+b+c+14+5+2+(d+2)+17 := by omega

/-- Every adaptive shape has the same whole-grid payload exponent. -/
theorem computed_payload_majorant (n : ℕ) (hn : 3≤n)
    (call : ComputedPhaseGeometry.Call AlignedCertificate.R n) :
    globalAddressCells (PhaseGeometry.outerSize call AlignedCertificate.S n)
      (Nat.ceil (RealCertificate.c*(ComputedPhaseGeometry.innerPower n call AlignedCertificate.S:ℝ)))
      (ComputedPhaseGeometry.innerPower n call AlignedCertificate.S) (call.cyclic AlignedCertificate.S)≤
    singlePayloadMajorant n := by
  exact ControllerHeapPow.globalPayload_le_pow_size n _ _ _ _ computedOuterConstant
    computedLengthConstant computedIndexConstant computedCyclicConstant
    (Nat.size_pos.mpr (by omega)) (computed_outer_le_pow_size n hn call)
    (computed_roundedLength_le_size n hn call) (computed_innerPower_le_size n hn call)
    (computed_cyclic_le_pow_size n hn call)

#print axioms ThinMatrix.BinaryControllerPolynomialBounds.computed_payload_majorant

theorem storedCellWidth_poly (n κ K : ℕ) :
    storedCellWidth n κ K≤cellWidthConstant κ K*(n.size+1)^2 := by
  have hs : n.size≤(n.size+1)^2 := by nlinarith
  have hp : 1≤(n.size+1)^2 := by nlinarith
  dsimp [storedCellWidth,commonBitWidth,cellWidthConstant,coefficientWidthConstant]
  have h₁:=Nat.mul_le_mul_left (controllerConstant κ K) hs
  have h₂:=Nat.mul_le_mul_left (κ+1) hs
  have h₃:=Nat.mul_le_mul_left 16 hp
  nlinarith

#print axioms ThinMatrix.BinaryControllerPolynomialBounds.storedCellWidth_poly

/-- Quadratic logarithmic scalar storage still has a fixed polynomial-size
address space. No unit-size binary scalar is assumed. -/
theorem storedCellWidth_pow (n κ K : ℕ) (hs : 1≤n.size) :
    storedCellWidth n κ K≤2^((cellWidthConstant κ K+2)*n.size) := by
  have hconst : cellWidthConstant κ K≤2^(cellWidthConstant κ K) :=
    (show cellWidthConstant κ K<2^(cellWidthConstant κ K) from Nat.lt_two_pow_self).le
  have hsize : n.size+1≤2^n.size := Nat.lt_two_pow_self
  calc
    _ ≤ cellWidthConstant κ K*(n.size+1)^2 := storedCellWidth_poly n κ K
    _ ≤ 2^(cellWidthConstant κ K)*(2^n.size)^2 :=
      Nat.mul_le_mul hconst (Nat.pow_le_pow_left hsize 2)
    _ = 2^(cellWidthConstant κ K+2*n.size) := by rw [←pow_mul,←pow_add];congr 1;ring
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (by
      have h:=Nat.le_mul_of_pos_right (cellWidthConstant κ K) hs
      nlinarith)

#print axioms ThinMatrix.BinaryControllerPolynomialBounds.storedCellWidth_pow

/-- Exact binary host call count is bounded without correctness or cost
premises on its callback. It follows only from its actual schedule. -/
theorem binary_host_calls_budget {n : ℕ} {Payload : Type} (O : BinaryAPSPCaller.Oracle n Payload)
    (w : BinaryAPSPCaller.OptionalTable n) (W degree : ℕ) (hW : W≤n^degree) :
    (BinaryAPSPCaller.apsp O w W).calls.length≤2*(AdaptiveQueryBitBounds.budget n degree)^2 := by
  rw [BinaryAPSPCaller.apsp,BinaryAPSPCaller.squared_calls]
  have hr:=AdaptiveQueryBitBounds.rounds_bound n
  have hd:=AdaptiveQueryBitBounds.bit_depth_bound n degree W hW
  have hb:=AdaptiveQueryBitBounds.budget_bounds n degree
  have hmul:=Nat.mul_le_mul hr (Nat.mul_le_mul_left 2 hd)
  have hfinal:=Nat.mul_le_mul hb.1 (Nat.mul_le_mul_left 2 (by omega : AdaptiveQueryBitBounds.exponent n degree+5≤AdaptiveQueryBitBounds.budget n degree))
  nlinarith


#print axioms ThinMatrix.BinaryControllerPolynomialBounds.binary_host_calls_budget

theorem binary_host_calls_pow {n : ℕ} {Payload : Type} (O : BinaryAPSPCaller.Oracle n Payload)
    (w : BinaryAPSPCaller.OptionalTable n) (W degree : ℕ) (hs : 1≤n.size) (hW : W≤n^degree) :
    (BinaryAPSPCaller.apsp O w W).calls.length≤2^(hostExponent degree*n.size) := by
  have hb:=binary_host_calls_budget O w W degree hW
  have hsize : n.size+1≤2^n.size := Nat.lt_two_pow_self
  have hd : degree+9≤2^(degree+9) := (show degree+9<2^(degree+9) from Nat.lt_two_pow_self).le
  have hbudget : AdaptiveQueryBitBounds.budget n degree≤2^((degree+10)*n.size) := by
    have hpoly : AdaptiveQueryBitBounds.budget n degree≤(degree+9)*(n.size+1) := by
      unfold AdaptiveQueryBitBounds.budget
      nlinarith
    calc
      _ ≤ (degree+9)*(n.size+1) := hpoly
      _ ≤ 2^(degree+9)*2^n.size := Nat.mul_le_mul hd hsize
      _ = 2^(degree+9+n.size) := by rw [←pow_add]
      _ ≤ _ := Nat.pow_le_pow_right (by decide) (by
        have ht:=Nat.le_mul_of_pos_right (degree+9) hs
        nlinarith)
  calc
    _ ≤ 2*(AdaptiveQueryBitBounds.budget n degree)^2 := hb
    _ ≤ 2*(2^((degree+10)*n.size))^2 := Nat.mul_le_mul_left 2 (Nat.pow_le_pow_left hbudget 2)
    _ = 2^(1+((degree+10)*n.size)*2) := by rw [←pow_mul];change 2^1*2^_=_;rw [←pow_add]
    _ ≤ _ := Nat.pow_le_pow_right (by decide) (by unfold hostExponent;nlinarith)

#print axioms ThinMatrix.BinaryControllerPolynomialBounds.binary_host_calls_pow

/-- The `U` type parameter does not affect the retained-layout formula. -/
def retainedHeap {n U : ℕ} (κ K hostCalls callbackCalls : ℕ)
    (parameters : CompleteAPSP.Parameters (block n) U) : ℕ :=
  ControllerHeapPow.heapBitCells (singlePayloadMajorant n) (CompactBlocks.blockCount n (block n))
    callbackCalls hostCalls parameters.pool.card (EndToEndAPSP.incidenceSize n (block n)) (n*n)
    (parameters.stages*(parameters.k+1)*parameters.pool.card) (storedCellWidth n κ K)

theorem retainedHeap_le_pow {n U : ℕ} (κ K Ch hostCalls callbackCalls : ℕ) (hn : 3≤n)
    (parameters : CompleteAPSP.Parameters (block n) U) (hp : program n U=some parameters)
    (hcalls : callbackCalls≤parameters.stages*(parameters.k+1)*parameters.pool.card)
    (hhost : hostCalls≤2^(Ch*n.size)) :
    retainedHeap κ K hostCalls callbackCalls parameters≤2^((addressConstant κ K Ch-1)*n.size) := by
  have hs : 1≤n.size := Nat.size_pos.mpr (by omega)
  rcases program_sound n U parameters hp with ⟨hpool,hscale,hlam,hk,hM,hstages⟩
  have hR : 1≤factorCount := by norm_num [factorCount]
  have hkp : parameters.k+1=factorCount := by rw [hk,Nat.sub_add_cancel hR]
  have hr : factorCount≤2^(factorCount*n.size) := by
    have ht : factorCount≤2^factorCount := (show factorCount<2^factorCount from Nat.lt_two_pow_self).le
    exact ht.trans (Nat.pow_le_pow_right (by decide) (Nat.le_mul_of_pos_right _ hs))
  have hcap : parameters.stages*(parameters.k+1)*parameters.pool.card≤2^((2+factorCount+14)*n.size) := by
    rw [hstages,hkp,hpool]
    calc
      _ ≤ 2^(2*n.size)*2^(factorCount*n.size)*2^(14*n.size) :=
        Nat.mul_le_mul (Nat.mul_le_mul (stages_pow n hs) hr) (computed_pool_pow n hs)
      _ = _ := by rw [←pow_add,←pow_add,Nat.add_mul,Nat.add_mul]
  have hblocks : CompactBlocks.blockCount n (block n)≤2^(1*n.size) := by
    simpa only [Nat.one_mul] using (blockCount_le_n n (block n) (EndToEndAPSP.block_pos n)).trans (nat_le_pow_size n)
  have hQ : n*n≤2^(2*n.size) := by
    calc
      _ ≤ 2^n.size*2^n.size := Nat.mul_le_mul (nat_le_pow_size n) (nat_le_pow_size n)
      _ = _ := by rw [←pow_add];congr 1;omega
  have h:=ControllerHeapPow.heapBitCells_le_pow n (singlePayloadMajorant n)
    (CompactBlocks.blockCount n (block n)) callbackCalls hostCalls parameters.pool.card
    (EndToEndAPSP.incidenceSize n (block n)) (n*n)
    (parameters.stages*(parameters.k+1)*parameters.pool.card) (storedCellWidth n κ K)
    payloadConstant 1 (2+factorCount+14) Ch 14 5 2 (cellWidthConstant κ K+2)
    hs le_rfl hblocks hcalls hcap hhost (by rw [hpool];exact computed_pool_pow n hs)
    (incidence_pow n (block n) (EndToEndAPSP.block_pos n) hs) hQ (storedCellWidth_pow n κ K hs)
  change _≤2^((payloadConstant+1+(2+factorCount+14)+Ch+14+5+2+(cellWidthConstant κ K+2)+18-1)*n.size)
  rw [address_sub_one]
  exact h

#print axioms ThinMatrix.BinaryControllerPolynomialBounds.retainedHeap_le_pow

/-- Every bit address in the complete retained heap has fixed linear width. -/
theorem retainedHeap_index_size {n U : ℕ} (κ K Ch hostCalls callbackCalls j : ℕ) (hn : 3≤n)
    (parameters : CompleteAPSP.Parameters (block n) U) (hp : program n U=some parameters)
    (hcalls : callbackCalls≤parameters.stages*(parameters.k+1)*parameters.pool.card)
    (hhost : hostCalls≤2^(Ch*n.size)) (hj : j<retainedHeap κ K hostCalls callbackCalls parameters) :
    j.size≤addressConstant κ K Ch*n.size := by
  have hs : 1≤n.size := Nat.size_pos.mpr (by omega)
  have h:=(Nat.size_le_size ((Nat.le_of_lt hj).trans (retainedHeap_le_pow κ K Ch hostCalls callbackCalls hn parameters hp hcalls hhost))).trans_eq Nat.size_pow
  have hc : 1≤addressConstant κ K Ch := by unfold addressConstant;omega
  calc
    _ ≤ (addressConstant κ K Ch-1)*n.size+1 := h
    _ ≤ (addressConstant κ K Ch-1)*n.size+n.size := Nat.add_le_add_left hs _
    _ = ((addressConstant κ K Ch-1)+1)*n.size := by rw [Nat.add_mul,Nat.one_mul]
    _ = _ := by rw [Nat.sub_add_cancel hc]


/-- A finite list of actual callback counts may vary with every adaptive host
query. Its sum is bounded by the proved common per-query capacity. -/
theorem sum_callback_counts_le (counts : List ℕ) (capacity hostCalls : ℕ)
    (hc : ∀c∈counts,c≤capacity) (hl : counts.length≤hostCalls) :
    counts.sum≤capacity*hostCalls := by
  have hs : counts.sum≤capacity*counts.length := by
    induction counts with
    |nil=>simp
    |cons c cs ih=>
      have h:=hc c (by simp)
      have ht:=ih (by intro x hx;exact hc x (by simp [hx])) (by simp only [List.length_cons] at hl;omega)
      simp only [List.sum_cons,List.length_cons]
      nlinarith
  exact hs.trans (Nat.mul_le_mul_left capacity hl)

/-- The layout bound permits independently varying actual callback counts;
all producer payloads and every host's metadata/history remain retained. -/
theorem varying_callback_layout (singlePayload blocks hostCalls P I Q capacity : ℕ)
    (counts : List ℕ) (hc : ∀c∈counts,c≤capacity) (hl : counts.length≤hostCalls) :
    singlePayload*blocks*counts.sum+(P+I+Q+capacity)*blocks*counts.length≤
      ControllerHeapPow.heapCells singlePayload blocks capacity hostCalls P I Q capacity := by
  have hs:=sum_callback_counts_le counts capacity hostCalls hc hl
  have hp:=Nat.mul_le_mul_left (singlePayload*blocks) hs
  have hm:=Nat.mul_le_mul_left ((P+I+Q+capacity)*blocks) hl
  calc
    _ ≤ singlePayload*blocks*(capacity*hostCalls)+(P+I+Q+capacity)*blocks*hostCalls := Nat.add_le_add hp hm
    _ = singlePayload*blocks*capacity*hostCalls+(P+I+Q+capacity)*blocks*hostCalls := by ring
    _ ≤ _ := ControllerHeapPow.retained_layout_le_heap singlePayload blocks capacity hostCalls P I Q capacity

/-- Complete retained heap of the actual binary APSP host. The common callback
capacity is charged for every host query; adaptive counts need not coincide. -/
def completeHeap {n U : ℕ} {Payload : Type} (κ K : ℕ)
    (host : BinaryAPSPCaller.Oracle n Payload) (w : BinaryAPSPCaller.OptionalTable n) (W : ℕ)
    (parameters : CompleteAPSP.Parameters (block n) U) : ℕ :=
  retainedHeap κ K (BinaryAPSPCaller.apsp host w W).calls.length
    (parameters.stages*(parameters.k+1)*parameters.pool.card) parameters

/-- Closed address width: original polynomial edge bounds and the computed
program suffice; no final host-call or global-address hypothesis remains. -/
theorem completeHeap_index_size {n U : ℕ} {Payload : Type} (κ K degree j : ℕ) (hn : 3≤n)
    (host : BinaryAPSPCaller.Oracle n Payload) (w : BinaryAPSPCaller.OptionalTable n)
    (W : ℕ) (hW : W≤n^degree) (parameters : CompleteAPSP.Parameters (block n) U)
    (hp : program n U=some parameters) (hj : j<completeHeap κ K host w W parameters) :
    j.size≤addressConstant κ K (hostExponent degree)*n.size := by
  exact retainedHeap_index_size κ K (hostExponent degree) _ _ j hn parameters hp le_rfl
    (binary_host_calls_pow host w W degree (Nat.size_pos.mpr (by omega)) hW) hj

/-- Every actual binary-controller callback trace fits the common per-host
capacity used by the complete retained heap. -/
theorem actual_callback_capacity {n U : ℕ} {Payload : Type*}
    (parameters : CompleteAPSP.Parameters (block n) U)
    (O : BinaryControllerExecution.Oracle (EndToEndAPSP.incidenceSize n (block n)) Payload)
    (owner : Owners (EndToEndAPSP.incidenceSize n (block n)) (n*n))
    (primes : Primes parameters.pool.card)
    (base : Counts (EndToEndAPSP.incidenceSize n (block n))) (remaining : Flags parameters.pool.card)
    (lam : NatCell) (active : Flags (EndToEndAPSP.incidenceSize n (block n))) (marked : Flags (n*n)) :
    (restartsExec O owner primes base remaining parameters.k lam parameters.stages active marked).value.calls.length≤
      parameters.stages*(parameters.k+1)*parameters.pool.card :=
  restartsExec_calls_length O owner primes base remaining parameters.k lam parameters.stages active marked


end
end ThinMatrix.BinaryControllerPolynomialBounds


namespace ThinMatrix.BinaryControllerPolynomialBounds
noncomputable section
open ComputableParameters BinaryControllerExecution
open ArrayCompositeAlgorithm (Flags Owners)
set_option maxHeartbeats 2000000
theorem binary_unit_mono {B C : ℕ} (h : B≤C) : unit B≤unit C := by
  unfold unit BackendScalarBits.backendScalarUnit BackendScalarBits.scalarUnit
  exact Nat.mul_le_mul_left 8 (Nat.mul_le_mul_left 100 (Nat.pow_le_pow_left (Nat.add_le_add_right h 1) 2))

/-- The public word price can be selected with fixed `K` before proving the
producer's eventual work bound. Arithmetic uses the concrete count/input caps. -/
theorem public_controller_bits {n U : ℕ} {Payload : Type*} (κ K : ℕ) (hn : 3≤n)
    (parameters : CompleteAPSP.Parameters (block n) U) (hp : program n U=some parameters)
    (hU : U≤n^κ)
    (O : BinaryControllerExecution.Oracle (EndToEndAPSP.incidenceSize n (block n)) Payload)
    (hO : OracleCountsBound O (block n))
    (owner : Owners (EndToEndAPSP.incidenceSize n (block n)) (n*n))
    (primes : Primes parameters.pool.card) (hprimes : ∀p,(primes.get p).control≤8*scale n)
    (base : Counts (EndToEndAPSP.incidenceSize n (block n))) (hbase : ∀i,nview (base.get i)≤block n)
    (remaining : Flags parameters.pool.card) (lam : NatCell) (hlam : nview lam=parameters.lam)
    (active : Flags (EndToEndAPSP.incidenceSize n (block n))) (marked : Flags (n*n)) :
    let out:=restartsExec O owner primes base remaining parameters.k lam parameters.stages active marked
    out.bitSteps≤unit (publicScalarWidth n κ K)*out.arithSites := by
  have hc:=computed_controller_width n U (n^K) κ K hn parameters hp hU le_rfl
  have hb:=restartsExec_price_cap (W:=n^K) O hO owner primes hprimes (by
    have hscale:= (program_sound n U parameters hp).2.1
    have hpos:=parameters.P_pos
    omega) base hbase remaining parameters.k lam parameters.stages active marked
  rw [hlam] at hb
  exact hb.trans (Nat.mul_le_mul_right _ (binary_unit_mono hc))

/-- Actual executed arithmetic and public control sites receive the fixed
quadratic word price; the loop ledger is an independently proved upper bound. -/
theorem public_controller_charge {n U : ℕ} {Payload : Type*} (κ K degree : ℕ) (hn : 3≤n)
    (parameters : CompleteAPSP.Parameters (block n) U) (hp : program n U=some parameters)
    (hU : U≤n^κ)
    (O : BinaryControllerExecution.Oracle (EndToEndAPSP.incidenceSize n (block n)) Payload)
    (hO : OracleCountsBound O (block n))
    (owner : Owners (EndToEndAPSP.incidenceSize n (block n)) (n*n))
    (primes : Primes parameters.pool.card) (hprimes : ∀p,(primes.get p).control≤8*scale n)
    (base : Counts (EndToEndAPSP.incidenceSize n (block n))) (hbase : ∀i,nview (base.get i)≤block n)
    (remaining : Flags parameters.pool.card) (lam : NatCell) (hlam : nview lam=parameters.lam)
    (active : Flags (EndToEndAPSP.incidenceSize n (block n))) (marked : Flags (n*n)) :
    let out:=restartsExec O owner primes base remaining parameters.k lam parameters.stages active marked
    let B:=publicScalarWidth n κ K
    let A:=publicAddressWidth n κ K degree
    out.bitSteps+BackendScalarBits.addressedUnit B A*out.controlSites≤
      publicUnitConstant κ K degree*(n.size+1)^2*
        (512*(parameters.k+1)*(parameters.k+2)*out.value.controllerVisits+1) := by
  have hb:=public_controller_bits κ K hn parameters hp hU O hO owner primes hprimes base hbase remaining lam hlam active marked
  have hpool : 0<parameters.pool.card := by
    have ht:=parameters.threshold
    have hs:=parameters.size
    omega
  have hw:=restartsExec_workSites_by_visits O owner primes base remaining parameters.k lam parameters.stages active marked hpool
  have hp₁:=executionWork_bound (A:=publicAddressWidth n κ K degree)
    (restartsExec O owner primes base remaining parameters.k lam parameters.stages active marked) hb
  unfold executionWork at hp₁
  have hp₂:=Nat.le_of_add_le_add_right hp₁
  exact hp₂.trans ((Nat.mul_le_mul_left _ hw).trans
    (Nat.mul_le_mul_right _ (public_units_poly n κ K degree)))

/-- Concrete setup widths for the computed public prime, block, lambda, and
original-cap cells. These are derived before adaptive inputs are processed. -/
theorem computed_public_widths (n U κ : ℕ) (hn : 3≤n)
    (parameters : CompleteAPSP.Parameters (block n) U) (hp : program n U=some parameters)
    (hU : U≤n^κ) :
    (8*scale n).size≤14*n.size ∧ (block n).size≤n.size ∧
    parameters.lam.size≤(κ+1)*n.size ∧ U.size≤(κ+1)*n.size := by
  have hs : 1≤n.size := Nat.size_pos.mpr (by omega)
  have hscale:=ParameterExecution.size_eight_mul (scale n)
  have hscale₂:=ParameterExecution.scale_width n
  have hu:=input_size_bound n U κ hU
  have hlam:parameters.lam=U.size := (program_sound n U parameters hp).2.2.1
  have hl:=ParameterExecution.size_le_self parameters.lam
  refine ⟨by omega,Nat.size_le_size (block_le_n n (by omega)),?_,?_⟩
  · rw [hlam] at hl ⊢
    nlinarith
  · nlinarith

end

end ThinMatrix.BinaryControllerPolynomialBounds


namespace ThinMatrix.BinaryControllerPolynomialBounds
noncomputable section
open ComputableParameters BinaryControllerExecution
set_option maxHeartbeats 1000000
/-- A coarse fixed-exponent bound on the public polynomial input-degree factor. -/
theorem cubic_degree_bound (degree : ℕ) :
    (degree+9)^3≤2^(2*degree+10) := by
  induction degree with
  | zero => norm_num
  | succ degree ih =>
    calc
      _ ≤4*(degree+9)^3 := by
        calc
          _ ≤(degree+1+9)^3+(3*degree^3+78*degree^2+672*degree+1916) := Nat.le_add_right _ _
          _ = _ := by ring
      _ ≤4*2^(2*degree+10) := Nat.mul_le_mul_left 4 ih
      _ = _ := by rw [show 2*(degree+1)+10=(2*degree+10)+2 by omega,pow_add];ring

/-- Scalar bit storage for the complete host can be charged by multiplying
its number of scheduled calls by the proved host width majorant. -/
def hostStorageMultiplicity (n degree : ℕ) : ℕ :=
  10*AdaptiveQueryBitBounds.budget n degree+1

theorem binary_host_storage_pow {n : ℕ} {Payload : Type}
    (O : BinaryAPSPCaller.Oracle n Payload) (w : BinaryAPSPCaller.OptionalTable n)
    (W degree : ℕ) (hs : 1≤n.size) (hW : W≤n^degree) :
    (BinaryAPSPCaller.apsp O w W).calls.length*hostStorageMultiplicity n degree≤
      2^(hostExponent degree*n.size) := by
  let b:=AdaptiveQueryBitBounds.budget n degree
  have hb:1≤b := by dsimp [b,AdaptiveQueryBitBounds.budget];omega
  have hbudget : b≤(degree+9)*(n.size+1) := by
    dsimp [b,AdaptiveQueryBitBounds.budget];nlinarith
  have hsize : n.size+1≤2^n.size := Nat.lt_two_pow_self
  have hc:=binary_host_calls_budget O w W degree hW
  change (BinaryAPSPCaller.apsp O w W).calls.length≤2*b^2 at hc
  have hwidth : hostStorageMultiplicity n degree≤11*b := by
    dsimp [hostStorageMultiplicity,b];omega
  calc
    _ ≤(2*b^2)*(11*b) := Nat.mul_le_mul hc hwidth
    _ =22*b^3 := by ring
    _ ≤22*((degree+9)*(n.size+1))^3 := Nat.mul_le_mul_left 22 (Nat.pow_le_pow_left hbudget 3)
    _ =22*(degree+9)^3*(n.size+1)^3 := by ring
    _ ≤2^5*2^(2*degree+10)*(2^n.size)^3 :=
      Nat.mul_le_mul (Nat.mul_le_mul (by norm_num) (cubic_degree_bound degree))
        (Nat.pow_le_pow_left hsize 3)
    _ =2^(5+(2*degree+10)+n.size*3) := by rw [←pow_mul,←pow_add,←pow_add]
    _ ≤_ := Nat.pow_le_pow_right (by decide) (by
      unfold hostExponent
      have ht:=Nat.le_mul_of_pos_right (2*degree+15) hs
      nlinarith)

/-- Whole retained producer/history layout with the host's variable-width
scalar storage charged explicitly by `hostStorageMultiplicity`. -/
def completeHostHeap {n U : ℕ} {Payload : Type} (κ K degree : ℕ)
    (host : BinaryAPSPCaller.Oracle n Payload) (w : BinaryAPSPCaller.OptionalTable n) (W : ℕ)
    (parameters : CompleteAPSP.Parameters (block n) U) : ℕ :=
  retainedHeap κ K ((BinaryAPSPCaller.apsp host w W).calls.length*hostStorageMultiplicity n degree)
    (parameters.stages*(parameters.k+1)*parameters.pool.card) parameters

theorem completeHostHeap_index_size {n U : ℕ} {Payload : Type} (κ K degree j : ℕ) (hn : 3≤n)
    (host : BinaryAPSPCaller.Oracle n Payload) (w : BinaryAPSPCaller.OptionalTable n)
    (W : ℕ) (hW : W≤n^degree) (parameters : CompleteAPSP.Parameters (block n) U)
    (hp : program n U=some parameters) (hj : j<completeHostHeap κ K degree host w W parameters) :
    j.size≤addressConstant κ K (hostExponent degree)*n.size := by
  exact retainedHeap_index_size κ K (hostExponent degree) _ _ j hn parameters hp le_rfl
    (binary_host_storage_pow host w W degree (Nat.size_pos.mpr (by omega)) hW) hj

#print axioms ThinMatrix.BinaryControllerPolynomialBounds.binary_host_storage_pow
#print axioms ThinMatrix.BinaryControllerPolynomialBounds.completeHostHeap_index_size
end
end ThinMatrix.BinaryControllerPolynomialBounds

#print axioms ThinMatrix.BinaryControllerPolynomialBounds.retainedHeap_index_size
#print axioms ThinMatrix.BinaryControllerPolynomialBounds.varying_callback_layout
#print axioms ThinMatrix.BinaryControllerPolynomialBounds.completeHeap_index_size
#print axioms ThinMatrix.BinaryControllerPolynomialBounds.actual_callback_capacity
#print axioms ThinMatrix.BinaryControllerPolynomialBounds.public_controller_bits
#print axioms ThinMatrix.BinaryControllerPolynomialBounds.public_controller_charge
#print axioms ThinMatrix.BinaryControllerPolynomialBounds.computed_public_widths
