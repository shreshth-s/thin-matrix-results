import HalfSourceBinaryState
import ExactHalfCroppedEmbedding

set_option autoImplicit false

/-! Translation generation with retained keys, power tables, binary sums and
explicitly decoded score indices. The old score arithmetic charge is carried
through every step. Control counts cover key formation and binary-state loops,
not the score kernel's native enumeration, row/sign closures, table indices or
power-table control. Consequently this is still a partial setup cost. -/
namespace ThinMatrix.HalfSourceRetainedTranslations
open WalshEmbedding HalfSourceGreedy HalfSourceList
open BinaryCell BinaryGroupedCoordinates BinaryGroupedPreparation HalfSourceBinaryState

structure State (m : ℕ) where
  entries : List (Cube m)
  memory : Vector Entry (2^m)

def State.sums {m : ℕ} (s : State m) (a : Characters m) : ℤ :=
  (s.memory.get (HalfSourceIntegerGreedy.cubeIndex m a.val)).2

def initial {m : ℕ} (keys : Vector (HalfSourceStoredKeys.Key m) (2^m)) : State m :=
  ⟨[],keys.map (fun _ => (zero,0))⟩

def build (m : ℕ) (ts : HalfSourceBinaryScores.Tables)
    (keys : Vector (HalfSourceStoredKeys.Key m) (2^m)) : ℕ → Run (State m)
  | 0 => ⟨initial keys,1,8*keys.toArray.size+8⟩
  | j+1 =>
      let prev := build m ts keys j
      let selected := HalfSourceBinarySelection.select m ts prev.value.sums m (fun a => a.val) (fun _ => false)
      let next := advance keys selected.value prev.value.memory
      ⟨⟨HalfSourceIntegerGreedy.vectorBits selected.value::prev.value.entries,next.value⟩,
        prev.bitSteps+selected.bitSteps+next.bitSteps,prev.control+next.control+12⟩

theorem build_cached (m : ℕ) (ts : HalfSourceBinaryScores.Tables)
    (keys : Vector (HalfSourceStoredKeys.Key m) (2^m)) (j : ℕ) (i : Fin (2^m)) :
    ((build m ts keys j).value.memory.get i).2=view ((build m ts keys j).value.memory.get i).1 := by
  cases j with
  | zero => simp [build,initial]
  | succ j => exact advance_cached _ _ _ i

theorem build_abs (m : ℕ) (ts : HalfSourceBinaryScores.Tables)
    (keys : Vector (HalfSourceStoredKeys.Key m) (2^m)) (j : ℕ) (i : Fin (2^m)) :
    (view ((build m ts keys j).value.memory.get i).1).natAbs≤j := by
  induction j generalizing i with
  | zero => simp [build,initial]
  | succ j ih => exact advance_abs j _ _ _ ih i

theorem advance_sum (m : ℕ) (s : State m) (hc : ∀ i,(s.memory.get i).2=view (s.memory.get i).1)
    (d : Vector Bool m) (a : Characters m) :
    ((advance (HalfSourceStoredKeys.produce m).value d s.memory).value.get
      (HalfSourceIntegerGreedy.cubeIndex m a.val)).2=s.sums a+sign (dotBits a.val d.get) := by
  have ha : (((HalfSourceStoredKeys.produce m).value.get
      (HalfSourceIntegerGreedy.cubeIndex m a.val))).active=true :=
    (HalfSourceStoredKeys.produce_active m _).mpr (by simpa using a.property)
  simp only [advance,tabulate_get,update_cached,update_view,ha,↓reduceIte,
    HalfSourceStoredKeys.produce_row,Equiv.symm_apply_apply]
  rw [←hc]
  rfl

theorem build_refines (m : ℕ) (ts : HalfSourceBinaryScores.Tables) (j : ℕ) :
    (build m ts (HalfSourceStoredKeys.produce m).value j).value.entries=
      (HalfSourceBinarySelection.build m ts j).value.entries ∧
    (build m ts (HalfSourceStoredKeys.produce m).value j).value.sums=
      (HalfSourceBinarySelection.build m ts j).value.sums := by
  induction j with
  | zero =>
      constructor
      · rfl
      · funext a
        simp [build,initial,State.sums,HalfSourceBinarySelection.build]
  | succ j ih =>
      constructor
      · simp only [build,HalfSourceBinarySelection.build,ih.1,ih.2]
      · funext a
        change ((advance _ _ _).value.get _).2=_
        rw [advance_sum m _ (build_cached m ts _ j)]
        simp only [HalfSourceBinarySelection.build,HalfSourceIntegerGreedy.sums_mk,ih.2]
        rfl

theorem build_control (m : ℕ) (ts : HalfSourceBinaryScores.Tables)
    (keys : Vector (HalfSourceStoredKeys.Key m) (2^m)) (j : ℕ) :
    (build m ts keys j).control≤8*2^m+8+j*(2^m*(6*m+45)+20) := by
  induction j with
  | zero => simp [build]
  | succ j ih =>
      have hn := advance_control keys
        (HalfSourceBinarySelection.select m ts (build m ts keys j).value.sums m (fun a => a.val) (fun _ => false)).value
        (build m ts keys j).value.memory
      simp only [build]
      nlinarith

theorem updateBudget_mono {j k : ℕ} (h : j≤k) : updateBudget j≤updateBudget k := by
  have hh := Nat.size_le_size (Nat.add_le_add_right h 1)
  unfold updateBudget BackendScalarBits.backendScalarUnit BackendScalarBits.scalarUnit
  gcongr

theorem build_bits (m j : ℕ) (hj : j≤64*m^3) :
    (build m (HalfSourceBinaryScores.tables m).value (HalfSourceStoredKeys.produce m).value j).bitSteps≤
      j*(m*HalfSourceBinarySelection.choiceBound m+1+2^m*updateBudget (64*m^3))+1 := by
  induction j with
  | zero => simp [build]
  | succ j ih =>
      have hj' : j≤64*m^3 := by omega
      have hi := ih hj'
      have hs : ∀ a, |(build m (HalfSourceBinaryScores.tables m).value (HalfSourceStoredKeys.produce m).value j).value.sums a|≤64*m^3 := by
        rw [(build_refines m _ j).2]
        exact HalfSourceBinarySelection.build_sum_bound m _ j hj'
      have hp := HalfSourceBinarySelection.select_price m _ hs m (fun a => a.val) (fun _ => false)
      have hn := advance_bits j (HalfSourceStoredKeys.produce m).value
        (HalfSourceBinarySelection.select m (HalfSourceBinaryScores.tables m).value
          (build m (HalfSourceBinaryScores.tables m).value (HalfSourceStoredKeys.produce m).value j).value.sums
          m (fun a => a.val) (fun _ => false)).value
        (build m (HalfSourceBinaryScores.tables m).value (HalfSourceStoredKeys.produce m).value j).value.memory
        (build_abs m _ _ j)
      have hm := Nat.mul_le_mul_left (2^m) (updateBudget_mono hj')
      simp only [build]
      nlinarith

theorem build_keeps_arithmetic (m : ℕ) (ts : HalfSourceBinaryScores.Tables) (j : ℕ) :
    (HalfSourceBinarySelection.build m ts j).bitSteps≤
      (build m ts (HalfSourceStoredKeys.produce m).value j).bitSteps := by
  induction j with
  | zero => rfl
  | succ j ih =>
      simp only [build,HalfSourceBinarySelection.build,(build_refines m ts j).2]
      omega

structure Payload (m : ℕ) where
  keys : Vector (HalfSourceStoredKeys.Key m) (2^m)
  powers : HalfSourceBinaryScores.Tables
  state : State m

def Payload.entries {m : ℕ} (p : Payload m) : List (Cube m) :=
  if m=0 then [WalshEmbedding.zeroBits m] else p.state.entries

def produce (m : ℕ) : Run (Payload m) :=
  let keys := HalfSourceStoredKeys.produce m
  let powers := HalfSourceBinaryScores.tables m
  let state := build m powers.value keys.value (64*m^3)
  ⟨⟨keys.value,powers.value,state.value⟩,keys.bitSteps+powers.bitSteps+state.bitSteps,
    keys.control+state.control+16⟩

theorem produce_entries (m : ℕ) : (produce m).value.entries=ExactHalfCroppedEmbedding.shifts m := by
  simp only [produce,Payload.entries,ExactHalfCroppedEmbedding.shifts,
    (build_refines m _ _).1,HalfSourceBinarySelection.translations]

theorem produce_keeps_arithmetic (m : ℕ) :
    (HalfSourceBinarySelection.translations m).bitSteps≤(produce m).bitSteps := by
  have hb := build_keeps_arithmetic m (HalfSourceBinaryScores.tables m).value (64*m^3)
  simp only [produce,HalfSourceBinarySelection.translations]
  omega

def arithmeticBudget (m : ℕ) : ℕ :=
  2*(HalfSourceBinaryScores.width m+2)+2*((2*HalfSourceIntegerScores.K m+1)*
    (2*HalfSourceIntegerScores.K m*HalfSourceBinaryScores.unit m+1))+
    64*m^3*(m*HalfSourceBinarySelection.choiceBound m+1+2^m*updateBudget (64*m^3))+1

theorem produce_bits (m : ℕ) : (produce m).bitSteps≤arithmeticBudget m := by
  have hp := HalfSourceBinaryScores.tables_price m
  have hb := build_bits m (64*m^3) le_rfl
  simp only [produce,HalfSourceStoredKeys.produce_bits,arithmeticBudget]
  omega

def indexedControlBudget (m : ℕ) : ℕ :=
  2^m*(4*m*m+20*m+50)+4*m+17+8*2^m+8+64*m^3*(2^m*(6*m+45)+20)+16

theorem produce_control (m : ℕ) : (produce m).control ≤ indexedControlBudget m := by
  have hk := HalfSourceStoredKeys.produce_control m
  have hb := build_control m (HalfSourceBinaryScores.tables m).value (HalfSourceStoredKeys.produce m).value (64*m^3)
  simp only [produce,indexedControlBudget]
  omega

#print axioms build_cached
#print axioms build_abs
#print axioms advance_sum
#print axioms build_refines
#print axioms build_control
#print axioms updateBudget_mono
#print axioms build_bits
#print axioms build_keeps_arithmetic
#print axioms produce_entries
#print axioms produce_keeps_arithmetic
#print axioms produce_bits
#print axioms produce_control
end ThinMatrix.HalfSourceRetainedTranslations
