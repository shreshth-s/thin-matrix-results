import BinaryGroupedPreparation
import HalfSourceBinarySelection
import HalfSourceMaskWork

set_option autoImplicit false

/-! Materialized character keys for translation construction. The recurrence
uses bounded natural division by two and stores every bit. Its control charge
is an indexed-register count, not unit bit cost for native Nat operations or
a claim about Lean's evaluator. Binary address lowering remains separate. -/
namespace ThinMatrix.HalfSourceStoredKeys
open BinaryGroupedCoordinates BinaryGroupedPreparation WalshEmbedding

def bits : (m : ℕ) → ℕ → Run (Vector Bool m)
  | 0, _ => ⟨#v[],0,4⟩
  | m+1, code =>
      let rest := bits m (code/2)
      let head := finTwoEquiv (⟨code%2,Nat.mod_lt _ (by decide)⟩ : Fin 2)
      ⟨Vector.ofFn (Fin.cons head rest.value.get),rest.bitSteps,rest.control+8*(m+1)+12⟩

theorem bits_get (m code : ℕ) (i : Fin m) :
    (bits m code).value.get i=finTwoEquiv (⟨code/2^i.val%2,Nat.mod_lt _ (by decide)⟩ : Fin 2) := by
  induction m generalizing code with
  | zero => exact Fin.elim0 i
  | succ m ih =>
      refine Fin.cases ?_ (fun j => ?_) i
      · simp only [bits,Vector.get_ofFn,Fin.cons_zero,Fin.val_zero,pow_zero,Nat.div_one]
      · simp only [bits,Vector.get_ofFn,Fin.cons_succ,ih,Fin.val_succ]
        congr 2
        rw [Nat.div_div_eq_div_mul,pow_succ']

theorem bits_cube (m : ℕ) (i : Fin (2^m)) :
    (bits m i.val).value.get=(HalfSourceIntegerGreedy.cubeIndex m).symm i := by
  funext j
  rw [bits_get]
  rfl

theorem bits_cost (m code : ℕ) : (bits m code).bitSteps=0 ∧ (bits m code).control=4*m*m+16*m+4 := by
  induction m generalizing code with
  | zero => simp [bits]
  | succ m ih =>
      simp only [bits,(ih (code/2)).1,(ih (code/2)).2]
      constructor
      · trivial
      · ring

def zeroScan : List Bool → Bool × ℕ
  | [] => (true,2)
  | b::bs => let tail := zeroScan bs; ((!b && tail.1),tail.2+4)

theorem zeroScan_value {m : ℕ} (v : Vector Bool m) :
    (zeroScan v.toList).1=true ↔ v.get=zeroBits m := by
  have hs (xs : List Bool) : (zeroScan xs).1=true ↔ ∀ b∈xs,b=false := by
    induction xs with
    | nil => simp [zeroScan]
    | cons b bs ih => cases b <;> simp [zeroScan,ih]
  rw [hs]
  constructor
  · intro hh
    funext i
    exact hh (v.get i) (by
      change v[i.val] ∈ v.toList
      exact Vector.mem_toList_iff.mpr (Vector.getElem_mem i.isLt))
  · intro hh b hb
    obtain ⟨i,hi,he⟩ := Vector.mem_iff_getElem.mp (Vector.mem_toList_iff.mp hb)
    have hi' : v.get ⟨i,hi⟩=b := he
    rw [←hi',hh];rfl

theorem zeroScan_control (xs : List Bool) : (zeroScan xs).2=4*xs.length+2 := by
  induction xs with
  | nil => rfl
  | cons b bs ih => simp only [zeroScan,ih,List.length_cons];omega

structure Key (m : ℕ) where
  row : Vector Bool m
  active : Bool

def key (m code : ℕ) : Run (Key m) :=
  let row := bits m code
  let scan := zeroScan row.value.toList
  ⟨⟨row.value,!scan.1⟩,row.bitSteps,row.control+scan.2+8⟩

def dimension : ℕ → ℕ × ℕ
  | 0 => (1,1)
  | m+1 => let prev := dimension m; (2*prev.1,prev.2+4)

theorem dimension_value (m : ℕ) : (dimension m).1=2^m := by
  induction m with
  | zero => rfl
  | succ m ih => simp only [dimension,ih,pow_succ']

theorem dimension_control (m : ℕ) : (dimension m).2=4*m+1 := by
  induction m with
  | zero => rfl
  | succ m ih => simp only [dimension,ih];omega

def produce (m : ℕ) : Run (Vector (Key m) (2^m)) :=
  let size := dimension m
  let shape := (Vector.replicate size.1 ()).cast (dimension_value m)
  let rows := tabulate shape (fun i => key m i.val)
  ⟨rows.value,rows.bitSteps,rows.control+size.2+4*shape.toArray.size+8⟩

theorem produce_row (m : ℕ) (i : Fin (2^m)) :
    ((produce m).value.get i).row.get=(HalfSourceIntegerGreedy.cubeIndex m).symm i := by
  simp only [produce,tabulate_get,key,bits_cube]

theorem produce_active (m : ℕ) (i : Fin (2^m)) :
    ((produce m).value.get i).active=true ↔ (HalfSourceIntegerGreedy.cubeIndex m).symm i≠zeroBits m := by
  simp only [produce,tabulate_get,key]
  have hz := zeroScan_value (bits m i.val).value
  rw [bits_cube] at hz
  cases hb : (zeroScan (bits m i.val).value.toList).1 <;> simp_all

theorem produce_bits (m : ℕ) : (produce m).bitSteps=0 := by
  simp only [produce,tabulate_bits_eq,key,(bits_cost m _).1,Finset.sum_const_zero]

theorem produce_control (m : ℕ) : (produce m).control≤2^m*(4*m*m+20*m+50)+4*m+17 := by
  have hh := tabulate_control ((Vector.replicate (dimension m).1 ()).cast (dimension_value m))
    (fun i => key m i.val) (W:=4*m*m+20*m+14) (by
      intro i
      simp only [key,(bits_cost m _).2,zeroScan_control,Vector.length_toList]
      omega)
  simp only [produce,dimension_control,Vector.size_toArray]
  nlinarith

#print axioms bits_get
#print axioms bits_cube
#print axioms bits_cost
#print axioms zeroScan_value
#print axioms zeroScan_control
#print axioms dimension_value
#print axioms dimension_control
#print axioms produce_row
#print axioms produce_active
#print axioms produce_bits
#print axioms produce_control
end ThinMatrix.HalfSourceStoredKeys
