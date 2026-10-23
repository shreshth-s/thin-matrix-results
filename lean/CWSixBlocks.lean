import CWExactDecomposition
import FiniteMatrixTensor

set_option autoImplicit false

namespace ThinMatrix.CWSixBlocks
open scoped BigOperators
open FiniteTrilinear CWPolynomialCertificate
variable {R : Type*} [CommRing R]

def color {q : ℕ} : Axis q → Fin 3
  | none => 0
  | some none => 2
  | some (some _) => 1

theorem pair011 (q : ℕ) (a b : Fin q) :
    target (R:=R) q origin (privateLabel a) (privateLabel b)=(if a=b then 1 else 0) := by
  simp [target,basis,origin,terminal,privateLabel,mul_ite,eq_comm]
theorem pair101 (q : ℕ) (a b : Fin q) :
    target (R:=R) q (privateLabel a) origin (privateLabel b)=(if a=b then 1 else 0) := by
  simp [target,basis,origin,terminal,privateLabel,mul_ite,eq_comm]
theorem pair110 (q : ℕ) (a b : Fin q) :
    target (R:=R) q (privateLabel a) (privateLabel b) origin=(if a=b then 1 else 0) := by
  simp [target,basis,origin,terminal,privateLabel,mul_ite,eq_comm]
theorem corner002 (q : ℕ) : target (R:=R) q origin origin terminal=1 := by
  simp [target,basis,origin,terminal,privateLabel]
theorem corner020 (q : ℕ) : target (R:=R) q origin terminal origin=1 := by
  simp [target,basis,origin,terminal,privateLabel]
theorem corner200 (q : ℕ) : target (R:=R) q terminal origin origin=1 := by
  simp [target,basis,origin,terminal,privateLabel]

theorem zero_outside (q : ℕ) (x y z : Axis q)
    (h : (color x).val+(color y).val+(color z).val≠2) : target (R:=R) q x y z=0 := by
  rcases x with _ | (_ | x) <;> rcases y with _ | (_ | y) <;> rcases z with _ | (_ | z) <;>
    simp_all [color,target,basis,origin,terminal,privateLabel]

inductive Block where
  | b011 | b101 | b110 | b002 | b020 | b200
  deriving DecidableEq, Repr

instance : Fintype Block := ⟨{.b011,.b101,.b110,.b002,.b020,.b200},by intro b;cases b <;> simp⟩

def cx : Block → Fin 3 | .b011 => 0 | .b101 => 1 | .b110 => 1 | .b002 => 0 | .b020 => 0 | .b200 => 2
def cy : Block → Fin 3 | .b011 => 1 | .b101 => 0 | .b110 => 1 | .b002 => 0 | .b020 => 2 | .b200 => 0
def cz : Block → Fin 3 | .b011 => 1 | .b101 => 1 | .b110 => 0 | .b002 => 2 | .b020 => 0 | .b200 => 0

abbrev Row (q : ℕ) : Block → Type | .b101 => Fin q | _ => PUnit
abbrev Inner (q : ℕ) : Block → Type | .b110 => Fin q | _ => PUnit
abbrev Col (q : ℕ) : Block → Type | .b011 => Fin q | _ => PUnit
instance (q : ℕ) (b : Block) : Fintype (Row q b) := by cases b <;> dsimp [Row] <;> infer_instance
instance (q : ℕ) (b : Block) : Fintype (Inner q b) := by cases b <;> dsimp [Inner] <;> infer_instance
instance (q : ℕ) (b : Block) : Fintype (Col q b) := by cases b <;> dsimp [Col] <;> infer_instance
instance (q : ℕ) (b : Block) : DecidableEq (Row q b) := by cases b <;> dsimp [Row] <;> infer_instance
instance (q : ℕ) (b : Block) : DecidableEq (Inner q b) := by cases b <;> dsimp [Inner] <;> infer_instance
instance (q : ℕ) (b : Block) : DecidableEq (Col q b) := by cases b <;> dsimp [Col] <;> infer_instance

def left (q : ℕ) : (b : Block) → Row q b×Inner q b → Axis q
  | .b011,_ => origin | .b101,x => privateLabel x.1 | .b110,x => privateLabel x.2
  | .b002,_ => origin | .b020,_ => origin | .b200,_ => terminal
def middle (q : ℕ) : (b : Block) → Inner q b×Col q b → Axis q
  | .b011,x => privateLabel x.2 | .b101,_ => origin | .b110,x => privateLabel x.1
  | .b002,_ => origin | .b020,_ => terminal | .b200,_ => origin
def right (q : ℕ) : (b : Block) → Col q b×Row q b → Axis q
  | .b011,x => privateLabel x.1 | .b101,x => privateLabel x.2 | .b110,_ => origin
  | .b002,_ => terminal | .b020,_ => origin | .b200,_ => origin

theorem colors (q : ℕ) (b : Block) (x : Row q b×Inner q b)
    (y : Inner q b×Col q b) (z : Col q b×Row q b) :
    color (left q b x)=cx b ∧ color (middle q b y)=cy b ∧ color (right q b z)=cz b := by
  cases b <;> simp [left,middle,right,cx,cy,cz,color,origin,terminal,privateLabel]

theorem identity (q : ℕ) (b : Block) (x : Row q b×Inner q b)
    (y : Inner q b×Col q b) (z : Col q b×Row q b) :
    target (R:=R) q (left q b x) (middle q b y) (right q b z)=
      FiniteMatrixTensor.coeff (Row q b) (Inner q b) (Col q b) R x y z := by
  cases b <;> dsimp [Row,Inner,Col] at x y z ⊢ <;> simp [left,middle,right,pair011,pair101,pair110,corner002,corner020,corner200,
    FiniteMatrixTensor.coeff,Row,Inner,Col,eq_comm]

theorem left_injective (q : ℕ) (b : Block) : Function.Injective (left q b) := by
  cases b <;> intro x y h <;> cases x <;> cases y <;>
    dsimp [Row,Inner] at * <;> simp_all [left,privateLabel]
theorem middle_injective (q : ℕ) (b : Block) : Function.Injective (middle q b) := by
  cases b <;> intro x y h <;> cases x <;> cases y <;>
    dsimp [Inner,Col] at * <;> simp_all [middle,privateLabel]
theorem right_injective (q : ℕ) (b : Block) : Function.Injective (right q b) := by
  cases b <;> intro x y h <;> cases x <;> cases y <;>
    dsimp [Row,Col] at * <;> simp_all [right,privateLabel]

def decode (x y z : Fin 3) : Block :=
  if x=2 then .b200 else if y=2 then .b020 else if z=2 then .b002
  else if x=0 then .b011 else if y=0 then .b101 else .b110

theorem decode_colors (x y z : Fin 3) (h : x.val+y.val+z.val=2) :
    cx (decode x y z)=x ∧ cy (decode x y z)=y ∧ cz (decode x y z)=z := by
  fin_cases x <;> fin_cases y <;> fin_cases z <;> simp_all [decode,cx,cy,cz]

theorem decode_block (b : Block) : decode (cx b) (cy b) (cz b)=b := by cases b <;> rfl
theorem color_sum (b : Block) : (cx b).val+(cy b).val+(cz b).val=2 := by cases b <;> rfl

#print axioms pair011
#print axioms pair101
#print axioms pair110
#print axioms corner002
#print axioms corner020
#print axioms corner200
#print axioms zero_outside
#print axioms colors
#print axioms identity
#print axioms left_injective
#print axioms middle_injective
#print axioms right_injective
#print axioms decode_colors
#print axioms decode_block
#print axioms color_sum
end ThinMatrix.CWSixBlocks
