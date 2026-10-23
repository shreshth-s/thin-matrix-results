import Mathlib

set_option autoImplicit false

/-! Retained integer numerator polynomials and node denominators.
Arithmetic counts integer additions/subtractions/multiplications. Control
counts indexed reads/writes/branches and is not a binary address charge.
Arrays retain coefficients through degree d; no rational additions occur. -/
namespace ThinMatrix.IntegerInterpolationRows
open scoped BigOperators
open Polynomial

def shift {d : ℕ} (v : Vector ℤ (d+1)) (k : Fin (d+1)) : ℤ :=
  Fin.cases 0 (fun j => v.get j.castSucc) k

def linear {d : ℕ} (z : ℤ) (v : Vector ℤ (d+1)) : Vector ℤ (d+1) :=
  Vector.ofFn (fun k => shift v k-z*v.get k)

structure Row (d : ℕ) where
  coeff : Vector ℤ (d+1)
  den : ℤ
  operations : ℕ
  control : ℕ

def build (d : ℕ) (i : Fin (d+1)) : List (Fin (d+1)) → Row d
  | [] => ⟨Vector.ofFn (fun k => if k.val=0 then 1 else 0),1,0,d+1⟩
  | j::xs =>
    let child := build d i xs
    if j=i then ⟨child.coeff,child.den,child.operations,child.control+3⟩
    else ⟨linear j.val child.coeff,((i.val:ℤ)-j.val)*child.den,
      child.operations+2*(d+1)+2,child.control+8*(d+1)+8⟩

def row (d : ℕ) (i : Fin (d+1)) : Row d := build d i (List.ofFn id)

noncomputable def poly {d : ℕ} (i : Fin (d+1)) (xs : List (Fin (d+1))) : ℤ[X] :=
  (xs.map (fun j => if j=i then 1 else X-C (j.val:ℤ))).prod

def denom {d : ℕ} (i : Fin (d+1)) (xs : List (Fin (d+1))) : ℤ :=
  (xs.map (fun j => if j=i then 1 else (i.val:ℤ)-j.val)).prod

theorem linear_coeff {d : ℕ} (v : Vector ℤ (d+1)) (p : ℤ[X]) (z : ℤ)
    (hv : ∀ k,v.get k=p.coeff k.val) (k : Fin (d+1)) :
    (linear z v).get k=((X-C z)*p).coeff k.val := by
  simp only [linear,Vector.get_ofFn,sub_mul,coeff_sub,coeff_C_mul]
  refine Fin.cases ?_ (fun j => ?_) k
  · simp [shift,hv]
  · simp [shift,hv,coeff_X_mul]

theorem build_coeff (d : ℕ) (i : Fin (d+1)) (xs : List (Fin (d+1))) (k : Fin (d+1)) :
    (build d i xs).coeff.get k=(poly i xs).coeff k.val := by
  induction xs generalizing k with
  | nil =>
      simp only [build,Vector.get_ofFn,poly,List.map_nil,List.prod_nil]
      rw [← C_1,coeff_C]
  | cons j xs ih =>
      by_cases h : j=i
      · simp only [build,h,↓reduceIte,poly,List.map_cons,List.prod_cons,one_mul] at *
        exact ih k
      · simp only [build,h,↓reduceIte,poly,List.map_cons,List.prod_cons]
        exact linear_coeff _ _ _ (fun a => by simpa only [poly] using ih a) k

theorem build_den (d : ℕ) (i : Fin (d+1)) (xs : List (Fin (d+1))) :
    (build d i xs).den=denom i xs := by
  induction xs with
  | nil => rfl
  | cons j xs ih => by_cases h : j=i <;> simp [build,denom,h,ih,denom] at *

theorem denom_ne_zero {d : ℕ} (i : Fin (d+1)) (xs : List (Fin (d+1))) : denom i xs≠0 := by
  induction xs with
  | nil => simp [denom]
  | cons j xs ih =>
      simp only [denom,List.map_cons,List.prod_cons]
      split_ifs with h
      · simpa only [one_mul,denom] using ih
      · apply mul_ne_zero _ ih
        apply sub_ne_zero.mpr
        intro he
        apply h
        apply Fin.ext
        exact_mod_cast he.symm

theorem build_operations (d : ℕ) (i : Fin (d+1)) (xs : List (Fin (d+1))) :
    (build d i xs).operations ≤ xs.length*(2*(d+1)+2) := by
  induction xs with
  | nil => simp [build]
  | cons j xs ih =>
      simp only [build,List.length_cons]
      split_ifs <;> dsimp <;> nlinarith

theorem build_control (d : ℕ) (i : Fin (d+1)) (xs : List (Fin (d+1))) :
    (build d i xs).control ≤ (d+1)+xs.length*(8*(d+1)+8) := by
  induction xs with
  | nil => simp [build]
  | cons j xs ih =>
      simp only [build,List.length_cons]
      split_ifs <;> dsimp <;> nlinarith

def envelope (d : ℕ) : ℕ := 2*d+2

theorem build_magnitude (d : ℕ) (i : Fin (d+1)) (xs : List (Fin (d+1))) :
    (∀ k,((build d i xs).coeff.get k).natAbs≤envelope d^xs.length) ∧
      (build d i xs).den.natAbs≤envelope d^xs.length := by
  induction xs with
  | nil => simp [build];intro k;split_ifs <;> simp
  | cons j xs ih =>
      have hg : 1≤envelope d := by unfold envelope;omega
      have hp : envelope d^xs.length≤envelope d^(xs.length+1) := Nat.pow_le_pow_right hg (by omega)
      by_cases h : j=i
      · simpa only [build,h,↓reduceIte,List.length_cons] using
          And.intro (fun k => (ih.1 k).trans hp) (ih.2.trans hp)
      · simp only [build,h,↓reduceIte,List.length_cons]
        constructor
        · intro k
          have hs : (shift (build d i xs).coeff k).natAbs≤envelope d^xs.length := by
            refine Fin.cases ?_ (fun a => ?_) k
            · simp [shift]
            · simpa [shift] using ih.1 a.castSucc
          calc
            _ ≤ (shift (build d i xs).coeff k).natAbs+j.val*((build d i xs).coeff.get k).natAbs := by
              simpa [linear,Int.natAbs_mul] using Int.natAbs_sub_le (shift (build d i xs).coeff k)
                ((j.val:ℤ)*(build d i xs).coeff.get k)
            _ ≤ envelope d^xs.length + d*(envelope d^xs.length) :=
              Nat.add_le_add hs (Nat.mul_le_mul (by omega) (ih.1 k))
            _ = (d+1)*(envelope d^xs.length) := by ring
            _ ≤ _ := by
              rw [pow_succ,mul_comm _ (envelope d)]
              exact Nat.mul_le_mul_right _ (by unfold envelope;omega)
        · have hd : ((i.val:ℤ)-j.val).natAbs≤2*d := by
            have hh := Int.natAbs_sub_le (i.val:ℤ) (j.val:ℤ)
            simp only [Int.natAbs_natCast] at hh
            omega
          simp only [Int.natAbs_mul]
          calc
            _ ≤ (2*d)*(envelope d^xs.length) := Nat.mul_le_mul hd ih.2
            _ ≤ _ := by
              rw [pow_succ,mul_comm _ (envelope d)]
              exact Nat.mul_le_mul_right _ (by unfold envelope;omega)

#print axioms linear_coeff
#print axioms build_coeff
#print axioms build_den
#print axioms denom_ne_zero
#print axioms build_operations
#print axioms build_control
#print axioms build_magnitude
end ThinMatrix.IntegerInterpolationRows
