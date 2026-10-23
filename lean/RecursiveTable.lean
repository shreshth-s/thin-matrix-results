import FiniteMatrixPowers

set_option autoImplicit false

/-! Explicit finite layouts for stored recursive tables. Variable-depth
addresses are built by product quotient/remainder; no finite-choice operation
is performed at a recursive level. -/
namespace ThinMatrix.RecursiveTable
open scoped BigOperators
open PolynomialDegeneration

structure Layout (I : Type) where
  size : ℕ
  index : I ≃ Fin size

def fin (n : ℕ) : Layout (Fin n) := ⟨n,Equiv.refl _⟩
def unit : Layout PUnit := ⟨1,{
  toFun := fun _ => 0
  invFun := fun _ => PUnit.unit
  left_inv := fun _ => rfl
  right_inv := fun _ => Subsingleton.elim _ _ }⟩

def prod {I J : Type} (a : Layout I) (b : Layout J) : Layout (I×J) :=
  ⟨a.size*b.size,(a.index.prodCongr b.index).trans finProdFinEquiv⟩

def power {I : Type} (a : Layout I) : (k : ℕ) → Layout (PowerIndex I k)
  | 0 => unit
  | k+1 => prod a (power a k)

@[simp] theorem power_size {I : Type} (a : Layout I) (k : ℕ) :
    (power a k).size=a.size^k := by
  induction k with
  | zero => rfl
  | succ k ih => simp [power,prod,ih,pow_succ']

abbrev Table {I : Type} (a : Layout I) (R : Type) := Vector R a.size

def read {I R : Type} {a : Layout I} (x : Table a R) (i : I) : R := x.get (a.index i)
def store {I R : Type} (a : Layout I) (f : I → R) : Table a R :=
  Vector.ofFn (fun i => f (a.index.symm i))

@[simp] theorem read_store {I R : Type} (a : Layout I) (f : I → R) (i : I) :
    read (store a f) i=f i := by simp [read,store]

theorem size_eq_card {I : Type} [Fintype I] (a : Layout I) : a.size=Fintype.card I :=
  (Fintype.card_fin a.size).symm.trans (Fintype.card_congr a.index).symm

theorem sum_store {I R : Type} [Fintype I] [AddCommMonoid R]
    (a : Layout I) (f : I → R) : (store a f).toList.sum=∑ i,f i := by
  simp only [store,Vector.toList_ofFn,List.sum_ofFn]
  exact a.index.symm.sum_comp f

/-- The counter records ring operations, separately from table cells and
indexed-control work. Binary pricing is a further refinement. -/
structure Run (A : Type) where
  value : A
  arithmetic : ℕ
  control : ℕ

def tabulate {I R : Type} (a : Layout I) (f : I → Run R) : Run (Table a R) :=
  let rows := store a f
  ⟨rows.map Run.value,(rows.toList.map Run.arithmetic).sum,
    (rows.toList.map Run.control).sum+32*a.size+8⟩

@[simp] theorem tabulate_read {I R : Type} (a : Layout I) (f : I → Run R) (i : I) :
    read (tabulate a f).value i=(f i).value := by simp [tabulate,read,store]

theorem tabulate_arithmetic {I R : Type} [Fintype I] (a : Layout I) (f : I → Run R) :
    (tabulate a f).arithmetic=∑ i,(f i).arithmetic := by
  simpa [tabulate,store,List.map_ofFn,Function.comp_apply,Vector.toList_ofFn,List.sum_ofFn]
    using a.index.symm.sum_comp (fun i => (f i).arithmetic)

theorem tabulate_control {I R : Type} [Fintype I] (a : Layout I) (f : I → Run R) :
    (tabulate a f).control=(∑ i,(f i).control)+32*a.size+8 := by
  simp only [tabulate,store,Vector.toList_ofFn,List.map_ofFn,List.sum_ofFn,Function.comp_apply]
  exact congrArg (fun n => n+32*a.size+8) (a.index.symm.sum_comp (fun i => (f i).control))

#print axioms power_size
#print axioms read_store
#print axioms size_eq_card
#print axioms sum_store
#print axioms tabulate_read
#print axioms tabulate_arithmetic
#print axioms tabulate_control
end ThinMatrix.RecursiveTable
