import RecursiveBilinearStep
import BinaryCell
import BinaryGroupedCoordinates

set_option autoImplicit false

namespace ThinMatrix.BinaryRecursiveDot
open scoped BigOperators
open RecursiveTable BinaryCell
abbrev Run := BinaryGroupedCoordinates.Run

def tabulate {I V : Type} (a : Layout I) (f : I → Run V) : Run (Table a V) :=
  let rows := store a f
  ⟨rows.map (fun v => v.value),(rows.toList.map (fun v => v.bitSteps)).sum,
    (rows.toList.map (fun v => v.control)).sum+32*a.size+8⟩

@[simp] theorem tabulate_read {I V : Type} (a : Layout I) (f : I → Run V) (i : I) :
    read (tabulate a f).value i=(f i).value := by simp [tabulate,RecursiveTable.read,store]

theorem tabulate_bits {I V : Type} [Fintype I] (a : Layout I) (f : I → Run V) :
    (tabulate a f).bitSteps=∑ i,(f i).bitSteps := by
  simp only [tabulate,store,Vector.toList_ofFn,List.map_ofFn,Function.comp_apply,List.sum_ofFn]
  exact a.index.symm.sum_comp (fun i => (f i).bitSteps)

theorem tabulate_control {I V : Type} [Fintype I] (a : Layout I) (f : I → Run V) :
    (tabulate a f).control=(∑ i,(f i).control)+32*a.size+8 := by
  simp only [tabulate,store,Vector.toList_ofFn,List.map_ofFn,Function.comp_apply,List.sum_ofFn]
  exact congrArg (fun n => n+32*a.size+8) (a.index.symm.sum_comp (fun i => (f i).control))

def dotList : List (Cell×Cell) → Run Cell
  | [] => ⟨zero,0,2⟩
  | p::ps =>
      let tail := dotList ps
      let product := mul p.1 p.2
      let sum := add product.value tail.value
      ⟨sum.value,tail.bitSteps+product.bitSteps+sum.bitSteps,tail.control+12⟩

theorem dotList_view (ps : List (Cell×Cell)) :
    view (dotList ps).value=(ps.map (fun p => view p.1*view p.2)).sum := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [dotList,ih]

theorem dotList_control (ps : List (Cell×Cell)) : (dotList ps).control=12*ps.length+2 := by
  induction ps with
  | nil => rfl
  | cons p ps ih => simp [dotList,ih];omega

theorem dotList_abs (ps : List (Cell×Cell)) (H B : ℕ)
    (h : ∀ p∈ps,(view p.1).natAbs≤H ∧ (view p.2).natAbs≤B) :
    (view (dotList ps).value).natAbs≤ps.length*H*B := by
  induction ps with
  | nil => simp [dotList]
  | cons p ps ih =>
    have ht := ih (fun q hq => h q (List.mem_cons_of_mem _ hq))
    have hp := h p (by simp)
    simp only [dotList,add_view,mul_view,List.length_cons]
    have hh := (Int.natAbs_add_le (view p.1*view p.2) (view (dotList ps).value)).trans
      (Nat.add_le_add (by simpa only [Int.natAbs_mul] using Nat.mul_le_mul hp.1 hp.2) ht)
    nlinarith

theorem dotList_bits (ps : List (Cell×Cell)) (H B N W : ℕ)
    (hN : ps.length≤N) (hH : H.size≤W) (hB : B.size≤W) (hp : (N*H*B).size≤W)
    (h : ∀ p∈ps,(view p.1).natAbs≤H ∧ (view p.2).natAbs≤B) :
    (dotList ps).bitSteps≤2*ps.length*BackendScalarBits.backendScalarUnit W := by
  induction ps with
  | nil => simp [dotList]
  | cons p ps ih =>
    have ht := ih (by simp only [List.length_cons] at hN;omega)
      (fun q hq => h q (List.mem_cons_of_mem _ hq))
    have hv := h p (by simp)
    have hm := mul_price W p.1 p.2 ((Nat.size_le_size hv.1).trans hH) ((Nat.size_le_size hv.2).trans hB)
    have hprod : (view (mul p.1 p.2).value).natAbs≤N*H*B := by
      rw [mul_view,Int.natAbs_mul]
      have hpos : 1≤N := by simp only [List.length_cons] at hN;omega
      exact (Nat.mul_le_mul hv.1 hv.2).trans
        (by simpa only [Nat.mul_assoc] using Nat.le_mul_of_pos_left (H*B) hpos)
    have hrest : (view (dotList ps).value).natAbs≤N*H*B :=
      (dotList_abs ps H B (fun q hq => h q (List.mem_cons_of_mem _ hq))).trans
        (Nat.mul_le_mul_right B (Nat.mul_le_mul_right H (by simp only [List.length_cons] at hN;omega)))
    have ha := add_price W (mul p.1 p.2).value (dotList ps).value
      ((Nat.size_le_size hprod).trans hp) ((Nat.size_le_size hrest).trans hp)
    simp only [dotList,List.length_cons]
    nlinarith

def dot {I : Type} (a : Layout I) (f g : I → Cell) : Run Cell :=
  let inputs := store a (fun i => (f i,g i))
  let out := dotList inputs.toList
  ⟨out.value,out.bitSteps,out.control+8*a.size+2⟩

theorem dot_view {I : Type} [Fintype I] (a : Layout I) (f g : I → Cell) :
    view (dot a f g).value=∑ i,view (f i)*view (g i) := by
  simp only [dot,dotList_view,store,Vector.toList_ofFn,List.map_ofFn,
    Function.comp_apply,List.sum_ofFn]
  exact a.index.symm.sum_comp (fun i => view (f i)*view (g i))

theorem dot_control {I : Type} (a : Layout I) (f g : I → Cell) :
    (dot a f g).control=20*a.size+4 := by simp [dot,dotList_control];omega

theorem dot_bounds {I : Type} (a : Layout I) (f g : I → Cell) (H B W : ℕ)
    (hH : H.size≤W) (hB : B.size≤W) (hp : (a.size*H*B).size≤W)
    (hf : ∀ i,(view (f i)).natAbs≤H) (hg : ∀ i,(view (g i)).natAbs≤B) :
    (view (dot a f g).value).natAbs≤a.size*H*B ∧
    (dot a f g).bitSteps≤2*a.size*BackendScalarBits.backendScalarUnit W := by
  have hh : ∀ p∈(store a (fun i => (f i,g i))).toList,
      (view p.1).natAbs≤H ∧ (view p.2).natAbs≤B := by
    intro p hp
    simp only [store,Vector.toList_ofFn,List.mem_ofFn] at hp
    obtain ⟨i,rfl⟩ := hp
    exact ⟨hf _,hg _⟩
  exact ⟨by simpa only [Vector.length_toList,dot] using dotList_abs _ H B hh,
    by simpa only [Vector.length_toList,dot] using dotList_bits _ H B a.size W (by simp) hH hB hp hh⟩

#print axioms tabulate_read
#print axioms tabulate_bits
#print axioms tabulate_control
#print axioms dotList_view
#print axioms dotList_control
#print axioms dotList_abs
#print axioms dotList_bits
#print axioms dot_view
#print axioms dot_control
#print axioms dot_bounds
end ThinMatrix.BinaryRecursiveDot
