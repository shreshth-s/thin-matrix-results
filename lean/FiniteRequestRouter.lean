import PrefixBatchSchedule

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! Stable bounded-index request routing. Each occurrence enters one retained
binary trie leaf. Initial storage is linear in the group count; each key read
and write takes a polynomial in its bit length, never a scan over groups. -/
namespace ThinMatrix.FiniteRequestRouter
open scoped BigOperators
open BinaryGroupedCoordinates
variable {G M : ℕ}

def padded (i : Fin G) : Fin (2^G.size) := ⟨i.val,i.isLt.trans (Nat.lt_size_self G)⟩
def code (i : Fin G) : BooleanRequestRouter.Key G.size :=
  Vector.ofFn (fun j => decide ((finFunctionFinEquiv.symm (padded i) j).val=1))

theorem code_injective : Function.Injective (@code G) := by
  intro a b h
  have hh : finFunctionFinEquiv.symm (padded a)=finFunctionFinEquiv.symm (padded b) := by
    funext j
    have hj := congrArg (fun key : BooleanRequestRouter.Key G.size => key.get j) h
    simp only [code,Vector.get_ofFn] at hj
    have hbool : ∀ x y : Fin 2, decide (x.val=1)=decide (y.val=1) → x=y := by
      intro x y; fin_cases x <;> fin_cases y <;> decide
    exact hbool _ _ hj
  have hp := finFunctionFinEquiv.symm.injective hh
  exact Fin.ext (congrArg (fun i : Fin (2^G.size) => i.val) hp)

theorem storage (G : ℕ) : 2^G.size≤2*(G+1) := by
  by_cases h : G=0
  · simp [h]
  · have hs : 0<G.size := Nat.size_pos.mpr (Nat.pos_of_ne_zero h)
    have hn : 2^(G.size-1)≤G := Nat.lt_size.mp (by omega)
    rw [show G.size=(G.size-1)+1 by omega,pow_succ]
    nlinarith

def rows (groups : Vector (Fin G) M) : List (BooleanRequestRouter.Key G.size × Fin M) :=
  List.ofFn (fun i => (code (groups.get i),i))

def run (groups : Vector (Fin G) M) : Run (BooleanRequestRouter.Tree (Fin M) G.size) :=
  let out := BooleanRequestRouter.build (rows groups)
  ⟨out.value,out.bitSteps,out.control+M*(64*(G.size+1)^3+24)+8⟩

def selected (groups : Vector (Fin G) M) (group : Fin G) : List (Fin M) :=
  (List.finRange M).filter (fun i => decide (groups.get i=group))

theorem bucket (groups : Vector (Fin G) M) (group : Fin G) :
    BooleanRequestRouter.bucket (run groups).value (code group)=selected groups group := by
  simp only [run,BooleanRequestRouter.build_bucket,BooleanRequestRouter.selected,rows,selected]
  rw [List.ofFn_eq_map]
  simp only [List.filterMap_map,Function.comp_apply]
  have hh (i : Fin M) : (if code (groups.get i)=code group then some i else none)=
      if decide (groups.get i=group) then some i else none := by
    simp only [code_injective.eq_iff,decide_eq_true_eq]
  simp only [hh]
  exact congrFun List.filterMap_eq_filter (List.finRange M)

theorem mem_bucket (groups : Vector (Fin G) M) (group : Fin G) (i : Fin M) :
    i∈BooleanRequestRouter.bucket (run groups).value (code group) ↔ groups.get i=group := by
  rw [bucket];simp [selected]

theorem total (groups : Vector (Fin G) M) : BooleanRequestRouter.items (run groups).value=M := by
  simp only [run,BooleanRequestRouter.build_items,rows,List.length_ofFn]

theorem group_total (groups : Vector (Fin G) M) : (∑ g : Fin G,(selected groups g).length)=M := by
  have h (g : Fin G) : (selected groups g).length=∑ i : Fin M, if groups.get i=g then 1 else 0 := by
    unfold selected
    rw [PrefixBatchSchedule.filter_length]
    change (List.map _ (List.ofFn (fun i : Fin M => i))).sum=_
    simp only [List.map_ofFn,List.sum_ofFn,decide_eq_true_eq,Function.comp_apply]
  simp only [h]
  rw [Finset.sum_comm]
  simp

theorem cost (groups : Vector (Fin G) M) :
    (run groups).bitSteps=0 ∧ (run groups).control≤
      24*(G+1)+M*(16*(G.size+1)^2+64*(G.size+1)^3+36)+20 := by
  have hh := BooleanRequestRouter.build_cost (rows groups)
  simp only [rows,List.length_ofFn] at hh
  refine ⟨hh.1,?_⟩
  have hs := storage G
  simp only [run,rows]
  nlinarith [hh.2]

def ids (tree : BooleanRequestRouter.Tree (Fin M) G.size) (group : Fin G) : Run (List (Fin M)) :=
  let out := BooleanRequestRouter.read tree (code group)
  ⟨out.value,out.bitSteps,out.control+64*(G.size+1)^3⟩

theorem ids_value (groups : Vector (Fin G) M) (group : Fin G) :
    (ids (run groups).value group).value=selected groups group := by
  simp only [ids,BooleanRequestRouter.read_value,bucket]

theorem ids_cost (tree : BooleanRequestRouter.Tree (Fin M) G.size) (group : Fin G) :
    (ids tree group).bitSteps=0 ∧ (ids tree group).control≤16*(G.size+1)^2+64*(G.size+1)^3 :=
  ⟨BooleanRequestRouter.read_bits _ _,Nat.add_le_add_right (BooleanRequestRouter.read_control _ _) _⟩

def gather {V : Type} (values : Vector V M) (indices : List (Fin M)) : Run (Array V) :=
  ⟨indices.toArray.map (fun i => values.get i),0,32*indices.length+8⟩

@[simp] theorem gather_size {V : Type} (values : Vector V M) (indices : List (Fin M)) :
    (gather values indices).value.size=indices.length := by simp [gather]

theorem gather_get {V : Type} (values : Vector V M) (indices : List (Fin M)) (j : Fin indices.length) :
    (gather values indices).value[j.val]'(by simp)=values.get indices[j.val] := by simp [gather]

#print axioms code_injective
#print axioms storage
#print axioms bucket
#print axioms mem_bucket
#print axioms total
#print axioms group_total
#print axioms cost
#print axioms ids_value
#print axioms ids_cost
#print axioms gather_size
#print axioms gather_get
end ThinMatrix.FiniteRequestRouter
