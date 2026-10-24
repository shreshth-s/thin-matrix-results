import BinaryRecursiveTable

set_option autoImplicit false
set_option maxHeartbeats 1000000

/-! Dot products retain the actual outputs of their binary-addressed reads,
then use those cells in the scalar contraction. Address work is summed once
per operand; no semantic re-read or uncharged equality scan is performed. -/
namespace ThinMatrix.BinaryAddressedDot
open scoped BigOperators
open BinaryCell BinaryGroupedCoordinates
open RecursiveTable (Table Layout prod fin power store)
variable {I : Type} {a b r t : ℕ}

def dot (layout : Layout I) (f g : I → Result Cell) : Run Cell :=
  let inputs := store layout (fun i =>
    let left := f i
    let right := g i
    ((left.value,right.value),left.bitSteps+right.bitSteps))
  let out := BinaryRecursiveDot.dotList (inputs.map Prod.fst).toList
  ⟨out.value,(inputs.toList.map Prod.snd).sum+out.bitSteps,out.control+8*layout.size+2⟩

theorem dot_value (layout : Layout I) (f g : I → Result Cell) :
    (dot layout f g).value=(BinaryRecursiveDot.dot layout (fun i => (f i).value) (fun i => (g i).value)).value := by
  simp only [dot,BinaryRecursiveDot.dot,store,Vector.map_ofFn]
  rfl

theorem dot_bits [Fintype I] (layout : Layout I) (f g : I → Result Cell) :
    (dot layout f g).bitSteps=
      (BinaryRecursiveDot.dot layout (fun i => (f i).value) (fun i => (g i).value)).bitSteps+
      ∑ i,((f i).bitSteps+(g i).bitSteps) := by
  have hinput : (store layout (fun i => (((f i).value,(g i).value),(f i).bitSteps+(g i).bitSteps))).map Prod.fst=
      store layout (fun i => ((f i).value,(g i).value)) := by
    simp only [store,Vector.map_ofFn]
    rfl
  simp only [dot,BinaryRecursiveDot.dot,hinput,Nat.add_comm]
  congr 1
  simp only [store,Vector.toList_ofFn,List.map_ofFn,Function.comp_apply,List.sum_ofFn]
  exact layout.index.symm.sum_comp (fun i => (f i).bitSteps+(g i).bitSteps)

theorem dot_control (layout : Layout I) (f g : I → Result Cell) :
    (dot layout f g).control=20*layout.size+4 := by
  simp only [dot,BinaryRecursiveDot.dotList_control,Vector.length_toList]
  omega

def coefficient (coeff : Table (prod (fin r) (prod (fin t) (prod (fin a) (fin b)))) Cell)
    (s : Fin r) (copy : Fin t) (i : Fin a×Fin b) : Result Cell :=
  let label := BinaryRecursiveAddress.pairRank i
  let column := BinaryMatrixAddress.join (a*b) copy.val label.value.val
  have hc : column.value<t*(a*b) := by
    rw [BinaryMatrixAddress.join_layout (copy,label.value)]
    exact (finProdFinEquiv (copy,label.value)).isLt
  let out := BinaryChunkAddress.matrixRead coeff s ⟨column.value,hc⟩
  ⟨out.value,label.bitSteps+column.bitSteps+out.bitSteps+8⟩

theorem coefficient_value (coeff : Table (prod (fin r) (prod (fin t) (prod (fin a) (fin b)))) Cell)
    (s : Fin r) (copy : Fin t) (i : Fin a×Fin b) :
    (coefficient coeff s copy i).value=RecursiveTable.read coeff (s,(copy,i)) := by
  simp only [coefficient,BinaryChunkAddress.matrixRead_value,RecursiveTable.read]
  apply congrArg coeff.get
  apply Fin.ext
  simp only [BinaryMatrixAddress.join_value,BinaryRecursiveAddress.pairRank_value]
  rfl

theorem coefficient_bits (coeff : Table (prod (fin r) (prod (fin t) (prod (fin a) (fin b)))) Cell)
    (s : Fin r) (copy : Fin t) (i : Fin a×Fin b) (W : ℕ)
    (hA : a.size≤W) (hB : b.size≤W) (hAB : (a*b).size≤W)
    (hT : t.size≤W) (hR : r.size≤W) (hTAb : (t*(a*b)).size≤W) :
    (coefficient coeff s copy i).bitSteps≤12304*(W+1)^2 := by
  have hl := BinaryMatrixAddress.join_bits b i.1.val i.2.val W hB
    ((Nat.size_le_size i.1.isLt.le).trans hA) ((Nat.size_le_size i.2.isLt.le).trans hB)
  have hc := BinaryMatrixAddress.join_bits (a*b) copy.val (BinaryRecursiveAddress.pairRank i).value.val W hAB
    ((Nat.size_le_size copy.isLt.le).trans hT)
    ((Nat.size_le_size (BinaryRecursiveAddress.pairRank i).value.isLt.le).trans hAB)
  have hr := BinaryChunkAddress.matrixRead_bits coeff s
    ⟨(BinaryMatrixAddress.join (a*b) copy.val (BinaryRecursiveAddress.pairRank i).value.val).value,by
      rw [BinaryMatrixAddress.join_layout (copy,(BinaryRecursiveAddress.pairRank i).value)]
      exact (finProdFinEquiv (copy,(BinaryRecursiveAddress.pairRank i).value)).isLt⟩ W hR hTAb
  simp only [coefficient,BinaryRecursiveAddress.pairRank]
  simp only [BinaryRecursiveAddress.pairRank] at hc hr
  nlinarith

#print axioms dot_value
#print axioms dot_bits
#print axioms dot_control
#print axioms coefficient_value
#print axioms coefficient_bits
end ThinMatrix.BinaryAddressedDot
