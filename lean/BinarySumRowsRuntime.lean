import BinaryGroupedCompletion

set_option autoImplicit false
set_option maxHeartbeats 1000000
namespace ThinMatrix.BinarySumRowsRuntime
open BinaryCell BinaryGroupedCoordinates BinaryGroupedPreparation
variable {C : ℕ}

def step (row : Bool × Vector Cell C) (rest : Run (Vector Cell C)) : Run (Vector Cell C) :=
  if row.1 then
    let next := BinaryGroupedCompletion.addVectors row.2 rest.value
    ⟨next.value,rest.bitSteps+next.bitSteps,rest.control+next.control+8⟩
  else ⟨rest.value,rest.bitSteps,rest.control+8⟩

def execute (rows : List (Bool × Vector Cell C)) : Run (Vector Cell C) :=
  rows.reverse.foldl (fun rest row => step row rest) ⟨Vector.replicate C zero,0,3*C+2⟩

theorem foldr (rows : List (Bool × Vector Cell C)) :
    rows.foldr step ⟨Vector.replicate C zero,0,3*C+2⟩=BinaryGroupedCompletion.sumRows rows := by
  induction rows with
  | nil => rfl
  | cons row rows ih =>
      rw [List.foldr_cons,ih]
      rcases row with ⟨b,v⟩
      rfl

@[csimp] theorem sumRows_eq_execute : @BinaryGroupedCompletion.sumRows=@execute := by
  funext C rows
  rw [←foldr]
  exact (List.foldr_eq_foldl_reverse ..)

#print axioms foldr
#print axioms sumRows_eq_execute
end ThinMatrix.BinarySumRowsRuntime
