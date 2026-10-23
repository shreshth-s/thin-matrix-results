import GraphRootWindows

set_option autoImplicit false

/-! Binary address construction for retained ternary rows. Coefficients are
not re-encoded; address arithmetic and decoding are charged separately from
indexed vector construction and traversal. -/
namespace ThinMatrix.TernaryWindowAddress
open BinaryGroupedCoordinates BinaryGroupedPreparation CroppedGroupedSuffix
open scoped BigOperators

def pair {n : ℕ} (word : Vector (Fin 3) n) : Vector Bool n := word.map (fun a => decide (a=1))
def rare {n : ℕ} (word : Vector (Fin 3) n) : Vector Bool n := word.map (fun a => decide (a=2))

theorem recovered {n : ℕ} (v : Vector (Fin 3) n) :
    CroppedGroupedSuffix.word (pair v).get (CappedBitPreparation.support (rare v))=v.get := by
  funext i
  have hi := (v.get i).isLt
  have h : v.get i=0 ∨ v.get i=1 ∨ v.get i=2 := by omega
  rcases h with h | h | h <;> simp [pair,rare,CroppedGroupedSuffix.word,CappedBitPreparation.support,
    CroppedGroupedSuffix.pairLetter,h]

def encode {n : ℕ} (word : Vector (Fin 3) n) : Run (Fin (3^n)) :=
  let out := locate (pair word) (rare word)
  ⟨⟨out.value.index,locate_lt _ _⟩,out.bitSteps,out.control+12*word.toArray.size+8⟩

theorem encode_value {n : ℕ} (v : Vector (Fin 3) n) :
    (encode v).value=StoredGroupedCompletion.rawIndex n v.get := by
  apply Fin.ext
  simp only [encode,locate_index,GroupedCoordinates.coordinates_index,recovered]

theorem encode_bits {n : ℕ} (v : Vector (Fin 3) n) : (encode v).bitSteps≤addressBudget n := locate_bits _ _

theorem encode_control {n : ℕ} (v : Vector (Fin 3) n) : (encode v).control=40*n+18 := by
  simp only [encode,locate_control,Vector.size_toArray]
  omega

def replace {n : ℕ} (v : Vector (Fin 3) n) (axis : Fin n) (a : Fin 3) : Vector (Fin 3) n :=
  GroupedPreparation.ofStoredFn v (fun j => if j=axis then a else v.get j)

theorem replace_get {n : ℕ} (v : Vector (Fin 3) n) (axis : Fin n) (a : Fin 3) :
    (replace v axis a).get=Function.update v.get axis a := by
  funext j
  simp only [replace,GroupedPreparation.ofStoredFn_eq,Vector.get_ofFn,Function.update_apply]

def locateReplacement {n : ℕ} (v : Vector (Fin 3) n) (axis : Fin n) (a : Fin 3) : Run (Fin (3^n)) :=
  let out := encode (replace v axis a)
  ⟨out.value,out.bitSteps,out.control+8*v.toArray.size+8⟩

theorem locateReplacement_value {n : ℕ} (v : Vector (Fin 3) n) (axis : Fin n) (a : Fin 3) :
    (locateReplacement v axis a).value=StoredGroupedCompletion.rawIndex n (Function.update v.get axis a) := by
  simp only [locateReplacement,encode_value,replace_get]

theorem locateReplacement_bits {n : ℕ} (v : Vector (Fin 3) n) (axis : Fin n) (a : Fin 3) :
    (locateReplacement v axis a).bitSteps≤addressBudget n := encode_bits _

theorem locateReplacement_control {n : ℕ} (v : Vector (Fin 3) n) (axis : Fin n) (a : Fin 3) :
    (locateReplacement v axis a).control=48*n+26 := by
  simp only [locateReplacement,encode_control,Vector.size_toArray]
  omega

#print axioms recovered
#print axioms encode_value
#print axioms encode_bits
#print axioms encode_control
#print axioms replace_get
#print axioms locateReplacement_value
#print axioms locateReplacement_bits
#print axioms locateReplacement_control
end ThinMatrix.TernaryWindowAddress
