import CWIndependentCopies

set_option autoImplicit false

namespace ThinMatrix.CWCanonicalType
open scoped BigOperators
open PolynomialDegeneration CWSixBlocks CWBlockWords CWTypeCounts CWIndependentCopies

def ofList : (xs : List Block) → Word xs.length
  | [] => PUnit.unit
  | b::xs => (b,ofList xs)

theorem ofList_count (b : Block) (xs : List Block) : count b xs.length (ofList xs)=xs.count b := by
  induction xs with
  | nil => rfl
  | cons a xs ih =>
      by_cases h : a=b
      · subst a;simp [ofList,count,ih,add_comm]
      · simp [ofList,count,ih,h]

def build (counts : Block → ℕ) : List Block :=
  List.replicate (counts .b011) .b011 ++ List.replicate (counts .b101) .b101 ++
  List.replicate (counts .b110) .b110 ++ List.replicate (counts .b002) .b002 ++
  List.replicate (counts .b020) .b020 ++ List.replicate (counts .b200) .b200

theorem build_count (counts : Block → ℕ) (b : Block) :
    count b (build counts).length (ofList (build counts))=counts b := by
  rw [ofList_count]
  cases b <;> simp [build,List.count_append,List.count_replicate]

theorem build_length (counts : Block → ℕ) : (build counts).length=
    counts .b011+counts .b101+counts .b110+counts .b002+counts .b020+counts .b200 := by
  simp [build,List.length_append,List.length_replicate,add_assoc]

/-- Exact integral period for the six probabilities of local lemma light-cw. -/
def period : ℕ := 75249000000000
def targetCounts : Block → ℕ
  | .b011 => 6888000000000 | .b101 => 4000000000000 | .b110 => 60000000000000
  | .b002 => 131843770853 | .b020 => 4180500000000 | .b200 => 48656229147
def targetProbability : Block → ℚ
  | .b011 => (861/500)*(4000/75249) | .b101 => 4000/75249 | .b110 => 15*(4000/75249)
  | .b002 => 1/18-4000/75249-646603/1000000000
  | .b020 => 1/18 | .b200 => 646603/1000000000

theorem probability_identity (b : Block) : (targetCounts b:ℚ)/period=targetProbability b := by
  cases b <;> norm_num [targetCounts,period,targetProbability]
theorem counts_positive (b : Block) : 0<targetCounts b := by cases b <;> norm_num [targetCounts]
theorem target_length : (build targetCounts).length=period := by rw [build_length];norm_num [targetCounts,period]
theorem aspect : 500*targetCounts .b011=861*targetCounts .b101 ∧
    targetCounts .b110=15*targetCounts .b101 := by norm_num [targetCounts]

/-- Realized type words, rather than an assumed valid type or isolated family.
The huge target period is never evaluated in the bounded runtime fixtures. -/
def reference (scale : ℕ) := ofList (build (fun b => scale*targetCounts b))

theorem reference_counts (scale : ℕ) (b : Block) :
    count b (build (fun b => scale*targetCounts b)).length (reference scale)=scale*targetCounts b :=
  build_count _ b

theorem reference_length (scale : ℕ) : (build (fun b => scale*targetCounts b)).length=scale*period := by
  rw [build_length]
  norm_num [targetCounts,period]
  ring

theorem extracted_dimensions (scale : ℕ)
    (X Y Z : Finset (Colors (build (fun b => scale*targetCounts b)).length))
    (w : Copies _ (reference scale) X Y Z) :
    Fintype.card (Rows 16 _ w.val)=16^(scale*4000000000000) ∧
    Fintype.card (Inners 16 _ w.val)=16^(scale*60000000000000) ∧
    Fintype.card (Cols 16 _ w.val)=16^(scale*6888000000000) := by
  have h := dimensions _ (reference scale) X Y Z w
  rw [reference_counts,reference_counts,reference_counts] at h
  exact h

#print axioms ofList_count
#print axioms build_count
#print axioms build_length
#print axioms probability_identity
#print axioms counts_positive
#print axioms target_length
#print axioms aspect
#print axioms reference_counts
#print axioms reference_length
#print axioms extracted_dimensions
end ThinMatrix.CWCanonicalType
