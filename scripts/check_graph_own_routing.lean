import GraphOwnResiduals
set_option maxHeartbeats 4000000
set_option maxRecDepth 8000
open ThinMatrix

private def checkFinite (G M : Nat) (hG : 0<G) : IO Nat := do
  let groups : Vector (Fin G) M := Vector.ofFn (fun i => ⟨(i.val*7+i.val/3)%G,Nat.mod_lt _ hG⟩)
  let out := FiniteRequestRouter.run groups
  let budget := 24*(G+1)+M*(16*(G.size+1)^2+64*(G.size+1)^3+36)+20
  unless out.bitSteps=0 && out.control≤budget do throw (IO.userError "Finite routing cost exceeds bound")
  unless BooleanRequestRouter.items out.value=M do throw (IO.userError "Finite routing lost occurrences")
  let mut seen := Array.replicate M 0
  for group in List.finRange G do
    let ids := FiniteRequestRouter.ids out.value group
    let expected := (List.finRange M).filter (fun i => groups.get i=group)
    unless ids.value=expected do throw (IO.userError "Finite routing group mismatch")
    for j in ids.value do seen := seen.modify j.val (·+1)
  unless seen.all (·=1) do throw (IO.userError "Finite routing duplicated an occurrence")
  return M

private def checkGraph (S L m M : Nat) (hS : 0<S) (hm : m≤L) (right : Bool) : IO Nat := do
  let width := ThinMatrixBackend.tileWidth L m
  have hw : 0<width := ThinMatrixBackend.tileWidth_pos L m hm
  let requests : Vector (GraphCompletionRequests.Physical L m 2) M := Vector.ofFn (fun i =>
    ⟨i.val%S,(i.val/3)%S,⟨(i.val*5+1)%width,Nat.mod_lt _ hw⟩,
      ⟨(i.val*7+3)%width,Nat.mod_lt _ hw⟩,⟨i.val%2,Nat.mod_lt _ (by decide)⟩,
      Vector.ofFn (fun j => ⟨(i.val/4^j.val)%4,Nat.mod_lt _ (by decide)⟩)⟩)
  have hb (i : Fin M) : (requests.get i).bandL<S ∧ (requests.get i).bandR<S := by
    simp only [requests,Vector.get_ofFn]
    exact ⟨Nat.mod_lt _ hS,Nat.mod_lt _ hS⟩
  let out := GraphOwnRequestRouter.run right requests hb
  let shape := BinaryBackendExecution.prepareShapeRuntime L m
  let masks := ResidualFamilyKeys.prepare shape.layout 1
  let mut seen := Array.replicate M 0
  let mut checked := 0
  for a in List.finRange S do
    for b in List.finRange S do
      for normal in List.finRange (GoodMapEmbedding.goodSlots L m).card do
        for opposite in List.finRange (GoodMapEmbedding.goodSlots L m).card do
          let ids := GraphOwnRequestRouter.ids out.value a b normal opposite
          let expected := (List.finRange M).filter (fun i =>
            RootRequestSelection.accepts a.val b.val right normal opposite (requests.get i))
          unless ids.value=expected do throw (IO.userError "Graph own-mask routing differs")
          let projected := GraphOwnResiduals.project right requests out.value a b normal opposite
            (masks.value.masks.get normal) (masks.value.masks.get opposite)
          let allProjected := GraphCompletionRequests.project right (masks.value.masks.get normal)
            (masks.value.masks.get opposite) requests
          unless projected.bitSteps=0 do throw (IO.userError "Projection has unaccounted scalar operations")
          unless projected.value.residuals.labels.size=ids.value.length do throw (IO.userError "Projected request count differs")
          for j in List.finRange ids.value.length do
            let original := ids.value[j.val]
            seen := seen.modify original.val (·+1)
            unless projected.value.residuals.labels[j.val]?=allProjected.value.labels[original.val]? do
              throw (IO.userError "Selected projection changed original labels")
            checked := checked+1
  unless seen.all (·=1) do throw (IO.userError "Graph query not assigned exactly one own-mask group")
  IO.println s!"PASS: graph own-root routing right={right}; {checked} original occurrences projected once."
  return checked

def main : IO Unit := do
  let mut total := 0
  for G in [1,2,3,4,7,8,9,16,17] do
    if hG : 0<G then
      for M in [0,1,2,17,53] do total := total+(←checkFinite G M hG)
  total := total+(←checkGraph 3 2 1 37 (by decide) (by decide) false)
  total := total+(←checkGraph 3 2 1 37 (by decide) (by decide) true)
  IO.println s!"PASS: {total} routed occurrences; stable indices, duplicates, empty lists, both orientations, original projected labels, and finite routing budgets."
  IO.println "SCOPE: routing and projection before completion; production graph scheduler and compact source-cost closure remain."
