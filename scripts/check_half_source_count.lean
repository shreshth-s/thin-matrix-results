import HalfSourceCountExecution
open ThinMatrix

def main : IO Unit := do
  for m in [0,1,2,20,100,1000] do
    let out := HalfSourceCountExecution.execute (ParameterExecution.input m)
    unless out.value=ExactHalfSourcePlan.count m do
      throw (IO.userError "binary translation cardinality differs")
    unless out.bitSteps≤500000*(m.size+1)^2 do
      throw (IO.userError "binary translation cardinality exceeds price")
    unless out.value.size≤3*m.size+8 do
      throw (IO.userError "binary cardinality exceeds width")
  IO.println "PASS 6 binary translation cardinalities, including m=1000; exact result, bit-step price, output width"
