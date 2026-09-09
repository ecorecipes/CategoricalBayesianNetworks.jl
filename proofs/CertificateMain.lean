import CategoricalBayesianNetworksProofs.CertificateJSON

/-- Validate one versioned JSON certificate; no Julia-runtime correctness is asserted. -/
def main (args : List String) : IO UInt32 := do
  let stderr ← IO.getStderr
  match args with
  | [path] =>
    try
      let text ← IO.FS.readFile path
      match OpenNet.RawCertificate.JSON.read text with
      | .error message =>
        stderr.putStrLn s!"invalid certificate: {message}"
        return (1 : UInt32)
      | .ok N =>
        IO.println s!"valid OpenNet.RawCertificate/v1: {N.variableCount} variables, \
          {N.mechanisms.length} mechanisms, {N.inputs.length} inputs, {N.outputs.length} outputs"
        return (0 : UInt32)
    catch error =>
      stderr.putStrLn s!"cannot read certificate: {error}"
      return (2 : UInt32)
  | _ =>
    stderr.putStrLn "usage: check_certificate PATH"
    return (2 : UInt32)
