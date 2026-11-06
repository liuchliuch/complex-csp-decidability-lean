import Lake.Build.Trace

/-! Read-only source hashing with the pinned toolchain's exact Lake algorithm.
This imports the hashing library; it does not load or execute a Lake workspace. -/

def main : IO Unit := do
  let input ← IO.getStdin
  let output ← IO.getStdout
  repeat
    let line ← input.getLine
    if line.isEmpty then break
    let path := line.trim
    let digest ← Lake.computeTextFileHash path
    output.putStrLn digest.toString
