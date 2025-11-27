open System

def mch2pog (mchPath : FilePath) : IO FilePath := do
  -- NOTE : adapte `dir` à ton installation (ici, chemin Mac CE 24.04.2).
  let dir : FilePath := "/Applications"/"atelierb-free-arm64-24.04.2.app"/"Contents"/"Resources"
  let stdout ← IO.Process.run {
    cmd := (dir/"bin"/"bxml").toString, args := #["-a", mchPath.toString]
  }
  let tmp ← IO.FS.createTempDir
  let bxml := tmp/"tmp.bxml"
  IO.FS.writeFile bxml stdout
  let _ ← IO.Process.run {
    cmd := (dir/"bin"/"pog").toString,
    args := #["-p", (dir/"include"/"pog"/"paramGOPSoftware.xsl").toString, bxml.toString]
  }
  pure <| bxml.withExtension "pog"

-- #eval do
--   let fp ← mch2pog <| "specs" / "Exists.mch"
--   dbg_trace fp
