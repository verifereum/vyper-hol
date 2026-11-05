(* Import-boundary probe only: not a copy-correctness result. *)
Theory externalReturnCopyImportProbe
Ancestors
  externalFrameRetOk valueCopy fragExec immutableMemoryFrame

Theorem copy_import_probe:
  !n:num. n = n
Proof
  simp[]
QED
