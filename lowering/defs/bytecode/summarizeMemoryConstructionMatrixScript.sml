(* Summarize observed results only; this theory makes no parity assertion. *)
Theory summarizeMemoryConstructionMatrix
Ancestors bool
fun repository_root dir =
  if OS.FileSys.access (OS.Path.concat (dir, "VYPER_PIN"), []) then dir
  else let val parent = OS.Path.getParent dir in
    if parent = dir then raise Fail "cannot locate repository VYPER_PIN"
    else repository_root parent
  end
val root = repository_root (OS.FileSys.getDir ())
fun quote s = "'" ^ String.translate (fn #"'" => "'\\''" | c => str c) s ^ "'"
val script = OS.Path.concat (root, "lowering/defs/bytecode/summarize_memory_construction_matrix.py")
val logfile = OS.Path.concat (root, "lowering/defs/bytecode/memory-matrix-summary.log")
val () = if OS.Process.isSuccess (OS.Process.system
  ("python3 " ^ quote script ^ " > " ^ quote logfile ^ " 2>&1"))
  then () else raise Fail "matrix summary failed: memory-matrix-summary.log"
