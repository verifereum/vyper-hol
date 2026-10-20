(* Independent Python phase of the remaining witness matrix. *)
Theory prepareMemoryConstructionMatrix
Ancestors bool
fun repository_root dir =
  if OS.FileSys.access (OS.Path.concat (dir, "VYPER_PIN"), []) then dir
  else let val parent = OS.Path.getParent dir in
    if parent = dir then raise Fail "cannot locate repository VYPER_PIN"
    else repository_root parent
  end
val root = repository_root (OS.FileSys.getDir ())
fun quote s = "'" ^ String.translate (fn #"'" => "'\\''" | c => str c) s ^ "'"
(* Source import is explicit and optional; normal reproduction uses retained sources. *)
val import_task = case OS.Process.getEnv "MEMORY_CONSTRUCTION_TASK" of
  SOME task => " --task " ^ quote task
| NONE => ""
val script = OS.Path.concat (root, "lowering/defs/bytecode/prepare_memory_construction_matrix.py")
val logfile = OS.Path.concat (root, "lowering/defs/bytecode/memory-matrix-prepare.log")
val () = if OS.Process.isSuccess (OS.Process.system
  ("python3 " ^ quote script ^ import_task ^ " > " ^ quote logfile ^ " 2>&1"))
  then () else raise Fail "matrix preparation failed: memory-matrix-prepare.log"
