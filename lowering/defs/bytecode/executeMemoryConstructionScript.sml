(* EVM differential execution checks; no logical oracle claims.
   Run the location-derived Python driver from a different working directory. *)
Theory executeMemoryConstruction
Ancestors bool
fun repository_root dir =
  if OS.FileSys.access (OS.Path.concat (dir, "VYPER_PIN"), []) then dir
  else let val parent = OS.Path.getParent dir in
    if parent = dir then raise Fail "cannot locate repository VYPER_PIN"
    else repository_root parent
  end
val root = repository_root (OS.FileSys.getDir ())
fun quote s = "'" ^ String.translate (fn #"'" => "'\\''" | c => str c) s ^ "'"
val python = case OS.Process.getEnv "MEMORY_VALIDATION_PYTHON" of
  SOME path => path
| NONE => OS.Path.concat (root, ".venv-memory-validation/bin/python")
val script = OS.Path.concat (root, "lowering/defs/bytecode/execute_memory_construction.py")
val logfile = OS.Path.concat (root, "lowering/defs/bytecode/memory-execute.log")
val original_dir = OS.FileSys.getDir ()
val () = OS.FileSys.chDir (OS.Path.concat (root, "tests"))
val result = OS.Process.system (quote python ^ " " ^ quote script ^
  " > " ^ quote logfile ^ " 2>&1")
val () = OS.FileSys.chDir original_dir
val () = if OS.Process.isSuccess result then ()
         else raise Fail "EVM execution failed: memory-execute.log"
