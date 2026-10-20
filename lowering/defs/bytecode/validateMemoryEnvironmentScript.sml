(* External prerequisite check; no logical oracle claims. *)
Theory validateMemoryEnvironment
Ancestors bool
fun repository_root dir =
  if OS.FileSys.access (OS.Path.concat (dir, "VYPER_PIN"), []) then dir
  else let val parent = OS.Path.getParent dir in
    if parent = dir then raise Fail "cannot locate repository VYPER_PIN"
    else repository_root parent
  end
val root = repository_root (OS.FileSys.getDir ())
fun quote s = "'" ^ String.translate (fn #"'" => "'\\''" | c => str c) s ^ "'"
fun run command =
  if OS.Process.isSuccess (OS.Process.system command) then ()
  else raise Fail "Memory validation environment command failed; see memory-environment.log"
val env = OS.Path.concat (root, ".venv-memory-validation")
val python = quote (OS.Path.concat (env, "bin/python"))
val logfile = quote (OS.Path.concat (root, "lowering/defs/bytecode/memory-environment.log"))
val () = run ("python3 -m venv " ^ quote env ^ " > " ^ logfile ^ " 2>&1")
val () = run (python ^ " -m pip install py-evm eth_abi eth_utils >> " ^ logfile ^ " 2>&1")
val () = run (python ^ " " ^ quote (OS.Path.concat (root,
  "lowering/defs/bytecode/validate_memory_environment.py")) ^ " >> " ^ logfile ^ " 2>&1")
