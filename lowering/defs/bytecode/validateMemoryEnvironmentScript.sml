(* External prerequisite check; no logical oracle claims. *)
Theory validateMemoryEnvironment
Ancestors bool

val root = "/home/lukasz/dev/vyper-hol/worktrees/issue-560"
fun run command =
  if OS.Process.isSuccess (OS.Process.system command) then ()
  else raise Fail "Memory validation environment command failed; see memory-environment.log"
val () = run ("python3 -m venv " ^ root ^ "/.venv-memory-validation > " ^ root ^ "/lowering/defs/bytecode/memory-environment.log 2>&1")
val () = run (root ^ "/.venv-memory-validation/bin/python -m pip install py-evm eth_abi eth_utils >> " ^ root ^ "/lowering/defs/bytecode/memory-environment.log 2>&1")
val () = run (root ^ "/.venv-memory-validation/bin/python " ^ root ^ "/lowering/defs/bytecode/validate_memory_environment.py >> " ^ root ^ "/lowering/defs/bytecode/memory-environment.log 2>&1")
