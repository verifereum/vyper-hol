(* Independent pinned Python generation of manifest fixtures, not a proof oracle. *)
Theory prepareMemoryConstruction
Ancestors bool
fun repository_root dir =
  if OS.FileSys.access (OS.Path.concat (dir, "VYPER_PIN"), []) then dir
  else let val parent = OS.Path.getParent dir in
    if parent = dir then raise Fail "cannot locate repository VYPER_PIN"
    else repository_root parent
  end
val root = repository_root (OS.FileSys.getDir ())
val command = "python3 " ^ root ^ "/lowering/defs/bytecode/prepare_memory_construction.py > " ^ root ^ "/lowering/defs/bytecode/memory-prepare.log 2>&1"
val () = if OS.Process.isSuccess (OS.Process.system command) then ()
         else raise Fail "Independent preparation failed: memory-prepare.log"
