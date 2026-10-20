(* Regenerate pinned Python artifacts independently, compare all retained bytes,
   and retain canonical manifest-scoped provenance. No HOL compiler is invoked. *)
Theory verifyMemoryConstructionFixtures
Ancestors bool
fun repository_root dir =
  if OS.FileSys.access (OS.Path.concat (dir, "VYPER_PIN"), []) then dir
  else let val parent = OS.Path.getParent dir in
    if parent = dir then raise Fail "cannot locate repository VYPER_PIN"
    else repository_root parent
  end
val root = repository_root (OS.FileSys.getDir ())
fun quote s = "'" ^ String.translate (fn #"'" => "'\\''" | c => str c) s ^ "'"
val bin = OS.Path.concat (root, ".venv-memory-validation/bin")
val driver = OS.Path.concat (root, "lowering/defs/bytecode/prepare_memory_construction.py")
val scratch = OS.Path.concat (root, "lowering/defs/bytecode/memory-construction-regenerated")
val logfile = OS.Path.concat (root, "lowering/defs/bytecode/memory-verify.log")
val olddir = OS.FileSys.getDir ()
val () = OS.FileSys.chDir (OS.Path.concat (root, "tests"))
val result = OS.Process.system ("PATH=" ^ quote bin ^ ":\"$PATH\" " ^
  quote (OS.Path.concat (bin, "python")) ^ " " ^ quote driver ^
  " --fixtures " ^ quote scratch ^
  " --check > " ^ quote logfile ^ " 2>&1")
val () = OS.FileSys.chDir olddir
val () = if OS.Process.isSuccess result then ()
         else raise Fail "independent fixture verification failed: memory-verify.log"
val input = TextIO.openIn (OS.Path.concat (scratch, "provenance.json"))
val provenance = TextIO.inputAll input before TextIO.closeIn input
val output = TextIO.openOut (OS.Path.concat (root,
  "lowering/defs/bytecode/memory-stores/oracle/provenance.json"))
val () = TextIO.output (output, provenance) before TextIO.closeOut output
