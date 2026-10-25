(* Byte-for-byte import of independently generated G0006 inputs, not HOL outputs.
   Retained as the reproducible import utility; normal tests only read fixtures. *)
structure importMembershipFixturesLib = struct
fun copy_file source target = let
  val i = TextIO.openIn source
  val text = TextIO.inputAll i before TextIO.closeIn i
  val o' = TextIO.openOut target
in TextIO.output(o',text) before TextIO.closeOut o' end
fun copy_tree source target = let
  val () = if OS.FileSys.isDir target handle OS.SysErr _ => false
           then () else OS.FileSys.mkDir target
  val d = OS.FileSys.openDir source
  fun loop () = case OS.FileSys.readDir d of NONE => () | SOME name => let
    val s = OS.Path.concat(source,name)
    val t = OS.Path.concat(target,name)
    val () = if OS.FileSys.isDir s then copy_tree s t else copy_file s t
  in loop() end
in loop() before OS.FileSys.closeDir d end
fun import root = let
  val source = OS.Path.concat(root,".agent-files/c6-validation")
  val target = OS.Path.concat(root,"tests/fixtures/membership")
  val () = if OS.FileSys.isDir target handle OS.SysErr _ => false
           then () else OS.FileSys.mkDir target
  val () = List.app (fn dir => copy_tree (OS.Path.concat(source,dir))
    (OS.Path.concat(target,dir))) ["inputs","compiler","sources"]
  val () = List.app (fn name => copy_file (OS.Path.concat(source,name))
    (OS.Path.concat(target,name)))
    ["report.json","compiler-provenance.json","compiler-source-audit.json",
     "artifact-sha256.json","generate.py"]
in () end
end
