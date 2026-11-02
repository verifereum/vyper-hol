Theory evalCompilerBytecodeLibTest
Ancestors words
Libs evalCompilerBytecodeLib

(* Model a clean staged build without an unrelated python-o1-no-asm-opt
   directory. Check each supported working directory independently. *)
val fixture_test_root = OS.FileSys.tmpName ();
val () = OS.FileSys.remove fixture_test_root;
val () = OS.FileSys.mkDir fixture_test_root;
val fixture_test_dirs =
  ["tests", "lowering", "lowering/defs", "lowering/defs/bytecode",
   "lowering/defs/bytecode/eval",
   "lowering/defs/bytecode/external-entries",
   "lowering/defs/bytecode/external-entries/oracle"];
val () = List.app
  (fn dir => OS.FileSys.mkDir (OS.Path.concat (fixture_test_root, dir)))
  fixture_test_dirs;
val fixture_test_file = OS.Path.concat
  (fixture_test_root,
   "lowering/defs/bytecode/external-entries/oracle/nr_ext_nonpayable.hex");
val () = let val output = TextIO.openOut fixture_test_file in
  TextIO.output (output, "deploy=0x0102\nruntime=0xff\n")
    before TextIO.closeOut output
end;

fun check_fixture_from dir filename = let
  val previous = OS.FileSys.getDir ()
  fun check () = let
    val () = OS.FileSys.chDir (OS.Path.concat (fixture_test_root, dir))
    val actual = evalCompilerBytecodeLib.read_hex_bytes filename
  in
    if aconv actual ``([1w; 2w] : word8 list, [255w] : word8 list)`` then ()
    else raise Fail ("incorrect bytecode fixture from " ^ dir)
  end
in
  (check () before OS.FileSys.chDir previous)
    handle exn => (OS.FileSys.chDir previous; raise exn)
end;

val fixture_test_contexts =
  ["lowering/defs/bytecode/eval", "lowering/defs", ".", "tests"];
fun cleanup_fixture_test () = (
  OS.FileSys.remove fixture_test_file;
  List.app
    (fn dir => OS.FileSys.rmDir (OS.Path.concat (fixture_test_root, dir)))
    (List.rev fixture_test_dirs);
  OS.FileSys.rmDir fixture_test_root);

val () = (
  List.app
    (fn dir => check_fixture_from dir
      "../external-entries/oracle/nr_ext_nonpayable.hex")
    fixture_test_contexts;
  (* The ordinary fixture directory still resolves in every context. *)
  OS.FileSys.rename
    {old = OS.Path.concat (fixture_test_root,
             "lowering/defs/bytecode/external-entries"),
     new = OS.Path.concat (fixture_test_root,
             "lowering/defs/bytecode/python-o1-no-asm-opt")};
  (List.app (fn dir => check_fixture_from dir "oracle/nr_ext_nonpayable.hex")
     fixture_test_contexts
   before OS.FileSys.rename
     {old = OS.Path.concat (fixture_test_root,
              "lowering/defs/bytecode/python-o1-no-asm-opt"),
      new = OS.Path.concat (fixture_test_root,
              "lowering/defs/bytecode/external-entries")})
  ) before cleanup_fixture_test ();
