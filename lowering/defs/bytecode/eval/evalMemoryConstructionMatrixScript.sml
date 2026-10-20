(* Diagnostic matrix: exact bytes are compared, never assumed as evaluation rules.
   A successful driver build is NOT a claim that every recorded row MATCHes. *)
Theory evalMemoryConstructionMatrix
Ancestors compileVyper supportedProgram concretizeMemLocDefs codegenReadyCompute alist byte integer_word option
Libs memoryStoreWitnessLib vyperCheckContractFrontendLib jsonASTLib evalCompilerBytecodeLib finite_mapLib computeLib wordsLib intReduce
val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset intReduce.add_int_compset
val () = computeLib.upd_compset (computeLib.add_thms
  [fmap_to_alist_FEMPTY, i2w_pos, byteTheory.set_byte_bit_field_insert])
fun repository_root dir =
  if OS.FileSys.access (OS.Path.concat (dir, "VYPER_PIN"), []) then dir
  else let val parent = OS.Path.getParent dir in
    if parent = dir then raise Fail "cannot locate repository VYPER_PIN"
    else repository_root parent
  end
val root = OS.Path.concat (repository_root (OS.FileSys.getDir ()),
  "lowering/defs/bytecode/memory-construction-matrix")
val oracle = OS.Path.concat (root, "oracle")
val output = OS.Path.concat (root, "hol")
val () = (OS.FileSys.mkDir output handle OS.SysErr _ => ())
val names = String.tokens Char.isSpace (memoryStoreWitnessLib.read
  (OS.Path.concat (root, "accepted.txt")))
val summary = TextIO.openOut (OS.Path.concat (root, "results.tsv"))
fun record name verdict =
  (TextIO.output (summary, name ^ "\t" ^ verdict ^ "\n"); TextIO.flushOut summary)
fun probe name = let
  val _ = memoryStoreWitnessLib.probe oracle output name
  val actual = OS.Path.concat (output, name ^ ".hex")
  val verdict = if OS.FileSys.access (actual, []) then
    if memoryStoreWitnessLib.read actual = memoryStoreWitnessLib.read
      (OS.Path.concat (oracle, name ^ ".hex")) then "MATCH" else "PARITY_DEFECT"
    else if OS.FileSys.access (OS.Path.concat (output, name ^ ".residual"), [])
      then "RESIDUAL" else "NONE"
  in record name verdict end
  handle exn => record name ("ERROR " ^ General.exnMessage exn)
val () = List.app probe names
val () = TextIO.closeOut summary
