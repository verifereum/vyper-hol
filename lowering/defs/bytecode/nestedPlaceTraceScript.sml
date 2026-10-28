(* Bounded stage observations for the retained s20 parity difference.
   All checked evaluation occurs inside instrumented Proof tactics. *)
Theory nestedPlaceTrace
Ancestors
  compileVyper supportedProgram concretizeMemLocDefs codegenReadyCompute
  byte option alist integer_word
  venomPipelineRunner venomFnScheduleRunner venomPassSchedule fcgDefs
Libs
  vyperCheckContractFrontendLib jsonASTLib finite_mapLib wordsLib
  evalCompilerBytecodeLib memoryStoreWitnessLib
  supportedEvalLib

fun holbuild_extra_deps (_ : string list) = ();
fun holbuild_extra_outputs (_ : string list) = ();
val () = holbuild_extra_deps
  ["nested_place_driver.py", "nested-places/diagnostic.tar.gz"];
val () = holbuild_extra_outputs
  ["nested-places/s20-policy.term", "nested-places/s20-lowered.term"];
val python = case OS.Process.getEnv "NESTED_PLACE_PYTHON" of
  SOME path => path | NONE => "/home/lukasz/.local/share/uv/tools/vyper/bin/python3";
val () = if OS.Process.isSuccess (OS.Process.system
  ("'" ^ python ^ "' nested_place_driver.py trace-prepare")) then ()
  else raise Fail "cannot unpack diagnostic inputs";
val () = computeLib.upd_compset finite_mapLib.add_finite_map_compset;
val () = supportedEvalLib.configure ();
val () = computeLib.upd_compset (computeLib.add_thms
  [alistTheory.fmap_to_alist_FEMPTY, integer_wordTheory.i2w_pos]);
val tops = memoryStoreWitnessLib.program "nested-places/oracle"
  "s20_nested_map_read_key_order";
val policy = ref (NONE : thm option);
val lowered = ref (NONE : thm option);
fun observed cell = rhs (concl (valOf (!cell)));
fun capture name cell tm g = let
  val th = EVAL tm
  val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  val () = if null (hyp th) andalso null axioms andalso
    List.all (fn s => s = "DISK_THM") oracles andalso
    aconv (lhs (concl th)) tm then () else raise Fail "untrusted stage trace"
  val () = cell := SOME th
  val () = memoryStoreWitnessLib.write ("nested-places/s20-" ^ name ^ ".term")
    (term_to_string (rhs (concl th)))
in ALL_TAC g end;

Theorem s20_policy_trace:
  T
Proof
  capture "policy" policy
    ``THE (resolve_o1_policy (o1_policy all_capabilities))`` >> simp[]
QED

Theorem s20_lowering_trace:
  T
Proof
  capture "lowered" lowered
    ``lower_vyper_runtime_unit ^tops ^(observed policy)`` >> simp[]
QED
