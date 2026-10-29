Theory sourceMeaningCheckedTest
Ancestors
  sourceMeaningCallTest sourceMeaningCallExampleDefs sourceMeaningCompile sourceMeaningDispatch
  sourceMeaningCallDefs sourceModuleCompile sourceModuleElaborate sourceModuleDefs sourceSyntax
  compileVyper vyperInterpreter vyperContext vyperState vyperAST vyperValue
Libs
  sourceModuleFrontendLib wordsLib

(* The public source frontend supplies genuine elaboration/checking equations;
   this is the same original N = 1 + 2, f(x=N): return x+N program whose
   independent call denotation and complete runtime dispatch were proved. *)
val checked = sourceModuleFrontendLib.check_simple
  {fuel=``12:num``, trust=``source_meaning_call_trust``, keys=``[["main"]]``,
   program=``SourceProgram source_meaning_call_syntax []``}
  {layouts=``[(0w:address,([]:storage_layout,[]:storage_layout))]``, address=``0w:address``};
val source_meaning_checked_phase = save_thm ("source_meaning_checked_phase",
  #equation (#elaboration checked));
val source_meaning_checked_frontend = save_thm ("source_meaning_checked_frontend", #composition checked);

Theorem source_meaning_checked_exact:
  source_module_elaborate_simple 12 source_meaning_call_trust [["main"]]
    (SourceProgram source_meaning_call_syntax []) =
    SM_Ok (SourceRetained (SourceProgram source_meaning_call_syntax [])
      [(NONE,source_meaning_call_tops)])
Proof
  CONV_TAC (LAND_CONV (REWR_CONV source_meaning_checked_phase)) >> EVAL_TAC
QED

(* The backend premise is the existing raw compiler equation on the SAME AST;
   neither bytecode simulation nor its remaining supported_program hypotheses
   are asserted away. No code is selected to define the source denotation. *)
Theorem source_meaning_checked_compiler_and_call:
  compile_vyper finalizer policy source_meaning_call_tops = SOME bytes ==>
  (?art. source_module_compile 12 source_meaning_call_trust [["main"]]
    (SourceProgram source_meaning_call_syntax [])
    [(0w:address,([]:storage_layout,[]:storage_layout))] (0w:address) finalizer policy =
      SM_Ok (SourceRetained (SourceProgram source_meaning_call_syntax [])
        [(NONE,source_meaning_call_tops)],art,bytes)) /\
  FST (call_external NONE source_meaning_call_machine
    (empty_call_txn with function_name := "f")) = INL (IntV 6)
Proof
  strip_tac >> simp[source_meaning_call_runtime_return, source_module_compile_def,
    source_meaning_checked_frontend, source_module_bind_def] >>
  fs[retained_executable_def, source_meaning_call_tops_def, source_meaning_call_uint_def,
    source_meaning_call_syntax_def, source_meaning_call_function_def,
    source_meaning_call_annotation_def, source_meaning_call_initializer_def]
QED

val () = List.app (fn (name,th) => let
  val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null (hyp th) andalso null axioms andalso
    List.all (fn tag => tag = "DISK_THM") oracles then ()
    else raise Fail ("source checked kernel audit: " ^ name) end)
  (DB.thms "sourceMeaningCheckedTest");
