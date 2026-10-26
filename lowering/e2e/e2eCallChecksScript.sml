(* TASK056 public schema and saved-kernel/classification gate.
 * Raw O1 call correctness is restricted to immutable-free programs because
 * its source-shape invariant excludes DLOAD; immutable compilation is unchanged.
 * Not a stage producer, definitionless rollup, or full-project audit.
 * Substantive grouped boundary consumer below needs no stage admission.
 *)
Theory e2eCallChecks
Ancestors
  e2eCorrectness configuredE2ECorrectness e2eProducers e2eEntry
  e2eDefs codegenCorrectness vyperLoweringCorrect loweringShapeProps unitTransformDefs
  contextPlanLayoutProps unitShapeDefs frameOutcome emitHelperProps
  compilePhasesProps venomExecSemantics venomState
  e2eBoundaryTest e2eSourceBoundaryCVTest vyperOracleEntryTest

(* Consume the existing entry helper GROUPS, not a strengthened top premise.
 * Exact FMP/calldata are initialized here; labels and outcomes are concrete.
 * No memory invariant is claimed: its witness is supplied later by S5.
 *)
Theorem call_entry_compiler_fields:
  !prog cp es.
  (entry_venom_state prog cp es).vs_outcomes = MAP SND (call_trace es) /\
  (entry_venom_state prog cp es).vs_requests = [] /\
  (entry_venom_state prog cp es).vs_call_ctx.cc_calldata =
    (FST (HD es.contexts)).msgParams.data /\
  (entry_venom_state prog cp es).vs_initial_fmp = n2w cp.cp_initial_fmp /\
  initial_codegen_state_rel cp (entry_venom_state prog cp es) /\
  (!l. FLOOKUP (entry_venom_state prog cp es).vs_labels l =
       OPTION_MAP n2w (FLOOKUP (SND (compute_label_offsets prog)) l))
Proof
  simp[entry_venom_state_frame_fields, entry_venom_state_fresh,
       entry_venom_state_def]
QED

val expected_top = ``
  !policy tops deploy_bc runtime_bc am tx ret es.
    compile_vyper (K SOME) policy tops = SOME (deploy_bc, runtime_bc) /\
    supported_program tops /\ immutable_free_program tops /\
    source_typing_ok tops am tx /\
    source_storage_ok tops am tx /\
    call_state_rel tops runtime_bc am tx es /\
    valid_vyper_call tops tx (FST (HD es.contexts)).msgParams.data ret /\
    call_outcomes_ok tops am tx (MAP SND (call_trace es))
    ==>
    ?r es'.
      run_call es = SOME (r, es') /\
      (frame_resource_starved es r es' \/
       precompile_call_starved es \/
       call_result_rel tops ret am tx es r es')``;
val saved_top = DB.fetch "e2eCorrectness" "vyper_call_correct";
val () = if aconv expected_top (Thm.concl saved_top) then
  print "TASK056 RAW O1 CALL SCHEMA: PASS; immutable-free source domain, no extra gas/state/memory/shape/ctx premise\n"
  else raise Fail "TASK056 public call schema changed";

fun check_object admitted (thy,name) = let
  val th = DB.fetch thy name
  val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  val actual = List.filter (fn s => s <> "DISK_THM") oracles
  val expected = if admitted then ["ch" ^ "eat"] else []
  val _ = if null (Thm.hyp th) andalso null axioms andalso actual = expected
    then () else raise Fail ("TASK056 kernel/classification mismatch " ^ thy ^ "." ^ name)
  in print ("TASK056 OBJECT " ^ thy ^ "." ^ name ^
    " Hyp=0 axioms=[] admission-tags=[" ^ String.concatWith "," actual ^ "]\n") end;

val producers =
  [("e2eProducers","compile_vyper_runtime_phases"),
   ("contextPlanLayoutProps","generate_context_plan_layout_wf"),
   ("contextPlanLayoutProps","asm_pc_to_offset_zero"),
   ("unitShapeDefs","entry_fn_first_lookup"),
   ("e2eProducers","o1_pipeline_codegen_obligations"),
   ("e2eProducers","entry_venom_state_initial_venom_state_rel"),
   ("e2eProducers","entry_venom_state_o1_initial_state_ok"),
   ("e2eProducers","entry_venom_state_initial_ctx_rel"),
   ("frameOutcome","frame_outcome_single_frame_run"),
   ("emitHelperProps","fresh_label_output_inj"),
   ("emitHelperProps","fresh_label_produces_external"),
   ("e2eProducers","type_env_all_modules_single"),
   ("contextPlanLayoutProps","ordered_spill_regions_SNOC")];
val () = List.app (check_object false) producers;
val () = List.app (check_object false)
  [("e2eCorrectness","e2e_vyper_to_evm"),
   ("e2eCorrectness","e2e_venom_pipeline"),
   ("e2eCorrectness","compile_vyper_runtime_bytecode"),
   ("configuredE2ECorrectness","compile_vyper_with_success_phases"),
   ("configuredE2ECorrectness","compile_vyper_with_deploy_runtime_compose"),
   ("e2eCallChecks","call_entry_compiler_fields")];
val () = List.app (fn thy => List.app
  (fn (name,_) => check_object false (thy,name)) (DB.thms thy))
  ["e2eBoundaryTest", "e2eSourceBoundaryCVTest", "vyperOracleEntryTest"];
val () = check_object true ("e2eCorrectness","vyper_call_correct");
val () = check_object true ("e2eCorrectness","e2e_deploy_correctness");

(* Phase re-exports retain exact original public schemas, not just names. *)
val () = List.app (fn name =>
  if aconv (concl (DB.fetch "configuredE2ECorrectness" name))
           (concl (DB.fetch "compilePhasesProps" name)) then ()
  else raise Fail ("TASK056 phase re-export drift " ^ name))
  ["compile_vyper_with_success_phases", "compile_vyper_with_deploy_runtime_compose"];

(* None of these compatibility names is saved in the rebuilt owners. *)
val retired =
  [("e2eCorrectness","e2e_vyper_to_evm_legacy"),
   ("e2eCorrectness","source_unit_execution_correct_legacy"),
   ("e2eCorrectness","source_unit_execution_correct_legacy_def"),
   ("codegenCorrectness","codegen_correct_legacy"),
   ("codegenCorrectness","initial_ctx_rel_legacy_def"),
   ("vyperLoweringCorrect","external_call_result_rel_legacy_def"),
   ("vyperLoweringCorrect","external_call_state_rel_def"),
   ("vyperLoweringCorrect","external_logs_rel_def"),
   ("configuredE2ECorrectness","e2e_vyper_to_evm_O1")];
val () = List.app (fn (thy,name) =>
  if List.exists (fn (n,_) => n = name) (DB.thms thy)
  then raise Fail ("TASK056 retained obsolete export " ^ thy ^ "." ^ name)
  else print ("TASK056 RETIRED " ^ thy ^ "." ^ name ^ " absent\n")) retired;
