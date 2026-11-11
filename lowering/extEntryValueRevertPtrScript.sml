(*
 * The pointer twin of S1's external_entry_value_revert: a call that sends
 * value to a nonpayable entry runs pointer-safely into the dispatcher's
 * callvalue check.
 *
 * TOP-LEVEL:
 *   external_entry_value_revert_ptr
 *)
Theory extEntryValueRevertPtr
Ancestors
  vyperCompiler selectorDispatch moduleLoweringProps stmtLoweringProps
  exprLoweringProps vyperInterpreter vyperContext venomExecSemantics
  venomState compileEnv e2eDefs supportedProgram compileVyper fragExec
  venomInst contextCodegenRel ptrDiscipline ptrSafeRun vyperLoweringCorrect
  bodyPtrDefs stmtSimDefs stmtSimProps loweringPosts bodySim moduleLowering
  stmtLowering vyperTypeSystem vyperState emitHelper vyperTypeSelectedEntrySoundness
  stmtLoweringMono venomWf memSafeRun allocaFrontierBound unitTransformDefs
  unitShapeDefs o1PassContract entryValueRevertPtr sourceEntrySelection
  sourceEntryCode entryDispatchPtr entryDispatchProps loweringShapeProps
  loweringShapeSource supportedNames o1PipelineCorrect

val _ = Parse.hide "body";

(* Value rejection follows the installed dispatcher into the nonpayable check. *)
Theorem external_entry_value_revert_ptr:
  !tops rpolicy unit am tx ret vs mut args fbody env e st efn elbl.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    source_storage_ok tops am tx /\
    source_deployment_rel tops am tx /\
    valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
    initial_venom_state_rel tops am tx vs /\
    call_outcomes_ok am tx vs.vs_outcomes /\
    ~source_exempt tops (call_external (SOME vs.vs_outcomes) [] am tx) /\
    lookup_function NONE tx.function_name External tops =
      SOME (mut, F, args, [], ret, fbody) /\
    bind_arguments (type_env tops) args tx.args = SOME env /\
    send_call_value mut
      (initial_evaluation_context am.sources am.layouts tx NONE)
      (initial_state am [env] with
         <| outcomes := SOME vs.vs_outcomes; requests := [] |>) =
      (INR e, st) /\
    lookup_function "__entry" unit.cu_context.ctx_functions = SOME efn /\
    fn_entry_label efn = SOME elbl ==>
    !fuel. ptr_safe_blocks
             (external_call_dead tx
                (call_external (SOME vs.vs_outcomes) [] am tx))
             0 fuel unit.cu_context efn [] FEMPTY entry_taint
             (vs with <| vs_prev_bb := NONE; vs_current_bb := elbl;
                         vs_inst_idx := 0 |>)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `source_storage_ok _ _ _` kall_tac >>
  qpat_x_assum `source_deployment_rel _ _ _` kall_tac >>
  qpat_x_assum `call_outcomes_ok _ _ _` kall_tac >>
  qpat_x_assum `~source_exempt _ _` kall_tac >>
  `tx.function_name <> "__default__"` by fs[valid_vyper_call_def] >>
  `~ctx_has_dalloca unit.cu_context` by
    (irule o1_source_unit_ok_no_dalloca >>
     irule loweringShapePropsTheory.lower_vyper_runtime_unit_source_unit_ok_shape >>
     goal_assum (drule_at Any) >> conj_tac
     >- (irule supported_names_internal_names_distinct >>
         fs[supported_program_def, supported_declaration_names_def]) >>
     metis_tac[supported_program_runtime_bodies_shape_ok]) >>
  drule_all initial_entry_rejected_value >> strip_tac >>
  drule_all source_valid_linear_dispatch_target >> strip_tac >>
  drule_all source_selected_entry_check_code >> strip_tac >>
  drule_all initial_entry_dispatch_scalars >>
  disch_then (qspecl_then [`0`, `elbl`, `ds`] strip_assume_tac) >>
  qmatch_goalsub_abbrev_tac `ptr_safe_blocks D 0 _ _ _ _ _ _ ss` >>
  `!G tn fuel. ptr_safe_run D 0 fuel unit.cu_context efn [] G tn ss` by
    (irule dispatch_nonpayable_check_ptr_safe >>
     simp[Abbr `ss`] >>
     qexistsl_tac [`checked`, `fb`, `min_cds`, `opened`,
       `MAP (\(sel,lbl,z). (sel,lbl))
          (build_selectors (type_env tops) (FST (classify_functions tops)))`,
       `ds`, `de`] >>
     gvs[] >>
     qspecl_then [`type_env tops`, `FST (classify_functions tops)`]
       mp_tac linear_selectors_lt >> simp[]) >>
  drule_all compile_selector_dispatch_linear_layout >> strip_tac >>
  irule ptr_safe_blocks_nonphi_run >>
  simp[Abbr `ss`] >>
  qexistsl_tac [`b0`, `mk_inst ds.cs_next_id CALLDATASIZE []
    [STRING #"%" (toString ds.cs_next_var)]`] >>
  gvs[mk_inst_def]
QED
