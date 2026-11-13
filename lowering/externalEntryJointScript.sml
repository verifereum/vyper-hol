(*
 * Runtime joint body entry on finite horizons: one actual body-start state
 * s0 carrying zero-GAS reachability from __entry, its memory-safe twin,
 * the allocation history and frame, and, at every horizon valid for the
 * call's storage trace, the pointer-safety lift, the pointer ghost, the
 * statement state relation and the zero-GAS pointer path from __entry to s0.
 * The endpoint is chosen before any horizon.
 *
 * r4: st is pinned by runtime_selected_body_start.
 *
 * Proof: the prefix seam (external_entry_reaches_registration_ptr) runs
 * __entry to the start s1 of argument registration; the registration seam
 * (register_positional_args_ptr) runs s1 to the body start s0.  Both carry
 * the zero-GAS memory-checked path and the joint pointer path, which
 * compose; the remaining facts at s0 follow from the composed path.
 *
 * TOP-LEVEL:
 *   external_entry_joint
 *)
Theory externalEntryJoint
Ancestors
  compileVyper moduleLowering compileEnv context supportedProgram e2eDefs
  vyperLoweringCorrect vyperInterpreter venomWf venomInst venomExecSemantics
  fragExec fragGasPath fragGasPathMem allocaHistory loweringStateRelDefs
  loweringPosts exprLoweringProps vyperStorageFootprint ptrSafeRun
  ptrDiscipline bodyPtrDefs runtimeBodyStartDefs fragGasOriginPtr
  entryPtrSeamPrefix entryPtrSeamRegister externalEntryChecks entryStateRel
  selectedBodyCode bodyMemAggregatePath fragGasPathFrameMem venomMemProofs
  moduleLoweringProps vyperCompiler

(* Helper: the runtime entry function, its label and its phi-free entry block. *)
Theorem runtime_entry_function_no_phi:
  lower_vyper_runtime_unit tops rpolicy = SOME unit /\
  supported_program tops /\ name <> "__default__" /\
  ALL_DISTINCT (FLAT (MAP (external_name_keys_toplevel (NONE:num option)) tops)) /\
  vyperInterpreter$lookup_function NONE name External tops =
    SOME (mut,F,args,[],ret,fbody) ==>
  unit.cu_context.ctx_entry = SOME "__entry" /\
  ?func bb.
    venomInst$lookup_function "__entry" unit.cu_context.ctx_functions = SOME func /\
    fn_entry_label func = SOME "__entry" /\
    lookup_block "__entry" func.fn_blocks = SOME bb /\
    phi_prefix_length bb.bb_instructions = 0
Proof
  strip_tac >>
  `supported_declaration_headers tops` by fs[supported_program_def] >>
  drule_all external_lookup_raw_package_member >> strip_tac >>
  qspecl_then [`tops`, `rpolicy.rpol_target`, `mut`,
    `lookup_raw_return_or_F (NONE:num option) name External tops`,
    `name`, `args`, `ret`, `fbody`] strip_assume_tac selected_external_package >>
  drule_all source_runtime_entry_checks_code >> strip_tac >>
  `sa.cs_current_bb = "__entry" /\ sa.cs_current_insts = []` by
    (qpat_x_assum `fresh_label _ _ = _` mp_tac >>
     simp[fresh_label_def, initial_compile_state_def, LET_THM] >>
     strip_tac >> gvs[]) >>
  drule_all linear_dispatch_entry_no_phi >> strip_tac >>
  simp[] >> qexistsl_tac [`func`, `bb`] >>
  gvs[fn_entry_label_def, entry_block_def, NULL_EQ]
QED

(* Helper: facts at the end s0 of a zero-GAS memory-checked path from the
   initial __entry state. *)
Theorem entry_path_endpoint_facts:
  initial_venom_state_rel tops am tx vs /\
  fn_inst_ids_distinct func /\
  gas_path_mem ctx func
    (vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry";
                vs_inst_idx := 0 |>) 0 (OK s0) ==>
  gas_path ctx func
    (vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry";
                vs_inst_idx := 0 |>) 0 (OK s0) /\
  alloca_history func s0 /\
  s0.vs_code = vs.vs_code /\ s0.vs_labels = vs.vs_labels /\
  runs_through ctx func
    (vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry";
                vs_inst_idx := 0 |>) s0
Proof
  strip_tac >>
  qabbrev_tac `ss = vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry";
                               vs_inst_idx := 0 |>` >>
  `ss.vs_allocas = FEMPTY /\ ss.vs_inst_idx = 0` by
    fs[Abbr `ss`, initial_venom_state_rel_def] >>
  drule gas_path_mem_exec >> strip_tac >> gvs[fragExecTheory.exit_result_def] >>
  drule registration_path_code >> simp[] >> strip_tac >>
  rpt conj_tac
  >- (irule gas_path_mem_zero_history >> simp[] >>
      qexistsl_tac [`ctx`, `ss`] >> simp[alloca_history_empty] >>
      rpt strip_tac >> irule aggregate_mem_path_alloca_inv >>
      metis_tac[alloca_inv_empty_proof])
  >- fs[Abbr `ss`]
  >- fs[Abbr `ss`] >>
  simp[runs_through_def] >> metis_tac[]
QED


Theorem external_entry_joint:
  !tops rpolicy unit am tx ret vs mut args fbody env es0.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    source_deployment_rel tops am tx /\
    valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
    initial_venom_state_rel tops am tx vs /\
    lookup_function NONE tx.function_name External tops =
      SOME (mut, F, args, [], ret, fbody) /\
    bind_arguments (type_env tops) args tx.args = SOME env /\
    send_call_value mut
      (initial_evaluation_context am.sources am.layouts tx NONE)
      (initial_state am [env] with
         <| outcomes := SOME vs.vs_outcomes; requests := [] |>) =
      (INL (), es0) ==>
    ?lbl cenv0 pos_args min_cds is_payable nkey ut' iv rt st cenv sa st' func
     s0 G0 tn0.
      set_external_package_target rpolicy.rpol_target
        (package_external_fn tops T (K global_nonreentrant_slot)
           (mut, F, lookup_raw_return_or_F (NONE : num option)
                       tx.function_name External tops,
            tx.function_name, args, [], ret, fbody)) =
        (lbl, cenv0, pos_args, min_cds, is_payable, F, nkey, ut', iv, fbody,
         rt) /\
      runtime_selected_body_start tops rpolicy
        (lbl, cenv0, pos_args, min_cds, is_payable, F, nkey, ut', iv, fbody, rt) st /\
      compile_register_positional_args cenv0 pos_args 4 st = (cenv, sa) /\
      compile_guarded_body cenv F nkey ut' iv fbody rt sa = ((), st') /\
      fn_has_code sa st' func /\ fn_inst_ids_distinct func /\
      local_ptrs_reserved cenv sa /\ ~block_is_terminated sa /\
      unit.cu_context.ctx_entry = SOME "__entry" /\
      lookup_function "__entry" unit.cu_context.ctx_functions = SOME func /\
      fn_entry_label func = SOME "__entry" /\
      gas_path unit.cu_context func
        (vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry";
                    vs_inst_idx := 0 |>) 0 (OK s0) /\
      gas_path_mem unit.cu_context func
        (vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry";
                    vs_inst_idx := 0 |>) 0 (OK s0) /\
      alloca_history func s0 /\
      return_buf_frame NONE cenv sa s0 /\
      ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
      s0.vs_gas_readings = vs.vs_gas_readings /\
      s0.vs_code = vs.vs_code /\ s0.vs_labels = vs.vs_labels /\
      (!fuel r. run_from fuel unit.cu_context func s0 = r /\
                (!e. r <> Error e) ==>
                ?fuel'. run_context fuel' unit.cu_context vs = r) /\
      !st0 H.
        valid_horizon
          (initial_evaluation_context am.sources am.layouts tx NONE) st0 H
          es0.storage_trace ==>
        ((!fuel. ptr_safe_run
            (cx_dead H (initial_evaluation_context am.sources am.layouts tx NONE))
            0 fuel unit.cu_context func [] G0 tn0 s0) ==>
          !fuel. ptr_safe_blocks
            (cx_dead H (initial_evaluation_context am.sources am.layouts tx NONE))
            0 fuel unit.cu_context func [] FEMPTY entry_taint
            (vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry";
                        vs_inst_idx := 0 |>)) /\
        ghost_inv_at
          (cx_dead H (initial_evaluation_context am.sources am.layouts tx NONE))
          0 NONE cenv
          (initial_evaluation_context am.sources am.layouts tx NONE) es0
          G0 tn0 s0 /\
        stmt_state_rel H unit.cu_context func cenv
          (initial_evaluation_context am.sources am.layouts tx NONE) es0 s0 /\
        !explicit.
          gas_origin_ptr_path
            (cx_dead H (initial_evaluation_context am.sources am.layouts tx NONE),
             0, explicit, unit.cu_context, func, [])
            (vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry";
                        vs_inst_idx := 0 |>, FEMPTY, entry_taint)
            [] (OK s0, G0, tn0)
Proof
  rpt gen_tac >> strip_tac >>
  `tx.function_name <> "__default__"` by fs[valid_vyper_call_def] >>
  drule source_typing_ok_external_names_distinct >> strip_tac >>
  drule_all runtime_entry_function_no_phi >> strip_tac >>
  drule_all external_entry_reaches_registration_ptr >> strip_tac >>
  drule_all register_positional_args_ptr >> strip_tac >>
  `gas_path_mem unit.cu_context func
     (vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry";
                 vs_inst_idx := 0 |>) (0 + 0) (OK s0)` by
    (irule gas_path_mem_then >> qexists_tac `s1` >> simp[]) >>
  fs[] >>
  drule_all entry_path_endpoint_facts >> strip_tac >>
  qexistsl_tac [`lbl`, `cenv0`, `pos_args`, `min_cds`, `is_payable`, `nkey`,
    `ut'`, `iv`, `rt`, `st`, `cenv`, `sa`, `st'`, `func`, `s0`, `G0`, `tn0`] >>
  simp[return_buf_frame_def] >>
  conj_tac >-
    (rpt strip_tac >> irule entry_context_continuation >> simp[] >>
     qexists_tac `bb` >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `IEC = initial_evaluation_context am.sources am.layouts tx NONE` >>
  first_x_assum (qspec_then `H` strip_assume_tac) >>
  simp[GSYM ghost_inv_cx_dead] >>
  conj_tac >-
    (strip_tac >>
     qpat_x_assum `!D. (!fuel. ptr_safe_run D 0 fuel _ _ [] G1 tn1 s1) ==> _` irule >>
     qpat_x_assum `!D. (!fuel. ptr_safe_run D 0 fuel _ _ [] G0 tn0 s0) ==> _` irule >>
     simp[]) >>
  gen_tac >>
  qpat_x_assum `!D explicit. gas_origin_ptr_path _ (_,FEMPTY,_) _ _`
    (qspecl_then [`cx_dead H IEC`, `explicit`] assume_tac) >>
  qpat_x_assum `!D explicit. gas_origin_ptr_path _ (s1,G1,tn1) _ _`
    (qspecl_then [`cx_dead H IEC`, `explicit`] assume_tac) >>
  qpat_x_assum `gas_origin_ptr_path _ (_,FEMPTY,_) _ _`
    (mp_tac o MATCH_MP gas_origin_ptr_path_append) >>
  disch_then (qspecl_then [`s1`, `G1`, `tn1`, `[]`, `OK s0`, `G0`, `tn0`] mp_tac) >>
  simp[]
QED
