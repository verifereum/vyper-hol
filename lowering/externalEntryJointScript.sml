(*
 * Runtime joint body entry on finite horizons: one actual body-start state
 * s0 carrying zero-GAS reachability from __entry, its memory-safe twin,
 * the allocation history and frame, and, at every horizon valid for the
 * call's storage trace, the pointer-safety lift, the pointer ghost, the
 * statement state relation and the zero-GAS pointer path from __entry to s0.
 * The endpoint is chosen before any horizon.
 *
 * r4: st is pinned by runtime_selected_body_start.  The statement is fixed; its proof is open (cheat) and is being done on
 * the canonical registration path.
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
  cheat
QED
