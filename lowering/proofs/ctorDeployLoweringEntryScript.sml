(* A piece of deploy_unit_execution_correct (ctorDeployLowering). *)
Theory ctorDeployLoweringEntry
Ancestors
  ctorDeployLoweringDefs o1PassContract stmtSimDefs ctorDeployLoweringEntryFmp
  ctorDeployLoweringEntryPrefix ctorDeployLoweringEntryBodyResources
  ctorDeployLoweringEntryStatic ctorDeployLoweringEntryStateRel
  exprLoweringProps compileEnv fragGasPath ctorDeployDefs bodyPtrDefs fragGasPathMem
  ctorDeployMemoryRunPtrEntry ctorDeployMemoryRunMemEntryTaskActual
  ctorDeployMemoryRunMemEntryProvenanceComplete
  ptrSafeRun venomExecSemantics fragExec
  fragGasOriginPtr fragGasOriginPtrLoop vyperStorageFootprint

(* The run from the unit's entry, after the payable check, the immutables
   region, the constructor arguments' registration and the lock, reaches
   the body start sa in a state s0 related to the source's body start
   (with the run's call outcomes, which the call-free body never reads),
   with the GAS readings still unread; every result from s0 is a result of
   run_context.  The source and the unit select the same constructor. *)
Theorem deploy_ctor_entry_reaches_body:
  !policy tops deploy_bc runtime_bc rpolicy dunit dout prog cplan am tx es vs
   body cenv nr nkey ut imm exit_lbl sa sb sj st_exit st_epilogue st_final func mut nr' body' am_c es0.
    deploy_phases policy tops (deploy_bc, runtime_bc)
      (rpolicy, dunit, dout, prog, cplan) /\
    deploy_source_ok tops am tx /\
    deploy_state_rel tops deploy_bc am tx es /\
    gas_variant vs (deploy_entry_state prog cplan tops es) /\
    deploy_ctor_code tops rpolicy runtime_bc dunit
      (body, cenv, nr, nkey, ut, imm, exit_lbl, sa, sb, sj, st_exit,
       st_epilogue, st_final, func) /\
    deploy_ctor_start tops am tx (mut, nr', body', am_c, es0) ==>
    nr' = nr /\ body' = body /\
    local_ptrs_reserved cenv sa /\ ~block_is_terminated sa /\
    ?s0.
      stmt_state_rel H dunit.cu_context func cenv (deploy_evaluation_context tops am tx)
        (es0 with outcomes := SOME vs.vs_outcomes) s0 /\
      ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
      s0.vs_gas_readings = vs.vs_gas_readings /\
      s0.vs_code = vs.vs_code /\ s0.vs_labels = vs.vs_labels /\
      !fuel r. run_from fuel dunit.cu_context func s0 = r /\
               (!e. r <> Error e) ==>
               ?fuel'. run_context fuel' dunit.cu_context vs = r
Proof
  rpt gen_tac >> strip_tac >>
  drule_all deploy_ctor_entry_body_resources >> strip_tac >>
  drule_all deploy_ctor_body_entry_static >> strip_tac >>
  drule_all deploy_ctor_entry_body_state_rel >> strip_tac >>
  gvs[] >> qexists `actual` >>
  gvs[stmt_state_rel_def, immutable_alloca_sep_def,
      fresh_label_def, comp_bind_def, comp_return_def] >>
  conj_tac >> first_assum ACCEPT_TAC
QED

(* Actual zero-GAS prefix to the same constructor body state. *)
Theorem deploy_ctor_entry_gas_path:
  !policy tops deploy_bc runtime_bc rpolicy dunit dout prog cplan am tx es vs
   body cenv nr nkey ut imm exit_lbl sa sb sj st_exit st_epilogue st_final func mut nr' body' am_c es0.
    deploy_phases policy tops (deploy_bc, runtime_bc)
      (rpolicy, dunit, dout, prog, cplan) /\
    deploy_source_ok tops am tx /\
    deploy_state_rel tops deploy_bc am tx es /\
    gas_variant vs (deploy_entry_state prog cplan tops es) /\
    deploy_ctor_code tops rpolicy runtime_bc dunit
      (body, cenv, nr, nkey, ut, imm, exit_lbl, sa, sb, sj, st_exit,
       st_epilogue, st_final, func) /\
    deploy_ctor_start tops am tx (mut, nr', body', am_c, es0) ==>
    nr' = nr /\ body' = body /\
    local_ptrs_reserved cenv sa /\ ~block_is_terminated sa /\
    ?s0.
      dunit.cu_context.ctx_entry = SOME "__deploy" /\
      lookup_function "__deploy" dunit.cu_context.ctx_functions = SOME func /\
      fn_entry_label func = SOME "__deploy" /\
      gas_path dunit.cu_context func
        (vs with <| vs_prev_bb := NONE; vs_current_bb := "__deploy";
                    vs_inst_idx := 0 |>) 0 (OK s0) /\
      stmt_state_rel dunit.cu_context func cenv (deploy_evaluation_context tops am tx)
        (es0 with outcomes := SOME vs.vs_outcomes) s0 /\
      ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
      s0.vs_gas_readings = vs.vs_gas_readings /\
      s0.vs_code = vs.vs_code /\ s0.vs_labels = vs.vs_labels /\
      !fuel r. run_from fuel dunit.cu_context func s0 = r /\
               (!e. r <> Error e) ==>
               ?fuel'. run_context fuel' dunit.cu_context vs = r
Proof
  rpt gen_tac >> strip_tac >>
  `supported_program tops` by fs[deploy_source_ok_def] >>
  drule_all deploy_ctor_original_entry_shape >> strip_tac >>
  drule_all deploy_ctor_entry_body_resources_gas_path >> strip_tac >>
  drule_all deploy_ctor_body_entry_static >> strip_tac >>
  drule_all deploy_ctor_entry_body_state_rel >> strip_tac >>
  gvs[] >> qexists `actual` >>
  gvs[stmt_state_rel_def, immutable_alloca_sep_def,
      fresh_label_def, comp_bind_def, comp_return_def] >>
  conj_tac >> first_assum ACCEPT_TAC
QED

(* Retain the actual decoder prefix and its history while exporting the
   registration provenance and empty pointer taint at the same endpoint.
   Complete source argument bounds belong to this entry producer; padded
   decoder reads alone do not establish a source-section memory window. *)
(* TEMPORARILY CHEATED - horizon restatement (ENTRY-H-r1) and RULE F joint
   path; the original proof below proves the pre-horizon statement.
Proof
  rpt gen_tac >> strip_tac >>
  drule_all ctorDeployLoweringEntrySelectionTheory.deploy_ctor_entry_selection_agrees >>
  strip_tac >> gvs[] >>
  `nr = F` by
    (drule_all (cj 1 deploy_ctor_entry_body_resources) >> simp[]) >>
  drule_all deploy_ctor_body_entry_static >> strip_tac >>
  `supported_program tops` by fs[deploy_source_ok_def] >>
  drule_all deploy_ctor_original_entry_shape >> strip_tac >>
  drule_all deploy_ptr_entry_prefix_related_checked >> strip_tac >>
  drule gas_path_mem_exec >> simp[fragExecTheory.exit_result_def] >> strip_tac >> gvs[] >>
  qexistsl [`actual`,`H`,`qt`] >> simp[] >>
  conj_tac
  >- (strip_tac >>
      qpat_x_assum `(!fuel. ptr_safe_run _ _ _ _ _ _ H qt actual) ==> _` drule >>
      disch_tac >> Cases_on `fuel` >> simp[Once ptr_safe_blocks_def] >>
      simp[eval_phis_no_phi] >>
      qpat_x_assum `!fuel. ptr_safe_run _ _ _ _ _ _ FEMPTY entry_taint _`
        (qspec_then `n` mp_tac) >> simp[ptr_safe_run_def]) >>
  rpt strip_tac >>
  first_x_assum (qspec_then `fuel` mp_tac) >>
  simp[] >> strip_tac >>
  qexists `SUC fuel'` >>
  simp[run_context_def, run_function_def, run_blocks_run_from_no_phi]
QED
*)
Theorem deploy_ctor_entry_joint:
  !policy tops deploy_bc runtime_bc rpolicy dunit dout prog cplan am tx es vs
   body cenv nr nkey ut imm exit_lbl sa sb sj st_exit st_epilogue st_final func mut nr' body' am_c es0.
    deploy_phases policy tops (deploy_bc, runtime_bc)
      (rpolicy, dunit, dout, prog, cplan) /\
    deploy_source_ok tops am tx /\
    deploy_state_rel tops deploy_bc am tx es /\
    gas_variant vs (deploy_entry_state prog cplan tops es) /\
    deploy_ctor_code tops rpolicy runtime_bc dunit
      (body, cenv, nr, nkey, ut, imm, exit_lbl, sa, sb, sj, st_exit,
       st_epilogue, st_final, func) /\
    deploy_ctor_start tops am tx (mut, nr', body', am_c, es0) ==>
    nr' = nr /\ body' = body /\
    local_ptrs_reserved cenv sa /\ ~block_is_terminated sa /\
    ?s0 G0 tn0.
      dunit.cu_context.ctx_entry = SOME "__deploy" /\
      lookup_function "__deploy" dunit.cu_context.ctx_functions = SOME func /\
      fn_entry_label func = SOME "__deploy" /\
      gas_path dunit.cu_context func
        (vs with <| vs_prev_bb := NONE; vs_current_bb := "__deploy";
                    vs_inst_idx := 0 |>) 0 (OK s0) /\
      gas_path_mem dunit.cu_context func
        (vs with <| vs_prev_bb := NONE; vs_current_bb := "__deploy";
                    vs_inst_idx := 0 |>) 0 (OK s0) /\
      alloca_history func s0 /\
      return_buf_frame NONE cenv sa s0 /\
      ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
      s0.vs_gas_readings = vs.vs_gas_readings /\
      s0.vs_code = vs.vs_code /\ s0.vs_labels = vs.vs_labels /\
      (!fuel r. run_from fuel dunit.cu_context func s0 = r /\
                (!e. r <> Error e) ==>
                ?fuel'. run_context fuel' dunit.cu_context vs = r) /\
      !st0 H.
        valid_horizon (deploy_evaluation_context tops am tx) st0 H
          (es0 with outcomes := SOME vs.vs_outcomes).storage_trace ==>
        ((!fuel. ptr_safe_run (deploy_dead H tops runtime_bc am tx)
            (imm_len tops) fuel dunit.cu_context func [] G0 tn0 s0) ==>
          !fuel. ptr_safe_blocks (deploy_dead H tops runtime_bc am tx)
            (imm_len tops) fuel dunit.cu_context func [] FEMPTY entry_taint
            (vs with <| vs_prev_bb := NONE; vs_current_bb := "__deploy";
                        vs_inst_idx := 0 |>)) /\
        deploy_ptr_inv H tops runtime_bc am tx imm G0 tn0 s0 /\
        ghost_inv_at (deploy_dead H tops runtime_bc am tx) (imm_len tops) NONE
          cenv (deploy_evaluation_context tops am tx)
          (es0 with outcomes := SOME vs.vs_outcomes) G0 tn0 s0 /\
        stmt_state_rel H dunit.cu_context func cenv
          (deploy_evaluation_context tops am tx)
          (es0 with outcomes := SOME vs.vs_outcomes) s0 /\
        !explicit.
          gas_origin_ptr_path
            (deploy_dead H tops runtime_bc am tx, imm_len tops, explicit,
             dunit.cu_context, func, [])
            (vs with <| vs_prev_bb := NONE; vs_current_bb := "__deploy";
                        vs_inst_idx := 0 |>, FEMPTY, entry_taint)
            [] (OK s0, G0, tn0)
Proof
  cheat
QED
