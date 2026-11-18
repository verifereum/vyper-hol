(* Extract all observations from the same entry-to-revert origin path. *)
Theory entryJointRevertExit
Ancestors
  fragGasOriginPtrExec fragGasOriginPtr fragGasOrigin fragGasMode
  fragExec fragExecPtr fragContinuationPtr entryDispatchPtr
  ptrSafeRun ptrDiscipline fragGasPathMem fragGasPathPtr
  venomExecSemantics venomState venomInst finite_map list

Theorem entry_joint_revert_exit:
  !ctx func vs s G' tn'.
    ctx.ctx_entry = SOME "__entry" /\
    lookup_function "__entry" ctx.ctx_functions = SOME func /\
    fn_entry_label func = SOME "__entry" /\
    entry_prov func
      (vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry";
                  vs_inst_idx := 0 |>) FEMPTY = FEMPTY /\
    entry_taint_vars func
      (vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry";
                  vs_inst_idx := 0 |>) entry_taint = entry_taint /\
    (!D explicit.
      gas_origin_ptr_path (D,0,explicit,ctx,func,[])
        (vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry";
                    vs_inst_idx := 0 |>, FEMPTY, entry_taint) []
        (Abort Revert_abort s,G',tn')) ==>
    (?fuel. run_context fuel ctx vs = Abort Revert_abort s) /\
    gas_path_mem ctx func
      (vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry";
                  vs_inst_idx := 0 |>) 0 (Abort Revert_abort s) /\
    (!D. gas_path_ptr D 0 ctx func [] FEMPTY entry_taint
      (vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry";
                  vs_inst_idx := 0 |>) 0 G' tn' (Abort Revert_abort s)) /\
    (!D fuel. ptr_safe_blocks D 0 fuel ctx func [] FEMPTY entry_taint
      (vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry";
                  vs_inst_idx := 0 |>))
Proof
  rpt gen_tac >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_origin_ptr_path _ (vs0,_,_) _ _` >>
  `!D. ?fuel. run_from fuel ctx func vs0 = Abort Revert_abort s /\
       ptr_safe_run D 0 fuel ctx func [] FEMPTY entry_taint vs0` by
    (gen_tac >>
     first_x_assum (qspecl_then [`D`, `EMPTY`] mp_tac) >>
     disch_then (mp_tac o MATCH_MP gas_origin_ptr_path_exec) >>
     simp[exit_result_def] >> metis_tac[]) >>
  `gas_origin_path T EMPTY ctx func vs0 [] (Abort Revert_abort s) /\
   !D. gas_path_ptr D 0 ctx func [] FEMPTY entry_taint vs0 0 G' tn'
         (Abort Revert_abort s)` by
    (conj_tac >>
     metis_tac[gas_origin_ptr_path_projections, LENGTH]) >>
  `~vs0.vs_halted` by
    (qpat_x_assum `gas_origin_path _ _ _ _ _ _ _` mp_tac >>
     simp[Once gas_origin_path_cases, gas_origin_edge_def] >> metis_tac[]) >>
  `?fuel. run_from fuel ctx func vs0 = Abort Revert_abort s` by metis_tac[] >>
  `?bb. lookup_block vs0.vs_current_bb func.fn_blocks = SOME bb` by
    (Cases_on `lookup_block vs0.vs_current_bb func.fn_blocks` >>
     gvs[run_from_def]) >>
  `phi_prefix_length bb.bb_instructions = 0` by
    (irule run_from_nonerror_no_phi >>
     qexistsl_tac [`ctx`, `func`, `fuel`, `vs0`] >>
     simp[Abbr `vs0`]) >>
  conj_tac
  >- (qexists_tac `SUC fuel` >>
      simp[run_context_def, run_function_def] >>
      drule_all run_blocks_run_from_no_phi >>
      simp[Abbr `vs0`]) >>
  conj_tac
  >- (drule gas_origin_path_erase >> simp[gas_marked_path_def]) >>
  conj_tac >- simp[] >>
  gen_tac >> irule ptr_safe_blocks_from_phi_free_run >>
  simp[Abbr `vs0`] >>
  irule ptr_safe_run_all_fuel >> metis_tac[exec_result_distinct]
QED
