Theory fmpStageFmpStepsEntryState
Ancestors
  fmpStageRel fmpLowerSequenceExec o1PassContract unitTransformDefs
  o1LowerDloadShared o1LowerDloadRelocationKernel ptrDiscipline
  analysisSimDefs venomExecSemantics venomState venomInst finite_map words list

Theorem fmp_entry_state_fields:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom ==>
  (vs with <| vs_prev_bb := NONE; vs_current_bb := lbl;
              vs_inst_idx := 0 |>).vs_vars = FEMPTY /\
  fmp_env_rel FEMPTY fn live FEMPTY tv
    (vs with <| vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0 |>)
    (vs' with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                 vs_inst_idx := idx; vs_vars := vars |>) /\
  fmp_params_rel FEMPTY []
    (vs with <| vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0 |>)
    (vs' with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                 vs_inst_idx := idx; vs_vars := vars |>) /\
  fmp_frontier_rel (w2n vs'.vs_initial_fmp) (w2n fmp)
    (w2n vs'.vs_initial_fmp) fmp
Proof
  simp[fmp_stage_ctx_def, o1_run_state_ok_def, o1_initial_state_ok_def] >>
  rpt strip_tac >>
  gvs[fmp_env_rel_def, fmp_params_rel_def, fmp_value_rel_def,
      ld_value_agree_def, word_agree_except_def,
      fmp_frontier_rel_def, fmp_variant_room_def]
QED

Theorem fmp_entry_run_root:
  lookup_function name C.ctx_functions = SOME fn /\
  lookup_block lbl fn.fn_blocks = SOME bb /\
  bb.bb_instructions = mk_inst id INITIAL_FMP [] [runner]::rest ==>
  !fuel. fmp_target_run fuel C name
    (s with <| vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0 |>)
    1 ((update_var runner s.vs_initial_fmp s) with
       <| vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 1 |>)
Proof
  rw[fmp_target_run_def] >>
  qexists_tac
    `update_var runner s.vs_initial_fmp
      (s with <| vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0 |>)` >>
  simp[fmp_root_initial_fmp_exec, update_var_def]
QED

Theorem fmp_entry_shared_fields:
  fmp_stage_ctx rpolicy D C C' vs vs' fmp eom /\
  s = vs with <| vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0 |> /\
  t = vs' with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                  vs_inst_idx := idx; vs_vars := vars |> ==>
  s.vs_current_bb = t.vs_current_bb /\ s.vs_prev_bb = t.vs_prev_bb /\
  s.vs_call_ctx = t.vs_call_ctx /\ s.vs_tx_ctx = t.vs_tx_ctx /\
  s.vs_block_ctx = t.vs_block_ctx /\ s.vs_data_section = t.vs_data_section /\
  s.vs_labels = t.vs_labels /\ s.vs_code = t.vs_code /\
  s.vs_prev_hashes = t.vs_prev_hashes /\
  w2n s.vs_initial_fmp = w2n fmp /\
  w2n t.vs_initial_fmp = w2n vs'.vs_initial_fmp /\
  s.vs_fmp = fmp /\
  ld_memory_agree (fmp_ld_sites FEMPTY) eom entry_taint.t_mem
    s.vs_memory t.vs_memory /\
  ld_shared_agree D s.vs_call_ctx.cc_address entry_taint s t /\
  s.vs_returndata = t.vs_returndata /\ s.vs_halted = t.vs_halted
Proof
  simp[fmp_stage_ctx_def] >> rpt strip_tac >>
  gvs[fmp_ld_sites_def, FMAP_MAP2_FEMPTY, ld_memory_agree_empty] >>
  mp_tac (Q.INST [`s` |-> `vs'`, `A` |-> `vs'.vs_call_ctx.cc_address`,
                    `tn` |-> `entry_taint`] ld_shared_agree_refl) >>
  simp[ld_shared_agree_def]
QED
