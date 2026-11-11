Theory internalReturnCopyFwdIndexCfgBoundary
Ancestors
  internalReturnCopyFwdIndexCfgProbe internalReturnCopyFwdIndexProbe
  internalReturnCopyFwdHaltProbe internalReturnCopyFwdSim reachableFnSim
  ptrDiscipline taintAgree venomExecSemantics venomInst venomState
  finite_map list o1LowerDloadShared contextCodegenRel passSimulationDefs

Definition ircf_index_cfg_caller_def:
  ircf_index_cfg_caller q = (ircf_index_state q) with vs_current_bb := "main"
End

Definition ircf_index_cfg_seed_def:
  ircf_index_cfg_seed q = q with
    <| vs_call_entry_fmp := q.vs_fmp; vs_return_pc_token := 0w |>
End

Definition ircf_index_cfg_stack_def:
  ircf_index_cfg_stack q =
    [<| cf_fn := ircf_index_main;
        cf_inst := mk_inst 1 INVOKE [Label "test"] [];
        cf_state := ircf_index_cfg_caller q;
        cf_params := []; cf_prov := FEMPTY; cf_tvar := entry_taint.t_var |>]
End

Theorem ircf_index_cfg_boundary_fields:
  (ircf_index_state q).vs_allocas = FEMPTY /\
  ~(ircf_index_state q).vs_halted
Proof
  simp[ircf_index_state_def]
QED

Theorem ircf_index_cfg_boundary_call:
  frame_reachable (ircf_index_state q) ircf_index_cfg_ctx [] [] FEMPTY
    entry_taint ircf_index_main (mk_inst 1 INVOKE [Label "test"] [])
    (ircf_index_cfg_caller q)
Proof
  irule frame_reachable_entry >>
  simp[ircf_index_cfg_ctx_def, ircf_index_main_def, mk_raw_function_def,
       lookup_function_def, fn_entry_label_def, entry_block_def, FIND_thm,
       ircf_index_cfg_caller_def, ircf_index_state_def] >>
  simp[active_inst_def, enters_block_def, lookup_block_def, FIND_thm,
       eval_phis_def, phi_prefix_length_def, mk_inst_def]
QED

Theorem ircf_index_cfg_boundary_setup:
  setup_callee ircf_index_cfg_fn [] (ircf_index_cfg_caller q) =
    SOME (ircf_index_state (ircf_index_cfg_seed q))
Proof
  simp[setup_callee_def, ircf_index_cfg_fn_def, mk_raw_function_def,
       ircf_index_cfg_entry_def, ircf_index_cfg_seed_def,
       ircf_index_cfg_caller_def, ircf_index_state_def] >>
  simp[venom_state_component_equality]
QED

Theorem ircf_index_cfg_boundary_entry:
  block_reach (ircf_index_state q) ircf_index_cfg_ctx (ircf_index_cfg_stack q)
    [] FEMPTY entry_taint ircf_index_cfg_fn
    (ircf_index_state (ircf_index_cfg_seed q))
Proof
  assume_tac ircf_index_cfg_boundary_call >>
  drule frame_reachable_call_block_reach >>
  disch_then (qspecl_then [`[]`, `"test"`, `ircf_index_state (ircf_index_cfg_seed q)`,
    `ircf_index_cfg_fn`, `[]`] mp_tac) >>
  simp[ircf_index_cfg_boundary_setup, ircf_index_cfg_stack_def,
       decode_invoke_def, mk_inst_def, eval_operands_def] >>
  simp[ircf_index_cfg_ctx_def, lookup_function_def, ircf_index_main_def,
       ircf_index_cfg_fn_def, mk_raw_function_def, FIND_thm,
       active_inst_def, ircf_index_cfg_caller_def, ircf_index_state_def,
       entry_taint_def, mk_inst_def]
QED

Theorem ircf_index_cfg_boundary_fuel:
  fn_sim_below D vs C C' R Rret (SUC 0)
Proof
  simp[ircf_halt_probe_fuel_zero]
QED

Theorem ircf_index_cfg_boundary_terminates:
  terminates (run_block k C ircf_index_cfg_return (ircf_index_cfg_return_state q))
Proof
  simp[ircf_index_cfg_source_run, terminates_def]
QED

Theorem ircf_index_cfg_boundary_conclusion:
  ~(?m bb'.
    lookup_block (ircf_index_cfg_return_state q).vs_current_bb
      ircf_index_cfg_target_fn.fn_blocks = SOME bb' /\
    block_step_rel D vs C (ircf_R D meta rma C)
      (ircf_R_ret D meta rma C) stk PG ircf_index_cfg_fn
      (run_block k C ircf_index_cfg_return (ircf_index_cfg_return_state q))
      (run_block m C' bb' (ircf_index_cfg_return_state q)))
Proof
  simp[ircf_index_cfg_lookup_blocks] >>
  rpt strip_tac >>
  gvs[ircf_index_cfg_source_run, ircf_index_cfg_target_run,
      block_step_rel_def, fn_run_rel_def, ircf_R_ret_def] >>
  drule taint_agree_frame >>
  simp[venom_state_component_equality, ircf_index_cfg_return_state_def]
QED

Theorem ircf_index_cfg_boundary_entry_active:
  frame_reachable (ircf_index_state q) ircf_index_cfg_ctx (ircf_index_cfg_stack q)
    [] FEMPTY entry_taint ircf_index_cfg_fn
    (EL 0 ircf_index_cfg_entry.bb_instructions)
    (ircf_index_state (ircf_index_cfg_seed q))
Proof
  mp_tac ircf_index_cfg_boundary_entry >>
  simp[block_reach_def] >> disch_then irule >>
  simp[enters_block_def, active_inst_def, ircf_index_cfg_fn_def,
       mk_raw_function_def, ircf_index_cfg_entry_def, ircf_index_state_def,
       lookup_block_def, FIND_thm, mk_inst_def, eval_phis_def,
       phi_prefix_length_def] >>
  qexists_tac `ircf_index_cfg_entry` >>
  simp[ircf_index_cfg_entry_def, mk_inst_def]
QED

Theorem ircf_index_cfg_boundary_reach:
  ?G tn. block_reach (ircf_index_state q) ircf_index_cfg_ctx
    (ircf_index_cfg_stack q) [] G tn ircf_index_cfg_fn
    (ircf_index_cfg_return_state (ircf_index_cfg_seed q))
Proof
  irule (cj 1 (cj 1 frame_reachable_walk)) >>
  qexistsl_tac [`FEMPTY`, `ircf_index_cfg_entry`, `0`,
    `OK (ircf_index_cfg_return_state (ircf_index_cfg_seed q))`,
    `ircf_index_state (ircf_index_cfg_seed q)`, `entry_taint`] >>
  assume_tac ircf_index_cfg_boundary_entry_active >>
  gvs[ircf_index_state_def] >>
  simp[ircf_index_cfg_entry_def, ircf_index_cfg_fn_def, mk_raw_function_def] >>
  EVAL_TAC
QED

Theorem ircf_index_cfg_boundary_relation:
  ircf_R D meta rma ircf_index_cfg_ctx (ircf_index_cfg_stack q) [] G tn
    ircf_index_cfg_fn
    (ircf_index_cfg_return_state (ircf_index_cfg_seed q))
    (ircf_index_cfg_return_state (ircf_index_cfg_seed q))
Proof
  simp[ircf_R_def, ircf_gam_stk_def, ircf_cross_def,
       ircf_index_cfg_stack_def, ircf_gam_cur_def, ircf_gam_def,
       ircf_index_cfg_caller_def, ircf_index_state_def] >>
  qexists_tac `tn` >>
  simp[entry_taint_vars_def, ircf_index_cfg_return_state_def,
       ircf_index_state_def, ircf_index_cfg_fn_def, mk_raw_function_def,
       lookup_block_def, FIND_thm, ircf_index_cfg_entry_def,
       ircf_index_cfg_return_def, phis_taint_def, mk_inst_def] >>
  simp[taint_agree_def] >>
  `ld_shared_agree D (ircf_index_cfg_seed q).vs_call_ctx.cc_address tn
    (ircf_index_cfg_seed q) (ircf_index_cfg_seed q)`
    by irule ld_shared_agree_refl >>
  gvs[ld_shared_agree_def, word_agree_except_def,
      venom_state_component_equality]
QED
