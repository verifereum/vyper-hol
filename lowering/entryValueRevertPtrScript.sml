(* Pointer-safe dispatch into a rejecting external call-value check. *)
Theory entryValueRevertPtr
Ancestors entryDispatchPtr entryChecksPtr sourceEntryCode sourceValueRejection
  ptrSafeRun ptrDiscipline moduleLowering compileEnv emitHelper fragExec
  venomExecSemantics venomInst venomState list finite_map words
  actualEntryAllocationFrame moduleLoweringProps vyperLoweringCorrect
  e2eDefs vyperTypeContractSoundness vyperState vyperContext vyperInterpreter

Theorem ptr_safe_blocks_nonphi_run:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb 0 = SOME inst /\ inst.inst_opcode <> PHI /\
  s.vs_inst_idx = 0 /\
  (!fuel. ptr_safe_run D lo fuel ctx fn PG G tn s) ==>
  !fuel. ptr_safe_blocks D lo fuel ctx fn PG G tn s
Proof
  strip_tac >>
  Cases_on `bb.bb_instructions` >> gvs[get_instruction_def] >>
  Cases >> simp[Once ptr_safe_blocks_def, eval_phis_def, phi_prefix_length_def] >>
  first_x_assum (qspec_then `n` mp_tac) >>
  simp[ptr_safe_run_def]
QED

Theorem compile_entry_checks_nonpayable_head:
  compile_entry_checks min_cds F opened = ((),checked) /\
  fn_has_code opened checked fn /\ opened.cs_current_insts = [] ==>
  ?bb inst. lookup_block opened.cs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb 0 = SOME inst /\ inst.inst_opcode = CALLVALUE
Proof
  strip_tac >>
  `?tail. checked.cs_current_bb = opened.cs_current_bb /\
    checked.cs_current_insts = opened.cs_current_insts ++
      mk_inst opened.cs_next_id CALLVALUE []
        ["%" ++ toString opened.cs_next_var] :: tail` by
    (qpat_x_assum `compile_entry_checks _ _ _ = _` mp_tac >>
     Cases_on `4 < min_cds` >>
     simp[compile_entry_checks_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_void_def, emit_inst_def,
       fresh_var_def, fresh_id_def, emit_def] >> strip_tac >> gvs[]) >>
  drule_all fn_has_code_same_block >> strip_tac >>
  first_x_assum (qspec_then `0` mp_tac) >> simp[] >> strip_tac >>
  qexistsl_tac [`bb`, `mk_inst opened.cs_next_id CALLVALUE []
    ["%" ++ toString opened.cs_next_var]`] >> simp[mk_inst_def]
QED

Theorem dispatch_nonpayable_check_ptr_safe:
  compile_selector_dispatch_linear selectors fallback st = ((),st') /\
  fn_has_code st st' fn /\
  EVERY (\(sel,lbl). sel < 2 ** 32) selectors /\
  LENGTH ss.vs_call_ctx.cc_calldata < dimword (:256) /\
  fresh_vars_wrt st ss /\ ~ss.vs_halted /\
  ss.vs_current_bb = st.cs_current_bb /\
  ss.vs_inst_idx = LENGTH st.cs_current_insts /\
  allocas_from lo ss /\ ~ctx_has_dalloca ctx /\
  ss.vs_call_ctx.cc_callvalue <> 0w /\
  compile_entry_checks min_cds F opened = ((),checked) /\
  fn_has_code opened checked fn /\ ~block_is_terminated opened /\
  opened.cs_current_insts = [] /\
  opened.cs_current_bb =
    linear_dispatch_target ss.vs_call_ctx.cc_calldata selectors fallback ==>
  !G tn fuel. ptr_safe_run D lo fuel ctx fn PG G tn ss
Proof
  strip_tac >> irule compile_selector_dispatch_linear_ptr_continuation >> simp[] >>
  qexistsl_tac [`fallback`, `selectors`, `st`, `st'`] >> gvs[] >>
  rpt strip_tac >>
  drule_all compile_entry_checks_nonpayable_head >> strip_tac >>
  drule vars_pc_only_fields >> strip_tac >>
  drule vars_pc_only_allocas >> strip_tac >>
  irule ptr_safe_blocks_nonphi_run >>
  simp[] >> reverse conj_tac
  >- (qexistsl_tac [`bb`, `inst`] >> gvs[]) >>
  irule compile_entry_checks_value_revert_ptr_safe >>
  simp[] >> conj_tac >- (gvs[allocas_from_def] >> metis_tac[]) >>
  qexistsl_tac [`min_cds`, `opened`, `checked`] >> gvs[]
QED

Theorem initial_entry_dispatch_scalars:
  source_typing_ok tops am tx /\ initial_venom_state_rel tops am tx vs ==>
  fresh_vars_wrt ds
    (vs with <| vs_prev_bb := NONE; vs_current_bb := elbl; vs_inst_idx := 0 |>) /\
  ~(vs with <| vs_prev_bb := NONE; vs_current_bb := elbl;
               vs_inst_idx := 0 |>).vs_halted /\
  allocas_from lo
    (vs with <| vs_prev_bb := NONE; vs_current_bb := elbl; vs_inst_idx := 0 |>) /\
  LENGTH vs.vs_call_ctx.cc_calldata < dimword (:256)
Proof
  strip_tac >> drule_all initial_venom_state_calldata_length >>
  gvs[initial_venom_state_rel_def, fresh_vars_wrt_def, allocas_from_def]
QED

Theorem initial_entry_rejected_value:
  source_typing_ok tops am tx /\ initial_venom_state_rel tops am tx vs /\
  send_call_value mut
    (initial_evaluation_context am.sources am.layouts tx NONE)
    (initial_state am [env] with
      <| outcomes := SOME vs.vs_outcomes; requests := [] |>) = (INR e,st) ==>
  mut <> Payable /\ vs.vs_call_ctx.cc_callvalue <> 0w
Proof
  strip_tac >>
  `value_transfer_ok
    (initial_evaluation_context am.sources am.layouts tx NONE).txn
    (initial_state am [env] with
      <| outcomes := SOME vs.vs_outcomes; requests := [] |>).accounts` by
    gvs[initial_venom_state_rel_def, initial_evaluation_context_def, initial_state_def] >>
  drule_all send_call_value_reject_condition >>
  simp[initial_evaluation_context_def] >> strip_tac >>
  gvs[initial_venom_state_rel_def, venom_env_rel_def, call_ctx_rel_def,
      source_typing_ok_def, call_tx_well_typed_def, dimword_def, n2w_11]
QED
