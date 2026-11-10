(* Straight-line execution on arbitrary runtime variable maps. *)
Theory abiEncoderWindowSequence
Ancestors
  abiEncoderWindowLeaves abiEncoderSequence abiEncoderExtendSim
  emitHelperProps moduleLoweringProps freshWrites exprLoweringProps
  compileEnv loweringStateRelDefs emitHelper fragExec venomInstProps
  venomState venomExecSemantics venomInst words list arithmetic
  abiEncoderWindowLookup

Definition window_seq_def:
  window_seq st st' s t <=>
    run_inst_seq (emitted_insts st st') s = OK t /\
    inst_extends st st' /\ st.cs_next_var <= st'.cs_next_var /\
    st'.cs_blocks = st.cs_blocks /\
    st'.cs_current_bb = st.cs_current_bb /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts st st') /\
    (!x. not_fresh_at st x ==> lookup_var x t = lookup_var x s)
End

Definition window_pure_seq_def:
  window_pure_seq st st' s t <=>
    window_seq st st' s t /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_call_ctx = s.vs_call_ctx /\ t.vs_data_section = s.vs_data_section /\
    t.vs_halted = s.vs_halted /\ t.vs_current_bb = s.vs_current_bb /\
    t.vs_inst_idx = s.vs_inst_idx /\
    t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
    t.vs_logs = s.vs_logs /\ t.vs_requests = s.vs_requests /\
    t.vs_pending_deletions = s.vs_pending_deletions
End

Theorem window_pure_seq_registered_effect:
  window_pure_seq st st' s t ==> abi_encoder_registered_effect ids outs s t
Proof
  simp[window_pure_seq_def, abiEncoderRegisteredEffectTheory.abi_encoder_registered_effect_def]
QED

Theorem window_seq_mono:
  window_seq st st' s t ==> st.cs_next_var <= st'.cs_next_var
Proof
  simp[window_seq_def, inst_extends_def]
QED

Theorem window_seq_labels:
  window_seq st st' s t ==> t.vs_labels = s.vs_labels
Proof
  simp_tac bool_ss [window_seq_def] >> strip_tac >>
  drule_at (Pos hd)
    (Q.ISPEC `\s:venom_state. s.vs_labels` run_inst_seq_preserves_field) >>
  simp[] >> disch_then irule >> rpt strip_tac >> fs[EVERY_MEM] >>
  metis_tac[step_preserves_labels, step_inst_non_invoke]
QED

Theorem window_seq_eval:
  window_seq st st' s t /\ (!x. op = Var x ==> not_fresh_at st x) /\
  eval_operand op s = SOME w ==> eval_operand op t = SOME w
Proof
  strip_tac >> drule window_seq_labels >> strip_tac >>
  Cases_on `op` >> fs[window_seq_def, eval_operand_def]
QED

Theorem window_seq_chain:
  window_seq st mid s t /\ window_seq mid fin t u ==>
  window_seq st fin s u
Proof
  strip_tac >>
  `st.cs_next_var <= mid.cs_next_var` by metis_tac[window_seq_mono] >>
  fs[window_seq_def] >>
  `emitted_insts st fin = emitted_insts st mid ++ emitted_insts mid fin` by
    metis_tac[emitted_insts_append, inst_extends_def] >>
  simp[window_seq_def] >> rpt conj_tac
  >- metis_tac[run_inst_seq_append]
  >- metis_tac[inst_extends_trans] >>
  metis_tac[not_fresh_at_mono]
QED

Theorem window_pure_seq_chain:
  window_pure_seq st mid s t /\ window_pure_seq mid fin t u ==>
  window_pure_seq st fin s u
Proof
  simp_tac bool_ss [window_pure_seq_def] >> strip_tac >>
  metis_tac[window_seq_chain]
QED

Theorem window_seq_extend_sim:
  window_seq st st' s t /\ fn_has_code st st' func /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  abi_encoder_extend_sim ctx func s (t with vs_inst_idx := LENGTH st'.cs_current_insts)
Proof
  simp_tac bool_ss [window_seq_def] >> strip_tac >>
  irule abi_encoder_run_sequence_extend_sim >>
  (conj_tac >- first_assum ACCEPT_TAC) >> qexists_tac `st` >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Theorem window_emit_register_pure:
  emit_op opc args st = (out,st') /\
  opc <> INVOKE /\ ~is_terminator opc /\
  run_inst_seq (emitted_insts st st') s =
    OK (update_var (STRING #"%" (toString st.cs_next_var)) w s) ==>
  window_pure_seq st st' s
    (update_var (STRING #"%" (toString st.cs_next_var)) w s) /\
  eval_operand out (update_var (STRING #"%" (toString st.cs_next_var)) w s) = SOME w /\
  (!x. out = Var x ==> not_fresh_at st' x)
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  drule inst_extends_emit_op >> strip_tac >>
  `st'.cs_blocks = st.cs_blocks /\ st'.cs_current_bb = st.cs_current_bb` by
    (gvs[emit_op_def, fresh_var_def, fresh_id_def, emit_def,
      comp_bind_def, comp_ignore_bind_def, comp_return_def]) >>
  simp[window_pure_seq_def, window_seq_def, mk_inst_def,
    update_var_def, eval_operand_def, lookup_var_def,
    finite_mapTheory.FLOOKUP_UPDATE, not_fresh_at_def] >>
  metis_tac[LESS_EQ_REFL, LESS_EQ_LESS_TRANS, LESS_EQ_TRANS, LESS_EQ_ANTISYM]
QED

Theorem window_emit_load_pure:
  emit_op MLOAD [ptr_op] st = (out,st') /\
  eval_operand ptr_op s = SOME (n2w p) /\ p < dimword (:256) ==>
  ?t. window_pure_seq st st' s t /\ eval_operand out t = SOME (mload p s) /\
    (!x. out = Var x ==> not_fresh_at st' x)
Proof
  strip_tac >> drule_all window_emit_load_run >> strip_tac >>
  `MLOAD <> INVOKE /\ ~is_terminator MLOAD` by simp[is_terminator_def] >>
  metis_tac[window_emit_register_pure]
QED

Theorem window_emit_add_pure:
  emit_op ADD [lhs;rhs] st = (out,st') /\
  eval_operand lhs s = SOME a /\ eval_operand rhs s = SOME b ==>
  ?t. window_pure_seq st st' s t /\ eval_operand out t = SOME (a+b) /\
    (!x. out = Var x ==> not_fresh_at st' x)
Proof
  strip_tac >>
  `run_inst_seq (emitted_insts st st') s =
    OK (update_var (STRING #"%" (toString st.cs_next_var)) (a+b) s)` by
    (drule emitted_insts_emit_op >> strip_tac >>
     simp[run_inst_seq_def, Once step_inst_base_def, mk_inst_def,
       exec_pure2_def, eval_operands_def]) >>
  qexists_tac `update_var (STRING #"%" (toString st.cs_next_var)) (a+b) s` >>
  irule window_emit_register_pure >> (conj_tac >- first_assum ACCEPT_TAC) >>
  qexistsl_tac [`[lhs;rhs]`, `ADD`] >> simp[is_terminator_def]
QED

Theorem window_emit_and_pure:
  emit_op AND [lhs;rhs] st = (out,st') /\
  eval_operand lhs s = SOME a /\ eval_operand rhs s = SOME b ==>
  ?t. window_pure_seq st st' s t /\ eval_operand out t = SOME (a && b) /\
    (!x. out = Var x ==> not_fresh_at st' x)
Proof
  strip_tac >>
  `run_inst_seq (emitted_insts st st') s =
    OK (update_var (STRING #"%" (toString st.cs_next_var)) (a && b) s)` by
    (drule emitted_insts_emit_op >> strip_tac >>
     simp[run_inst_seq_def, Once step_inst_base_def, mk_inst_def,
       exec_pure2_def, eval_operands_def]) >>
  qexists_tac `update_var (STRING #"%" (toString st.cs_next_var)) (a && b) s` >>
  irule window_emit_register_pure >> (conj_tac >- first_assum ACCEPT_TAC) >>
  qexistsl_tac [`[lhs;rhs]`, `AND`] >> simp[is_terminator_def]
QED

Theorem abi_window_emit_register_fresh:
  emit_op opc args st = (out,en) /\ opc <> INVOKE /\
  ~is_terminator opc /\
  run_inst_seq (emitted_insts st en) s =
    OK (update_var (STRING #"%" (toString st.cs_next_var)) w s) /\
  en.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  window_pure_seq st en s
    (update_var (STRING #"%" (toString st.cs_next_var)) w s) /\
  fresh_vars_wrt limit_st
    ((update_var (STRING #"%" (toString st.cs_next_var)) w s)
       with vs_inst_idx := idx)
Proof
  strip_tac >> conj_tac
  >- metis_tac[window_emit_register_pure] >>
  drule_all abi_window_emit_register_bounds >> strip_tac >>
  irule abi_window_seq_fresh_idx >>
  qexistsl_tac [`en`, `emitted_insts st en`, `s`] >> simp[]
QED
