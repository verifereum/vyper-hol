Theory abiDecoderReentryAddress
Ancestors
  abiDecoderReentry abiDecoderAllocation abiDecoderTypedContract context compileEnv emitHelper
  emitHelperProps exprLoweringProps venomExecSemantics venomState venomInst finite_map words
  arithmetic abiDecoderContract venomExecProofs

(* Actual scratch allocation tolerates stale output variables and reused sites. *)
Theorem abi_decoder_register_update:
  t.vs_vars = s.vs_vars |+ (STRING #"%" (toString next),w) /\
  t.vs_labels = s.vs_labels /\ fresh_vars_wrt limit_st s /\
  next < limit_st.cs_next_var ==>
  fresh_vars_wrt limit_st t /\
  (!op. abi_decoder_operand_live next op ==> eval_operand op t = eval_operand op s)
Proof
  strip_tac >>
  `fresh_vars_wrt limit_st (update_var (STRING #"%" (toString next)) w s)` by
    (mp_tac (Q.SPECL [`limit_st`, `s`, `STRING #"%" (toString (next:num))`, `next`, `w`]
      fresh_vars_wrt_update_var) >> simp[]) >>
  `fresh_vars_wrt limit_st t` by fs[fresh_vars_wrt_def, update_var_def] >>
  asm_simp_tac bool_ss [] >> gen_tac >> strip_tac >> Cases_on `op` >>
  gvs[abi_decoder_operand_live_def, abi_decoder_older_vars_def,
      eval_operand_def, lookup_var_def, FLOOKUP_UPDATE] >>
  qpat_x_assum `!n. next <= n ==> _` (qspec_then `next` mp_tac) >> simp[]
QED

Theorem abi_decoder_alloca32_registers[local]:
  exec_alloca inst s (32w:bytes32) = OK t /\ inst.inst_outputs = [out] /\
  lookup_var out t = SOME w ==>
  t.vs_vars = s.vs_vars |+ (out,w) /\ t.vs_labels = s.vs_labels /\
  t.vs_halted = s.vs_halted
Proof
  rw[exec_alloca_def] >>
  gvs[AllCaseEqs(), update_var_def, lookup_var_def, FLOOKUP_UPDATE]
QED

Theorem abi_decoder_alloc_buffer_reentry:
  compile_alloc_buffer 32 st = (buf,st') /\
  abi_decoder_budget first last b cap s /\
  st.cs_next_id IN abi_decoder_ids first last /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  ?t p. run_inst_seq (emitted_insts st st') s = OK t /\
    eval_operand buf.buf_operand t = SOME (n2w p) /\ buf.buf_size = 32 /\
    abi_decoder_budget first last b cap t /\ fresh_vars_wrt limit_st t /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    b <= p /\ p + 32 <= b + cap /\
    FLOOKUP t.vs_allocas st.cs_next_id = SOME (p,32) /\
    (!id. id <> st.cs_next_id ==> FLOOKUP t.vs_allocas id = FLOOKUP s.vs_allocas id) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\ t.vs_halted = s.vs_halted
Proof
  simp_tac bool_ss [compile_alloc_buffer_def, comp_bind_def, comp_return_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  rename1 `emit_op ALLOCA [Lit 32w] st = (allocated_op,allocation_st)` >>
  drule emitted_insts_emit_op >> strip_tac >>
  qabbrev_tac `alloc_inst = mk_inst st.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString st.cs_next_var)]` >>
  `alloc_inst.inst_id IN abi_decoder_ids first last /\
   alloc_inst.inst_outputs = [STRING #"%" (toString st.cs_next_var)]` by
    simp[Abbr`alloc_inst`, mk_inst_def] >>
  drule_all abi_decoder_alloca32 >> strip_tac >>
  rename1 `exec_alloca alloc_inst s 32w = OK t` >>
  rename1 `lookup_var (STRING #"%" (toString st.cs_next_var)) t = SOME (n2w p)` >>
  drule_all abi_decoder_alloca32_registers >> strip_tac >>
  `st.cs_next_var < limit_st.cs_next_var` by decide_tac >>
  drule_all abi_decoder_register_update >> strip_tac >>
  `run_inst_seq (emitted_insts st allocation_st) s = OK t` by
    (simp[run_inst_seq_def, Once step_inst_base_def, mk_inst_def] >>
     qpat_x_assum `exec_alloca alloc_inst s 32w = OK t` mp_tac >>
     simp[Abbr`alloc_inst`, mk_inst_def]) >>
  qexistsl_tac [`t`, `p`] >>
  gvs[Abbr`alloc_inst`, mk_inst_def, eval_operand_def]
QED

(* Address-producing instructions in the emitted loop body overwrite their own
   old temporaries while preserving live outer operands and enclosing freshness. *)
Theorem abi_decoder_read_reentry:
  emit_op opc [src] st = (out,st') /\ abi_decode_source_opcode opc /\
  eval_operand src s = SOME p /\ st'.cs_next_var <= limit_st.cs_next_var /\
  fresh_vars_wrt limit_st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    eval_operand out t = SOME (abi_decode_load opc p s) /\
    fresh_vars_wrt limit_st t /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    t = update_var (STRING #"%" (toString st.cs_next_var)) (abi_decode_load opc p s) s /\
    inst_extends st st'
Proof
  strip_tac >> drule inst_extends_emit_op >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  qabbrev_tac `t = update_var (STRING #"%" (toString st.cs_next_var))
    (abi_decode_load opc p s) s` >>
  `t.vs_vars = s.vs_vars |+ (STRING #"%" (toString st.cs_next_var),abi_decode_load opc p s) /\
   t.vs_labels = s.vs_labels` by simp[Abbr`t`, update_var_def] >>
  `st.cs_next_var < limit_st.cs_next_var` by decide_tac >>
  drule_all abi_decoder_register_update >> strip_tac >>
  `step_inst_base (mk_inst st.cs_next_id opc [src]
     [STRING #"%" (toString st.cs_next_var)]) s = OK t` by
    (simp_tac bool_ss [Abbr`t`] >> irule abi_decode_read_step >> simp[]) >>
  qexists_tac `t` >>
  asm_simp_tac (srw_ss()) [run_inst_seq_def, abi_decode_read_step, Abbr`t`,
    eval_operand_def, lookup_var_update_var]
QED

Theorem abi_decoder_binary_reentry:
  emit_op opc [lhs;rhs] st = (out,st') /\ (opc = ADD \/ opc = MUL) /\
  eval_operand lhs s = SOME a /\ eval_operand rhs s = SOME b /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    eval_operand out t = SOME (if opc = ADD then a + b else a * b) /\
    fresh_vars_wrt limit_st t /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_halted = s.vs_halted /\
    t = update_var (STRING #"%" (toString st.cs_next_var))
      (if opc = ADD then a + b else a * b) s /\ inst_extends st st'
Proof
  strip_tac >> drule inst_extends_emit_op >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  qabbrev_tac `t = update_var (STRING #"%" (toString st.cs_next_var))
    (if opc = ADD then a + b else a * b) s` >>
  `t.vs_vars = s.vs_vars |+ (STRING #"%" (toString st.cs_next_var),
     if opc = ADD then a + b else a * b) /\ t.vs_labels = s.vs_labels`
    by simp[Abbr`t`, update_var_def] >>
  `st.cs_next_var < limit_st.cs_next_var` by decide_tac >>
  drule_all abi_decoder_register_update >> strip_tac >>
  `step_inst_base (mk_inst st.cs_next_id opc [lhs;rhs]
     [STRING #"%" (toString st.cs_next_var)]) s = OK t` by
    (gvs[Abbr`t`] >> FIRST [irule step_ADD, irule step_MUL] >> simp[]) >>
  qexists_tac `t` >> gvs[Abbr`t`] >>
  simp[run_inst_seq_def, eval_operand_def, lookup_var_update_var] >> simp[update_var_def]
QED
