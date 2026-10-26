(* Address-producing instructions in the emitted loop body overwrite their own
   old temporaries while preserving live outer operands and enclosing freshness. *)
Theory abiDecoderReentryAddress
Ancestors
  abiDecoderReentryAllocation abiDecoderReentry abiDecoderContract
  emitHelperProps exprLoweringProps compileEnv emitHelper
  venomExecSemantics venomExecProofs venomState venomInst words arithmetic finite_map

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

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_DECODER_REENTRY_ADDRESS_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI address re-entry not kernel closed: " ^ n)
  end) (DB.thms "abiDecoderReentryAddress");
