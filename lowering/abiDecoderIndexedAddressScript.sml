(* The three instructions used for both array payload addresses in the loop. *)
Theory abiDecoderIndexedAddress
Ancestors
  abiDecoderReentryAddress abiDecoderReentry abiDecoderGuards abiDecoderContract
  emitHelperProps exprLoweringProps compileEnv emitHelper
  venomExecSemantics venomState words arithmetic

Definition abi_decode_indexed_address_def:
  abi_decode_indexed_address base_op idx stride =
    do data_op <- emit_op ADD [base_op; Lit 32w];
       offset_op <- emit_op MUL [idx; Lit (n2w stride)];
       emit_op ADD [data_op; offset_op]
    od
End

Theorem abi_decode_indexed_address_counters:
  abi_decode_indexed_address base_op idx stride st = (address_op,st') ==>
  st'.cs_next_var = st.cs_next_var + 3 /\
  abi_decoder_operand_live st'.cs_next_var address_op
Proof
  simp[abi_decode_indexed_address_def, comp_bind_def] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  imp_res_tac emitted_insts_emit_op >>
  imp_res_tac abi_decoder_operand_live_emit >> conj_tac >- decide_tac >> first_assum ACCEPT_TAC
QED

Theorem abi_decode_indexed_address_reentry:
  abi_decode_indexed_address base_op idx stride st = (address_op,st') /\
  eval_operand base_op s = SOME (n2w sb) /\ eval_operand idx s = SOME (n2w i) /\
  abi_decoder_operand_live st.cs_next_var idx /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    eval_operand address_op t = SOME (n2w (sb + 32 + i * stride)) /\
    fresh_vars_wrt limit_st t /\ abi_decoder_operand_live st'.cs_next_var address_op /\
    (!op. abi_decoder_operand_live st.cs_next_var op ==>
      eval_operand op t = eval_operand op s) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\
    t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
    t.vs_halted = s.vs_halted /\ inst_extends st st' /\
    st'.cs_next_var = st.cs_next_var + 3
Proof
  simp[abi_decode_indexed_address_def, comp_bind_def] >>
  pairarg_tac >> strip_tac >> gvs[] >> pairarg_tac >> gvs[] >>
  rename1 `emit_op ADD [base_op; Lit 32w] st = (data_op,c1)` >>
  rename1 `emit_op MUL [idx; Lit (n2w stride)] c1 = (offset_op,c2)` >>
  imp_res_tac emitted_insts_emit_op >>
  imp_res_tac abi_decoder_operand_live_emit >>
  `c1.cs_next_var <= limit_st.cs_next_var /\ c2.cs_next_var <= limit_st.cs_next_var`
    by decide_tac >>
  `eval_operand (Lit 32w) s = SOME 32w` by simp[eval_operand_def] >>
  drule_all (SIMP_RULE (srw_ss()) []
    (Q.INST [`opc` |-> `ADD`] abi_decoder_binary_reentry)) >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st c1) s = OK s1` >>
  `eval_operand idx s1 = SOME (n2w i)` by metis_tac[] >>
  `eval_operand (Lit (n2w stride)) s1 = SOME (n2w stride)` by simp[eval_operand_def] >>
  drule_all (SIMP_RULE (srw_ss()) []
    (Q.INST [`opc` |-> `MUL`] abi_decoder_binary_reentry)) >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 c2) s1 = OK s2` >>
  `abi_decoder_operand_live c1.cs_next_var data_op` by
    first_assum ACCEPT_TAC >>
  `eval_operand data_op s2 = SOME ((n2w sb : bytes32) + 32w)` by metis_tac[] >>
  drule_all (SIMP_RULE (srw_ss()) []
    (Q.INST [`opc` |-> `ADD`] abi_decoder_binary_reentry)) >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c2 st') s2 = OK t` >>
  `run_inst_seq (emitted_insts st c2) s = OK s2 /\ inst_extends st c2` by
    (irule abi_decode_sequence_chain >> qexistsl_tac [`s1`, `c1`] >> simp[]) >>
  `run_inst_seq (emitted_insts st st') s = OK t /\ inst_extends st st'` by
    (irule abi_decode_sequence_chain >> qexistsl_tac [`s2`, `c2`] >> simp[]) >>
  `abi_decoder_operand_live st'.cs_next_var address_op` by
    first_assum ACCEPT_TAC >>
  `!op. abi_decoder_operand_live st.cs_next_var op ==>
    eval_operand op t = eval_operand op s` by
    (rpt strip_tac >>
     `abi_decoder_operand_live c1.cs_next_var op /\
      abi_decoder_operand_live c2.cs_next_var op` by
       (conj_tac >> irule abi_decoder_operand_live_mono >>
        qexists_tac `st.cs_next_var` >> simp[]) >> metis_tac[]) >>
  qexists_tac `t` >> gvs[word_add_n2w, word_mul_n2w, update_var_def]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_DECODER_INDEXED_ADDRESS_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI indexed address not kernel closed: " ^ n)
  end) (DB.thms "abiDecoderIndexedAddress");
