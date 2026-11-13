Theory exprSimAbiDecodeRunOutcome
Ancestors
  exprSimAbiDecodeImmutableOutcome abiDecoderLoop venomExecSemantics fragExec

Theorem abi_decode_same_block_run_outcome:
  lower_abi_decode data (type_to_abi_dec_info ce.ce_struct_fields ce ty)
    (abi_static_size ce.ce_struct_fields ty) (abi_size_bound ce.ce_struct_fields ty)
    (type_memory_bytes ce ty) start = (out,final) /\
  abi_decoder_coherent ce env ce.ce_struct_fields ty tv /\
  assignable_type env ty /\ abi_decode_bytes_widths env ty /\
  abi_decoder_operand_live start.cs_next_var data /\
  start.cs_next_var <= limit_st.cs_next_var /\
  final.cs_next_var <= limit_st.cs_next_var /\
  eval_operand data s = SOME (n2w p) /\
  val_in_memory (BaseTV (BytesT (Dynamic n))) (BytesV bs) p s.vs_memory /\
  abi_builtin_decode_site_resources ctx func start final.cs_next_id
    (abi_static_size ce.ce_struct_fields ty) (abi_size_bound ce.ce_struct_fields ty)
    (type_memory_bytes ce ty) (LENGTH bs) p d s /\
  cs_extends start final /\ fn_has_code start final fn /\
  frag_gas_free start final /\ fn_inst_ids_distinct fn /\
  (!i. MEM i (fn_insts fn) /\ i.inst_opcode <> STOP /\ i.inst_opcode <> NOP ==>
       MEM i (fn_insts func)) /\
  start.cs_blocks = final.cs_blocks /\
  ~s.vs_halted /\ s.vs_current_bb = start.cs_current_bb /\
  s.vs_inst_idx = LENGTH start.cs_current_insts /\
  immutable_alloca_sep func ce cx es s ==>
  (?t. abi_decode_immutable_success ce env ty tv bs out d start final ctx func cx es s t /\
    ~t.vs_halted /\ t.vs_current_bb = final.cs_current_bb /\
    t.vs_inst_idx = LENGTH final.cs_current_insts /\ abi_decode_sim ctx fn s t) \/
  (?fuel. exit_result (run_from fuel ctx fn s) /\
    ?e u. evaluate_abi_decode env ty bs = INR e /\
      run_from fuel ctx fn s = Abort Revert_abort u)
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `(?t. abi_decode_immutable_success ce env ty tv bs out d start final ctx func cx es s t /\
      ~t.vs_halted /\ t.vs_current_bb = final.cs_current_bb /\
      t.vs_inst_idx = LENGTH final.cs_current_insts /\ abi_decode_sim ctx fn s t /\
      local_prefix ctx fn (frag_observer_cut final) s t) \/
    ((?e. evaluate_abi_decode env ty bs = INR e) /\
      ?fuel u. run_from fuel ctx fn s = Abort Revert_abort u)` by
    (irule abi_decode_original_entry_immutable_outcome >> simp[] >>
     conj_tac >- (qexists_tac `limit_st` >> simp[]) >>
     qexistsl_tac [`data`, `n`, `p`] >> simp[]) >>
  metis_tac[exit_result_def]
QED
