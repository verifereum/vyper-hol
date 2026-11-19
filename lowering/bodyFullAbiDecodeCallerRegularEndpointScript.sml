Theory bodyFullAbiDecodeCallerRegularEndpoint
Ancestors
  bodyFullAbiDecodeCallerEndpoint bodyFullAbiDecodeCallerBlockShape
  bodyFullAbiDecodeCallerOperands exprSimAbiDecodeOblivious
  exprSimAbiEncodeObliviousLabels exprSimAbiGasBridge list

Theorem lower_abi_decode_regular_gas_free[local]:
  lower_abi_decode data di mn mx cap a = (out,b) /\
  fn_has_code a b fn /\ data <> Label a.cs_current_bb /\
  ~(a.cs_blocks <> b.cs_blocks /\ a.cs_current_bb = b.cs_current_bb) ==>
  frag_gas_free a b
Proof
  strip_tac >> drule lower_abi_decode_frag_facts >> strip_tac >>
  Cases_on `a.cs_blocks = b.cs_blocks` >- fs[] >>
  `a.cs_current_bb <> b.cs_current_bb` by fs[] >>
  drule_all_then strip_assume_tac lower_abi_decode_opened_labels_exclude_entry >>
  `~MEM a.cs_current_bb (opened_labels a b)` by
    (simp[opened_labels_def] >> IF_CASES_TAC >>
     simp[MEM_APPEND, listTheory.MAP_REVERSE]) >>
  drule_all_then assume_tac lower_abi_decode_unopened_operand >>
  gs[frag_gas_free_def, frag_ops_free_def, EVERY_MEM, boolTheory.FORALL_AND_THM]
QED

Theorem abi_decode_caller_endpoint_regular:
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
  cs_extends start final /\ fn_has_code start final func /\
  fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = start.cs_current_bb /\
  s.vs_inst_idx = LENGTH start.cs_current_insts /\
  immutable_alloca_sep func ce cx es s /\
  (!obs. fn_has_code start final obs ==> gas_path ctx obs s 0 r) /\
  ((?t. r = OK t /\ ~t.vs_halted /\
     t.vs_current_bb = final.cs_current_bb /\
     t.vs_inst_idx = LENGTH final.cs_current_insts) \/
   (?u. r = Abort Revert_abort u)) /\
  ~(start.cs_blocks <> final.cs_blocks /\ start.cs_current_bb = final.cs_current_bb) /\
  data <> Label start.cs_current_bb ==>
  (?t. r = OK t /\
    abi_decode_immutable_success ce env ty tv bs out d start final ctx func cx es s t) \/
  ((?u. r = Abort Revert_abort u) /\
   ?e. evaluate_abi_decode env ty bs = INR e)
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_all_then assume_tac lower_abi_decode_regular_gas_free >>
  mp_tac abi_decode_caller_endpoint_observed >> simp[]
QED
