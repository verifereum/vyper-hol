(* The source return adapter for the held allocation-backed decoder. *)
Theory extcallReturnDecodeSummary
Ancestors
  extcallReturnEntryBridge abiReturnSuccessSource abiValidAllocatedSuccess
  abiValidAllocatedContract abiValidAllocatedMembers vyperABIValid vyperABI
  abiDecoderCoherence abiMalformedRecursiveInterface compileEnv venomState
  list rich_list arithmetic

Theorem return_capped_allocated_success:
  rt = (if needs_external_call_wrap ty then TupleT [ty] else ty) /\
  rv = (if needs_external_call_wrap ty then ArrayV (TupleV [v]) else v) /\
  cap = vyper_abi_size_bound env rt /\
  evaluate_abi_decode_return env ty bs = INL v /\
  abi_decoder_coherent ce env sf rt tv /\
  compile_abi_decode_to_buf dst (Lit 0w) MLOAD base_op hi
    (type_to_abi_dec_info sf ce rt) st = ((),en) /\
  fn_has_code st en func /\ fn_inst_ids_distinct func /\
  abi_malformed_entry ctx func cenv cx es st
    (abi_malformed_scratch_sites st en func) dstid live base_op hi
    (Lit 0w) dst B (LENGTH (TAKE cap bs)) (TAKE cap bs) 0 d
    (type_memory_bytes ce rt) s /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?ceiling t. abi_valid_allocated_post tv rv ctx func cenv cx es st en
    ceiling dstid d (type_memory_bytes ce rt) s t
Proof
  strip_tac >>
  `evaluate_abi_decode env rt (TAKE cap bs) = INL rv` by
    (irule abi_return_source_capped_success >> goal_assum (drule_at Any) >>
     simp[] >> goal_assum (drule_at Any) >> simp[]) >>
  `vyper_valid_enc env rt (TAKE cap bs)` by
    metis_tac[evaluate_abi_decode_vyper_valid_enc] >>
  `is_dynamic (vyper_to_abi_type env rt) \/
   static_length (vyper_to_abi_type env rt) <= LENGTH (TAKE cap bs)` by
    metis_tac[vyper_valid_enc_static_length_lower] >>
  qspecl_then [`s`, `en`] strip_assume_tac return_decoder_ceiling_exists >>
  qexists_tac `ceiling` >>
  irule (SRULE [abi_valid_allocated_type_contract_def] abi_valid_allocated_success) >>
  simp_tac bool_ss [abi_valid_allocated_entry_def] >>
  qexistsl_tac [`B`, `LENGTH (TAKE cap bs)`, `base_op`, `dst`, `env`,
    `hi`, `live`, `0`, `sf`, `Lit 0w`, `TAKE cap bs`] >>
  fs[vyper_valid_enc_def, evaluate_abi_decode_def, decode_abi_value_def,
     AllCaseEqs(), Excl "dec_def", Excl "enc_def",
     Excl "vyper_decode_valid_enc_def"] >> gvs[]
QED
