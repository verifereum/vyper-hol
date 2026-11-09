(* The sentinel dynamic-array child pointer and its canonical source window. *)
Theory abiDecoderArrayPtr
Ancestors
  abiDecoderRange abiDecoderBytesBound abiDecoderGuards abiDecoderContract abiCanonicalHeadSize
  abiEncoder emitHelperProps exprLoweringProps compileEnv emitHelper
  valueEncoding contractABI venomExecSemantics venomState words arithmetic list

Theorem abi_decode_array_pointer_sentinel:
  compile_abi_decode_dyn_elem_ptr opc base_op elem_src src_data (Lit 0w) abi_sz
    st = (child_op,st') /\
  abi_decode_source_opcode opc /\ eval_operand elem_src s = SOME (n2w pos) /\
  eval_operand base_op s = SOME (n2w B) /\
  eval_operand src_data s = SOME (n2w data_base) /\
  abi_decode_load opc (n2w (B + pos):bytes32) s = n2w child_off /\ fresh_vars_wrt st s ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    eval_operand child_op t = SOME (n2w (data_base + child_off)) /\
    fresh_vars_wrt st' t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\ inst_extends st st'
Proof
  simp[compile_abi_decode_dyn_elem_ptr_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  rename1 `compile_abi_dec_addr base_op elem_src st = (addr,addr_st)` >>
  drule_all compile_abi_dec_addr_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st addr_st) s = OK sa` >>
  `abi_decode_load opc (n2w (B + pos):bytes32) sa = n2w child_off` by
    gvs[abi_decode_load_def, abi_decode_source_def, mload_def] >>
  drule_all abi_decode_read >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts addr_st c1) sa = OK s1` >>
  `eval_operand off_val s1 = SOME (n2w child_off)` by fs[] >>
  `eval_operand src_data s1 = SOME (n2w data_base)` by metis_tac[] >>
  drule_all abi_decode_add_sequence >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts c1 st') s1 = OK t` >>
  `inst_extends addr_st c1 /\ inst_extends c1 st'` by
    metis_tac[inst_extends_emit_op] >>
  `inst_extends st addr_st` by
    (Cases_on `base_op = Lit 0w` >>
     gvs[compile_abi_dec_addr_def, comp_return_def, inst_extends_refl] >>
     metis_tac[inst_extends_emit_op]) >>
  `run_inst_seq (emitted_insts addr_st st') sa = OK t /\ inst_extends addr_st st'` by
    (irule abi_decode_sequence_chain >> qexistsl_tac [`s1`, `c1`] >> simp[]) >>
  drule_all abi_decode_sequence_chain >> strip_tac >>
  qexists_tac `t` >> gvs[word_add_n2w] >> metis_tac[]
QED

Theorem abi_decode_canonical_array_pointer:
  compile_abi_decode_dyn_elem_ptr opc base_op elem_src src_data (Lit 0w) abi_sz
    st = (child_op,st') /\
  has_type (Array NONE ty) (ListV (pre ++ v::post)) /\ is_dynamic ty /\
  abi_decode_source_opcode opc /\ fresh_vars_wrt st s /\
  eval_operand base_op s = SOME (n2w B) /\
  eval_operand elem_src s =
    SOME (n2w (sb + (32 + LENGTH pre * abi_member_head_size ty))) /\
  eval_operand src_data s = SOME (n2w (sb + 32)) /\
  mem_bytes_at (B + sb) (LENGTH (enc (Array NONE ty) (ListV (pre ++ v::post))))
    (abi_decode_source opc s) = enc (Array NONE ty) (ListV (pre ++ v::post)) /\
  B + sb + LENGTH (enc (Array NONE ty) (ListV (pre ++ v::post))) < dimword (:256) ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    eval_operand child_op t = SOME (n2w (sb + 32 +
      (LENGTH (pre ++ v::post) * abi_member_head_size ty +
       SUM (MAP (abi_member_tail_size ty) pre)))) /\
    mem_bytes_at (B + sb + (32 + LENGTH (pre ++ v::post) * abi_member_head_size ty +
      SUM (MAP (abi_member_tail_size ty) pre))) (LENGTH (enc ty v))
      (abi_decode_source opc t) = enc ty v /\
    fresh_vars_wrt st' t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\ inst_extends st st'
Proof
  strip_tac >>
  drule_all (SIMP_RULE bool_ss []
    (Q.INST [`bound` |-> `NONE`] canonical_array_offset_load)) >> strip_tac >>
  rule_assum_tac (PURE_REWRITE_RULE [GSYM ADD_ASSOC]) >>
  drule_all abi_decode_array_pointer_sentinel >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st st') s = OK t` >>
  drule_all (SIMP_RULE bool_ss []
    (Q.INST [`bound` |-> `NONE`] canonical_array_dynamic_child_source)) >> strip_tac >>
  qexists_tac `t` >> gvs[abi_decode_source_def]
QED
