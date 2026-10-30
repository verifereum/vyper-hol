(* Canonical source offsets discharge the retained bounded-memory guards. *)
Theory abiDecoderCanonicalBound
Ancestors
  abiDecoderCanonicalPtr abiDecoderMemberBound abiDecoderArrayBound
  abiDecoderHeadAdequacy abiDecoderCoherence vyperABI compileEnv
  abiCanonicalHeadSize abiCanonicalHeadSize abiDecodeRanges abiDecoderContract
  contractABI valueEncoding venomExecSemantics venomState words arithmetic list

Theorem abi_decode_canonical_dynamic_member_pointer:
  compile_getelemptr_abi src T (SUM (MAP abi_member_head_size pre)) opc hi
    st = (member_op,st') /\
  has_types (pre ++ ty::post) (pvs ++ v::rest) /\
  LENGTH pre = LENGTH pvs /\ is_dynamic ty /\
  abi_decode_source_opcode opc /\ eval_operand src s = SOME (n2w sb) /\
  fresh_vars_wrt st s /\
  mem_bytes_at sb (LENGTH (enc (Tuple (pre ++ ty::post))
    (ListV (pvs ++ v::rest)))) (abi_decode_source opc s) =
      enc (Tuple (pre ++ ty::post)) (ListV (pvs ++ v::rest)) /\
  sb + LENGTH (enc (Tuple (pre ++ ty::post)) (ListV (pvs ++ v::rest))) <
    dimword (:256) ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    eval_operand member_op t = SOME (n2w (sb + head_lengths (pre ++ ty::post) 0 +
      SUM (MAP2 abi_member_tail_size pre pvs))) /\
    mem_bytes_at (sb + head_lengths (pre ++ ty::post) 0 +
      SUM (MAP2 abi_member_tail_size pre pvs)) (LENGTH (enc ty v))
      (abi_decode_source opc t) = enc ty v /\
    fresh_vars_wrt st' t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\ inst_extends st st'
Proof
  strip_tac >> drule_all canonical_member_offset_load >> strip_tac >>
  drule_all canonical_member_ranges >> asm_simp_tac bool_ss [LET_THM] >> strip_tac >>
  `sb + (head_lengths (pre ++ ty::post) 0 +
     SUM (MAP2 abi_member_tail_size pre pvs)) < dimword (:256)` by
    (asm_simp_tac arith_ss [head_lengths_acc] >> decide_tac) >>
  drule_all abi_decode_dynamic_member_pointer >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st st') s = OK t` >>
  drule_all canonical_tuple_dynamic_child_source >> strip_tac >>
  qexists_tac `t` >> gvs[abi_decode_source_def] >> simp[ADD_ASSOC]
QED

Theorem abi_decode_canonical_array_pointer_bounded:
  compile_abi_decode_dyn_elem_ptr opc elem_src src_data hi abi_sz
    st = (child_op,st') /\ hi <> Lit 0w /\
  has_type (Array NONE ty) (ListV (pre ++ v::post)) /\ is_dynamic ty /\
  abi_sz <= LENGTH (enc ty v) /\
  abi_decode_source_opcode opc /\ fresh_vars_wrt st s /\
  eval_operand elem_src s =
    SOME (n2w (sb + (32 + LENGTH pre * abi_member_head_size ty))) /\
  eval_operand src_data s = SOME (n2w (sb + 32)) /\
  eval_operand hi s = SOME (n2w hb) /\ hb < dimword (:256) /\
  sb + LENGTH (enc (Array NONE ty) (ListV (pre ++ v::post))) <= hb /\
  mem_bytes_at sb (LENGTH (enc (Array NONE ty) (ListV (pre ++ v::post))))
    (abi_decode_source opc s) = enc (Array NONE ty) (ListV (pre ++ v::post)) ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    eval_operand child_op t = SOME (n2w (sb + 32 +
      (LENGTH (pre ++ v::post) * abi_member_head_size ty +
       SUM (MAP (abi_member_tail_size ty) pre)))) /\
    mem_bytes_at (sb + (32 + LENGTH (pre ++ v::post) * abi_member_head_size ty +
      SUM (MAP (abi_member_tail_size ty) pre))) (LENGTH (enc ty v))
      (abi_decode_source opc t) = enc ty v /\
    fresh_vars_wrt st' t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\ inst_extends st st'
Proof
  strip_tac >>
  drule_all (SIMP_RULE bool_ss [LET_THM]
    (Q.INST [`bound` |-> `NONE`] canonical_array_member_ranges)) >> strip_tac >>
  `sb + LENGTH (enc (Array NONE ty) (ListV (pre ++ v::post))) < dimword (:256) /\
   sb + 32 + (LENGTH (pre ++ v::post) * abi_member_head_size ty +
     SUM (MAP (abi_member_tail_size ty) pre)) + abi_sz <= hb` by
    (gvs[Excl "enc_def"] >> decide_tac) >>
  drule_all (SIMP_RULE bool_ss []
    (Q.INST [`bound` |-> `NONE`] canonical_array_offset_load)) >> strip_tac >>
  drule_all abi_decode_bounded_array_pointer >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts st st') s = OK t` >>
  drule_all (SIMP_RULE bool_ss []
    (Q.INST [`bound` |-> `NONE`] canonical_array_dynamic_child_source)) >> strip_tac >>
  qexists_tac `t` >> gvs[abi_decode_source_def]
QED

Theorem abi_decode_typed_array_pointer_bounded:
  compile_abi_decode_dyn_elem_ptr opc elem_src src_data hi
    (abi_embedded_static_size ce.ce_struct_fields ty) st = (child_op,st') /\
  hi <> Lit 0w /\
  abi_decoder_coherent ce env sf (ArrayT ty (Dynamic maxn)) (ArrayTV tv (Dynamic maxn)) /\
  has_type (Array NONE (vyper_to_abi_type env ty)) (ListV (pre ++ av::post)) /\
  is_dynamic (vyper_to_abi_type env ty) /\
  abi_decode_source_opcode opc /\ fresh_vars_wrt st s /\
  eval_operand elem_src s = SOME (n2w (sb + (32 +
    LENGTH pre * abi_member_head_size (vyper_to_abi_type env ty)))) /\
  eval_operand src_data s = SOME (n2w (sb + 32)) /\
  eval_operand hi s = SOME (n2w hb) /\ hb < dimword (:256) /\
  sb + LENGTH (enc (Array NONE (vyper_to_abi_type env ty))
    (ListV (pre ++ av::post))) <= hb /\
  mem_bytes_at sb (LENGTH (enc (Array NONE (vyper_to_abi_type env ty))
    (ListV (pre ++ av::post)))) (abi_decode_source opc s) =
    enc (Array NONE (vyper_to_abi_type env ty)) (ListV (pre ++ av::post)) ==>
  ?t. run_inst_seq (emitted_insts st st') s = OK t /\
    eval_operand child_op t = SOME (n2w (sb + 32 +
      (LENGTH (pre ++ av::post) * abi_member_head_size (vyper_to_abi_type env ty) +
       SUM (MAP (abi_member_tail_size (vyper_to_abi_type env ty)) pre)))) /\
    mem_bytes_at (sb + (32 + LENGTH (pre ++ av::post) *
      abi_member_head_size (vyper_to_abi_type env ty) +
      SUM (MAP (abi_member_tail_size (vyper_to_abi_type env ty)) pre)))
      (LENGTH (enc (vyper_to_abi_type env ty) av)) (abi_decode_source opc t) =
      enc (vyper_to_abi_type env ty) av /\
    fresh_vars_wrt st' t /\
    (!op w. eval_operand op s = SOME w ==> eval_operand op t = SOME w) /\
    t.vs_memory = s.vs_memory /\ t.vs_call_ctx = s.vs_call_ctx /\
    t.vs_data_section = s.vs_data_section /\ inst_extends st st'
Proof
  strip_tac >>
  `has_type (vyper_to_abi_type env ty) av` by
    (drule_all canonical_array_member_type >> simp[]) >>
  `abi_embedded_static_size ce.ce_struct_fields ty <=
     LENGTH (enc (vyper_to_abi_type env ty) av)` by
    (drule_all abi_decoder_array_child_head_adequate >> simp[]) >>
  drule_all abi_decode_canonical_array_pointer_bounded >> simp[]
QED
