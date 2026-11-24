Theory exprSimAbiEncodeObliviousFacts
Ancestors
  exprSimAbiEncodeObliviousCode exprSimAbiEncodeObliviousLabels
  exprSimAbiEncodeObliviousContext exprSimAbiGasBridge
  abiEncoder builtinAbi compileEnv emitHelper context venomInst list fragExec

Definition enc_safe_opcode_def:
  enc_safe_opcode opc <=> opc <> GAS /\ opc <> INVOKE /\ opc <> PHI /\
                          opc <> STOP /\ opc <> RETURN
End

(* All opcodes emitted by an encoder reading and writing memory. *)
Definition encode_window_opcode_def:
  encode_window_opcode opc <=>
    MEM opc [MLOAD; MSTORE; MCOPY; ADD; AND; NOT; ALLOCA;
             JMP; JNZ; LT; ISZERO; MUL]
End

Theorem encode_window_code_action_static:
  !dst src. code_action encode_window_opcode (compile_abi_encode_static dst src)
Proof
  simp[compile_abi_encode_static_def, code_action_bind, code_action_ignore_bind,
       code_action_emit_op, code_action_emit_void, code_action_return,
       encode_window_opcode_def]
QED

Theorem encode_window_code_action_static_info:
  !dst src ei.
    code_action encode_window_opcode (compile_abi_encode_static_info dst src ei)
Proof
  Cases_on `ei` >> simp[compile_abi_encode_static_info_def,
    encode_window_code_action_static, code_action_return, code_action_ignore_bind,
    code_action_emit_void, encode_window_opcode_def]
QED

Theorem encode_window_code_action_static_loop:
  !dst src ei asz msz len.
    code_action encode_window_opcode
      (compile_abi_encode_dyn_static_loop dst src ei asz msz len)
Proof
  rpt gen_tac >> rewrite_tac[compile_abi_encode_dyn_static_loop_def]
  >> irule code_action_bind >> simp[code_action_alloc_buffer, encode_window_opcode_def]
  >> gen_tac >> simp[]
  >> irule code_action_ignore_bind >> simp[code_action_emit_void, encode_window_opcode_def]
  >> irule code_action_bind >> simp[code_action_fresh_label] >> gen_tac
  >> irule code_action_bind >> simp[code_action_fresh_label] >> gen_tac
  >> irule code_action_bind >> simp[code_action_fresh_label] >> gen_tac
  >> irule code_action_ignore_bind >> simp[code_action_emit_inst, encode_window_opcode_def]
  >> irule code_action_ignore_bind >> simp[code_action_new_block]
  >> irule code_action_bind >> simp[code_action_emit_op, encode_window_opcode_def] >> gen_tac
  >> irule code_action_bind >> simp[code_action_emit_op, encode_window_opcode_def] >> gen_tac
  >> irule code_action_bind >> simp[code_action_emit_op, encode_window_opcode_def] >> gen_tac
  >> irule code_action_ignore_bind >> simp[code_action_emit_inst, encode_window_opcode_def]
  >> irule code_action_ignore_bind >> simp[code_action_new_block]
  >> irule code_action_bind >> simp[code_action_emit_op, encode_window_opcode_def] >> gen_tac
  >> irule code_action_bind >> simp[code_action_emit_op, encode_window_opcode_def] >> gen_tac
  >> irule code_action_bind >> simp[code_action_emit_op, encode_window_opcode_def] >> gen_tac
  >> irule code_action_bind >> simp[code_action_emit_op, encode_window_opcode_def] >> gen_tac
  >> irule code_action_bind >> simp[code_action_emit_op, encode_window_opcode_def] >> gen_tac
  >> irule code_action_bind >> simp[code_action_emit_op, encode_window_opcode_def] >> gen_tac
  >> irule code_action_bind >> simp[code_action_emit_op, encode_window_opcode_def] >> gen_tac
  >> irule code_action_ignore_bind >> simp[encode_window_code_action_static_info]
  >> irule code_action_bind >> simp[code_action_emit_op, encode_window_opcode_def] >> gen_tac
  >> irule code_action_ignore_bind >> simp[code_action_emit_void, encode_window_opcode_def]
  >> irule code_action_ignore_bind >> simp[code_action_emit_inst, encode_window_opcode_def]
  >> irule code_action_ignore_bind >> simp[code_action_new_block]
  >> simp[code_action_bind, code_action_emit_op, encode_window_opcode_def]
QED

Theorem encode_window_code_action_dyn_loop_step:
  !ei. (!dst src. code_action encode_window_opcode (compile_abi_encode_to_buf dst src ei)) ==>
  !dst src asz msz len.
    code_action encode_window_opcode (compile_abi_encode_dyn_loop dst src ei asz msz len)
Proof
  rpt strip_tac >> once_rewrite_tac[compile_abi_encode_child_def]
  >> irule code_action_bind >> simp[code_action_alloc_buffer, encode_window_opcode_def]
  >> gen_tac >> simp[]
  >> irule code_action_ignore_bind >> simp[code_action_emit_void, encode_window_opcode_def]
  >> irule code_action_bind >> simp[code_action_alloc_buffer, encode_window_opcode_def]
  >> gen_tac >> simp[]
  >> irule code_action_bind >> simp[code_action_emit_op, encode_window_opcode_def] >> gen_tac
  >> irule code_action_ignore_bind >> simp[code_action_emit_void, encode_window_opcode_def]
  >> irule code_action_bind >> simp[code_action_fresh_label] >> gen_tac
  >> irule code_action_bind >> simp[code_action_fresh_label] >> gen_tac
  >> irule code_action_bind >> simp[code_action_fresh_label] >> gen_tac
  >> irule code_action_ignore_bind >> simp[code_action_emit_inst, encode_window_opcode_def]
  >> irule code_action_ignore_bind >> simp[code_action_new_block]
  >> irule code_action_bind >> simp[code_action_emit_op, encode_window_opcode_def] >> gen_tac
  >> irule code_action_bind >> simp[code_action_emit_op, encode_window_opcode_def] >> gen_tac
  >> irule code_action_bind >> simp[code_action_emit_op, encode_window_opcode_def] >> gen_tac
  >> irule code_action_ignore_bind >> simp[code_action_emit_inst, encode_window_opcode_def]
  >> irule code_action_ignore_bind >> simp[code_action_new_block]
  >> irule code_action_bind >> simp[code_action_emit_op, encode_window_opcode_def] >> gen_tac
  >> irule code_action_bind >> simp[code_action_emit_op, encode_window_opcode_def] >> gen_tac
  >> irule code_action_bind >> simp[code_action_emit_op, encode_window_opcode_def] >> gen_tac
  >> irule code_action_bind >> simp[code_action_emit_op, encode_window_opcode_def] >> gen_tac
  >> irule code_action_bind >> simp[code_action_emit_op, encode_window_opcode_def] >> gen_tac
  >> irule code_action_bind >> simp[code_action_emit_op, encode_window_opcode_def] >> gen_tac
  >> irule code_action_bind >> simp[code_action_emit_op, encode_window_opcode_def] >> gen_tac
  >> irule code_action_bind >> simp[code_action_emit_op, encode_window_opcode_def] >> gen_tac
  >> irule code_action_bind >> simp[code_action_emit_op, encode_window_opcode_def] >> gen_tac
  >> irule code_action_bind >> simp[] >> gen_tac
  >> irule code_action_ignore_bind >> simp[code_action_emit_void, encode_window_opcode_def]
  >> irule code_action_bind >> simp[code_action_emit_op, encode_window_opcode_def] >> gen_tac
  >> irule code_action_ignore_bind >> simp[code_action_emit_void, encode_window_opcode_def]
  >> irule code_action_bind >> simp[code_action_emit_op, encode_window_opcode_def] >> gen_tac
  >> irule code_action_ignore_bind >> simp[code_action_emit_void, encode_window_opcode_def]
  >> irule code_action_ignore_bind >> simp[code_action_emit_inst, encode_window_opcode_def]
  >> irule code_action_ignore_bind >> simp[code_action_new_block]
  >> simp[code_action_bind, code_action_ignore_bind, code_action_emit_op,
          code_action_emit_void, encode_window_opcode_def]
QED

Theorem encode_window_code_action_mutual:
  (!dst ptr ei dyn so dp.
    code_action encode_window_opcode (compile_abi_encode_child dst ptr ei dyn so dp)) /\
  (!dst src ei.
    code_action encode_window_opcode (compile_abi_encode_to_buf dst src ei)) /\
  (!dst src infos so ho ptr.
    code_action encode_window_opcode (compile_abi_encode_complex_elems dst src infos so ho ptr)) /\
  (!dst src ei asz msz len.
    code_action encode_window_opcode (compile_abi_encode_dyn_loop dst src ei asz msz len))
Proof
  ho_match_mp_tac compile_abi_encode_child_ind >> rpt conj_tac >> rpt gen_tac
  >> rpt (disch_then strip_assume_tac)
  >> RULE_ASSUM_TAC (SIMP_RULE (srw_ss()) [])
  >~ [`code_action _ (compile_abi_encode_dyn_loop dst src ei asz msz len)`]
  >- (irule encode_window_code_action_dyn_loop_step >> simp[])
  >> once_rewrite_tac[compile_abi_encode_child_def]
  >> simp_tac pure_ss [LET_THM] >> BETA_TAC
  >- (Cases_on `dyn` >> gvs[]
      >> irule code_action_bind >> simp[code_action_emit_op, encode_window_opcode_def] >> gen_tac
      >> simp[code_action_bind, code_action_ignore_bind,
              code_action_emit_op, code_action_emit_void, code_action_return,
              encode_window_opcode_def]
      >> irule code_action_bind >> simp[code_action_emit_op, encode_window_opcode_def] >> gen_tac
      >> irule code_action_bind >> simp[code_action_emit_op, encode_window_opcode_def] >> gen_tac
      >> irule code_action_bind >> simp[] >> gen_tac
      >> simp[code_action_bind, code_action_ignore_bind,
              code_action_emit_op, code_action_emit_void, code_action_return,
              encode_window_opcode_def])
  >- simp[encode_window_code_action_static]
  >- (irule code_action_bind >> simp[code_action_emit_op, encode_window_opcode_def] >> gen_tac
      >> irule code_action_bind >> simp[code_action_emit_op, encode_window_opcode_def] >> gen_tac
      >> irule code_action_bind >> simp[code_action_emit_op, encode_window_opcode_def] >> gen_tac
      >> irule code_action_bind >> simp[code_action_emit_op, encode_window_opcode_def] >> gen_tac
      >> irule code_action_ignore_bind >> simp[code_action_emit_void, encode_window_opcode_def]
      >> irule code_action_bind >> simp[code_action_emit_op, encode_window_opcode_def] >> gen_tac
      >> irule code_action_ignore_bind >> simp[code_action_emit_void, encode_window_opcode_def]
      >> irule code_action_bind >> simp[code_action_emit_op, encode_window_opcode_def] >> gen_tac
      >> irule code_action_bind >> simp[code_action_emit_op, encode_window_opcode_def] >> gen_tac
      >> irule code_action_bind >> simp[code_action_emit_op, encode_window_opcode_def] >> gen_tac
      >> simp[code_action_emit_op, encode_window_opcode_def])
  >- simp[code_action_ignore_bind, code_action_emit_void, code_action_return,
          encode_window_opcode_def]
  >- (Cases_on `elem_is_dyn` >> gvs[]
      >> irule code_action_bind >> simp[code_action_alloc_buffer, encode_window_opcode_def] >> gen_tac
      >> simp[] >> irule code_action_ignore_bind >> simp[code_action_emit_void, encode_window_opcode_def]
      >> irule code_action_bind >> simp[code_action_emit_op, encode_window_opcode_def] >> gen_tac
      >> irule code_action_ignore_bind >> simp[code_action_emit_void, encode_window_opcode_def]
      >> irule code_action_bind >> simp[encode_window_code_action_static_loop] >> gen_tac
      >> simp[code_action_bind, code_action_ignore_bind,
              code_action_emit_void, code_action_emit_op, encode_window_opcode_def])
  >- simp[code_action_return]
  >- (IF_CASES_TAC >> gvs[] >> simp[code_action_bind, code_action_ignore_bind,
        code_action_alloc_buffer, code_action_emit_void, code_action_emit_op,
        code_action_return, encode_window_opcode_def])
  >- simp[code_action_return]
  >> simp[code_action_bind, code_action_ignore_bind, code_action_emit_op,
          encode_window_opcode_def]
QED

Theorem encode_window_action_safe[local]:
  !m. code_action encode_window_opcode m ==> code_action enc_safe_opcode m
Proof
  simp[code_action_def, code_step_def, EVERY_MEM] >> rpt strip_tac >>
  res_tac >> fs[encode_window_opcode_def, enc_safe_opcode_def]
QED

Theorem code_action_static:
  !dst src. code_action enc_safe_opcode (compile_abi_encode_static dst src)
Proof
  metis_tac[encode_window_action_safe, encode_window_code_action_static]
QED

Theorem code_action_static_info:
  !dst src ei.
    code_action enc_safe_opcode (compile_abi_encode_static_info dst src ei)
Proof
  metis_tac[encode_window_action_safe, encode_window_code_action_static_info]
QED

Theorem code_action_static_loop:
  !dst src ei asz msz len.
    code_action enc_safe_opcode
      (compile_abi_encode_dyn_static_loop dst src ei asz msz len)
Proof
  metis_tac[encode_window_action_safe, encode_window_code_action_static_loop]
QED

Theorem code_action_dyn_loop_step:
  !ei. (!dst src. code_action enc_safe_opcode (compile_abi_encode_to_buf dst src ei)) ==>
  !dst src asz msz len.
    code_action enc_safe_opcode (compile_abi_encode_dyn_loop dst src ei asz msz len)
Proof
  metis_tac[encode_window_action_safe, cj 4 encode_window_code_action_mutual]
QED

Theorem code_action_encoder_mutual:
  (!dst ptr ei dyn so dp.
    code_action enc_safe_opcode (compile_abi_encode_child dst ptr ei dyn so dp)) /\
  (!dst src ei.
    code_action enc_safe_opcode (compile_abi_encode_to_buf dst src ei)) /\
  (!dst src infos so ho ptr.
    code_action enc_safe_opcode (compile_abi_encode_complex_elems dst src infos so ho ptr)) /\
  (!dst src ei asz msz len.
    code_action enc_safe_opcode (compile_abi_encode_dyn_loop dst src ei asz msz len))
Proof
  rpt strip_tac >> irule encode_window_action_safe >>
  simp[encode_window_code_action_mutual]
QED

Theorem code_action_lower_abi_encode:
  !mid src info maxlen.
    code_action enc_safe_opcode (lower_abi_encode mid maxlen (\dst. compile_abi_encode_to_buf dst src info))
Proof
  rpt gen_tac >> Cases_on `mid` >> simp[lower_abi_encode_def, comp_ignore_bind_def] >>
  rpt (FIRST [
    CHANGED_TAC (simp[code_action_return, code_action_alloc_buffer,
      code_action_emit_op, code_action_emit_void, cj 2 code_action_encoder_mutual,
      enc_safe_opcode_def]),
    irule code_action_bind, conj_tac, gen_tac])
QED

Theorem label_action_linear:
  (!opc ops. label_action (emit_op opc ops)) /\
  (!opc ops. label_action (emit_void opc ops)) /\
  (!opc ops outs. label_action (emit_inst opc ops outs)) /\
  (!n. label_action (compile_alloc_buffer n))
Proof
  simp[label_action_def, label_step_def, entry_shape_def,
       opened_labels_def, emitted_blocks_def,
       emit_op_def, emit_void_def, emit_inst_def, compile_alloc_buffer_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_var_def,
       fresh_id_def, emit_def]
  >> rpt strip_tac >> metis_tac[APPEND_ASSOC]
QED

Theorem label_action_static:
  !dst src. label_action (compile_abi_encode_static dst src)
Proof
  simp[compile_abi_encode_static_def, label_action_bind, label_action_ignore_bind,
       label_action_linear, label_action_return]
QED

Theorem label_action_encoder_mutual:
  (!dst ptr ei dyn so dp.
    label_action (compile_abi_encode_child dst ptr ei dyn so dp)) /\
  (!dst src ei.
    label_action (compile_abi_encode_to_buf dst src ei)) /\
  (!dst src infos so ho ptr.
    label_action (compile_abi_encode_complex_elems dst src infos so ho ptr)) /\
  (!dst src ei asz msz len.
    label_action (compile_abi_encode_dyn_loop dst src ei asz msz len))
Proof
  ho_match_mp_tac compile_abi_encode_child_ind >> rpt conj_tac >> rpt gen_tac
  >> rpt (disch_then strip_assume_tac)
  >> RULE_ASSUM_TAC (SIMP_RULE (srw_ss()) [])
  >~ [`label_action (compile_abi_encode_dyn_loop dst src ei asz msz len)`]
  >- (irule label_action_dyn_loop_step >> simp[])
  >> once_rewrite_tac[compile_abi_encode_child_def]
  >> simp_tac pure_ss [LET_THM] >> BETA_TAC
  >- (Cases_on `dyn` >> gvs[]
      >> irule label_action_bind >> simp[label_action_linear] >> gen_tac
      >> simp[label_action_bind, label_action_ignore_bind,
              label_action_linear, label_action_return]
      >> irule label_action_bind >> simp[label_action_linear] >> gen_tac
      >> irule label_action_bind >> simp[label_action_linear] >> gen_tac
      >> irule label_action_bind >> simp[] >> gen_tac
      >> simp[label_action_bind, label_action_ignore_bind,
              label_action_linear, label_action_return])
  >- simp[label_action_static]
  >- (irule label_action_bind >> simp[label_action_linear] >> gen_tac
      >> irule label_action_bind >> simp[label_action_linear] >> gen_tac
      >> irule label_action_bind >> simp[label_action_linear] >> gen_tac
      >> irule label_action_bind >> simp[label_action_linear] >> gen_tac
      >> irule label_action_ignore_bind >> simp[label_action_linear]
      >> irule label_action_bind >> simp[label_action_linear] >> gen_tac
      >> simp[label_action_bind, label_action_ignore_bind, label_action_linear])
  >- simp[label_action_ignore_bind, label_action_linear, label_action_return]
  >- (Cases_on `elem_is_dyn` >> gvs[]
      >> irule label_action_bind >> simp[label_action_linear] >> gen_tac
      >> simp[] >> irule label_action_ignore_bind >> simp[label_action_linear]
      >> irule label_action_bind >> simp[label_action_linear] >> gen_tac
      >> irule label_action_ignore_bind >> simp[label_action_linear]
      >> irule label_action_bind >> simp[label_action_static_loop] >> gen_tac
      >> simp[label_action_bind, label_action_ignore_bind, label_action_linear])
  >- simp[label_action_return]
  >- (IF_CASES_TAC >> gvs[] >> simp[label_action_bind, label_action_ignore_bind,
        label_action_linear, label_action_return])
  >- simp[label_action_return]
  >> simp[label_action_bind, label_action_ignore_bind, label_action_linear]
QED

Theorem label_action_lower_abi_encode:
  !mid src info maxlen.
    label_action (lower_abi_encode mid maxlen (\dst. compile_abi_encode_to_buf dst src info))
Proof
  rpt gen_tac >> Cases_on `mid` >> simp[lower_abi_encode_def, comp_ignore_bind_def] >>
  rpt (FIRST [
    CHANGED_TAC (simp[label_action_return, label_action_linear,
      cj 2 label_action_encoder_mutual]),
    irule label_action_bind, conj_tac, gen_tac])
QED

Theorem lower_abi_encode_structural_facts:
  !mid src info maxlen sa out sb.
    lower_abi_encode mid maxlen (\dst. compile_abi_encode_to_buf dst src info) sa = (out,sb) ==>
    cs_extends sa sb /\ frag_ops_free sa sb /\
    ALL_DISTINCT (MAP (\i. i.inst_id) (frag_code sa sb)) /\
    ~MEM sb.cs_current_bb
      (MAP (\bb. bb.bb_label) (FRONT (emitted_blocks sa sb)))
Proof
  rpt strip_tac
  >> `code_step enc_safe_opcode sa sb` by
       metis_tac[code_action_def, code_action_lower_abi_encode]
  >> `label_step sa sb` by
       metis_tac[label_action_def, label_action_lower_abi_encode]
  >> drule (SIMP_RULE (srw_ss()) [GSYM enc_safe_opcode_def, ETA_THM] code_step_frag_facts)
  >> strip_tac
  >> simp[] >> metis_tac[label_step_current_excluded]
QED
