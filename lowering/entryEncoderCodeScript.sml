Theory entryEncoderCode
Ancestors
  entryCodePredicate entryContextCodePredicate abiEncoder

Theorem entry_code_zero_pad[local]:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_abi_zero_pad p_op len cnt)
Proof
  simp[compile_abi_zero_pad_def, compileEnvTheory.comp_ignore_bind_def] >>
  ntac 3 (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_emit_op] >> rpt gen_tac >> BETA_TAC) >>
  simp[entry_code_emit_void]
QED

Theorem entry_code_get_element_ptr[local]:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_get_element_ptr p_op offset)
Proof
  simp[compile_get_element_ptr_def, entry_code_emit_op]
QED

Theorem entry_code_get_dynarray_elem_ptr[local]:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_get_dynarray_elem_ptr p_op idx sz)
Proof
  simp[compile_get_dynarray_elem_ptr_def] >>
  ntac 2 (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_emit_op] >> rpt gen_tac >> BETA_TAC) >>
  simp[entry_code_emit_op]
QED

Theorem entry_code_encode_static[local]:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_abi_encode_static dst src)
Proof
  simp[compile_abi_encode_static_def, compileEnvTheory.comp_ignore_bind_def] >>
  ntac 2 (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_emit_op, entry_code_emit_void] >> rpt gen_tac >> BETA_TAC) >>
  simp[entry_code_return]
QED

Theorem entry_code_encode_static_info[local]:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_abi_encode_static_info dst src info)
Proof
  Cases_on `info` >>
  simp[compile_abi_encode_static_info_def, entry_code_encode_static,
       entry_code_return, compileEnvTheory.comp_ignore_bind_def] >>
  irule entry_code_bind >> simp[entry_code_emit_void, entry_code_return]
QED

Theorem entry_code_encode_dyn_static_loop[local]:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_abi_encode_dyn_static_loop dst src info asz msz len)
Proof
  simp[compile_abi_encode_dyn_static_loop_def,
       compileEnvTheory.comp_ignore_bind_def] >>
  ntac 26 (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_alloc_buffer, entry_code_emit_op,
            entry_code_emit_void, entry_code_emit_inst, entry_code_new_block,
            entry_code_fresh_label, entry_code_encode_static_info] >>
    rpt gen_tac >> BETA_TAC) >>
  simp[entry_code_emit_op]
QED

Theorem entry_code_encoder_mutual[local]:
  (!dst cp ci dy so dp.
    entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
      (compile_abi_encode_child dst cp ci dy so dp)) /\
  (!dst src info.
    entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
      (compile_abi_encode_to_buf dst src info)) /\
  (!dst src elems so ho dp.
    entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
      (compile_abi_encode_complex_elems dst src elems so ho dp)) /\
  (!dst src ei asz msz len.
    entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
      (compile_abi_encode_dyn_loop dst src ei asz msz len))
Proof
  ho_match_mp_tac compile_abi_encode_child_ind >>
  conj_tac >- suspend "child" >>
  conj_tac >- suspend "prim" >>
  conj_tac >- suspend "bytes" >>
  conj_tac >- suspend "copy" >>
  conj_tac >- suspend "array" >>
  conj_tac >- suspend "empty" >>
  conj_tac >- suspend "complex" >>
  conj_tac >- suspend "nil" >>
  conj_tac >- suspend "cons" >>
  suspend "loop"
QED

Resume entry_code_encoder_mutual[child]:
  rpt strip_tac >> Cases_on `dy` >> gvs[] >>
  simp[Once compile_abi_encode_child_def, compileEnvTheory.comp_ignore_bind_def] >>
  rpt (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_emit_op, entry_code_emit_void] >>
    rpt gen_tac >> BETA_TAC) >>
  simp[entry_code_return]
QED

Resume entry_code_encoder_mutual[prim]:
  simp[Once compile_abi_encode_child_def, entry_code_encode_static]
QED

Resume entry_code_encoder_mutual[bytes]:
  rpt gen_tac >>
  simp[Once compile_abi_encode_child_def, compileEnvTheory.comp_ignore_bind_def] >>
  ntac 9 (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_emit_op, entry_code_emit_void] >>
    rpt gen_tac >> BETA_TAC) >> simp[entry_code_emit_op]
QED

Resume entry_code_encoder_mutual[copy]:
  simp[Once compile_abi_encode_child_def, compileEnvTheory.comp_ignore_bind_def] >>
  rpt gen_tac >> irule entry_code_bind >>
  simp[entry_code_emit_void, entry_code_return]
QED

Resume entry_code_encoder_mutual[array]:
  rpt strip_tac >> Cases_on `elem_is_dyn` >> gvs[] >>
  simp[Once compile_abi_encode_child_def, compileEnvTheory.comp_ignore_bind_def] >>
  ntac 8 (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_alloc_buffer, entry_code_emit_op, entry_code_emit_void,
            entry_code_encode_dyn_static_loop] >>
    rpt gen_tac >> BETA_TAC) >> simp[entry_code_emit_op]
QED

Resume entry_code_encoder_mutual[empty]:
  simp[Once compile_abi_encode_child_def, entry_code_return]
QED

Resume entry_code_encoder_mutual[complex]:
  rpt strip_tac >> gvs[] >>
  pure_once_rewrite_tac[compile_abi_encode_child_def] >>
  simp[compileEnvTheory.comp_ignore_bind_def] >>
  IF_CASES_TAC >> gvs[] >>
  rpt (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_alloc_buffer, entry_code_emit_void] >>
    rpt gen_tac >> BETA_TAC) >>
  simp[entry_code_emit_op, entry_code_return]
QED

Resume entry_code_encoder_mutual[nil]:
  simp[Once compile_abi_encode_child_def, entry_code_return]
QED

Resume entry_code_encoder_mutual[cons]:
  rpt strip_tac >>
  simp[Once compile_abi_encode_child_def, compileEnvTheory.comp_ignore_bind_def] >>
  irule entry_code_bind >> reverse conj_tac
  >- simp[entry_code_emit_op] >> gen_tac >> BETA_TAC >>
  irule entry_code_bind >> reverse conj_tac >- simp[] >>
  rpt gen_tac >> BETA_TAC >> metis_tac[arithmeticTheory.ADD_COMM]
QED

Resume entry_code_encoder_mutual[loop]:
  rpt strip_tac >> gvs[] >>
  simp[Once compile_abi_encode_child_def, compileEnvTheory.comp_ignore_bind_def] >>
  rpt (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_alloc_buffer, entry_code_emit_op, entry_code_emit_void,
            entry_code_emit_inst, entry_code_new_block, entry_code_fresh_label] >>
    rpt gen_tac >> BETA_TAC) >>
  simp[entry_code_emit_op]
QED

Finalise entry_code_encoder_mutual

Theorem entry_code_encode_child:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_abi_encode_child dst child_src ci dy so dp)
Proof
  metis_tac[entry_code_encoder_mutual]
QED

Theorem entry_code_encode_to_buf:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_abi_encode_to_buf dst src info)
Proof
  metis_tac[entry_code_encoder_mutual]
QED

Theorem entry_code_encode_complex_elems:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_abi_encode_complex_elems dst src elems so ho dp)
Proof
  metis_tac[entry_code_encoder_mutual]
QED

Theorem entry_code_encode_dyn_loop:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_abi_encode_dyn_loop dst src ei asz msz len)
Proof
  metis_tac[entry_code_encoder_mutual]
QED
