Theory entryTypedCopyCode
Ancestors
  entryCodePredicate entryContextCodePredicate context

Theorem entry_code_bytestring_copy_len:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_bytestring_copy_len src)
Proof
  simp[compile_bytestring_copy_len_def] >>
  ntac 3 (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_emit_op] >> rpt gen_tac >> BETA_TAC) >>
  simp[entry_code_emit_op]
QED

Theorem entry_code_store_bytestring:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_store_bytestring src dst)
Proof
  simp[compile_store_bytestring_def] >> irule entry_code_bind >>
  simp[entry_code_bytestring_copy_len, entry_code_emit_void]
QED

Theorem entry_code_with_byte_offset:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_with_byte_offset ptr_op off)
Proof
  Cases_on `off = 0` >>
  simp[compile_with_byte_offset_def, entry_code_return, entry_code_emit_op]
QED

Theorem entry_code_copy_memory_dynamic:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_copy_memory_dynamic dst src len)
Proof
  simp[compile_copy_memory_dynamic_def, entry_code_emit_void]
QED

Theorem entry_code_typed_copy_mutual[local]:
  (!ce dst dt src st.
    entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
      (compile_store_memory_typed ce dst dt src st)) /\
  (!ce dst src dts sts doff soff.
    entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
      (compile_typed_copy_fields ce dst src dts sts doff soff)) /\
  (!ce dst dt src st n.
    entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
      (compile_copy_sarray_typed ce dst dt src st n)) /\
  (!ce dst dt cap src st.
    entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
      (compile_copy_dynarray_typed ce dst dt cap src st)) /\
  (!ce dst src dfs sfs doff soff.
    entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
      (compile_struct_typed_copy ce dst src dfs sfs doff soff))
Proof
  ho_match_mp_tac compile_store_memory_typed_ind >>
  conj_tac >- suspend "store" >>
  conj_tac >- suspend "nil" >>
  conj_tac >- suspend "empty_src" >>
  conj_tac >- suspend "fields" >>
  conj_tac >- suspend "sarray" >>
  conj_tac >- suspend "dynarray" >>
  conj_tac >- suspend "struct_nil" >>
  suspend "struct_cons"
QED

Resume entry_code_typed_copy_mutual[store]:
  rpt strip_tac >>
  pure_once_rewrite_tac[compile_store_memory_typed_def] >>
  Cases_on `is_word_type dt`
  >- (simp[] >> irule entry_code_bind >>
      simp[entry_code_emit_op, entry_code_emit_void]) >>
  Cases_on `is_bytestring_type dt /\ is_bytestring_type st`
  >- simp[entry_code_store_bytestring] >>
  Cases_on `acyclic_struct_metadata ce.ce_struct_fields`
  >- (simp[] >> Cases_on `dt` >> Cases_on `st` >>
      gvs[entry_code_copy_memory] >>
      Cases_on `b` >> Cases_on `b'` >> gvs[entry_code_copy_memory]) >>
  simp[entry_code_emit_void]
QED

Resume entry_code_typed_copy_mutual[nil]:
  simp[Once compile_store_memory_typed_def, entry_code_return]
QED

Resume entry_code_typed_copy_mutual[empty_src]:
  simp[Once compile_store_memory_typed_def, entry_code_return]
QED

Resume entry_code_typed_copy_mutual[fields]:
  rpt strip_tac >> gvs[] >>
  simp[Once compile_store_memory_typed_def, compileEnvTheory.comp_ignore_bind_def] >>
  ntac 2 (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_with_byte_offset] >> rpt gen_tac >> BETA_TAC) >>
  irule entry_code_bind >> simp[]
QED

Resume entry_code_typed_copy_mutual[sarray]:
  rpt strip_tac >> gvs[] >>
  pure_once_rewrite_tac[compile_store_memory_typed_def] >>
  simp[] >>
  Cases_on `type_memory_bytes ce dt = type_memory_bytes ce st /\
            ~is_abi_dynamic ce.ce_struct_fields dt`
  >- simp[entry_code_copy_memory] >>
  gvs[compileEnvTheory.comp_ignore_bind_def] >>
  simp[SF CONJ_ss] >>
  ntac 15 (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_fresh_label, entry_code_fresh_var, entry_code_emit_inst,
            entry_code_new_block, entry_code_emit_op] >> rpt gen_tac >> BETA_TAC) >>
  irule entry_code_bind >> reverse conj_tac >- simp[] >>
  rpt gen_tac >> BETA_TAC >>
  ntac 4 (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_emit_op, entry_code_emit_inst, entry_code_new_block] >>
    rpt gen_tac >> BETA_TAC) >> simp[entry_code_return]
QED

Resume entry_code_typed_copy_mutual[dynarray]:
  rpt strip_tac >> gvs[] >>
  simp[Once compile_store_memory_typed_def, compileEnvTheory.comp_ignore_bind_def] >>
  ntac 7 (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_emit_op, entry_code_emit_void] >> rpt gen_tac >> BETA_TAC) >>
  Cases_on `type_memory_bytes ce dt = type_memory_bytes ce st /\ dt = st`
  >- (simp[] >> irule entry_code_bind >>
      simp[entry_code_emit_op, entry_code_copy_memory_dynamic]) >>
  gvs[] >> `dt <> st` by metis_tac[] >> simp[] >>
  ntac 15 (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_fresh_label, entry_code_fresh_var, entry_code_emit_inst,
            entry_code_new_block, entry_code_emit_op] >> rpt gen_tac >> BETA_TAC) >>
  irule entry_code_bind >> reverse conj_tac >- simp[] >>
  rpt gen_tac >> BETA_TAC >>
  ntac 4 (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_emit_op, entry_code_emit_inst, entry_code_new_block] >>
    rpt gen_tac >> BETA_TAC) >> simp[entry_code_return]
QED

Resume entry_code_typed_copy_mutual[struct_nil]:
  simp[Once compile_store_memory_typed_def, entry_code_return]
QED

Resume entry_code_typed_copy_mutual[struct_cons]:
  rpt strip_tac >> gvs[] >>
  pure_once_rewrite_tac[compile_store_memory_typed_def] >>
  Cases_on `ALOOKUP sfs name` >>
  gvs[compileEnvTheory.comp_ignore_bind_def] >>
  CONV_TAC (DEPTH_CONV pairLib.GEN_BETA_CONV) >>
  ntac 2 (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_with_byte_offset] >> rpt gen_tac >> BETA_TAC) >>
  irule entry_code_bind >> simp[] >>
  Cases_on `x` >> gvs[]
QED

Finalise entry_code_typed_copy_mutual

Theorem entry_code_store_memory_typed:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_store_memory_typed ce dst dt src st)
Proof
  metis_tac[entry_code_typed_copy_mutual]
QED

Theorem entry_code_typed_copy_fields:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_typed_copy_fields ce dst src dts sts doff soff)
Proof
  metis_tac[entry_code_typed_copy_mutual]
QED

Theorem entry_code_copy_sarray_typed:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_copy_sarray_typed ce dst dt src st n)
Proof
  metis_tac[entry_code_typed_copy_mutual]
QED

Theorem entry_code_copy_dynarray_typed:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_copy_dynarray_typed ce dst dt cap src st)
Proof
  metis_tac[entry_code_typed_copy_mutual]
QED

Theorem entry_code_struct_typed_copy:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_struct_typed_copy ce dst src dfs sfs doff soff)
Proof
  metis_tac[entry_code_typed_copy_mutual]
QED

Theorem entry_code_store_memory:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_store_memory ce src dst dt st)
Proof
  simp[compile_store_memory_def] >>
  Cases_on `is_word_type dt` >- simp[entry_code_emit_void] >>
  Cases_on `is_bytestring_type dt` >- simp[entry_code_store_bytestring] >>
  Cases_on `dt = st` >>
  simp[entry_code_copy_memory, entry_code_store_memory_typed]
QED
