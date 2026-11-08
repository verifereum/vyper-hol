Theory entryValueCode
Ancestors
  entryCodePredicate entryContextCodePredicate exprLowering
  entryTypedCopyCode entryLocationValueCode

Theorem entry_code_store_byte_chunks:
  !p bs off. entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_store_byte_chunks p bs off)
Proof
  ho_match_mp_tac compile_store_byte_chunks_ind >> conj_tac
  >- simp[Once compile_store_byte_chunks_def, entry_code_return] >>
  rpt strip_tac >> gvs[] >>
  simp[Once compile_store_byte_chunks_def, compileEnvTheory.comp_ignore_bind_def] >>
  ntac 2 (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_emit_op, entry_code_emit_void] >>
    rpt gen_tac >> BETA_TAC) >> simp[]
QED

Theorem entry_code_bytelike_literal:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_bytelike_literal bs max_len)
Proof
  simp[compile_bytelike_literal_def, compileEnvTheory.comp_ignore_bind_def] >>
  ntac 3 (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_alloc_buffer, entry_code_emit_void, entry_code_store_byte_chunks] >>
    rpt gen_tac >> BETA_TAC) >> simp[entry_code_return]
QED

Theorem entry_code_env_var:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA) (compile_env_var ev)
Proof
  Cases_on `ev` >> simp[compile_env_var_def, entry_code_emit_op] >>
  ntac 2 (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_emit_op] >> rpt gen_tac >> BETA_TAC) >>
  simp[entry_code_emit_op]
QED

Theorem entry_code_int_clamp:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_int_clamp signed bits v)
Proof
  Cases_on `signed` >>
  simp[compile_int_clamp_def, compileEnvTheory.comp_ignore_bind_def] >>
  rpt (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_emit_op, entry_code_emit_void] >>
    rpt gen_tac >> BETA_TAC) >> simp[entry_code_return]
QED

Theorem entry_code_load_bytestring_as_word:
  shift_opc <> DALLOCA ==>
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (load_bytestring_as_word v shift_opc)
Proof
  strip_tac >> Cases_on `shift_opc = SAR` >>
  simp[load_bytestring_as_word_def] >>
  rpt (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_emit_op, entry_code_return] >>
    rpt gen_tac >> BETA_TAC) >> simp[entry_code_return] >>
  irule entry_code_bind >> reverse conj_tac
  >- (ntac 2 (irule entry_code_bind >> reverse conj_tac
        >- simp[entry_code_emit_op] >> rpt gen_tac >> BETA_TAC) >>
      simp[entry_code_emit_op]) >>
  rpt gen_tac >> BETA_TAC >>
  ntac 3 (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_emit_op] >> rpt gen_tac >> BETA_TAC) >>
  simp[entry_code_return]
QED

Theorem entry_code_bytestring_widen_copy:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_bytestring_widen_copy dst_sz v src_sz)
Proof
  simp[compile_bytestring_widen_copy_def, compileEnvTheory.comp_ignore_bind_def] >>
  ntac 2 (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_alloc_buffer, entry_code_copy_memory] >>
    rpt gen_tac >> BETA_TAC) >> simp[entry_code_return]
QED

Theorem entry_code_literal_vv:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_literal_vv ty lit)
Proof
  Cases_on `lit` >> simp[oneline compile_literal_vv_def, entry_code_return]
  >~ [`if b then _ else _`] >- (Cases_on `b` >> simp[entry_code_return]) >>
  Cases_on `ty` >> simp[entry_code_return] >>
  rpt BasicProvers.TOP_CASE_TAC >> simp[entry_code_return] >>
  irule entry_code_bind >> simp[entry_code_bytelike_literal, entry_code_return]
QED

Theorem entry_code_name_vv:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_name_vv cenv ty name)
Proof
  simp[compile_name_vv_def] >>
  Cases_on `FLOOKUP cenv.ce_vars name` >> simp[entry_code_return]
  >- (simp[compileEnvTheory.comp_ignore_bind_def] >>
      irule entry_code_bind >> simp[entry_code_emit_inst, entry_code_return]) >>
  rename1 `SOME loc` >> Cases_on `loc` >>
  simp[entry_code_return, compileEnvTheory.comp_ignore_bind_def] >>
  irule entry_code_bind >> simp[entry_code_emit_inst, entry_code_return]
QED

Theorem entry_code_type_convert:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_type_convert v cv)
Proof
  Cases_on `cv` >>
  simp[compile_type_convert_def, compileEnvTheory.comp_ignore_bind_def,
       entry_code_return, entry_code_emit_op] >>
  rpt IF_CASES_TAC >> simp[entry_code_return, entry_code_int_clamp] >>
  rpt (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_emit_op, entry_code_emit_void, entry_code_return,
            entry_code_load_bytestring_as_word] >>
    rpt gen_tac >> BETA_TAC) >>
  simp[entry_code_emit_op, entry_code_return, entry_code_int_clamp] >>
  rpt IF_CASES_TAC >>
  simp[entry_code_return, entry_code_int_clamp, entry_code_emit_op,
       entry_code_emit_void, entry_code_load_bytestring_as_word,
       entry_code_bind, pairTheory.FORALL_PROD] >>
  CONV_TAC (DEPTH_CONV pairLib.GEN_BETA_CONV) >>
  rpt IF_CASES_TAC >> simp[entry_code_int_clamp, entry_code_return] >>
  rpt (irule entry_code_bind >> reverse conj_tac
    >- (simp[entry_code_return, entry_code_emit_op, entry_code_emit_void] >>
        rpt (irule entry_code_bind >> reverse conj_tac
          >- simp[entry_code_emit_op, entry_code_emit_void] >>
          rpt gen_tac >> BETA_TAC) >>
        simp[entry_code_emit_op, entry_code_emit_void, entry_code_return]) >>
    rpt gen_tac >> BETA_TAC) >>
  simp[entry_code_emit_op, entry_code_return, entry_code_int_clamp]
QED

Theorem entry_code_materialize_vv:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_materialize_vv cenv ty vv)
Proof
  simp[compile_materialize_vv_def, compileEnvTheory.comp_ignore_bind_def] >>
  ntac 3 (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_alloc_buffer, entry_code_unwrap_value, entry_code_store_memory] >>
    rpt gen_tac >> BETA_TAC) >> simp[entry_code_return]
QED

Theorem entry_code_ifexp_arm:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_ifexp_arm cenv res_ty arm_ty vv)
Proof
  Cases_on `is_word_type res_ty \/ same_memory_layout cenv arm_ty res_ty`
  >- simp[compile_ifexp_arm_def, entry_code_unwrap_value] >>
  simp[compile_ifexp_arm_def, compileEnvTheory.comp_ignore_bind_def] >>
  ntac 3 (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_alloc_buffer, entry_code_unwrap_value, entry_code_store_memory] >>
    rpt gen_tac >> BETA_TAC) >> simp[entry_code_return]
QED
