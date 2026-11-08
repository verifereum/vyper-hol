Theory entryAggregateCode
Ancestors
  entryValueCode entryLocationValueCode entryTypedCopyCode
  entryCodePredicate entryContextCodePredicate exprLowering targetPlaceSimCases targetPlaceLive

Theorem entry_code_lower_value:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA) (cfn cenv ty e) ==>
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA) (lower_value cfn cenv ty e)
Proof
  strip_tac >> simp[lower_value_def] >> irule entry_code_bind >>
  simp[entry_code_unwrap_value]
QED

Theorem entry_code_lower_value_with_loc:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA) (cfn cenv ty e) ==>
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (lower_value_with_loc cfn cenv ty e)
Proof
  strip_tac >> simp[lower_value_with_loc_def] >>
  irule entry_code_bind >> reverse conj_tac >- simp[] >>
  gen_tac >> BETA_TAC >> irule entry_code_bind >>
  simp[entry_code_unwrap_value, entry_code_return]
QED

Theorem entry_code_multi_exprs:
  !es cenv. (!e ce ty. MEM e es ==>
    entry_preserves_code (\i. i.inst_opcode <> DALLOCA) (cfn ce ty e)) ==>
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_multi_exprs cfn cenv es)
Proof
  Induct_on `es` >- simp[compile_multi_exprs_def, entry_code_return] >>
  rpt strip_tac >> gvs[] >> simp[compile_multi_exprs_def] >>
  irule entry_code_bind >> reverse conj_tac
  >- (irule entry_code_lower_value >> simp[]) >>
  gen_tac >> BETA_TAC >> irule entry_code_bind >>
  simp[entry_code_return]
QED

Theorem entry_code_multi_vvs:
  !es cenv. (!e ce ty. MEM e es ==>
    entry_preserves_code (\i. i.inst_opcode <> DALLOCA) (cfn ce ty e)) ==>
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_multi_vvs cfn cenv es)
Proof
  Induct_on `es` >- simp[compile_multi_vvs_def, entry_code_return] >>
  rpt strip_tac >> gvs[] >> simp[compile_multi_vvs_def] >>
  irule entry_code_bind >> reverse conj_tac >- simp[] >>
  gen_tac >> BETA_TAC >> irule entry_code_bind >>
  simp[entry_code_return]
QED

Theorem entry_code_make_tuple:
  !es cenv buf off. (!e ce ty. MEM e es ==>
    entry_preserves_code (\i. i.inst_opcode <> DALLOCA) (cfn ce ty e)) ==>
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_make_tuple cfn cenv es buf off)
Proof
  Induct_on `es` >- simp[compile_make_tuple_def, entry_code_return] >>
  rpt strip_tac >> gvs[] >>
  simp[compile_make_tuple_def, compileEnvTheory.comp_ignore_bind_def] >>
  ntac 4 (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_emit_op, entry_code_unwrap_value, entry_code_store_memory] >>
    rpt gen_tac >> BETA_TAC) >> simp[]
QED

Theorem entry_code_make_array_elems:
  !es cenv et sz hl buf idx. (!e ce ty. MEM e es ==>
    entry_preserves_code (\i. i.inst_opcode <> DALLOCA) (cfn ce ty e)) ==>
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_make_array_elems cfn cenv es et sz hl buf idx)
Proof
  Induct_on `es` >- simp[compile_make_array_elems_def, entry_code_return] >>
  rpt strip_tac >> gvs[] >>
  simp[compile_make_array_elems_def, compileEnvTheory.comp_ignore_bind_def] >>
  ntac 4 (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_emit_op, entry_code_unwrap_value, entry_code_store_memory] >>
    rpt gen_tac >> BETA_TAC) >> simp[]
QED

Theorem entry_code_make_array:
  (!e ce ty. MEM e es ==>
    entry_preserves_code (\i. i.inst_opcode <> DALLOCA) (cfn ce ty e)) ==>
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_make_array cfn cenv es et sz hl buf)
Proof
  strip_tac >> simp[compile_make_array_def, compileEnvTheory.comp_ignore_bind_def] >>
  irule entry_code_bind >> reverse conj_tac
  >- (Cases_on `hl` >> simp[entry_code_emit_void, entry_code_return]) >>
  simp[entry_code_make_array_elems]
QED

Theorem entry_code_struct_lit:
  !fs cenv ty buf off. (!name e ce et. MEM (name,e) fs ==>
    entry_preserves_code (\i. i.inst_opcode <> DALLOCA) (cfn ce et e)) ==>
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_struct_lit cfn cenv ty fs buf off)
Proof
  Induct_on `fs` >- simp[compile_struct_lit_def, entry_code_return] >>
  Cases_on `h` >> rpt strip_tac >> gvs[] >>
  simp[compile_struct_lit_def, compileEnvTheory.comp_ignore_bind_def] >>
  ntac 4 (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_emit_op, entry_code_unwrap_value, entry_code_store_memory] >>
    rpt gen_tac >> BETA_TAC) >>
  first_x_assum irule >> metis_tac[]
QED

Theorem entry_code_attribute:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA) (cfn cenv ty base_e) ==>
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_attribute cfn cenv ret_ty ty base_e fname)
Proof
  strip_tac >> simp[compile_attribute_def] >>
  irule entry_code_bind >> reverse conj_tac >- simp[] >>
  gen_tac >> BETA_TAC >> irule entry_code_bind >>
  simp[entry_code_emit_op, entry_code_return]
QED

Theorem entry_code_mapping_subscript:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_mapping_subscript slot key)
Proof
  simp[compile_mapping_subscript_def, compileEnvTheory.comp_ignore_bind_def] >>
  ntac 4 (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_alloc_buffer, entry_code_emit_void, entry_code_emit_op] >>
    rpt gen_tac >> BETA_TAC) >> simp[entry_code_emit_op]
QED

Theorem entry_code_keccak256_key:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_keccak256_key key is_bytes32)
Proof
  Cases_on `is_bytes32` >>
  simp[compile_keccak256_key_def, compileEnvTheory.comp_ignore_bind_def] >>
  ntac 2 (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_alloc_buffer, entry_code_emit_void, entry_code_emit_op] >>
    rpt gen_tac >> BETA_TAC) >> simp[entry_code_emit_op]
QED

Theorem entry_code_tuple_subscript:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_tuple_subscript ptr_op off)
Proof
  simp[compile_tuple_subscript_def, entry_code_emit_op]
QED

Theorem entry_code_array_subscript:
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA) (loader base_op) ==>
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_array_subscript base_op idx dyn nitems ws sz signed loader)
Proof
  strip_tac >>
  simp[compile_array_subscript_def, compileEnvTheory.comp_ignore_bind_def] >>
  irule entry_code_bind >> reverse conj_tac
  >- (Cases_on `dyn` >> simp[entry_code_return]) >>
  rpt gen_tac >> BETA_TAC >>
  irule entry_code_bind >> reverse conj_tac
  >- (Cases_on `signed` >> simp[entry_code_return, entry_code_emit_op]) >>
  rpt gen_tac >> BETA_TAC >>
  ntac 5 (irule entry_code_bind >> reverse conj_tac
    >- simp[entry_code_emit_op, entry_code_emit_void] >> rpt gen_tac >> BETA_TAC) >>
  irule entry_code_bind >> reverse conj_tac
  >- (Cases_on `dyn` >> simp[entry_code_return, entry_code_emit_op]) >>
  rpt gen_tac >> BETA_TAC >>
  irule entry_code_bind >> simp[entry_code_emit_op]
QED

Theorem entry_code_subscript:
  (!ce et. entry_preserves_code (\i. i.inst_opcode <> DALLOCA) (cfn ce et base_e)) /\
  (!ce et. entry_preserves_code (\i. i.inst_opcode <> DALLOCA) (cfn ce et idx_e)) ==>
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_subscript cfn cenv ret_ty ty base_e idx_e)
Proof
  strip_tac >> simp[compile_subscript_def] >>
  irule entry_code_bind >> reverse conj_tac >- simp[] >>
  gen_tac >> BETA_TAC >> Cases_on `place_type cenv base_e`
  >~ [`place_type cenv base_e = ValPT _`] >- suspend "val" >>
  simp[] >> irule entry_code_bind >> reverse conj_tac
  >- (irule entry_code_lower_value >> simp[]) >>
  gen_tac >> BETA_TAC >> irule entry_code_bind >> reverse conj_tac
  >- (IF_CASES_TAC >> simp[entry_code_keccak256_key, entry_code_return]) >>
  gen_tac >> BETA_TAC >> irule entry_code_bind >>
  simp[entry_code_mapping_subscript, entry_code_return]
QED

Resume entry_code_subscript[val]:
  rename1 `ValPT bty` >> Cases_on `bty` >> simp[] >>
  (irule entry_code_bind >> reverse conj_tac
   >- simp[entry_code_tuple_subscript, entry_code_lower_value] >>
   rpt gen_tac >> BETA_TAC >> simp[entry_code_return] >>
   irule entry_code_bind >> simp[entry_code_return] >>
   irule entry_code_array_subscript >> simp[entry_code_ptr_load])
QED

Finalise entry_code_subscript

Theorem entry_code_get_target_ptr:
  !bt cenv. (!e ce et. MEM e (target_indices bt) ==>
    entry_preserves_code (\i. i.inst_opcode <> DALLOCA) (cfn ce et e)) ==>
  entry_preserves_code (\i. i.inst_opcode <> DALLOCA)
    (compile_get_target_ptr cfn cenv bt)
Proof
  measureInduct_on `base_assignment_target_size bt` >> Cases_on `bt`
  >- suspend "name"
  >- suspend "topname"
  >- suspend "subscript"
  >- suspend "attribute"
QED

Resume entry_code_get_target_ptr[name]:
  rpt strip_tac >> simp[compile_get_target_ptr_def] >>
  Cases_on `FLOOKUP cenv.ce_vars s` >> simp[entry_code_return] >>
  Cases_on `x` >> simp[entry_code_return]
QED

Resume entry_code_get_target_ptr[topname]:
  rpt strip_tac >> simp[compile_get_target_ptr_def] >>
  qmatch_goalsub_rename_tac `FLOOKUP cenv.ce_module_vars nsid` >>
  Cases_on `FLOOKUP cenv.ce_module_vars nsid` >> simp[entry_code_return] >>
  Cases_on `x` >> simp[entry_code_return]
QED

Resume entry_code_get_target_ptr[attribute]:
  rpt strip_tac >> gvs[target_indices_def] >>
  simp[compile_get_target_ptr_def] >> irule entry_code_bind >>
  reverse conj_tac >- simp[] >>
  rpt gen_tac >> BETA_TAC >> irule entry_code_bind >>
  simp[entry_code_emit_op, entry_code_return]
QED

Resume entry_code_get_target_ptr[subscript]:
  rpt strip_tac >> gvs[target_indices_def] >>
  simp[compile_get_target_ptr_def] >> irule entry_code_bind >>
  reverse conj_tac >- simp[] >> rpt gen_tac >> BETA_TAC >>
  qabbrev_tac `desc = SND (SND x)` >>
  Cases_on `desc`
  >- (simp[] >> irule entry_code_bind >> reverse conj_tac
      >- (irule entry_code_lower_value >> simp[]) >>
      rpt gen_tac >> BETA_TAC >> irule entry_code_bind >>
      simp[entry_code_return] >> irule entry_code_array_subscript >>
      simp[entry_code_ptr_load]) >>
  rename1 `SOME pt` >> Cases_on `pt` >> simp[]
  >- (irule entry_code_bind >> reverse conj_tac
      >- (irule entry_code_lower_value >> simp[]) >>
      rpt gen_tac >> BETA_TAC >> irule entry_code_bind >> reverse conj_tac
      >- (IF_CASES_TAC >> simp[entry_code_keccak256_key, entry_code_return]) >>
      rpt gen_tac >> BETA_TAC >> irule entry_code_bind >>
      simp[entry_code_mapping_subscript, entry_code_return]) >>
  irule entry_code_bind >> reverse conj_tac
  >- (irule entry_code_lower_value >> simp[]) >>
  rpt gen_tac >> BETA_TAC >> irule entry_code_bind >>
  simp[entry_code_return] >> irule entry_code_array_subscript >>
  simp[entry_code_ptr_load]
QED

Finalise entry_code_get_target_ptr
