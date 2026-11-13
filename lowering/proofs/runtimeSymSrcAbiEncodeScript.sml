Theory runtimeSymSrcAbiEncode
Ancestors
  runtimeSymSrcAbiCalls runtimeSymSrcContext runtimeSymSrcEmission
  runtimeSymSrcInterfaces runtimeSymSrcModuleDispatch
  abiEncoder compileEnv emitHelper loweringShapeDefs
  venomInst list stackPlanTypes

Theorem runtime_sym_encode_op[local]:
  emit_op opc ops s = (v,s') ==>
  opc <> CODESIZE /\ opc <> CODECOPY /\
  EVERY (\op. ~is_label_operand op) ops /\
  EVERY runtime_sym_inst (state_insts s) ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand v
Proof
  metis_tac[runtime_sym_emit_op]
QED

Theorem runtime_sym_encode_void[local]:
  emit_void opc ops s = (u,s') ==>
  opc <> CODESIZE /\ opc <> CODECOPY /\
  EVERY (\op. ~is_label_operand op) ops /\
  EVERY runtime_sym_inst (state_insts s) ==>
  EVERY runtime_sym_inst (state_insts s')
Proof
  metis_tac[runtime_sym_emit_void]
QED

Theorem runtime_sym_abi_encode_dyn_static_loop:
  ~is_label_operand dst /\ ~is_label_operand src /\
  ~is_label_operand len /\ EVERY runtime_sym_inst (state_insts s) /\
  compile_abi_encode_dyn_static_loop dst src info asz msz len s = (v,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand v
Proof
  simp[compile_abi_encode_dyn_static_loop_def, comp_bind_def,
       comp_ignore_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  drule_all runtime_sym_alloc_buffer >> strip_tac >>
  rev_dxrule runtime_sym_encode_void >> simp[is_label_operand_def] >> strip_tac >>
  ntac 3 (rev_dxrule runtime_sym_fresh_label >> strip_tac) >> gvs[] >>
  rev_dxrule_at (Pat `emit_inst _ _ _ _ = _`) runtime_sym_jump >> simp[] >> strip_tac >>
  imp_res_tac runtime_sym_new_block_result >> gvs[] >>
  ntac 3 (rev_dxrule runtime_sym_encode_op >> simp[] >> strip_tac) >>
  drule_all runtime_sym_jnz >> strip_tac >>
  ntac 7 (rev_dxrule runtime_sym_encode_op >>
          simp[is_label_operand_def] >> strip_tac) >>
  drule_all runtime_sym_abi_encode_static_info >> strip_tac >>
  rev_dxrule runtime_sym_encode_op >> simp[is_label_operand_def] >> strip_tac >>
  rev_dxrule runtime_sym_encode_void >> simp[] >> strip_tac >>
  rev_dxrule_at (Pat `emit_inst _ _ _ _ = _`) runtime_sym_jump >> simp[] >> strip_tac >>
  ntac 2 (rev_dxrule runtime_sym_encode_op >>
          simp[is_label_operand_def] >> strip_tac) >>
  rev_dxrule runtime_sym_encode_op >> simp[is_label_operand_def]
QED

Theorem runtime_sym_abi_encode_mutual:
  (!dst cp ci dyn off dp s v s'.
     ~is_label_operand dst /\ ~is_label_operand cp /\ ~is_label_operand dp /\
     EVERY runtime_sym_inst (state_insts s) /\
     compile_abi_encode_child dst cp ci dyn off dp s = (v,s') ==>
     EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand v) /\
  (!dst src info s v s'.
     ~is_label_operand dst /\ ~is_label_operand src /\
     EVERY runtime_sym_inst (state_insts s) /\
     compile_abi_encode_to_buf dst src info s = (v,s') ==>
     EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand v) /\
  (!dst src elems so ho dp s v s'.
     ~is_label_operand dst /\ ~is_label_operand src /\ ~is_label_operand dp /\
     EVERY runtime_sym_inst (state_insts s) /\
     compile_abi_encode_complex_elems dst src elems so ho dp s = (v,s') ==>
     EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand v) /\
  (!dst src info asz msz len s v s'.
     ~is_label_operand dst /\ ~is_label_operand src /\ ~is_label_operand len /\
     EVERY runtime_sym_inst (state_insts s) /\
     compile_abi_encode_dyn_loop dst src info asz msz len s = (v,s') ==>
     EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand v)
Proof
  ho_match_mp_tac compile_abi_encode_child_ind >>
  rpt conj_tac >> rpt gen_tac >> strip_tac >>
  all_tac
  >- suspend "child"
  >- suspend "word"
  >- suspend "bytes"
  >- suspend "copy"
  >- suspend "array"
  >- suspend "empty"
  >- suspend "complex"
  >- suspend "elems_empty"
  >- suspend "elems_cons"
  >> suspend "loop"
QED

Resume runtime_sym_abi_encode_mutual[word]:
  gvs[Once compile_abi_encode_child_def] >>
  metis_tac[runtime_sym_abi_encode_static]
QED
Resume runtime_sym_abi_encode_mutual[copy]:
  gvs[Once compile_abi_encode_child_def, comp_bind_def,
      comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> gvs[is_label_operand_def] >>
  rev_dxrule runtime_sym_encode_void >> simp[is_label_operand_def]
QED
Resume runtime_sym_abi_encode_mutual[empty]:
  gvs[Once compile_abi_encode_child_def, comp_return_def, is_label_operand_def]
QED
Resume runtime_sym_abi_encode_mutual[elems_empty]:
  gvs[Once compile_abi_encode_child_def, comp_return_def, is_label_operand_def]
QED
Resume runtime_sym_abi_encode_mutual[bytes]:
  gvs[Once compile_abi_encode_child_def, comp_bind_def,
      comp_ignore_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >>
  ntac 4 (rev_dxrule runtime_sym_encode_op >>
          simp[is_label_operand_def] >> strip_tac) >>
  rev_dxrule runtime_sym_encode_void >> simp[is_label_operand_def] >> strip_tac >>
  rev_dxrule runtime_sym_encode_op >> simp[is_label_operand_def] >> strip_tac >>
  rev_dxrule runtime_sym_encode_void >> simp[] >> strip_tac >>
  ntac 3 (rev_dxrule runtime_sym_encode_op >>
          simp[is_label_operand_def] >> strip_tac) >>
  rev_dxrule runtime_sym_encode_op >> simp[is_label_operand_def]
QED
Resume runtime_sym_abi_encode_mutual[child]:
  rpt gen_tac >>
  Cases_on `dyn` >> gvs[] >>
  simp[Once compile_abi_encode_child_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  rev_dxrule runtime_sym_encode_op >> simp[is_label_operand_def] >> strip_tac >>
  all_tac
  >- (ntac 2 (rev_dxrule runtime_sym_encode_op >> simp[] >> strip_tac) >>
      first_x_assum drule_all >> strip_tac >>
      rev_dxrule runtime_sym_encode_void >> simp[] >> strip_tac >>
      rev_dxrule runtime_sym_encode_op >> simp[] >> strip_tac >>
      rev_dxrule runtime_sym_encode_void >> simp[]) >>
  first_x_assum drule_all >> simp[]
QED
Resume runtime_sym_abi_encode_mutual[array]:
  rpt gen_tac >> Cases_on `elem_is_dyn` >> gvs[] >>
  pure_once_rewrite_tac[compile_abi_encode_child_def] >>
  simp[comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  drule_all runtime_sym_alloc_buffer >> strip_tac >>
  rev_dxrule runtime_sym_encode_void >> simp[is_label_operand_def] >> strip_tac >>
  rev_dxrule runtime_sym_encode_op >> simp[] >> strip_tac >>
  rev_dxrule runtime_sym_encode_void >> simp[] >> strip_tac >>
  all_tac
  >- (first_x_assum drule_all >> strip_tac >>
      ntac 2 (rev_dxrule runtime_sym_encode_op >> simp[] >> strip_tac) >>
      rev_dxrule runtime_sym_encode_void >> simp[] >> strip_tac >>
      rev_dxrule runtime_sym_encode_op >> simp[]) >>
  drule_all runtime_sym_abi_encode_dyn_static_loop >> strip_tac >>
  ntac 2 (rev_dxrule runtime_sym_encode_op >> simp[] >> strip_tac) >>
  rev_dxrule runtime_sym_encode_void >> simp[] >> strip_tac >>
  rev_dxrule runtime_sym_encode_op >> simp[]
QED
Resume runtime_sym_abi_encode_mutual[complex]:
  rpt gen_tac >>
  rename1 `compile_abi_encode_to_buf dst src (AbiComplex (el::els))` >>
  PairCases_on `el` >>
  qpat_x_assum `!static_size has_dynamic dp dyn_ptr_alloc. _`
    (mk_asm "dynih") >>
  qpat_x_assum `!static_size has_dynamic. _` (mk_asm "staticih") >>
  pure_once_rewrite_tac[compile_abi_encode_child_def] >>
  simp[NoAsms, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  IF_CASES_TAC >> simp[NoAsms, comp_bind_def, comp_ignore_bind_def]
  >- (Cases_on `compile_alloc_buffer 32 s` >>
      rename1 `compile_alloc_buffer 32 s = (buf,s1)` >> simp[NoAsms] >>
      qmatch_goalsub_abbrev_tac `emit_void MSTORE ops s1` >>
      Cases_on `emit_void MSTORE ops s1` >>
      rename1 `emit_void MSTORE ops s1 = (u,s2)` >> simp[NoAsms] >>
      Cases_on `compile_abi_encode_complex_elems dst src
                ((el0,el1,el2,el3)::els) 0 0 buf.buf_operand s2` >>
      simp[NoAsms] >> strip_tac >>
      drule_all runtime_sym_alloc_buffer >> strip_tac >>
      rev_dxrule runtime_sym_encode_void >>
      simp[Abbr `ops`, is_label_operand_def] >> strip_tac >>
      asm_x "dynih" (mp_tac o SRULE []) >>
      simp[] >> disch_then (qspec_then `buf` mp_tac) >>
      disch_then drule_all >> strip_tac >>
      rev_dxrule runtime_sym_encode_op >> simp[]) >>
  gvs[] >>
  Cases_on `compile_abi_encode_complex_elems dst src
             ((el0,el1,el2,F)::els) 0 0 (Lit 0w) s` >>
  simp[NoAsms, comp_return_def] >> strip_tac >> gvs[] >>
  asm_x "staticih" (mp_tac o SRULE []) >>
  simp[is_label_operand_def] >>
  disch_then drule_all >> simp[is_label_operand_def]
QED
Resume runtime_sym_abi_encode_mutual[elems_cons]:
  rpt gen_tac >>
  qpat_x_assum `!cp s v s'. _` (mk_asm "childih") >>
  qpat_x_assum `!s v s'. _` (mk_asm "tailih") >>
  simp[Once compile_abi_encode_child_def, comp_bind_def,
       comp_ignore_bind_def] >>
  namedCases_on `emit_op ADD [src; Lit (n2w so)] s` ["elem_src s1"] >> simp[] >>
  Cases_on `compile_abi_encode_child dst elem_src ci dyn ho dp s1` >> simp[] >>
  strip_tac >>
  rev_dxrule runtime_sym_encode_op >> simp[is_label_operand_def] >> strip_tac >>
  asm_x "childih" (drule_all) >> strip_tac >>
  asm_x "tailih" (drule_all o SRULE [arithmeticTheory.ADD_COMM]) >> simp[]
QED
Resume runtime_sym_abi_encode_mutual[loop]:
  rpt gen_tac >>
  first_x_assum (mk_asm "bufih" o SRULE []) >>
  simp[Once compile_abi_encode_child_def, comp_bind_def,
       comp_ignore_bind_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  dxrule_all runtime_sym_alloc_buffer >> strip_tac >>
  rev_dxrule runtime_sym_encode_void >> simp[is_label_operand_def] >> strip_tac >>
  dxrule_all runtime_sym_alloc_buffer >> strip_tac >>
  rev_dxrule runtime_sym_encode_op >> simp[is_label_operand_def] >> strip_tac >>
  rev_dxrule runtime_sym_encode_void >> simp[] >> strip_tac >>
  ntac 3 (rev_dxrule runtime_sym_fresh_label >> strip_tac) >> gvs[] >>
  rev_dxrule_at (Pat `emit_inst _ _ _ _ = _`) runtime_sym_jump >> simp[] >> strip_tac >>
  imp_res_tac runtime_sym_new_block_result >> gvs[] >>
  ntac 3 (rev_dxrule runtime_sym_encode_op >> simp[] >> strip_tac) >>
  drule_all runtime_sym_jnz >> strip_tac >>
  ntac 9 (rev_dxrule runtime_sym_encode_op >>
          simp[is_label_operand_def] >> strip_tac) >>
  asm_x "bufih" drule_all >> strip_tac >>
  rev_dxrule runtime_sym_encode_void >> simp[] >> strip_tac >>
  rev_dxrule runtime_sym_encode_op >> simp[] >> strip_tac >>
  rev_dxrule runtime_sym_encode_void >> simp[] >> strip_tac >>
  rev_dxrule runtime_sym_encode_op >> simp[is_label_operand_def] >> strip_tac >>
  rev_dxrule runtime_sym_encode_void >> simp[] >> strip_tac >>
  rev_dxrule_at (Pat `emit_inst _ _ _ _ = _`) runtime_sym_jump >> simp[] >> strip_tac >>
  ntac 2 (rev_dxrule runtime_sym_encode_op >> simp[] >> strip_tac) >>
  rev_dxrule runtime_sym_encode_op >> simp[is_label_operand_def]
QED
Finalise runtime_sym_abi_encode_mutual

Theorem runtime_sym_abi_encode_child:
  ~is_label_operand dst /\ ~is_label_operand child_ptr /\ ~is_label_operand dp /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_abi_encode_child dst child_ptr ci dyn off dp s = (v,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand v
Proof
  strip_tac >> drule_all (cj 1 runtime_sym_abi_encode_mutual) >> simp[]
QED

Theorem runtime_sym_abi_encode_to_buf:
  ~is_label_operand dst /\ ~is_label_operand src /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_abi_encode_to_buf dst src info s = (v,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand v
Proof
  strip_tac >> drule_all (cj 2 runtime_sym_abi_encode_mutual) >> simp[]
QED

Theorem runtime_sym_abi_encode_complex_elems:
  ~is_label_operand dst /\ ~is_label_operand src /\ ~is_label_operand dp /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_abi_encode_complex_elems dst src elems so ho dp s = (v,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand v
Proof
  strip_tac >> drule_all (cj 3 runtime_sym_abi_encode_mutual) >> simp[]
QED

Theorem runtime_sym_abi_encode_dyn_loop:
  ~is_label_operand dst /\ ~is_label_operand src /\ ~is_label_operand len /\
  EVERY runtime_sym_inst (state_insts s) /\
  compile_abi_encode_dyn_loop dst src info asz msz len s = (v,s') ==>
  EVERY runtime_sym_inst (state_insts s') /\ ~is_label_operand v
Proof
  strip_tac >> drule_all (cj 4 runtime_sym_abi_encode_mutual) >> simp[]
QED
