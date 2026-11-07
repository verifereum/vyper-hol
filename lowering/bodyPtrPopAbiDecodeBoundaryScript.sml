Theory bodyPtrPopAbiDecodeBoundary
Ancestors bodyPtrPopAbiDecodePrimitiveBoundary bodyPtrPopCompilerBoundary
  bodyPtrPopArithmeticBoundary bodyPtrPopAllocationBoundary bodyPtrPopMaterialization
  abiEncoder compileEnv emitHelper list
Libs monadsyntax

Theorem pop_abi_short_check_then_boundary:
  op <> SUB /\ op <> ISZERO /\ pop_comp_boundary sa /\
  (!s x t. pop_comp_boundary s /\ k s = (x,t) ==> pop_comp_boundary t) /\
  (do a <- emit_op op args; b <- emit_op ISZERO [a];
      ignored <- emit_void ASSERT [b]; k od) sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  ntac 2 (CONV_TAC (ONCE_DEPTH_CONV (HO_REWR_CONV (GSYM comp_bind_assoc)))) >>
  rpt strip_tac >>
  drule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
  disch_then irule >> simp[] >> conj_tac
  >- (rpt strip_tac >> gvs[comp_bind_assoc] >>
      drule_at (Pat `comp_bind _ _ _ = _`) pop_abi_short_check_boundary >> simp[]) >>
  rpt strip_tac >> first_x_assum drule_all >> simp[]
QED

Theorem pop_abi_decode_boundary_mutual:
  (!dst src lop hi info sa r sb.
    lop <> ASSERT /\ pop_comp_boundary sa /\
    compile_abi_decode_to_buf dst src lop hi info sa = (r,sb) ==>
    pop_comp_boundary sb) /\
  (!dst src lop hi elems ao vo sa r sb.
    lop <> ASSERT /\ pop_comp_boundary sa /\
    compile_abi_decode_complex_elems dst src lop hi elems ao vo sa = (r,sb) ==>
    pop_comp_boundary sb) /\
  (!dst src lop hi ei asz msz ip cnt sa r sb.
    lop <> ASSERT /\ pop_comp_boundary sa /\
    compile_abi_decode_dyn_loop dst src lop hi ei asz msz ip cnt sa = (r,sb) ==>
    pop_comp_boundary sb)
Proof
  ho_match_mp_tac compile_abi_decode_to_buf_ind >> rpt conj_tac
  >- suspend "word"
  >- suspend "bytes"
  >- suspend "array"
  >- suspend "complex"
  >- suspend "nil"
  >- suspend "cons"
  >> suspend "loop"
QED

Resume pop_abi_decode_boundary_mutual[word]:
  simp[Once compile_abi_decode_to_buf_def] >> rpt strip_tac >>
  drule_at (Pat `compile_abi_decode_static _ _ _ _ _ = _`)
    pop_compile_abi_decode_static_boundary >> disch_then irule >> simp[] >>
  rpt strip_tac >> drule_all pop_compile_abi_clamp_basetype_boundary >> simp[]
QED

Resume pop_abi_decode_boundary_mutual[nil]:
  simp[Once compile_abi_decode_to_buf_def] >> rpt strip_tac >>
  drule_all pop_comp_boundary_return >> simp[]
QED

Resume pop_abi_decode_boundary_mutual[cons]:
  rpt strip_tac >>
  qpat_x_assum `compile_abi_decode_complex_elems _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_abi_decode_to_buf_def, comp_ignore_bind_def] >> strip_tac >>
  gvs[arithmeticTheory.ADD_COMM] >>
  rpt (drule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
       disch_then irule >> simp[] >> conj_tac >> rpt gen_tac >> strip_tac) >>
  FIRST [drule_all pop_compile_getelemptr_abi_boundary,
         drule_at (Pat `emit_op _ _ _ = _`) pop_emit_op_boundary,
         first_x_assum drule_all] >> simp[]
QED

Resume pop_abi_decode_boundary_mutual[complex]:
  rpt gen_tac >> strip_tac >> Cases_on `hi = Lit 0w` >> gvs[] >>
  rpt strip_tac >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_abi_decode_to_buf_def, comp_ignore_bind_def] >> strip_tac >>
  rpt (FIRST [
    (drule_at (Pat `comp_bind _ _ _ = _`) pop_abi_short_check_then_boundary >>
     disch_then irule >> simp[] >> rpt gen_tac >> strip_tac),
    (drule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
     disch_then irule >> simp[] >> conj_tac >> rpt gen_tac >> strip_tac)]) >>
  FIRST [drule_at (Pat `emit_op _ _ _ = _`) pop_emit_op_boundary,
         first_x_assum drule_all] >> simp[]
QED

Resume pop_abi_decode_boundary_mutual[loop]:
  rpt strip_tac >>
  qpat_x_assum `compile_abi_decode_dyn_loop _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_abi_decode_to_buf_def, comp_ignore_bind_def] >> strip_tac >>
  Cases_on `dec_info_needs_offset ei` >> gvs[] >>
  rpt (drule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
       disch_then irule >> simp[] >> conj_tac >> rpt gen_tac >> strip_tac) >>
  FIRST [drule_all pop_fresh_label_boundary,
         drule_at (Pat `emit_void _ _ _ = _`) pop_emit_void_boundary,
         drule_at (Pat `emit_inst _ _ _ _ = _`) pop_emit_inst_boundary,
         drule_at (Pat `emit_op _ _ _ = _`) pop_emit_op_boundary,
         drule_all pop_comp_boundary_new_block,
         drule_all pop_comp_boundary_return,
         drule_all pop_compile_abi_decode_dyn_elem_ptr_boundary,
         first_x_assum drule_all] >> simp[]
QED

Resume pop_abi_decode_boundary_mutual[bytes]:
  rpt gen_tac >> Cases_on `hi = Lit 0w` >>
  simp[Once compile_abi_decode_to_buf_def, comp_ignore_bind_def] >> rpt strip_tac >>
  rpt (FIRST [
    (drule_at (Pat `comp_bind _ _ _ = _`) pop_abi_short_check_then_boundary >>
     disch_then irule >> simp[] >> rpt gen_tac >> strip_tac),
    (drule_at (Pat `comp_bind _ _ _ = _`) pop_abi_short_check_boundary >> simp[] >> NO_TAC),
    (drule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
     disch_then irule >> simp[] >> conj_tac >> rpt gen_tac >> strip_tac)]) >>
  FIRST [drule_at (Pat `emit_op _ _ _ = _`) pop_emit_op_boundary >> simp[],
         drule_all pop_comp_boundary_return >> simp[],
         Cases_on `lop` >>
           RULE_ASSUM_TAC (PURE_REWRITE_RULE [venomInstTheory.opcode_case_def]) >>
           drule_at (Pat `emit_void _ _ _ = _`) pop_emit_void_boundary >> simp[]]
QED

Resume pop_abi_decode_boundary_mutual[array]:
  rpt gen_tac >> strip_tac >>
  Cases_on `hi = Lit 0w` >>
  Cases_on `~elem_is_dyn /\ ~dec_info_needs_clamp ei` >> gvs[] >>
  rpt strip_tac >>
  qpat_x_assum `compile_abi_decode_to_buf _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_abi_decode_to_buf_def, comp_ignore_bind_def] >> strip_tac >>
  rpt (FIRST [
    (drule_at (Pat `comp_bind _ _ _ = _`) pop_abi_short_check_then_boundary >>
     disch_then irule >> simp[] >> rpt gen_tac >> strip_tac),
    (drule_at (Pat `comp_bind _ _ _ = _`) pop_abi_short_check_boundary >> simp[] >> NO_TAC),
    (drule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
     disch_then irule >> simp[] >> conj_tac >> rpt gen_tac >> strip_tac)]) >>
  FIRST [drule_at (Pat `emit_op _ _ _ = _`) pop_emit_op_boundary >> simp[],
         drule_at (Pat `emit_void _ _ _ = _`) pop_emit_void_boundary >> simp[],
         drule_all pop_comp_boundary_return >> simp[],
         drule_all pop_compile_alloc_buffer_boundary >> simp[],
         first_x_assum drule_all >> simp[],
         Cases_on `lop` >>
           RULE_ASSUM_TAC (PURE_REWRITE_RULE [venomInstTheory.opcode_case_def]) >>
           drule_at (Pat `emit_void _ _ _ = _`) pop_emit_void_boundary >> simp[]]
QED

Finalise pop_abi_decode_boundary_mutual

Theorem pop_compile_abi_decode_to_buf_boundary:
  lop <> ASSERT /\ pop_comp_boundary sa /\
  compile_abi_decode_to_buf dst src lop hi info sa = (r,sb) ==> pop_comp_boundary sb
Proof
  metis_tac[pop_abi_decode_boundary_mutual]
QED

Theorem pop_compile_abi_decode_complex_elems_boundary:
  lop <> ASSERT /\ pop_comp_boundary sa /\
  compile_abi_decode_complex_elems dst src lop hi elems ao vo sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  metis_tac[pop_abi_decode_boundary_mutual]
QED

Theorem pop_compile_abi_decode_dyn_loop_boundary:
  lop <> ASSERT /\ pop_comp_boundary sa /\
  compile_abi_decode_dyn_loop dst src lop hi ei asz msz ip cnt sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  metis_tac[pop_abi_decode_boundary_mutual]
QED
