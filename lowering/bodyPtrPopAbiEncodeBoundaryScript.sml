Theory bodyPtrPopAbiEncodeBoundary
Ancestors bodyPtrPopAbiStaticBoundary bodyPtrPopCompilerBoundary
  bodyPtrPopArithmeticBoundary bodyPtrPopAllocationBoundary
  bodyPtrPopMaterialization abiEncoder compileEnv emitHelper list

Theorem pop_abi_encode_boundary_mutual:
  (!dst cp ci is_dyn soff dop sa r sb.
    pop_comp_boundary sa /\
    compile_abi_encode_child dst cp ci is_dyn soff dop sa = (r,sb) ==>
    pop_comp_boundary sb) /\
  (!dst src info sa r sb.
    pop_comp_boundary sa /\
    compile_abi_encode_to_buf dst src info sa = (r,sb) ==>
    pop_comp_boundary sb) /\
  (!dst src elems so ho dp sa r sb.
    pop_comp_boundary sa /\
    compile_abi_encode_complex_elems dst src elems so ho dp sa = (r,sb) ==>
    pop_comp_boundary sb) /\
  (!dst src ei asz msz lo sa r sb.
    pop_comp_boundary sa /\
    compile_abi_encode_dyn_loop dst src ei asz msz lo sa = (r,sb) ==>
    pop_comp_boundary sb)
Proof
  ho_match_mp_tac compile_abi_encode_child_ind >> rpt conj_tac
  >- suspend "child"
  >- suspend "word"
  >- suspend "bytes"
  >- suspend "copy"
  >- suspend "array"
  >- suspend "empty"
  >- suspend "complex"
  >- suspend "elems_nil"
  >- suspend "elems_cons"
  >> suspend "loop"
QED

Resume pop_abi_encode_boundary_mutual[word]:
  simp[Once compile_abi_encode_child_def] >> rpt strip_tac >>
  drule_all pop_compile_abi_encode_static_boundary >> simp[]
QED

Resume pop_abi_encode_boundary_mutual[bytes]:
  simp[Once compile_abi_encode_child_def, comp_ignore_bind_def] >> rpt strip_tac >>
  rpt (drule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
       disch_then irule >> simp[] >> conj_tac >> rpt gen_tac >> strip_tac) >>
  FIRST [drule_at (Pat `emit_void _ _ _ = _`) pop_emit_void_boundary,
         drule_at (Pat `emit_op _ _ _ = _`) pop_emit_op_boundary] >> simp[]
QED

Resume pop_abi_encode_boundary_mutual[copy]:
  simp[Once compile_abi_encode_child_def, comp_ignore_bind_def] >> rpt strip_tac >>
  drule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
  disch_then irule >> simp[] >> conj_tac >> rpt strip_tac >>
  FIRST [drule_at (Pat `emit_void _ _ _ = _`) pop_emit_void_boundary,
         drule_all pop_comp_boundary_return] >> simp[]
QED

Resume pop_abi_encode_boundary_mutual[empty]:
  simp[Once compile_abi_encode_child_def] >> rpt strip_tac >>
  drule_all pop_comp_boundary_return >> simp[]
QED

Resume pop_abi_encode_boundary_mutual[elems_nil]:
  simp[Once compile_abi_encode_child_def] >> rpt strip_tac >>
  drule_all pop_comp_boundary_return >> simp[]
QED

Resume pop_abi_encode_boundary_mutual[child]:
  rpt gen_tac >> strip_tac >> Cases_on `is_dyn` >> gvs[] >>
  rpt strip_tac >>
  qpat_x_assum `compile_abi_encode_child _ _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_abi_encode_child_def, comp_ignore_bind_def] >> strip_tac >>
  gvs[arithmeticTheory.ADD_COMM] >>
  rpt (drule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
       disch_then irule >> simp[] >> conj_tac >> rpt gen_tac >> strip_tac) >>
  FIRST [drule_at (Pat `emit_void _ _ _ = _`) pop_emit_void_boundary,
         drule_at (Pat `emit_op _ _ _ = _`) pop_emit_op_boundary,
         drule_all pop_comp_boundary_return,
         first_x_assum drule_all] >> simp[]
QED

Resume pop_abi_encode_boundary_mutual[elems_cons]:
  rpt strip_tac >>
  qpat_x_assum `compile_abi_encode_complex_elems _ _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_abi_encode_child_def, comp_ignore_bind_def] >> strip_tac >>
  gvs[arithmeticTheory.ADD_COMM] >>
  rpt (drule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
       disch_then irule >> simp[] >> conj_tac >> rpt gen_tac >> strip_tac) >>
  FIRST [drule_at (Pat `emit_op _ _ _ = _`) pop_emit_op_boundary,
         first_x_assum drule_all] >> simp[]
QED

Resume pop_abi_encode_boundary_mutual[array]:
  rpt gen_tac >> strip_tac >> Cases_on `elem_is_dyn` >> gvs[] >>
  rpt strip_tac >>
  qpat_x_assum `compile_abi_encode_to_buf _ _ _ _ = _` mp_tac >>
  simp[Once compile_abi_encode_child_def, comp_ignore_bind_def] >> strip_tac >>
  gvs[arithmeticTheory.ADD_COMM] >>
  rpt (drule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
       disch_then irule >> simp[] >> conj_tac >> rpt gen_tac >> strip_tac) >>
  FIRST [drule_all pop_compile_alloc_buffer_boundary,
         drule_at (Pat `emit_void _ _ _ = _`) pop_emit_void_boundary,
         drule_at (Pat `emit_op _ _ _ = _`) pop_emit_op_boundary,
         drule_all pop_compile_abi_encode_dyn_static_loop_boundary,
         first_x_assum drule_all] >> simp[]
QED

Resume pop_abi_encode_boundary_mutual[loop]:
  rpt strip_tac >>
  qpat_x_assum `compile_abi_encode_dyn_loop _ _ _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_abi_encode_child_def, comp_ignore_bind_def] >> strip_tac >>
  gvs[arithmeticTheory.ADD_COMM] >>
  rpt (drule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
       disch_then irule >> simp[] >> conj_tac >> rpt gen_tac >> strip_tac) >>
  FIRST [drule_all pop_compile_alloc_buffer_boundary,
         drule_all pop_fresh_label_boundary,
         drule_at (Pat `emit_void _ _ _ = _`) pop_emit_void_boundary,
         drule_at (Pat `emit_inst _ _ _ _ = _`) pop_emit_inst_boundary,
         drule_at (Pat `emit_op _ _ _ = _`) pop_emit_op_boundary,
         drule_all pop_comp_boundary_new_block,
         first_x_assum drule_all] >> simp[]
QED

Resume pop_abi_encode_boundary_mutual[complex]:
  rpt gen_tac >> strip_tac >>
  Cases_on `EXISTS (\(_,_,_,is_dyn). is_dyn) (v26::v27)` >>
  rpt strip_tac >>
  qpat_x_assum `compile_abi_encode_to_buf _ _ _ _ = _` mp_tac >>
  pure_once_rewrite_tac[compile_abi_encode_child_def] >>
  asm_simp_tac pure_ss [LET_THM, COND_CLAUSES] >>
  strip_tac >> gvs[comp_ignore_bind_def] >>
  rpt (drule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
       disch_then irule >> simp[] >> conj_tac >> rpt gen_tac >> strip_tac) >>
  FIRST [drule_all pop_compile_alloc_buffer_boundary,
         drule_at (Pat `emit_void _ _ _ = _`) pop_emit_void_boundary,
         drule_at (Pat `emit_op _ _ _ = _`) pop_emit_op_boundary,
         drule_all pop_comp_boundary_return,
         first_x_assum drule_all] >> simp[]
QED

Finalise pop_abi_encode_boundary_mutual

Theorem pop_compile_abi_encode_child_boundary:
  pop_comp_boundary sa /\ compile_abi_encode_child dst child_ptr ci is_dyn soff dop sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  metis_tac[pop_abi_encode_boundary_mutual]
QED

Theorem pop_compile_abi_encode_to_buf_boundary:
  pop_comp_boundary sa /\ compile_abi_encode_to_buf dst src info sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  metis_tac[pop_abi_encode_boundary_mutual]
QED

Theorem pop_compile_abi_encode_complex_elems_boundary:
  pop_comp_boundary sa /\ compile_abi_encode_complex_elems dst src elems so ho dp sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  metis_tac[pop_abi_encode_boundary_mutual]
QED

Theorem pop_compile_abi_encode_dyn_loop_boundary:
  pop_comp_boundary sa /\ compile_abi_encode_dyn_loop dst src ei asz msz lo sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  metis_tac[pop_abi_encode_boundary_mutual]
QED
