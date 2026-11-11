(* TOP-LEVEL: aggregate traversal preserves all actual code cuts, including
   children with generated blocks. A singleton dynamic aggregate exposes
   its counter setup, source-address ADD, child and final length load. *)
Theory abiComplexStructure
Ancestors
  abiComplexCode abiEncoder abiEncoderStructure abiStaticLoopCode
  compileAppendProps compileEnv fragExec emitHelper context list pair rich_list arithmetic

Theorem abi_complex_prefix_extends:
  !head_size cs. cs_extends cs (abi_complex_prefix_cut head_size cs)
Proof
  rpt gen_tac >> irule cs_extends_same_block >> simp[abi_complex_prefix_cut_def, IS_PREFIX_APPEND]
QED

Theorem abi_complex_field_extends:
  !src offset cs. cs_extends cs (abi_complex_field_cut src offset cs)
Proof
  rpt gen_tac >> irule cs_extends_same_block >> simp[abi_complex_field_cut_def, IS_PREFIX_APPEND]
QED

Theorem compile_abi_child_extends =
  REWRITE_RULE [cs_appends_def] (CONJUNCT1 cs_appends_compile_abi_encode);

Theorem compile_abi_fields_extends =
  REWRITE_RULE [cs_appends_def] (cj 3 cs_appends_compile_abi_encode);

Theorem abi_complex_length_extends:
  !dyn_ptr cs op cs'. emit_op MLOAD [dyn_ptr] cs = (op,cs') ==> cs_extends cs cs'
Proof
  rpt gen_tac >> DISCH_TAC >>
  `cs_appends (emit_op MLOAD [dyn_ptr])` by simp[cs_appends_emit_helpers] >>
  drule_all cs_appends_result_extends >> simp[]
QED

Theorem abi_complex_fields_nil:
  !dst src source_offset head_offset dyn_ptr cs.
    compile_abi_encode_complex_elems dst src [] source_offset head_offset dyn_ptr cs = (Lit 0w,cs)
Proof
  simp[Once compile_abi_encode_child_def, comp_return_def]
QED

Theorem abi_complex_traversal_contains:
  !dst src fields source_offset head_offset dyn_ptr head_size cs ret mid op cs' func.
    compile_abi_encode_complex_elems dst src fields source_offset head_offset dyn_ptr
      (abi_complex_prefix_cut head_size cs) = (ret,mid) /\
    emit_op MLOAD [dyn_ptr] mid = (op,cs') /\ fn_has_code cs cs' func ==>
    fn_has_code cs (abi_complex_prefix_cut head_size cs) func /\
    fn_has_code (abi_complex_prefix_cut head_size cs) mid func /\ fn_has_code mid cs' func
Proof
  rpt gen_tac >> strip_tac >>
  `cs_extends cs (abi_complex_prefix_cut head_size cs)` by simp[abi_complex_prefix_extends] >>
  `cs_extends (abi_complex_prefix_cut head_size cs) mid` by
    (drule_all compile_abi_fields_extends >> simp[]) >>
  `cs_extends mid cs'` by (drule_all abi_complex_length_extends >> simp[]) >>
  `cs_extends (abi_complex_prefix_cut head_size cs) cs'` by
    (irule cs_extends_trans >> qexists_tac `mid` >> simp[]) >>
  mp_tac (Q.SPECL [`cs`, `abi_complex_prefix_cut head_size cs`, `cs'`, `func`] fn_has_code_split) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> strip_tac >>
  mp_tac (Q.SPECL [`abi_complex_prefix_cut head_size cs`, `mid`, `cs'`, `func`] fn_has_code_split) >> simp[]
QED

Theorem compile_abi_complex_single_dynamic:
  !dst src info mem_size cs op cs'.
    compile_abi_encode_to_buf dst src (AbiComplex [(info,32,mem_size,T)]) cs = (op,cs') <=>
    ?child_result mid.
      compile_abi_encode_child dst (Var (compiler_var_name (cs.cs_next_var + 1) 0)) info T 0
        (Var (compiler_var_name cs.cs_next_var 0))
        (abi_complex_field_cut src 0 (abi_complex_prefix_cut 32 cs)) = (child_result,mid) /\
      emit_op MLOAD [Var (compiler_var_name cs.cs_next_var 0)] mid = (op,cs')
Proof
  rpt gen_tac >>
  mp_tac (Q.SPECL [`dst`, `src`, `[(info,32,mem_size,T)]`, `cs`, `op`, `cs'`]
    compile_abi_complex_dynamic_split) >>
  simp_tac (srw_ss()) [compile_abi_complex_prefix_result, compile_abi_complex_fields_cons_split,
    emit_abi_complex_field_address, abi_complex_fields_nil, abi_complex_prefix_cut_def, PULL_EXISTS] >>
  metis_tac[]
QED

Theorem abi_complex_single_contains:
  !dst src info cs child_result mid op cs' func.
    compile_abi_encode_child dst (Var (compiler_var_name (cs.cs_next_var + 1) 0)) info T 0
      (Var (compiler_var_name cs.cs_next_var 0))
      (abi_complex_field_cut src 0 (abi_complex_prefix_cut 32 cs)) = (child_result,mid) /\
    emit_op MLOAD [Var (compiler_var_name cs.cs_next_var 0)] mid = (op,cs') /\
    fn_has_code cs cs' func ==>
    fn_has_code cs (abi_complex_prefix_cut 32 cs) func /\
    fn_has_code (abi_complex_prefix_cut 32 cs) (abi_complex_field_cut src 0 (abi_complex_prefix_cut 32 cs)) func /\
    fn_has_code (abi_complex_field_cut src 0 (abi_complex_prefix_cut 32 cs)) mid func /\
    fn_has_code mid cs' func
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `prefix = abi_complex_prefix_cut 32 cs` >>
  qabbrev_tac `addressed = abi_complex_field_cut src 0 prefix` >>
  `cs_extends cs prefix` by simp[Abbr`prefix`, abi_complex_prefix_extends] >>
  `cs_extends prefix addressed` by simp[Abbr`addressed`, abi_complex_field_extends] >>
  `cs_extends addressed mid` by (drule_all compile_abi_child_extends >> simp[]) >>
  `cs_extends mid cs'` by (drule_all abi_complex_length_extends >> simp[]) >>
  `cs_extends addressed cs'` by (irule cs_extends_trans >> qexists_tac `mid` >> simp[]) >>
  `cs_extends prefix cs'` by (irule cs_extends_trans >> qexists_tac `addressed` >> simp[]) >>
  mp_tac (Q.SPECL [`cs`, `prefix`, `cs'`, `func`] fn_has_code_split) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> strip_tac >>
  mp_tac (Q.SPECL [`prefix`, `addressed`, `cs'`, `func`] fn_has_code_split) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> strip_tac >>
  mp_tac (Q.SPECL [`addressed`, `mid`, `cs'`, `func`] fn_has_code_split) >> simp[]
QED
