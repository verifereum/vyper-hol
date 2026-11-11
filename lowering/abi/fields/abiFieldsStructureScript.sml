(* TOP-LEVEL: arbitrary field traversal exposes the actual address ADD,
   child encoder and suffix, with containing code spans and SSA bounds. *)
Theory abiFieldsStructure
Ancestors
  abiComplexCode abiComplexStructure abiEncodeVarFlow compileVarFlow
  compileEnv fragExec list pair arithmetic

Theorem compile_abi_fields_cons_cuts:
  !dst src info head_size mem_size is_dyn rest source_offset head_offset dyn_ptr cs ret cs'.
    compile_abi_encode_complex_elems dst src ((info,head_size,mem_size,is_dyn)::rest)
      source_offset head_offset dyn_ptr cs = (ret,cs') <=>
    ?child_result mid.
      compile_abi_encode_child dst (Var (compiler_var_name cs.cs_next_var 0)) info is_dyn head_offset dyn_ptr
        (abi_complex_field_cut src source_offset cs) = (child_result,mid) /\
      compile_abi_encode_complex_elems dst src rest (source_offset + mem_size) (head_offset + head_size)
        dyn_ptr mid = (ret,cs')
Proof
  simp[compile_abi_complex_fields_cons_split, emit_abi_complex_field_address]
QED

Theorem abi_fields_cons_contains:
  !dst src info is_dyn head_offset dyn_ptr rest source_offset mem_size head_size cs child_result mid ret cs' func.
    compile_abi_encode_child dst (Var (compiler_var_name cs.cs_next_var 0)) info is_dyn head_offset dyn_ptr
      (abi_complex_field_cut src source_offset cs) = (child_result,mid) /\
    compile_abi_encode_complex_elems dst src rest (source_offset + mem_size) (head_offset + head_size)
      dyn_ptr mid = (ret,cs') /\
    fn_has_code cs cs' func ==>
    fn_has_code cs (abi_complex_field_cut src source_offset cs) func /\
    fn_has_code (abi_complex_field_cut src source_offset cs) mid func /\
    fn_has_code mid cs' func
Proof
  rpt gen_tac >> strip_tac >> qabbrev_tac `addressed = abi_complex_field_cut src source_offset cs` >>
  `cs_extends cs addressed` by simp[Abbr`addressed`, abi_complex_field_extends] >>
  `cs_extends addressed mid` by (drule_all compile_abi_child_extends >> simp[]) >>
  `cs_extends mid cs'` by (drule_all compile_abi_fields_extends >> simp[]) >>
  `cs_extends addressed cs'` by (irule cs_extends_trans >> qexists_tac `mid` >> simp[]) >>
  mp_tac (Q.SPECL [`cs`, `addressed`, `cs'`, `func`] fn_has_code_split) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> strip_tac >>
  mp_tac (Q.SPECL [`addressed`, `mid`, `cs'`, `func`] fn_has_code_split) >> simp[]
QED

Theorem compile_abi_child_next_var:
  !dst src info is_dyn head_offset dyn_ptr cs op cs'.
    compile_abi_encode_child dst src info is_dyn head_offset dyn_ptr cs = (op,cs') ==>
    cs.cs_next_var <= cs'.cs_next_var
Proof
  rpt gen_tac >> DISCH_TAC >>
  mp_tac (Q.SPECL [`dst`, `src`, `info`, `is_dyn`, `head_offset`, `dyn_ptr`]
    (cj 1 compiler_vars_mono_abi_encode)) >>
  DISCH_TAC >> drule_all compiler_vars_mono_result >> simp[]
QED

Theorem compile_abi_fields_next_var:
  !dst src fields source_offset head_offset dyn_ptr cs op cs'.
    compile_abi_encode_complex_elems dst src fields source_offset head_offset dyn_ptr cs = (op,cs') ==>
    cs.cs_next_var <= cs'.cs_next_var
Proof
  rpt gen_tac >> DISCH_TAC >>
  mp_tac (Q.SPECL [`dst`, `src`, `fields`, `source_offset`, `head_offset`, `dyn_ptr`]
    (cj 3 compiler_vars_mono_abi_encode)) >>
  DISCH_TAC >> drule_all compiler_vars_mono_result >> simp[]
QED
