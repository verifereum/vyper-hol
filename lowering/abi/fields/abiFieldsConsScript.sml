(* TOP-LEVEL: the actual field traversal composes its first field action
   with the remaining compiler action, including children with new blocks. *)
Theory abiFieldsCons
Ancestors
  abiFieldsContract abiFieldsStructure abiComplexCode abiComplexStructure
  abiStaticLoopCode compileEnv fragExec fragBlockPath venomState list pair arithmetic

Theorem abi_fields_step_contains:
  !dst src info is_dyn head_offset dyn_ptr rest source_offset mem_size head_size cs child_result mid ret cs' func.
    compile_abi_encode_child dst (Var (compiler_var_name cs.cs_next_var 0)) info is_dyn head_offset dyn_ptr
      (abi_complex_field_cut src source_offset cs) = (child_result,mid) /\
    compile_abi_encode_complex_elems dst src rest (source_offset + mem_size) (head_offset + head_size)
      dyn_ptr mid = (ret,cs') /\ fn_has_code cs cs' func ==>
    fn_has_code cs mid func /\ fn_has_code mid cs' func
Proof
  rpt gen_tac >> strip_tac >>
  `cs_extends cs (abi_complex_field_cut src source_offset cs)` by simp[abi_complex_field_extends] >>
  `cs_extends (abi_complex_field_cut src source_offset cs) mid` by
    (drule_all compile_abi_child_extends >> simp[]) >>
  `cs_extends mid cs'` by (drule_all compile_abi_fields_extends >> simp[]) >>
  `cs_extends cs mid` by
    (irule cs_extends_trans >> qexists_tac `abi_complex_field_cut src source_offset cs` >> simp[]) >>
  irule fn_has_code_split >> rpt conj_tac >> first_assum MATCH_ACCEPT_TAC
QED

Theorem abi_fields_contract_cons:
  !ctx func dst src dyn_ptr P info head_size mem_size is_dyn rest.
    abi_field_contract ctx func dst src dyn_ptr P (info,head_size,mem_size,is_dyn) rest /\
    abi_fields_contract ctx func dst src dyn_ptr P rest ==>
    abi_fields_contract ctx func dst src dyn_ptr P ((info,head_size,mem_size,is_dyn)::rest)
Proof
  rpt gen_tac >> simp_tac bool_ss [abi_fields_contract_def, abi_field_contract_def] >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_abi_encode_complex_elems _ _ (_::_) _ _ _ _ = _`
    (mp_tac o REWRITE_RULE [compile_abi_fields_cons_cuts]) >>
  disch_then (qx_choose_then `child_result` (qx_choose_then `mid` strip_assume_tac)) >>
  drule_all abi_fields_step_contains >> strip_tac >>
  qpat_x_assum `!source_offset head_offset cs child_result mid ss.
      compile_abi_encode_child _ _ _ _ _ _ _ = _ /\ _ ==> _`
    (qspecl_then [`source_offset`, `head_offset`, `cs`, `child_result`, `mid`, `ss`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  disch_then (qx_choose_then `child_out` strip_assume_tac) >>
  qpat_x_assum `!source_offset head_offset cs ret cs' ss.
      compile_abi_encode_complex_elems _ _ _ _ _ _ _ = _ /\ _ ==> _`
    (qspecl_then [`source_offset + mem_size`, `head_offset + head_size`, `mid`, `ret`, `cs'`, `child_out`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >>
  disch_then (qx_choose_then `out` strip_assume_tac) >>
  `fragment_path ctx func ss out` by
    (irule fragment_path_trans >> qexists_tac `child_out` >> simp[]) >>
  qexists_tac `out` >> simp_tac bool_ss [MAP, SUM, pairTheory.UNCURRY_DEF, ADD_ASSOC] >>
  asm_rewrite_tac []
QED
