(* TOP-LEVEL: a containing function includes the real prefix, recursive
   child (possibly containing loops), and suffix of dynamic child encoding. *)
Theory abiChildStructure
Ancestors
  abiChildCode abiEncoderStructure abiEncodeVarFlow
  abiStaticLoopCode compileEnv fragExec list rich_list arithmetic

Theorem abi_child_prefix_extends:
  !dst dyn_ptr head_offset cs.
    cs_extends cs (abi_child_prefix_cut dst dyn_ptr head_offset cs)
Proof
  rpt gen_tac >> irule cs_extends_same_block >> simp[abi_child_prefix_cut_def, IS_PREFIX_APPEND]
QED

Theorem abi_child_suffix_extends:
  !head_ptr tail_offset dyn_ptr child_len cs.
    cs_extends cs (abi_child_suffix_cut head_ptr tail_offset dyn_ptr child_len cs)
Proof
  rpt gen_tac >> irule cs_extends_same_block >> simp[abi_child_suffix_cut_def, IS_PREFIX_APPEND]
QED

Theorem compile_abi_child_dynamic_cuts:
  !dst src info head_offset dyn_ptr cs ret cs'.
    compile_abi_encode_child dst src info T head_offset dyn_ptr cs = (ret,cs') <=>
    ?mid.
      compile_abi_encode_to_buf (Var (compiler_var_name cs.cs_next_var 2)) src info
        (abi_child_prefix_cut dst dyn_ptr head_offset cs) = (ret,mid) /\
      cs' = abi_child_suffix_cut (Var (compiler_var_name cs.cs_next_var 0))
        (Var (compiler_var_name cs.cs_next_var 1)) dyn_ptr ret mid
Proof
  simp[compile_abi_child_dynamic_split, compile_abi_child_prefix_result, compile_abi_child_suffix_result,
    EQ_SYM_EQ]
QED

Theorem abi_child_dynamic_contains:
  !dst src info head_offset dyn_ptr cs child_len mid func.
    compile_abi_encode_to_buf (Var (compiler_var_name cs.cs_next_var 2)) src info
      (abi_child_prefix_cut dst dyn_ptr head_offset cs) = (child_len,mid) /\
    fn_has_code cs
      (abi_child_suffix_cut (Var (compiler_var_name cs.cs_next_var 0))
        (Var (compiler_var_name cs.cs_next_var 1)) dyn_ptr child_len mid) func ==>
    fn_has_code cs (abi_child_prefix_cut dst dyn_ptr head_offset cs) func /\
    fn_has_code (abi_child_prefix_cut dst dyn_ptr head_offset cs) mid func /\
    fn_has_code mid
      (abi_child_suffix_cut (Var (compiler_var_name cs.cs_next_var 0))
        (Var (compiler_var_name cs.cs_next_var 1)) dyn_ptr child_len mid) func
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `prefix = abi_child_prefix_cut dst dyn_ptr head_offset cs` >>
  qabbrev_tac `parent_end = abi_child_suffix_cut (Var (compiler_var_name cs.cs_next_var 0))
    (Var (compiler_var_name cs.cs_next_var 1)) dyn_ptr child_len mid` >>
  `cs_extends cs prefix` by simp[Abbr`prefix`, abi_child_prefix_extends] >>
  `cs_extends prefix mid` by (drule_all compile_abi_encode_extends >> simp[]) >>
  `cs_extends mid parent_end` by simp[Abbr`parent_end`, abi_child_suffix_extends] >>
  `cs_extends prefix parent_end` by
    (irule cs_extends_trans >> qexists_tac `mid` >> simp[]) >>
  mp_tac (Q.SPECL [`cs`, `prefix`, `parent_end`, `func`] fn_has_code_split) >>
  impl_tac >- (rpt conj_tac >> first_assum MATCH_ACCEPT_TAC) >> strip_tac >>
  mp_tac (Q.SPECL [`prefix`, `mid`, `parent_end`, `func`] fn_has_code_split) >> simp[]
QED
