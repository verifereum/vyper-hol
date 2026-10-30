(* TOP-LEVEL: old aggregate operands avoid the address temporary and the
   following child interval. The produced source pointer is safe for every
   generated name of that child, independently of its recursive shape. *)
Theory abiFieldReady
Ancestors
  abiFieldAddress typedArrayLoopNames abiStaticLoopCode
  compileEnv venomState list words arithmetic

Theorem abi_field_input_names:
  !arg_op var_base child_count.
    EVERY (\name. arg_op <> Var name) (compiler_var_names var_base (child_count + 1)) ==>
    arg_op <> Var (compiler_var_name var_base 0) /\
    EVERY (\name. arg_op <> Var name) (compiler_var_names (var_base + 1) child_count)
Proof
  rpt gen_tac >> DISCH_TAC >> conj_tac
  >- (mp_tac (Q.SPECL [`arg_op`, `var_base`, `child_count + 1`, `0`] compiler_var_names_avoid_index) >> simp[]) >>
  mp_tac (Q.SPECL [`arg_op`, `var_base`, `child_count + 1`, `1`, `child_count`]
    compiler_var_names_avoid_segment) >> simp[]
QED

Theorem abi_field_source_names:
  !var_base child_count.
    EVERY (\name. Var (compiler_var_name var_base 0) <> Var name)
      (compiler_var_names (var_base + 1) child_count)
Proof
  rpt gen_tac >> irule compiler_var_names_before >> simp[]
QED

Theorem abi_field_address_inputs:
  !dst dyn_ptr cs source_offset src_addr ss dst_addr dyn_addr child_count.
    eval_operand dst ss = SOME dst_addr /\ eval_operand dyn_ptr ss = SOME dyn_addr /\
    EVERY (\name. dst <> Var name /\ dyn_ptr <> Var name)
      (compiler_var_names cs.cs_next_var (child_count + 1)) ==>
    let addressed = abi_field_address_state cs source_offset src_addr ss in
    eval_operand dst addressed = SOME dst_addr /\ eval_operand dyn_ptr addressed = SOME dyn_addr /\
    eval_operand (Var (compiler_var_name cs.cs_next_var 0)) addressed = SOME (src_addr + n2w source_offset) /\
    EVERY (\name. dst <> Var name /\ dyn_ptr <> Var name /\ Var (compiler_var_name cs.cs_next_var 0) <> Var name)
      (compiler_var_names (cs.cs_next_var + 1) child_count)
Proof
  rpt gen_tac >> simp_tac bool_ss [LET_THM] >> strip_tac >>
  qpat_assum `EVERY _ _` (strip_assume_tac o SIMP_RULE bool_ss [EVERY_CONJ]) >>
  mp_tac (Q.SPECL [`dst`, `cs.cs_next_var`, `child_count`] abi_field_input_names) >>
  impl_tac >- first_assum MATCH_ACCEPT_TAC >> strip_tac >>
  mp_tac (Q.SPECL [`dyn_ptr`, `cs.cs_next_var`, `child_count`] abi_field_input_names) >>
  impl_tac >- first_assum MATCH_ACCEPT_TAC >> strip_tac >>
  asm_simp_tac (srw_ss()) [abi_field_address_state_operand, abi_field_address_state_value,
    abi_field_source_names, EVERY_CONJ]
QED
