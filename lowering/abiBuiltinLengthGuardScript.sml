(* Both exact-size and interval length guards match lower_abi_decode. *)
Theory abiBuiltinLengthGuard
Ancestors
  abiBuiltinBoundTests abiBuiltinPrefix abiDecoderDynamicLoopSetup abiDecoderReentry
  abiDecoderContract emitHelperProps exprLoweringProps compileEnv emitHelper
  venomExecSemantics venomState venomInst words arithmetic list rich_list

Definition abi_builtin_interval_guard_def:
  abi_builtin_interval_guard len min_size max_size =
    do ge_min <- abi_builtin_bound_test LT len (Lit (n2w min_size));
       le_max <- abi_builtin_bound_test GT len (Lit (n2w max_size));
       valid <- emit_op AND [ge_min;le_max];
       emit_void ASSERT [valid]
    od
End

Definition abi_builtin_length_guard_def:
  abi_builtin_length_guard len min_size max_size =
    if min_size = max_size then abi_builtin_eq_guard len (Lit (n2w min_size))
    else abi_builtin_interval_guard len min_size max_size
End

Theorem abi_builtin_length_guard_shape:
  abi_builtin_length_guard len min_size max_size st = ((),st') ==>
  st'.cs_next_var = st.cs_next_var + (if min_size = max_size then 1 else 5) /\
  st'.cs_next_id = st.cs_next_id + (if min_size = max_size then 2 else 6) /\
  st'.cs_blocks = st.cs_blocks /\ st'.cs_current_bb = st.cs_current_bb /\
  isPREFIX st.cs_current_insts st'.cs_current_insts /\ inst_extends st st' /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\ ~is_alloca_op i.inst_opcode)
    (emitted_insts st st')
Proof
  Cases_on `min_size = max_size` >>
  simp[abi_builtin_length_guard_def, abi_builtin_interval_guard_def,
    abi_builtin_eq_guard_def, abi_builtin_bound_test_def, comp_bind_def,
    comp_ignore_bind_def, comp_return_def, emit_op_def, emit_void_def, fresh_var_def, fresh_id_def, emit_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >> gvs[] >>
  simp[inst_extends_def, emitted_insts_def] >>
  pure_rewrite_tac [GSYM APPEND_ASSOC] >>
  simp[DROP_LENGTH_APPEND, IS_PREFIX_APPEND,
    is_terminator_def, is_alloca_op_def, mk_inst_def]
QED

Theorem abi_builtin_interval_guard:
  abi_builtin_interval_guard len min_size max_size st = ((),st') /\
  eval_operand len s = SOME (n2w cnt) /\ min_size <= cnt /\ cnt <= max_size /\
  max_size < dimword (:256) /\ abi_decoder_operand_live st.cs_next_var len /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  ?t. abi_builtin_prefix st st' limit_st s t
Proof
  simp_tac bool_ss [abi_builtin_interval_guard_def, comp_bind_def, LET_THM] >>
  pairarg_tac >> strip_tac >> gvs[] >> rpt (pairarg_tac >> gvs[]) >>
  rename1 `abi_builtin_bound_test LT len (Lit (n2w min_size)) st = (ge,c1)` >>
  rename1 `abi_builtin_bound_test GT len (Lit (n2w max_size)) c1 = (le,c2)` >>
  rename1 `emit_op AND [ge;le] c2 = (valid,c3)` >>
  imp_res_tac abi_builtin_bound_test_shape >>
  imp_res_tac emitted_insts_emit_op >> imp_res_tac emitted_insts_emit_void >>
  `c1.cs_next_var <= limit_st.cs_next_var /\ c2.cs_next_var <= limit_st.cs_next_var /\
   c3.cs_next_var <= limit_st.cs_next_var /\ min_size < dimword (:256) /\ cnt < dimword (:256)`
    by decide_tac >>
  mp_tac (Q.INST [`opc` |-> `LT`, `lhs` |-> `len`, `rhs` |-> `Lit (n2w min_size)`,
    `a` |-> `n2w cnt:bytes32`, `b` |-> `n2w min_size:bytes32`, `out` |-> `ge`, `st'` |-> `c1`]
    abi_builtin_bound_test) >>
  impl_tac >- asm_simp_tac (srw_ss()) [eval_operand_def, w2n_n2w] >> strip_tac >>
  rename1 `abi_builtin_prefix st c1 limit_st s s1` >>
  `eval_operand len s1 = SOME (n2w cnt) /\ fresh_vars_wrt limit_st s1` by
    fs[abi_builtin_prefix_def, abi_decoder_address_frame_def] >>
  mp_tac (Q.INST [`opc` |-> `GT`, `lhs` |-> `len`, `rhs` |-> `Lit (n2w max_size)`,
    `a` |-> `n2w cnt:bytes32`, `b` |-> `n2w max_size:bytes32`, `out` |-> `le`,
    `st` |-> `c1`, `st'` |-> `c2`, `s` |-> `s1:venom_state`] abi_builtin_bound_test) >>
  impl_tac >- asm_simp_tac (srw_ss()) [eval_operand_def, w2n_n2w] >> strip_tac >>
  rename1 `abi_builtin_prefix c1 c2 limit_st s1 s2` >>
  `abi_builtin_prefix st c2 limit_st s s2` by
    (irule abi_builtin_prefix_chain >> qexistsl_tac [`c1`, `s1`] >> simp[]) >>
  `eval_operand ge s2 = SOME 1w /\ fresh_vars_wrt limit_st s2` by
    fs[abi_builtin_prefix_def, abi_decoder_address_frame_def] >>
  mp_tac (Q.INST [`opc` |-> `AND`, `lhs` |-> `ge`, `rhs` |-> `le`, `out` |-> `valid`,
    `a` |-> `1w:bytes32`, `b` |-> `1w:bytes32`, `w` |-> `1w:bytes32`,
    `st` |-> `c2`, `st'` |-> `c3`, `s` |-> `s2:venom_state`] abi_builtin_emit_binary) >>
  impl_tac >- asm_simp_tac (srw_ss()) [WORD_AND_IDEM] >> strip_tac >>
  rename1 `abi_builtin_prefix c2 c3 limit_st s2 t` >>
  `abi_builtin_prefix st c3 limit_st s t` by
    (irule abi_builtin_prefix_chain >> qexistsl_tac [`c2`, `s2`] >> simp[]) >>
  `fresh_vars_wrt limit_st t` by fs[abi_builtin_prefix_def] >>
  `abi_builtin_prefix c3 st' limit_st t t` by
    (irule abi_builtin_assert >> asm_simp_tac bool_ss [] >>
     qexistsl_tac [`valid`, `1w:bytes32`] >> simp[]) >>
  qexists_tac `t` >> irule abi_builtin_prefix_chain >>
  qexistsl_tac [`c3`, `t`] >> simp[]
QED

Theorem abi_builtin_length_guard:
  abi_builtin_length_guard len min_size max_size st = ((),st') /\
  eval_operand len s = SOME (n2w cnt) /\ min_size <= cnt /\ cnt <= max_size /\
  max_size < dimword (:256) /\ abi_decoder_operand_live st.cs_next_var len /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  ?t. abi_builtin_prefix st st' limit_st s t
Proof
  Cases_on `min_size = max_size` >>
  asm_simp_tac bool_ss [abi_builtin_length_guard_def] >> strip_tac
  >- (`cnt = min_size` by decide_tac >>
      mp_tac (Q.INST [`lhs` |-> `len`, `rhs` |-> `Lit (n2w min_size)`,
        `v` |-> `n2w cnt:bytes32`] abi_builtin_eq_guard) >>
      asm_simp_tac (srw_ss()) [eval_operand_def]) >>
  drule_all abi_builtin_interval_guard >> simp[]
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_BUILTIN_LENGTH_GUARD_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI builtin length guard not kernel closed: " ^ n)
  end) (DB.thms "abiBuiltinLengthGuard");
