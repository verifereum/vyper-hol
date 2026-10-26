(* The exact comparison/test sequences used by ABI builtin length checks. *)
Theory abiBuiltinBoundTests
Ancestors
  abiBuiltinPrefix abiDecoderDynamicLoopSetup abiDecoderReentry abiDecoderContract
  emitHelperProps exprLoweringProps compileEnv emitHelper
  venomExecSemantics venomState venomInst words arithmetic list

Definition abi_builtin_bound_test_def:
  abi_builtin_bound_test opc lhs rhs =
    do bad <- emit_op opc [lhs;rhs];
       emit_op ISZERO [bad]
    od
End

Definition abi_builtin_eq_guard_def:
  abi_builtin_eq_guard lhs rhs =
    do valid <- emit_op EQ [lhs;rhs];
       emit_void ASSERT [valid]
    od
End

Theorem abi_builtin_bound_test_shape:
  abi_builtin_bound_test opc lhs rhs st = (out,st') ==>
  st'.cs_next_var = st.cs_next_var + 2 /\ st'.cs_next_id = st.cs_next_id + 2 /\
  abi_decoder_operand_live st'.cs_next_var out
Proof
  simp[abi_builtin_bound_test_def, comp_bind_def] >>
  pairarg_tac >> strip_tac >> gvs[] >> imp_res_tac emitted_insts_emit_op >>
  imp_res_tac abi_decoder_operand_live_emit >> simp[]
QED

Theorem abi_builtin_bound_test:
  abi_builtin_bound_test opc lhs rhs st = (out,st') /\
  ((opc = LT /\ w2n b <= w2n a) \/ (opc = GT /\ w2n a <= w2n b)) /\
  eval_operand lhs s = SOME a /\ eval_operand rhs s = SOME b /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  ?t. eval_operand out t = SOME 1w /\ abi_builtin_prefix st st' limit_st s t
Proof
  simp_tac bool_ss [abi_builtin_bound_test_def, comp_bind_def, LET_THM] >>
  pairarg_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >> gvs[] >>
  (rename1 `emit_op _ [lhs;rhs] st = (bad,middle)` >>
  imp_res_tac emitted_insts_emit_op >>
  `middle.cs_next_var <= limit_st.cs_next_var /\ st.cs_next_var <= middle.cs_next_var`
    by decide_tac >>
  drule (Q.INST [`w` |-> `0w:bytes32`] abi_builtin_emit_binary) >>
  disch_then (qspecl_then [`s:venom_state`, `limit_st`, `b:bytes32`, `a:bytes32`] mp_tac) >>
  impl_tac >- (asm_simp_tac bool_ss [] >> gvs[bool_to_word_def]) >> strip_tac >>
  rename1 `abi_builtin_prefix st middle limit_st s prepared` >>
  qpat_assum `abi_builtin_prefix _ _ _ _ _`
    (MAP_EVERY assume_tac o CONJUNCTS o PURE_REWRITE_RULE [abi_builtin_prefix_def]) >>
  drule_all abi_builtin_emit_iszero >> strip_tac >>
  rename1 `abi_builtin_prefix middle st' limit_st prepared t` >>
  drule_all abi_builtin_prefix_chain >> strip_tac >>
  qexists_tac `t` >> asm_simp_tac (srw_ss()) [bool_to_word_def])
QED

Theorem abi_builtin_eq_guard:
  abi_builtin_eq_guard lhs rhs st = ((),st') /\
  eval_operand lhs s = SOME v /\ eval_operand rhs s = SOME v /\
  st'.cs_next_var <= limit_st.cs_next_var /\ fresh_vars_wrt limit_st s ==>
  ?t. abi_builtin_prefix st st' limit_st s t
Proof
  simp_tac bool_ss [abi_builtin_eq_guard_def, comp_bind_def, LET_THM] >>
  pairarg_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >> gvs[] >>
  rename1 `emit_op EQ [lhs;rhs] st = (valid,middle)` >>
  imp_res_tac emitted_insts_emit_op >> imp_res_tac emitted_insts_emit_void >>
  `middle.cs_next_var <= limit_st.cs_next_var /\ st.cs_next_var <= middle.cs_next_var`
    by decide_tac >>
  mp_tac (Q.INST [`opc` |-> `EQ`, `out` |-> `valid`, `st'` |-> `middle`,
    `a` |-> `v:bytes32`, `b` |-> `v:bytes32`, `w` |-> `1w:bytes32`]
    abi_builtin_emit_binary) >>
  impl_tac >- asm_simp_tac (srw_ss()) [bool_to_word_def] >> strip_tac >>
  rename1 `abi_builtin_prefix st middle limit_st s t` >>
  `fresh_vars_wrt limit_st t` by fs[abi_builtin_prefix_def] >>
  `abi_builtin_prefix middle st' limit_st t t` by
    (irule abi_builtin_assert >> asm_simp_tac bool_ss [] >>
     qexistsl_tac [`valid`, `1w:bytes32`] >> simp[]) >>
  qexists_tac `t` >> irule abi_builtin_prefix_chain >>
  qexistsl_tac [`middle`, `t`] >> asm_simp_tac bool_ss []
QED

val () = List.app (fn (n,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th) in
    if null (Thm.hyp th) andalso null axioms andalso
       List.all (fn s => s = "DISK_THM") oracles then
      print ("ABI_BUILTIN_BOUND_TESTS_KERNEL_CLOSED " ^ n ^ "\n")
    else raise Fail ("ABI builtin bounds not kernel closed: " ^ n)
  end) (DB.thms "abiBuiltinBoundTests");
