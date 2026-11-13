(* Compiler and successful-source boundaries for pointer argument recursion. *)
Theory abiEncTuplePtrArgsContext
Ancestors
  abiEncodeArgsSim exprLoweringProps exprOperandVar freshWrites fragExec
  exprSimHypsDefs

Theorem abi_args_success_ready_ptr:
  abi_args_ready ctx func ce cx Inv (e::args) /\ Inv es /\
  (!s gs. Inv s ==> Inv (s with gas_obs := gs)) /\
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) = (INL v,es1) ==>
  Inv es1 /\ abi_args_ready ctx func ce cx Inv args /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  (~is_word_type (expr_type e) ==>
    ?tv. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
      value_has_type tv v /\ val_wf tv v /\
      type_memory_bytes ce (lowered_value_type ce e) = type_memory_size tv /\
      type_memory_size tv < 2 ** 64 /\
      type_memory_size tv + 64 < dimword (:256))
Proof
  strip_tac >>
  `Inv (es with gas_obs := gs)` by metis_tac[] >>
  drule_all abi_args_ready_head >> strip_tac >>
  `abi_args_ready ctx func ce cx Inv args` by metis_tac[abi_args_ready_tail] >>
  qpat_x_assum `!v es'. _ ==> Inv es' /\ _`
    (qspecl_then [`v`, `es1`] mp_tac) >> simp[] >>
  disch_then irule >> CONV_TAC (DEPTH_CONV ETA_CONV) >> first_assum ACCEPT_TAC
QED

Theorem abi_args_compile_uncaptured_ptr_context:
  compile_expr ce (expr_type e) e sa = (vv,mid) /\
  unwrap_value ce vv mid = (op,sm) /\
  compile_abi_encode_args compile_expr ce args sm = (ops,sb) /\
  fn_has_code sa sb func /\ local_ptrs_reserved ce sa ==>
  lower_value compile_expr ce (expr_type e) e sa = (op,sm) /\
  ci_mono sa mid /\ ci_mono mid sm /\ ci_mono sm sb /\ ci_mono sa sm /\
  fn_has_code sa sm func /\ fn_has_code sm sb func /\
  local_ptrs_reserved ce mid /\ local_ptrs_reserved ce sm /\
  (!x. op = Var x ==> not_fresh_at sm x)
Proof
  strip_tac >>
  `lower_value compile_expr ce (expr_type e) e sa = (op,sm)` by
    simp[exprLoweringTheory.lower_value_def, compileEnvTheory.comp_bind_def] >>
  `ci_mono sa mid` by metis_tac[compile_expr_ci_mono, pairTheory.SND] >>
  `ci_mono mid sm` by metis_tac[ci_mono_unwrap_value, pairTheory.SND] >>
  `ci_mono sm sb` by metis_tac[abi_args_compile_mono, pairTheory.SND] >>
  `ci_mono sa sm` by
    (gvs[ci_mono_def] >> metis_tac[compileEnvTheory.cs_extends_trans,
                                 arithmeticTheory.LESS_EQ_TRANS]) >>
  simp[] >>
  conj_tac >- (gvs[ci_mono_def] >> metis_tac[fn_has_code_split]) >>
  conj_tac >- (gvs[ci_mono_def] >> metis_tac[fn_has_code_split]) >>
  conj_tac >- metis_tac[local_ptrs_reserved_next_var, ci_mono_def] >>
  conj_tac >- metis_tac[local_ptrs_reserved_next_var, ci_mono_def] >>
  metis_tac[compile_lower_value_var]
QED

Theorem abi_args_compile_captured_ptr_context:
  compile_expr ce (expr_type e) e sa = (vv,mid) /\
  compile_materialize_vv ce (lowered_value_type ce e) vv mid = (op,sm) /\
  compile_abi_encode_args compile_expr ce args sm = (ops,sb) /\
  fn_has_code sa sb func /\ local_ptrs_reserved ce sa ==>
  ci_mono sa mid /\ ci_mono mid sm /\ ci_mono sm sb /\ ci_mono sa sm /\
  fn_has_code sa mid func /\ fn_has_code mid sm func /\ fn_has_code sm sb func /\
  local_ptrs_reserved ce mid /\ local_ptrs_reserved ce sm /\
  (!x. vv_operand vv = Var x ==> not_fresh_at mid x) /\
  (!x. op = Var x ==> not_fresh_at sm x) /\ (!l. op <> Label l)
Proof
  strip_tac >>
  `ci_mono sa mid` by metis_tac[compile_expr_ci_mono, pairTheory.SND] >>
  `ci_mono mid sm` by metis_tac[ci_mono_compile_materialize_vv, pairTheory.SND] >>
  `ci_mono sm sb` by metis_tac[abi_args_compile_mono, pairTheory.SND] >>
  `ci_mono sa sm` by
    (gvs[ci_mono_def] >> metis_tac[compileEnvTheory.cs_extends_trans,
                                 arithmeticTheory.LESS_EQ_TRANS]) >>
  `cs_extends sa mid /\ cs_extends mid sm /\ cs_extends sm sb` by gvs[ci_mono_def] >>
  `fn_has_code sa mid func /\ fn_has_code mid sm func /\ fn_has_code sm sb func` by
    metis_tac[fn_has_code_split, compileEnvTheory.cs_extends_trans] >>
  simp[] >>
  conj_tac >- metis_tac[local_ptrs_reserved_next_var, ci_mono_def] >>
  conj_tac >- metis_tac[local_ptrs_reserved_next_var, ci_mono_def] >>
  conj_tac >- metis_tac[compiler_compile_var] >>
  conj_tac >- metis_tac[compiler_materialize_vv_var] >>
  metis_tac[abi_args_materialize_not_label]
QED
