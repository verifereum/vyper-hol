(* A common-endpoint accumulator for evaluated internal-call arguments. *)
Theory bodyIntCallHeldArgs
Ancestors
  bodyIntCallHeldFrame bodyIntCallSourceFrame bodyIntCallProducerInterface
  bodyIntCallArgType exprOperandVar exprSimSource loweringPosts pair
  exprSimCalldataSlice valueEncodingTyping list

Definition intcall_held_args_def:
  intcall_held_args ce cx a sm es s H <=>
    EVERY (\(ty,raw,vv).
      vv_holds ce cx ty raw vv es s /\
      vv_at ce cx ty a sm es raw vv s /\
      intcall_vv_provenance ce cx ty a sm es raw vv s /\
      vv_storage_live cx vv es s /\
      (!v tv. read_result cx raw es = (INL v,es) /\
              evaluate_type (get_tenv cx) ty = SOME tv ==>
              val_wf tv v /\ value_has_type tv v) /\
      (!x. vv_operand vv = Var x ==> not_fresh_at sm x)) H
End

Theorem intcall_held_args_nil[simp]:
  intcall_held_args ce cx a sm es s []
Proof
  simp[intcall_held_args_def]
QED

Theorem intcall_held_args_append[simp]:
  intcall_held_args ce cx a sm es s (H ++ hs) <=>
  intcall_held_args ce cx a sm es s H /\
  intcall_held_args ce cx a sm es s hs
Proof
  simp[intcall_held_args_def]
QED

Theorem intcall_held_args_member:
  intcall_held_args ce cx a sm es s H /\ MEM (ty,raw,vv) H ==>
  vv_holds ce cx ty raw vv es s /\
  vv_at ce cx ty a sm es raw vv s /\
  intcall_vv_provenance ce cx ty a sm es raw vv s /\
  vv_storage_live cx vv es s /\
  (!v tv. read_result cx raw es = (INL v,es) /\
          evaluate_type (get_tenv cx) ty = SOME tv ==>
          val_wf tv v /\ value_has_type tv v) /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x)
Proof
  simp[intcall_held_args_def, EVERY_MEM] >> strip_tac >>
  first_x_assum (qspec_then `(ty,raw,vv)` mp_tac) >> simp[]
QED

Theorem intcall_held_args_outcomes[simp]:
  intcall_held_args ce cx a sm
    (es with <|outcomes := os; gas_obs := gs|>) s H <=>
  intcall_held_args ce cx a sm es s H
Proof
  simp[intcall_held_args_def, EVERY_MEM, FORALL_PROD,
       intcall_held_source_outcomes, read_result_outcomes_iff]
QED

Theorem intcall_held_args_singleton:
  expr_body_pre ce cx env e es /\ ~expr_has_effect e /\
  eval_expr cx e es = (INL raw,ee) /\
  compile_expr ce (expr_type e) e sm = (vv,sn) /\
  local_ptrs_reserved ce sm /\
  vv_post ctx func ce cx e es sm sn s ee raw vv t /\
  intcall_vv_provenance ce cx (expr_type e) sm sn ee raw vv t ==>
  intcall_held_args ce cx sm sn ee t [(expr_type e,raw,vv)]
Proof
  strip_tac >>
  drule_all exprSimSourceTheory.expr_body_pre_runtime_typed >> strip_tac >>
  `!x. vv_operand vv = Var x ==> not_fresh_at sn x` by
    metis_tac[CONJUNCT1 compiler_compile_var] >>
  drule effect_free_post_value_type >> strip_tac >>
  gvs[intcall_held_args_def, vv_post_def] >>
  metis_tac[cj 1 value_has_type_val_wf]
QED

Theorem intcall_vv_provenance_start_mono:
  a.cs_next_id <= sm.cs_next_id /\
  intcall_vv_provenance ce cx ty sm sn es raw vv s ==>
  intcall_vv_provenance ce cx ty a sn es raw vv s
Proof
  simp[intcall_vv_provenance_def] >> strip_tac >>
  qx_gen_tac `op` >> disch_tac >>
  qpat_x_assum `!op. _` (qspec_then `op` mp_tac) >>
  simp[] >> disch_tac >> rpt gen_tac >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  qexists_tac `w` >> simp[]
  >- (disj1_tac >> qexistsl_tac [`aid`, `b`, `sz`] >> simp[] >>
      first_assum ACCEPT_TAC)
  >- (disj2_tac >> disj2_tac >> disj1_tac >>
      qexistsl_tac [`n`, `b`, `sz`] >> simp[]) >>
  disj2_tac >> disj2_tac >> disj2_tac >>
  rename1 `lookup_var rootp s = SOME rootw` >>
  qexistsl_tac [`n`, `sz`, `entry`, `rootp`, `rootw`, `k`] >> simp[]
QED

Theorem intcall_held_args_start_mono:
  a.cs_next_id <= sm.cs_next_id /\
  intcall_held_args ce cx sm sn es s H ==>
  intcall_held_args ce cx a sn es s H
Proof
  simp[intcall_held_args_def, EVERY_MEM, FORALL_PROD] >>
  rpt strip_tac >> first_x_assum drule >> strip_tac >>
  simp[] >> metis_tac[vv_at_start_mono, intcall_vv_provenance_start_mono]
QED
