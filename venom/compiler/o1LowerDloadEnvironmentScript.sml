(* Local factors shared by active and suspended LowerDload frames. *)
Theory o1LowerDloadEnvironment
Ancestors
  o1LowerDloadRelocationKernel o1LowerDloadOpaque ptrDiscipline
  unitShapeDefs irSupply venomState finite_map list option

Definition ld_env_agree_def:
  ld_env_agree sites fn H tn s t <=>
    (!v. MEM v (fn_ir_vars fn) ==>
      (IS_SOME (FLOOKUP s.vs_vars v) <=> IS_SOME (FLOOKUP t.vs_vars v))) /\
    (!v x y. MEM v (fn_ir_vars fn) /\ ~retpc_var fn v /\
      FLOOKUP s.vs_vars v = SOME x /\ FLOOKUP t.vs_vars v = SOME y ==>
      ld_value_agree sites (FLOOKUP H v) (op_taint tn (Var v)) x y)
End

Definition ld_params_agree_def:
  ld_params_agree sites HP s t <=>
    LENGTH s.vs_params = LENGTH t.vs_params /\
    (!k. k < LENGTH s.vs_params ==>
      ld_value_agree sites (if k < LENGTH HP then EL k HP else NONE) {}
        (EL k s.vs_params) (EL k t.vs_params))
End

Theorem ld_env_lookup_defined:
  ld_env_agree sites fn H tn s t /\ MEM v (fn_ir_vars fn) ==>
  (IS_SOME (FLOOKUP s.vs_vars v) <=> IS_SOME (FLOOKUP t.vs_vars v))
Proof
  simp[ld_env_agree_def] >> metis_tac[]
QED

Theorem ld_env_lookup_value:
  ld_env_agree sites fn H tn s t /\ MEM v (fn_ir_vars fn) /\
  ~retpc_var fn v /\ FLOOKUP s.vs_vars v = SOME x /\
  FLOOKUP t.vs_vars v = SOME y ==>
  ld_value_agree sites (FLOOKUP H v) (op_taint tn (Var v)) x y
Proof
  simp[ld_env_agree_def] >> metis_tac[]
QED

Theorem ld_env_initial:
  ld_env_agree FEMPTY fn FEMPTY tn s s
Proof
  simp[ld_env_agree_def, ld_value_agree_scalar, word_agree_except_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem ld_params_initial:
  ld_params_agree FEMPTY [] s s
Proof
  simp[ld_params_agree_def, ld_value_agree_scalar, word_agree_except_def]
QED

Theorem ld_env_fresh_target:
  ld_env_agree sites fn H tn s t /\ ~MEM fresh (fn_ir_vars fn) ==>
  ld_env_agree sites fn H tn s (update_var fresh value t)
Proof
  simp[ld_env_agree_def, update_var_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> metis_tac[]
QED

Theorem ld_params_element:
  ld_params_agree sites HP s t /\ k < LENGTH s.vs_params ==>
  ld_value_agree sites (if k < LENGTH HP then EL k HP else NONE) {}
    (EL k s.vs_params) (EL k t.vs_params)
Proof
  simp[ld_params_agree_def]
QED

Theorem ld_env_operand_defined:
  ld_env_agree sites fn H tn s t /\ s.vs_labels = t.vs_labels /\
  (!v. op = Var v ==> MEM v (fn_ir_vars fn)) ==>
  (IS_SOME (eval_operand op s) <=> IS_SOME (eval_operand op t))
Proof
  Cases_on `op` >> simp[eval_operand_def, lookup_var_def] >>
  rpt strip_tac >> drule_all ld_env_lookup_defined >> simp[]
QED

Theorem ld_env_operand_value:
  ld_env_agree sites fn H tn s t /\ s.vs_labels = t.vs_labels /\
  (!v. op = Var v ==> MEM v (fn_ir_vars fn)) /\
  (!v. op = Var v ==> ~retpc_var fn v) /\ eval_operand op s = SOME x ==>
  ?y. eval_operand op t = SOME y /\
      ld_value_agree sites (op_prov H op) (op_taint tn op) x y
Proof
  Cases_on `op` >> simp[eval_operand_def, lookup_var_def, op_prov_def, op_taint_def]
  >- (rpt strip_tac >> gvs[] >>
      simp[ld_value_agree_scalar, word_agree_except_def])
  >- (rpt strip_tac >>
      drule_all ld_env_lookup_defined >>
      Cases_on `FLOOKUP t.vs_vars s'` >> simp[] >>
      drule_all ld_env_lookup_value >> simp[op_taint_def]) >>
  rpt strip_tac >> gvs[] >> simp[ld_value_agree_scalar, word_agree_except_def]
QED

Theorem ld_env_operand_clean:
  ld_env_agree sites fn H tn s t /\ s.vs_labels = t.vs_labels /\
  (!v. op = Var v ==> MEM v (fn_ir_vars fn)) /\
  (!v. op = Var v ==> ~retpc_var fn v) /\
  op_prov H op = NONE /\ op_taint tn op = {} ==>
  eval_operand op s = eval_operand op t
Proof
  strip_tac >>
  `IS_SOME (eval_operand op s) <=> IS_SOME (eval_operand op t)` by
    (drule_all ld_env_operand_defined >> simp[]) >>
  Cases_on `eval_operand op s`
  >- (Cases_on `eval_operand op t` >> gvs[]) >>
  drule_all ld_env_operand_value >> strip_tac >> gvs[] >>
  drule ld_value_agree_clean >> simp[]
QED

Theorem ld_env_operands_defined:
  ld_env_agree sites fn H tn s t /\ s.vs_labels = t.vs_labels /\
  (!v. MEM (Var v) ops ==> MEM v (fn_ir_vars fn)) ==>
  (IS_SOME (eval_operands ops s) <=> IS_SOME (eval_operands ops t))
Proof
  strip_tac >> irule eval_operands_defined_iff >> rpt strip_tac >>
  irule ld_env_operand_defined >> simp[] >>
  qexistsl_tac [`H`, `fn`, `sites`, `tn`] >> simp[] >> metis_tac[]
QED
