Theory bodyPtrBopPairCompose
Ancestors
  bodyPtrBopPairCps bodyPtrBopContinuation bodyPtrBopEntry
  exprSimOperators exprBopSimProps gasExemptCert bodyPtrBopSource emitHelperProps compileEnv

Theorem bop_word_pair_outcome_ptr:
  lower_value compile_expr cenv ty1 e1 ca = (x,c1) /\
  lower_value compile_expr cenv ty2 e2 c1 = (y,c2) /\
  compile_binop bop x y (expr_type e1)
    (if bop = Exp then expr_int_literal e1 else NONE)
    (if bop = Exp then expr_int_literal e2 else NONE) c2 = (op,cz) /\
  body_inv tops ctx cenv cx /\ body_exprs_ptr_ok cx [e1;e2] /\
  expr_body_pre cenv cx env (Builtin ann (Bop bop) [e1;e2]) es /\
  word_value_type (expr_type e1) /\ word_value_type (expr_type e2) /\
  bop_operand_entry d ctx func cenv cx (Builtin ann (Bop bop) [e1;e2])
    es ca cz op t0 G0 tn0 /\
  bop <> In /\ bop <> NotIn /\
  cs_extends ca c1 /\ cs_extends c1 c2 /\ cs_extends c2 cz /\
  ca.cs_next_var <= c1.cs_next_var /\ ca.cs_next_id <= c1.cs_next_id /\
  c1.cs_next_var <= c2.cs_next_var /\ c1.cs_next_id <= c2.cs_next_id /\
  (!z. x = Var z ==> not_fresh_at c1 z) /\ (!l. x <> Label l) /\
  (!z. y = Var z ==> not_fresh_at c2 z) ==>
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
    (bind (bind (eval_expr cx e1) (read_result cx)) (\v1.
     bind (bind (eval_expr cx e2) (read_result cx)) (\v2.
       \st. (bop_result cx ann bop [expr_type e1;expr_type e2] v1 v2 st,st))))
    (es,t0,G0,tn0)
    (\res ee G tn t. ?v. res = INL v /\
      bop_operand_post d ctx func cenv cx (Builtin ann (Bop bop) [e1;e2])
        es ca cz op t0 G0 tn0 v ee t G tn)
    (\res ee gt r. expr_exit res r)
Proof
  strip_tac >> drule expr_body_pre_bop >> strip_tac >> irule (BETA_RULE (Q.INST [`next` |->
    `\v1 v2 st. (bop_result cx ann bop [expr_type e1;expr_type e2] v1 v2 st,st)`]
    (INST_TYPE [alpha |-> ``:value``] bop_pair_outcome_ptr))) >> simp[] >>
  conj_tac >- (rpt strip_tac >> irule gas_exempt_cert_error_value >> simp[]) >>
  conj_tac >- (rpt strip_tac >> irule gas_exempt_cert_bind_value >>
    goal_assum (drule_at Any) >> simp[]) >>
  qexistsl_tac [`\rr ee. ?gs. bind (eval_expr cx e1) (read_result cx)
      (es with gas_obs := gs) = (rr,ee)`,
    `\v1 es1 rr ee. ?gs. bind (eval_expr cx e2) (read_result cx)
      (es1 with gas_obs := gs) = (rr,ee)`,
    `cenv`, `d`, `env`, `ca`, `c1`, `c2`, `tops`, `ty1`, `ty2`, `x`, `y`] >>
  simp[] >> conj_tac >- metis_tac[] >>
  conj_tac >- (rpt gen_tac >> strip_tac >> irule bop_scalar_parent_outcome >>
    simp[] >> conj_tac >- metis_tac[] >>
    qexistsl_tac [`G1`, `c1`, `c2`, `es1`, `s1`, `tn1`, `x`, `y`] >>
    simp[] >> metis_tac[]) >>
  conj_tac >- (rpt gen_tac >> strip_tac >> conj_tac
    >- (rpt strip_tac >> irule gas_exempt_cert_error_value >> simp[]) >>
    rpt strip_tac >> irule gas_exempt_cert_bind_value >>
    goal_assum (drule_at Any) >> simp[]) >>
  conj_tac >- (rpt gen_tac >> strip_tac >> conj_tac
    >- (irule (INST_TYPE [alpha |-> ``:operand``] bop_operand_entry_next) >> simp[] >>
        conj_tac >- metis_tac[bop_word_source_witness] >>
        goal_assum (drule_at (Pat `bop_operand_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
        qexistsl_tac [`cz`, `op`, `Builtin ann (Bop bop) [e1;e2]`] >> simp[]) >>
    metis_tac[]) >>
  conj_tac >- metis_tac[bop_word_source_witness] >>
  irule (INST_TYPE [alpha |-> ``:operand``] bop_operand_entry_prefix) >> simp[] >>
  conj_tac >- metis_tac[] >>
  qexistsl_tac [`cz`, `op`, `Builtin ann (Bop bop) [e1;e2]`] >>
  simp[] >> metis_tac[cs_extends_trans]
QED
