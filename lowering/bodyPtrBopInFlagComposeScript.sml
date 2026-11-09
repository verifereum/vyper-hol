Theory bodyPtrBopInFlagCompose
Ancestors bodyPtrBopInFlagOutcome bodyPtrBopInFlagPairRun
  bodyPtrBopContinuation bodyPtrBopPairCps bodyPtrBopParentPost
  bodyPtrBopEntry bodyPtrBopOperandContract bodyPtrDefs
  exprSimOperators exprBopSimProps gasExemptCert bodyPtrBopTypedSource
  emitHelperProps compileEnv localPtrsProps exprSimDefs list rich_list
  bodyPtrBopScalarDispatch bodyPtrBopAnchored freshWrites
  exprLoweringProps fragExec bodyPtrBopInFlagCertificate pred_set

Theorem membership_flag_parent_outcome:
  expr_body_pre cenv cx env (Builtin ann (Bop bop) [e1;e2]) es /\
  is_word_type (expr_type e1) /\ is_word_type (expr_type e2) /\
  bop_operand_entry d ctx func cenv cx (Builtin ann (Bop bop) [e1;e2])
    es ca cz op t0 G0 tn0 /\
  bop_operand_post d ctx func cenv cx e1 es ca c1 x t0 G0 tn0
    v1 es1 t1 G1 tn1 /\
  bop_operand_post d ctx func cenv cx e2 es1 c1 c2 y t1 G1 tn1
    v2 es2 t2 G2 tn2 /\
  (?gs. bind (eval_expr cx e1) (read_result cx) (es with gas_obs := gs) =
        (INL v1,es1)) /\
  (?gs. bind (eval_expr cx e2) (read_result cx) (es1 with gas_obs := gs) =
        (INL v2,es2)) /\
  (bop = In \/ bop = NotIn) /\ expr_type e2 = FlagT fid /\
  compile_binop bop x y (expr_type e1)
    (if bop = Exp then expr_int_literal e1 else NONE)
    (if bop = Exp then expr_int_literal e2 else NONE) c2 = (op,cz) /\
  cs_extends ca c1 /\ cs_extends c1 c2 /\
  ca.cs_next_var <= c1.cs_next_var /\ ca.cs_next_id <= c1.cs_next_id /\
  c1.cs_next_var <= c2.cs_next_var /\ c1.cs_next_id <= c2.cs_next_id /\
  (!z. x = Var z ==> not_fresh_at c1 z) /\ (!l. x <> Label l) /\
  (!z. y = Var z ==> not_fresh_at c2 z) /\
  es2.gas_obs = [] /\ ~t2.vs_halted ==>
  gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
    (\st. (bop_result cx ann bop [expr_type e1;expr_type e2] v1 v2 st,st))
    (es2,t2,G2,tn2)
    (\res ee G tn t. ?v. res = INL v /\
      bop_operand_post d ctx func cenv cx (Builtin ann (Bop bop) [e1;e2])
        es ca cz op t0 G0 tn0 v ee t G tn)
    (\res ee gt r. expr_exit res r)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule bop_pair_source_facts >>
  disch_then (qspecl_then [`v2`, `v1`, `es2`, `es1`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac >>
  drule_all bop_pair_word_inputs >> strip_tac >>
  `!z. x = Var z ==> not_fresh_at c2 z` by metis_tac[not_fresh_at_mono] >>
  `local_ptrs_reserved cenv c1 /\ local_ptrs_reserved cenv c2` by
    metis_tac[bop_operand_entry_def, local_ptrs_reserved_next_var] >>
  drule compile_binop_shape >> strip_tac >>
  `fn_has_code c2 cz func` by
    metis_tac[bop_operand_entry_def, fn_has_code_mid, cs_extends_refl, cs_extends_trans] >>
  `?B. bop_scalar_seq {z | not_fresh_at c2 z}
      ({x;y} UNION IMAGE Lit UNIV) (emitted_insts c2 cz) B /\
      cz.cs_current_insts = c2.cs_current_insts ++ emitted_insts c2 cz /\
      same_blocks c2 cz /\ op IN B` by
    (drule membership_flag_scalar_certificate >>
     disch_then (drule_at (Pat `compile_binop _ _ _ _ _ _ _ = _`)) >>
     disch_then (qspecl_then [`{z | not_fresh_at c2 z}`,
       `{x;y} UNION IMAGE Lit UNIV`] mp_tac) >> simp[] >> metis_tac[]) >>
  `?bb. lookup_block t2.vs_current_bb func.fn_blocks = SOME bb /\
       isPREFIX (emitted_insts c2 cz) (DROP t2.vs_inst_idx bb.bb_instructions)` by
    (irule bop_suffix_placement >> gvs[bop_operand_post_def] >>
     qexistsl_tac [`c2`, `cz`] >> simp[]) >>
  `ghost_inv d cenv cx es2 G2 tn2 t2` by gvs[bop_operand_post_def] >>
  drule membership_flag_suffix_outcome_ptr >>
  disch_then (drule_at (Pat `compile_binop _ _ _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `ghost_inv _ _ _ es2 _ _ _`)) >>
  disch_then irule >> simp[] >>
  conj_tac >- metis_tac[bop_operand_entry_def, not_fresh_at_mono] >>
  conj_tac >- metis_tac[bop_operand_entry_def, not_fresh_at_mono] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `t2.vs_current_bb = cz.cs_current_bb /\
       LENGTH (emitted_insts c2 cz) + t2.vs_inst_idx = LENGTH cz.cs_current_insts` by
        (gvs[bop_operand_post_def, same_blocks_def] >> simp[]) >>
      drule_all bop_scalar_parent_success >> simp[]) >>
  reverse conj_tac >- metis_tac[bop_operand_entry_def] >>
  drule_all membership_flag_pair_run >> simp[]
QED

Theorem membership_flag_pair_outcome_ptr:
  lower_value compile_expr cenv ty1 e1 ca = (x,c1) /\
  lower_value compile_expr cenv ty2 e2 c1 = (y,c2) /\
  compile_binop bop x y (expr_type e1)
    (if bop = Exp then expr_int_literal e1 else NONE)
    (if bop = Exp then expr_int_literal e2 else NONE) c2 = (op,cz) /\
  body_inv tops ctx cenv cx /\ body_exprs_ptr_ok cx [e1;e2] /\
  expr_body_pre cenv cx env (Builtin ann (Bop bop) [e1;e2]) es /\
  is_word_type (expr_type e1) /\ is_word_type (expr_type e2) /\
  bop_operand_entry d ctx func cenv cx (Builtin ann (Bop bop) [e1;e2])
    es ca cz op t0 G0 tn0 /\
  (bop = In \/ bop = NotIn) /\ expr_type e2 = FlagT fid /\
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
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule expr_body_pre_bop >> strip_tac >> irule (BETA_RULE (Q.INST [`next` |->
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
  conj_tac >- (rpt gen_tac >> strip_tac >>
    qpat_assum `expr_type e2 = FlagT fid` (fn th => pure_rewrite_tac[GSYM th]) >>
    irule membership_flag_parent_outcome >>
    simp[] >> conj_tac >- metis_tac[] >>
    qexistsl_tac [`G1`, `c1`, `c2`, `es1`, `s1`, `tn1`, `x`, `y`] >>
    simp[] >> metis_tac[]) >>
  conj_tac >- (rpt gen_tac >> strip_tac >> conj_tac
    >- (rpt strip_tac >> irule gas_exempt_cert_error_value >> simp[]) >>
    rpt strip_tac >> irule gas_exempt_cert_bind_value >>
    goal_assum (drule_at Any) >> simp[]) >>
  conj_tac >- (rpt gen_tac >> strip_tac >> conj_tac
    >- (irule (INST_TYPE [alpha |-> ``:operand``] bop_operand_entry_next) >> simp[] >>
        conj_tac >- metis_tac[bop_typed_source_witness] >>
        goal_assum (drule_at (Pat `bop_operand_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
        qexistsl_tac [`cz`, `op`, `Builtin ann (Bop bop) [e1;e2]`] >> simp[]) >>
    metis_tac[]) >>
  conj_tac >- metis_tac[bop_typed_source_witness] >>
  irule (INST_TYPE [alpha |-> ``:operand``] bop_operand_entry_prefix) >> simp[] >>
  conj_tac >- metis_tac[] >>
  qexistsl_tac [`cz`, `op`, `Builtin ann (Bop bop) [e1;e2]`] >>
  simp[] >> metis_tac[cs_extends_trans]
QED
