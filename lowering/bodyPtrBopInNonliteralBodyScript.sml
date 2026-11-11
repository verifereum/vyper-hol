Theory bodyPtrBopInNonliteralBody
Ancestors bodyPtrBopInRuntimeContinuation bodyPtrBopInSourceTyping
  bodyPtrBopInCallHaystackResidual
  exprSimBopRestWordFacts exprBopLowering exprLowering compileEnv
  exprSimOperators bodyPtrPreds exprPtrUnwrap exprSimWordArgs wordArgsPtr
  bodyPtrBopInRuntimeCompiler bodyPtrBopInHeaderCode exprSimBopRestWordBasics
  exprSimSource exprLoweringProps fragExec freshWrites exprBopSimProps
  bodyPtrBopInMixed bodyPtrBopInMixedAdapter bodyPtrBopInSourceOrigin
  gasExemptCert bodyPtrDefs vyperState fragGasPathPtr gasSummaryComposePtr vyperAST
Libs pairLib

Theorem membership_nonliteral_lower_value:
  (bop = In \/ bop = NotIn) /\
  expr_type e2 = ArrayT et bd /\
  (!a t n elems. e2 <> Builtin a (MakeArray t n) elems) /\
  lower_value compile_expr cenv ty
    (Builtin ann (Bop bop) [e1;e2]) sa = (op,sb) ==>
  ?needle vv sc sm.
    lower_value compile_expr cenv (expr_type e1) e1 sa = (needle,sc) /\
    compile_expr cenv (expr_type e2) e2 sc = (vv,sm) /\
    compile_var_array_membership cenv needle vv (expr_type e2)
      (bop = In) sm = (op,sb)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all rest_word_nonliteral_dispatch >> disch_tac >>
  qpat_x_assum `lower_value _ _ _ _ _ = _` mp_tac >>
  simp[Once lower_value_def, comp_bind_def, compile_expr_bop] >>
  simp[Once (CONJUNCT1 (CONJUNCT2 compile_expr_raw_def)),
       lower_value_child_call] >>
  rpt (pairarg_tac >> gnvs[]) >>
  simp[as_stack_val_pair, unwrap_value_def, comp_return_def] >> strip_tac >>
  qpat_x_assum `as_stack_val _ _ = _` mp_tac >>
  qmatch_goalsub_abbrev_tac `as_stack_val _ tailcomp` >>
  Cases_on `tailcomp` >>
  simp[as_stack_val_pair] >> strip_tac >>
  gnvs[unwrap_value_def, comp_return_def, comp_bind_def, ETA_AX] >>
  rule_assum_tac (CONV_RULE (DEPTH_CONV ETA_CONV)) >>
  qexistsl_tac [`needle`,`arr_vv`,`st1`,`st2`] >> simp[]
QED

Theorem membership_mixed_post_frames:
  bop_operand_post d ctx fn cenv cx e1 es sa sc needle s0 G0 tn0
    v es1 s1 G1 tn1 /\
  membership_vv_post d ctx fn cenv cx e2 es1 sc sm vv s1 G1 tn1
    tv es2 s2 G2 tn2 /\
  stmt_state_rel ctx fn cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  sa.cs_next_var <= sc.cs_next_var /\ sa.cs_next_id <= sc.cs_next_id ==>
  wb_frame cenv es es2 sa s0 s2 /\
  ghost_kept cenv es sa G0 tn0 s0 G2 tn2
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  fs[bodyPtrBopOperandContractTheory.bop_operand_post_def,
     bodyPtrBopInVvContractTheory.membership_vv_post_def] >>
  `wb_frame cenv es es1 sa s0 s1` by metis_tac[expr_post_frame] >>
  `wb_frame cenv es1 es2 sc s1 s2` by
    (fs[loweringPostsTheory.vv_post_def, loweringPostsTheory.wb_frame_def] >>
     metis_tac[]) >>
  conj_tac
  >- (qspecl_then [`fn`, `cenv`, `cx`, `es`, `s0`, `sa`, `es1`, `es2`, `sc`, `s1`, `s2`,
                   `ctx`] mp_tac wb_frame_trans >> simp[]) >>
  mp_tac (Q.INST [`func` |-> `fn`, `es0` |-> `es`, `es'` |-> `es1`, `sb` |-> `sc`]
            ghost_kept_wb_trans) >> simp[]
QED

Theorem membership_nonliteral_tail_extends:
  ~cenv.ce_is_ctor /\
  compile_var_array_membership cenv needle vv (ArrayT et bd) isin sa = (op,sb) ==>
  cs_extends sa sb
Proof
  Cases_on `bd` >> strip_tac
  >- (gvs[rest_word_fixed_dispatch] >>
      drule membership_runtime_loop_extends >> simp[]) >>
  qpat_x_assum `compile_var_array_membership _ _ _ _ _ _ = _` mp_tac >>
  rewrite_tac[membership_dynamic_compile_split] >>
  pure_once_rewrite_tac[comp_bind_def] >> rewrite_tac[LET_THM] >>
  pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  rename1 `compile_array_membership_loop _ _ _ _ _ _ _ mid = _` >>
  `cs_extends sa mid` by
    (irule membership_runtime_header_extends >> goal_assum (drule_at Any)) >>
  drule membership_runtime_loop_extends >>
  metis_tac[cs_extends_trans]
QED


Theorem nonliteral_expr_sim_ptr:
  post_value_type cenv e2 = expr_type e2 /\
  expr_body_pre cenv cx env (Builtin ann (Bop bop) [e1;e2]) es /\
  (bop = In \/ bop = NotIn) /\ is_word_type (expr_type e1) /\
  expr_type e2 = ArrayT (expr_type e1) bd /\
  (!a t n elems. e2 <> Builtin a (MakeArray t n) elems) /\
  body_exprs_ptr_ok cx [e1;e2] /\ body_inv tops ctx cenv cx ==>
  expr_sim_ptr d ctx PG fn cenv cx ty (Builtin ann (Bop bop) [e1;e2]) es
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  rewrite_tac[expr_sim_ptr_def] >> rpt gen_tac >> strip_tac >>
  drule_all membership_nonliteral_lower_value >> strip_tac >>
  drule (cj 2 compile_expr_grows) >> strip_tac >>
  drule (cj 1 compile_expr_grows) >> strip_tac >>
  `cs_extends sm sb` by
    (irule membership_nonliteral_tail_extends >> gvs[] >> metis_tac[]) >>
  `cs_extends sc sb` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa sc fn /\ fn_has_code sc sm fn /\ fn_has_code sm sb fn` by
    metis_tac[fn_has_code_mid, cs_extends_trans, cs_extends_refl] >>
  `local_ptrs_reserved cenv sc /\ local_ptrs_reserved cenv sm` by
    metis_tac[local_ptrs_reserved_next_var] >>
  rewrite_tac[membership_source_bind] >>
  drule_at (Pat `lower_value _ _ _ _ _ = _`)
    (UNDISCH (SPEC_ALL membership_mixed_source_adapter)) >>
  disch_then drule >> disch_then irule >> simp[] >>
  conj_tac >- (rpt strip_tac >> irule gas_exempt_cert_error_value >> simp[]) >>
  conj_tac >- (rpt strip_tac >> irule gas_exempt_cert_bind_value >>
    goal_assum (drule_at Any) >> simp[]) >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  qexists_tac `d` >>
  conj_tac >- suspend "success" >>
  conj_tac >- suspend "exempt" >>
  suspend "entries"
QED

Resume nonliteral_expr_sim_ptr[exempt]:
  rpt gen_tac >> strip_tac >> conj_tac
  >- (rpt strip_tac >> irule gas_exempt_cert_error_result >>
      simp[ignore_bind_def]) >>
  rpt strip_tac >> irule gas_exempt_cert_bind_result >>
  goal_assum (drule_at Any) >> simp[]
QED
Resume nonliteral_expr_sim_ptr[entries]:
  drule expr_body_pre_bop >> strip_tac >>
  reverse conj_tac
  >- (simp[bodyPtrBopOperandContractTheory.bop_operand_entry_def] >>
      metis_tac[expr_body_pre_gas_admissible]) >>
  rpt gen_tac >> disch_tac >>
  `expr_sim_inv cenv cx env es1` by
    (irule (cj 1 membership_needle_origin_success) >> metis_tac[]) >>
  `expr_body_pre cenv cx env e2 es1` by metis_tac[] >>
  qpat_x_assum `bop = In \/ bop = NotIn` kall_tac >>
  fs[bodyPtrBopInVvContractTheory.membership_vv_entry_def,
     bodyPtrBopOperandContractTheory.bop_operand_post_def] >>
  simp[] >>
  rpt conj_tac
  >- metis_tac[not_fresh_at_mono]
  >- metis_tac[not_fresh_at_mono]
  >- (irule exprSimHypsTheory.expr_body_pre_vv_gas_admissible >> metis_tac[]) >>
  drule expr_post_state >> simp[]
QED
Resume nonliteral_expr_sim_ptr[success]:
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `vv_holds cenv cx (expr_type e2) tv vv es2 s2` by
    (qpat_assum `membership_vv_post _ _ _ _ _ e2 _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     rewrite_tac[bodyPtrBopInVvContractTheory.membership_vv_post_def,
                 loweringPostsTheory.vv_post_def] >>
     qpat_assum `post_value_type cenv e2 = _` (fn th => rewrite_tac[th]) >>
     rpt strip_tac >> first_assum ACCEPT_TAC) >>
  drule_all membership_mixed_origin_success >> strip_tac >> gnvs[] >>
  drule expr_body_pre_bop >> strip_tac >>
  drule_all expr_body_pre_lower_value_word_shape >> strip_tac >>
  `eval_operand needle s1 = SOME (typed_val_to_w256 tv' v1)` by
    (gnvs[bodyPtrBopOperandContractTheory.bop_operand_post_def,
       loweringPostsTheory.expr_post_def, loweringPostsTheory.expr_val_at_def,
       loweringPostsTheory.expr_val_rel_def] >> metis_tac[]) >>
  drule_all membership_mixed_word_post_kept >> strip_tac >>
  `op_prov G2 needle = NONE /\ op_taint tn2 needle = {}` by
    metis_tac[ptr_val_ok_def] >>
  `(!x. needle = Var x ==> not_fresh_at sm x) /\
   (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
   (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x)` by
    metis_tac[not_fresh_at_mono] >>
  drule_all membership_mixed_post_frames >> strip_tac >>
  `sa.cs_next_var <= sm.cs_next_var` by decide_tac >>
  `post_value_type cenv e2 = expr_type e2` by fs[] >>
  drule_all membership_array_continuation_summary_ptr >>
  disch_then (qspecl_then [`Unsigned 0`,`e1`,`PG`,`cx_dead cx`] assume_tac) >>
  drule membership_typed_read_continuation >> disch_then (fn th => rewrite_tac[th]) >>
  rewrite_tac[gas_outcome_ptr_def] >> qexists_tac `[]` >> disj1_tac >>
  irule gas_summary_ptr_at_conseq >> first_assum (irule_at (Pos last)) >>
  simp[expr_type_def, is_word_type_def] >> metis_tac[]
QED
Finalise nonliteral_expr_sim_ptr

Theorem membership_nonliteral_compile_stack:
  (bop = In \/ bop = NotIn) /\ expr_type e2 = ArrayT et bd /\
  (!a t n elems. e2 <> Builtin a (MakeArray t n) elems) ==>
  ?t op sb. compile_expr cenv ty (Builtin ann (Bop bop) [e1;e2]) sa =
    (StackValue t op,sb)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all rest_word_nonliteral_dispatch >> disch_tac >>
  simp[compile_expr_bop, Once (CONJUNCT1 (CONJUNCT2 compile_expr_raw_def)),
    lower_value_child_call] >>
  rpt (pairarg_tac >> gnvs[]) >>
  simp[as_stack_val_pair] >> metis_tac[]
QED

Theorem body_bop_in_nonliteral_word_ptr_ok:
  (bop = In \/ bop = NotIn) /\ is_word_type (expr_type e1) /\
  expr_type e2 = ArrayT (expr_type e1) bd /\
  (!a t n elems. e2 <> Builtin a (MakeArray t n) elems) /\
  body_exprs_ptr_ok cx [e1;e2] ==>
  body_expr_ptr_ok cx (Builtin ann (Bop bop) [e1;e2])
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  simp[body_expr_ptr_ok_def] >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `expr_sim_ptr d ctx PG func cenv cx ty (Builtin ann (Bop bop) [e1;e2]) es` by
    (Cases_on `post_value_type cenv e2 = expr_type e2`
     >- metis_tac[nonliteral_expr_sim_ptr]
     >- metis_tac[bop_in_nonliteral_call_haystack_ptr]) >>
  conj_tac >- simp[] >>
  irule expr_vv_sim_ptr_stack >> simp[] >>
  reverse conj_tac >- metis_tac[eval_expr_builtin_value] >>
  gen_tac >> irule membership_nonliteral_compile_stack >> metis_tac[]
QED
