Theory wordArgsPtr
Ancestors
  bodyPtrDefs bodyPtrPreds exprSimWordArgs exprSimProps loweringPosts
  compileEnv loweringStateRelDefs ptrDiscipline venomState exprLoweringProps
  list finite_map freshWrites gasSummaryComposePtr fragGasPathPtr
  vyperInterpreter vyperState gasCount exprSimCalldataSlice

Theorem ghost_kept_at_refl:
  ghost_kept_at lo cenv es sa G tn s G tn
Proof
  simp[ghost_kept_at_def]
QED

Theorem ghost_kept_refl:
  ghost_kept cenv es sa G tn s G tn
Proof
  simp[ghost_kept_def]
QED

Theorem ghost_kept_operand:
  ghost_kept cenv es sa G0 tn0 s0 G tn /\
  (!x. op = Var x ==> not_fresh_at sa x) ==>
  op_taint tn op = op_taint tn0 op
Proof
  Cases_on `op` >> simp[op_taint_def, ghost_kept_def] >>
  metis_tac[op_taint_def]
QED

Theorem word_operand_frame:
  wb_frame cenv es es' sa s0 s /\ ghost_kept cenv es sa G0 tn0 s0 G tn /\
  (!x. op = Var x ==> not_fresh_at sa x) /\ (!l. op <> Label l) /\
  eval_operand op s0 = SOME w ==>
  eval_operand op s = SOME w /\ op_taint tn op = op_taint tn0 op
Proof
  strip_tac >> conj_tac
  >- (Cases_on `op` >> gvs[eval_operand_def] >> metis_tac[wb_frame_vars]) >>
  irule ghost_kept_operand >> metis_tac[]
QED

Theorem word_operands_frame:
  wb_frame cenv es es' sa s0 s /\ ghost_kept cenv es sa G0 tn0 s0 G tn /\
  EVERY (\op. (!x. op = Var x ==> not_fresh_at sa x) /\ (!l. op <> Label l)) ops /\
  eval_operands ops s0 = SOME ws /\
  EVERY (\op. op_taint tn0 op = {}) ops ==>
  eval_operands ops s = SOME ws /\ EVERY (\op. op_taint tn op = {}) ops
Proof
  qid_spec_tac `ws` >> Induct_on `ops` >>
  simp[eval_operands_def] >> rpt strip_tac >>
  gvs[AllCaseEqs()] >>
  drule_all word_operand_frame >> strip_tac >>
  gvs[]
QED

Theorem ghost_kept_trans:
  ghost_kept cenv es0 sa G0 tn0 s0 G1 tn1 /\
  ghost_kept cenv es1 sb G1 tn1 s1 G2 tn2 /\
  sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
           FLOOKUP s1.vs_allocas aid = SOME b) /\
  (!n b sz. local_region cenv es0.scopes s0 n b sz <=>
            local_region cenv es1.scopes s1 n b sz) ==>
  ghost_kept cenv es0 sa G0 tn0 s0 G2 tn2
Proof
  simp[ghost_kept_def] >> rpt strip_tac
  >- (`not_fresh_at sb x` by metis_tac[not_fresh_at_mono] >>
      res_tac >> gvs[])
  >- (`not_fresh_at sb x` by metis_tac[not_fresh_at_mono] >>
      res_tac >> gvs[])
  >- (`aid < sb.cs_next_id` by decide_tac >>
      `FLOOKUP s1.vs_allocas aid = SOME (off,sz)` by metis_tac[] >>
      `i IN tn1.t_mem` by
        (qpat_x_assum `!aid off sz i. FLOOKUP s1.vs_allocas aid = _ /\ _ ==> _`
          irule >> metis_tac[]) >>
      qpat_x_assum `!aid off sz i. FLOOKUP s0.vs_allocas aid = _ /\ _ ==> _`
        irule >> metis_tac[]) >>
  metis_tac[]
QED

Theorem wb_frame_local_regions:
  stmt_state_rel H ctx func cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  wb_frame cenv es es' sa s0 s1 ==>
  (!n b sz. local_region cenv es.scopes s0 n b sz <=>
            local_region cenv es1.scopes s1 n b sz)
Proof
  strip_tac >>
  `local_ptrs_rel func cenv es.scopes s0` by
    gvs[stmt_state_rel_def, state_rel_def] >>
  `!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
          lookup_var x s1 = SOME w` by metis_tac[wb_frame_vars] >>
  metis_tac[local_region_frame, local_region_frame_fwd]
QED

Theorem ghost_kept_wb_trans:
  stmt_state_rel H ctx func cenv cx es0 s0 /\ local_ptrs_reserved cenv sa /\
  MAP FDOM es0.scopes = MAP FDOM es1.scopes /\
  wb_frame cenv es0 es' sa s0 s1 /\
  sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id /\
  ghost_kept cenv es0 sa G0 tn0 s0 G1 tn1 /\
  ghost_kept cenv es1 sb G1 tn1 s1 G2 tn2 ==>
  ghost_kept cenv es0 sa G0 tn0 s0 G2 tn2
Proof
  strip_tac >> drule_all wb_frame_local_regions >> strip_tac >>
  irule ghost_kept_trans >>
  gvs[wb_frame_def] >> metis_tac[]
QED

(* ghost_kept_trans at a low-memory bound lo. *)
Theorem ghost_kept_at_trans:
  ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1 /\
  ghost_kept_at lo cenv es1 sm G1 tn1 s1 G2 tn2 /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
           FLOOKUP s1.vs_allocas aid = SOME b) /\
  (!n b sz. local_region cenv es1.scopes s1 n b sz <=>
            local_region cenv es.scopes s0 n b sz) ==>
  ghost_kept_at lo cenv es sa G0 tn0 s0 G2 tn2
Proof
  simp[ghost_kept_at_def] >> rpt strip_tac
  >- (`not_fresh_at sm x` by (gvs[not_fresh_at_def] >> decide_tac) >> metis_tac[])
  >- (`not_fresh_at sm x` by (gvs[not_fresh_at_def] >> decide_tac) >> metis_tac[])
  >- (`i IN tn1.t_mem` suffices_by
        (strip_tac >>
         qpat_x_assum `!aid off sz i. FLOOKUP s0.vs_allocas aid = _ /\ _ ==> _`
           (qspecl_then [`aid`,`off`,`sz`,`i`] mp_tac) >>
         impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
         disch_then ACCEPT_TAC) >>
      qpat_x_assum `!aid off sz i. FLOOKUP s1.vs_allocas aid = _ /\ _ ==> _` irule >>
      conj_tac >- (qexistsl_tac [`aid`,`off`,`sz`] >> simp[] >> metis_tac[]) >> simp[])
  >- (`i IN tn1.t_mem` suffices_by
        (strip_tac >>
         qpat_x_assum `!n b sz i. local_region cenv es.scopes s0 n b sz /\ _ ==> _`
           (qspecl_then [`n`,`b`,`sz`,`i`] mp_tac) >>
         impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
         disch_then ACCEPT_TAC) >>
      qpat_x_assum `!n b sz i. local_region cenv es1.scopes s1 n b sz /\ _ ==> _` irule >>
      conj_tac >- simp[] >> qexistsl_tac [`b`,`n`,`sz`] >> simp[] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem ghost_kept_at_wb_trans:
  !lo cenv es sa G0 tn0 s0 G1 tn1 es1 sm G2 tn2 s1 H ctx func cx es'.
  ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1 /\
  ghost_kept_at lo cenv es1 sm G1 tn1 s1 G2 tn2 /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  stmt_state_rel H ctx func cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\ wb_frame cenv es es' sa s0 s1 ==>
  ghost_kept_at lo cenv es sa G0 tn0 s0 G2 tn2
Proof
  rpt gen_tac >> strip_tac >>
  drule_all wb_frame_local_regions >> strip_tac >>
  irule ghost_kept_at_trans >>
  qexistsl_tac [`G1`,`es1`,`s1`,`sm`,`tn1`] >> simp[] >>
  gvs[wb_frame_def] >> metis_tac[]
QED

Theorem eval_exprs_nil_marked_ptr:
  ~s.vs_halted ==>
  gas_marked_exec_ptr D (ctx,func) PG (eval_exprs cx []) (es,s,G,tn)
    [] (INL []) es G tn (OK s)
Proof
  simp[gas_marked_exec_ptr_def, Once evaluate_def, return_def,
       gas_path_ptr_rules]
QED

Theorem eval_exprs_cons_marked_ptr:
  gas_marked_exec_ptr D (ctx,func) PG
    (bind (eval_expr cx e) (read_result cx)) (es,s,G0,tn0)
    left (INL v) mid G1 tn1 (OK t) /\
  gas_marked_exec_ptr D (ctx,func) PG
    (bind (eval_exprs cx args) (\vs. return (v::vs)))
    (mid with gas_obs := [],t,G1,tn1) right res fin G tn r ==>
  gas_marked_exec_ptr D (ctx,func) PG (eval_exprs cx (e::args))
    (es,s,G0,tn0) (left ++ right) res fin G tn r
Proof
  rewrite_tac[eval_exprs_cons_action] >> strip_tac >>
  irule gas_marked_exec_ptr_bind_normal >> metis_tac[]
QED

Theorem eval_exprs_cons_exception_ptr:
  gas_marked_exec_ptr D (ctx,func) PG
    (bind (eval_expr cx e) (read_result cx)) (es,s,G0,tn0)
    marks (INR exc) fin G tn r ==>
  gas_marked_exec_ptr D (ctx,func) PG (eval_exprs cx (e::args))
    (es,s,G0,tn0) marks (INR exc) fin G tn r
Proof
  rewrite_tac[eval_exprs_cons_action] >>
  metis_tac[gas_marked_exec_ptr_bind_exception]
QED

Theorem body_exprs_ptr_ok_tail:
  body_exprs_ptr_ok cx (e::args) /\
  bind (eval_expr cx e) (read_result cx) es = (INL v, es1) ==>
  body_exprs_ptr_ok cx args
Proof
  simp[body_exprs_ptr_ok_def, bind_def] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem precompile_two_operand_entry_rebase:
  stmt_state_rel H ctx fn cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  MAP FDOM ee.scopes = MAP FDOM ee'.scopes /\
  sa.cs_next_var <= s1.cs_next_var /\ sa.cs_next_id <= s1.cs_next_id /\
  s1.cs_next_var <= sm.cs_next_var /\ s1.cs_next_id <= sm.cs_next_id /\
  expr_post H ctx fn cenv cx a es sa s1 s0 ee va opa t /\
  expr_post H ctx fn cenv cx b ee s1 sm t ee' vb opb t' /\
  ghost_kept cenv es sa G0 tn0 s0 G1 tn1 /\
  ghost_kept cenv ee s1 G1 tn1 t G2 tn2 /\
  vv_post H ctx fn cenv cx e ee' sm sb t' fin tv vv u /\
  ghost_kept cenv ee' sm G2 tn2 t' Gf tnf /\
  (~expr_has_effect e ==> ~expr_has_effect a /\ ~expr_has_effect b) ==>
  vv_post H ctx fn cenv cx e es sa sb s0 fin tv vv u /\
  ghost_kept cenv es sa G0 tn0 s0 Gf tnf
Proof
  strip_tac >>
  `wb_frame cenv es ee sa s0 t` by metis_tac[expr_post_frame] >>
  `wb_frame cenv ee ee' s1 t t'` by metis_tac[expr_post_frame] >>
  `wb_frame cenv es ee' sa s0 t'` by
    (irule wb_frame_trans >>
     qpat_assum `wb_frame _ ee _ s1 t t'` (irule_at Any) >> simp[] >> metis_tac[]) >>
  `sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id` by decide_tac >>
  `MAP FDOM es.scopes = MAP FDOM ee'.scopes` by metis_tac[] >>
  `ghost_kept cenv es sa G0 tn0 s0 G2 tn2` by
    (irule ghost_kept_wb_trans >>
     qpat_assum `ghost_kept _ ee s1 _ _ _ G2 tn2` (irule_at Any) >> simp[] >> metis_tac[]) >>
  reverse conj_tac >-
    (irule ghost_kept_wb_trans >>
     qpat_assum `ghost_kept _ ee' sm _ _ _ Gf tnf` (irule_at Any) >> simp[] >> metis_tac[]) >>
  `~expr_has_effect e ==> pure_frame cenv fn es sa s0 t'` by
    (strip_tac >>
     qpat_x_assum `~expr_has_effect e ==> _` drule >> strip_tac >>
     `pure_frame cenv fn es sa s0 t /\ pure_frame cenv fn ee s1 t t'` by
       metis_tac[exprSimWordArgsTheory.expr_post_pure_frame] >>
     qpat_x_assum `wb_frame cenv es ee sa s0 t`
       (strip_assume_tac o REWRITE_RULE [loweringPostsTheory.wb_frame_def]) >>
     qpat_x_assum `wb_frame cenv ee ee' s1 t t'`
       (strip_assume_tac o REWRITE_RULE [loweringPostsTheory.wb_frame_def]) >>
     match_mp_tac (Q.SPECL [`cenv`, `fn`, `es`, `ee`, `sa`, `s1`, `s0`, `t`, `t'`]
       exprSimPropsTheory.pure_frame_trans) >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >> decide_tac) >>
  irule vv_post_prefix_frame >>
  qpat_assum `vv_post _ _ _ _ _ _ ee' sm _ _ _ _ _ _` (irule_at Any) >>
  simp[] >> metis_tac[]
QED
