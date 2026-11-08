Theory typedWordArgsSimPtr
Ancestors
  typedWordArgsReadyPtr typedWordArgsPostPtr exprSimPrecompiles
  exprSimWordArgs gasSummaryComposePtr gasContext exprSimDefs
  fragExec bodyPtrDefs exprLoweringProps list gasOutcomeMarkedPtr argsTailPtr fragGasSeqPtr vyperState

Theorem typed_args_ptr_head_admissible:
  typed_args_ready ctx func cenv cx arg_ty Inv (e::args) /\ Inv es /\
  (!es gs. Inv es ==> Inv (es with gas_obs := gs)) ==>
  gas_admissible (do r <- eval_expr cx e; read_result cx r od) expr_res_ok es
Proof
  rewrite_tac[gas_admissible_def] >> rpt strip_tac >>
  `Inv (es with gas_obs := gs)` by metis_tac[] >>
  drule_all typed_args_ready_head >> metis_tac[]
QED

Theorem typed_args_ptr_head_marked_facts:
  typed_args_ready ctx func cenv cx arg_ty Inv (e::args) /\ Inv es /\
  (!es gs. Inv es ==> Inv (es with gas_obs := gs)) /\
  gas_marked_exec_ptr D (ctx,func) PG
    (do r <- eval_expr cx e; read_result cx r od)
    (es,s0,G0,tn0) marks (INL v) mid G tn (OK t) /\
  ptr_args_ready d ctx PG func cenv cx arg_ty Inv (e::args) ==>
  ~t.vs_halted /\ Inv (mid with gas_obs := []) /\
  typed_args_ready ctx func cenv cx arg_ty Inv args /\
  ptr_args_ready d ctx PG func cenv cx arg_ty Inv args /\
  MAP FDOM es.scopes = MAP FDOM mid.scopes
Proof
  strip_tac >>
  `~t.vs_halted` by
    (fs[gas_marked_exec_ptr_def] >>
     metis_tac[gas_path_ptr_ok_not_halted]) >>
  `Inv (es with gas_obs := gas_explicit marks s0.vs_gas_readings)` by
    metis_tac[] >>
  `((do r <- eval_expr cx e; read_result cx r od)
      (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
      (INL v,mid with gas_obs := []))` by
    (fs[gas_marked_exec_ptr_def] >>
     first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  `MAP FDOM es.scopes = MAP FDOM mid.scopes` by
    (drule forced_eval_expr_preserves_scopes_dom >> simp[]) >>
  drule_all typed_args_ready_head >> strip_tac >>
  drule_all typed_args_ready_tail >>
  drule_all ptr_args_ready_tail >> metis_tac[]
QED


Theorem typed_args_ptr_head_outcome_facts:
  typed_args_ready ctx func cenv cx arg_ty Inv (e::args) /\ Inv es /\
  (!es gs. Inv es ==> Inv (es with gas_obs := gs)) /\
  ptr_args_ready d ctx PG func cenv cx arg_ty Inv (e::args) /\
  gas_outcome_ptr D tops (ctx,func) PG
    (do r <- eval_expr cx e; read_result cx r od) (es,s0,G0,tn0) Q R ==>
  gas_outcome_ptr D tops (ctx,func) PG
    (do r <- eval_expr cx e; read_result cx r od) (es,s0,G0,tn0)
    (\rr ee G tn t. Q rr ee G tn t /\ ~t.vs_halted /\
      (!v. rr = INL v ==>
        Inv ee /\ typed_args_ready ctx func cenv cx arg_ty Inv args /\
        ptr_args_ready d ctx PG func cenv cx arg_ty Inv args /\
        MAP FDOM es.scopes = MAP FDOM ee.scopes)) R
Proof
  strip_tac >> irule gas_outcome_ptr_marked_conseq >>
  qexists_tac `Q` >> reverse conj_tac >- first_assum ACCEPT_TAC >>
  rpt strip_tac >> simp[] >> conj_tac
  >- (fs[gas_marked_exec_ptr_def] >> metis_tac[gas_path_ptr_ok_not_halted]) >>
  rpt strip_tac >>
  gvs[] >> drule_all typed_args_ptr_head_marked_facts >> simp[]
QED

Theorem lower_typed_args_sim_ptr:
  !args d ctx PG func cenv cx arg_ty Inv es sa xs sb s0 G0 tn0.
    typed_args_ready ctx func cenv cx arg_ty Inv args /\
    ptr_args_ready d ctx PG func cenv cx arg_ty Inv args /\ Inv es /\
    (!es gs. Inv es ==> Inv (es with gas_obs := gs)) /\
    wb_args_shape cenv arg_ty args /\
    lower_word_args cenv arg_ty args sa = (xs,sb) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\
    ~cenv.ce_is_ctor /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    stmt_state_rel ctx func cenv cx es s0 /\
    ghost_inv d cenv cx es G0 tn0 s0 /\ ~s0.vs_halted /\
    s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
      (eval_exprs cx args) (es,s0,G0,tn0)
      (\rr ee G tn t. ?vs. rr = INL vs /\
        typed_args_post_ptr d ctx func cenv cx es sa s0 G0 tn0 ee args xs vs G tn t /\
        t.vs_current_bb = sb.cs_current_bb /\
        t.vs_inst_idx = LENGTH sb.cs_current_insts)
      (\rr ee ghosts r. wb_args_exit rr r)
Proof
  Induct
  >- (rpt strip_tac >> gvs[lower_word_args_nil] >>
      irule lower_typed_args_nil_sim_ptr >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  gvs[lower_word_args_cons] >>
  `cs_extends sa s1 /\ sa.cs_next_var <= s1.cs_next_var /\
   sa.cs_next_id <= s1.cs_next_id /\
   (!z. x = Var z ==> not_fresh_at s1 z) /\ (!l. x <> Label l)` by
    (fs[wb_args_shape_def] >> metis_tac[MEM]) >>
  drule wb_args_shape_tail >> strip_tac >>
  drule_all lower_word_args_shape_ready >> strip_tac >>
  drule_all fn_has_code_split >> strip_tac >>
  drule_all ptr_args_ready_head >>
  rewrite_tac[expr_sim_ptr_def] >>
  disch_then (qspecl_then [`sa`,`s1`,`x`,`s0`,`G0`,`tn0`] mp_tac) >>
  impl_tac
  >- (simp[] >>
      drule_all typed_args_ptr_head_admissible >>
      simp[SF ETA_ss]) >>
  strip_tac >>
  drule_all (typed_args_ptr_head_outcome_facts |> SIMP_RULE (srw_ss()) [SF ETA_ss]) >>
  qpat_x_assum `gas_outcome_ptr _ _ _ _ _ _ _ (\res ee gt r. expr_exit res r)` kall_tac >>
  disch_tac >>
  rewrite_tac[eval_exprs_cons_action] >>
  irule gas_outcome_ptr_bind >> rpt conj_tac
  >- suspend "certificate_head"
  >- suspend "certificate_tail" >>
  suspend "head_bind"
QED

Resume lower_typed_args_sim_ptr[head_bind]:
  irule gas_outcome_ptr_conseq >>
  goal_assum (drule_at Any) >>
  qpat_x_assum `gas_outcome_ptr _ _ _ _ _ _ _ _` kall_tac >>
  conj_tac
  >- (rpt strip_tac >> gvs[] >>
      drule_all typed_args_ready_head >> strip_tac >>
      `?tv. evaluate_type (get_tenv cx) (expr_type h) = SOME tv` by
        metis_tac[optionTheory.IS_SOME_EXISTS] >>
      `local_ptrs_reserved cenv s1` by
        (irule local_ptrs_reserved_next_var >> metis_tac[]) >>
      irule lower_typed_args_cons_tail_ptr >>
      goal_assum (drule_at Any) >>
      simp[] >> qexists_tac `s1` >> simp[] >>
      first_x_assum irule >>
      drule expr_post_state >> disch_tac >> simp[] >>
      conj_tac
      >- (rpt strip_tac >> irule stmtFragPtrTheory.not_fresh_at_mono >>
          metis_tac[]) >>
      conj_tac
      >- (rpt strip_tac >> irule stmtFragPtrTheory.not_fresh_at_mono >>
          metis_tac[]) >>
      qexistsl_tac [`Inv`,`arg_ty`] >> simp[]) >>
  rpt strip_tac >> Cases_on `res` >> gvs[expr_exit_def, wb_args_exit_def]
QED

Resume lower_typed_args_sim_ptr[certificate_head]:
  rpt strip_tac >>
  qpat_x_assum `!d ctx PG func cenv cx arg_ty Inv es sa xs sb s0 G0 tn0. _` kall_tac >>
  qpat_x_assum `gas_outcome_ptr _ _ _ _ _ _ _ _` kall_tac >>
  gvs[ignore_bind_def, bind_assoc, bind_return] >>
  irule (wb_args_tail_exempt_cert |> GEN_ALL |> SIMP_RULE (srw_ss())
    [eval_exprs_cons_action, ignore_bind_def, bind_assoc, bind_return]) >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Resume lower_typed_args_sim_ptr[certificate_tail]:
  rpt strip_tac >>
  qpat_x_assum `!d ctx PG func cenv cx arg_ty Inv es sa xs sb s0 G0 tn0. _` kall_tac >>
  qpat_x_assum `gas_outcome_ptr _ _ _ _ _ _ _ _` kall_tac >>
  gvs[ignore_bind_def, bind_assoc, bind_return] >>
  irule (wb_args_head_exempt_cert |> GEN_ALL |> SIMP_RULE (srw_ss())
    [eval_exprs_cons_action, ignore_bind_def, bind_assoc, bind_return]) >>
  metis_tac[]
QED

Finalise lower_typed_args_sim_ptr
