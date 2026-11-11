(* Counted typed operands followed by a same-endpoint builtin continuation. *)
Theory bodyPtrWordBuiltinsArgsCompose
Ancestors bodyPtrWordBuiltinsModularContinue bodyPtrWordBuiltinsWitnessCompose
  typedWordArgsSimPtr typedWordArgsFactsPtr typedWordArgsReadyPtr bodyWordArgsReady
  typedWordArgsPostPtr
  exprSimWordBuiltins exprSimWordArgs exprSimPrecompiles exprSimSource
  bodyPtrPreds bodyPtrDefs bodySim exprSimHypsDefs loweringPosts exprSimDefs
  exprSimProps exprLoweringProps fragGasFresh freshWrites compileEnv
  gasSummaryComposePtr gasExemptCert vyperInterpreter vyperState vyperAST
  vyperTypeSystem vyperValue vyperTyping valueEncoding stmtFragPtr list fragExec
  exprSimUnopComposeProps exprSimUnopProps

Theorem word_args_compose_sim_ptr:
  body_inv tops ctx cenv cx /\ expr_body_pre cenv cx env (Builtin ann bt args) es /\
  body_exprs_ptr_ok cx args /\ EVERY (\e. expr_type e = BaseT (UintT 256)) args /\
  bt <> Len /\ bt <> Env MsgGas /\ ~precompile_builtin bt /\
  builtin_args_length_ok bt (LENGTH args) /\ is_word_type ann /\
  (!sa sb op. lower_value compile_expr cenv ty (Builtin ann bt args) sa = (op,sb) ==>
     ?xs sm. lower_word_args cenv (\e. ty) args sa = (xs,sm) /\ code xs sm = (op,sb)) /\
  (!xs. straight_fresh (code xs)) /\
  (!sa sm sb xs op s0 G0 tn0 ee t G tn vs.
    code xs sm = (op,sb) /\
    wb_args_post ctx func cenv cx es sa s0 ee xs vs t /\
    LIST_REL (\e v. value_has_type (BaseTV (UintT 256)) v) args vs /\
    EVERY (\x. !z. x = Var z ==> not_fresh_at sm z) xs /\
    EVERY (\x. op_taint tn x = {}) xs /\
    fn_has_code sm sb func /\ local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
    ~ctx_has_dalloca ctx /\ ~t.vs_halted /\
    t.vs_current_bb = sm.cs_current_bb /\ t.vs_inst_idx = LENGTH sm.cs_current_insts /\
    sa.cs_next_var <= sm.cs_next_var /\ ghost_inv d cenv cx ee G tn t /\
    ghost_kept cenv es sa G0 tn0 s0 G tn /\ ee.gas_obs = [] /\
    (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
    (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) ==>
    gas_outcome_ptr (cx_dead cx) (cx_tops cx) (ctx,func) PG
      (\ee. (builtin_result cx ee.accounts ann bt (MAP expr_type args) vs,ee)) (ee,t,G,tn)
      (\res fin G' tn' u. ?v. res = INL v /\
         expr_post ctx func cenv cx (Builtin ann bt args) es sa sb s0 fin v op u /\
         u.vs_current_bb = sb.cs_current_bb /\ u.vs_inst_idx = LENGTH sb.cs_current_insts /\
         ghost_inv d cenv cx fin G' tn' u /\ ptr_val_ok cx ann v op G' tn' u /\
         ghost_kept cenv es sa G0 tn0 s0 G' tn')
      (\res fin gt r. expr_exit res r)) ==>
  expr_sim_ptr d ctx PG func cenv cx ty (Builtin ann bt args) es
Proof
  strip_tac >>
  `!e s. MEM e args /\ expr_sim_inv cenv cx env s ==>
     expr_body_pre cenv cx env e s /\ is_word_type (expr_type e)` by suspend "pre" >>
  `typed_args_ready ctx func cenv cx (\e. ty) (expr_sim_inv cenv cx env) args` by
    (irule body_word_args_ready >> metis_tac[]) >>
  `ptr_args_ready d ctx PG func cenv cx (\e. ty) (expr_sim_inv cenv cx env) args` by
    (irule body_exprs_ptr_ok_ready >> metis_tac[]) >>
  `wb_args_shape cenv (\e. ty) args` by
    (irule typed_word_args_shape >> conj_tac
     >- gvs[EVERY_MEM, word_value_type_def, is_numeric_type_def] >> metis_tac[]) >>
  simp[expr_sim_ptr_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `!sa sb op. _` drule >> strip_tac >>
  `straight_fresh (code xs)` by simp[] >>
  drule_all straight_fresh_cs_extends >> strip_tac >>
  drule_all lower_word_args_shape_ready >> strip_tac >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func` by
    (irule fn_has_code_split >> simp[]) >>
  `local_ptrs_reserved cenv sm` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `expr_sim_inv cenv cx env es` by gvs[expr_body_pre_def] >>
  `fn_inst_ids_distinct func /\ ~cenv.ce_is_ctor` by gvs[body_inv_def] >>
  `!ee gs. expr_sim_inv cenv cx env ee ==> expr_sim_inv cenv cx env (ee with gas_obs := gs)` by simp[] >>
  drule_all lower_typed_args_sim_ptr >> strip_tac >>
  `typed_args_ready ctx func cenv cx expr_type (expr_sim_inv cenv cx env) args` by
    (irule body_word_args_ready >> metis_tac[]) >>
  drule_all typed_args_outcome_ptr_facts >> strip_tac >>
  `bt <> Bop In /\ bt <> Bop NotIn` by
    (rpt strip_tac >> gvs[vyperContextTheory.builtin_args_length_ok_def, LENGTH_EQ_NUM_compute] >>
     qpat_x_assum `expr_body_pre _ _ _ _ _` mp_tac >>
     simp[expr_body_pre_def, well_typed_expr_def, well_typed_builtin_app_def,
          well_typed_binop_def]) >>
  simp[eval_expr_builtin_action, expr_type_def] >>
  irule gas_outcome_ptr_bind_mid >>
  conj_tac >- suspend "cert_normal" >>
  conj_tac >- suspend "cert_error" >>
  suspend "bind"
QED

Resume word_args_compose_sim_ptr[pre]:
  rpt strip_tac >>
  `expr_type e = BaseT (UintT 256)` by gvs[EVERY_MEM] >> simp[is_word_type_def] >>
  irule expr_body_pre_builtin_typed_arg >> simp[] >>
  qexistsl_tac [`ann`, `args`, `bt`, `es`] >> simp[] >>
  gvs[EVERY_MEM, is_numeric_type_def]
QED

Resume word_args_compose_sim_ptr[cert_normal]:
  rpt strip_tac >> irule gas_exempt_cert_bind_values >>
  goal_assum (drule_at Any) >> gvs[]
QED
Resume word_args_compose_sim_ptr[cert_error]:
  rpt strip_tac >> irule gas_exempt_cert_error_values >> simp[]
QED
Resume word_args_compose_sim_ptr[bind]:
  qmatch_asmsub_abbrev_tac `gas_outcome_ptr _ _ _ _ _ _ Qfacts _` >>
  qexists_tac `\vs. Qfacts (INL vs)` >> reverse conj_tac
  >- (irule gas_outcome_ptr_conseq >>
      qexistsl_tac [`Qfacts`, `\rr ee gt r. wb_args_exit rr r`] >>
      simp[Abbr `Qfacts`] >> rpt strip_tac >> gvs[] >>
      Cases_on `res` >> gvs[wb_args_exit_def, expr_exit_def]) >>
  rpt gen_tac >> strip_tac >>
  fs[Abbr `Qfacts`, typed_args_post_ptr_def] >>
  `wb_args_post ctx func cenv cx es sa s0 em xs v t` by
    (irule word_uint_args_post >> metis_tac[]) >>
  first_x_assum irule >> simp[] >> reverse conj_tac
  >- (gvs[EVERY_MEM] >> metis_tac[]) >>
  qpat_x_assum `LIST_REL _ args v` mp_tac >>
  qpat_x_assum `EVERY _ args` mp_tac >>
  map_every qid_spec_tac [`v`, `args`] >>
  Induct >> Cases_on `v` >> simp[] >> rpt strip_tac >>
  gvs[evaluate_type_def] >> metis_tac[]
QED
Finalise word_args_compose_sim_ptr
