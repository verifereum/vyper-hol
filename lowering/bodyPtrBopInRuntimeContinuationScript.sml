Theory bodyPtrBopInRuntimeContinuation
Ancestors bodyPtrBopInNormalizedRuntime bodyPtrBopInRuntimePost
  bodyPtrBopInSemanticList bodyPtrBopInMixed bodyPtrBopInLiteralContinuation
  gasSummaryComposePtr fragGasPathPtr vyperState vyperAST
  vyperValueOperation vyperTyping valueEncoding loweringPosts exprSimWordArgs
  exprLowering compileEnv bodyPtrDefs exprSimPtrProps venomState exprLoweringProps
  loweringSlice venomExecSemantics appendStorageGhostPtr exprSimMemorySource

Theorem membership_array_source_encoded:
  is_word_type et /\ evaluate_type tenv et = SOME tv /\
  value_has_type tv v /\ value_has_type (ArrayTV tv bd) (ArrayV av) /\
  (bop = In \/ bop = NotIn) /\
  ws = (case av of DynArrayV vs => MAP (typed_val_to_w256 tv) vs
        | SArrayV kvs => GENLIST (\j. typed_val_to_w256 tv (sparse_val tv kvs j))
                           (bound_length bd)) ==>
  evaluate_binop u (ArrayTV tv bd) bop v (ArrayV av) =
    INL (BoolV (if bop = In then MEM (typed_val_to_w256 tv v) ws
               else ~MEM (typed_val_to_w256 tv v) ws))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `bd` >> Cases_on `av` >> gnvs[bound_length_def] >>
  TRY (fs[Once value_has_type_def] >> NO_TAC)
  >- (drule_all membership_fixed_source_encoded >> simp[])
  >> drule_all membership_dynamic_source_encoded >> simp[]
QED

Theorem membership_array_continuation_summary_ptr:
  post_value_type cenv e2 = expr_type e2 /\
  membership_vv_post d ctx fn cenv cx e2 es1 sc sm vv s1 G1 tn1 tvv ee s G tn /\
  compile_expr cenv ty e2 sc = (vv,sm) /\
  local_ptrs_reserved cenv sc /\ local_ptrs_reserved cenv sm /\
  compile_var_array_membership cenv needle vv (ArrayT et bd) (bop = In) sm = (op,sb) /\
  fn_has_code sm sb fn /\ ~ctx_has_dalloca ctx /\ ~cenv.ce_is_ctor /\
  expr_type e2 = ArrayT et bd /\
  evaluate_type (get_tenv cx) (ArrayT et bd) = SOME (ArrayTV tv bd) /\
  evaluate_type (get_tenv cx) et = SOME tv /\ is_word_type et /\
  read_result cx tvv ee = (INL (ArrayV av),ee) /\
  value_has_type (ArrayTV tv bd) (ArrayV av) /\ value_has_type tv v /\
  (bop = In \/ bop = NotIn) /\
  (!x. needle = Var x ==> not_fresh_at sm x) /\
  eval_operand needle s = SOME (typed_val_to_w256 tv v) /\
  op_prov G needle = NONE /\ op_taint tn needle = {} /\ ~s.vs_halted /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  ghost_kept cenv es sa G0 tn0 s0 G tn /\
  wb_frame cenv es ee sa s0 s /\ sa.cs_next_var <= sm.cs_next_var /\ ee.gas_obs = [] ==>
  gas_summary_ptr_at D (ctx,fn) PG []
    (bind (read_result cx tvv) (\a. lift_sum (evaluate_binop u (ArrayTV tv bd) bop v a)))
    (ee,s,G,tn)
    (\res fin G' tn' t. ?b. res = INL (BoolV b) /\
      expr_post ctx fn cenv cx (Builtin (BaseT BoolT) (Bop bop) [e1;e2])
        es sa sb s0 fin (BoolV b) op t /\
      ghost_inv d cenv cx fin G' tn' t /\
      ptr_val_ok cx (BaseT BoolT) (BoolV b) op G' tn' t /\
      ghost_kept cenv es sa G0 tn0 s0 G' tn' /\
      t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts)
    (\res fin ghosts r. expr_exit res r)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `ws = (case av of DynArrayV vs => MAP (typed_val_to_w256 tv) vs
        | SArrayV kvs => GENLIST (\j. typed_val_to_w256 tv (sparse_val tv kvs j))
                           (bound_length bd))` >>
  qpat_assum `Abbrev _` (assume_tac o PURE_REWRITE_RULE [markerTheory.Abbrev_def]) >>
  drule_all membership_array_source_encoded >> disch_tac >>
  drule read_result_gas_obs >> disch_tac >>
  `!tail. bind (read_result cx tvv)
    (\a. lift_sum (evaluate_binop u (ArrayTV tv bd) bop v a))
    (ee with gas_obs := tail) =
    (INL (BoolV (if bop = In then MEM (typed_val_to_w256 tv v) ws
      else ~MEM (typed_val_to_w256 tv v) ws)),ee with gas_obs := tail)` by
    (gen_tac >> pure_rewrite_tac[bind_def] >>
     qpat_assum `!tail. read_result _ _ _ = _` (fn th => pure_rewrite_tac[th]) >>
     pure_rewrite_tac[pairTheory.pair_case_thm] >> BETA_TAC >>
     pure_rewrite_tac[sumTheory.sum_case_def] >> BETA_TAC >>
     qpat_assum `!u. evaluate_binop _ _ _ _ _ = _` (fn th => pure_rewrite_tac[th]) >>
     rewrite_tac[lift_sum_def, sumTheory.sum_case_def] >> BETA_TAC >>
     rewrite_tac[return_def]) >>
  drule_all membership_normalized_array_runtime >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  `stmt_state_rel ctx fn cenv cx ee s /\ ghost_inv d cenv cx ee G tn s` by
    fs[bodyPtrBopInVvContractTheory.membership_vv_post_def, vv_post_def] >>
  drule_all membership_runtime_readonly_frames >> strip_tac >>
  `ghost_kept cenv es sa G0 tn0 s0 G' tn'` by
    (qpat_assum `ghost_kept _ es sa _ _ _ G tn`
       (mp_then Any mp_tac ghost_kept_suffix_compose) >>
     disch_then irule >> reverse conj_tac
     >- fs[bodyPtrBopInLoopContractTheory.membership_loop_frame_def] >>
     qexists_tac `sm` >>
     fs[bodyPtrBopInLoopContractTheory.membership_loop_frame_def]) >>
  drule_all literal_bool_post >> disch_tac >>
  qpat_x_assum `Abbrev _` kall_tac >>
  qpat_x_assum `ws = _` kall_tac >>
  pure_rewrite_tac[gas_summary_ptr_at_def] >>
  qexistsl_tac [`INL (BoolV (if bop = In then MEM (typed_val_to_w256 tv v) ws
                           else ~MEM (typed_val_to_w256 tv v) ws))`,
                `ee`,`G'`,`tn'`,`OK t`] >> simp[] >>
  `ee with gas_obs := [] = ee` by simp[evaluation_state_component_equality] >>
  asm_rewrite_tac[]
QED
