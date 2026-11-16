(* Sequential ABI argument composition, independent of the head implementation. *)
Theory bodyFullAbiEncodeArgsCompose
Ancestors
  bodyFullAbiEncodeArgsFrame bodyFullAbiEncodeReadResources
  bodyFullAbiEncodeOutcomeFrame bodyFullAbiEncodeArgsPost
  bodyFullPreds abiEncodeArgsSim abiEncodeArgsCase gasOutcomeFullCompose
  gasShadowCompile gasShadowCompileHelpers gasShadowState gasShadowCompileConvert
  exprLoweringProps exprLowering compileEnv
  gasOutcomeFull fragGasOriginPtr fragExec bodySimFull bodyPtrDefs loweringPosts
  exprSimHyps exprSimSource exprSimWordArgs venomState venomExecSemantics vyperInterpreter
  vyperStorageTrace vyperStorageFootprint vyperStorageBackend vyperState list arithmetic words

Theorem abi_encode_args_full_from_step:
  (!cx e tops ctx ce env es sa vv mid rest op sb shadow_sa shadow_mid shadow_sb
    shadow_ctx func shadow_func DF lo d s0 st0 G0 tn0 PG.
  body_expr_full_ok cx e /\ body_inv tops ctx ce cx /\
  expr_body_pre ce cx env e es /\
  compile_expr ce (expr_type e) e sa = (vv,mid) /\
  (if ~is_word_type (expr_type e) /\ exprs_can_mutate ce rest
   then compile_materialize_vv ce (lowered_value_type ce e) vv mid
   else unwrap_value ce vv mid) = (op,sb) /\
  compile_expr ce (expr_type e) (gas_shadow_expr e) shadow_sa = (vv,shadow_mid) /\
  (if ~is_word_type (expr_type e) /\ exprs_can_mutate ce rest
   then compile_materialize_vv ce (lowered_value_type ce e) vv shadow_mid
   else unwrap_value ce vv shadow_mid) = (op,shadow_sb) /\
  gas_shadow_state sa shadow_sa /\ gas_shadow_state mid shadow_mid /\
  gas_shadow_state sb shadow_sb /\ gas_shadow_context ctx shadow_ctx /\
  ctx_inst_ids_distinct ctx /\ gas_shadow_function func shadow_func /\
  MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa /\
  ~ctx_has_dalloca ctx /\ (!H. dead_lo_ok H (DF H) lo ce cx) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
  return_buf_frame d ce sa s0 /\ alloca_history func s0 /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func ce cx es s0 /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d ce cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 (bind (eval_expr cx e) (read_result cx))
    (es,s0,G0,tn0)
    (\H rr ee G tn t. ?v tv.
      rr = INL v /\
      evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
      value_has_type tv v /\
      expr_post H ctx func ce cx e es sa sb s0 ee v op t /\
      expr_val_rel cx (lowered_value_type ce e) v op t /\
      expr_val_at ce cx (lowered_value_type ce e) sa sb ee v op t /\
      type_memory_bytes ce (lowered_value_type ce e) = type_memory_size tv /\
      type_memory_bytes ce (lowered_value_type ce e) < 2**64 /\
      ghost_inv_at (DF H) lo d ce cx ee G tn t /\
      ghost_kept_at lo ce es sa G0 tn0 s0 G tn /\
      alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      (!x. op = Var x ==> not_fresh_at sb x) /\
      (~(~is_word_type (expr_type e) /\ exprs_can_mutate ce rest) ==>
        expr_store_bound cx (post_value_type ce e) v op t /\
        ptr_val_ok cx (post_value_type ce e) v op G tn t /\
        (~is_word_type (post_value_type ce e) ==> ptr_buf_ok ce e op G t) /\
        (~is_word_type (post_value_type ce e) ==> !w.
          eval_operand op t = SOME w ==>
          type_memory_size tv = 0 \/ w2n w + type_memory_size tv <= t.vs_alloca_next)) /\
      (~is_word_type (expr_type e) /\ exprs_can_mutate ce rest ==>
        ?x w. op = Var x /\ lookup_var x t = SOME w /\
          FLOOKUP t.vs_allocas mid.cs_next_id = SOME (w2n w,type_memory_size tv) /\
          FLOOKUP G x = SOME (w2n w,type_memory_size tv) /\
          ptr_buf_ok ce e op G t /\ lo <= w2n w /\
          ptr_covers G tn x t (type_memory_size tv) /\
          (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
            val_in_memory tv v (w2n w) mem) /\
          w2n w + type_memory_size tv < dimword(:256) /\
          w2n w + type_memory_size tv <= t.vs_alloca_next /\
          (!name b sz. local_region ce es.scopes s0 name b sz ==>
            b+sz <= w2n w \/ w2n w+type_memory_size tv <= b)))
    (\H rr ee gt r. expr_exit rr r /\ halt_exit H cx ee rr r)) ==>
  !args cx tops ctx ce Inv env es sa ops sb shadow_sa shadow_sb shadow_ctx
    func shadow_func DF lo PG d st0 s0 G0 tn0.
  body_exprs_full_ok cx args /\ body_inv tops ctx ce cx /\ Inv es /\
  (!q. Inv q ==> expr_sim_inv ce cx env q) /\
  (!q gs. Inv q ==> Inv (q with gas_obs := gs)) /\
  EVERY (\e. !q. Inv q ==> expr_body_pre ce cx env e q) args /\
  EVERY (\e. !q v q'. Inv q /\
    bind (eval_expr cx e) (read_result cx) q = (INL v,q') ==>
    Inv q' /\ MAP FDOM q'.scopes = MAP FDOM q.scopes) args /\
  compile_abi_encode_args compile_expr ce args sa = (ops,sb) /\
  compile_abi_encode_args compile_expr ce (MAP gas_shadow_expr args) shadow_sa = (ops,shadow_sb) /\
  gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\
  MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa /\
  ~ctx_has_dalloca ctx /\ (!H. dead_lo_ok H (DF H) lo ce cx) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  return_buf_frame d ce sa s0 /\ alloca_history func s0 /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func ce cx es s0 /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d ce cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 (eval_exprs cx args) (es,s0,G0,tn0)
    (\H rr ee G tn t. ?vs tvs.
      rr = INL vs /\ LENGTH tvs = LENGTH args /\
      abi_args_post H ctx func ce cx es sa sb s0 ee args ops vs t /\
      (!i. i < LENGTH args ==>
        evaluate_type (get_tenv cx) (lowered_value_type ce (EL i args)) = SOME (EL i tvs) /\
        value_has_type (EL i tvs) (EL i vs) /\
        type_memory_bytes ce (lowered_value_type ce (EL i args)) = type_memory_size (EL i tvs) /\
        type_memory_size (EL i tvs) < 2**64 /\
        (is_word_type (lowered_value_type ce (EL i args)) ==>
          abi_tuple_input ce (lowered_value_type ce (EL i args)) (EL i tvs) (EL i vs) (EL i ops) t /\
          op_taint tn (EL i ops) = {}) /\
        (~is_word_type (lowered_value_type ce (EL i args)) /\ 0 < type_memory_size (EL i tvs) ==>
          abi_tuple_input ce (lowered_value_type ce (EL i args)) (EL i tvs) (EL i vs) (EL i ops) t /\
          ?x w. EL i ops = Var x /\ lookup_var x t = SOME w /\
            ptr_covers G tn x t (type_memory_size (EL i tvs)) /\
            w2n w + type_memory_size (EL i tvs) < dimword(:256) /\
            w2n w + type_memory_size (EL i tvs) <= t.vs_alloca_next /\
            (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
              val_in_memory (EL i tvs) (EL i vs) (w2n w) mem))) /\
      ghost_inv_at (DF H) lo d ce cx ee G tn t /\
      ghost_kept_at lo ce es sa G0 tn0 s0 G tn /\
      alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      EVERY (\op. !x. op = Var x ==> not_fresh_at sb x) ops /\
      Inv ee /\ MAP FDOM ee.scopes = MAP FDOM es.scopes)
    (\H rr ee gt r. wb_args_exit rr r /\ halt_exit H cx ee rr r)
Proof
  disch_then (mk_asm "step") >>
  Induct_on `args` >- suspend "nil" >>
  rpt gen_tac >> strip_tac >> suspend "cons"
QED

Resume abi_encode_args_full_from_step[nil]:
  asm_x "step" kall_tac >> rpt strip_tac >>
  gvs[compile_abi_encode_args_def, comp_return_def] >>
  irule gas_outcome_full_pure >> simp[] >>
  simp[eval_exprs_nil] >>
  qexistsl_tac [`G0`, `es`, `INL []`, `s0`, `tn0`] >>
  simp[] >> rpt strip_tac >>
  simp[gas_origin_ptr_path_rules, abi_args_post_nil, wb_frame_refl,
       ghost_kept_at_def] >>
  qpat_x_assum `!H. valid_horizon _ _ _ _ ==> _`
    (qspec_then `H` mp_tac) >> simp[] >> strip_tac >>
  fs[storage_well_formed_on_def, ghost_inv_at_def] >>
  rpt strip_tac
  >~ [`slots_in_range (get_storage _ _ b) _ _`]
  >- (Cases_on `b` >> fs[get_storage_def] >> metis_tac[get_storage_def]) >>
  fs[] >> metis_tac[]
QED

Resume abi_encode_args_full_from_step[cons]:
  gvs[EVERY_DEF, body_exprs_full_ok_def] >>
  qpat_x_assum `compile_abi_encode_args _ _ (h::args) sa = _`
    (strip_assume_tac o REWRITE_RULE [abi_args_compile_cons]) >> gvs[] >>
  `?shadow_mid. compile_expr ce (expr_type h) (gas_shadow_expr h) shadow_sa =
    (vv,shadow_mid) /\ gas_shadow_state mid shadow_mid` by
    (mp_tac (cj 1 gas_shadow_compile_expr) >>
     disch_then (qspecl_then [`ce`, `expr_type h`, `h`, `T`] mp_tac) >>
     simp[gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`sa`, `shadow_sa`] mp_tac) >> simp[] >>
     Cases_on `compile_expr ce (expr_type h) (gas_shadow_expr h) shadow_sa` >> simp[]) >>
  `?shadow_sm.
    (if ~is_word_type (expr_type h) /\ exprs_can_mutate ce args
     then compile_materialize_vv ce (lowered_value_type ce h) vv shadow_mid
     else unwrap_value ce vv shadow_mid) = (op,shadow_sm) /\
    gas_shadow_state sm shadow_sm` by
    (qpat_x_assum `(if _ then _ else _) = (op,sm)` mp_tac >>
     Cases_on `~is_word_type (expr_type h) /\ exprs_can_mutate ce args` >> simp[] >>
     strip_tac
     >- (mp_tac (Q.INST [`cenv` |-> `ce`, `ty` |-> `lowered_value_type ce h`, `vv` |-> `vv`] gas_shadow_compiles_materialize_vv) >>
         rewrite_tac[gas_shadow_compiles_def] >>
         disch_then (qspecl_then [`mid`, `shadow_mid`] mp_tac) >> simp[] >>
         Cases_on `compile_materialize_vv ce (lowered_value_type ce h) vv shadow_mid` >>
         simp[]) >>
     mp_tac (Q.INST [`cenv` |-> `ce`, `vv` |-> `vv`] gas_shadow_compiles_unwrap_value) >>
     rewrite_tac[gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`mid`, `shadow_mid`] mp_tac) >> simp[] >>
     Cases_on `unwrap_value ce vv shadow_mid` >> simp[]) >>
  qpat_x_assum `compile_abi_encode_args _ _ (gas_shadow_expr h::_) _ = _` mp_tac >>
  simp[abi_args_compile_cons, gas_shadow_expr_can_mutate,
       gasShadowTheory.gas_shadow_expr_type] >>
  strip_tac >>
  `ci_mono sa mid /\ ci_mono shadow_sa shadow_mid` by
    (asm_x "step" kall_tac >>
     qpat_x_assum `!cx' tops' ctx' ce' Inv'. _` kall_tac >>
     metis_tac[compile_expr_ci_mono, pairTheory.SND]) >>
  `ci_mono mid sm /\ ci_mono shadow_mid shadow_sm` by
    (asm_x "step" kall_tac >>
     qpat_x_assum `!cx' tops' ctx' ce' Inv'. _` kall_tac >>
     Cases_on `~is_word_type (expr_type h) /\ exprs_can_mutate ce args` >> gvs[] >>
     metis_tac[ci_mono_compile_materialize_vv, ci_mono_unwrap_value, pairTheory.SND]) >>
  `ci_mono sm sb /\ ci_mono shadow_sm shadow_sb` by
    (asm_x "step" kall_tac >>
     qpat_x_assum `!cx' tops' ctx' ce' Inv'. _` kall_tac >>
     metis_tac[abi_args_compile_mono, pairTheory.SND]) >>
  `cs_extends sa sm /\ cs_extends shadow_sa shadow_sm` by
    (asm_x "step" kall_tac >>
     qpat_x_assum `!cx' tops' ctx' ce' Inv'. _` kall_tac >>
     fs[ci_mono_def] >> metis_tac[cs_extends_trans]) >>
  `cs_extends sm sb /\ cs_extends shadow_sm shadow_sb` by fs[ci_mono_def] >>
  `fn_has_code sa sm func /\ fn_has_code sm sb func /\
   fn_has_code shadow_sa shadow_sm shadow_func /\ fn_has_code shadow_sm shadow_sb shadow_func` by
    (asm_x "step" kall_tac >>
     qpat_x_assum `!cx' tops' ctx' ce' Inv'. _` kall_tac >>
     metis_tac[fn_has_code_split]) >>
  `expr_body_pre ce cx env h es` by
    (qpat_x_assum `!q. Inv q ==> expr_body_pre _ _ _ _ _` irule >> simp[]) >>
  `gas_admissible (bind (eval_expr cx h) (read_result cx)) expr_res_ok es` by
    (irule expr_body_pre_gas_admissible >> goal_assum (drule_at Any)) >>
  asm "step" drule_all >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ headQ headR` >>
  rewrite_tac[eval_exprs_cons_action] >>
  irule gas_outcome_full_bind_all >> BETA_TAC >> rpt conj_tac
  >~ [`storage_trace_frame (bind (eval_expr _ _) _)`]
  >- (irule vyperStorageTraceTheory.storage_trace_frame_bind >>
      simp[vyperStorageTraceTheory.evaluate_storage_trace_frame,
           vyperStorageTraceTheory.storage_trace_frame_read_result])
  >~ [`!v. storage_trace_frame (bind (eval_exprs cx args) (\vs. return (v::vs)))`]
  >- (gen_tac >> irule vyperStorageTraceTheory.storage_trace_frame_bind >>
      simp[vyperStorageTraceTheory.evaluate_storage_trace_frame,
           vyperStorageTraceTheory.storage_trace_frame_return])
  >~ [`gas_marked_exec _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> drule gasExemptCertTheory.gas_exempt_cert_bind_value >> simp[] >>
      disch_then irule >> simp[])
  >~ [`gas_exempt_cert _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_error_value >>
      first_assum ACCEPT_TAC) >>
  qexists `headQ` >> conj_tac
  >- suspend "tail_bind" >>
  irule gas_outcome_full_post_source >> first_assum (irule_at Any) >>
  simp[Abbr `headR`] >> rpt strip_tac >>
  qpat_x_assum `expr_exit res r` mp_tac >>
  qpat_x_assum `halt_exit H cx ee res r` mp_tac >>
  rpt (pop_assum kall_tac) >>
  Cases_on `res` >> simp[wb_args_exit_def, exprSimDefsTheory.expr_exit_def] >>
  simp[exprSimDefsTheory.halt_exit_def]
QED

Resume abi_encode_args_full_from_step[tail_bind]:
  asm_x "step" kall_tac >> rpt gen_tac >> strip_tac >>
  `?v tv. res = INL v /\
    evaluate_type (get_tenv cx) (lowered_value_type ce h) = SOME tv` by
    (qpat_assum `!H. valid_horizon _ _ _ _ ==> headQ _ _ _ _ _ _`
       (qspec_then `storage_trace_horizon mid'.storage_trace` mp_tac) >>
     qpat_x_assum `!cx' tops' ctx' ce' Inv'. _` kall_tac >>
     rpt (qpat_x_assum `!PG. gas_outcome_full _ _ _ _ _ _ _ _` kall_tac) >>
     fs[storage_trace_domain_def, Abbr `headQ`] >> metis_tac[]) >>
  gvs[] >>
  qpat_assum `!H. valid_horizon _ _ _ _ ==> headQ _ _ _ _ _ _`
    (qspec_then `storage_trace_horizon mid'.storage_trace` mp_tac) >>
  impl_tac >- fs[storage_trace_domain_def] >>
  simp_tac (srw_ss()) [] >> strip_tac >>
  `Inv mid' /\ MAP FDOM mid'.scopes = MAP FDOM es.scopes` by
    (qpat_x_assum `!tail. bind _ _ _ = _`
       (qspec_then `mid'.gas_obs` mp_tac) >>
     simp[] >> strip_tac >>
     qpat_x_assum `!q v q'. Inv q /\ _ ==> _`
       (qspec_then `es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ mid'.gas_obs` mp_tac) >>
     simp[] >> disch_then irule >> qexists `v` >> simp[]) >>
  `body_exprs_full_ok cx args` by
    (qpat_x_assum `(?s tv t s1 v t1. _) ==> body_exprs_full_ok _ _` irule >>
     qpat_assum `!tail. bind _ _ _ = _` (qspec_then `mid'.gas_obs` mp_tac) >>
     rpt (pop_assum kall_tac) >>
     simp[bind_def, AllCaseEqs()] >> metis_tac[]) >>
  fs[Abbr `headQ`] >>
  `sa.cs_next_var <= sm.cs_next_var` by
    (fs[ci_mono_def, cs_extends_def] >> decide_tac) >>
  `local_ptrs_reserved ce sm` by metis_tac[local_ptrs_reserved_next_var] >>
  `return_buf_frame d ce sm t` by
    (irule bodyMemoryDefsTheory.return_buf_frame_frame >>
     qexistsl_tac [`ce`, `s0`, `sa`] >>
     fs[expr_post_def]) >>
  `(!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
   (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x)` by
    (metis_tac[loweringShapeDefsTheory.not_fresh_at_mono]) >>
  `!H. valid_horizon cx st0 H mid'.storage_trace ==>
    stmt_state_rel H ctx func ce cx mid' t /\
    storage_well_formed_on cx mid' (FST H) /\
    ghost_inv_at (DF H) lo d ce cx mid' G1 tn1 t` by
    (rpt strip_tac >>
     qpat_x_assum `!H. valid_horizon _ _ _ _ ==> expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (qspec_then `H` mp_tac) >> simp[expr_post_def]) >>
  qpat_x_assum `!cx' tops' ctx' ce' Inv' env' es' sa' ops' sb' shadow_sa' shadow_sb' shadow_ctx' func' shadow_func' DF' lo' PG d' st0' s0' G0' tn0'. _`
    (drule_at (Pat `compile_abi_encode_args _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `return_buf_frame _ _ _ _`)) >>
  disch_then drule_all >>
  disch_then (qspec_then `PG` assume_tac) >>
  dxrule abi_encode_outcome_labels >>
  qmatch_abbrev_tac `gas_outcome_full _ _ _ _ _ _ tailQ tailR ==> _` >>
  disch_tac >>
  qabbrev_tac `cons_res = (\res : value list + exception. case res of INL vs => INL (v::vs) | INR ex => INR ex)` >>
  `gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 (bind (eval_exprs cx args) (\vs. return (v::vs))) (mid',t,G1,tn1)
    (\H raw ee G tn t. ?res. raw = cons_res res /\ tailQ H res ee G tn t)
    (\H raw ee gt r. ?res. raw = cons_res res /\ tailR H res ee gt r)` by
    (irule gas_outcome_full_source_map >>
     simp[Abbr `cons_res`] >>
     qexists_tac `eval_exprs cx args` >> simp[] >>
     gen_tac >> Cases_on `eval_exprs cx args es'` >>
     Cases_on `q` >> simp[bind_def, return_def]) >>
  irule gas_outcome_full_post_source >>
  goal_assum (drule_at Any) >>
  conj_tac >- suspend "cons_resources" >>
  simp[Abbr `tailR`, Abbr `cons_res`] >>
  rpt strip_tac >> rename1 `raw = case oldres of INL vs => INL (v::vs) | INR ex => INR ex` >>
  Cases_on `oldres` >> gvs[wb_args_exit_def, exprSimDefsTheory.halt_exit_def]
QED

Resume abi_encode_args_full_from_step[cons_resources]:
  rpt gen_tac >> simp[Abbr `tailQ`] >> rpt strip_tac >>
  gvs[Abbr `cons_res`] >>
  simp_tac (srw_ss()) [] >>
  qpat_x_assum `!PG. gas_outcome_full _ _ _ _ _ _ _ _` kall_tac >>
  rpt (qpat_x_assum `gas_outcome_full _ _ _ _ _ _ _ _` kall_tac) >>
  `wb_frame ce mid' ee sm t t' /\ stmt_state_rel H ctx func ce cx ee t'` by
    fs[abi_args_post_def] >>
  `expr_sim_inv ce cx env mid'` by metis_tac[] >>
  `expr_body_pre ce cx env h es` by metis_tac[] >>
  `val_wf tv v` by metis_tac[valueEncodingTypingTheory.value_has_type_val_wf] >>
  `sa.cs_next_id <= sm.cs_next_id /\ sm.cs_next_id <= sb.cs_next_id /\
   sm.cs_next_var <= sb.cs_next_var` by (fs[ci_mono_def] >> decide_tac) >>
  `storage_trace_domain cx st0 es.storage_trace` by
    (`storage_trace_frame (bind (eval_expr cx h) (read_result cx))` by
       (irule vyperStorageTraceTheory.storage_trace_frame_bind >>
        simp[vyperStorageTraceTheory.evaluate_storage_trace_frame,
             vyperStorageTraceTheory.storage_trace_frame_read_result]) >>
     qpat_x_assum `storage_trace_frame _` mp_tac >>
     simp[vyperStorageTraceTheory.storage_trace_frame_def] >>
     disch_then (qspecl_then
       [`es with gas_obs := gas_explicit marks s0.vs_gas_readings`, `es.storage_trace`] mp_tac) >>
     Cases_on `bind (eval_expr cx h) (read_result cx)
       (es with <|gas_obs := gas_explicit marks s0.vs_gas_readings; storage_trace := []|>)` >>
     simp[] >> strip_tac >>
     qpat_x_assum `!tail. bind (eval_expr cx h) _ _ = _` (qspec_then `[]` mp_tac) >>
     pure_rewrite_tac[APPEND_NIL] >>
     qpat_x_assum `bind _ _ (es with gas_obs := _) = _` (fn th => rewrite_tac[th]) >>
     simp_tac (srw_ss()) [] >> strip_tac >>
     qpat_x_assum `storage_trace_domain cx st0 mid'.storage_trace` mp_tac >>
     qpat_x_assum `r with storage_trace := _ = _`
       (mp_tac o AP_TERM ``\s:evaluation_state. s.storage_trace``) >>
     simp_tac (srw_ss()) [] >> disch_then (fn th => rewrite_tac[GSYM th]) >>
     strip_tac >> drule storage_trace_domain_prefix >> simp[]) >>
  `stmt_state_rel (storage_trace_horizon es.storage_trace) ctx func ce cx es s0` by
    (qpat_x_assum `!H. valid_horizon _ _ _ es.storage_trace ==> _`
       (qspec_then `storage_trace_horizon es.storage_trace` mp_tac) >>
     fs[storage_trace_domain_def]) >>
  `~exprs_can_mutate ce args ==> ee.scopes = mid'.scopes` by
    (strip_tac >>
     qpat_x_assum `!tail. bind (eval_exprs cx args) _ _ = _`
       (qspec_then `[]` mp_tac) >>
     Cases_on `eval_exprs cx args (mid' with gas_obs := xs)` >>
     Cases_on `q` >> simp[bind_def, return_def] >> strip_tac >> gvs[] >>
     drule_all abiEncodeArgsScopesTheory.eval_exprs_no_mutation_scopes >> simp[]) >>
  `~is_word_type (expr_type h) /\ exprs_can_mutate ce args ==>
    ?x w. op = Var x /\ lookup_var x t = SOME w /\
      val_footprint tv v <= type_memory_size tv /\
      (!n b k. local_region ce mid'.scopes t n b k ==>
        w2n w + type_memory_size tv <= b \/ b+k <= w2n w) /\
      mid.cs_next_id < sm.cs_next_id` by suspend "owned_frame_facts" >>
  qexists `tv::tvs` >> simp[] >>
  conj_asm1_tac >- suspend "cons_post" >>
  conj_tac >- suspend "cons_indexed" >>
  conj_tac >- suspend "cons_ghost" >>
  metis_tac[loweringShapeDefsTheory.not_fresh_at_mono, ci_mono_def, cs_extends_def]
QED

Resume abi_encode_args_full_from_step[cons_indexed]:
  gen_tac >> Cases_on `i` >> simp[] >>
  conj_tac >- suspend "head_word_resource" >>
  suspend "head_positive_resource"
QED

Resume abi_encode_args_full_from_step[head_word_resource]:
  strip_tac >>
  `is_word_type (expr_type h)` by
    metis_tac[expr_body_pre_lowered_fits, exprSimLayoutTransportTheory.compatible_word_type] >>
  `?ptv. evaluate_type (get_tenv cx) (post_value_type ce h) = SOME ptv` by
    metis_tac[post_type_evaluates] >>
  `abi_tuple_input ce (lowered_value_type ce h) tv v op t /\ op_taint tn1 op = {}` by
    (irule (INST_TYPE [alpha |-> ``:256``] (cj 1 abi_encode_arg_positive_resources)) >>
     simp[] >> goal_assum (drule_at Any) >> simp[] >>
     fs[] >>
     qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
     qpat_x_assum `ptr_val_ok _ _ _ _ _ _ _` mp_tac >>
     qpat_x_assum `evaluate_type _ (post_value_type _ _) = _` mp_tac >>
     qpat_x_assum `is_word_type (expr_type h)` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[] >> rpt strip_tac >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any)) >>
  `expr_val_rel cx (lowered_value_type ce h) v op t'` by
    (qpat_x_assum `abi_args_post _ _ _ _ _ _ _ _ _ _ (h::args) _ _ _` mp_tac >>
     simp[abi_args_post_def]) >>
  `op_taint tn' op = op_taint tn1 op` by
    (Cases_on `op` >> fs[ghost_kept_at_def, ptrDisciplineTheory.op_taint_def]) >>
  gvs[abiTuplePropsTheory.abi_tuple_input_def, expr_val_rel_def]
QED

Resume abi_encode_args_full_from_step[head_positive_resource]:
  strip_tac >>
  `~is_word_type (expr_type h)` by
    metis_tac[expr_body_pre_lowered_fits, exprSimLayoutTransportTheory.compatible_word_type] >>
  Cases_on `exprs_can_mutate ce args`
  >- suspend "positive_owned" >>
  suspend "positive_borrowed"
QED

Resume abi_encode_args_full_from_step[positive_borrowed]:
  `?ptv. evaluate_type (get_tenv cx) (post_value_type ce h) = SOME ptv` by
    metis_tac[post_type_evaluates] >>
  `~is_word_type (post_value_type ce h)` by
    metis_tac[exprSimIfExpWidenedPhysicalTypeTheory.post_value_type_nonword] >>
  `abi_tuple_input ce (lowered_value_type ce h) tv v op t /\
   ?x w. op = Var x /\ lookup_var x t = SOME w /\
     ptr_covers G1 tn1 x t (type_memory_bytes ce (lowered_value_type ce h)) /\
     w2n w + type_memory_bytes ce (lowered_value_type ce h) < dimword(:256) /\
     w2n w + type_memory_bytes ce (lowered_value_type ce h) <= t.vs_alloca_next /\
     (!mem. mem_agree_outside tn1.t_mem t.vs_memory mem ==>
       val_in_memory tv v (w2n w) mem)` by
    (irule (INST_TYPE [alpha |-> ``:256``] (cj 2 abi_encode_arg_positive_resources)) >>
     simp[] >> metis_tac [NOT_LESS, EQ_LESS_EQ]) >>
  `ee.scopes = mid'.scopes` by simp[] >>
  `stmt_state_rel (storage_trace_horizon mid'.storage_trace) ctx func ce cx mid' t` by
    (qpat_x_assum `!H. valid_horizon _ _ _ _ ==> stmt_state_rel _ _ _ _ _ mid' _ /\ _`
       (qspec_then `storage_trace_horizon mid'.storage_trace` mp_tac) >>
     fs[storage_trace_domain_def]) >>
  drule_at (Pat `wb_frame _ _ _ _ _ _`) abi_encode_borrowed_args_frame >>
  disch_then (drule_at (Pat `expr_val_at _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `ghost_kept_at _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `expr_sim_inv _ _ _ _`)) >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ mid' _`)) >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ ee _`)) >>
  simp[] >> (impl_tac >-
    (fs[] >> qpat_x_assum `ptr_covers G1 tn1 x t _` mp_tac >> simp[])) >> simp[]
QED

Resume abi_encode_args_full_from_step[owned_frame_facts]:
  strip_tac >> fs[] >>
  `val_footprint tv v <= type_memory_size tv` by
    metis_tac[exprSimPropsTheory.val_footprint_le] >>
  `!n b k. local_region ce mid'.scopes t n b k ==>
    w2n w + type_memory_size tv <= b \/ b+k <= w2n w` by
    (rpt strip_tac >>
     `local_region ce es.scopes s0 n b k` by
       (irule (INST_TYPE [alpha |-> ``:256``] stmtSimDefsTheory.local_region_kept) >>
        conj_tac
        >- (qexistsl_tac [`mid'`, `t`, `sa`] >> simp[] >>
            qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
            simp[expr_post_def]) >>
        qexistsl_tac [`storage_trace_horizon es.storage_trace`, `ctx`, `cx`, `func`] >>
        first_assum ACCEPT_TAC) >>
     qpat_x_assum `!name b sz. local_region ce es.scopes s0 name b sz ==> _`
       drule >> decide_tac) >>
  `mid.cs_next_id < sm.cs_next_id` by
    (qpat_assum `compile_materialize_vv ce (lowered_value_type ce h) vv mid = (op,sm)`
       (mp_tac o MATCH_MP abiEncodeMaterializeTheory.materialize_compile_trace) >>
     disch_then (qx_choose_then `buf` (qx_choose_then `sn`
       (qx_choose_then `src` (qx_choose_then `su` strip_assume_tac)))) >>
     `ci_mono su sm` by metis_tac[ci_mono_compile_store_memory, pairTheory.SND] >>
     `ci_mono sn su` by metis_tac[ci_mono_unwrap_value, pairTheory.SND] >>
     qpat_x_assum `compile_alloc_buffer _ mid = _` mp_tac >>
     simp[contextTheory.compile_alloc_buffer_def, comp_bind_def, comp_return_def] >>
     pairarg_tac >> simp[] >> strip_tac >>
     drule emitted_insts_emit_op_local >> fs[ci_mono_def] >> decide_tac) >>
  simp[] >> rpt strip_tac >>
  qpat_x_assum `!n b k. local_region ce mid'.scopes t n b k ==> _` drule >> decide_tac
QED

Resume abi_encode_args_full_from_step[positive_owned]:
  fs[] >>
  drule_at (Pat `wb_frame _ _ _ _ _ _`) abi_encode_owned_args_frame >>
  disch_then (drule_at (Pat `ghost_kept_at _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `ptr_covers _ _ _ _ _`)) >>
  disch_then (qspecl_then [`w`, `v`, `tv`, `type_memory_size tv`,
    `w2n w`, `func`, `d`, `cx`, `mid.cs_next_id`, `DF H`] mp_tac) >>
  (impl_tac >- (simp[] >> gvs[])) >>
  strip_tac >>
  `abi_tuple_input ce (lowered_value_type ce h) tv v (Var x) t'` by
    (simp[abiTuplePropsTheory.abi_tuple_input_def, eval_operand_def] >>
     metis_tac[mem_agree_outside_def]) >>
  simp[] >> qexists `w` >> simp[] >> decide_tac
QED

Resume abi_encode_args_full_from_step[cons_post]:
  Cases_on `~is_word_type (expr_type h) /\ exprs_can_mutate ce args`
  >- (fs[] >>
      `~is_word_type (lowered_value_type ce h)` by
        metis_tac[expr_body_pre_lowered_fits, exprSimLayoutTransportTheory.compatible_word_type] >>
      irule abi_args_post_cons_captured >>
      qexistsl_tac [`storage_trace_horizon es.storage_trace`,
        `storage_trace_horizon mid'.storage_trace`, `mid.cs_next_id`,
        `w2n w`, `type_memory_size tv`, `t`, `tv`, `w`] >>
      simp[eval_operand_def] >> metis_tac[]) >>
  `~is_word_type (lowered_value_type ce h) ==> ee.scopes = mid'.scopes` by
    (metis_tac[expr_body_pre_lowered_fits, exprSimLayoutTransportTheory.compatible_word_type]) >>
  `?w. eval_operand op t = SOME w` by
    (qpat_x_assum `expr_val_rel _ _ _ _ t` mp_tac >>
     simp[expr_val_rel_def] >> metis_tac[]) >>
  `eval_operand op t = eval_operand op t'` by
    (Cases_on `op` >> simp[eval_operand_def] >>
     metis_tac[abi_args_operand_kept, eval_operand_def]) >>
  irule abi_encode_args_post_cons_uncaptured_eq >>
  goal_assum (drule_at Any) >>
  qexistsl_tac [`storage_trace_horizon es.storage_trace`,
    `storage_trace_horizon mid'.storage_trace`, `env`, `t`] >> simp[]
QED

Resume abi_encode_args_full_from_step[cons_ghost]:
  irule wordArgsPtrTheory.ghost_kept_at_wb_trans >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
  qexistsl_tac [`storage_trace_horizon es.storage_trace`, `ctx`, `cx`, `func`, `mid'`] >>
  simp[] >> qpat_x_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[expr_post_def]
QED

Finalise abi_encode_args_full_from_step
