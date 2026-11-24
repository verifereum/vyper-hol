Theory entryCreateAgreedCtorRows
Ancestors
  gasShadowCompileBase e2eDefs exprSimFullBundleProps fragExec fragGasOrigin
  gasExplicitSites gasSummary venomState vyperState relation list words pair
  arithmetic exprLowering vfmConstants compileEnv exprLoweringProps
  exprBodyPreProps bodyFullPreds vyperStorageTrace rich_list exprSimHypsDefs
  vyperTypeSystem bodyPtrDefs loweringPosts context vyperAST vyperStorageFootprint
  vyperTyping vyperValue integer_word valueEncoding createCtorSegmentArrival
  loweringStateRelDefs exprSimMemDefs ptrDiscipline bodySim createExprSizeExitDefs
  createSizePrefixReplay createSizeCtorValueRow entryCreateCtorWordRow

(* This is the VV callback's post at the expression exit, before a possible
   private copy. It is a script-local notation, not a new proof obligation. *)
Overload ctor_replay_vv_post[local] = ``\DF lo d ctx func ce cx e p a m s vv G tn
    H res ee G' tn' t. ?tv. res = INL tv /\
  vv_post H ctx func ce cx e p a m s ee tv vv t /\
  vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e) ee tv vv t /\
  alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
  s.vs_alloca_next <= t.vs_alloca_next /\
  ghost_inv_at (DF H) lo d ce cx ee G' tn' t /\
  ptr_vv_ok cx (post_value_type ce e) tv vv ee G' tn' t /\
  (!v. tv = Value v /\ ~is_word_type (post_value_type ce e) /\
       ~is_bytestring_type (post_value_type ce e) ==>
       vv_own ce cx (post_value_type ce e) a m ee tv vv t /\
       (!t' p. vv = LocatedValue t' p ==> p.ptr_location = LocMemory)) /\
  (ce.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
     ?val. read_result cx tv ee = (INL val,ee) /\
       !rt w. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
         eval_operand (vv_operand vv) t = SOME w ==>
         w2n w + type_memory_size rt <= lo /\
         (!mem. mem_agree_outside tn'.t_mem t.vs_memory mem ==>
                val_in_memory rt val (w2n w) mem)) /\
  (!tag op. vv = StackValue tag op /\ ~is_word_type (post_value_type ce e) ==>
     ptr_buf_ok ce e op G' t) /\
  (!tag p. vv = LocatedValue tag p /\ p.ptr_location = LocMemory ==>
     ptr_buf_ok ce e p.ptr_operand G' t) /\
  ghost_kept_at lo ce p a G tn s G' tn'``

Theorem agreed_ctor_row_replay:
  body_inv tops ctx ce cx /\ shadow_body_inv tops ctx shctx /\
  expr_body_pre ce cx env e p /\
  (!op. expr_sim_full_pre (DF,lo,d,ctx,shctx,PG,func,shfunc)
    ce cx (expr_type e) e p (st0,a,b,sha,shb,op,s,G,tn) ==>
    gas_completed_operand (DF,lo,gas_explicit_sites ctx shctx,ctx,func,PG)
      tops cx st0 a b (bind (eval_expr cx e) (read_result cx)) (p,s,G,tn)
      (expr_sim_full_post (DF,lo,d,ctx,func) ce cx e (p,a,b,s,op,G,tn))) /\
  (expr_vv_sim_full_pre (DF,lo,d,ctx,shctx,PG,func,shfunc)
    ce cx (expr_type e) e p (st0,a,m,sha,shm,vv,s,G,tn) ==>
    gas_completed_operand (DF,lo,gas_explicit_sites ctx shctx,ctx,func,PG)
      tops cx st0 a m (eval_expr cx e) (p,s,G,tn)
      (ctor_replay_vv_post DF lo d ctx func ce cx e p a m s vv G tn)) /\
  compile_expr ce (expr_type e) e a = (vv,m) /\
  compile_expr (gas_shadow_env T ce) (expr_type e) (gas_shadow_expr e) sha = (vv,shm) /\
  compile_snapshot_vv ce (exprs_can_mutate ce xs)
    (ext_call_arg_value (lowered_value_type ce e) vv) m = (saved,b) /\
  local_ptrs_reserved ce a /\ (!h. dead_lo_ok h (DF h) lo ce cx) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x) /\
  return_buf_frame d ce a s /\ alloca_history func s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  (!f i z. frag_reachable ctx func s f i z ==> dalloca_fmp_headroom i z) /\
  (!h. valid_horizon cx st0 h p.storage_trace ==>
     stmt_state_rel h ctx func ce cx p s /\ storage_well_formed_on cx p (FST h) /\
     ghost_inv_at (DF h) lo d ce cx p G tn s) /\
  ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts /\
  t.vs_current_bb = b.cs_current_bb /\ t.vs_inst_idx = LENGTH b.cs_current_insts /\
  (is_word_type (lowered_value_type ce e) ==>
    compile_snapshot_vv ce (exprs_can_mutate ce xs)
      (ext_call_arg_value (lowered_value_type ce e) vv) shm = (saved,shb) /\
    expr_sim_full_code (ctx,shctx,func,shfunc) (a,b,sha,shb) /\
    create_expr_prefix a b (gas_explicit_sites ctx shctx) ctx func s (chunk ++ snap) t) /\
  (~is_word_type (lowered_value_type ce e) ==>
    expr_sim_full_code (ctx,shctx,func,shfunc) (a,m,sha,shm) /\
    create_expr_prefix a m (gas_explicit_sites ctx shctx) ctx func s chunk mid /\
    mid.vs_current_bb = m.cs_current_bb /\ mid.vs_inst_idx = LENGTH m.cs_current_insts /\
    create_expr_prefix m b (gas_explicit_sites ctx shctx) ctx func mid snap t /\
    (exprs_can_mutate ce xs ==>
      fn_has_code m b func /\
      (?j. ctor_segment_fetch func t = SOME j /\ j.inst_opcode <> PHI /\
           b.cs_next_id <= j.inst_id) /\
      (gas_origin_path T (gas_explicit_sites ctx shctx) ctx func mid [] (OK t) ==> snap = []))) /\
  bind (eval_expr cx e) (read_result cx) p = (rr,q) /\
  valid_horizon cx st0 H q.storage_trace /\
  p.gas_obs = gas_explicit ((chunk ++ snap) ++ rest) s.vs_gas_readings ++ tail ==>
  (?err. rr = INR (Error err) /\ unspecified_behaviour_exempt tops err) \/
  ?v Gt tt. rr = INL v /\
    q.gas_obs = gas_explicit rest t.vs_gas_readings ++ tail /\
    expr_sim_inv ce cx env q /\ return_buf_frame d ce b t /\ alloca_history func t /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    (!f i z. frag_reachable ctx func t f i z ==> dalloca_fmp_headroom i z) /\
    ~t.vs_halted /\ t.vs_current_bb = b.cs_current_bb /\
    t.vs_inst_idx = LENGTH b.cs_current_insts /\
    (!h. valid_horizon cx st0 h q.storage_trace ==>
      stmt_state_rel h ctx func ce cx q t /\ storage_well_formed_on cx q (FST h) /\
      ghost_inv_at (DF h) lo d ce cx q Gt tt t) /\
    (?tv ann. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
      evaluate_type (get_tenv cx) (expr_type e) = SOME ann /\
      arg_type_fits (lowered_value_type ce e) (expr_type e) /\
      value_has_type tv v /\ value_has_type ann v) /\
    (is_word_type (lowered_value_type ce e) ==>
      ?G' tn'. !K op. valid_horizon cx st0 K q.storage_trace /\
        lower_value compile_expr ce (expr_type e) e a = (op,b) ==>
        expr_sim_full_post (DF,lo,d,ctx,func) ce cx e (p,a,b,s,op,G,tn)
          K (INL v : value + exception) (q with gas_obs := []) G' tn' t) /\
    (~is_word_type (lowered_value_type ce e) ==>
      ?Gm tm raw. eval_expr cx e p = (INL raw,q) /\
      !h. valid_horizon cx st0 h q.storage_trace ==>
        vv_post h ctx func ce cx e p a m s (q with gas_obs := []) raw vv mid /\
        vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e)
          (q with gas_obs := []) raw vv mid /\
        ptr_vv_ok cx (post_value_type ce e) raw vv (q with gas_obs := []) Gm tm mid /\
        alloca_history func mid /\ s.vs_alloca_next <= mid.vs_alloca_next /\
        ghost_inv_at (DF h) lo d ce cx (q with gas_obs := []) Gm tm mid /\
        ghost_kept_at lo ce p a G tn s Gm tm /\
        (!tag op. vv = StackValue tag op /\ ~is_word_type (post_value_type ce e) ==>
          ptr_buf_ok ce e op Gm mid) /\
        (!tag p0. vv = LocatedValue tag p0 /\ p0.ptr_location = LocMemory ==>
          ptr_buf_ok ce e p0.ptr_operand Gm mid) /\
        (ce.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
          ?val. read_result cx raw (q with gas_obs := []) = (INL val,q with gas_obs := []) /\
            !rt w. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
              eval_operand (vv_operand vv) mid = SOME w ==>
              w2n w + type_memory_size rt <= lo /\
              (!mem. mem_agree_outside tm.t_mem mid.vs_memory mem ==>
                 val_in_memory rt val (w2n w) mem)))
Proof
  CONV_TAC (DEPTH_CONV BETA_CONV) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `is_word_type (lowered_value_type ce e)`
  >- (qpat_x_assum `is_word_type _ ==> _` (drule_then (map_every assume_tac o CONJUNCTS)) >>
      drule_all blueprint_ctor_word_row_at >> strip_tac
      >- (disj1_tac >> qexists_tac `err` >> simp[]) >>
      disj2_tac >> qexistsl [`v`,`G'`,`tn'`] >> simp[] >>
      rpt conj_tac >> TRY (first_assum ACCEPT_TAC >> NO_TAC) >>
      qexistsl [`G'`,`tn'`] >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `~is_word_type _ ==> _` (drule_then (map_every assume_tac o CONJUNCTS)) >>
  qpat_assum `p.gas_obs = _` (assume_tac o REWRITE_RULE [GSYM APPEND_ASSOC]) >>
  drule_all blueprint_ctor_vv_row_at >> strip_tac
  >- (disj1_tac >> qexists_tac `err` >> simp[]) >>
  disj2_tac >> qexistsl_tac [`v`,`Gt'`,`tt`] >> asm_rewrite_tac[] >>
  conj_tac >- metis_tac[] >>
  qexistsl_tac [`Gm`,`tm`,`raw`] >> asm_rewrite_tac[]
QED

(* Specialize both guarded callbacks before applying the fixed-row theorem.
   These guards refer only to this entry and its ghosts. *)
fun specialize_ctor_callbacks ghosts =
  qpat_assum `i < LENGTH args` (fn idx =>
  qpat_assum `expr_body_pre ce cx env (EL i args) p` (fn pre =>
  qpat_assum `body_const_cells_agree [(NONE,tops)] cx env p` (fn agree =>
    let
      val specialize = qspecl_then ([`i`,`p`] @ ghosts)
        (assume_tac o PURE_REWRITE_RULE [idx,pre,agree,AND_CLAUSES])
    in
      qpat_assum `!j z g h op. _ ==> gas_completed_operand _ _ _ _ _ _ _ _ _` specialize >>
      qpat_assum `!j z g h. _ ==> gas_completed_operand _ _ _ _ _ _ _ _ _` specialize
    end)))

(* R i is the residual stream including the caller's continuation. The
   callback guard is checked at the source entry of each reached row. *)
Theorem agreed_ctor_rows_at_cuts:
  body_inv tops ctx ce cx /\ shadow_body_inv tops ctx shctx /\
  (!K. dead_lo_ok K (DF K) lo ce cx) /\
  (!i p. i < LENGTH args /\ expr_sim_inv ce cx env p ==>
    expr_body_pre ce cx env (EL i args) p) /\
  (!i p g h op. i < LENGTH args /\
    expr_body_pre ce cx env (EL i args) p /\
    body_const_cells_agree [(NONE,tops)] cx env p /\
    expr_sim_full_pre (DF,lo,d,ctx,shctx,PG,func,shfunc)
      ce cx (expr_type (EL i args)) (EL i args) p
      (st0,C i,C (SUC i),Sh i,Sh (SUC i),op,St i,g,h) ==>
    gas_completed_operand (DF,lo,gas_explicit_sites ctx shctx,ctx,func,PG)
      tops cx st0 (C i) (C (SUC i)) (bind (eval_expr cx (EL i args)) (read_result cx))
      (p,St i,g,h) (expr_sim_full_post (DF,lo,d,ctx,func) ce cx (EL i args)
        (p,C i,C (SUC i),St i,op,g,h))) /\
  (!i p g h. i < LENGTH args /\
    expr_body_pre ce cx env (EL i args) p /\
    body_const_cells_agree [(NONE,tops)] cx env p /\
    expr_vv_sim_full_pre (DF,lo,d,ctx,shctx,PG,func,shfunc)
      ce cx (expr_type (EL i args)) (EL i args) p
      (st0,C i,M i,Sh i,SM i,V i,St i,g,h) ==>
    gas_completed_operand (DF,lo,gas_explicit_sites ctx shctx,ctx,func,PG)
      tops cx st0 (C i) (M i) (eval_expr cx (EL i args)) (p,St i,g,h)
      (ctor_replay_vv_post DF lo d ctx func ce cx (EL i args) p (C i) (M i) (St i) (V i) g h)) /\
  (!i. i < LENGTH args ==>
    compile_expr ce (expr_type (EL i args)) (EL i args) (C i) = (V i,M i) /\
    compile_expr (gas_shadow_env T ce) (expr_type (EL i args)) (gas_shadow_expr (EL i args)) (Sh i) = (V i,SM i) /\
    compile_snapshot_vv ce (exprs_can_mutate ce (DROP (SUC i) args))
      (ext_call_arg_value (lowered_value_type ce (EL i args)) (V i)) (M i) =
      (EL i svs,C (SUC i)) /\
    local_ptrs_reserved ce (C i) /\
    (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at (C i) x) /\
    (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at (C i) x) /\
    (St (SUC i)).vs_current_bb = (C (SUC i)).cs_current_bb /\
    (St (SUC i)).vs_inst_idx = LENGTH (C (SUC i)).cs_current_insts /\
    R i = (Chunk i ++ Snap i) ++ R (SUC i) /\
    (is_word_type (lowered_value_type ce (EL i args)) ==>
      compile_snapshot_vv ce (exprs_can_mutate ce (DROP (SUC i) args))
        (ext_call_arg_value (lowered_value_type ce (EL i args)) (V i)) (SM i) =
        (EL i svs,Sh (SUC i)) /\
      expr_sim_full_code (ctx,shctx,func,shfunc) (C i,C (SUC i),Sh i,Sh (SUC i)) /\
      create_expr_prefix (C i) (C (SUC i)) (gas_explicit_sites ctx shctx) ctx func
        (St i) (Chunk i ++ Snap i) (St (SUC i))) /\
    (~is_word_type (lowered_value_type ce (EL i args)) ==>
      expr_sim_full_code (ctx,shctx,func,shfunc) (C i,M i,Sh i,SM i) /\
      create_expr_prefix (C i) (M i) (gas_explicit_sites ctx shctx) ctx func
        (St i) (Chunk i) (Mid i) /\
      (Mid i).vs_current_bb = (M i).cs_current_bb /\
      (Mid i).vs_inst_idx = LENGTH (M i).cs_current_insts /\
      create_expr_prefix (M i) (C (SUC i)) (gas_explicit_sites ctx shctx) ctx func
        (Mid i) (Snap i) (St (SUC i)) /\
      (exprs_can_mutate ce (DROP (SUC i) args) ==>
        fn_has_code (M i) (C (SUC i)) func /\
        (?j. ctor_segment_fetch func (St (SUC i)) = SOME j /\ j.inst_opcode <> PHI /\
             (C (SUC i)).cs_next_id <= j.inst_id) /\
        (gas_origin_path T (gas_explicit_sites ctx shctx) ctx func (Mid i) [] (OK (St (SUC i))) ==>
          Snap i = [])))) /\
  bind (eval_exprs cx args) k p0 = (res,out) /\ (!vs. storage_trace_frame (k vs)) /\
  valid_horizon cx st0 H out.storage_trace /\
  p0.gas_obs = gas_explicit (R 0) (St 0).vs_gas_readings ++ tail /\
  expr_sim_inv ce cx env p0 /\ body_const_cells_agree [(NONE,tops)] cx env p0 /\
  return_buf_frame d ce (C 0) (St 0) /\
  alloca_history func (St 0) /\ (ctx_has_dalloca ctx ==> allocas_below_fmp (St 0)) /\
  (!f i z. frag_reachable ctx func (St 0) f i z ==> dalloca_fmp_headroom i z) /\
  ~(St 0).vs_halted /\ (St 0).vs_current_bb = (C 0).cs_current_bb /\
  (St 0).vs_inst_idx = LENGTH (C 0).cs_current_insts /\
  (!K. valid_horizon cx st0 K p0.storage_trace ==>
    stmt_state_rel K ctx func ce cx p0 (St 0) /\ storage_well_formed_on cx p0 (FST K) /\
    ghost_inv_at (DF K) lo d ce cx p0 G0 tn0 (St 0)) ==>
  (?err. res = INR (Error err) /\ unspecified_behaviour_exempt tops err) \/
  ?vs E Gf tf. E 0 = p0 /\ LENGTH vs = LENGTH args /\
    eval_exprs cx args p0 = (INL vs,E (LENGTH args)) /\
    k vs (E (LENGTH args)) = (res,out) /\
    valid_horizon cx st0 H (E (LENGTH args)).storage_trace /\
    (!i. i <= LENGTH args ==>
      (E i).gas_obs = gas_explicit (R i) (St i).vs_gas_readings ++ tail /\
      expr_sim_inv ce cx env (E i) /\ body_const_cells_agree [(NONE,tops)] cx env (E i) /\
      return_buf_frame d ce (C i) (St i) /\
      alloca_history func (St i) /\ (ctx_has_dalloca ctx ==> allocas_below_fmp (St i)) /\
      (!f j z. frag_reachable ctx func (St i) f j z ==> dalloca_fmp_headroom j z) /\
      ~(St i).vs_halted /\ (St i).vs_current_bb = (C i).cs_current_bb /\
      (St i).vs_inst_idx = LENGTH (C i).cs_current_insts) /\
    (!K. valid_horizon cx st0 K (E (LENGTH args)).storage_trace ==>
      stmt_state_rel K ctx func ce cx (E (LENGTH args)) (St (LENGTH args)) /\
      storage_well_formed_on cx (E (LENGTH args)) (FST K) /\
      ghost_inv_at (DF K) lo d ce cx (E (LENGTH args)) Gf tf (St (LENGTH args))) /\
    (!i. i < LENGTH args ==>
      bind (eval_expr cx (EL i args)) (read_result cx) (E i) = (INL (EL i vs),E (SUC i)) /\
      (St (SUC i)).vs_labels = (St i).vs_labels /\
      expr_body_pre ce cx env (EL i args) (E i) /\
      (?tv ann. evaluate_type (get_tenv cx) (lowered_value_type ce (EL i args)) = SOME tv /\
        evaluate_type (get_tenv cx) (expr_type (EL i args)) = SOME ann /\
        arg_type_fits (lowered_value_type ce (EL i args)) (expr_type (EL i args)) /\
        value_has_type tv (EL i vs) /\ value_has_type ann (EL i vs)) /\
      (!g h. (!K. valid_horizon cx st0 K (E i).storage_trace ==>
          stmt_state_rel K ctx func ce cx (E i) (St i) /\
          storage_well_formed_on cx (E i) (FST K) /\
          ghost_inv_at (DF K) lo d ce cx (E i) g h (St i)) ==>
        (is_word_type (lowered_value_type ce (EL i args)) ==>
          ?g' h'. !K op. valid_horizon cx st0 K (E (SUC i)).storage_trace /\
            lower_value compile_expr ce (expr_type (EL i args)) (EL i args) (C i) =
              (op,C (SUC i)) ==>
            expr_sim_full_post (DF,lo,d,ctx,func) ce cx (EL i args)
              (E i,C i,C (SUC i),St i,op,g,h) K (INL (EL i vs) : value + exception)
              ((E (SUC i)) with gas_obs := []) g' h' (St (SUC i))) /\
        (~is_word_type (lowered_value_type ce (EL i args)) ==>
          ?g' h' raw. eval_expr cx (EL i args) (E i) = (INL raw,E (SUC i)) /\
          !K. valid_horizon cx st0 K (E (SUC i)).storage_trace ==>
            vv_post K ctx func ce cx (EL i args) (E i) (C i) (M i) (St i)
              ((E (SUC i)) with gas_obs := []) raw (V i) (Mid i) /\
            vv_store_bound cx (post_value_type ce (EL i args)) (lowered_value_type ce (EL i args))
              ((E (SUC i)) with gas_obs := []) raw (V i) (Mid i) /\
            ptr_vv_ok cx (post_value_type ce (EL i args)) raw (V i)
              ((E (SUC i)) with gas_obs := []) g' h' (Mid i) /\
            alloca_history func (Mid i) /\ (St i).vs_alloca_next <= (Mid i).vs_alloca_next /\
            ghost_inv_at (DF K) lo d ce cx ((E (SUC i)) with gas_obs := []) g' h' (Mid i) /\
            ghost_kept_at lo ce (E i) (C i) g h (St i) g' h' /\
            (!tag op. V i = StackValue tag op /\ ~is_word_type (post_value_type ce (EL i args)) ==>
              ptr_buf_ok ce (EL i args) op g' (Mid i)) /\
            (!tag p. V i = LocatedValue tag p /\ p.ptr_location = LocMemory ==>
              ptr_buf_ok ce (EL i args) p.ptr_operand g' (Mid i)) /\
            (ce.ce_is_ctor /\ vv_location (V i) = SOME LocCode ==>
              ?val. read_result cx raw ((E (SUC i)) with gas_obs := []) =
                (INL val,(E (SUC i)) with gas_obs := []) /\
              !rt w. evaluate_type (get_tenv cx) (post_value_type ce (EL i args)) = SOME rt /\
                eval_operand (vv_operand (V i)) (Mid i) = SOME w ==>
                w2n w + type_memory_size rt <= lo /\
                (!mem. mem_agree_outside h'.t_mem (Mid i).vs_memory mem ==>
                  val_in_memory rt val (w2n w) mem)))))
Proof
  CONV_TAC (DEPTH_CONV BETA_CONV) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `Entry = \i p g h.
    p.gas_obs = gas_explicit (R i) (St i).vs_gas_readings ++ tail /\
    expr_sim_inv ce cx env p /\ body_const_cells_agree [(NONE,tops)] cx env p /\
    return_buf_frame d ce (C i) (St i) /\
    alloca_history func (St i) /\ (ctx_has_dalloca ctx ==> allocas_below_fmp (St i)) /\
    (!f j z. frag_reachable ctx func (St i) f j z ==> dalloca_fmp_headroom j z) /\
    ~(St i).vs_halted /\ (St i).vs_current_bb = (C i).cs_current_bb /\
    (St i).vs_inst_idx = LENGTH (C i).cs_current_insts /\
    (!K. valid_horizon cx st0 K p.storage_trace ==>
      stmt_state_rel K ctx func ce cx p (St i) /\ storage_well_formed_on cx p (FST K) /\
      ghost_inv_at (DF K) lo d ce cx p g h (St i))` >>
  `Entry 0 p0 G0 tn0` by (simp[Abbr `Entry`] >> first_assum ACCEPT_TAC) >>
  `valid_horizon cx st0 H p0.storage_trace` by
    (qpat_assum `bind (eval_exprs cx args) k p0 = _`
       (mp_then Any irule valid_horizon_frame) >>
     simp[evaluate_storage_trace_frame,storage_trace_frame_bind_all]) >>
  qabbrev_tac `P = \i p. valid_horizon cx st0 H p.storage_trace /\ ?g h. Entry i p g h` >>
  `P 0 p0` by (simp[Abbr `P`] >> qexistsl [`G0`,`tn0`] >> first_assum ACCEPT_TAC) >>
  qspecl_then [`LENGTH args`,`0`,`p0`,`k`] mp_tac
    (Q.INST [`es` |-> `args`] blueprint_ctor_source_walk) >>
  simp[] >>
  (impl_tac >- suspend "step") >> strip_tac
  >- (disj1_tac >> qexists_tac `err` >> simp[]) >>
  suspend "success"
QED

Resume agreed_ctor_rows_at_cuts[step]:
  map_every qx_gen_tac [`i`,`p`,`l`] >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `P i p` mp_tac >> simp[Abbr `P`,Abbr `Entry`] >> strip_tac >>
  qpat_assum `!i. _ ==> compile_expr _ _ _ _ = _ /\ _`
    (qspec_then `i` (drule_then (map_every assume_tac o CONJUNCTS))) >>
  `expr_body_pre ce cx env (EL i args) p` by metis_tac[] >>
  `p.gas_obs = gas_explicit ((Chunk i ++ Snap i) ++ R (SUC i)) (St i).vs_gas_readings ++ tail`
    by fs[] >>
  `?rr q. bind (eval_expr cx (EL i args)) (read_result cx) p = (rr,q)` by
    (Cases_on `bind (eval_expr cx (EL i args)) (read_result cx) p` >> simp[]) >>
  `valid_horizon cx st0 H q.storage_trace` by
    (qpat_assum `bind (bind _ _) l p = _` mp_tac >> pure_once_rewrite_tac[bind_def] >>
     Cases_on `rr` >> simp[] >> strip_tac >>
     qpat_assum `l _ q = _` (mp_then Any irule valid_horizon_frame) >> simp[]) >>
  suspend "step_replay"
QED

Resume agreed_ctor_rows_at_cuts[success]:
  `!i. i <= LENGTH args ==> valid_horizon cx st0 H (E i).storage_trace /\
     ?g h. Entry i (E i) g h` by fs[Abbr `P`] >>
  `valid_horizon cx st0 H (E (LENGTH args)).storage_trace` by simp[] >>
  `?g h. Entry (LENGTH args) (E (LENGTH args)) g h` by simp[] >>
  disj2_tac >> qexistsl_tac [`vs`,`E`,`g`,`h`] >> asm_rewrite_tac[] >>
  conj_tac
  >- (gen_tac >> disch_tac >>
      qpat_assum `!i. _ ==> _ /\ ?g h. Entry i _ g h` (qspec_then `i` mp_tac) >>
      simp[Abbr `Entry`] >> metis_tac[]) >>
  conj_tac
  >- (qpat_assum `Entry (LENGTH args) _ g h` mp_tac >>
      simp[Abbr `Entry`] >> metis_tac[]) >>
  suspend "callbacks"
QED

Resume agreed_ctor_rows_at_cuts[step_replay]:
  specialize_ctor_callbacks [`g`,`h`] >>
  drule_all agreed_ctor_row_replay >> strip_tac
  >- (disj1_tac >> qexists_tac `err` >> fs[bind_def]) >>
  `body_const_cells_agree [(NONE,tops)] cx env q` by
    (irule body_const_cells_agree_expr_read >>
     qpat_assum `bind (eval_expr cx (EL i args)) (read_result cx) p = _` (irule_at Any) >>
     simp[] >> drule expr_body_pre_static_facts >> simp[]) >>
  disj2_tac >> qexistsl_tac [`v`,`q`] >> simp[] >>
  conj_tac
  >- (qpat_assum `bind (bind _ _) l p = _` mp_tac >> pure_once_rewrite_tac[bind_def] >> simp[]) >>
  qexistsl_tac [`Gt'`,`tt`] >> conj_tac >- first_assum ACCEPT_TAC >>
  rpt strip_tac >> first_x_assum (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC
QED

Resume agreed_ctor_rows_at_cuts[callbacks]:
  qx_gen_tac `i` >> disch_tac >>
  `i <= LENGTH args /\ SUC i <= LENGTH args` by decide_tac >>
  `valid_horizon cx st0 H (E (SUC i)).storage_trace` by simp[] >>
  qpat_assum `!i. i < LENGTH args ==> bind _ _ _ = _`
    (qspec_then `i` (drule_then assume_tac)) >>
  qpat_assum `!i. _ ==> compile_expr _ _ _ _ = _ /\ _`
    (qspec_then `i` (drule_then (map_every assume_tac o CONJUNCTS))) >>
  `?Gin tin. Entry i (E i) Gin tin` by simp[] >>
  qpat_x_assum `Entry i (E i) _ _` mp_tac >> simp[Abbr `Entry`] >> strip_tac >>
  `expr_body_pre ce cx env (EL i args) (E i)` by metis_tac[] >>
  `(St (SUC i)).vs_labels = (St i).vs_labels` by
    (Cases_on `is_word_type (lowered_value_type ce (EL i args))` >>
     (first_x_assum (drule_then strip_assume_tac)) >> metis_tac[create_prefix_labels]) >>
  `(E i).gas_obs = gas_explicit ((Chunk i ++ Snap i) ++ R (SUC i)) (St i).vs_gas_readings ++ tail`
    by fs[] >>
  qpat_assum `bind _ _ (E i) = _` (fn th => rewrite_tac [th]) >>
  qpat_assum `expr_body_pre ce cx env (EL i args) (E i)` (fn th => rewrite_tac [th]) >>
  qpat_assum `(St (SUC i)).vs_labels = _` (fn th => rewrite_tac [th]) >>
  suspend "row_posts"
QED

Resume agreed_ctor_rows_at_cuts[row_posts]:
  qabbrev_tac `p = E i` >>
  conj_tac
  >- (specialize_ctor_callbacks [`Gin`,`tin`] >>
      drule_all agreed_ctor_row_replay >> strip_tac >- fs[] >>
      qexistsl_tac [`tv`,`ann`] >> fs[]) >>
  qpat_x_assum `!K. _ ==> stmt_state_rel K _ _ _ _ p _ /\ _` (mk_asm "row_entry") >>
  map_every qx_gen_tac [`Ga`,`ta`] >> disch_tac >>
  `!K. valid_horizon cx st0 K p.storage_trace ==>
    stmt_state_rel K ctx func ce cx p (St i) /\
    storage_well_formed_on cx p (FST K) /\
    ghost_inv_at (DF K) lo d ce cx p Ga ta (St i)` by
    (asm "row_entry" mp_tac >> metis_tac[]) >>
  asm_x "row_entry" kall_tac >>
  specialize_ctor_callbacks [`Ga`,`ta`] >>
  drule_all agreed_ctor_row_replay >> strip_tac >- fs[] >>
  gvs[AC ADD_ASSOC ADD_COMM]
QED
Finalise agreed_ctor_rows_at_cuts
