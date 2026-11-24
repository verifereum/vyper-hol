Theory createSizeCtorRowsReplayMods
Ancestors
  createSizeCtorRowsReplay createExprSizeExitDefsMods
  gasShadowCompileBase
  e2eDefs exprSimFullBundleProps fragExec gasExplicitSites gasSummary venomState vyperState
  relation list words pair arithmetic exprLowering vfmConstants compileEnv exprLoweringProps
  vyperStorageTrace rich_list exprSimHypsDefs vyperTypeSystem bodyPtrDefs loweringPosts
  context vyperAST vyperStorageFootprint vyperTyping vyperValue integer_word valueEncoding
  createCtorSegmentArrival loweringStateRelDefs exprSimMemDefs ptrDiscipline bodySim
  createExprSizeExitDefs createSizeCtorValueRowMods createSizeCtorWordRowMods

(* Replay one reached row, retaining both the next entry and the producer's
   view at the expression cut. The two ghost pairs in the VV arm serve
   different purposes. *)

Theorem blueprint_ctor_row_dispatch_mods[local]:
  contract_inv mods exps ctx ce cx /\
  module_body_inv mods src tops ce cx /\ shadow_body_inv_mods mods exps ctx shctx /\
  expr_body_pre_mods mods ce cx env e p /\ create_operand_completed_ok_mods mods exps cx e /\
  compile_expr ce (expr_type e) e a = (vv,m) /\
  compile_expr (gas_shadow_env T ce) (expr_type e) (gas_shadow_expr e) sha = (vv,shm) /\
  compile_snapshot_vv ce (exprs_can_mutate ce xs)
    (ext_call_arg_value (lowered_value_type ce e) vv) m = (saved,b) /\
  local_ptrs_reserved ce a /\ (!h. dead_lo_ok_mods h (DF h) lo ce cx) /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at a x) /\
  return_buf_frame d ce a s /\ alloca_history func s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  (!f i z. frag_reachable ctx func s f i z ==> dalloca_fmp_headroom i z) /\
  (!h. valid_horizon cx st0 h p.storage_trace ==>
     stmt_state_rel h ctx func ce cx p s /\
     immutable_frame_mods func ce cx p s /\ storage_well_formed_on cx p (FST h) /\
     ghost_inv_at_mods (DF h) lo d ce cx p G tn s) /\
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
  (?err. rr = INR (Error err) /\ unspecified_behaviour_exempt_mods mods err) \/
  ?v Gt tt. rr = INL v /\
    q.gas_obs = gas_explicit rest t.vs_gas_readings ++ tail /\
    expr_sim_inv_mods mods ce cx env q /\ return_buf_frame d ce b t /\ alloca_history func t /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    (!f i z. frag_reachable ctx func t f i z ==> dalloca_fmp_headroom i z) /\
    ~t.vs_halted /\ t.vs_current_bb = b.cs_current_bb /\
    t.vs_inst_idx = LENGTH b.cs_current_insts /\
    (!h. valid_horizon cx st0 h q.storage_trace ==>
      stmt_state_rel h ctx func ce cx q t /\
      immutable_frame_mods func ce cx q t /\ storage_well_formed_on cx q (FST h) /\
      ghost_inv_at_mods (DF h) lo d ce cx q Gt tt t) /\
    (?tv ann. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
      evaluate_type (get_tenv cx) (expr_type e) = SOME ann /\
      arg_type_fits (lowered_value_type ce e) (expr_type e) /\
      value_has_type tv v /\ value_has_type ann v) /\
    (is_word_type (lowered_value_type ce e) ==>
      ?G' tn'. !K op. valid_horizon cx st0 K q.storage_trace /\
        lower_value compile_expr ce (expr_type e) e a = (op,b) ==>
        expr_sim_full_post_mods (DF,lo,d,ctx,func) ce cx e (p,a,b,s,op,G,tn)
          K (INL v : value + exception) (q with gas_obs := []) G' tn' t) /\
    (~is_word_type (lowered_value_type ce e) ==>
      ?Gm tm raw. eval_expr cx e p = (INL raw,q) /\
      !h. valid_horizon cx st0 h q.storage_trace ==>
        vv_post_mods h ctx func ce cx e p a m s (q with gas_obs := []) raw vv mid /\
        vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e)
          (q with gas_obs := []) raw vv mid /\
        ptr_vv_ok cx (post_value_type ce e) raw vv (q with gas_obs := []) Gm tm mid /\
        alloca_history func mid /\ s.vs_alloca_next <= mid.vs_alloca_next /\
        ghost_inv_at_mods (DF h) lo d ce cx (q with gas_obs := []) Gm tm mid /\
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
  cheat
QED

Theorem create_ctor_rows_at_cuts_mods:
  contract_inv mods exps ctx ce cx /\
  module_body_inv mods src tops ce cx /\ shadow_body_inv_mods mods exps ctx shctx /\
  (!K. dead_lo_ok_mods K (DF K) lo ce cx) /\
  (!i. i < LENGTH args ==> create_operand_completed_ok_mods mods exps cx (EL i args)) /\
  (!i p. i < LENGTH args /\ expr_sim_inv_mods mods ce cx env p ==>
    expr_body_pre_mods mods ce cx env (EL i args) p) /\
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
  expr_sim_inv_mods mods ce cx env p0 /\ return_buf_frame d ce (C 0) (St 0) /\
  alloca_history func (St 0) /\ (ctx_has_dalloca ctx ==> allocas_below_fmp (St 0)) /\
  (!f i z. frag_reachable ctx func (St 0) f i z ==> dalloca_fmp_headroom i z) /\
  ~(St 0).vs_halted /\ (St 0).vs_current_bb = (C 0).cs_current_bb /\
  (St 0).vs_inst_idx = LENGTH (C 0).cs_current_insts /\
  (!K. valid_horizon cx st0 K p0.storage_trace ==>
    stmt_state_rel K ctx func ce cx p0 (St 0) /\
    immutable_frame_mods func ce cx p0 (St 0) /\ storage_well_formed_on cx p0 (FST K) /\
    ghost_inv_at_mods (DF K) lo d ce cx p0 G0 tn0 (St 0)) ==>
  (?err. res = INR (Error err) /\ unspecified_behaviour_exempt_mods mods err) \/
  ?vs E Gf tf. E 0 = p0 /\ LENGTH vs = LENGTH args /\
    eval_exprs cx args p0 = (INL vs,E (LENGTH args)) /\
    k vs (E (LENGTH args)) = (res,out) /\
    valid_horizon cx st0 H (E (LENGTH args)).storage_trace /\
    (!i. i <= LENGTH args ==>
      (E i).gas_obs = gas_explicit (R i) (St i).vs_gas_readings ++ tail /\
      expr_sim_inv_mods mods ce cx env (E i) /\ return_buf_frame d ce (C i) (St i) /\
      alloca_history func (St i) /\ (ctx_has_dalloca ctx ==> allocas_below_fmp (St i)) /\
      (!f j z. frag_reachable ctx func (St i) f j z ==> dalloca_fmp_headroom j z) /\
      ~(St i).vs_halted /\ (St i).vs_current_bb = (C i).cs_current_bb /\
      (St i).vs_inst_idx = LENGTH (C i).cs_current_insts) /\
    (!K. valid_horizon cx st0 K (E (LENGTH args)).storage_trace ==>
      stmt_state_rel K ctx func ce cx (E (LENGTH args)) (St (LENGTH args)) /\
      immutable_frame_mods func ce cx (E (LENGTH args)) (St (LENGTH args)) /\
      storage_well_formed_on cx (E (LENGTH args)) (FST K) /\
      ghost_inv_at_mods (DF K) lo d ce cx (E (LENGTH args)) Gf tf (St (LENGTH args))) /\
    (!i. i < LENGTH args ==>
      bind (eval_expr cx (EL i args)) (read_result cx) (E i) = (INL (EL i vs),E (SUC i)) /\
      expr_body_pre_mods mods ce cx env (EL i args) (E i) /\
      (?tv ann. evaluate_type (get_tenv cx) (lowered_value_type ce (EL i args)) = SOME tv /\
        evaluate_type (get_tenv cx) (expr_type (EL i args)) = SOME ann /\
        arg_type_fits (lowered_value_type ce (EL i args)) (expr_type (EL i args)) /\
        value_has_type tv (EL i vs) /\ value_has_type ann (EL i vs)) /\
      (!g h. (!K. valid_horizon cx st0 K (E i).storage_trace ==>
          stmt_state_rel K ctx func ce cx (E i) (St i) /\
          storage_well_formed_on cx (E i) (FST K) /\
          ghost_inv_at_mods (DF K) lo d ce cx (E i) g h (St i)) ==>
        (is_word_type (lowered_value_type ce (EL i args)) ==>
          ?g' h'. !K op. valid_horizon cx st0 K (E (SUC i)).storage_trace /\
            lower_value compile_expr ce (expr_type (EL i args)) (EL i args) (C i) =
              (op,C (SUC i)) ==>
            expr_sim_full_post_mods (DF,lo,d,ctx,func) ce cx (EL i args)
              (E i,C i,C (SUC i),St i,op,g,h) K (INL (EL i vs) : value + exception)
              ((E (SUC i)) with gas_obs := []) g' h' (St (SUC i))) /\
        (~is_word_type (lowered_value_type ce (EL i args)) ==>
          ?g' h' raw. eval_expr cx (EL i args) (E i) = (INL raw,E (SUC i)) /\
          !K. valid_horizon cx st0 K (E (SUC i)).storage_trace ==>
            vv_post_mods K ctx func ce cx (EL i args) (E i) (C i) (M i) (St i)
              ((E (SUC i)) with gas_obs := []) raw (V i) (Mid i) /\
            vv_store_bound cx (post_value_type ce (EL i args)) (lowered_value_type ce (EL i args))
              ((E (SUC i)) with gas_obs := []) raw (V i) (Mid i) /\
            ptr_vv_ok cx (post_value_type ce (EL i args)) raw (V i)
              ((E (SUC i)) with gas_obs := []) g' h' (Mid i) /\
            alloca_history func (Mid i) /\ (St i).vs_alloca_next <= (Mid i).vs_alloca_next /\
            ghost_inv_at_mods (DF K) lo d ce cx ((E (SUC i)) with gas_obs := []) g' h' (Mid i) /\
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
  cheat
QED
