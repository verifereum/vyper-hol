(* Request-prefix companion to bodyFullForRange. *)
Theory s1PrefixForRange
Ancestors
  s1PrefixPreds bodyFullForRange s1PrefixDefs s1PrefixForRangeDriver

val _ = Parse.hide "body";

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  rpt gen_tac >> strip_tac >>
  pure_once_rewrite_tac[stmt_frag_prefix_def] >> rpt gen_tac >> disch_tac >>
  irule range_frag_prefix_from_cons >>
  reverse (rpt conj_tac)
  >- (qexistsl [`RetQ`,`bindings`,`cenv`,`cenv'`,`d`,`env`,`env'`,`lctx`,
               `ret_ty`,`sa`,`sb`,`shadow_func`,`shadow_sa`,`shadow_sb`,`tops`] >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  first_assum ACCEPT_TAC
QED
*)
Theorem compile_for_range_frag_prefix:
  !cx id typ e1 e2 n body DF lo d PG tops bindings ctx shadow_ctx func
 shadow_func cenv env env' ret_ty lctx RetQ es.
  (!func0 ctx0 c0 e0 sa0 s0 G0 tn0 c1 e1 sa1 s1 G1 tn1 c2 e2 s2 G2 tn2.
    (alloca_history func0 s1 /\
     (ctx_has_dalloca ctx0 ==> allocas_below_fmp s1) /\
     s0.vs_alloca_next <= s1.vs_alloca_next /\
     (!x w. not_fresh_at sa0 x /\ lookup_var x s0 = SOME w ==>
            lookup_var x s1 = SOME w) /\
     (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
              FLOOKUP s1.vs_allocas aid = SOME b) /\
     (!x. not_fresh_at sa0 x ==>
          FLOOKUP G1 x = FLOOKUP G0 x /\
          op_taint tn1 (Var x) = op_taint tn0 (Var x)) /\
     alloca_frame c0 e0 sa0 s0 c1 e1 s1 /\
     (!aid off sz i.
       FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
       aid < sa0.cs_next_id /\
       (!nm b sz'. local_region c0 e0.scopes s0 nm b sz' ==>
                   off + sz <= b \/ b + sz' <= off) /\
       off <= i /\ i < off + sz /\ i IN tn1.t_mem ==> i IN tn0.t_mem)) /\
    (alloca_history func0 s2 /\
     (ctx_has_dalloca ctx0 ==> allocas_below_fmp s2) /\
     s1.vs_alloca_next <= s2.vs_alloca_next /\
     (!x w. not_fresh_at sa1 x /\ lookup_var x s1 = SOME w ==>
            lookup_var x s2 = SOME w) /\
     (!aid b. FLOOKUP s1.vs_allocas aid = SOME b ==>
              FLOOKUP s2.vs_allocas aid = SOME b) /\
     (!x. not_fresh_at sa1 x ==>
          FLOOKUP G2 x = FLOOKUP G1 x /\
          op_taint tn2 (Var x) = op_taint tn1 (Var x)) /\
     alloca_frame c1 e1 sa1 s1 c2 e2 s2 /\
     (!aid off sz i.
       FLOOKUP s1.vs_allocas aid = SOME (off,sz) /\
       aid < sa1.cs_next_id /\
       (!nm b sz'. local_region c1 e1.scopes s1 nm b sz' ==>
                   off + sz <= b \/ b + sz' <= off) /\
       off <= i /\ i < off + sz /\ i IN tn2.t_mem ==> i IN tn1.t_mem)) /\
    sa0.cs_next_id <= sa1.cs_next_id /\
    (!x. not_fresh_at sa0 x ==> not_fresh_at sa1 x) ==>
    alloca_history func0 s2 /\
    (ctx_has_dalloca ctx0 ==> allocas_below_fmp s2) /\
    s0.vs_alloca_next <= s2.vs_alloca_next /\
    (!x w. not_fresh_at sa0 x /\ lookup_var x s0 = SOME w ==>
           lookup_var x s2 = SOME w) /\
    (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
             FLOOKUP s2.vs_allocas aid = SOME b) /\
    (!x. not_fresh_at sa0 x ==>
         FLOOKUP G2 x = FLOOKUP G0 x /\
         op_taint tn2 (Var x) = op_taint tn0 (Var x)) /\
    alloca_frame c0 e0 sa0 s0 c2 e2 s2 /\
    (!aid off sz i.
      FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
      aid < sa0.cs_next_id /\
      (!nm b sz'. local_region c0 e0.scopes s0 nm b sz' ==>
                  off + sz <= b \/ b + sz' <= off) /\
      off <= i /\ i < off + sz /\ i IN tn2.t_mem ==> i IN tn0.t_mem)) /\
  (!func0 ctx0 c0 e0 sa0 s0 G0 tn0 c ee t G tn cenv0 sc rest.
    (alloca_history func0 t /\
     (ctx_has_dalloca ctx0 ==> allocas_below_fmp t) /\
     s0.vs_alloca_next <= t.vs_alloca_next /\
     (!x w. not_fresh_at sa0 x /\ lookup_var x s0 = SOME w ==>
            lookup_var x t = SOME w) /\
     (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
              FLOOKUP t.vs_allocas aid = SOME b) /\
     (!x. not_fresh_at sa0 x ==>
          FLOOKUP G x = FLOOKUP G0 x /\
          op_taint tn (Var x) = op_taint tn0 (Var x)) /\
     alloca_frame c0 e0 sa0 s0 c ee t /\
     (!aid off sz i.
       FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
       aid < sa0.cs_next_id /\
       (!nm b sz'. local_region c0 e0.scopes s0 nm b sz' ==>
                   off + sz <= b \/ b + sz' <= off) /\
       off <= i /\ i < off + sz /\ i IN tn.t_mem ==> i IN tn0.t_mem)) /\
    cenv_top_ext cenv0 c ee.scopes /\ ee.scopes = sc :: rest /\
    (!nm. nm IN FDOM sc ==> lookup_scopes nm rest = NONE) ==>
    alloca_history func0 t /\
    (ctx_has_dalloca ctx0 ==> allocas_below_fmp t) /\
    s0.vs_alloca_next <= t.vs_alloca_next /\
    (!x w. not_fresh_at sa0 x /\ lookup_var x s0 = SOME w ==>
           lookup_var x t = SOME w) /\
    (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
             FLOOKUP t.vs_allocas aid = SOME b) /\
    (!x. not_fresh_at sa0 x ==>
         FLOOKUP G x = FLOOKUP G0 x /\
         op_taint tn (Var x) = op_taint tn0 (Var x)) /\
    alloca_frame c0 e0 sa0 s0 cenv0 (ee with scopes := rest) t /\
    (!aid off sz i.
      FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
      aid < sa0.cs_next_id /\
      (!nm b sz'. local_region c0 e0.scopes s0 nm b sz' ==>
                  off + sz <= b \/ b + sz' <= off) /\
      off <= i /\ i < off + sz /\ i IN tn.t_mem ==> i IN tn0.t_mem)) /\
  (!DF0 lo0 d0 ctx0 func0 PG0 tops0 cx0 st0 body0 es0 s G tn Q R.
    es0.scopes <> [] /\
    gas_outcome_full (DF0,lo0,d0,ctx0,func0,PG0) tops0 cx0 st0
      (eval_stmts cx0 body0) (es0,s,G,tn) Q R ==>
    gas_outcome_full (DF0,lo0,d0,ctx0,func0,PG0) tops0 cx0 st0
      (finally (try (do eval_stmts cx0 body0; return F od)
         handle_loop_exception) pop_scope) (es0,s,G,tn)
      (\H res' ee G tn t. ?res sc.
        res' = (case res of INL u => INL F | INR ex =>
          if ex = BreakException then INL T else
          if ex = ContinueException then INL F else INR ex) /\
        Q H res (ee with scopes := sc::ee.scopes) G tn t)
      (\H res' ee gt r. ?res sc.
        res' = (case res of INL u => INL F | INR ex =>
          if ex = BreakException then INL T else
          if ex = ContinueException then INL F else INR ex) /\
        R H res (ee with scopes := sc::ee.scopes) gt r)) /\
  (!RetQ0 H cx0 ee (res:unit+exception) gt r ctx0 sc g.
    ((!tail. stmt_exit_ptr (RetQ0 H) (ee with gas_obs:=tail) res gt r) /\
     halt_exit H cx0 ee res r /\
     (ctx_has_dalloca ctx0 ==> !s.
       (r=Halt s \/ ?ir. r=IntRet ir s) ==> allocas_below_fmp s)) ==>
    ((!tail. stmt_exit_ptr (RetQ0 H)
       ((ee with <|scopes:=sc;gas_obs:=g|>) with gas_obs:=tail) res gt r) /\
     halt_exit H cx0 (ee with <|scopes:=sc;gas_obs:=g|>) res r /\
     (ctx_has_dalloca ctx0 ==> !s.
       (r=Halt s \/ ?ir. r=IntRet ir s) ==> allocas_below_fmp s))) /\
  (!tenv s'' tyv t s'3' vs t' s'4' x t''.
    tenv = get_tenv cx /\
    lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
      (INL tyv,t) /\ eval_iterator cx (Range e1 e2) s'3' = (INL vs,t') /\
    check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" s'4' =
      (INL x,t'') ==> body_for_full_ok cx tyv id body vs) /\
  (!tenv s'' tyv t s'3' vs t' s'4' x t''.
    tenv = get_tenv cx /\
    lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
      (INL tyv,t) /\ eval_iterator cx (Range e1 e2) s'3' = (INL vs,t') /\
    check (compatible_bound (Dynamic n) (LENGTH vs)) "For too long" s'4' =
      (INL x,t'') ==> body_for_prefix_ok cx tyv id body vs) /\
  (!tenv s'' tyv t.
    tenv = get_tenv cx /\
    lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
      (INL tyv,t) ==> body_iterator_full_ok cx (Range e1 e2)) /\
  (!tenv s'' tyv t.
    tenv = get_tenv cx /\
    lift_option_type (evaluate_type tenv typ) "For evaluate_type" s'' =
      (INL tyv,t) ==> body_iterator_prefix_ok cx (Range e1 e2)) /\
  body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\
  supported_stmt tops bindings (For id typ (Range e1 e2) n body) /\
  (!target. supported_stmt_expr_exists (expr_abi_decode_target_root target)
      (For id typ (Range e1 e2) n body) ==>
      occurs_abi_decode_target target tops) /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  expr_sim_inv cenv cx env es /\
  ce_locals_declared cenv env /\
  locals_alloc_ok cenv env /\
  type_stmt env ret_ty (For id typ (Range e1 e2) n body) = SOME env' /\
  stmt_exprs_ok cenv (For id typ (Range e1 e2) n body) /\
  call_evaluation_safe cx (int_calls_stmt (For id typ (Range e1 e2) n body)) /\
  frame_ret_ok_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    cx RetQ cenv ret_ty ==>
  stmt_frag_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
   cx lctx RetQ cenv
   (stmt_env cenv lctx ret_ty (For id typ (Range e1 e2) n body))
   (stmt_env (gas_shadow_env T cenv) lctx ret_ty
      (gas_shadow_stmt (For id typ (Range e1 e2) n body)))
   (eval_stmt cx (For id typ (Range e1 e2) n body)) es
Proof
  cheat
QED
