(* Source GAS origins, memory bounds and pointer ghosts share one witness.
   Inputs and posts are stated at every finite horizon valid for the
   start and end traces; the dead mask is DF H. *)
Theory bodySimFull
Ancestors
  exprSimMapDefs ptrDiscipline unitMemInv contextRawReachable
  gasOutcomeFull bodyPtrDefs vyperStorageFootprint exprSimMemDefs stmtSimDefs
  gasShadow gasShadowState gasShadowUnit gasExplicitSites gasShadowCompileBase
  exprLowering stmtLowering loweringPosts compileEnv allocaHistory
  vyperInterpreter vyperState venomState venomWf list option

Definition expr_map_sim_full_def:
  expr_map_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
    cenv cx ty e es <=>
    !st0 sa sb shadow_sa shadow_sb vv s0 G0 tn0.
      compile_expr cenv ty e sa = (vv, sb) /\
      compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr e) shadow_sa = (vv, shadow_sb) /\
      gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
      gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
      gas_shadow_function func shadow_func /\
      MEM func ctx.ctx_functions /\
      MEM shadow_func shadow_ctx.ctx_functions /\
      fn_has_code sa sb func /\
      fn_has_code shadow_sa shadow_sb shadow_func /\
      fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
      (!H. dead_lo_ok H (DF H) lo cenv cx) /\
      (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
              not_fresh_at sa x) /\
      (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
              not_fresh_at sa x) /\
      gas_admissible (eval_expr cx e) expr_map_res_ok es /\
      return_buf_frame d cenv sa s0 /\
      alloca_history func s0 /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
      (!fn inst s. frag_reachable ctx func s0 fn inst s ==>
                  dalloca_fmp_headroom inst s) /\
      (!H. valid_horizon cx st0 H es.storage_trace ==>
        stmt_state_rel H ctx func cenv cx es s0 /\
        storage_well_formed_on cx es (FST H) /\
        ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\ ~s0.vs_halted /\
      s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
      gas_outcome_full
        (DF, lo, gas_explicit_sites ctx shadow_ctx, ctx, func, PG)
        (cx_tops cx) cx st0 (eval_expr cx e) (es, s0, G0, tn0)
        (\H res ee G tn t. ?tr slot kt vt tp p.
          res = INL (HashMapRef tr slot kt vt) /\
          storage_mapping_region cx tr slot (HashMapT kt vt) /\
          vv = LocatedValue tp p /\ p.ptr_location = slot_loc tr /\
          eval_operand p.ptr_operand t = SOME slot /\
          stmt_state_rel H ctx func cenv cx ee t /\
          storage_well_formed_on cx ee (FST H) /\
          (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
                 lookup_var x t = SOME w) /\
          (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
                   FLOOKUP t.vs_allocas aid = SOME b) /\
          (!aid off sz.
             FLOOKUP s0.vs_allocas aid = SOME (off, sz) /\
             aid < sa.cs_next_id /\
             (!n b sz'. local_region cenv es.scopes s0 n b sz' ==>
                        off + sz <= b \/ b + sz' <= off) ==>
             mem_bytes_at off sz t.vs_memory =
               mem_bytes_at off sz s0.vs_memory) /\
          locals_kept cenv es ee s0 t /\
          (~expr_has_effect e ==> pure_frame cenv func es sa s0 t) /\
          return_buf_frame d cenv sa t /\
          t.vs_current_bb = sb.cs_current_bb /\
          t.vs_inst_idx = LENGTH sb.cs_current_insts /\
          alloca_history func t /\
          (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
          s0.vs_alloca_next <= t.vs_alloca_next /\
          ghost_inv_at (DF H) lo d cenv cx ee G tn t /\
          op_taint tn p.ptr_operand = {} /\
          op_prov G p.ptr_operand = NONE /\
          ghost_kept_at lo cenv es sa G0 tn0 s0 G tn)
        (\H res ee gt r.
          expr_exit res r /\ halt_exit H cx ee res r /\
          (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s))
End

Definition expr_sim_full_def:
  expr_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
    cenv cx ty e es <=>
    !st0 sa sb shadow_sa shadow_sb op s0 G0 tn0.
      lower_value compile_expr cenv ty e sa = (op, sb) /\
      lower_value compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr e) shadow_sa =
        (op, shadow_sb) /\
      gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
      gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
      gas_shadow_function func shadow_func /\
      MEM func ctx.ctx_functions /\
      MEM shadow_func shadow_ctx.ctx_functions /\
      fn_has_code sa sb func /\
      fn_has_code shadow_sa shadow_sb shadow_func /\
      fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
      (!H. dead_lo_ok H (DF H) lo cenv cx) /\
      (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
              not_fresh_at sa x) /\
      (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
              not_fresh_at sa x) /\
      gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es /\
      return_buf_frame d cenv sa s0 /\
      alloca_history func s0 /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
      (!fn inst s. frag_reachable ctx func s0 fn inst s ==>
                  dalloca_fmp_headroom inst s) /\
      (!H. valid_horizon cx st0 H es.storage_trace ==>
        stmt_state_rel H ctx func cenv cx es s0 /\
        storage_well_formed_on cx es (FST H) /\
        ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\ ~s0.vs_halted /\
      s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
      gas_outcome_full
        (DF, lo, gas_explicit_sites ctx shadow_ctx, ctx, func, PG)
        (cx_tops cx) cx st0 (bind (eval_expr cx e) (read_result cx))
        (es, s0, G0, tn0)
        (\H res ee G tn t. ?v. res = INL v /\
          expr_post H ctx func cenv cx e es sa sb s0 ee v op t /\
          expr_store_bound cx (post_value_type cenv e) v op t /\
          t.vs_current_bb = sb.cs_current_bb /\
          t.vs_inst_idx = LENGTH sb.cs_current_insts /\
          alloca_history func t /\
          (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
          s0.vs_alloca_next <= t.vs_alloca_next /\
          ghost_inv_at (DF H) lo d cenv cx ee G tn t /\
          ptr_val_ok cx (post_value_type cenv e) v op G tn t /\
          (~is_word_type (post_value_type cenv e) ==>
           ptr_buf_ok cenv e op G t) /\
          ghost_kept_at lo cenv es sa G0 tn0 s0 G tn)
        (\H res ee gt r.
          expr_exit res r /\ halt_exit H cx ee res r /\
          (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s))
End

Definition expr_vv_sim_full_def:
  expr_vv_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
    cenv cx ty e es <=>
    !st0 sa sb shadow_sa shadow_sb vv s0 G0 tn0.
      compile_expr cenv ty e sa = (vv, sb) /\
      compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr e) shadow_sa = (vv, shadow_sb) /\
      gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
      gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
      gas_shadow_function func shadow_func /\
      MEM func ctx.ctx_functions /\
      MEM shadow_func shadow_ctx.ctx_functions /\
      fn_has_code sa sb func /\
      fn_has_code shadow_sa shadow_sb shadow_func /\
      fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
      (!H. dead_lo_ok H (DF H) lo cenv cx) /\
      (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
              not_fresh_at sa x) /\
      (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
              not_fresh_at sa x) /\
      gas_admissible (eval_expr cx e) expr_vv_res_ok es /\
      return_buf_frame d cenv sa s0 /\
      alloca_history func s0 /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
      (!fn inst s. frag_reachable ctx func s0 fn inst s ==>
                  dalloca_fmp_headroom inst s) /\
      (!H. valid_horizon cx st0 H es.storage_trace ==>
        stmt_state_rel H ctx func cenv cx es s0 /\
        storage_well_formed_on cx es (FST H) /\
        ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\ ~s0.vs_halted /\
      s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
      gas_outcome_full
        (DF, lo, gas_explicit_sites ctx shadow_ctx, ctx, func, PG)
        (cx_tops cx) cx st0 (eval_expr cx e) (es, s0, G0, tn0)
        (\H res ee G tn t. ?tv. res = INL tv /\
          vv_post H ctx func cenv cx e es sa sb s0 ee tv vv t /\
          vv_store_bound cx (post_value_type cenv e) (lowered_value_type cenv e)
            ee tv vv t /\
          t.vs_current_bb = sb.cs_current_bb /\
          t.vs_inst_idx = LENGTH sb.cs_current_insts /\
          alloca_history func t /\
          (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
          s0.vs_alloca_next <= t.vs_alloca_next /\
          ghost_inv_at (DF H) lo d cenv cx ee G tn t /\
          ptr_vv_ok cx (post_value_type cenv e) tv vv ee G tn t /\
          (!v. tv = Value v /\ ~is_word_type (post_value_type cenv e) /\
               ~is_bytestring_type (post_value_type cenv e) ==>
               vv_own cenv cx (post_value_type cenv e) sa sb ee tv vv t /\
               (!t' p. vv = LocatedValue t' p ==>
                       p.ptr_location = LocMemory)) /\
          (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
           ?val. read_result cx tv ee = (INL val, ee) /\
                 !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) =
                          SOME rt /\
                        eval_operand (vv_operand vv) t = SOME w ==>
                        w2n w + type_memory_size rt <= lo /\
                        (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
                               val_in_memory rt val (w2n w) mem)) /\
          (!t' op. vv = StackValue t' op /\
                   ~is_word_type (post_value_type cenv e) ==>
                   ptr_buf_ok cenv e op G t) /\
          (!t' p. vv = LocatedValue t' p /\ p.ptr_location = LocMemory ==>
                  ptr_buf_ok cenv e p.ptr_operand G t) /\
          ghost_kept_at lo cenv es sa G0 tn0 s0 G tn)
        (\H res ee gt r.
          expr_exit res r /\ halt_exit H cx ee res r /\
          (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s))
End

(* The caller's return buffer is separate from callee allocations and
   live local regions, including borrowed parameters. *)
Definition return_buf_sep_def:
  (return_buf_sep NONE cenv es s <=> T) /\
  (return_buf_sep (SOME (bw : bytes32, capacity)) cenv es s <=>
    allocas_from (w2n bw + capacity) s /\
    !n b sz. local_region cenv es.scopes s n b sz ==>
             loweringStateRelDefs$regions_disjoint (w2n bw) capacity b sz)
End

(* Both compilations include local declarations: the original returns
   cenv', as stmt_env and stmts_env do, and the shadow returns
   gas_shadow_env T cenv'. *)
Definition stmt_frag_full_def:
  stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
    cx lctx RetQ cenv
    (m : compile_env compiler) (shadow_m : compile_env compiler)
    source es <=>
    !st0 sa sb shadow_sa shadow_sb s0 G0 tn0 cenv'.
      m sa = (cenv', sb) /\
      shadow_m shadow_sa = (gas_shadow_env T cenv', shadow_sb) /\
      gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
      gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
      gas_shadow_function func shadow_func /\
      MEM func ctx.ctx_functions /\
      MEM shadow_func shadow_ctx.ctx_functions /\
      fn_has_code sa sb func /\
      fn_has_code shadow_sa shadow_sb shadow_func /\
      (!H. dead_lo_ok H (DF H) lo cenv cx) /\
      fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
      ret_pc_ok cenv sa s0 /\
      (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
              not_fresh_at sa x) /\
      ~block_is_terminated sa /\
      gas_admissible source (stmt_res_ok lctx) es /\
      return_buf_frame d cenv sa s0 /\
      return_buf_sep d cenv es s0 /\
      alloca_history func s0 /\
      (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
      (!fn inst s. frag_reachable ctx func s0 fn inst s ==>
                  dalloca_fmp_headroom inst s) /\
      (!H. valid_horizon cx st0 H es.storage_trace ==>
        stmt_state_rel H ctx func cenv cx es s0 /\
        storage_well_formed_on cx es (FST H) /\
        ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\ ~s0.vs_halted /\
      s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
      gas_outcome_full
        (DF, lo, gas_explicit_sites ctx shadow_ctx, ctx, func, PG)
        (cx_tops cx) cx st0 source (es, s0, G0, tn0)
        (\H res ee G tn t. ?cenv''.
          stmt_lands lctx sb res t /\ ~t.vs_halted /\
          (res = INL () ==> ~block_is_terminated sb /\ cenv'' = cenv') /\
          cenv_top_ext cenv cenv'' ee.scopes /\
          stmt_state_rel H ctx func cenv'' cx ee t /\
          storage_well_formed_on cx ee (FST H) /\
          return_buf_frame d cenv'' sb t /\ alloca_history func t /\
          return_buf_sep d cenv'' ee t /\
          (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
          s0.vs_alloca_next <= t.vs_alloca_next /\
          ghost_inv_at (DF H) lo d cenv'' cx ee G tn t /\
          (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
                 lookup_var x t = SOME w) /\
          (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
                   FLOOKUP t.vs_allocas aid = SOME b) /\
          (!x. not_fresh_at sa x ==>
               FLOOKUP G x = FLOOKUP G0 x /\
               op_taint tn (Var x) = op_taint tn0 (Var x)) /\
          alloca_frame cenv es sa s0 cenv'' ee t /\
          (!aid off sz i.
             FLOOKUP s0.vs_allocas aid = SOME (off, sz) /\ aid < sa.cs_next_id /\
             (!n b sz'. local_region cenv es.scopes s0 n b sz' ==>
                        off + sz <= b \/ b + sz' <= off) /\
             off <= i /\ i < off + sz /\ i IN tn.t_mem ==>
             i IN tn0.t_mem))
        (\H res ee gt r.
          (!tail. stmt_exit_ptr (RetQ H) (ee with gas_obs := tail) res gt r) /\
          halt_exit H cx ee res r /\
          (ctx_has_dalloca ctx ==>
           !s. (r = Halt s \/ ?ir. r = IntRet ir s) ==> allocas_below_fmp s))
End

Theorem stmt_frag_full_source_cong:
  stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
    cx lctx RetQ cenv m shadow_m source es /\
  (!gs. source' (es with gas_obs := gs) = source (es with gas_obs := gs)) ==>
  stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
    cx lctx RetQ cenv m shadow_m source' es
Proof
  rewrite_tac[stmt_frag_full_def] >>
  strip_tac >> rpt gen_tac >> strip_tac >>
  irule gas_outcome_full_source_cong >> qexists_tac `source` >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qpat_x_assum `!st0 sa sb shadow_sa shadow_sb s0 G0 tn0 cenv'. _`
    (qspecl_then [`st0`,`sa`,`sb`,`shadow_sa`,`shadow_sb`,`s0`,`G0`,`tn0`,`cenv'`]
      match_mp_tac) >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  qpat_x_assum `gas_admissible source' (stmt_res_ok lctx) es` mp_tac >>
  simp[gasContextTheory.gas_admissible_def]
QED

(* The bytes of the older allocations clear of the live locals gain no
   taint across two fragments, the first keeping its allocations and the
   frame (alloca_frame) of those it started with. *)
Theorem alloca_taint_kept_trans:
  alloca_frame c0 e0 sa0 s0 c1 e1 s1 /\ sa0.cs_next_id <= sa1.cs_next_id /\
  (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
           FLOOKUP s1.vs_allocas aid = SOME b) /\
  (!aid off sz i.
     FLOOKUP s0.vs_allocas aid = SOME (off, sz) /\ aid < sa0.cs_next_id /\
     (!n b sz'. local_region c0 e0.scopes s0 n b sz' ==>
                off + sz <= b \/ b + sz' <= off) /\
     off <= i /\ i < off + sz /\ i IN tn1.t_mem ==>
     i IN tn0.t_mem) /\
  (!aid off sz i.
     FLOOKUP s1.vs_allocas aid = SOME (off, sz) /\ aid < sa1.cs_next_id /\
     (!n b sz'. local_region c1 e1.scopes s1 n b sz' ==>
                off + sz <= b \/ b + sz' <= off) /\
     off <= i /\ i < off + sz /\ i IN tn2.t_mem ==>
     i IN tn1.t_mem) ==>
  !aid off sz i.
    FLOOKUP s0.vs_allocas aid = SOME (off, sz) /\ aid < sa0.cs_next_id /\
    (!n b sz'. local_region c0 e0.scopes s0 n b sz' ==>
               off + sz <= b \/ b + sz' <= off) /\
    off <= i /\ i < off + sz /\ i IN tn2.t_mem ==>
    i IN tn0.t_mem
Proof
  rewrite_tac[alloca_frame_def] >> rpt strip_tac >>
  qpat_x_assum `!aid off sz. FLOOKUP s0.vs_allocas _ = _ /\ _ ==> _ /\ _`
    (qspecl_then [`aid`, `off`, `sz`] mp_tac) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  `FLOOKUP s1.vs_allocas aid = SOME (off, sz)` by res_tac >>
  `aid < sa1.cs_next_id` by decide_tac >>
  `i IN tn1.t_mem` by
    (qpat_x_assum `!aid off sz i. FLOOKUP s1.vs_allocas _ = _ /\ _ ==> _`
       (qspecl_then [`aid`, `off`, `sz`, `i`] mp_tac) >>
     impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> simp[]) >>
  qpat_x_assum `!aid off sz i. FLOOKUP s0.vs_allocas _ = _ /\ _ ==> _`
    (qspecl_then [`aid`, `off`, `sz`, `i`] mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >> simp[]
QED

Definition frame_ret_ok_full_def:
  frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
    cx RetQ cenv ret_ty <=>
    !cenv' env lctx eo es.
      same_frame cenv cenv' /\ expr_sim_inv cenv' cx env es /\
      stmt_exprs_ok cenv' (Return eo) /\
      IS_SOME (type_stmt env ret_ty (Return eo)) /\
      call_evaluation_safe cx (int_calls_stmt (Return eo)) /\
      (!e ty. eo = SOME e ==>
              expr_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
                cenv' cx ty e es /\
              expr_vv_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
                cenv' cx ty e es) ==>
      stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
        cx lctx RetQ cenv'
        (stmt_env cenv' lctx ret_ty (Return eo))
        (stmt_env (gas_shadow_env T cenv') lctx ret_ty
          (Return (OPTION_MAP gas_shadow_expr eo)))
        (eval_stmt cx (Return eo)) es
End
