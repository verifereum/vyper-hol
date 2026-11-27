(* Prefix certificates for the S1 simulations, with their own GAS marks. *)
Theory s1PrefixDefs
Ancestors
  bodySimFull gasOutcomeFull fragGasOriginPtr gasSummary gasExplicitSites
  e2eRequestCutDefs sourceUnitExecution compileUnit ptrSafeRun
  contextCodegenRel memSafeRun loweringStateRelDefs ptrDiscipline
  vyperStorageFootprint vyperInterpreter vyperState vyperAST
  venomExecSemantics venomInst venomState extCallOracle
  exprSimMapDefs bodyPtrDefs unitMemInv contextRawReachable exprSimMemDefs stmtSimDefs
  gasShadow gasShadowState gasShadowUnit exprLowering stmtLowering loweringPosts
  compileEnv allocaHistory venomWf finite_map list option
  gasOutcomeFullMods[qualified]


(* The raw state t a focus from s reaches, whose own (non-INVOKE) step
   issues request k, agreeing with the source's rq; the outcome is the
   oracle entry t is about to take. *)
Definition request_site_def:
  request_site (D, lo, explicit, ctx, func, PG) cx H (s, G, tn) k rq outcome <=>
    ?left leaf leaf_pg G' tn' t inst fuel t'.
      gas_origin_ptr_focus (D, lo, explicit, ctx, func, PG)
        (s, G, tn) left (leaf, leaf_pg, G', tn', t) /\
      active_inst leaf inst t /\ inst.inst_opcode <> INVOKE /\
      ptr_inst_ok D lo 0 ctx leaf G' tn' inst t /\
      stor_taint_ok_at D tn' t /\
      mem_safe_step fuel ctx inst t /\
      step_inst fuel ctx inst t = OK t' /\
      LENGTH t.vs_requests = k /\ k < LENGTH t'.vs_requests /\
      request_agree H cx.txn.target rq (EL k t'.vs_requests) /\
      outcome = (if t.vs_outcomes = [] then failed_outcome rq
                 else HD t.vs_outcomes)
End

(* Companion prefix judgment of one source fragment against the Venom run
   from s.  Its own marks, focus-backed as gas_outcome_full's bad arm is
   (horizon valid on the input trace whenever it has one).  Every outcome
   the fragment takes, under that marks and ANY tail, whose preceding trace
   is a valid horizon and whose request is not a computed precompile, has
   its request site.  No posts: Q/R stay in gas_outcome_full. *)
Definition gas_prefix_full_def:
  gas_prefix_full (DF, lo, explicit, ctx, func, PG) cx st0 source (es, s, G, tn) <=>
    ?marks.
      (?H leaf leaf_pg leaf_g leaf_tn finish.
         (storage_trace_domain cx st0 es.storage_trace ==>
          valid_horizon cx st0 H es.storage_trace) /\
         gas_origin_ptr_focus (DF H, lo, explicit, ctx, func, PG)
           (s, G, tn) marks (leaf, leaf_pg, leaf_g, leaf_tn, finish)) /\
      !tail res ee obs_pre rq outcome sfx H.
        LENGTH es.requests = recorded_outcomes_count es.storage_trace /\
        source (es with gas_obs :=
                  gas_explicit marks s.vs_gas_readings ++ tail) = (res, ee) /\
        ee.storage_trace = obs_pre ++ StorageOutcome rq outcome :: sfx /\
        LENGTH es.storage_trace <= LENGTH obs_pre /\
        valid_horizon cx st0 H obs_pre /\
        ~computed_precompile rq ==>
        request_site (DF H, lo, explicit, ctx, func, PG) cx H (s, G, tn)
          (recorded_outcomes_count obs_pre) rq outcome
End

Definition expr_map_sim_full_pre_def:
  expr_map_sim_full_pre (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
    cenv cx ty e es
    (st0, sa, sb, shadow_sa, shadow_sb, vv, s0, G0, tn0) <=>
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
      (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_fmp_headroom inst s) /\
      (!H. valid_horizon cx st0 H es.storage_trace ==>
        stmt_state_rel H ctx func cenv cx es s0 /\
        storage_well_formed_on cx es (FST H) /\
        ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\ ~s0.vs_halted /\
      s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts
End

Definition expr_map_sim_prefix_def:
  expr_map_sim_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
    cenv cx ty e es <=>
    !st0 sa sb shadow_sa shadow_sb vv s0 G0 tn0.
      expr_map_sim_full_pre (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
        cenv cx ty e es
        (st0, sa, sb, shadow_sa, shadow_sb, vv, s0, G0, tn0) ==>
      gas_prefix_full (DF, lo, gas_explicit_sites ctx shadow_ctx, ctx, func, PG)
        cx st0 (eval_expr cx e) (es, s0, G0, tn0)
End

Definition expr_sim_full_pre_def:
  expr_sim_full_pre (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
    cenv cx ty e es
    (st0, sa, sb, shadow_sa, shadow_sb, op, s0, G0, tn0) <=>
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
      (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_fmp_headroom inst s) /\
      (!H. valid_horizon cx st0 H es.storage_trace ==>
        stmt_state_rel H ctx func cenv cx es s0 /\
        storage_well_formed_on cx es (FST H) /\
        ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\ ~s0.vs_halted /\
      s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts
End

Definition expr_sim_prefix_def:
  expr_sim_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
    cenv cx ty e es <=>
    !st0 sa sb shadow_sa shadow_sb op s0 G0 tn0.
      expr_sim_full_pre (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
        cenv cx ty e es
        (st0, sa, sb, shadow_sa, shadow_sb, op, s0, G0, tn0) ==>
      gas_prefix_full (DF, lo, gas_explicit_sites ctx shadow_ctx, ctx, func, PG)
        cx st0 (bind (eval_expr cx e) (read_result cx)) (es, s0, G0, tn0)
End

Definition expr_vv_sim_full_pre_def:
  expr_vv_sim_full_pre (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
    cenv cx ty e es
    (st0, sa, sb, shadow_sa, shadow_sb, vv, s0, G0, tn0) <=>
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
      (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_fmp_headroom inst s) /\
      (!H. valid_horizon cx st0 H es.storage_trace ==>
        stmt_state_rel H ctx func cenv cx es s0 /\
        storage_well_formed_on cx es (FST H) /\
        ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\ ~s0.vs_halted /\
      s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts
End

Definition expr_vv_sim_prefix_def:
  expr_vv_sim_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
    cenv cx ty e es <=>
    !st0 sa sb shadow_sa shadow_sb vv s0 G0 tn0.
      expr_vv_sim_full_pre (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
        cenv cx ty e es
        (st0, sa, sb, shadow_sa, shadow_sb, vv, s0, G0, tn0) ==>
      gas_prefix_full (DF, lo, gas_explicit_sites ctx shadow_ctx, ctx, func, PG)
        cx st0 (eval_expr cx e) (es, s0, G0, tn0)
End

Definition stmt_frag_full_pre_def:
  stmt_frag_full_pre (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
    cx lctx RetQ cenv
    (m : compile_env compiler) (shadow_m : compile_env compiler)
    source es
    (st0, sa, sb, shadow_sa, shadow_sb, s0, G0, tn0, cenv') <=>
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
      (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_fmp_headroom inst s) /\
      (!H. valid_horizon cx st0 H es.storage_trace ==>
        stmt_state_rel H ctx func cenv cx es s0 /\
        storage_well_formed_on cx es (FST H) /\
        ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\ ~s0.vs_halted /\
      s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts
End

Definition stmt_frag_prefix_def:
  stmt_frag_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
    cx lctx RetQ cenv
    m shadow_m
    source es <=>
    !st0 sa sb shadow_sa shadow_sb s0 G0 tn0 cenv'.
      stmt_frag_full_pre (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
        cx lctx RetQ cenv
        m shadow_m
        source es
        (st0, sa, sb, shadow_sa, shadow_sb, s0, G0, tn0, cenv') ==>
      gas_prefix_full (DF, lo, gas_explicit_sites ctx shadow_ctx, ctx, func, PG)
        cx st0 source (es, s0, G0, tn0)
End

Definition frame_ret_ok_full_pre_def:
  frame_ret_ok_full_pre (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
    cx RetQ cenv ret_ty
    (cenv', env, lctx, eo, es) <=>
      same_frame cenv cenv' /\ expr_sim_inv cenv' cx env es /\
      stmt_exprs_ok cenv' (Return eo) /\
      IS_SOME (type_stmt env ret_ty (Return eo)) /\
      call_evaluation_safe cx (int_calls_stmt (Return eo)) /\
      (!e ty. eo = SOME e ==>
              expr_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
                cenv' cx ty e es /\
              expr_vv_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
                cenv' cx ty e es)
End

Definition frame_ret_ok_prefix_def:
  frame_ret_ok_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
    cx RetQ cenv ret_ty <=>
    !cenv' env lctx eo es.
      frame_ret_ok_full_pre (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
        cx RetQ cenv ret_ty
        (cenv', env, lctx, eo, es) ==>
      stmt_frag_prefix (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
        cx lctx RetQ cenv'
        (stmt_env cenv' lctx ret_ty (Return eo))
        (stmt_env (gas_shadow_env T cenv') lctx ret_ty
          (Return (OPTION_MAP gas_shadow_expr eo)))
        (eval_stmt cx (Return eo)) es
End

Definition unit_prefix_cert_def:
  unit_prefix_cert shadow_ctx tops am tx unit vs <=>
    ?func marks.
      unit.cu_context.ctx_entry = SOME "__entry" /\
      lookup_function "__entry" unit.cu_context.ctx_functions = SOME func /\
      (?(H : (bool # bytes32 # type_value) list # num list)
         leaf leaf_pg leaf_g leaf_tn finish.
         gas_origin_ptr_focus
           (cx_dead H (initial_evaluation_context am.sources am.layouts tx NONE),
            0, gas_explicit_sites unit.cu_context shadow_ctx, unit.cu_context, func, [])
           (vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry";
                       vs_inst_idx := 0 |>, FEMPTY, entry_taint)
           marks (leaf, leaf_pg, leaf_g, leaf_tn, finish)) /\
      !tail res am' rqs obs obs_pre rq outcome sfx H.
        call_external_trace (SOME vs.vs_outcomes)
          (gas_explicit marks vs.vs_gas_readings ++ tail) am tx = (res,am',rqs,obs) /\
        obs = obs_pre ++ StorageOutcome rq outcome :: sfx /\
        valid_horizon (initial_evaluation_context am.sources am.layouts tx NONE)
          (initial_state am []) H obs_pre /\
        ~computed_precompile rq ==>
        request_site
          (cx_dead H (initial_evaluation_context am.sources am.layouts tx NONE),
           0, gas_explicit_sites unit.cu_context shadow_ctx, unit.cu_context, func, [])
          (initial_evaluation_context am.sources am.layouts tx NONE) H
          (vs with <| vs_prev_bb := NONE; vs_current_bb := "__entry";
                      vs_inst_idx := 0 |>, FEMPTY, entry_taint)
          (recorded_outcomes_count obs_pre) rq outcome
End

Theorem expr_map_sim_full_eq:
  expr_map_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
    cenv cx ty e es <=>
    !st0 sa sb shadow_sa shadow_sb vv s0 G0 tn0.
      expr_map_sim_full_pre (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
        cenv cx ty e es
        (st0, sa, sb, shadow_sa, shadow_sb, vv, s0, G0, tn0) ==>
      gas_outcome_full_mods
        (DF, lo, gas_explicit_sites ctx shadow_ctx, ctx, func, PG)
        cenv.ce_modules cx st0 (eval_expr cx e) (es, s0, G0, tn0)
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
Proof
  simp[expr_map_sim_full_def, expr_map_sim_full_pre_def]
QED

Theorem expr_sim_full_eq:
  expr_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
    cenv cx ty e es <=>
    !st0 sa sb shadow_sa shadow_sb op s0 G0 tn0.
      expr_sim_full_pre (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
        cenv cx ty e es
        (st0, sa, sb, shadow_sa, shadow_sb, op, s0, G0, tn0) ==>
      gas_outcome_full_mods
        (DF, lo, gas_explicit_sites ctx shadow_ctx, ctx, func, PG)
        cenv.ce_modules cx st0 (bind (eval_expr cx e) (read_result cx))
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
Proof
  simp[expr_sim_full_def, expr_sim_full_pre_def]
QED

Theorem expr_vv_sim_full_eq:
  expr_vv_sim_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
    cenv cx ty e es <=>
    !st0 sa sb shadow_sa shadow_sb vv s0 G0 tn0.
      expr_vv_sim_full_pre (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
        cenv cx ty e es
        (st0, sa, sb, shadow_sa, shadow_sb, vv, s0, G0, tn0) ==>
      gas_outcome_full_mods
        (DF, lo, gas_explicit_sites ctx shadow_ctx, ctx, func, PG)
        cenv.ce_modules cx st0 (eval_expr cx e) (es, s0, G0, tn0)
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
Proof
  simp[expr_vv_sim_full_def, expr_vv_sim_full_pre_def]
QED

Theorem stmt_frag_full_eq:
  stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
    cx lctx RetQ cenv
    m shadow_m
    source es <=>
    !st0 sa sb shadow_sa shadow_sb s0 G0 tn0 cenv'.
      stmt_frag_full_pre (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
        cx lctx RetQ cenv
        m shadow_m
        source es
        (st0, sa, sb, shadow_sa, shadow_sb, s0, G0, tn0, cenv') ==>
      gas_outcome_full_mods
        (DF, lo, gas_explicit_sites ctx shadow_ctx, ctx, func, PG)
        cenv.ce_modules cx st0 source (es, s0, G0, tn0)
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
Proof
  simp[stmt_frag_full_def, stmt_frag_full_pre_def]
QED

Theorem frame_ret_ok_full_eq:
  frame_ret_ok_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
    cx RetQ cenv ret_ty <=>
    !cenv' env lctx eo es.
      frame_ret_ok_full_pre (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
        cx RetQ cenv ret_ty
        (cenv', env, lctx, eo, es) ==>
      stmt_frag_full (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
        cx lctx RetQ cenv'
        (stmt_env cenv' lctx ret_ty (Return eo))
        (stmt_env (gas_shadow_env T cenv') lctx ret_ty
          (Return (OPTION_MAP gas_shadow_expr eo)))
        (eval_stmt cx (Return eo)) es
Proof
  simp[frame_ret_ok_full_def, frame_ret_ok_full_pre_def]
QED
