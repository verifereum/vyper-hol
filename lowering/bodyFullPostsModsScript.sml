(* Value posts and simulations for the linked unit's immutable section. *)
Theory bodyFullPostsMods
Ancestors
  bodySimFull bodySimEntry loweringPosts loweringStateRelDefs bodyPtrDefs bodySim
  exprLowering exprLoweringProps compileEnv bodyInvSplit bodyFullShadowBodyInv
  exprSimDefs exprSimMapDefs exprSimHypsDefs stmtSimDefs stmtLowering
  gasOutcomeFull gasOutcomeFullMods gasShadow gasShadowState gasShadowUnit
  gasExplicitSites gasContext allocaHistory contextRawReachable unitMemInv
  vyperInterpreter vyperState vyperAST vyperContext vyperTypeSystem
  vyperTypeCallGraph vyperTypeInvariants vyperStoragePlaceProvenance vyperStorageFootprint
  venomState venomWf alist finite_map list pair option

(* Only the immutable lookup changes module. The expression's frame
   and its local variables still belong to the active compile env. *)
Definition immutable_holds_mods_def[nocompute]:
  immutable_holds_mods cenv cx t tv w es s <=>
    ?src tops. ALOOKUP cenv.ce_modules src = SOME tops /\
               immutable_holds (cenv with ce_module := src) cx t tv w es s
End

Definition vv_place_ptr_mods_def[nocompute]:
  vv_place_ptr_mods cenv cx es s tv vv <=>
    case (tv,vv) of
      (PlaceR (ImmutablePlace src id path), LocatedValue ty p) =>
        IS_SOME (ALOOKUP cenv.ce_modules src) /\
        vv_place_ptr (cenv with ce_module := src) cx es s tv vv
    | _ => vv_place_ptr cenv cx es s tv vv
End

Definition vv_holds_mods_def[nocompute]:
  vv_holds_mods cenv cx t tv vv es s <=>
    case vv of
      LocatedValue t' p =>
        if p.ptr_location = LocCode then
          t' = t /\
          ?w. eval_operand p.ptr_operand s = SOME w /\
              immutable_holds_mods cenv cx t tv w es s
        else vv_holds cenv cx t tv vv es s
    | StackValue t' op => vv_holds cenv cx t tv vv es s
End

(* The state relation of the active frame is accompanied by the
   immutable bytes and allocation separation for every linked module. *)
Definition immutable_frame_mods_def[nocompute]:
  immutable_frame_mods func cenv cx es s <=>
    immutables_rel_mods cenv cx.txn.target cenv.ce_is_ctor es s /\
    immutable_alloca_sep_mods func cenv cx es s
End

Definition expr_post_mods_def[nocompute]:
  expr_post_mods H ctx func cenv cx e es sa sb s0 es' v op s <=>
    expr_post H ctx func cenv cx e es sa sb s0 es' v op s /\
    immutable_frame_mods func cenv cx es' s
End

Definition vv_post_mods_def[nocompute]:
  vv_post_mods H ctx func cenv cx e es sa sb s0 es' tv vv s <=>
    stmt_state_rel H ctx func cenv cx es' s ∧
    immutable_frame_mods func cenv cx es' s /\
    storage_well_formed_on cx es' (FST H) ∧
    vv_holds_mods cenv cx (post_value_type cenv e) tv vv es' s /\
    vv_at cenv cx (post_value_type cenv e) sa sb es' tv vv s /\
    vv_place_ptr_mods cenv cx es' s tv vv /\
    (post_value_type cenv e <> expr_type e ==>
     vv_own cenv cx (post_value_type cenv e) sa sb es' tv vv s) /\
    (~expr_has_effect e ==> vv_storage_live H cx vv es' s) /\
    (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
           lookup_var x s = SOME w) /\
    (!aid b. FLOOKUP s0.vs_allocas aid = SOME b ==>
             FLOOKUP s.vs_allocas aid = SOME b) /\
    (!aid off sz.
       FLOOKUP s0.vs_allocas aid = SOME (off, sz) /\ aid < sa.cs_next_id /\
       (!n b sz'. local_region cenv es.scopes s0 n b sz' ==>
                  off + sz <= b \/ b + sz' <= off) ==>
       mem_bytes_at off sz s.vs_memory = mem_bytes_at off sz s0.vs_memory) /\
    locals_kept cenv es es' s0 s /\
    (~expr_has_effect e ==> pure_frame cenv func es sa s0 s)
End

Definition expr_sim_full_mods_def[nocompute]:
  expr_sim_full_mods (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
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
      (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
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
        immutable_frame_mods func cenv cx es s0 /\
        storage_well_formed_on cx es (FST H) /\
        ghost_inv_at_mods (DF H) lo d cenv cx es G0 tn0 s0) /\ ~s0.vs_halted /\
      s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
      gas_outcome_full_mods
        (DF, lo, gas_explicit_sites ctx shadow_ctx, ctx, func, PG)
        cenv.ce_modules cx st0 (bind (eval_expr cx e) (read_result cx))
        (es, s0, G0, tn0)
        (\H res ee G tn t. ?v. res = INL v /\
          expr_post_mods H ctx func cenv cx e es sa sb s0 ee v op t /\
          expr_store_bound cx (post_value_type cenv e) v op t /\
          t.vs_current_bb = sb.cs_current_bb /\
          t.vs_inst_idx = LENGTH sb.cs_current_insts /\
          alloca_history func t /\
          (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
          s0.vs_alloca_next <= t.vs_alloca_next /\
          ghost_inv_at_mods (DF H) lo d cenv cx ee G tn t /\
          ptr_val_ok cx (post_value_type cenv e) v op G tn t /\
          (~is_word_type (post_value_type cenv e) ==>
           ptr_buf_ok cenv e op G t) /\
          ghost_kept_at lo cenv es sa G0 tn0 s0 G tn)
        (\H res ee gt r.
          expr_exit res r /\ halt_exit H cx ee res r /\
          (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s))
End

Definition expr_vv_sim_full_mods_def[nocompute]:
  expr_vv_sim_full_mods (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
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
      (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
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
        immutable_frame_mods func cenv cx es s0 /\
        storage_well_formed_on cx es (FST H) /\
        ghost_inv_at_mods (DF H) lo d cenv cx es G0 tn0 s0) /\ ~s0.vs_halted /\
      s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
      gas_outcome_full_mods
        (DF, lo, gas_explicit_sites ctx shadow_ctx, ctx, func, PG)
        cenv.ce_modules cx st0 (eval_expr cx e) (es, s0, G0, tn0)
        (\H res ee G tn t. ?tv. res = INL tv /\
          vv_post_mods H ctx func cenv cx e es sa sb s0 ee tv vv t /\
          vv_store_bound cx (post_value_type cenv e) (lowered_value_type cenv e)
            ee tv vv t /\
          t.vs_current_bb = sb.cs_current_bb /\
          t.vs_inst_idx = LENGTH sb.cs_current_insts /\
          alloca_history func t /\
          (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
          s0.vs_alloca_next <= t.vs_alloca_next /\
          ghost_inv_at_mods (DF H) lo d cenv cx ee G tn t /\
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

Definition expr_map_sim_full_mods_def[nocompute]:
  expr_map_sim_full_mods (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
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
      (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
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
        immutable_frame_mods func cenv cx es s0 /\
        storage_well_formed_on cx es (FST H) /\
        ghost_inv_at_mods (DF H) lo d cenv cx es G0 tn0 s0) /\ ~s0.vs_halted /\
      s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
      gas_outcome_full_mods
        (DF, lo, gas_explicit_sites ctx shadow_ctx, ctx, func, PG)
        cenv.ce_modules cx st0 (eval_expr cx e) (es, s0, G0, tn0)
        (\H res ee G tn t. ?tr slot kt vt tp p.
          res = INL (HashMapRef tr slot kt vt) /\
          storage_mapping_region cx tr slot (HashMapT kt vt) /\
          vv = LocatedValue tp p /\ p.ptr_location = slot_loc tr /\
          eval_operand p.ptr_operand t = SOME slot /\
          stmt_state_rel H ctx func cenv cx ee t /\
          immutable_frame_mods func cenv cx ee t /\
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
          ghost_inv_at_mods (DF H) lo d cenv cx ee G tn t /\
          op_taint tn p.ptr_operand = {} /\
          op_prov G p.ptr_operand = NONE /\
          ghost_kept_at lo cenv es sa G0 tn0 s0 G tn)
        (\H res ee gt r.
          expr_exit res r /\ halt_exit H cx ee res r /\
          (ctx_has_dalloca ctx ==> !s. r = Halt s ==> allocas_below_fmp s))
End

Definition stmt_frag_full_mods_def[nocompute]:
  stmt_frag_full_mods (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
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
      (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
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
        immutable_frame_mods func cenv cx es s0 /\
        storage_well_formed_on cx es (FST H) /\
        ghost_inv_at_mods (DF H) lo d cenv cx es G0 tn0 s0) /\ ~s0.vs_halted /\
      s0.vs_current_bb = sa.cs_current_bb /\
      s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
      gas_outcome_full_mods
        (DF, lo, gas_explicit_sites ctx shadow_ctx, ctx, func, PG)
        cenv.ce_modules cx st0 source (es, s0, G0, tn0)
        (\H res ee G tn t. ?cenv''.
          stmt_lands lctx sb res t /\ ~t.vs_halted /\
          (res = INL () ==> ~block_is_terminated sb /\ cenv'' = cenv') /\
          cenv_top_ext cenv cenv'' ee.scopes /\
          stmt_state_rel H ctx func cenv'' cx ee t /\
          immutable_frame_mods func cenv'' cx ee t /\
          storage_well_formed_on cx ee (FST H) /\
          return_buf_frame d cenv'' sb t /\ alloca_history func t /\
          return_buf_sep d cenv'' ee t /\
          (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
          s0.vs_alloca_next <= t.vs_alloca_next /\
          ghost_inv_at_mods (DF H) lo d cenv'' cx ee G tn t /\
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

Definition frame_ret_ok_full_mods_def[nocompute]:
  frame_ret_ok_full_mods mods (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
    cx RetQ cenv ret_ty <=>
    !cenv' env lctx eo es.
      same_frame cenv cenv' /\ expr_sim_inv_mods mods cenv' cx env es /\
      stmt_exprs_ok cenv' (Return eo) /\
      IS_SOME (type_stmt env ret_ty (Return eo)) /\
      call_evaluation_safe cx (int_calls_stmt (Return eo)) /\
      (!e ty. eo = SOME e ==>
              expr_sim_full_mods (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
                cenv' cx ty e es /\
              expr_vv_sim_full_mods (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
                cenv' cx ty e es) ==>
      stmt_frag_full_mods (DF, lo, d, ctx, shadow_ctx, PG, func, shadow_func)
        cx lctx RetQ cenv'
        (stmt_env cenv' lctx ret_ty (Return eo))
        (stmt_env (gas_shadow_env T cenv') lctx ret_ty
          (Return (OPTION_MAP gas_shadow_expr eo)))
        (eval_stmt cx (Return eo)) es
End

Theorem ce_module_update_same[local]:
  cenv with ce_module := cenv.ce_module = cenv
Proof
  simp[compile_env_component_equality]
QED

Theorem immutable_holds_mods_singleton:
  cenv.ce_modules = [(NONE,tops)] /\ cenv.ce_module = NONE ==>
  (immutable_holds_mods cenv cx t tv w es s <=>
   immutable_holds cenv cx t tv w es s)
Proof
  strip_tac >>
  `cenv with ce_module := NONE = cenv` by metis_tac[ce_module_update_same] >>
  simp[immutable_holds_mods_def, ALOOKUP_def] >>
  metis_tac[]
QED

Theorem vv_place_ptr_mods_singleton:
  cenv.ce_modules = [(NONE,tops)] /\ cenv.ce_module = NONE ==>
  (vv_place_ptr_mods cenv cx es s tv vv <=>
   vv_place_ptr cenv cx es s tv vv)
Proof
  strip_tac >>
  `cenv with ce_module := NONE = cenv` by metis_tac[ce_module_update_same] >>
  Cases_on `vv` >> Cases_on `tv` >>
  TRY (rename1 `PlaceR place` >> Cases_on `place`) >>
  simp[vv_place_ptr_mods_def, ALOOKUP_def] >>
  rename1 `vv_place_ptr _ _ _ _ (PlaceR (ImmutablePlace src id path)) _` >>
  Cases_on `src` >> simp[vv_place_ptr_def]
QED

Theorem vv_holds_mods_singleton:
  cenv.ce_modules = [(NONE,tops)] /\ cenv.ce_module = NONE ==>
  (vv_holds_mods cenv cx t tv vv es s <=>
   vv_holds cenv cx t tv vv es s)
Proof
  strip_tac >>
  Cases_on `vv` >> simp[vv_holds_mods_def] >>
  rename1 `p.ptr_location = LocCode` >>
  Cases_on `p.ptr_location = LocCode` >>
  simp[vv_holds_def, vv_holds_mods_def, immutable_holds_mods_singleton]
QED

Theorem stmt_state_rel_immutable_frame[local]:
  cenv.ce_modules = [(NONE,tops)] /\ cenv.ce_module = NONE /\
  stmt_state_rel H ctx func cenv cx es s ==>
  immutable_frame_mods func cenv cx es s
Proof
  strip_tac >>
  `cenv with ce_module := NONE = cenv` by metis_tac[ce_module_update_same] >>
  qpat_x_assum `stmt_state_rel _ _ _ _ _ _ _` mp_tac >>
  simp[stmt_state_rel_def, loweringStateRelDefsTheory.state_rel_def,
       immutable_frame_mods_def, immutable_alloca_sep_mods_def,
       immutables_rel_mods_def, ALOOKUP_def, FORALL_OPTION]
QED

Theorem immutable_frame_conj_singleton[local]:
  cenv.ce_modules = [(NONE,tops)] /\ cenv.ce_module = NONE ==>
  (stmt_state_rel H ctx func cenv cx es s /\
   immutable_frame_mods func cenv cx es s /\ P <=>
   stmt_state_rel H ctx func cenv cx es s /\ P)
Proof
  strip_tac >>
  Cases_on `stmt_state_rel H ctx func cenv cx es s` >> simp[] >>
  drule_all stmt_state_rel_immutable_frame >> simp[]
QED

Theorem expr_post_mods_singleton:
  cenv.ce_modules = [(NONE,tops)] /\ cenv.ce_module = NONE ==>
  (expr_post_mods H ctx func cenv cx e es sa sb s0 es' v op s <=>
   expr_post H ctx func cenv cx e es sa sb s0 es' v op s)
Proof
  strip_tac >>
  simp[expr_post_mods_def, expr_post_def] >>
  metis_tac[stmt_state_rel_immutable_frame]
QED

Theorem vv_post_mods_singleton:
  cenv.ce_modules = [(NONE,tops)] /\ cenv.ce_module = NONE ==>
  (vv_post_mods H ctx func cenv cx e es sa sb s0 es' tv vv s <=>
   vv_post H ctx func cenv cx e es sa sb s0 es' tv vv s)
Proof
  strip_tac >>
  simp[vv_post_mods_def, vv_post_def,
       immutable_frame_conj_singleton, vv_holds_mods_singleton,
       vv_place_ptr_mods_singleton]
QED

Theorem expr_sim_full_mods_singleton:
  cenv.ce_modules = [(NONE,cx_tops cx)] /\ cenv.ce_module = NONE ==>
  (expr_sim_full_mods cfg cenv cx ty e es <=>
   expr_sim_full cfg cenv cx ty e es)
Proof
  strip_tac >> PairCases_on `cfg` >>
  simp[expr_sim_full_mods_def, expr_sim_full_def,
       GSYM gas_outcome_full_singleton_def,
       dead_lo_ok_mods_singleton, ghost_inv_at_mods_singleton,
       immutable_frame_conj_singleton, SF CONJ_ss, expr_post_mods_singleton]
QED

Theorem expr_vv_sim_full_mods_singleton:
  cenv.ce_modules = [(NONE,cx_tops cx)] /\ cenv.ce_module = NONE ==>
  (expr_vv_sim_full_mods cfg cenv cx ty e es <=>
   expr_vv_sim_full cfg cenv cx ty e es)
Proof
  strip_tac >> PairCases_on `cfg` >>
  simp[expr_vv_sim_full_mods_def, expr_vv_sim_full_def,
       GSYM gas_outcome_full_singleton_def,
       dead_lo_ok_mods_singleton, ghost_inv_at_mods_singleton,
       immutable_frame_conj_singleton, SF CONJ_ss, vv_post_mods_singleton]
QED

Theorem expr_map_sim_full_mods_singleton:
  cenv.ce_modules = [(NONE,cx_tops cx)] /\ cenv.ce_module = NONE ==>
  (expr_map_sim_full_mods cfg cenv cx ty e es <=>
   expr_map_sim_full cfg cenv cx ty e es)
Proof
  strip_tac >> PairCases_on `cfg` >>
  simp[expr_map_sim_full_mods_def, expr_map_sim_full_def,
       GSYM gas_outcome_full_singleton_def,
       dead_lo_ok_mods_singleton, ghost_inv_at_mods_singleton,
       immutable_frame_conj_singleton, SF CONJ_ss]
QED

Theorem same_frame_module_fields[local]:
  same_frame cenv cenv' ==>
  cenv'.ce_modules = cenv.ce_modules /\
  cenv'.ce_module = cenv.ce_module /\
  cenv'.ce_module_vars = cenv.ce_module_vars
Proof
  simp[same_frame_def, compile_env_component_equality]
QED

Theorem stmt_frag_full_mods_singleton:
  cenv.ce_modules = [(NONE,cx_tops cx)] /\ cenv.ce_module = NONE ==>
  (stmt_frag_full_mods cfg cx lctx RetQ cenv m shadow_m source es <=>
   stmt_frag_full cfg cx lctx RetQ cenv m shadow_m source es)
Proof
  strip_tac >>
  PairCases_on `cfg` >>
  ASM_SIMP_TAC bool_ss [stmt_frag_full_mods_def, stmt_frag_full_def,
                       GSYM gas_outcome_full_singleton_def] >>
  simp[cenv_top_ext_def,
       compile_env_component_equality,
       dead_lo_ok_mods_singleton, ghost_inv_at_mods_singleton,
       immutable_frame_conj_singleton, SF CONJ_ss]
QED

Theorem expr_sim_inv_mods_singleton:
  ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] /\
  cenv.ce_module = NONE /\ immutable_section_layout_mods [(NONE,tops)] cenv ==>
  (expr_sim_inv_mods [(NONE,tops)] cenv cx env es <=>
   expr_sim_inv cenv cx env es)
Proof
  strip_tac >>
  `cx_tops cx = tops` by simp[cx_tops_def, get_module_code_def, ALOOKUP_def] >>
  simp[expr_sim_inv_split_def] >>
  eq_tac >> simp[] >> strip_tac >>
  `env_consistent env cx es` by fs[expr_sim_inv_mods_def] >>
  `env_context_consistent env cx` by fs[env_consistent_def] >>
  rpt gen_tac >> disch_then (CONJUNCTS_THEN2 ASSUME_TAC ASSUME_TAC) >>
  `?ts. get_module_code cx src = SOME ts /\ is_bare_global_decl id ts` by
    metis_tac[env_context_consistent_bare_global_find_NONE] >>
  `src = NONE /\ ts = tops` by
    (qpat_x_assum `get_module_code cx src = SOME ts` mp_tac >>
     Cases_on `src` >> simp[get_module_code_def, ALOOKUP_def] >> metis_tac[]) >>
  qpat_x_assum `src = NONE` SUBST_ALL_TAC >>
  qpat_x_assum `ts = tops` SUBST_ALL_TAC >>
  simp[] >>
  `?vis ty' slot. MEM (VariableDecl vis Immutable id ty' slot) tops` by
    (mp_tac (Q.SPECL [`env`, `cx`, `es`, `tops`, `id`]
                     bare_global_clause_immutable) >>
     simp[get_module_code_def, ALOOKUP_def]) >>
  qpat_x_assum `MEM (VariableDecl _ Immutable _ _ _) tops`
    (strip_assume_tac o REWRITE_RULE [MEM_SPLIT]) >>
  `?off size. immutable_region_mods [(NONE,tops)] NONE id off size` by
    (simp[immutable_region_mods_def, ALOOKUP_def] >>
     qexists_tac `compute_immutables_len
       (get_struct_fields (make_struct_fields_map_mods [(NONE,tops)])) l1` >>
     qexistsl_tac [`l1`, `l2`, `vis`, `ty'`, `slot`] >> simp[]) >>
  qpat_x_assum `immutable_section_layout_mods _ _`
    (mp_tac o Q.SPECL [`NONE`, `id`, `off`] o CONJUNCT1 o
     REWRITE_RULE [immutable_section_layout_mods_def]) >>
  metis_tac[IS_SOME_EXISTS]
QED

Theorem frame_ret_ok_full_mods_singleton:
  ALOOKUP cx.sources cx.txn.target = SOME [(NONE,tops)] /\
  cenv.ce_modules = [(NONE,tops)] /\ cenv.ce_module = NONE /\
  immutable_section_layout_mods [(NONE,tops)] cenv ==>
  (frame_ret_ok_full_mods [(NONE,tops)] cfg cx RetQ cenv ret_ty <=>
   frame_ret_ok_full cfg cx RetQ cenv ret_ty)
Proof
  strip_tac >>
  `cx_tops cx = tops` by simp[cx_tops_def, get_module_code_def, ALOOKUP_def] >>
  `!cenv'. same_frame cenv cenv' ==>
      cenv'.ce_modules = [(NONE,tops)] /\ cenv'.ce_module = NONE /\
      immutable_section_layout_mods [(NONE,tops)] cenv'` by
    (gen_tac >> disch_then (mp_tac o MATCH_MP same_frame_module_fields) >>
     simp[] >> strip_tac >>
     qpat_x_assum `immutable_section_layout_mods [(NONE,tops)] cenv` mp_tac >>
     simp[immutable_section_layout_mods_def] >> metis_tac[]) >>
  PairCases_on `cfg` >>
  simp[frame_ret_ok_full_mods_def, frame_ret_ok_full_def, GSYM AND_IMP_INTRO, SF CONJ_ss,
       expr_sim_inv_mods_singleton, expr_sim_full_mods_singleton,
       expr_vv_sim_full_mods_singleton, stmt_frag_full_mods_singleton]
QED
