Theory bodyFullBuiltinECArithStaging
Ancestors
  bodyFullBuiltinECArithOperands bodyFullBuiltinECArithTransfers
  bodyFullBuiltinECArithPayloadShape bodyFullBuiltinECArithPointCopy
  bodyFullAllocaFresh bodyFullAllocGeneric bodyFullUnwrapRun bodyFullGhostFrame
  bodyMemEcArithCode bodyMemEcArithSafe
  bodySimFull bodyFullPreds exprSimECArith
  gasShadowCompile exprSimHypsDefs exprLowering loweringPosts vyperAST list
  vyperStorageTrace vyperStorageFootprint exprSimHyps exprSimOperands exprSimSource

Theorem ec_arith_staging_full_conditional:
  (bt = ECAdd \/ bt = ECMul) /\
  a = ArrayT (BaseT (UintT 256)) (Fixed 2) /\
  expr_type e1 = ArrayT (BaseT (UintT 256)) (Fixed 2) /\
  expr_type e2 = (if bt = ECAdd then a else BaseT (UintT 256)) /\
  body_exprs_full_ok cx [e1;e2] /\ body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env (Builtin a bt [e1;e2]) es /\
  compile_expr cenv ty (Builtin a bt [e1;e2]) sa = (vv,sb) /\
  compile_expr cenv ty (gas_shadow_expr (Builtin a bt [e1;e2])) shadow_sa =
    (vv,shadow_sb) /\
  lower_value compile_expr cenv (expr_type e1) e1 sa = (x,s1) /\
  lower_value compile_expr cenv (expr_type e2) e2 s1 = (y,s2) /\
  lower_value compile_expr cenv (expr_type e1) (gas_shadow_expr e1) shadow_sa =
    (x,shadow_s1) /\
  lower_value compile_expr cenv (expr_type e2) (gas_shadow_expr e2) shadow_s1 =
    (y,shadow_s2) /\
  (if bt = ECAdd then compile_ecadd_points x y s2
   else compile_ecmul_point x y s2) = (res,sb) /\
  vv = FST (as_ptr_val a LocMemory (res,sb)) /\
  gas_shadow_state sa shadow_sa /\ gas_shadow_state s1 shadow_s1 /\
  gas_shadow_state s2 shadow_s2 /\ gas_shadow_state sb shadow_sb /\
  gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
  gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
  MEM shadow_func shadow_ctx.ctx_functions /\
  fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  ~ctx_has_dalloca ctx /\ (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  gas_admissible (eval_expr cx (Builtin a bt [e1;e2])) expr_vv_res_ok es /\
  return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!tail. bind (eval_expr cx e1) (read_result cx)
      (es with gas_obs := gas_explicit marks1 s0.vs_gas_readings ++ tail) =
      (INL v1,es1 with gas_obs := tail)) /\
  storage_trace_domain cx st0 es1.storage_trace /\
  ~t1.vs_halted /\ es1.gas_obs = [] /\
  (!H. valid_horizon cx st0 H es1.storage_trace ==>
    expr_post H ctx func cenv cx e1 es sa s1 s0 es1 v1 x t1 /\
    expr_store_bound cx (expr_type e1) v1 x t1 /\
    t1.vs_current_bb = s1.cs_current_bb /\
    t1.vs_inst_idx = LENGTH s1.cs_current_insts /\
    alloca_history func t1 /\ s0.vs_alloca_next <= t1.vs_alloca_next /\
    ghost_inv_at (DF H) lo d cenv cx es1 G1 tn1 t1 /\
    ptr_val_ok cx (post_value_type cenv e1) v1 x G1 tn1 t1 /\
    (~is_word_type (post_value_type cenv e1) ==> ptr_buf_ok cenv e1 x G1 t1) /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1) /\
  (!tail. bind (eval_expr cx e2) (read_result cx)
      (es1 with gas_obs := gas_explicit marks2 t1.vs_gas_readings ++ tail) =
      (INL v2,es2 with gas_obs := tail)) /\
  storage_trace_domain cx st0 es2.storage_trace /\
  ~t2.vs_halted /\ es2.gas_obs = [] /\
  (!H. valid_horizon cx st0 H es2.storage_trace ==>
    expr_post H ctx func cenv cx e2 es1 s1 s2 t1 es2 v2 y t2 /\
    expr_store_bound cx (expr_type e2) v2 y t2 /\
    t2.vs_current_bb = s2.cs_current_bb /\
    t2.vs_inst_idx = LENGTH s2.cs_current_insts /\
    alloca_history func t2 /\ t1.vs_alloca_next <= t2.vs_alloca_next /\
    ghost_inv_at (DF H) lo d cenv cx es2 G2 tn2 t2 /\
    ptr_val_ok cx (post_value_type cenv e2) v2 y G2 tn2 t2 /\
    (~is_word_type (post_value_type cenv e2) ==> ptr_buf_ok cenv e2 y G2 t2) /\
    ghost_kept_at lo cenv es1 s1 G1 tn1 t1 G2 tn2) ==>
  ?ib ob ca cp sm src dst wi wo addr an id gv cv gi ci ai bb u Gu tnu.
    addr = (if bt = ECAdd then 6w else 7w) /\
    an = (if bt = ECAdd then 128w else 96w) /\
    ib.buf_operand = Var src /\ ob.buf_operand = Var dst /\
    context$compile_alloc_buffer (w2n an) s2 = (ib,ca) /\
    context$compile_alloc_buffer 64 cp = (ob,sm) /\
    (if bt = ECAdd then
      (do xp <- emit_op ADD [x; Lit 0w];
          vx <- emit_op MLOAD [xp];
          dst0 <- emit_op ADD [ib.buf_operand; Lit 0w];
          emit_void MSTORE [dst0; vx];
          yp <- emit_op ADD [x; Lit 32w];
          vy <- emit_op MLOAD [yp];
          dst1 <- emit_op ADD [ib.buf_operand; Lit 32w];
          emit_void MSTORE [dst1; vy];
          xp2 <- emit_op ADD [y; Lit 0w];
          vx2 <- emit_op MLOAD [xp2];
          dst2 <- emit_op ADD [ib.buf_operand; Lit 64w];
          emit_void MSTORE [dst2; vx2];
          yp2 <- emit_op ADD [y; Lit 32w];
          vy2 <- emit_op MLOAD [yp2];
          dst3 <- emit_op ADD [ib.buf_operand; Lit 96w];
          emit_void MSTORE [dst3; vy2] od) ca = ((),cp)
     else
      (do xp <- emit_op ADD [x; Lit 0w];
          vx <- emit_op MLOAD [xp];
          dst0 <- emit_op ADD [ib.buf_operand; Lit 0w];
          emit_void MSTORE [dst0; vx];
          yp <- emit_op ADD [x; Lit 32w];
          vy <- emit_op MLOAD [yp];
          dst1 <- emit_op ADD [ib.buf_operand; Lit 32w];
          emit_void MSTORE [dst1; vy];
          dst2 <- emit_op ADD [ib.buf_operand; Lit 64w];
          emit_void MSTORE [dst2; y] od) ca = ((),cp)) /\
    (do gas <- emit_op GAS [];
        success <- emit_op STATICCALL
          [gas; Lit addr; Var src; Lit an; Var dst; Lit 64w];
        emit_void ASSERT [success]; return (Var dst) od) sm = (res,sb) /\
    gi = mk_inst id GAS [] [gv] /\
    ci = mk_inst (id+1) STATICCALL
      [Var gv; Lit addr; Var src; Lit an; Var dst; Lit 64w] [cv] /\
    ai = mk_inst (id+2) ASSERT [Var cv] [] /\
    emitted_insts sm sb = [gi;ci;ai] /\
    emitted_insts s2 sb = emitted_insts s2 sm ++ emitted_insts sm sb /\
    eval_operand (Var src) u = SOME wi /\ eval_operand (Var dst) u = SOME wo /\
    src <> gv /\ dst <> gv /\ dst <> cv /\
    not_fresh_at sm src /\ not_fresh_at sm dst /\
    ~not_fresh_at sm gv /\ ~not_fresh_at sm cv /\
    s2.cs_next_var <= sm.cs_next_var /\ s2.cs_next_id <= sm.cs_next_id /\
    local_ptrs_reserved cenv sm /\
    (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
    (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
    (lo <> 0 ==> !z. cenv.ce_imm_alloca = SOME (Var z) ==> not_fresh_at sm z) /\
    ~u.vs_halted /\ ~ctx_has_dalloca ctx /\
    lookup_block u.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX [gi;ci;ai] (DROP u.vs_inst_idx bb.bb_instructions) /\
    (func.fn_name,id) NOTIN gas_explicit_sites ctx shadow_ctx /\
    w2n wi + w2n an <= u.vs_alloca_next /\
    w2n wo + w2n (64w:256 word) <= u.vs_alloca_next /\ lo <= w2n wo /\
    u.vs_current_bb = sm.cs_current_bb /\
    u.vs_inst_idx = LENGTH sm.cs_current_insts /\
    alloca_history func u /\ t2.vs_alloca_next <= u.vs_alloca_next /\
    (!p. eval_operand x t2 = SOME p ==>
      mem_word_at (w2n wi) u.vs_memory = mem_word_at (w2n p) t2.vs_memory /\
      mem_word_at (w2n wi+32) u.vs_memory = mem_word_at (w2n p+32) t2.vs_memory) /\
    (!q. eval_operand y t2 = SOME q ==>
      if bt = ECAdd then
        mem_word_at (w2n wi+64) u.vs_memory = mem_word_at (w2n q) t2.vs_memory /\
        mem_word_at (w2n wi+96) u.vs_memory = mem_word_at (w2n q+32) t2.vs_memory
      else mem_word_at (w2n wi+64) u.vs_memory = q) /\
    (!z. not_fresh_at s2 z ==> lookup_var z u = lookup_var z t2) /\
    (!H. valid_horizon cx st0 H es2.storage_trace ==>
      gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
        (t2,G2,tn2) [] (OK u,Gu,tnu) /\
      ghost_kept_at lo cenv es2 s2 G2 tn2 t2 Gu tnu /\
      wb_frame cenv es2 es2 s2 t2 u /\
      ghost_inv_at (DF H) lo d cenv cx es2 Gu tnu u /\
      stmt_state_rel H ctx func cenv cx es2 u /\
      local_ptrs_rel func cenv es2.scopes u /\
      ptr_covers Gu tnu src u (w2n an) /\ ptr_covers Gu tnu dst u (w2n (64w:256 word)) /\
      allocas_from lo u /\
      tnu.t_stor SUBSET (DF H).d_stor u.vs_call_ctx.cc_address
        (u.vs_accounts u.vs_call_ctx.cc_address).storage /\
      tnu.t_trans SUBSET (DF H).d_trans u.vs_call_ctx.cc_address
        (u.vs_transient u.vs_call_ctx.cc_address) /\
      (!i. w2n wi <= i /\ i < w2n wi + w2n an ==> i NOTIN tnu.t_mem) /\
      (addr = 1w ==> !i. w2n wo <= i /\ i < w2n wo + 32 ==> i NOTIN tnu.t_mem) /\
      (!name b sz. local_region cenv es2.scopes u name b sz ==>
        regions_disjoint (w2n wo) (w2n (64w:256 word)) b sz) /\
      (!aid b sz. aid < s2.cs_next_id /\ FLOOKUP u.vs_allocas aid = SOME (b,sz) ==>
        regions_disjoint (w2n wo) (w2n (64w:256 word)) b sz) /\
      (cenv.ce_is_ctor ==> !name tv iv off.
        FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
        FLOOKUP (case ALOOKUP es2.immutables cx.txn.target of NONE => FEMPTY
          | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (tv,iv) ==>
        regions_disjoint (w2n wo) (w2n (64w:256 word)) off (type_memory_size tv)))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `bind (eval_expr cx e1) (read_result cx)
     (es with gas_obs := gas_explicit marks1 s0.vs_gas_readings ++ es1.gas_obs) =
     (INL v1,es1)` by
    (qpat_assum `!tail. bind (eval_expr cx e1) _ _ = _`
       (qspec_then `es1.gas_obs` mp_tac) >> simp[]) >>
  `bind (eval_expr cx e2) (read_result cx)
     (es1 with gas_obs := gas_explicit marks2 t1.vs_gas_readings ++ es2.gas_obs) =
     (INL v2,es2)` by
    (qpat_assum `!tail. bind (eval_expr cx e2) _ _ = _`
       (qspec_then `es2.gas_obs` mp_tac) >> simp[]) >>
  `storage_trace_frame (bind (eval_expr cx e1) (read_result cx)) /\
   storage_trace_frame (bind (eval_expr cx e2) (read_result cx))` by
    (conj_tac >> irule storage_trace_frame_bind_all >>
     simp[storage_trace_frame_read_result, evaluate_storage_trace_frame]) >>
  `!H. valid_horizon cx st0 H es2.storage_trace ==>
       valid_horizon cx st0 H es1.storage_trace` by
    (rpt strip_tac >>
     qpat_assum `bind (eval_expr cx e2) _ _ = _`
       (mp_then (Pos last) mp_tac storage_trace_frame_prefix) >>
     simp[] >> strip_tac >> gvs[valid_horizon_def]) >>
  `expr_sim_inv cenv cx env es` by fs[expr_body_pre_def] >>
  `!n. bt <> Slice n` by (rpt strip_tac >> gvs[]) >>
  `expr_body_pre cenv cx env e1 es` by
    (drule expr_body_pre_builtin_arg >>
     disch_then (qspecl_then [`e1`,`es`] mp_tac) >> simp[]) >>
  `post_value_type cenv e1 = expr_type e1` by
    (irule post_value_type_ec_point >> simp[] >>
     qexistsl_tac [`cx`,`env`,`es`] >> fs[expr_body_pre_def]) >>
  qpat_assum `lower_value _ _ _ e1 _ = _`
    (mp_then Any strip_assume_tac (cj 2 exprLoweringPropsTheory.compile_expr_grows)) >>
  qpat_assum `lower_value _ _ _ e2 _ = _`
    (mp_then Any strip_assume_tac (cj 2 exprLoweringPropsTheory.compile_expr_grows)) >>
  `local_ptrs_reserved cenv s1 /\ local_ptrs_reserved cenv s2` by
    metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var] >>
  `MAP FDOM es1.scopes = MAP FDOM es2.scopes` by
    (qpat_assum `bind (eval_expr cx e2) _ _ = _`
       (mp_then Any mp_tac
         (CONV_RULE (DEPTH_CONV ETA_CONV)
           exprSimWordArgsTheory.forced_eval_expr_preserves_scopes_dom)) >> simp[]) >>
  `valid_horizon cx st0 (storage_trace_horizon es2.storage_trace) es2.storage_trace` by
    fs[storage_trace_domain_def] >>
  `valid_horizon cx st0 (storage_trace_horizon es2.storage_trace) es1.storage_trace` by
    metis_tac[] >>
  qpat_assum `!H. valid_horizon _ _ H es1.storage_trace ==> _`
    (qspec_then `storage_trace_horizon es2.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H es2.storage_trace ==> _ /\ _`
    (qspec_then `storage_trace_horizon es2.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  `safe_operand s1 x` by
    (irule ec_point_lower_value_safe_operand >> metis_tac[]) >>
  `(!z. x = Var z ==> not_fresh_at s1 z) /\ (!l. x <> Label l)` by
    fs[exprSafeOperandTheory.safe_operand_def] >>
  drule_all expr_post_operand_word >> strip_tac >>
  `!w. eval_operand x t1 = SOME w ==> eval_operand x t2 = SOME w` by
    metis_tac[optionTheory.SOME_11] >>
  drule_all ec_first_point_staging_ready >> strip_tac >>
  `ghost_kept cenv es1 s1 G1 tn1 t1 G2 tn2` by
    (qpat_assum `ghost_kept_at lo cenv es1 s1 G1 tn1 t1 G2 tn2` mp_tac >>
     simp[NoAsms, bodyPtrDefsTheory.ghost_kept_at_def,
          bodyPtrDefsTheory.ghost_kept_def] >> metis_tac[]) >>
  `ptr_val_ok cx (expr_type e1) v1 x G1 tn1 t1` by metis_tac[] >>
  `value_has_type (ArrayTV (BaseTV (UintT 256)) (Fixed 2)) v1` by
    (`expr_body_pre cenv cx env e1
        (es with gas_obs := gas_explicit marks1 s0.vs_gas_readings ++ es1.gas_obs)` by
       simp[expr_body_pre_gas_obs] >>
     qpat_assum `expr_body_pre _ _ _ e1 (es with gas_obs := _)`
       (mp_then Any mp_tac
         (CONV_RULE (DEPTH_CONV ETA_CONV)
           exprSimHypsTheory.memory_rhs_read_annotation_typed)) >>
     disch_then drule >>
     simp[vyperTypeExprSoundnessTheory.value_runtime_typed_def,
          vyperValueTheory.evaluate_type_def]) >>
  `!w. eval_operand x t2 = SOME w ==>
       !i. w2n w <= i /\ i < w2n w + 64 ==> i NOTIN tn2.t_mem` by
    metis_tac[bodyPtrPrecompileBuiltinsOperandsTheory.ec_point_clean_kept] >>
  drule_all bodyPtrPrecompileBuiltinsOperandsTheory.ec_point_covers_kept >> strip_tac >>
  `cs_extends s2 sb` by
    (Cases_on `bt = ECAdd` >> gvs[] >>
     metis_tac[externalEntryShapeTheory.compile_ecadd_points_labels,
               externalEntryShapeTheory.compile_ecmul_point_labels, pairTheory.SND]) >>
  `cs_extends s1 sb` by metis_tac[compileEnvTheory.cs_extends_trans] >>
  `fn_has_code s2 sb func` by metis_tac[fragExecTheory.fn_has_code_split] >>
  `!i. MEM i (emitted_insts s2 sb) ==> MEM i (fn_insts func)` by
    metis_tac[exprSimHashTheory.hash_emitted_inst_mem] >>
  Cases_on `bt = ECAdd`
  >- (gvs[] >> drule_all ecadd_points_prefix >> strip_tac >>
      rename1 `compile_alloc_buffer 128 s2 = (ib,ca)` >>
      `stmt_state_rel (storage_trace_horizon es2.storage_trace)
         ctx func cenv cx es2 t2` by fs[expr_post_def] >>
      `ghost_inv_at (DF (storage_trace_horizon es2.storage_trace))
         lo d cenv cx es2 G2 tn2 t2` by metis_tac[] >>
      `allocas_from lo t2 /\ lo <= t2.vs_alloca_next` by
        metis_tac[bodyPtrDefsTheory.ghost_inv_at_def] >>
      qpat_assum `compile_alloc_buffer 128 s2 = _`
        (mp_then Any strip_assume_tac
          abiBufferAllocationCodeTheory.compile_alloc_buffer_code) >>
      drule (cj 1 ec_points_code_shape) >> strip_tac >>
      `cs_extends ca sb` by
        (simp[compileEnvTheory.cs_extends_def] >> qexists_tac `[]` >>
         fs[exprLoweringPropsTheory.same_blocks_def] >>
         simp[rich_listTheory.IS_PREFIX_APPEND] >>
         metis_tac[listTheory.APPEND_ASSOC]) >>
      `fn_has_code s2 ca func` by
        metis_tac[fragExecTheory.fn_has_code_split,
                  loweringHaltTheory.compile_alloc_buffer_extends] >>
      `128 < dimword (:256)` by simp[wordsTheory.dimword_def] >>
      drule_all alloc_buffer_origin_ptr_path >>
      disch_then (qspecl_then [`tn2`,`gas_explicit_sites ctx shadow_ctx`,`PG`,`G2`]
        (qx_choose_then `src` (qx_choose_then `wi` (qx_choose_then `ta`
          (qx_choose_then `Ga` (qx_choose_then `tna` strip_assume_tac)))))) >>
      drule ecadd_payload_point_cuts >> strip_tac >>
      `not_fresh_at s2 p /\ not_fresh_at ca p` by
        (fs[compileEnvTheory.not_fresh_at_def] >> decide_tac) >>
      `lookup_var p ta = lookup_var p t2 /\
       FLOOKUP Ga p = FLOOKUP G2 p /\
       op_taint tna (Var p) = op_taint tn2 (Var p)` by metis_tac[] >>
      `lookup_var p ta = SOME w /\ ptr_covers Ga tna p ta 64` by
        (fs[bodyPtrDefsTheory.ptr_covers_def,
            venomStateTheory.eval_operand_def] >> metis_tac[]) >>
      `ta.vs_alloca_next >= t2.vs_alloca_next /\
       ta.vs_memory = t2.vs_memory /\ ta.vs_halted = t2.vs_halted` by
        (qpat_assum `ta with <|vs_vars := _; vs_allocas := _;
           vs_alloca_next := _; vs_inst_idx := _|> = t2` mp_tac >>
         simp[venomStateTheory.venom_state_component_equality]) >>
      `w2n w + 64 < dimword (:256)` by
        metis_tac[ec_point_pointer_bound] >>
      `regions_disjoint (w2n wi) 128 (w2n w) 64` by
        (irule exprSimECArithTheory.ec_point_fresh_scratch_disjoint >>
         rpt (first_assum (irule_at Any)) >> simp[]) >>
      FAIL_TAC "ECAdd point preparation") >>
  gvs[] >> drule_all ecmul_points_prefix >> strip_tac >>
  FAIL_TAC "ECMul staging"
QED
