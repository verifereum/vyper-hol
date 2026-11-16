Theory bodyFullBuiltinECMulStagingCore
Ancestors
  bodyFullBuiltinECArithOperands bodyFullBuiltinECArithTransfers
  bodyFullBuiltinECArithPayloadShape bodyFullBuiltinECArithPointCopy
  bodyFullAllocaFresh bodyFullAllocGeneric bodyFullUnwrapRun bodyFullGhostFrame
  allocaHistoryFragment bodyFullUnwrapSlotPost
  bodyMemEcArithCode bodyMemEcArithSafe bodyMemEcArithAssemble bodyBinopFragMemory
  bodyPtrMakeArrayCopyStateFrame exprSimAbiEncodeMemoryLength exprSimHash
  bodySimFull bodyFullPreds exprSimECArith
  gasShadowCompile exprSimHypsDefs exprLowering loweringPosts vyperAST list
  vyperStorageTrace vyperStorageFootprint exprSimHyps exprSimOperands exprSimSource

open compileEnvTheory;

Theorem ecmul_staging_full_from_transfers:
  bt = ECMul /\
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
    expr_store_bound cx (post_value_type cenv e1) v1 x t1 /\
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
    expr_store_bound cx (post_value_type cenv e2) v2 y t2 /\
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
    pure_frame cenv func es2 s2 t2 u /\
    FLOOKUP u.vs_allocas cp.cs_next_id = SOME (w2n wo,64) /\
    s2.cs_next_id <= cp.cs_next_id /\
    MEM (mk_inst cp.cs_next_id ALLOCA [Lit 64w] [dst]) (fn_insts func) /\
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
  `expr_sim_inv cenv cx env es1` by
    (`expr_body_pre cenv cx env e1
        (es with gas_obs := gas_explicit marks1 s0.vs_gas_readings ++ es1.gas_obs)` by
       simp[expr_body_pre_gas_obs] >>
     drule_all (CONV_RULE (DEPTH_CONV ETA_CONV)
       (cj 1 exprSimSourceTheory.expr_body_pre_eval)) >> simp[]) >>
  `expr_body_pre cenv cx env e2 es1` by
    (irule expr_body_pre_builtin_arg >>
     conj_tac >- simp[] >>
     qexistsl_tac [`a`,`[e1;e2]`,`bt`,`es`] >> simp[]) >>
  `vyperTypeExprSoundness$value_runtime_typed env (expr_type e2) v2` by
    (`expr_body_pre cenv cx env e2
        (es1 with gas_obs := gas_explicit marks2 t1.vs_gas_readings ++ es2.gas_obs)` by
       simp[expr_body_pre_gas_obs] >>
     qpat_assum `expr_body_pre _ _ _ e2 (es1 with gas_obs := _)`
       (mp_then Any mp_tac
         (CONV_RULE (DEPTH_CONV ETA_CONV)
           exprSimHypsTheory.memory_rhs_read_annotation_typed)) >>
     disch_then drule >> simp[]) >>
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
  `expr_store_bound cx (expr_type e1) v1 x t1` by metis_tac[] >>
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
  gvs[] >> drule_all ecmul_points_prefix >> strip_tac >>
      rename1 `compile_alloc_buffer 96 s2 = (ib,ca)` >>
      `stmt_state_rel (storage_trace_horizon es2.storage_trace)
         ctx func cenv cx es2 t2` by fs[expr_post_def] >>
      `ghost_inv_at (DF (storage_trace_horizon es2.storage_trace))
         lo d cenv cx es2 G2 tn2 t2` by metis_tac[] >>
      `allocas_from lo t2 /\ lo <= t2.vs_alloca_next` by
        metis_tac[bodyPtrDefsTheory.ghost_inv_at_def] >>
      qpat_assum `compile_alloc_buffer 96 s2 = _`
        (mp_then Any strip_assume_tac
          abiBufferAllocationCodeTheory.compile_alloc_buffer_code) >>
      drule (cj 2 ec_points_code_shape) >> strip_tac >>
      `cs_extends ca sb` by
        (simp[compileEnvTheory.cs_extends_def] >> qexists_tac `[]` >>
         fs[exprLoweringPropsTheory.same_blocks_def] >>
         simp[rich_listTheory.IS_PREFIX_APPEND] >>
         metis_tac[listTheory.APPEND_ASSOC]) >>
      `fn_has_code s2 ca func` by
        metis_tac[fragExecTheory.fn_has_code_split,
                  loweringHaltTheory.compile_alloc_buffer_extends] >>
      `96 < dimword (:256)` by simp[wordsTheory.dimword_def] >>
      qpat_assum `stmt_state_rel (storage_trace_horizon _) _ _ _ _ _ t2`
        (fn ssr => let
           val horizon = hd (snd (strip_comb (concl ssr)));
           val th = alloc_buffer_origin_ptr_path;
           val hv = valOf (List.find (fn v => fst (dest_var v) = "H")
             (free_vars (concl th)));
           val typed = INST_TYPE (match_type (type_of hv) (type_of horizon)) th;
           val (_,post) = strip_exists (snd (dest_imp (concl typed)));
           val hv' = fst (dest_forall (List.nth (strip_conj post,6)));
           val typed = INST_TYPE (match_type (type_of hv') (type_of horizon)) typed;
         in drule_all typed end) >>
      disch_then (qspecl_then [`tn2`,`gas_explicit_sites ctx shadow_ctx`,`PG`,`G2`]
        (qx_choose_then `src` (qx_choose_then `wi` (qx_choose_then `ta`
          (qx_choose_then `Ga` (qx_choose_then `tna` strip_assume_tac)))))) >>
      drule ecmul_payload_point_cut >> strip_tac >>
      `not_fresh_at s2 p /\ not_fresh_at ca p` by
        (fs[loweringStateRelDefsTheory.not_fresh_at_def] >> decide_tac) >>
      `lookup_var p ta = lookup_var p t2 /\
       FLOOKUP Ga p = FLOOKUP G2 p /\
       op_taint tna (Var p) = op_taint tn2 (Var p)` by metis_tac[] >>
      `lookup_var p ta = SOME w /\ ptr_covers Ga tna p ta 64` by
        (gvs[bodyPtrDefsTheory.ptr_covers_def,
             venomStateTheory.eval_operand_def]) >>
      `ta.vs_alloca_next >= t2.vs_alloca_next /\
       ta.vs_memory = t2.vs_memory /\ ta.vs_halted = t2.vs_halted` by
        (qpat_assum `ta with <|vs_vars := _; vs_allocas := _;
           vs_alloca_next := _; vs_inst_idx := _|> = t2` mp_tac >>
         simp[venomStateTheory.venom_state_component_equality]) >>
      `w2n w + 64 < dimword (:256)` by
        metis_tac[ec_point_pointer_bound] >>
      `regions_disjoint (w2n wi) 96 (w2n w) 64` by
        (irule bodyMemEcArithAssembleTheory.ec_point_fresh_scratch_disjoint >>
         qpat_assum `expr_val_at _ _ _ sa s2 _ _ _ _` (irule_at Any) >>
         qexists `ta` >> simp[] >>
         rpt conj_tac >> first_assum ACCEPT_TAC) >>
      `cm.cs_current_insts = ca.cs_current_insts ++ emitted_insts ca cm /\
       same_blocks ca cm /\ ca.cs_next_var <= cm.cs_next_var /\
       ca.cs_next_id <= cm.cs_next_id` by
        (qpat_assum `_ ca = ((),cm)` mp_tac >>
         simp[NoAsms, emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
           compileEnvTheory.comp_bind_def, compileEnvTheory.comp_ignore_bind_def,
           compileEnvTheory.comp_return_def, compileEnvTheory.fresh_id_def,
           compileEnvTheory.fresh_var_def, compileEnvTheory.emit_def] >>
         disch_then (SUBST1_TAC o SYM) >>
         simp[NoAsms, exprLoweringPropsTheory.emitted_insts_def,
              listTheory.APPEND_ASSOC, rich_listTheory.DROP_APPEND1,
              exprLoweringPropsTheory.same_blocks_def]) >>
      `sp.cs_current_insts = cm.cs_current_insts ++ emitted_insts cm sp /\
       same_blocks cm sp /\ cm.cs_next_var <= sp.cs_next_var /\
       cm.cs_next_id <= sp.cs_next_id` by
        (qpat_assum `_ cm = ((),sp)` mp_tac >>
         simp[NoAsms, emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
           compileEnvTheory.comp_bind_def, compileEnvTheory.comp_ignore_bind_def,
           compileEnvTheory.comp_return_def, compileEnvTheory.fresh_id_def,
           compileEnvTheory.fresh_var_def, compileEnvTheory.emit_def] >>
         disch_then (SUBST1_TAC o SYM) >>
         simp[NoAsms, exprLoweringPropsTheory.emitted_insts_def,
              listTheory.APPEND_ASSOC, rich_listTheory.DROP_APPEND1,
              exprLoweringPropsTheory.same_blocks_def]) >>
      `cs_extends ca cm /\ cs_extends cm sp` by
        (simp[compileEnvTheory.cs_extends_def] >>
         fs[exprLoweringPropsTheory.same_blocks_def,
            rich_listTheory.IS_PREFIX_APPEND] >> metis_tac[]) >>
      `emitted_insts ca sp = emitted_insts ca cm ++ emitted_insts cm sp` by
        (irule arithmeticPropsTheory.emitted_insts_prefix_split >> simp[]) >>
      `cs_extends cm sb` by
        (simp[compileEnvTheory.cs_extends_def] >> qexists `[]` >>
         fs[exprLoweringPropsTheory.same_blocks_def] >>
         simp[rich_listTheory.IS_PREFIX_APPEND] >>
         metis_tac[listTheory.APPEND_ASSOC]) >>
      `fn_has_code ca sb func` by
        (irule (cj 2 fragExecTheory.fn_has_code_split) >> simp[] >>
         qexists `s2` >> simp[] >>
         metis_tac[loweringHaltTheory.compile_alloc_buffer_extends]) >>
      `fn_has_code ca cm func` by
        (irule (cj 1 fragExecTheory.fn_has_code_split) >> (metis_tac[])) >>
      `?bb. lookup_block ta.vs_current_bb func.fn_blocks = SOME bb /\
        isPREFIX (emitted_insts ca cm)
          (DROP ta.vs_inst_idx bb.bb_instructions)` by
        (`cm.cs_current_bb = ca.cs_current_bb` by
           fs[exprLoweringPropsTheory.same_blocks_def] >>
         drule stmtReasonLitFragMemoryTheory.fn_has_code_code >>
         simp[]) >>
      `!i. w2n w <= i /\ i < w2n w+64 ==> i NOTIN tna.t_mem` by
        (rpt strip_tac >> simp[] >>
         `i NOTIN tn2.t_mem` by metis_tac[] >>
         qpat_x_assum `!i. i IN tna.t_mem <=> _` (qspec_then `i` mp_tac) >>
         simp[] >> decide_tac) >>
      `w2n w+64 <= ta.vs_alloca_next /\ lo <= ta.vs_alloca_next /\
       ~ta.vs_halted` by (simp[] >> decide_tac) >>
      qpat_assum `ib.buf_operand = Var src` (fn th =>
        qpat_assum `_ ca = ((),cm)` (assume_tac o REWRITE_RULE [th])) >>
      Q.SUBGOAL_THEN
        `w2n w+64 <= w2n wi \/ w2n wi+64 <= w2n w` assume_tac >-
        (qpat_x_assum `regions_disjoint (w2n wi) 96 (w2n w) 64` mp_tac >>
         pure_rewrite_tac[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
      drule_all (SRULE [] (Q.INST [`pd` |-> `0`, `nd` |-> `96`]
        (SPEC_ALL ec_point_copy_origin_ptr_path))) >>
      disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`,`PG`]
        (qx_choose_then `tm` (qx_choose_then `Gm`
          (qx_choose_then `tnm` strip_assume_tac)))) >>
      `post_value_type cenv e2 = expr_type e2` by
        (irule post_value_type_word >> simp[compileEnvTheory.is_word_type_def]) >>
      `safe_operand s2 y` by
        (irule exprWordOperandTheory.lower_value_word_safe_operand >>
         goal_assum (drule_at Any) >> simp[compileEnvTheory.is_word_type_def] >>
         metis_tac[exprSimSourceTheory.expr_body_pre_var_types_well_formed,
                   expr_body_pre_def]) >>
      `(!z. y = Var z ==> not_fresh_at s2 z) /\ (!l. y <> Label l)` by
        fs[exprSafeOperandTheory.safe_operand_def] >>
      `?sw. eval_operand y t2 = SOME sw` by
        (qpat_assum `!H. valid_horizon cx st0 H es2.storage_trace ==> expr_post H ctx func cenv cx e2 es1 s1 s2 t1 es2 v2 y t2 /\ _`
           (qspec_then `storage_trace_horizon es2.storage_trace` mp_tac) >>
         (impl_tac >- first_assum ACCEPT_TAC) >>
         disch_then (fn packet => POP_ASSUM_LIST (K all_tac) >>
           mp_tac (CONJUNCT1 packet)) >>
         simp[expr_post_def,expr_val_rel_def] >> metis_tac[]) >>
      `op_taint tn2 y = {}` by
        fs[bodyPtrDefsTheory.ptr_val_ok_def,compileEnvTheory.is_word_type_def] >>
      `eval_operand y ta = SOME sw /\ op_taint tna y = {}` by
        (qpat_assum `eval_operand y t2 = SOME sw` (fn ev =>
         qpat_assum `op_taint tn2 y = {}` (fn clean =>
         qpat_assum `!z. y = Var z ==> not_fresh_at s2 z` (fn live =>
         qpat_assum `!l. y <> Label l` (fn nlabel =>
         qpat_assum `!x. not_fresh_at s2 x ==> lookup_var x ta = _ /\ _` (fn frame =>
           POP_ASSUM_LIST (K all_tac) >> MAP_EVERY assume_tac [ev,clean,live,nlabel,frame]))))) >>
         Cases_on `y` >> gvs[venomStateTheory.eval_operand_def,
           ptrDisciplineTheory.op_taint_def] >> metis_tac[]) >>
      `!z. not_fresh_at s2 z ==> not_fresh_at ca z` by
        (rpt strip_tac >> fs[loweringStateRelDefsTheory.not_fresh_at_def] >> decide_tac) >>
      `eval_operand y tm = SOME sw /\ op_taint tnm y = {}` by
        (qpat_assum `eval_operand y ta = SOME sw` (fn ev =>
         qpat_assum `op_taint tna y = {}` (fn clean =>
         qpat_assum `!z. y = Var z ==> not_fresh_at s2 z` (fn live =>
         qpat_assum `!l. y <> Label l` (fn nlabel =>
         qpat_assum `!z. not_fresh_at s2 z ==> not_fresh_at ca z` (fn mono =>
         qpat_assum `!x. not_fresh_at ca x ==> lookup_var x tm = _ /\ _` (fn frame =>
           POP_ASSUM_LIST (K all_tac) >> MAP_EVERY assume_tac [ev,clean,live,nlabel,mono,frame])))))) >>
         Cases_on `y` >> gvs[venomStateTheory.eval_operand_def,
           ptrDisciplineTheory.op_taint_def] >> metis_tac[]) >>
      `not_fresh_at cm src /\ (!z. y = Var z ==> not_fresh_at cm z)` by
        (rpt strip_tac >> fs[loweringStateRelDefsTheory.not_fresh_at_def] >> decide_tac) >>
      `lookup_var src tm = SOME wi /\ ptr_covers Gm tnm src tm 96` by
        (pure_rewrite_tac[bodyPtrDefsTheory.ptr_covers_def] >>
         qpat_assum `ptr_covers Ga tna src ta 96`
           (strip_assume_tac o REWRITE_RULE [bodyPtrDefsTheory.ptr_covers_def]) >> metis_tac[]) >>
      `tm.vs_alloca_next = ta.vs_alloca_next /\
       tm.vs_allocas = ta.vs_allocas /\ tm.vs_halted = ta.vs_halted /\
       tm.vs_current_bb = ta.vs_current_bb` by
        (qpat_assum `tm with <|vs_memory := _; vs_vars := _; vs_inst_idx := _|> = ta`
           mp_tac >> simp[venomStateTheory.venom_state_component_equality]) >>
      `allocas_from lo tm` by
        (qpat_assum `allocas_from lo ta`
           (mp_tac o REWRITE_RULE [ptrDisciplineTheory.allocas_from_def]) >>
         simp[ptrDisciplineTheory.allocas_from_def]) >>
      `w2n wi+96 <= tm.vs_alloca_next /\ lo <= tm.vs_alloca_next /\ ~tm.vs_halted` by simp[] >>
      `cs_extends sp sb` by
        (simp[compileEnvTheory.cs_extends_def] >> qexists `[]` >>
         fs[exprLoweringPropsTheory.same_blocks_def] >>
         simp[rich_listTheory.IS_PREFIX_APPEND] >> metis_tac[listTheory.APPEND_ASSOC]) >>
      `fn_has_code cm sb func` by
        (irule (cj 2 fragExecTheory.fn_has_code_split) >> simp[] >> qexists `ca` >> simp[]) >>
      `fn_has_code cm sp func` by
        (irule (cj 1 fragExecTheory.fn_has_code_split) >> simp[] >> qexists `sb` >> simp[]) >>
      `tm.vs_current_bb = cm.cs_current_bb /\ tm.vs_inst_idx = LENGTH cm.cs_current_insts` by
        (qpat_assum `tm.vs_inst_idx = _` (fn th => rewrite_tac[th]) >>
         simp[] >> fs[exprLoweringPropsTheory.same_blocks_def]) >>
      `?bb2. lookup_block tm.vs_current_bb func.fn_blocks = SOME bb2 /\
        isPREFIX (emitted_insts cm sp) (DROP tm.vs_inst_idx bb2.bb_instructions)` by
        (`sp.cs_current_bb = cm.cs_current_bb` by fs[exprLoweringPropsTheory.same_blocks_def] >>
         qpat_assum `fn_has_code cm sp func`
           (mp_then Any mp_tac stmtReasonLitFragMemoryTheory.fn_has_code_code) >> simp[]) >>
      qpat_assum `ib.buf_operand = Var src` (fn th =>
        qpat_assum `_ cm = ((),sp)` (assume_tac o REWRITE_RULE [th])) >>
      drule_all (SRULE [] (Q.INST [`pd` |-> `64`, `nd` |-> `96`]
        (SPEC_ALL ec_scalar_store_origin_ptr_path))) >>
      disch_then (qspecl_then [`gas_explicit_sites ctx shadow_ctx`,`PG`]
        (qx_choose_then `tp` (qx_choose_then `Gp` (qx_choose_then `tnp` strip_assume_tac)))) >>
      `!off len. regions_disjoint (w2n wi) 96 off len ==>
         mem_bytes_at off len tp.vs_memory = mem_bytes_at off len ta.vs_memory` by
        (rpt gen_tac >> disch_tac >>
         qpat_assum `tp.vs_memory = _` (fn th => pure_rewrite_tac[th]) >>
         dep_rewrite.DEP_REWRITE_TAC
           [Q.INST [`b` |-> `w2n (wi:256 word)`, `sz` |-> `96`]
             (SPEC_ALL exprSimHashTheory.mstore_region_frame)] >>
         conj_tac >- (simp[GSYM arithmeticTheory.ADD_ASSOC] >> decide_tac) >>
         qpat_assum `tm.vs_memory = _` (fn th => pure_rewrite_tac[th]) >>
         dep_rewrite.DEP_REWRITE_TAC
           [Q.INST [`b` |-> `w2n (wi:256 word)`, `sz` |-> `96`]
             (SPEC_ALL exprSimHashTheory.mstore_region_frame)] >>
         simp[GSYM arithmeticTheory.ADD_ASSOC] >> decide_tac) >>
      `LENGTH ta.vs_memory <= LENGTH tp.vs_memory` by
        (`LENGTH ta.vs_memory <= LENGTH tm.vs_memory` by
           (qpat_assum `tm.vs_memory = _` (fn th =>
              POP_ASSUM_LIST (K all_tac) >> pure_rewrite_tac[th]) >>
            metis_tac[arithmeticTheory.LESS_EQ_TRANS,
              exprSimAbiEncodeMemoryLengthTheory.abi_encode_mstore_memory_length]) >>
         `LENGTH tm.vs_memory <= LENGTH tp.vs_memory` by
           (qpat_assum `tp.vs_memory = _` (fn th =>
              POP_ASSUM_LIST (K all_tac) >> pure_rewrite_tac[th]) >>
            metis_tac[arithmeticTheory.LESS_EQ_TRANS,
              exprSimAbiEncodeMemoryLengthTheory.abi_encode_mstore_memory_length]) >>
         decide_tac) >>
      `copy_static tp = copy_static ta` by
        (qpat_assum `tp with <|vs_memory := _; vs_vars := _; vs_inst_idx := _|> = tm`
           (mp_tac o Q.AP_TERM `copy_static`) >>
         qpat_assum `tm with <|vs_memory := _; vs_vars := _; vs_inst_idx := _|> = ta`
           (mp_tac o Q.AP_TERM `copy_static`) >>
         simp[NoAsms, exprSimStorageCopyTheory.copy_static_def] >> metis_tac[]) >>
      `tp.vs_allocas = ta.vs_allocas /\ tp.vs_alloca_next = ta.vs_alloca_next /\
       tp.vs_halted = ta.vs_halted /\ tp.vs_current_bb = ta.vs_current_bb` by
        (qpat_assum `tp with <|vs_memory := _; vs_vars := _; vs_inst_idx := _|> = tm`
           (mp_tac o Q.AP_TERM `\z. (z.vs_allocas,z.vs_alloca_next,z.vs_halted,z.vs_current_bb)`) >>
         fs[exprLoweringPropsTheory.same_blocks_def]) >>
      `!z. not_fresh_at ca z ==> lookup_var z tp = lookup_var z ta` by
        (gen_tac >> disch_tac >>
         `not_fresh_at cm z` by
           (fs[loweringStateRelDefsTheory.not_fresh_at_def] >> decide_tac) >>
         metis_tac[]) >>
      `!H. valid_horizon cx st0 H es2.storage_trace ==>
         stmt_state_rel H ctx func cenv cx es2 tp` by
        (gen_tac >> disch_tac >>
         MATCH_MP_TAC (Q.INST [`u` |-> `ta:venom_state`, `sa` |-> `s2:compile_state`,
           `sh` |-> `ca:compile_state`, `b` |-> `w2n (wi:256 word)`,
           `n` |-> `96`, `aid` |-> `s2.cs_next_id`,
           `p` |-> `STRING #"%" (toString s2.cs_next_var)`]
           (SPEC_ALL bodyPtrMakeArrayCopyStateFrameTheory.literal_copy_window_stmt_state_rel)) >>
         conj_tac >-
           (qpat_assum `!H'. stmt_state_rel H' ctx func cenv cx es2 t2 ==> _`
              (MATCH_MP_TAC o Q.SPEC `H`) >>
            qpat_assum `!H. valid_horizon cx st0 H es2.storage_trace ==>
              expr_post H ctx func cenv cx e2 es1 s1 s2 t1 es2 v2 _ t2 /\ _`
              (qspec_then `H` mp_tac) >>
            (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
            qpat_assum `expr_post H ctx func cenv cx e2 es1 s1 s2 t1 es2 v2 _ t2`
              (ACCEPT_TAC o CONJUNCT1 o REWRITE_RULE [expr_post_def])) >>
         conj_tac >- first_assum ACCEPT_TAC >>
         conj_tac >- (rpt strip_tac >>
           fs[loweringStateRelDefsTheory.not_fresh_at_def] >> decide_tac) >>
         conj_tac >- first_assum ACCEPT_TAC >>
         conj_tac >- first_assum ACCEPT_TAC >>
         conj_tac >- first_assum ACCEPT_TAC >>
         conj_tac >- first_assum ACCEPT_TAC >>
         conj_tac >- (rpt strip_tac >>
           qpat_assum `!off len. regions_disjoint (w2n wi) 96 off len ==> _` irule >>
           simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
         conj_tac >- first_assum ACCEPT_TAC >> simp[]) >>
      `!name b len. local_region cenv es2.scopes t2 name b len ==>
         regions_disjoint (w2n wi) 96 b len` by
        (qx_genl_tac [`name`,`b`,`len`] >> disch_tac >>
         `local_region cenv es2.scopes ta name b len` by
           (MATCH_MP_TAC (Q.SPECL [`cenv`,`es2.scopes`,`s2`,`es2.scopes`,
              `t2`,`ta`,`name`,`b`,`len`] exprSimPropsTheory.local_region_frame_fwd) >>
            simp[NoAsms] >> conj_tac >- first_assum ACCEPT_TAC >>
            conj_tac >-
              (qx_genl_tac [`oldvar`,`oldword`] >> strip_tac >>
               qpat_assum `!x. not_fresh_at s2 x ==> lookup_var x ta = _ /\ _`
                 (qspec_then `oldvar` mp_tac) >> simp[]) >>
            first_assum ACCEPT_TAC) >>
         qpat_assum `!name b len. local_region cenv es2.scopes ta name b len ==> _`
           (qspec_then `name` (qspec_then `b` (qspec_then `len` mp_tac))) >> simp[]) >>
      `pure_frame cenv func es2 s2 t2 tp` by
        (MATCH_MP_TAC (Q.SPECL [`cenv`,`func`,`es2`,`s2`,`t2`,`tp`,
           `s2.cs_next_id`,`[Lit 96w]`,
           `[STRING #"%" (toString s2.cs_next_var)]`,`w2n (wi:256 word)`,`96`]
           exprSimPropsTheory.pure_frame_fresh_alloca) >>
         conj_tac >- first_assum ACCEPT_TAC >> simp[NoAsms] >>
         conj_tac >- simp[] >>
         conj_tac >-
           (qx_genl_tac [`name`,`lb`,`lsz`] >> disch_tac >>
            `regions_disjoint (w2n wi) 96 lb lsz` by
              (qpat_assum `!name b len. local_region cenv es2.scopes t2 name b len ==> _`
                 (qspecl_then [`name`,`lb`,`lsz`] MATCH_MP_TAC) >>
               first_assum ACCEPT_TAC) >>
            qpat_assum `!off len. regions_disjoint (w2n wi) 96 off len ==> _`
              (fn frame => qpat_assum `regions_disjoint (w2n wi) 96 lb lsz`
                (fn rd => qpat_assum `ta.vs_memory = t2.vs_memory`
                  (fn memeq => ACCEPT_TAC (PURE_REWRITE_RULE [memeq]
                    (MATCH_MP (Q.SPECL [`lb`,`lsz`] frame) rd)))))) >>
         qx_genl_tac [`off`,`len`] >> disch_tac >>
         `regions_disjoint (w2n wi) 96 off len` by
           (fs[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
         qpat_assum `!off len. regions_disjoint (w2n wi) 96 off len ==> _`
           (fn frame => qpat_assum `regions_disjoint (w2n wi) 96 off len`
             (fn rd => qpat_assum `ta.vs_memory = t2.vs_memory`
               (fn memeq => ACCEPT_TAC (PURE_REWRITE_RULE [memeq]
                 (MATCH_MP (Q.SPECL [`off`,`len`] frame) rd)))))) >>
      qpat_assum `_ ca = ((),sp)`
        (mp_then Any strip_assume_tac (cj 2 ec_input_stores_shape)) >>
      `EVERY (\i. i.inst_opcode <> ALLOCA) (emitted_insts ca sp)` by
        (qpat_assum `_ ca = ((),sp)` (fn run =>
           POP_ASSUM_LIST (K all_tac) >> mp_tac run) >>
         simp[NoAsms, emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
           compileEnvTheory.comp_bind_def, compileEnvTheory.comp_ignore_bind_def,
           compileEnvTheory.comp_return_def, compileEnvTheory.fresh_id_def,
           compileEnvTheory.fresh_var_def, compileEnvTheory.emit_def] >>
         disch_then (SUBST1_TAC o SYM) >>
         simp[NoAsms, exprLoweringPropsTheory.emitted_insts_def,
           listTheory.APPEND_ASSOC, rich_listTheory.DROP_APPEND1,
           venomInstTheory.mk_inst_def]) >>
      `cs_extends ca sp` by
        metis_tac[compileEnvTheory.cs_extends_trans] >>
      `fn_has_code ca sp func` by
        (MATCH_MP_TAC (cj 1 fragExecTheory.fn_has_code_split) >>
         qexists `sb` >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
      `?bbfull rest. lookup_block ta.vs_current_bb func.fn_blocks = SOME bbfull /\
         DROP ta.vs_inst_idx bbfull.bb_instructions = emitted_insts ca sp ++ rest` by
        (`sp.cs_current_bb = ca.cs_current_bb` by
           fs[exprLoweringPropsTheory.same_blocks_def] >>
         qpat_assum `ta.vs_current_bb = ca.cs_current_bb`
           (fn eq => pure_rewrite_tac[eq]) >>
         qpat_assum `ta.vs_inst_idx = LENGTH ca.cs_current_insts`
           (fn eq => pure_rewrite_tac[eq]) >>
         qspecl_then [`ca`,`sp`,`func`,`emitted_insts ca sp`] mp_tac
           stmtReasonLitFragMemoryTheory.fn_has_code_code >>
         (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
         disch_then (fn th => POP_ASSUM_LIST (K all_tac) >> mp_tac th) >>
         rw[rich_listTheory.IS_PREFIX_APPEND] >> metis_tac[]) >>
      `tp.vs_inst_idx = ta.vs_inst_idx + LENGTH (emitted_insts ca sp)` by
        (qpat_assum `emitted_insts ca sp = _` (fn th => pure_rewrite_tac[th]) >>
         simp[NoAsms, listTheory.LENGTH_APPEND] >> decide_tac) >>
      `alloca_history func tp` by
        (qspecl_then [`func`,`ta`,`tp`,`bbfull`,`emitted_insts ca sp`,`rest`]
           mp_tac bodyBinopFragMemoryTheory.alloca_history_no_alloca_slice >>
         (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
         qpat_assum `tp.vs_inst_idx = ta.vs_inst_idx + LENGTH (emitted_insts ca sp)`
           (fn idx => pure_rewrite_tac[GSYM idx] >> simp[NoAsms])) >>
      `stmt_state_rel (storage_trace_horizon es2.storage_trace)
         ctx func cenv cx es2 tp` by
        (qpat_assum `!H. valid_horizon cx st0 H es2.storage_trace ==>
           stmt_state_rel H ctx func cenv cx es2 tp`
           (MATCH_MP_TAC o Q.SPEC `storage_trace_horizon es2.storage_trace`) >>
         first_assum ACCEPT_TAC) >>
      `allocas_from lo tp` by
        (qpat_assum `allocas_from lo ta`
           (mp_tac o REWRITE_RULE [ptrDisciplineTheory.allocas_from_def]) >>
         simp[ptrDisciplineTheory.allocas_from_def]) >>
      `lo <= tp.vs_alloca_next /\ ~tp.vs_halted /\
       tp.vs_current_bb = sp.cs_current_bb /\
       tp.vs_inst_idx = LENGTH sp.cs_current_insts` by
        (fs[exprLoweringPropsTheory.same_blocks_def] >> decide_tac) >>
      qpat_assum `compile_alloc_buffer 64 sp = (ob,sm)`
        (mp_then Any strip_assume_tac
          abiBufferAllocationCodeTheory.compile_alloc_buffer_code) >>
      `cs_extends sp sm` by
        metis_tac[loweringHaltTheory.compile_alloc_buffer_extends] >>
      qpat_assum `_ sm = (res,sb)`
        (mp_then Any strip_assume_tac exprSimPrecompilesTheory.computed_suffix_shape) >>
      `cs_extends sm sb` by
        (simp[compileEnvTheory.cs_extends_def] >> qexists `[]` >>
         fs[exprLoweringPropsTheory.same_blocks_def] >>
         simp[rich_listTheory.IS_PREFIX_APPEND] >>
         metis_tac[listTheory.APPEND_ASSOC]) >>
      `fn_has_code sp sb func` by
        (MATCH_MP_TAC (cj 2 fragExecTheory.fn_has_code_split) >>
         qexists `ca` >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
      `fn_has_code sp sm func` by
        (MATCH_MP_TAC (cj 1 fragExecTheory.fn_has_code_split) >>
         qexists `sb` >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
      `64 < dimword (:256)` by simp[wordsTheory.dimword_def] >>
      qpat_assum `stmt_state_rel (storage_trace_horizon _) _ _ _ _ _ tp`
        (fn ssr => let
           val horizon = hd (snd (strip_comb (concl ssr)));
           val th = alloc_buffer_origin_ptr_path;
           val hv = valOf (List.find (fn v => fst (dest_var v) = "H")
             (free_vars (concl th)));
           val typed = INST_TYPE (match_type (type_of hv) (type_of horizon)) th;
           val (_,post) = strip_exists (snd (dest_imp (concl typed)));
           val hv' = fst (dest_forall (List.nth (strip_conj post,6)));
           val typed = INST_TYPE (match_type (type_of hv') (type_of horizon)) typed;
         in drule_all (Q.INST [`n` |-> `64`,`sa` |-> `sp`,
           `sb` |-> `sm`,`s` |-> `tp`,`buf` |-> `ob`] typed) end) >>
      disch_then (qspecl_then [`tnp`,`gas_explicit_sites ctx shadow_ctx`,`PG`,`Gp`]
        (qx_choose_then `dst` (qx_choose_then `wo` (qx_choose_then `u`
          (qx_choose_then `Gu` (qx_choose_then `tnu` strip_assume_tac)))))) >>
      `(!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==>
         not_fresh_at s2 z) /\
       (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==>
         not_fresh_at s2 z)` by
        (rpt strip_tac >>
         `not_fresh_at sa z` by metis_tac[] >>
         irule stmtFragPtrTheory.not_fresh_at_mono >>
         qexists `sa` >> simp[] >> decide_tac) >>
      `!H. valid_horizon cx st0 H es2.storage_trace ==>
         ghost_inv_at (DF H) lo d cenv cx es2 Ga tna ta` by
        (gen_tac >> strip_tac >>
         qpat_assum `!H. valid_horizon cx st0 H es2.storage_trace ==>
           expr_post H ctx func cenv cx e2 es1 s1 s2 t1 es2 v2 _ t2 /\ _`
           (qspec_then `H` mp_tac) >>
         (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
         `stmt_state_rel H ctx func cenv cx es2 t2` by fs[expr_post_def] >>
         qpat_assum `stmt_state_rel H ctx func cenv cx es2 t2`
           (fn ssr => let
              val horizon = hd (snd (strip_comb (concl ssr)));
              val th = alloc_buffer_ghost_inv_at;
              val hv = valOf (List.find (fn v => fst (dest_var v) = "H")
                (free_vars (concl th)));
              val typed = INST_TYPE (match_type (type_of hv) (type_of horizon)) th;
            in MATCH_MP_TAC (Q.INST [`D` |-> `DF H`,`H` |-> `H`,
              `ctx` |-> `ctx`,`func` |-> `func`,`sa` |-> `s2`,
              `s` |-> `t2`,`t` |-> `ta`,`G` |-> `G2`,`tn` |-> `tn2`,
              `G'` |-> `Ga`,`tn'` |-> `tna`,
              `e` |-> `w2n (wi:256 word)+96`] typed) end) >> simp[]) >>
      `!z. not_fresh_at ca z ==>
         lookup_var z tp = lookup_var z ta /\ FLOOKUP Gp z = FLOOKUP Ga z /\
         op_taint tnp (Var z) = op_taint tna (Var z)` by
        (gen_tac >> strip_tac >>
         `not_fresh_at cm z` by
           (fs[loweringStateRelDefsTheory.not_fresh_at_def] >> decide_tac) >>
         qpat_assum `!x. not_fresh_at cm x ==> lookup_var x tp = _ /\ _`
           (qspec_then `z` mp_tac) >>
         qpat_assum `!x. not_fresh_at ca x ==> lookup_var x tm = _ /\ _`
           (qspec_then `z` mp_tac) >> simp[]) >>
      `!j. j < w2n wi \/ w2n wi+96 <= j ==>
         (j IN tnp.t_mem <=> j IN tna.t_mem)` by
        (qpat_assum `tnp.t_mem = _` (fn eq => pure_rewrite_tac[eq]) >>
         qpat_assum `tnm.t_mem = _` (fn eq => pure_rewrite_tac[eq]) >>
         simp[NoAsms, pred_setTheory.IN_DIFF, pred_setTheory.GSPECIFICATION] >>
         rpt strip_tac >> decide_tac) >>
      `lo <= w2n wi` by
        (qpat_assum `allocas_from lo ta`
           (mp_tac o PURE_REWRITE_RULE [ptrDisciplineTheory.allocas_from_def]) >>
         disch_then (qspecl_then [`s2.cs_next_id`,`w2n (wi:256 word)`,`96`] mp_tac) >>
         simp[]) >>
      `(!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==>
         not_fresh_at ca z) /\
       (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==>
         not_fresh_at ca z)` by
        (rpt strip_tac >> `not_fresh_at s2 z` by metis_tac[] >>
         MATCH_MP_TAC (Q.INST [`sa` |-> `s2`,`sm` |-> `ca`,`x` |-> `z`]
           stmtFragPtrTheory.not_fresh_at_mono) >>
         simp[]) >>
      `stmt_state_rel (storage_trace_horizon es2.storage_trace)
         ctx func cenv cx es2 ta` by
        (qpat_assum `!H'. stmt_state_rel H' ctx func cenv cx es2 t2 ==> _`
           (MATCH_MP_TAC o Q.SPEC `storage_trace_horizon es2.storage_trace`) >>
         first_assum ACCEPT_TAC) >>
      `local_ptrs_rel func cenv es2.scopes ta` by
        (qpat_assum `stmt_state_rel (storage_trace_horizon _) _ _ _ _ _ ta`
           (ACCEPT_TAC o CONJUNCT1 o PURE_REWRITE_RULE
             [loweringStateRelDefsTheory.state_rel_def] o CONJUNCT1 o
             PURE_REWRITE_RULE [exprLoweringPropsTheory.stmt_state_rel_def])) >>
      `tnp.t_stor = tna.t_stor /\ tnp.t_trans = tna.t_trans /\
       tnp.t_imm = tna.t_imm` by metis_tac[] >>
      `tp.vs_accounts = ta.vs_accounts /\ tp.vs_transient = ta.vs_transient /\
       tp.vs_call_ctx = ta.vs_call_ctx /\ tp.vs_immutables = ta.vs_immutables` by
        (qpat_assum `copy_static tp = copy_static ta`
           (mp_tac o Q.AP_TERM
             `\z. (z.vs_accounts,z.vs_transient,z.vs_call_ctx,z.vs_immutables)`) >>
         simp[NoAsms, exprSimStorageCopyTheory.copy_static_def]) >>
      `!H. valid_horizon cx st0 H es2.storage_trace ==>
         ghost_inv_at (DF H) lo d cenv cx es2 Gp tnp tp` by
        (gen_tac >> strip_tac >>
         qpat_assum `!H. valid_horizon cx st0 H es2.storage_trace ==>
           ghost_inv_at (DF H) lo d cenv cx es2 Ga tna ta`
           (qspec_then `H` mp_tac) >>
         (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
         qpat_assum `ghost_inv_at (DF H) lo d cenv cx es2 Ga tna ta`
           (fn initial => let
              val actualD = hd (snd (strip_comb (concl initial)));
              val th = bodyFullUnwrapSlotPostTheory.unwrap_slot_copy_ghost_inv_at;
              val dv = valOf (List.find (fn v => fst (dest_var v) = "D")
                (free_vars (concl th)));
            in MATCH_MP_TAC (Q.INST [`s` |-> `ta`,`z` |-> `tp`,
              `G` |-> `Ga`,`tn` |-> `tna`,`H` |-> `Gp`,`tf` |-> `tnp`,
              `start` |-> `w2n (wi:256 word)`,`nb` |-> `96`,`sa` |-> `ca`]
              (INST [dv |-> actualD] th)) end) >>
         conj_tac >- first_assum ACCEPT_TAC >>
         conj_tac >- first_assum ACCEPT_TAC >>
         conj_tac >- first_assum ACCEPT_TAC >>
         conj_tac >- first_assum ACCEPT_TAC >>
         conj_tac >- first_assum ACCEPT_TAC >>
         conj_tac >-
           (qx_genl_tac [`name`,`b`,`len`] >> strip_tac >>
            qpat_assum `!name b len. local_region cenv es2.scopes ta name b len ==> _`
              (qspecl_then [`name`,`b`,`len`] mp_tac) >>
            (impl_tac >- first_assum ACCEPT_TAC) >>
            simp[NoAsms, loweringStateRelDefsTheory.regions_disjoint_def]) >>
         conj_tac >- first_assum ACCEPT_TAC >>
         conj_tac >-
           (qx_genl_tac [`off`,`len`] >> strip_tac >>
            qpat_assum `!off len. regions_disjoint (w2n wi) 96 off len ==> _`
              (qspecl_then [`off`,`len`] MATCH_MP_TAC) >>
            simp[loweringStateRelDefsTheory.regions_disjoint_def]) >>
         conj_tac >- first_assum ACCEPT_TAC >>
         conj_tac >- first_assum ACCEPT_TAC >>
         conj_tac >-
           (pure_rewrite_tac[bodyPtrDefsTheory.stor_taint_ok_at_def] >>
            map_every (fn pat => qpat_assum pat
              (fn eq => pure_rewrite_tac[eq]))
              [`tnp.t_stor = tna.t_stor`,`tnp.t_trans = tna.t_trans`,
               `tnp.t_imm = tna.t_imm`,`tp.vs_accounts = ta.vs_accounts`,
               `tp.vs_transient = ta.vs_transient`,`tp.vs_call_ctx = ta.vs_call_ctx`,
               `tp.vs_immutables = ta.vs_immutables`] >>
            qpat_assum `ghost_inv_at (DF H) lo d cenv cx es2 Ga tna ta`
              (fn gh => ACCEPT_TAC (PURE_REWRITE_RULE
                [bodyPtrDefsTheory.stor_taint_ok_at_def]
                (List.nth (CONJUNCTS (PURE_REWRITE_RULE
                  [bodyPtrDefsTheory.ghost_inv_at_def] gh),3))))) >>
         conj_tac >- first_assum ACCEPT_TAC >> first_assum ACCEPT_TAC) >>
      `u.vs_memory = tp.vs_memory /\ u.vs_halted = tp.vs_halted` by
        (qpat_assum `u with <|vs_vars := _; vs_allocas := _;
           vs_alloca_next := _; vs_inst_idx := _|> = tp`
           (mp_tac o Q.AP_TERM `\z. (z.vs_memory,z.vs_halted)`) >> simp[NoAsms]) >>
      `pure_frame cenv func es2 s2 t2 u` by
        (MATCH_MP_TAC (Q.SPECL [`cenv`,`func`,`es2`,`s2`,`t2`,`tp`,`u`]
           exprSimPropsTheory.pure_frame_mem_tail) >>
         rpt conj_tac >> first_assum ACCEPT_TAC) >>
      `(!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==>
         not_fresh_at sp z) /\
       (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==>
         not_fresh_at sp z)` by
        (rpt strip_tac >> `not_fresh_at s2 z` by metis_tac[] >>
         MATCH_MP_TAC (Q.INST [`sa` |-> `s2`,`sm` |-> `sp`,`x` |-> `z`]
           stmtFragPtrTheory.not_fresh_at_mono) >>
         conj_tac >- first_assum ACCEPT_TAC >> simp[] >> decide_tac) >>
      `!H. valid_horizon cx st0 H es2.storage_trace ==>
         ghost_inv_at (DF H) lo d cenv cx es2 Gu tnu u` by
        (gen_tac >> strip_tac >>
         qpat_assum `!H. valid_horizon cx st0 H es2.storage_trace ==>
           ghost_inv_at (DF H) lo d cenv cx es2 Gp tnp tp`
           (qspec_then `H` mp_tac) >>
         (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
         `stmt_state_rel H ctx func cenv cx es2 tp` by
           (qpat_assum `!H. valid_horizon cx st0 H es2.storage_trace ==>
             stmt_state_rel H ctx func cenv cx es2 tp`
             (MATCH_MP_TAC o Q.SPEC `H`) >> first_assum ACCEPT_TAC) >>
         qpat_assum `stmt_state_rel H ctx func cenv cx es2 tp`
           (fn ssr => let
              val horizon = hd (snd (strip_comb (concl ssr)));
              val th = alloc_buffer_ghost_inv_at;
              val hv = valOf (List.find (fn v => fst (dest_var v) = "H")
                (free_vars (concl th)));
              val typed = INST_TYPE (match_type (type_of hv) (type_of horizon)) th;
            in MATCH_MP_TAC (Q.INST [`D` |-> `DF H`,`H` |-> `H`,
              `ctx` |-> `ctx`,`func` |-> `func`,`sa` |-> `sp`,
              `s` |-> `tp`,`t` |-> `u`,`G` |-> `Gp`,`tn` |-> `tnp`,
              `G'` |-> `Gu`,`tn'` |-> `tnu`,
              `e` |-> `w2n (wo:256 word)+64`] typed) end) >> simp[]) >>
      `!H. valid_horizon cx st0 H es2.storage_trace ==>
         stmt_state_rel H ctx func cenv cx es2 u` by
        (gen_tac >> strip_tac >>
         qpat_assum `!H'. stmt_state_rel H' ctx func cenv cx es2 tp ==> _`
           (MATCH_MP_TAC o Q.SPEC `H`) >>
         qpat_assum `!H. valid_horizon cx st0 H es2.storage_trace ==>
           stmt_state_rel H ctx func cenv cx es2 tp`
           (MATCH_MP_TAC o Q.SPEC `H`) >> first_assum ACCEPT_TAC) >>
      `not_fresh_at sp src` by
        (MATCH_MP_TAC (Q.INST [`sa` |-> `ca`,`sm` |-> `sp`,`x` |-> `src`]
           stmtFragPtrTheory.not_fresh_at_mono) >>
         conj_tac >- first_assum ACCEPT_TAC >> simp[] >> decide_tac) >>
      `lookup_var src tp = SOME wi /\ ptr_covers Gp tnp src tp 96` by
        (qpat_assum `!z. not_fresh_at ca z ==> lookup_var z tp = _ /\ _`
           (fn frame => qpat_assum `not_fresh_at ca src`
             (strip_assume_tac o MATCH_MP (Q.SPEC `src` frame))) >>
         conj_tac >-
           (qpat_assum `lookup_var src tp = lookup_var src ta`
              (fn eq => pure_rewrite_tac[eq]) >> first_assum ACCEPT_TAC) >>
         MATCH_MP_TAC (Q.INST [`G` |-> `Ga`,`tn` |-> `tna`,`p` |-> `src`,
           `s` |-> `ta`,`n` |-> `96`,`t` |-> `tp`]
           (SPEC_ALL decoderGhostFramePtrTheory.ptr_covers_frame)) >>
         rpt conj_tac >> first_assum ACCEPT_TAC) >>
      `lookup_var src u = SOME wi /\ ptr_covers Gu tnu src u 96` by
        (qpat_assum `!x. not_fresh_at sp x ==> lookup_var x u = _ /\ _`
           (fn frame => qpat_assum `not_fresh_at sp src`
             (strip_assume_tac o MATCH_MP (Q.SPEC `src` frame))) >>
         conj_tac >-
           (qpat_assum `lookup_var src u = lookup_var src tp`
              (fn eq => pure_rewrite_tac[eq]) >> first_assum ACCEPT_TAC) >>
         MATCH_MP_TAC (Q.INST [`G` |-> `Gp`,`tn` |-> `tnp`,`p` |-> `src`,
           `s` |-> `tp`,`n` |-> `96`,`t` |-> `u`]
           (Q.INST [`u` |-> `tf`] (SPEC_ALL decoderGhostFramePtrTheory.ptr_covers_frame))) >>
         rpt conj_tac >> first_assum ACCEPT_TAC) >>
      `!i. w2n wi <= i /\ i < w2n wi+96 ==> i NOTIN tnp.t_mem` by
        (qpat_assum `tnp.t_mem = _` (fn eq => pure_rewrite_tac[eq]) >>
         qpat_assum `tnm.t_mem = _` (fn eq => pure_rewrite_tac[eq]) >>
         simp[NoAsms, pred_setTheory.IN_DIFF, pred_setTheory.GSPECIFICATION] >>
         rpt strip_tac >> decide_tac) >>
      `!i. w2n wi <= i /\ i < w2n wi+96 ==> i NOTIN tnu.t_mem` by
        (gen_tac >> strip_tac >>
         qpat_assum `!i. i IN tnu.t_mem <=> _` (qspec_then `i` mp_tac) >>
         `i NOTIN tnp.t_mem` by metis_tac[] >> simp[] >> decide_tac) >>
      `!z. not_fresh_at s2 z ==>
         lookup_var z u = lookup_var z t2 /\ FLOOKUP Gu z = FLOOKUP G2 z /\
         op_taint tnu (Var z) = op_taint tn2 (Var z)` by
        (gen_tac >> strip_tac >>
         `not_fresh_at ca z /\ not_fresh_at sp z` by
           (conj_tac >>
            MATCH_MP_TAC (Q.INST [`sa` |-> `s2`,`x` |-> `z`]
              stmtFragPtrTheory.not_fresh_at_mono) >>
            conj_tac >- first_assum ACCEPT_TAC >> simp[] >> decide_tac) >>
         qpat_assum `!x. not_fresh_at s2 x ==> lookup_var x ta = _ /\ _`
           (fn frame => qpat_assum `not_fresh_at s2 z`
             (strip_assume_tac o MATCH_MP (Q.SPEC `z` frame))) >>
         qpat_assum `!x. not_fresh_at ca x ==> lookup_var x tp = _ /\ _`
           (fn frame => qpat_assum `not_fresh_at ca z`
             (strip_assume_tac o MATCH_MP (Q.SPEC `z` frame))) >>
         qpat_assum `!x. not_fresh_at sp x ==> lookup_var x u = _ /\ _`
           (fn frame => qpat_assum `not_fresh_at sp z`
             (strip_assume_tac o MATCH_MP (Q.SPEC `z` frame))) >> simp[]) >>
      `!i. i < t2.vs_alloca_next /\ i IN tnu.t_mem ==> i IN tn2.t_mem` by
        (gen_tac >>
         qpat_assum `!i. i IN tnu.t_mem <=> _`
           (qspec_then `i` (fn eq => pure_rewrite_tac[eq])) >>
         qpat_assum `tnp.t_mem = _` (fn eq => pure_rewrite_tac[eq]) >>
         qpat_assum `tnm.t_mem = _` (fn eq => pure_rewrite_tac[eq]) >>
         simp[NoAsms, pred_setTheory.IN_DIFF, pred_setTheory.GSPECIFICATION] >>
         qpat_assum `!i. i IN tna.t_mem <=> _`
           (qspec_then `i` (fn eq => pure_rewrite_tac[eq])) >>
         rpt strip_tac >> decide_tac) >>
      `!aid b sz. FLOOKUP t2.vs_allocas aid = SOME (b,sz) ==>
         b+sz <= t2.vs_alloca_next` by
        (qpat_assum `stmt_state_rel (storage_trace_horizon _) _ _ _ _ _ t2`
           (strip_assume_tac o PURE_REWRITE_RULE
             [exprLoweringPropsTheory.stmt_state_rel_def,
              venomMemDefsTheory.alloca_inv_def,
              venomMemDefsTheory.alloca_next_valid_def]) >>
         rpt strip_tac >> first_assum (drule_all_then ACCEPT_TAC)) >>
      `local_ptrs_rel func cenv es2.scopes t2` by
        (qpat_assum `stmt_state_rel (storage_trace_horizon _) _ _ _ _ _ t2`
           (ACCEPT_TAC o CONJUNCT1 o PURE_REWRITE_RULE
             [loweringStateRelDefsTheory.state_rel_def] o CONJUNCT1 o
             PURE_REWRITE_RULE [exprLoweringPropsTheory.stmt_state_rel_def])) >>
      `ghost_kept_at lo cenv es2 s2 G2 tn2 t2 Gu tnu` by
        (MATCH_MP_TAC (Q.INST [`Gi` |-> `G2`,`ti` |-> `tn2`,
           `G` |-> `G2`,`tn` |-> `tn2`,`s0` |-> `t2`]
           (SPEC_ALL bodyFullUnwrapSlotPostTheory.unwrap_slot_copy_ghost_kept_at)) >>
         conj_tac >- simp[bodyPtrDefsTheory.ghost_kept_at_def] >>
         conj_tac >-
           (gen_tac >> strip_tac >>
            qpat_assum `!z. not_fresh_at s2 z ==> lookup_var z u = _ /\ _`
              (qspec_then `x` mp_tac) >> simp[]) >>
         conj_tac >-
           (qx_genl_tac [`aid`,`off`,`sz`,`i`] >> strip_tac >>
            `off+sz <= t2.vs_alloca_next` by
              (qpat_assum `!aid b sz. FLOOKUP t2.vs_allocas aid = SOME (b,sz) ==> _`
                 (qspecl_then [`aid`,`off`,`sz`] MATCH_MP_TAC) >>
               first_assum ACCEPT_TAC) >>
            `i < t2.vs_alloca_next` by decide_tac >>
            qpat_assum `!i. i < t2.vs_alloca_next /\ i IN tnu.t_mem ==> _`
              (qspec_then `i` MATCH_MP_TAC) >> simp[]) >>
         conj_tac >-
           (qx_genl_tac [`name`,`b`,`sz`,`i`] >> strip_tac >>
            `i < t2.vs_alloca_next` by
              (CCONTR_TAC >>
               `t2.vs_alloca_next <= i` by decide_tac >>
               `regions_disjoint b sz i 1` by
                 (MATCH_MP_TAC (Q.SPECL [`func`,`cenv`,`es2.scopes`,`t2`,
                    `name`,`b`,`sz`,`i`,`1`]
                    localPtrsPropsTheory.local_ptrs_rel_above_frontier) >>
                  rpt conj_tac >> first_assum ACCEPT_TAC) >>
               qpat_assum `regions_disjoint b sz i 1`
                 (fn sep => qpat_assum `b <= i`
                   (fn lb => qpat_assum `i < b+sz`
                     (fn ub => POP_ASSUM_LIST (K all_tac) >>
                       MAP_EVERY mp_tac [sep,lb,ub]))) >>
               pure_rewrite_tac[loweringStateRelDefsTheory.regions_disjoint_def] >>
               decide_tac) >>
            qpat_assum `!i. i < t2.vs_alloca_next /\ i IN tnu.t_mem ==> _`
              (qspec_then `i` MATCH_MP_TAC) >> simp[]) >>
         rpt strip_tac >>
         `i < t2.vs_alloca_next` by decide_tac >>
         qpat_assum `!i. i < t2.vs_alloca_next /\ i IN tnu.t_mem ==> _`
           (qspec_then `i` MATCH_MP_TAC) >> simp[]) >>
      `!z. not_fresh_at s2 z ==> lookup_var z tp = lookup_var z t2` by
        (gen_tac >> strip_tac >>
         `not_fresh_at ca z` by
           (MATCH_MP_TAC (Q.INST [`sa` |-> `s2`,`sm` |-> `ca`,`x` |-> `z`]
              stmtFragPtrTheory.not_fresh_at_mono) >>
            conj_tac >- first_assum ACCEPT_TAC >> simp[] >> decide_tac) >>
         qpat_assum `!x. not_fresh_at s2 x ==> lookup_var x ta = _ /\ _`
           (fn frame => qpat_assum `not_fresh_at s2 z`
             (strip_assume_tac o MATCH_MP (Q.SPEC `z` frame))) >>
         qpat_assum `!x. not_fresh_at ca x ==> lookup_var x tp = _ /\ _`
           (fn frame => qpat_assum `not_fresh_at ca z`
             (strip_assume_tac o MATCH_MP (Q.SPEC `z` frame))) >> simp[]) >>
      `!aid entry. FLOOKUP t2.vs_allocas aid = SOME entry ==>
         FLOOKUP tp.vs_allocas aid = SOME entry` by
        (rpt strip_tac >> simp[] >>
         qpat_assum `!aid e. FLOOKUP t2.vs_allocas aid = SOME e ==> _`
           (qspecl_then [`aid`,`entry`] MATCH_MP_TAC) >> first_assum ACCEPT_TAC) >>
      `wb_frame cenv es2 es2 s2 t2 tp` by
        (MATCH_MP_TAC (Q.INST [`sa` |-> `s2`,`s` |-> `t2`,`z` |-> `tp`,
           `start` |-> `w2n (wi:256 word)`,`nb` |-> `96`]
           (SPEC_ALL bodyFullUnwrapSlotPostTheory.unwrap_slot_copy_wb_frame)) >>
         conj_tac >- first_assum ACCEPT_TAC >>
         conj_tac >- first_assum ACCEPT_TAC >>
         conj_tac >-
           (qx_genl_tac [`aid`,`off`,`sz`] >> strip_tac >>
            qpat_assum `!aid b len. aid < s2.cs_next_id /\
              FLOOKUP t2.vs_allocas aid = SOME (b,len) ==> _`
              (qspecl_then [`aid`,`off`,`sz`] mp_tac) >>
            (impl_tac >- simp[]) >>
            simp[NoAsms, loweringStateRelDefsTheory.regions_disjoint_def,
              boolTheory.DISJ_COMM]) >>
         conj_tac >-
           (qx_genl_tac [`name`,`b`,`len`] >> strip_tac >>
            qpat_assum `!name b len. local_region cenv es2.scopes t2 name b len ==> _`
              (qspecl_then [`name`,`b`,`len`] mp_tac) >>
            (impl_tac >- first_assum ACCEPT_TAC) >>
            simp[NoAsms, loweringStateRelDefsTheory.regions_disjoint_def,
              boolTheory.DISJ_COMM]) >>
         qx_genl_tac [`off`,`len`] >> strip_tac >>
         qpat_assum `ta.vs_memory = t2.vs_memory`
           (fn eq => pure_rewrite_tac[GSYM eq]) >>
         qpat_assum `!off len. regions_disjoint (w2n wi) 96 off len ==> _`
           (qspecl_then [`off`,`len`] MATCH_MP_TAC) >>
         simp[loweringStateRelDefsTheory.regions_disjoint_def]) >>
      `wb_frame cenv es2 es2 s2 t2 u` by
        (MATCH_MP_TAC (Q.SPECL [`cenv`,`es2`,`es2`,`s2`,`t2`,`tp`,`sp`,`u`]
           exprSimWordArgsTheory.wb_frame_readonly_tail) >>
         conj_tac >- first_assum ACCEPT_TAC >>
         conj_tac >- decide_tac >>
         conj_tac >-
           (qx_genl_tac [`z`,`oldword`] >> strip_tac >>
            qpat_assum `!x. not_fresh_at sp x ==> lookup_var x u = _ /\ _`
              (fn frame => qpat_assum `not_fresh_at sp z`
                (strip_assume_tac o MATCH_MP (Q.SPEC `z` frame))) >> simp[]) >>
         conj_tac >- first_assum ACCEPT_TAC >> first_assum ACCEPT_TAC) >>
      `!D. gas_origin_ptr_path
         (D,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
         (t2,G2,tn2) [] (OK u,Gu,tnu)` by
        (gen_tac >>
         qpat_assum `!D. gas_origin_ptr_path _ (t2,G2,tn2) [] (OK ta,Ga,tna)`
           (fn p1 => qpat_assum `!D. gas_origin_ptr_path _ (ta,Ga,tna) [] (OK tm,Gm,tnm)`
             (fn p2 => qpat_assum `!D. gas_origin_ptr_path _ (tm,Gm,tnm) [] (OK tp,Gp,tnp)`
               (fn p3 => qpat_assum `!D. gas_origin_ptr_path _ (tp,Gp,tnp) [] (OK u,Gu,tnu)`
                 (fn p4 => POP_ASSUM_LIST (K all_tac) >>
                   MAP_EVERY assume_tac (map (Q.SPEC `D`) [p1,p2,p3,p4]))))) >>
         metis_tac[fragGasOriginPtrTheory.gas_origin_ptr_path_append,
           listTheory.APPEND_NIL]) >>
      `mem_word_at (w2n wi) u.vs_memory = mem_word_at (w2n w) t2.vs_memory /\
       mem_word_at (w2n wi+32) u.vs_memory = mem_word_at (w2n w+32) t2.vs_memory` by
        (conj_tac >>
         qpat_assum `u.vs_memory = tp.vs_memory` (fn eq => pure_rewrite_tac[eq]) >>
         qpat_assum `tp.vs_memory = _` (fn eq => pure_rewrite_tac[eq]) >>
         dep_rewrite.DEP_REWRITE_TAC
           [valueEncodingPropsTheory.mstore_mem_word_at_disjoint] >>
         conj_tac >- decide_tac >> simp[]) >>
      `mem_word_at (w2n wi+64) u.vs_memory = sw` by
        (qpat_assum `u.vs_memory = tp.vs_memory` (fn eq => pure_rewrite_tac[eq]) >>
         qpat_assum `tp.vs_memory = _` (fn eq => pure_rewrite_tac[eq]) >>
         simp[NoAsms,valueEncodingPropsTheory.mstore_mem_word_at_same]) >>
      qpat_assum `ib.buf_operand = Var src`
        (fn eq => RULE_ASSUM_TAC (PURE_REWRITE_RULE [eq]) >> assume_tac eq) >>
      qpat_assum `ob.buf_operand = Var dst`
        (fn eq => RULE_ASSUM_TAC (PURE_REWRITE_RULE [eq]) >> assume_tac eq) >>
      qabbrev_tac `gv = STRING #"%" (toString sm.cs_next_var)` >>
      qabbrev_tac `cv = STRING #"%" (toString (sm.cs_next_var+1))` >>
      qabbrev_tac `gi = mk_inst sm.cs_next_id GAS [] [gv]` >>
      qabbrev_tac `ci = mk_inst (sm.cs_next_id+1) STATICCALL
        [Var gv;Lit 7w;Var src;Lit 96w;Var dst;Lit 64w] [cv]` >>
      qabbrev_tac `ai = mk_inst (sm.cs_next_id+2) ASSERT [Var cv] []` >>
      `emitted_insts sm sb = [gi;ci;ai]` by
        simp[Abbr `gi`,Abbr `ci`,Abbr `ai`,Abbr `gv`,Abbr `cv`] >>
      `~not_fresh_at sm gv /\ ~not_fresh_at sm cv` by
        (qunabbrev_tac `gv` >> qunabbrev_tac `cv` >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[loweringStateRelDefsTheory.not_fresh_at_def] >>
         metis_tac[arithmeticTheory.LESS_EQ_REFL,arithmeticTheory.LESS_EQ_ADD]) >>
      `not_fresh_at sm src` by
        (MATCH_MP_TAC (Q.INST [`sa` |-> `ca`,`sm` |-> `sm`,`x` |-> `src`]
           stmtFragPtrTheory.not_fresh_at_mono) >>
         conj_tac >- first_assum ACCEPT_TAC >> simp[] >> decide_tac) >>
      `src <> gv /\ dst <> gv /\ dst <> cv` by
        (qpat_assum `not_fresh_at sm src` (fn src_live =>
         qpat_assum `not_fresh_at sm dst` (fn dst_live =>
         qpat_assum `~not_fresh_at sm gv` (fn gas_fresh =>
         qpat_assum `~not_fresh_at sm cv` (fn call_fresh =>
           POP_ASSUM_LIST (K all_tac) >>
           MAP_EVERY assume_tac [src_live,dst_live,gas_fresh,call_fresh])))) >>
         metis_tac[]) >>
      `same_blocks sm sb` by
        (qpat_assum `(do gas <- emit_op GAS []; _ od) sm = (res,sb)`
           (fn cut => POP_ASSUM_LIST (K all_tac) >> mp_tac cut) >>
         simp[comp_bind_def,comp_ignore_bind_def,comp_return_def] >>
         rpt (pairarg_tac >> gvs[]) >> strip_tac >>
         imp_res_tac exprLoweringPropsTheory.emit_op_same_blocks >>
         imp_res_tac exprLoweringPropsTheory.emit_void_same_blocks >>
         gvs[] >> metis_tac[exprLoweringPropsTheory.same_blocks_trans]) >>
      `fn_has_code sm sb func` by
        (MATCH_MP_TAC (cj 2 fragExecTheory.fn_has_code_split) >>
         qexists `sp` >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
      `?bb. lookup_block u.vs_current_bb func.fn_blocks = SOME bb /\
         isPREFIX [gi;ci;ai] (DROP u.vs_inst_idx bb.bb_instructions)` by
        (qpat_assum `fn_has_code sm sb func` (fn code =>
         qpat_assum `same_blocks sm sb` (fn blocks =>
         qpat_assum `sb.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sb`
           (fn insts =>
         qpat_assum `emitted_insts sm sb = [gi;ci;ai]` (fn suffix =>
         qpat_assum `u.vs_current_bb = sm.cs_current_bb` (fn block =>
         qpat_assum `u.vs_inst_idx = LENGTH sm.cs_current_insts` (fn idx =>
           POP_ASSUM_LIST (K all_tac) >>
           MAP_EVERY assume_tac [code,blocks,insts,suffix,block,idx])))))) >>
         qpat_assum `fn_has_code sm sb func`
           (mp_tac o CONJUNCT2 o PURE_REWRITE_RULE [fragExecTheory.fn_has_code_def]) >>
         disch_then (qx_choose_then `suffix_bb` strip_assume_tac) >>
         qexists_tac `suffix_bb` >>
         fs[exprLoweringPropsTheory.same_blocks_def,rich_listTheory.IS_PREFIX_APPEND] >>
         simp[rich_listTheory.DROP_APPEND1] >> metis_tac[]) >>
      rename1 `isPREFIX [gi;ci;ai] (DROP u.vs_inst_idx packet_bb.bb_instructions)` >>
      qabbrev_tac `payload = \inop. do
        xp <- emit_op ADD [Var p;Lit 0w]; vx <- emit_op MLOAD [xp];
        d0 <- emit_op ADD [inop;Lit 0w]; emit_void MSTORE [d0;vx];
        yp <- emit_op ADD [Var p;Lit 32w]; vy <- emit_op MLOAD [yp];
        d1 <- emit_op ADD [inop;Lit 32w]; emit_void MSTORE [d1;vy];
        d2 <- emit_op ADD [inop;Lit 64w]; emit_void MSTORE [d2;y] od` >>
      `payload (Var src) ca = ((),sp)` by
        (simp[NoAsms,Abbr `payload`] >> first_assum ACCEPT_TAC) >>
      qabbrev_tac `buf_code = do bin <- compile_alloc_buffer 96;
        payload bin.buf_operand;
        bout <- compile_alloc_buffer 64;
        comp_return (bin.buf_operand,bout.buf_operand) od` >>
      `buf_code s2 = ((Var src,Var dst),sm)` by
        (qunabbrev_tac `buf_code` >>
         qpat_assum `compile_alloc_buffer 96 s2 = (ib,ca)` (fn input =>
         qpat_assum `compile_alloc_buffer 64 sp = (ob,sm)` (fn output =>
         qpat_assum `payload (Var src) ca = ((),sp)` (fn stores =>
         qpat_assum `ib.buf_operand = Var src` (fn ip =>
         qpat_assum `ob.buf_operand = Var dst` (fn optr =>
           POP_ASSUM_LIST (K all_tac) >>
           MAP_EVERY assume_tac [input,output,stores,ip,optr]))))) >>
         simp[comp_bind_def,comp_ignore_bind_def,comp_return_def]) >>
      `gas_shadow_compiles buf_code buf_code` by
        (qunabbrev_tac `buf_code` >> qunabbrev_tac `payload` >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[comp_ignore_bind_def,comp_bind_assoc] >>
         rpt (match_mp_tac gasShadowStateTheory.gas_shadow_compiles_bind >> conj_tac
           >- simp[gasShadowCompileContextTheory.gas_shadow_compiles_alloc_buffer,
                gasShadowStateTheory.gas_shadow_compiles_emit_op,
                gasShadowStateTheory.gas_shadow_compiles_emit_void,
                gasShadowStateTheory.gas_shadow_compiles_bind] >> gen_tac >> BETA_TAC) >>
         simp[gasShadowStateTheory.gas_shadow_compiles_return]) >>
      `?shadow_sm. buf_code shadow_s2 = ((Var src,Var dst),shadow_sm) /\
         gas_shadow_state sm shadow_sm` by
        (qpat_assum `gas_shadow_compiles buf_code buf_code`
           (mp_tac o Q.SPECL [`s2`,`shadow_s2`] o
            REWRITE_RULE [gasShadowStateTheory.gas_shadow_compiles_def]) >> simp[] >>
         Cases_on `buf_code shadow_s2` >> simp[] >> metis_tac[]) >>
      `compile_ecmul_point (Var p) y =
        (do bufs <- buf_code; gas <- emit_op GAS [];
            success <- emit_op STATICCALL
              [gas;Lit 7w;FST bufs;Lit 96w;SND bufs;Lit 64w];
            emit_void ASSERT [success]; comp_return (SND bufs) od)` by
        (simp[Abbr `buf_code`,Abbr `payload`,builtinMiscTheory.compile_ecmul_point_def,
           comp_ignore_bind_def,comp_bind_assoc] >>
         simp[comp_bind_def,comp_return_def,FUN_EQ_THM]) >>
      `?shadow_res. compile_ecmul_point (Var p) y shadow_s2 =
         (shadow_res,shadow_sb)` by
        (qpat_assum `compile_expr cenv ty (gas_shadow_expr _) shadow_sa = _`
           (fn whole =>
         qpat_assum `lower_value _ _ _ (gas_shadow_expr e1) shadow_sa = _` (fn one =>
         qpat_assum `lower_value _ _ _ (gas_shadow_expr e2) shadow_s1 = _` (fn two =>
         qpat_assum `expr_type e1 = _` (fn type1 =>
         qpat_assum `expr_type e2 = _` (fn type2 =>
           POP_ASSUM_LIST (K all_tac) >>
           MAP_EVERY assume_tac [one,two,type1,type2] >>
           mp_tac (SIMP_RULE (srw_ss())
             [gasShadowTheory.gas_shadow_expr_def,gasShadowTheory.gas_shadow_builtin_def]
             whole)))))) >>
         disch_then (mp_then Any strip_assume_tac (cj 1 compile_ec_operands)) >>
         gvs[gasShadowTheory.gas_shadow_expr_type]) >>
      `(do gas <- emit_op GAS [];
           success <- emit_op STATICCALL
             [gas;Lit 7w;Var src;Lit 96w;Var dst;Lit 64w];
           emit_void ASSERT [success]; comp_return (Var dst) od)
         shadow_sm = (shadow_res,shadow_sb)` by
        (qpat_x_assum `compile_ecmul_point (Var p) y shadow_s2 = _` mp_tac >>
         simp[comp_bind_def,comp_return_def]) >>
      qpat_assum `(do gas <- emit_op GAS []; _ od) shadow_sm = _`
        (mp_then Any strip_assume_tac exprSimPrecompilesTheory.computed_suffix_shape) >>
      qabbrev_tac `cg = SND (emit_op GAS [] sm)` >>
      `emit_op GAS [] sm = (Var gv,cg)` by
        simp[Abbr `cg`,Abbr `gv`,emitHelperTheory.emit_op_def,
          comp_bind_def,comp_ignore_bind_def,comp_return_def,
          compileEnvTheory.fresh_id_def,compileEnvTheory.fresh_var_def,
          compileEnvTheory.emit_def] >>
      `?shadow_cg. emit_op GAS [] shadow_sm = (Var gv,shadow_cg) /\
         gas_shadow_state cg shadow_cg` by
        (mp_tac (Q.SPECL [`sm`,`shadow_sm`]
           (REWRITE_RULE [gasShadowStateTheory.gas_shadow_compiles_def]
            (SIMP_RULE bool_ss [] (Q.INST [`opc` |-> `GAS`,`opc'` |-> `GAS`,
              `ops` |-> `[]`] gasShadowStateTheory.gas_shadow_compiles_emit_op)))) >>
         simp[] >> Cases_on `emit_op GAS [] shadow_sm` >> simp[] >> metis_tac[]) >>
      `!inop st. ci_mono st (SND (payload inop st))` by
        (qunabbrev_tac `payload` >> POP_ASSUM_LIST (K all_tac) >>
         rpt gen_tac >> BETA_TAC >> simp[comp_ignore_bind_def] >>
         rpt (match_mp_tac exprLoweringPropsTheory.ci_mono_bind >> conj_tac
           >- simp[exprLoweringPropsTheory.ci_mono_emit_op,
                exprLoweringPropsTheory.ci_mono_emit_void] >> rpt gen_tac >> BETA_TAC) >>
         simp[exprLoweringPropsTheory.ci_mono_emit_void]) >>
      `!st. ci_mono st (SND (buf_code st))` by
        (qunabbrev_tac `buf_code` >> gen_tac >> simp[comp_ignore_bind_def] >>
         rpt (match_mp_tac exprLoweringPropsTheory.ci_mono_bind >> conj_tac
           >- simp[exprLoweringPropsTheory.ci_mono_compile_alloc_buffer,
                exprLoweringPropsTheory.ci_mono_comp_return] >>
           rpt gen_tac >> BETA_TAC) >>
         simp[exprLoweringPropsTheory.ci_mono_comp_return]) >>
      `!gas st. ci_mono st (SND ((do
           success <- emit_op STATICCALL
             [gas;Lit 7w;Var src;Lit 96w;Var dst;Lit 64w];
           emit_void ASSERT [success]; comp_return (Var dst) od) st))` by
        (POP_ASSUM_LIST (K all_tac) >> rpt gen_tac >> simp[comp_ignore_bind_def] >>
         rpt (match_mp_tac exprLoweringPropsTheory.ci_mono_bind >> conj_tac
           >- simp[exprLoweringPropsTheory.ci_mono_emit_op,
                exprLoweringPropsTheory.ci_mono_emit_void] >> rpt gen_tac >> BETA_TAC) >>
         simp[exprLoweringPropsTheory.ci_mono_comp_return]) >>
      `((do success <- emit_op STATICCALL
           [Var gv;Lit 7w;Var src;Lit 96w;Var dst;Lit 64w];
           emit_void ASSERT [success]; comp_return (Var dst) od) cg = (Var dst,sb)) /\
       ((do success <- emit_op STATICCALL
           [Var gv;Lit 7w;Var src;Lit 96w;Var dst;Lit 64w];
           emit_void ASSERT [success]; comp_return (Var dst) od) shadow_cg =
           (Var dst,shadow_sb))` by
        (conj_tac
         >- (qpat_x_assum `(do gas <- emit_op GAS []; _ od) sm = (res,sb)` mp_tac >>
             simp[comp_bind_def]) >>
         qpat_x_assum `(do gas <- emit_op GAS []; _ od) shadow_sm = _` mp_tac >>
         simp[comp_bind_def]) >>
      `ci_mono cg sb /\ ci_mono shadow_cg shadow_sb /\
       ci_mono shadow_s2 shadow_sm` by metis_tac[pairTheory.SND] >>
      `ci_mono sm cg /\ ci_mono shadow_sm shadow_cg` by
        (mp_tac (Q.SPECL [`GAS`,`[]`,`sm`] exprLoweringPropsTheory.ci_mono_emit_op) >>
         mp_tac (Q.SPECL [`GAS`,`[]`,`shadow_sm`] exprLoweringPropsTheory.ci_mono_emit_op) >>
         simp[]) >>
      `ci_mono s2 sm` by
        (qpat_assum `!st. ci_mono st (SND (buf_code st))` (fn mono =>
         qpat_assum `buf_code s2 = ((Var src,Var dst),sm)` (fn code =>
           POP_ASSUM_LIST (K all_tac) >>
           MAP_EVERY assume_tac [Q.SPEC `s2` mono,code])) >>
         metis_tac[pairTheory.SND]) >>
      qpat_assum `lower_value _ _ _ (gas_shadow_expr e1) shadow_sa = _`
        (mp_then Any strip_assume_tac (cj 2 exprLoweringPropsTheory.compile_expr_grows)) >>
      qpat_assum `lower_value _ _ _ (gas_shadow_expr e2) shadow_s1 = _`
        (mp_then Any strip_assume_tac (cj 2 exprLoweringPropsTheory.compile_expr_grows)) >>
      `cs_extends sa sm /\ cs_extends sm cg /\ cs_extends cg sb /\
       cs_extends shadow_sa shadow_sm /\ cs_extends shadow_sm shadow_cg /\
       cs_extends shadow_cg shadow_sb` by
        (ASSUM_LIST (fn ths => let
           fun relevant th = let val head = fst (strip_comb (concl th)) in
             is_const head andalso
             (same_const head ``cs_extends`` orelse same_const head ``ci_mono``) end;
           val facts = List.filter relevant ths;
         in POP_ASSUM_LIST (K all_tac) >> MAP_EVERY assume_tac facts end) >>
         fs[exprLoweringPropsTheory.ci_mono_def] >>
         metis_tac[compileEnvTheory.cs_extends_trans]) >>
      `fn_has_code sm cg func /\ fn_has_code shadow_sm shadow_cg shadow_func` by
        (conj_tac
         >- (MATCH_MP_TAC (Q.SPECL [`sa`,`sm`,`cg`,`sb`,`func`]
               fragExecTheory.fn_has_code_mid) >> simp[]) >>
         MATCH_MP_TAC (Q.SPECL [`shadow_sa`,`shadow_sm`,`shadow_cg`,`shadow_sb`,
           `shadow_func`] fragExecTheory.fn_has_code_mid) >> simp[]) >>
      `~u.vs_halted` by simp[] >>
      drule_all (Q.INST [`s0` |-> `u`,`memory` |-> `T`]
        generatedGasOriginTheory.compile_generated_gas_origin_path) >>
      disch_then strip_assume_tac >>
      `stmt_state_rel (storage_trace_horizon es2.storage_trace)
         ctx func cenv cx es2 u` by
        (qpat_assum `!H. valid_horizon cx st0 H es2.storage_trace ==>
           stmt_state_rel H ctx func cenv cx es2 u`
           (MATCH_MP_TAC o Q.SPEC `storage_trace_horizon es2.storage_trace`) >>
         first_assum ACCEPT_TAC) >>
      `local_ptrs_rel func cenv es2.scopes u /\ alloca_inv u` by
        (qpat_assum `stmt_state_rel (storage_trace_horizon _) _ _ _ _ _ u`
           (fn ssr => let
             val cs = CONJUNCTS (PURE_REWRITE_RULE
               [exprLoweringPropsTheory.stmt_state_rel_def] ssr);
             val locals = CONJUNCT1 (PURE_REWRITE_RULE
               [loweringStateRelDefsTheory.state_rel_def] (hd cs));
           in ACCEPT_TAC (CONJ locals (List.nth (cs,1))) end)) >>
      `MEM (mk_inst sp.cs_next_id ALLOCA [Lit 64w] [dst]) (fn_insts func)` by
        (qpat_assum `Var dst = Var (STRING #"%" (toString sp.cs_next_var))` (fn name =>
         qpat_assum `MEM (mk_inst sp.cs_next_id ALLOCA [Lit 64w]
           [STRING #"%" (toString sp.cs_next_var)]) (fn_insts func)` (fn inst =>
           POP_ASSUM_LIST (K all_tac) >> MAP_EVERY assume_tac [name,inst])) >>
         metis_tac[venomStateTheory.operand_11]) >>
      `(lo <> 0 ==> !z. cenv.ce_imm_alloca = SOME (Var z) ==>
         not_fresh_at sm z)` by
        (qpat_assum `local_ptrs_reserved cenv sm`
           (mp_tac o PURE_REWRITE_RULE [loweringStateRelDefsTheory.local_ptrs_reserved_def]) >>
         metis_tac[]) >>
      `lo <= w2n wo` by
        (qpat_assum `allocas_from lo u`
           (mp_tac o PURE_REWRITE_RULE [ptrDisciplineTheory.allocas_from_def]) >>
         disch_then (qspecl_then [`sp.cs_next_id`,`w2n wo`,`64`] mp_tac) >> simp[]) >>
      `s2.cs_next_var <= sm.cs_next_var /\ s2.cs_next_id <= sm.cs_next_id /\
       s2.cs_next_id <= sp.cs_next_id /\
       w2n wi+96 <= u.vs_alloca_next /\
       t2.vs_alloca_next <= u.vs_alloca_next` by
        decide_tac >>
      `!aid b sz. aid < s2.cs_next_id /\ FLOOKUP u.vs_allocas aid = SOME (b,sz) ==>
         regions_disjoint (w2n wo) 64 b sz` by
        (rpt strip_tac >>
         `aid <> sp.cs_next_id` by decide_tac >>
         qpat_assum `alloca_inv u`
           (mp_tac o CONJUNCT1 o PURE_REWRITE_RULE [venomMemDefsTheory.alloca_inv_def]) >>
         pure_rewrite_tac[venomMemDefsTheory.allocas_non_overlapping_def] >>
         disch_then (qspecl_then [`sp.cs_next_id`,`aid`,`w2n wo`,`64`,`b`,`sz`] mp_tac) >>
         simp[loweringStateRelDefsTheory.regions_disjoint_def]) >>
      `(cenv.ce_is_ctor ==> !name tv iv off.
         FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
         FLOOKUP (case ALOOKUP es2.immutables cx.txn.target of NONE => FEMPTY
           | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (tv,iv) ==>
         regions_disjoint (w2n wo) 64 off (type_memory_size tv))` by
        (qpat_assum `stmt_state_rel (storage_trace_horizon _) _ _ _ _ _ u`
           (fn ssr => let
             val actualH = hd (snd (strip_comb (concl ssr)));
             val th = SPEC_ALL
               exprSimPrecompilesTheory.precompile_alloca_immutable_disjoint;
             fun horizon th = valOf (List.find (fn v => fst (dest_var v) = "H")
               (free_vars (concl th)));
             val typed = INST_TYPE (match_type (type_of (horizon th))
               (type_of actualH)) th;
           in MATCH_MP_TAC (Q.INST [`s` |-> `u`,
             `inst` |-> `mk_inst sp.cs_next_id ALLOCA [Lit 64w] [dst]`]
             (INST [horizon typed |-> actualH] typed)) end) >>
         rpt conj_tac
         >- first_assum ACCEPT_TAC
         >- first_assum ACCEPT_TAC
         >- simp[NoAsms,venomInstTheory.mk_inst_def]
         >- (simp[NoAsms,venomInstTheory.mk_inst_def] >> first_assum ACCEPT_TAC)) >>
      `!H. valid_horizon cx st0 H es2.storage_trace ==>
         allocas_from lo u /\
         tnu.t_stor SUBSET (DF H).d_stor u.vs_call_ctx.cc_address
           (u.vs_accounts u.vs_call_ctx.cc_address).storage /\
         tnu.t_trans SUBSET (DF H).d_trans u.vs_call_ctx.cc_address
           (u.vs_transient u.vs_call_ctx.cc_address)` by
        (rpt strip_tac >>
         qpat_assum `!H. valid_horizon cx st0 H es2.storage_trace ==>
            ghost_inv_at (DF H) lo d cenv cx es2 Gu tnu u`
           (qspec_then `H` mp_tac) >>
         (impl_tac >- first_assum ACCEPT_TAC) >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[bodyPtrDefsTheory.ghost_inv_at_def,bodyPtrDefsTheory.stor_taint_ok_at_def]) >>
      `(!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==>
         not_fresh_at sm z) /\
       (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==>
         not_fresh_at sm z)` by
        (rpt strip_tac >>
         MATCH_MP_TAC (Q.INST [`sa` |-> `sp`,`sm` |-> `sm`,`x` |-> `z`]
           stmtFragPtrTheory.not_fresh_at_mono) >>
         conj_tac >- metis_tac[] >> simp[]) >>
      qpat_assum `u.vs_memory = tp.vs_memory` kall_tac >>
      qpat_assum `tp.vs_memory = _` kall_tac >>
      qpat_assum `tm.vs_memory = _` kall_tac >>
      qpat_assum `ta.vs_memory = t2.vs_memory` kall_tac >>
      qunabbrev_tac `gi` >> qunabbrev_tac `ci` >> qunabbrev_tac `ai` >>
      qexistsl_tac [`ib`,`ob`,`ca`,`sp`,`sm`,`src`,`dst`,`wi`,`wo`,
        `sm.cs_next_id`,`gv`,`cv`,`packet_bb`,`u`,`Gu`,`tnu`] >>
      rpt (conj_tac >- first_assum ACCEPT_TAC) >>
      `96 MOD dimword (:256) = 96` by
        (irule arithmeticTheory.LESS_MOD >> first_assum ACCEPT_TAC) >>
      `64 MOD dimword (:256) = 64` by
        (irule arithmeticTheory.LESS_MOD >>
         qpat_assum `96 < dimword (:256)` mp_tac >> decide_tac) >>
      `7 MOD dimword (:256) = 7` by
        (irule arithmeticTheory.LESS_MOD >>
         qpat_assum `96 < dimword (:256)` mp_tac >> decide_tac) >>
      qpat_assum `96 MOD dimword (:256) = 96`
        (pure_rewrite_tac o single) >>
      qpat_assum `64 MOD dimword (:256) = 64`
        (pure_rewrite_tac o single) >>
      qpat_assum `7 MOD dimword (:256) = 7`
        (pure_rewrite_tac o single) >>
      rpt (conj_tac >- first_assum ACCEPT_TAC) >>
      conj_tac >-
        (qunabbrev_tac `payload` >>
         qpat_assum `_ ca = ((),sp)` (fn payload =>
         qpat_assum `ib.buf_operand = Var src` (fn operand =>
           POP_ASSUM_LIST (K all_tac) >>
           map_every assume_tac [payload,operand])) >>
         gvs[]) >>
      rpt (conj_tac >- first_assum ACCEPT_TAC) >>
      conj_tac >-
        (pure_rewrite_tac[venomStateTheory.eval_operand_def] >>
         first_assum ACCEPT_TAC) >>
      conj_tac >-
        (pure_rewrite_tac[venomStateTheory.eval_operand_def] >>
         first_assum ACCEPT_TAC) >>
      rpt (conj_tac >- first_assum ACCEPT_TAC) >>
      conj_tac >-
        (qpat_assum `isPREFIX _ (DROP u.vs_inst_idx packet_bb.bb_instructions)`
           (fn pref => POP_ASSUM_LIST (K all_tac) >> mp_tac pref) >>
         simp[NoAsms,listTheory.isPREFIX]) >>
      rpt (conj_tac >- first_assum ACCEPT_TAC) >>
      conj_tac >- (conj_tac >> first_assum ACCEPT_TAC) >>
      conj_tac >-
        (qpat_assum `eval_operand y t2 = SOME sw` (fn ev =>
         qpat_assum `mem_word_at (w2n wi + 64) u.vs_memory = sw` (fn mem =>
           POP_ASSUM_LIST (K all_tac) >> map_every assume_tac [ev,mem])) >>
         gvs[]) >>
      conj_tac >-
        (qpat_assum `!z. not_fresh_at s2 z ==> _ /\ _ /\ _` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >> simp[]) >>
      qx_gen_tac `H` >> disch_tac >>
      qpat_assum `!H. valid_horizon cx st0 H es2.storage_trace ==> ghost_inv_at _ _ _ _ _ _ _ _ _`
        (qspec_then `H` mp_tac) >>
      (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
      qpat_assum `!H. valid_horizon cx st0 H es2.storage_trace ==> stmt_state_rel H ctx func cenv cx es2 u`
        (qspec_then `H` mp_tac) >>
      (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
      qpat_assum `!H. valid_horizon cx st0 H es2.storage_trace ==> allocas_from lo u /\ _`
        (qspec_then `H` mp_tac) >>
      (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
      conj_tac >- (first_assum MATCH_ACCEPT_TAC) >>
      rpt (conj_tac >- first_assum ACCEPT_TAC) >>
      conj_tac >- simp[NoAsms] >>
      rpt conj_tac >> first_assum ACCEPT_TAC
QED
