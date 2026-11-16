Theory bodyFullBuiltinECArithSuffix
Ancestors
  bodyFullBuiltinECArithSourceMatch bodyPtrPrecompileBuiltinsArithmeticValue
  bodyMemEcArithSafe bodyPtrPrecompileBuiltinsRuntime
  exprSimPrecompiles exprSimProps exprLoweringProps exprSimWordArgs
  wordArgsPtr allocaHistoryFragment valueEncodingProofs venomCallOracleDefs
  venomExecSemantics venomInst venomState finite_map rich_list
  compileEnv vyperValue vyperTypeExprSoundness vyperState vyperInterpreter
  vyperContext fragGasOriginPtr gasOutcomeFull fragExec
  extCallOracle loweringStateRelDefs exprSimDefs
  byte entrySinkExtraction bodyBinopFragMemory
  valueEncoding valueEncodingDefs exprSimCalldataSlice exprSimMemDefs
  bodyFullBuiltinECArithOperands bodyFullBuiltinPrecompileSuffixSuccess
  bodyFullBuiltinPrecompileSuffixAbort bodyFullUnwrapRun bodyFullGhostFrame
  bodySimFull bodyFullPreds exprSimECArith gasOutcomeFullCompose
  gasShadowCompile exprSimHypsDefs exprLowering loweringPosts vyperAST list
  vyperStorageTrace vyperStorageFootprint exprSimHyps exprSimOperands exprSimSource

Theorem ec_arith_tail_full_from_staging:
  (!bt a e1 e2 cx tops ctx cenv env es ty sa vv sb shadow_sa shadow_sb
      x s1 y s2 shadow_s1 shadow_s2 res shadow_ctx func shadow_func DF lo d
      s0 st0 G0 tn0 marks1 v1 es1 t1 G1 tn1 marks2 v2 es2 t2 G2 tn2 PG.
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
        regions_disjoint (w2n wo) (w2n (64w:256 word)) off (type_memory_size tv)))) ==>
  !bt a e1 e2 cx tops ctx cenv env es ty sa vv sb shadow_sa shadow_sb
      x s1 y s2 shadow_s1 shadow_s2 res shadow_ctx func shadow_func DF lo d
      s0 st0 G0 tn0 marks1 v1 es1 t1 G1 tn1 marks2 v2 es2 t2 G2 tn2 PG.
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
  gas_outcome_full
    (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0
    (ec_source_tail cx a bt [expr_type e1;expr_type e2] [v1;v2])
    (es2,t2,G2,tn2)
    (\H rr ee G tn t. ?tv. rr = INL tv /\
      vv_post H ctx func cenv cx (Builtin a bt [e1;e2]) es sa sb s0 ee tv vv t /\
      vv_store_bound cx (expr_type (Builtin a bt [e1;e2]))
        (lowered_value_type cenv (Builtin a bt [e1;e2])) ee tv vv t /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv cx ee G tn t /\
      ptr_vv_ok cx (post_value_type cenv (Builtin a bt [e1;e2])) tv vv ee G tn t /\
      (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
        ?val. read_result cx tv ee = (INL val,ee) /\
          !rt w. evaluate_type (get_tenv cx) (post_value_type cenv (Builtin a bt [e1;e2])) = SOME rt /\
            eval_operand (vv_operand vv) t = SOME w ==>
            w2n w + type_memory_size rt <= lo /\
            (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
              val_in_memory rt val (w2n w) mem)) /\
      (!ty' op. vv = StackValue ty' op /\
        ~is_word_type (post_value_type cenv (Builtin a bt [e1;e2])) ==>
        ptr_buf_ok cenv (Builtin a bt [e1;e2]) op G t) /\
      (!ty' p. vv = LocatedValue ty' p /\ p.ptr_location = LocMemory ==>
        ptr_buf_ok cenv (Builtin a bt [e1;e2]) p.ptr_operand G t) /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G tn)
    (\H rr ee gt r. expr_exit rr r /\ halt_exit H cx ee rr r)
Proof
  disch_tac >>
  rpt gen_tac >> disch_tac >>
  first_x_assum (fn th => first_assum (strip_assume_tac o MATCH_MP th)) >>
  qpat_x_assum `!PG. ?ib ob ca cp sm src dst wi wo addr an id gv cv gi ci ai bb u Gu tnu. _`
    (qspec_then `PG` strip_assume_tac) >>
  qpat_x_assum `(bt = ECAdd \/ bt = ECMul) /\ _`
    (map_every assume_tac o CONJUNCTS) >>
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
     simp[] >> strip_tac >>
     qpat_assum `es2.storage_trace = es1.storage_trace ++ _` (fn trace_eq =>
       qpat_assum `valid_horizon cx st0 H es2.storage_trace`
         (ACCEPT_TAC o MATCH_MP valid_horizon_append o PURE_REWRITE_RULE[trace_eq]))) >>
  `!H. valid_horizon cx st0 H es1.storage_trace ==>
       valid_horizon cx st0 H es.storage_trace` by
    (rpt strip_tac >>
     qpat_assum `bind (eval_expr cx e1) _ _ = _`
       (mp_then (Pos last) mp_tac storage_trace_frame_prefix) >>
     simp[] >> strip_tac >>
     qpat_assum `es1.storage_trace = es.storage_trace ++ _` (fn trace_eq =>
       qpat_assum `valid_horizon cx st0 H es1.storage_trace`
         (ACCEPT_TAC o MATCH_MP valid_horizon_append o PURE_REWRITE_RULE[trace_eq]))) >>
  `MAP FDOM es.scopes = MAP FDOM es1.scopes` by
    (qpat_assum `bind (eval_expr cx e1) _ _ = _`
       (mp_then Any mp_tac
         (CONV_RULE (DEPTH_CONV ETA_CONV) forced_eval_expr_preserves_scopes_dom)) >> simp[]) >>
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
  suspend "operands"
QED

Resume ec_arith_tail_full_from_staging[operands]:
  `post_value_type cenv e1 = expr_type e1` by
    (irule post_value_type_ec_point >> simp[] >>
     qexistsl_tac [`cx`,`env`,`es`] >> fs[expr_body_pre_def]) >>
  `post_value_type cenv e2 = expr_type e2` by
    (Cases_on `bt = ECAdd`
     >- (irule post_value_type_ec_point >> simp[] >>
         qexistsl_tac [`cx`,`env`,`es1`] >> fs[expr_body_pre_def]) >>
     irule post_value_type_word >> fs[is_word_type_def]) >>
  qpat_assum `lower_value _ _ _ e1 _ = _`
    (mp_then Any strip_assume_tac (cj 2 compile_expr_grows)) >>
  qpat_assum `lower_value _ _ _ e2 _ = _`
    (mp_then Any strip_assume_tac (cj 2 compile_expr_grows)) >>
  `local_ptrs_reserved cenv s1 /\ local_ptrs_reserved cenv s2` by
    metis_tac[local_ptrs_reserved_next_var] >>
  `MAP FDOM es1.scopes = MAP FDOM es2.scopes` by
    (qpat_assum `bind (eval_expr cx e2) _ _ = _`
       (mp_then Any mp_tac
         (CONV_RULE (DEPTH_CONV ETA_CONV) forced_eval_expr_preserves_scopes_dom)) >> simp[]) >>
  `valid_horizon cx st0 (storage_trace_horizon es2.storage_trace) es2.storage_trace` by
    fs[storage_trace_domain_def] >>
  `valid_horizon cx st0 (storage_trace_horizon es2.storage_trace) es1.storage_trace` by
    metis_tac[] >>
  qpat_assum `!H. valid_horizon _ _ H es1.storage_trace ==> expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (qspec_then `storage_trace_horizon es2.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H es2.storage_trace ==> expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
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
  rename1 `eval_operand x t2 = SOME point_word` >>
  suspend "source"
QED

Resume ec_arith_tail_full_from_staging[source]:
  `value_has_type (ArrayTV (BaseTV (UintT 256)) (Fixed 2)) v1` by
    (`expr_body_pre cenv cx env e1
        (es with gas_obs := gas_explicit marks1 s0.vs_gas_readings ++ es1.gas_obs)` by
       simp[expr_body_pre_gas_obs] >>
     qpat_assum `expr_body_pre _ _ _ e1 (es with gas_obs := _)`
       (mp_then Any mp_tac
         (CONV_RULE (DEPTH_CONV ETA_CONV) memory_rhs_read_annotation_typed)) >>
     disch_then drule >> simp[value_runtime_typed_def, evaluate_type_def]) >>
  `value_has_type (if bt = ECAdd then ArrayTV (BaseTV (UintT 256)) (Fixed 2)
                    else BaseTV (UintT 256)) v2` by
    (`expr_body_pre cenv cx env e2
        (es1 with gas_obs := gas_explicit marks2 t1.vs_gas_readings ++ es2.gas_obs)` by
       simp[expr_body_pre_gas_obs] >>
     qpat_assum `expr_body_pre _ _ _ e2 (es1 with gas_obs := _)`
       (mp_then Any mp_tac
         (CONV_RULE (DEPTH_CONV ETA_CONV) memory_rhs_read_annotation_typed)) >>
     disch_then drule >>
     Cases_on `bt = ECAdd` >> simp[value_runtime_typed_def, evaluate_type_def]) >>
  `expr_val_rel cx (ArrayT (BaseT (UintT 256)) (Fixed 2)) v1 x t2 /\
   expr_val_rel cx (if bt = ECAdd then ArrayT (BaseT (UintT 256)) (Fixed 2)
                    else BaseT (UintT 256)) v2 y t2` by
    (qpat_assum `expr_post _ _ _ _ _ e2 _ _ _ _ _ _ _ _`
       (strip_assume_tac o PURE_REWRITE_RULE [expr_post_def]) >>
     conj_tac
     >- (qpat_assum `expr_type e1 = _` (fn ty1 =>
           qpat_assum `expr_val_rel cx (expr_type e1) v1 x t2`
             (ACCEPT_TAC o PURE_REWRITE_RULE [ty1]))) >>
     qpat_assum `post_value_type cenv e2 = expr_type e2` (fn pty =>
       qpat_assum `expr_type e2 = _` (fn ty2 =>
         qpat_assum `a = ArrayT (BaseT (UintT 256)) (Fixed 2)` (fn aty =>
           qpat_assum `expr_val_rel cx (post_value_type cenv e2) v2 y t2`
             (ACCEPT_TAC o PURE_REWRITE_RULE [pty,ty2,aty]))))) >>
  `?q. eval_operand y t2 = SOME q` by fs[expr_post_def, expr_val_rel_def] >>
  rename1 `eval_operand y t2 = SOME other_word` >>
  mp_tac (Q.INST [`t` |-> `t2`, `p` |-> `point_word`, `q` |-> `other_word`]
    ec_arith_staged_source_match) >>
  (impl_tac >- (simp[] >> rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choose_then `point_result` strip_assume_tac) >>
  `computed_precompile (venom_call_request u addr 0w wi an T)` by
    (qpat_assum `precompile_result _ _ = SOME _` mp_tac >>
     simp[NoAsms, computed_precompile_def, venom_call_request_def]) >>
  qpat_assum `_ sm = (_,sb)` (mp_then Any strip_assume_tac computed_suffix_shape) >>
  qpat_assum `emitted_insts sm sb = [mk_inst sm.cs_next_id GAS _ _;_;_]`
    (fn shape => qpat_assum `emitted_insts sm sb = [gi;ci;ai]`
      (strip_assume_tac o SRULE [shape])) >>
  `res = Var dst` by metis_tac[] >>
  suspend "runtime"
QED

Resume ec_arith_tail_full_from_staging[runtime]:
  qpat_assum `!H. valid_horizon _ _ H es2.storage_trace ==> gas_origin_ptr_path _ (t2,G2,tn2) [] (OK u,Gu,tnu) /\ _`
    (qspec_then `storage_trace_horizon es2.storage_trace` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  `es2.outcomes = SOME u.vs_outcomes` by fs[stmt_state_rel_def, state_rel_def] >>
  `?sg sc. step_inst_base gi u = OK sg /\ step_inst_base ci sg = OK sc` by
    (drule_all computed_call_prefix >>
     disch_then (qspecl_then [`64w`,`id`,`cv`]
       (strip_assume_tac o SRULE [run_inst_seq_def, AllCaseEqs()])) >>
     metis_tac[]) >>
  qabbrev_tac `Gf = step_prov PG (step_prov PG Gu gi sg) ci sc` >>
  qabbrev_tac `tnf = step_taint ci sg sc (step_taint gi u sg tnu)` >>
  Cases_on `?rx ry co rest. point_result = SOME (rx,ry) /\
    u.vs_outcomes = co::rest /\ co.co_success`
  >- (pop_assum strip_assume_tac >>
      rename1 `point_result = SOME (rx,ry)` >>
      rename1 `u.vs_outcomes = co::rest` >>
      suspend "success") >>
  `?bad. run_inst_seq [gi;ci;ai] u = Abort Revert_abort bad` by
    (Cases_on `point_result = NONE`
     >- (qpat_assum `_ sm = (_,sb)` (mp_then Any mp_tac computed_suffix_failure) >>
         disch_then (qspecl_then [`wo`,`wi`,`u`] mp_tac o SRULE []) >>
         (impl_tac >- simp[]) >>
         qpat_assum `emitted_insts sm sb = [gi;ci;ai]`
           (fn eq => PURE_REWRITE_TAC [eq]) >> simp[NoAsms]) >>
     `?px py. point_result = SOME (px,py)` by
       (Cases_on `point_result` >> simp[] >> metis_tac[pairTheory.PAIR]) >>
     `u.vs_outcomes = [] \/ ?co rest. u.vs_outcomes = co::rest /\ ~co.co_success` by
       (Cases_on `u.vs_outcomes` >> simp[] >> metis_tac[]) >>
     qpat_assum `_ sm = (_,sb)` (mp_then Any mp_tac computed_suffix_oracle_failure) >>
     disch_then (qspecl_then [`wo`,`wi`,`u`] mp_tac o SRULE []) >>
     (impl_tac >- simp[]) >>
     qpat_assum `emitted_insts sm sb = [gi;ci;ai]`
       (fn eq => PURE_REWRITE_TAC [eq]) >> simp[NoAsms]) >>
  `eval_operand (Var cv) sc = SOME 0w` by
    (qpat_assum `run_inst_seq [gi;ci;ai] u = Abort _ _` mp_tac >>
     qpat_assum `step_inst_base gi u = OK sg` mp_tac >>
     qpat_assum `step_inst_base ci sg = OK sc` mp_tac >>
     qpat_assum `ai = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     rpt strip_tac >>
     fs[run_inst_seq_def, AllCaseEqs()] >>
     gvs[] >>
     qpat_x_assum `step_inst_base (mk_inst _ ASSERT _ _) _ = Abort _ _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[NoAsms, step_inst_base_def, mk_inst_def, AllCaseEqs()] >>
     rpt strip_tac >>
     gvs[]) >>
  suspend "abort"
QED

Resume ec_arith_tail_full_from_staging[abort]:
  mp_tac (Q.INST [`s` |-> `u`, `u` |-> `sg`, `v` |-> `sc`,
    `G` |-> `Gu`, `tn` |-> `tnu`, `G2` |-> `Gf`, `tn2` |-> `tnf`,
    `rn` |-> `64w`, `trace` |-> `es2.storage_trace`,
    `explicit` |-> `gas_explicit_sites ctx shadow_ctx`]
    precompile_suffix_abort_full_family) >>
  (impl_tac
   >- (conj_tac
       >- (Cases_on `bt = ECAdd` >>
           simp[wordsTheory.dimword_def, fcpLib.INDEX_CONV ``dimindex(:256)``]) >>
       simp[wordsTheory.dimword_def, fcpLib.INDEX_CONV ``dimindex(:256)``,
         Abbr `Gf`, Abbr `tnf`])) >> strip_tac >>
  `?msg ee. ec_source_tail cx a bt [expr_type e1;expr_type e2] [v1;v2] es2 =
      (INR (Error (RuntimeError msg)),ee) /\ ee.storage_trace = es2.storage_trace` by
    (qpat_assum `(if bt = ECAdd then evaluate_ecadd _ else evaluate_ecmul _) = _` mp_tac >>
     qpat_assum `es2.outcomes = SOME u.vs_outcomes` mp_tac >>
     qpat_assum `~?rx ry co rest. point_result = SOME (rx,ry) /\ _` mp_tac >>
     qpat_assum `bt = ECAdd \/ bt = ECMul` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     Cases_on `point_result` >>
     gvs[ec_source_tail_cases, builtin_result_def, evaluate_builtin_def] >>
     Cases_on `u.vs_outcomes` >> gvs[] >>
     BasicProvers.every_case_tac >> gvs[] >> metis_tac[pairTheory.PAIR]) >>
  W (fn (_,goal) => mp_tac (Q.INST [`G'` |-> `G'`, `tn'` |-> `tn'`, `marks` |-> `[F]`,
    `r` |-> `Abort Revert_abort t`,
    `res` |-> `INR (Error (RuntimeError msg))`, `ee` |-> `ee`]
    (PART_MATCH (snd o dest_imp) gas_outcome_full_intro goal))) >>
  (impl_tac >- (conj_tac
  >- (`gas_explicit [F] t2.vs_gas_readings = []` by
        (Cases_on `t2.vs_gas_readings` >> simp[gasSummaryTheory.gas_explicit_cons]) >>
      qpat_assum `gas_explicit [F] t2.vs_gas_readings = []`
        (fn silent => PURE_REWRITE_TAC [silent, APPEND]) >>
      gen_tac >>
      qpat_assum `bt = ECAdd \/ bt = ECMul` (fn builtin =>
        qpat_assum `ec_source_tail _ _ _ _ _ es2 = _` (fn source_eval =>
          ACCEPT_TAC (Q.INST [`g` |-> `tail`]
            (MATCH_MP ec_source_tail_gas_obs (CONJ builtin source_eval)))))) >>
  conj_tac >- simp[] >>
  gen_tac >> strip_tac >>
  qpat_assum `ee.storage_trace = es2.storage_trace` (fn trace_eq =>
    qpat_assum `valid_horizon cx st0 H ee.storage_trace`
      (assume_tac o PURE_REWRITE_RULE [trace_eq])) >>
  simp[exit_result_def, expr_exit_def, halt_exit_def] >>
  qpat_assum `!H. valid_horizon _ _ H es2.storage_trace ==> gas_origin_ptr_path _ (t2,G2,tn2) [] (OK u,Gu,tnu) /\ _`
    (drule_then strip_assume_tac) >>
  qpat_assum `!H. valid_horizon _ _ H es2.storage_trace ==> gas_origin_ptr_path _ _ _ _`
    (drule_then assume_tac) >>
  qpat_assum `gas_origin_ptr_path _ (t2,G2,tn2) [] _`
    (mp_tac o MATCH_MP gas_origin_ptr_path_append) >>
  simp[] >> disch_then drule >> simp[])) >>
  disch_then ACCEPT_TAC
QED

Resume ec_arith_tail_full_from_staging[success]:
  qabbrev_tac `data = word_to_bytes (n2w rx:bytes32) T ++ word_to_bytes (n2w ry:bytes32) T` >>
  `precompile_result (venom_call_request u addr 0w wi an T).cr_target
      (venom_call_request u addr 0w wi an T).cr_data = SOME (SOME data)` by
    simp[Abbr `data`] >>
  `?q. run_inst_seq [gi;ci;ai] u = OK q` by
    (qpat_assum `_ sm = (_,sb)` (mp_then Any mp_tac computed_suffix_success) >>
     disch_then (qspecl_then [`wo`,`wi`,`u`,`data`] mp_tac o SRULE []) >>
     (impl_tac >- (simp[] >> qexistsl_tac [`co`,`rest`] >> simp[])) >>
     qpat_assum `emitted_insts sm sb = [gi;ci;ai]`
       (fn eq => PURE_REWRITE_TAC [eq]) >>
     metis_tac[]) >>
  rename1 `run_inst_seq [gi;ci;ai] u = OK qend` >>
  `addr <> 1w /\ 64 <= LENGTH data` by
    (Cases_on `bt = ECAdd` >>
     simp[Abbr `data`, LENGTH_word_to_bytes, wordsTheory.n2w_11,
       wordsTheory.dimword_def, fcpLib.INDEX_CONV ``dimindex(:256)``]) >>
  mp_tac (Q.INST [`s` |-> `u`, `u` |-> `sg`, `v` |-> `sc`, `q` |-> `qend`,
    `G` |-> `Gu`, `tn` |-> `tnu`, `G2` |-> `Gf`, `tn2` |-> `tnf`,
    `rn` |-> `64w`, `trace` |-> `es2.storage_trace`, `sf` |-> `s2`, `es` |-> `es2`,
    `explicit` |-> `gas_explicit_sites ctx shadow_ctx`]
    precompile_suffix_success_full_family) >>
  (impl_tac
   >- (conj_tac
       >- (Cases_on `bt = ECAdd` >>
           simp[wordsTheory.dimword_def, fcpLib.INDEX_CONV ``dimindex(:256)``]) >>
       simp[wordsTheory.dimword_def, fcpLib.INDEX_CONV ``dimindex(:256)``,
         Abbr `Gf`, Abbr `tnf`] >>
       gen_tac >> strip_tac >>
       qpat_assum `!H. valid_horizon _ _ H es2.storage_trace ==> gas_origin_ptr_path _ (t2,G2,tn2) [] (OK u,Gu,tnu) /\ _`
         (drule_then (strip_assume_tac o SRULE
           [wordsTheory.dimword_def, fcpLib.INDEX_CONV ``dimindex(:256)``])) >>
       rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  strip_tac >>
  rename1 `ec_tail_end = qend with vs_inst_idx := u.vs_inst_idx + 3` >>
  rename1 `Gout = Gf` >> rename1 `tnout = tnf` >>
  qabbrev_tac `ee = es2 with outcomes := SOME (DROP 1 u.vs_outcomes)` >>
  `ec_source_tail cx a bt [expr_type e1;expr_type e2] [v1;v2] es2 =
    (INL (Value (mk_ec_result (rx,ry))),ee)` by
    (simp[NoAsms, Abbr `ee`] >>
     qpat_assum `(if bt = ECAdd then evaluate_ecadd _ else evaluate_ecmul _) = _` mp_tac >>
     qpat_assum `point_result = SOME (rx,ry)` mp_tac >>
     qpat_assum `u.vs_outcomes = co::rest` mp_tac >>
     qpat_assum `co.co_success` mp_tac >>
     qpat_assum `es2.outcomes = SOME u.vs_outcomes` mp_tac >>
     qpat_assum `bt = ECAdd \/ bt = ECMul` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
     gvs[ec_source_tail_cases, builtin_result_def, evaluate_builtin_def]) >>
  suspend "success_post"
QED

Resume ec_arith_tail_full_from_staging[success_post]:
  rename1 `compile_alloc_buffer 64 out_alloc = (ob,sm)` >>
  `sm.cs_next_id = out_alloc.cs_next_id + 1` by
    (qpat_assum `compile_alloc_buffer 64 out_alloc = (ob,sm)`
       (mp_tac o AP_TERM ``\r:buffer # compile_state. (SND r).cs_next_id``) >>
     simp[NoAsms, contextTheory.compile_alloc_buffer_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def, emitHelperTheory.emit_op_def,
       fresh_id_def, fresh_var_def, emit_def]) >>
  `sb.cs_current_bb = sm.cs_current_bb` by
    (qpat_assum `_ sm = (_,sb)`
       (mp_tac o AP_TERM ``\r:operand # compile_state. (SND r).cs_current_bb``) >>
     simp[NoAsms, comp_bind_def, comp_ignore_bind_def, comp_return_def,
       emitHelperTheory.emit_op_def, emitHelperTheory.emit_void_def,
       fresh_id_def, fresh_var_def, emit_def]) >>
  `~qend.vs_halted /\ qend.vs_current_bb = u.vs_current_bb` by
    (qspecl_then [`[gi;ci;ai]`,`u`,`qend`] mp_tac run_inst_seq_preserves_entry_control >>
     simp[mk_inst_def, is_terminator_def]) >>
  W (fn (_,goal) => mp_tac (Q.INST [`G'` |-> `Gout`, `tn'` |-> `tnout`, `marks` |-> `[F]`,
    `r` |-> `(OK ec_tail_end : exec_result)`,
    `res` |-> `(INL (Value (mk_ec_result (rx,ry))) : eval_result + exception)`,
    `ee` |-> `ee`] (PART_MATCH (snd o dest_imp) gas_outcome_full_intro goal))) >>
  (impl_tac >- (conj_tac
  >- (`gas_explicit [F] t2.vs_gas_readings = []` by
        (Cases_on `t2.vs_gas_readings` >> simp[gasSummaryTheory.gas_explicit_cons]) >>
      qpat_assum `gas_explicit [F] t2.vs_gas_readings = []`
        (fn silent => PURE_REWRITE_TAC [silent, APPEND]) >>
      gen_tac >>
      qpat_assum `bt = ECAdd \/ bt = ECMul` (fn builtin =>
        qpat_assum `ec_source_tail _ _ _ _ _ es2 = _` (fn source_eval =>
          ACCEPT_TAC (Q.INST [`g` |-> `tail`]
            (MATCH_MP ec_source_tail_gas_obs (CONJ builtin source_eval)))))) >>
  conj_tac >- simp[Abbr `ee`] >>
  `ee.storage_trace = es2.storage_trace /\ (ee with gas_obs := []) = ee` by
    simp[Abbr `ee`, evaluation_state_component_equality] >>
  gen_tac >>
  qpat_assum `ee.storage_trace = es2.storage_trace`
    (fn trace_eq => PURE_REWRITE_TAC [trace_eq]) >> strip_tac >>
  qpat_assum `!H. valid_horizon cx st0 H es2.storage_trace ==>
      valid_horizon cx st0 H es1.storage_trace` (fn prefix =>
    qpat_assum `valid_horizon cx st0 H es2.storage_trace`
      (assume_tac o MATCH_MP (Q.SPEC `H` prefix))) >>
  qpat_assum `!H. valid_horizon cx st0 H es1.storage_trace ==>
      valid_horizon cx st0 H es.storage_trace` (fn prefix =>
    qpat_assum `valid_horizon cx st0 H es1.storage_trace`
      (assume_tac o MATCH_MP (Q.SPEC `H` prefix))) >>
  qpat_assum `!H. valid_horizon _ _ H es.storage_trace ==> _`
    (drule_then (strip_assume_tac o SRULE
      [wordsTheory.dimword_def, fcpLib.INDEX_CONV ``dimindex(:256)``])) >>
  qpat_assum `!H. valid_horizon _ _ H es1.storage_trace ==> expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (drule_then (strip_assume_tac o SRULE
      [wordsTheory.dimword_def, fcpLib.INDEX_CONV ``dimindex(:256)``])) >>
  qpat_assum `!H. valid_horizon _ _ H es2.storage_trace ==> expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (drule_then (strip_assume_tac o SRULE
      [wordsTheory.dimword_def, fcpLib.INDEX_CONV ``dimindex(:256)``])) >>
  qpat_assum `!H. valid_horizon _ _ H es2.storage_trace ==> gas_origin_ptr_path _ (t2,G2,tn2) [] (OK u,Gu,tnu) /\ _`
    (drule_then (strip_assume_tac o SRULE
      [wordsTheory.dimword_def, fcpLib.INDEX_CONV ``dimindex(:256)``])) >>
  qpat_assum `!H. valid_horizon _ _ H es2.storage_trace ==> gas_origin_ptr_path _ _ [F] _ /\ _`
    (drule_then (strip_assume_tac o SRULE
      [wordsTheory.dimword_def, fcpLib.INDEX_CONV ``dimindex(:256)``])) >>
  `gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     (t2,G2,tn2) [F] (OK ec_tail_end,Gout,tnout)` by
    (qpat_assum `gas_origin_ptr_path _ (t2,G2,tn2) [] _`
       (mp_tac o MATCH_MP gas_origin_ptr_path_append) >>
     simp[NoAsms] >> disch_then drule >> simp[NoAsms]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qpat_assum `(ee with gas_obs := []) = ee`
    (fn source_end => PURE_REWRITE_TAC [source_end]) >>
  disj1_tac >> qexists_tac `ec_tail_end` >> simp[NoAsms] >>
  qpat_assum `expr_post H ctx func cenv cx e1 es sa s1 s0 es1 v1 x t1`
    (fn post => assume_tac (MATCH_MP (SPEC_ALL expr_post_frame) post) >>
      strip_assume_tac (PURE_REWRITE_RULE [expr_post_def] post)) >>
  qpat_assum `expr_post H ctx func cenv cx e2 es1 s1 s2 t1 es2 v2 y t2`
    (fn post => assume_tac (MATCH_MP (SPEC_ALL expr_post_frame) post) >>
      strip_assume_tac (PURE_REWRITE_RULE [expr_post_def] post)) >>
  `wb_frame cenv es2 ee s2 t2 ec_tail_end` by
    (qspecl_then [`func`,`cenv`,`cx`,`es2`,`t2`,`s2`,`es2`,`ee`,
       `s2`,`u`,`ec_tail_end`,`ctx`] mp_tac (INST_TYPE [alpha |-> ``:256``] wb_frame_trans) >>
     simp[Abbr `ee`]) >>
  `!n b sz. local_region cenv es2.scopes t2 n b sz <=>
             local_region cenv es2.scopes u n b sz` by
    (mp_tac (Q.INST [`es` |-> `es2`, `s0` |-> `t2`, `sa` |-> `s2`,
       `es1` |-> `es2`, `s1` |-> `u`, `es'` |-> `es2`]
       (INST_TYPE [alpha |-> ``:256``] wb_frame_local_regions)) >>
     simp[]) >>
  `!n b sz. local_region cenv es2.scopes u n b sz <=>
             local_region cenv ee.scopes ec_tail_end n b sz` by
    (mp_tac (Q.INST [`es` |-> `es2`, `s0` |-> `u`, `sa` |-> `s2`,
       `es1` |-> `ee`, `s1` |-> `ec_tail_end`, `es'` |-> `ee`]
       (INST_TYPE [alpha |-> ``:256``] wb_frame_local_regions)) >>
     simp[Abbr `ee`]) >>
  `!n b sz. local_region cenv es2.scopes t2 n b sz ==>
     regions_disjoint (w2n wo) 64 b sz` by
    (rpt strip_tac >>
     qpat_assum `!name b sz. local_region cenv es2.scopes u name b sz ==> _`
       (irule o SRULE [wordsTheory.dimword_def]) >> metis_tac[]) >>
  `!off len. regions_disjoint off len (w2n wo) 64 ==>
     mem_bytes_at off len ec_tail_end.vs_memory = mem_bytes_at off len u.vs_memory` by
    (rpt strip_tac >> qpat_assum `ec_tail_end.vs_memory = _`
       (fn eq => PURE_REWRITE_TAC [eq]) >>
     irule write_memory_take_exterior >> simp[wordsTheory.dimword_def]) >>
  `pure_frame cenv func es2 s2 t2 ec_tail_end` by
    (qspecl_then [`cenv`,`func`,`es2`,`s2`,`t2`,`u`,`ec_tail_end`,
       `mk_inst out_alloc.cs_next_id ALLOCA [Lit 64w] [dst]`,`w2n wo`,`64`]
       mp_tac pure_frame_buffer_tail >>
     (impl_tac >-
       (qpat_assum `MEM (mk_inst out_alloc.cs_next_id ALLOCA [Lit 64w] [dst]) _`
          (assume_tac o SRULE [mk_inst_def]) >>
        qpat_assum `ec_tail_end.vs_allocas = u.vs_allocas`
          (fn allocas => simp[NoAsms, allocas, mk_inst_def]) >>
        rpt conj_tac >> first_assum ACCEPT_TAC)) >> disch_then ACCEPT_TAC) >>
  `mem_bytes_at (w2n wo) 64 ec_tail_end.vs_memory =
     word_to_bytes (n2w rx:bytes32) T ++ word_to_bytes (n2w ry:bytes32) T` by
    (qpat_assum `ec_tail_end.vs_memory = _` (fn eq => PURE_REWRITE_TAC [eq]) >>
     qspecl_then [`w2n wo`,`data`,`u`] mp_tac write_memory_mem_bytes_at_same >>
     simp[NoAsms, Abbr `data`, wordsTheory.dimword_def, LENGTH_word_to_bytes,
       fcpLib.INDEX_CONV ``dimindex(:256)``, TAKE_LENGTH_TOO_LONG]) >>
  `storage_well_formed_on cx ee (FST H)` by
    (mp_tac (Q.INST [`st'` |-> `ee`, `st` |-> `es2`,
       `regions` |-> `FST (H : (bool # bytes32 # type_value) list # num list)`]
       (INST_TYPE [alpha |-> ``:256``] storage_well_formed_on_backends)) >>
     (impl_tac >- simp[Abbr `ee`]) >>
     disch_then (fn eq => qpat_assum `storage_well_formed_on cx es2 (FST H)`
       (ACCEPT_TAC o EQ_MP (GSYM eq)))) >>
  `!name b sz. local_region cenv ee.scopes ec_tail_end name b sz ==>
     regions_disjoint (w2n wo) 64 b sz` by
    (rpt strip_tac >>
     qpat_assum `!name b sz. local_region cenv es2.scopes u name b sz ==> _`
       (irule o SRULE [wordsTheory.dimword_def]) >> metis_tac[]) >>
  `!c. bt <> Concat c` by
    (qpat_assum `bt = ECAdd \/ bt = ECMul` DISJ_CASES_TAC >> simp[]) >>
  `FLOOKUP ec_tail_end.vs_allocas out_alloc.cs_next_id = SOME (w2n wo,64)` by
    (qpat_assum `ec_tail_end.vs_allocas = u.vs_allocas`
       (fn allocas => PURE_REWRITE_TAC [allocas]) >> first_assum ACCEPT_TAC) >>
  `out_alloc.cs_next_id < sb.cs_next_id` by
    (qpat_assum `sm.cs_next_id = out_alloc.cs_next_id + 1` mp_tac >>
     qpat_assum `sb.cs_next_id = sm.cs_next_id + 3` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
  mp_tac (Q.INST [`fn` |-> `func`, `es` |-> `es2`, `es'` |-> `ee`,
    `sa` |-> `s2`, `s0` |-> `t2`, `t` |-> `ec_tail_end`, `G` |-> `Gout`,
    `tn` |-> `tnout`, `w` |-> `wo`, `x` |-> `rx`, `y` |-> `ry`,
    `aid` |-> `out_alloc.cs_next_id`, `args` |-> `[e1;e2]`]
    (INST_TYPE [alpha |-> ``:256``] ec_builtin_result_posts)) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  suspend "success_frames")) >>
  disch_then ACCEPT_TAC
QED

Resume ec_arith_tail_full_from_staging[success_frames]:
  `vv = LocatedValue a (mk_ptr (Var dst) LocMemory)` by
    simp[as_ptr_val_def] >>
  `post_value_type cenv (Builtin a bt [e1;e2]) = a /\
   lowered_value_type cenv (Builtin a bt [e1;e2]) = a` by
    (qpat_assum `bt = ECAdd \/ bt = ECMul` DISJ_CASES_TAC >>
     simp[post_value_type_def, lowered_value_type_def, expr_type_def]) >>
  `(~expr_has_effect (Builtin a bt [e1;e2]) ==>
      pure_frame cenv func es sa s0 t1) /\
   (~expr_has_effect (Builtin a bt [e1;e2]) ==>
      pure_frame cenv func es1 s1 t1 t2)` by
    (conj_tac >> simp[] >> strip_tac >> first_assum irule >>
     first_assum ACCEPT_TAC) >>
  `vv_post H ctx func cenv cx (Builtin a bt [e1;e2])
     es2 s2 sb t2 ee (Value (mk_ec_result (rx,ry))) vv ec_tail_end` by
    (qpat_assum `vv_post H _ _ _ _ _ es2 s2 sb t2 ee _ _ ec_tail_end` mp_tac >>
     qpat_assum `a = ArrayT (BaseT (UintT 256)) (Fixed 2)` (fn annotation =>
       qpat_assum `vv = LocatedValue a (mk_ptr (Var dst) LocMemory)`
         (fn value => simp[NoAsms, annotation, value, as_ptr_val_def]))) >>
  `vv_post H ctx func cenv cx (Builtin a bt [e1;e2])
     es1 s1 sb t1 ee (Value (mk_ec_result (rx,ry))) vv ec_tail_end` by
    (mp_tac (Q.INST [`es` |-> `es1`, `sa` |-> `s1`, `s0` |-> `t1`,
       `es1` |-> `es2`, `sm` |-> `s2`, `t` |-> `t2`, `es2` |-> `ee`,
       `tv` |-> `Value (mk_ec_result (rx,ry))`, `vv` |-> `vv`, `u` |-> `ec_tail_end`,
       `e` |-> `Builtin a bt [e1;e2]`]
       (INST_TYPE [alpha |-> ``:256``] vv_post_prefix_frame)) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
     disch_then ACCEPT_TAC) >>
  `vv_post H ctx func cenv cx (Builtin a bt [e1;e2])
     es sa sb s0 ee (Value (mk_ec_result (rx,ry))) vv ec_tail_end` by
    (mp_tac (Q.INST [`es1` |-> `es1`, `sm` |-> `s1`, `t` |-> `t1`,
       `es2` |-> `ee`, `tv` |-> `Value (mk_ec_result (rx,ry))`,
       `u` |-> `ec_tail_end`, `e` |-> `Builtin a bt [e1;e2]`]
       (INST_TYPE [alpha |-> ``:256``] vv_post_prefix_frame)) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
     disch_then ACCEPT_TAC) >>
  `ghost_kept_at lo cenv es2 s2 G2 tn2 t2 Gout tnout` by
    (qspecl_then [`lo`,`cenv`,`es2`,`s2`,`G2`,`tn2`,`t2`,`Gu`,`tnu`,
       `es2`,`s2`,`Gout`,`tnout`,`u`,`H`,`ctx`,`func`,`cx`,`es2`]
       mp_tac (INST_TYPE [alpha |-> ``:num # num``, beta |-> ``:256``]
         ghost_kept_at_wb_trans) >>
     (impl_tac >- (simp[NoAsms] >> rpt conj_tac >> first_assum ACCEPT_TAC)) >>
     disch_then ACCEPT_TAC) >>
  `ghost_kept_at lo cenv es1 s1 G1 tn1 t1 Gout tnout` by
    (qspecl_then [`lo`,`cenv`,`es1`,`s1`,`G1`,`tn1`,`t1`,`G2`,`tn2`,
       `es2`,`s2`,`Gout`,`tnout`,`t2`,`H`,`ctx`,`func`,`cx`,`es2`]
       mp_tac (INST_TYPE [alpha |-> ``:num # num``, beta |-> ``:256``]
         ghost_kept_at_wb_trans) >>
     (impl_tac >- (simp[NoAsms] >> rpt conj_tac >> first_assum ACCEPT_TAC)) >>
     disch_then ACCEPT_TAC) >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 Gout tnout` by
    (qspecl_then [`lo`,`cenv`,`es`,`sa`,`G0`,`tn0`,`s0`,`G1`,`tn1`,
       `es1`,`s1`,`Gout`,`tnout`,`t1`,`H`,`ctx`,`func`,`cx`,`es1`]
       mp_tac (INST_TYPE [alpha |-> ``:num # num``, beta |-> ``:256``]
         ghost_kept_at_wb_trans) >>
     (impl_tac >- (simp[NoAsms] >> rpt conj_tac >> first_assum ACCEPT_TAC)) >>
     disch_then ACCEPT_TAC) >>
  `qend.vs_allocas = u.vs_allocas` by
    (qpat_assum `ec_tail_end = _` (fn finish_eq =>
       qpat_assum `ec_tail_end.vs_allocas = u.vs_allocas`
         (mp_tac o PURE_REWRITE_RULE [finish_eq])) >> simp[NoAsms]) >>
  `?code_tail. DROP u.vs_inst_idx bb.bb_instructions = [gi;ci;ai] ++ code_tail` by
    (qpat_assum `isPREFIX [gi;ci;ai] (DROP u.vs_inst_idx bb.bb_instructions)`
       (ACCEPT_TAC o PURE_REWRITE_RULE [IS_PREFIX_APPEND])) >>
  `alloca_history func ec_tail_end` by
    (qspecl_then [`func`,`u`,`qend`,`bb`,`[gi;ci;ai]`,`code_tail`]
       mp_tac alloca_history_no_alloca_slice >> simp[mk_inst_def]) >>
  `s0.vs_alloca_next <= ec_tail_end.vs_alloca_next` by
    (qpat_assum `s0.vs_alloca_next <= t1.vs_alloca_next` mp_tac >>
     qpat_assum `t1.vs_alloca_next <= t2.vs_alloca_next` mp_tac >>
     qpat_assum `t2.vs_alloca_next <= u.vs_alloca_next` mp_tac >>
     qpat_assum `ec_tail_end.vs_alloca_next = u.vs_alloca_next`
       (fn frontier => PURE_REWRITE_TAC [frontier]) >>
     POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
  `vv_post H ctx func cenv cx (Builtin a bt [e1;e2]) es sa sb s0 ee
     (Value (mk_ec_result (rx,ry)))
     (LocatedValue a (mk_ptr (Var dst) LocMemory)) ec_tail_end` by
    (qpat_assum `vv_post H _ _ _ _ _ es sa sb s0 ee _ vv ec_tail_end`
       (fn post => qpat_assum `vv = LocatedValue a (mk_ptr (Var dst) LocMemory)`
         (ACCEPT_TAC o (fn value => PURE_REWRITE_RULE [value] post)))) >>
  `evaluate_type (get_tenv cx) a =
     SOME (ArrayTV (BaseTV (UintT 256)) (Fixed 2))` by
    (qpat_assum `a = ArrayT (BaseT (UintT 256)) (Fixed 2)`
       (fn annotation => simp[NoAsms, annotation, evaluate_type_def, type_slot_size_def,
         wordsTheory.dimword_def, fcpLib.INDEX_CONV ``dimindex(:256)``])) >>
  `eval_operand (mk_ptr (Var dst) LocMemory).ptr_operand ec_tail_end = SOME wo` by
    (simp[NoAsms, contextTheory.mk_ptr_def] >> first_assum ACCEPT_TAC) >>
  `w2n wo + 64 <= ec_tail_end.vs_alloca_next` by
    (qpat_assum `ec_tail_end.vs_alloca_next = u.vs_alloca_next`
       (fn frontier => PURE_REWRITE_TAC [frontier]) >>
     qpat_assum `w2n wo + w2n (64w:256 word) <= u.vs_alloca_next`
       (ACCEPT_TAC o SRULE [wordsTheory.dimword_def,
         fcpLib.INDEX_CONV ``dimindex(:256)``])) >>
  `vv_store_bound cx a a ee (Value (mk_ec_result (rx,ry))) vv ec_tail_end` by
    (mp_tac (Q.INST [`e` |-> `Builtin a bt [e1;e2]`, `es'` |-> `ee`,
       `tv` |-> `Value (mk_ec_result (rx,ry))`, `vt` |-> `a`,
       `p` |-> `mk_ptr (Var dst) LocMemory`, `t` |-> `ec_tail_end`,
       `ftv` |-> `ArrayTV (BaseTV (UintT 256)) (Fixed 2)`, `fw` |-> `wo`]
       (INST_TYPE [alpha |-> ``:256``] vv_store_bound_capacity)) >>
     (impl_tac >- (simp[NoAsms, expr_type_def, type_memory_size_def,
       type_slot_size_def] >> rpt conj_tac >> first_assum ACCEPT_TAC)) >>
     disch_then (fn bound =>
       qpat_assum `vv = LocatedValue a (mk_ptr (Var dst) LocMemory)`
         (fn value => ACCEPT_TAC (PURE_REWRITE_RULE
           [expr_type_def, GSYM value] bound)))) >>
  simp[Abbr `ee`, contextTheory.vv_location_def, contextTheory.mk_ptr_def,
    expr_type_def, as_ptr_val_def] >>
  qpat_assum `vv_store_bound cx a a _ _ vv ec_tail_end` mp_tac >>
  qpat_assum `ptr_vv_ok cx _ _ _ _ Gout tnout ec_tail_end` mp_tac >>
  qpat_assum `ptr_buf_ok cenv (Builtin _ bt [e1;e2]) (Var dst) Gout ec_tail_end` mp_tac >>
  qpat_assum `a = ArrayT (BaseT (UintT 256)) (Fixed 2)` mp_tac >>
  qpat_assum `vv = LocatedValue a (mk_ptr (Var dst) LocMemory)` mp_tac >>
  qpat_assum `ec_tail_end = _` mp_tac >>
  qpat_assum `u.vs_inst_idx = LENGTH sm.cs_current_insts` mp_tac >>
  qpat_assum `u.vs_outcomes = co::rest` mp_tac >>
  qpat_assum `Gout = Gf` mp_tac >> qpat_assum `tnout = tnf` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >>
  gvs[as_ptr_val_def, contextTheory.mk_ptr_def]
QED

Finalise ec_arith_tail_full_from_staging
