(* Discharge the point-copy contract of the retained ECAdd layout proof. *)
Theory bodyFullBuiltinECAddStaging
Ancestors bodyFullBuiltinECAddStagingCore bodyFullBuiltinECArithPointCopy
  compileEnv

Theorem ecadd_staging_full:
  bt = ECAdd /\
  a = ArrayT (BaseT (UintT 256)) (Fixed 2) /\
  expr_type e1 = ArrayT (BaseT (UintT 256)) (Fixed 2) /\
  expr_type e2 = (if bt = ECAdd then a else BaseT (UintT 256)) /\
  body_exprs_full_ok cx [e1;e2] /\ body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env (Builtin a bt [e1;e2]) es /\
  compile_expr cenv ty (Builtin a bt [e1;e2]) sa = (vv,sb) /\
  compile_expr cenv ty (gas_shadow_expr (Builtin a bt [e1;e2])) shadow_sa = (vv,shadow_sb) /\
  lower_value compile_expr cenv (expr_type e1) e1 sa = (x,s1) /\
  lower_value compile_expr cenv (expr_type e2) e2 s1 = (y,s2) /\
  lower_value compile_expr cenv (expr_type e1) (gas_shadow_expr e1) shadow_sa = (x,shadow_s1) /\
  lower_value compile_expr cenv (expr_type e2) (gas_shadow_expr e2) shadow_s1 = (y,shadow_s2) /\
  (if bt = ECAdd then compile_ecadd_points x y s2 else compile_ecmul_point x y s2) = (res,sb) /\
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
    stmt_state_rel H ctx func cenv cx es s0 /\ storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!tail. bind (eval_expr cx e1) (read_result cx)
    (es with gas_obs := gas_explicit marks1 s0.vs_gas_readings ++ tail) =
    (INL v1,es1 with gas_obs := tail)) /\
  storage_trace_domain cx st0 es1.storage_trace /\ ~t1.vs_halted /\ es1.gas_obs = [] /\
  (!H. valid_horizon cx st0 H es1.storage_trace ==>
    expr_post H ctx func cenv cx e1 es sa s1 s0 es1 v1 x t1 /\
    expr_store_bound cx (post_value_type cenv e1) v1 x t1 /\
    t1.vs_current_bb = s1.cs_current_bb /\ t1.vs_inst_idx = LENGTH s1.cs_current_insts /\
    alloca_history func t1 /\ s0.vs_alloca_next <= t1.vs_alloca_next /\
    ghost_inv_at (DF H) lo d cenv cx es1 G1 tn1 t1 /\
    ptr_val_ok cx (post_value_type cenv e1) v1 x G1 tn1 t1 /\
    (~is_word_type (post_value_type cenv e1) ==> ptr_buf_ok cenv e1 x G1 t1) /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 G1 tn1) /\
  (!tail. bind (eval_expr cx e2) (read_result cx)
    (es1 with gas_obs := gas_explicit marks2 t1.vs_gas_readings ++ tail) =
    (INL v2,es2 with gas_obs := tail)) /\
  storage_trace_domain cx st0 es2.storage_trace /\ ~t2.vs_halted /\ es2.gas_obs = [] /\
  (!H. valid_horizon cx st0 H es2.storage_trace ==>
    expr_post H ctx func cenv cx e2 es1 s1 s2 t1 es2 v2 y t2 /\
    expr_store_bound cx (post_value_type cenv e2) v2 y t2 /\
    t2.vs_current_bb = s2.cs_current_bb /\ t2.vs_inst_idx = LENGTH s2.cs_current_insts /\
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
      (do xp <- emit_op ADD [x; Lit 0w]; vx <- emit_op MLOAD [xp];
          dst0 <- emit_op ADD [ib.buf_operand; Lit 0w]; emit_void MSTORE [dst0; vx];
          yp <- emit_op ADD [x; Lit 32w]; vy <- emit_op MLOAD [yp];
          dst1 <- emit_op ADD [ib.buf_operand; Lit 32w]; emit_void MSTORE [dst1; vy];
          xp2 <- emit_op ADD [y; Lit 0w]; vx2 <- emit_op MLOAD [xp2];
          dst2 <- emit_op ADD [ib.buf_operand; Lit 64w]; emit_void MSTORE [dst2; vx2];
          yp2 <- emit_op ADD [y; Lit 32w]; vy2 <- emit_op MLOAD [yp2];
          dst3 <- emit_op ADD [ib.buf_operand; Lit 96w]; emit_void MSTORE [dst3; vy2] od) ca = ((),cp)
     else
      (do xp <- emit_op ADD [x; Lit 0w]; vx <- emit_op MLOAD [xp];
          dst0 <- emit_op ADD [ib.buf_operand; Lit 0w]; emit_void MSTORE [dst0; vx];
          yp <- emit_op ADD [x; Lit 32w]; vy <- emit_op MLOAD [yp];
          dst1 <- emit_op ADD [ib.buf_operand; Lit 32w]; emit_void MSTORE [dst1; vy];
          dst2 <- emit_op ADD [ib.buf_operand; Lit 64w]; emit_void MSTORE [dst2; y] od) ca = ((),cp)) /\
    (do gas <- emit_op GAS [];
        success <- emit_op STATICCALL [gas; Lit addr; Var src; Lit an; Var dst; Lit 64w];
        emit_void ASSERT [success]; return (Var dst) od) sm = (res,sb) /\
    gi = mk_inst id GAS [] [gv] /\
    ci = mk_inst (id+1) STATICCALL [Var gv; Lit addr; Var src; Lit an; Var dst; Lit 64w] [cv] /\
    ai = mk_inst (id+2) ASSERT [Var cv] [] /\ emitted_insts sm sb = [gi;ci;ai] /\
    emitted_insts s2 sb = emitted_insts s2 sm ++ emitted_insts sm sb /\
    eval_operand (Var src) u = SOME wi /\ eval_operand (Var dst) u = SOME wo /\
    src <> gv /\ dst <> gv /\ dst <> cv /\
    not_fresh_at sm src /\ not_fresh_at sm dst /\ ~not_fresh_at sm gv /\ ~not_fresh_at sm cv /\
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
    u.vs_current_bb = sm.cs_current_bb /\ u.vs_inst_idx = LENGTH sm.cs_current_insts /\
    alloca_history func u /\ t2.vs_alloca_next <= u.vs_alloca_next /\
    pure_frame cenv func es2 s2 t2 u /\
    FLOOKUP u.vs_allocas cp.cs_next_id = SOME (w2n wo,64) /\ s2.cs_next_id <= cp.cs_next_id /\
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
      ghost_kept_at lo cenv es2 s2 G2 tn2 t2 Gu tnu /\ wb_frame cenv es2 es2 s2 t2 u /\
      ghost_inv_at (DF H) lo d cenv cx es2 Gu tnu u /\ stmt_state_rel H ctx func cenv cx es2 u /\
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
  match_mp_tac ecadd_staging_full_from_transfers >>
  rpt gen_tac >> MATCH_ACCEPT_TAC ec_point_copy_origin_ptr_path
QED
