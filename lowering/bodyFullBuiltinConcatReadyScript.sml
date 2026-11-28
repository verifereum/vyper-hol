(* Shared entry invariant for the full and request-prefix Concat loops. *)
Theory bodyFullBuiltinConcatReady
Ancestors bodyFullPreds bodySimFull gasShadowState gasShadowUnit
  bodyFullShadowBodyInv[qualified]
  bodyInvSplit[qualified]
  bodyFullPredsMods[qualified]
  bodyPtrDefs exprSimHypsDefs exprLowering compileEnv loweringStateRelDefs
  loweringPosts unitTransformDefs vyperStorageTrace vyperStorageFootprint
  vyperState venomState words list finite_map pred_set

Definition concat_loop_ready_def:
  concat_loop_ready args P k DF lo d ctx shadow_ctx (PG : (num # num) option list)
    mods exps tops func shadow_func cenv cx env st0 es sa sb shadow_sa shadow_sb
    s0 G0 tn0 dv ov ow binst B bsz oinst <=>
    compile_concat compile_expr cenv args (Var dv)
      (MAP (\e.
         if is_bytestring_type (expr_type e) then (T,0:num)
         else case expr_type e of BaseT (BytesT (Fixed m)) => (F,m)
                       | _ => (F,32:num)) args) (Var ov) sa = ((),sb) /\
    compile_concat compile_expr (gas_shadow_env T cenv) (MAP gas_shadow_expr args) (Var dv)
      (MAP (\e.
         if is_bytestring_type (expr_type e) then (T,0:num)
         else case expr_type e of BaseT (BytesT (Fixed m)) => (F,m)
                       | _ => (F,32:num)) args) (Var ov) shadow_sa = ((),shadow_sb) /\
    gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
    gas_shadow_context ctx shadow_ctx /\ gas_shadow_function func shadow_func /\
    ctx_inst_ids_distinct ctx /\
    MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
    fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
    fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
    EVERY (\e. is_bytestring_type (expr_type e) \/
                 ?m. expr_type e = BaseT (BytesT (Fixed m))) args /\
    body_const_cells_agree mods cx env es /\
    expr_sim_inv_mods mods cenv cx env es /\
    (!e st. MEM e args /\ expr_sim_inv_mods mods cenv cx env st ==>
       expr_body_pre_mods mods cenv cx env e st) /\
    body_exprs_full_ok_mods mods exps cx args /\
    contract_inv mods exps ctx cenv cx /\
    module_body_inv mods cenv.ce_module tops cenv cx /\
    shadow_body_inv_mods mods exps ctx shadow_ctx /\
    (!fn inst z. frag_reachable ctx func s0 fn inst z ==> dalloca_fmp_headroom inst z) /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
    (!H. dead_lo_ok H (DF H) lo cenv cx) /\
    return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
    (!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==> not_fresh_at sa z) /\
    (!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==> not_fresh_at sa z) /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
       stmt_state_rel H ctx func cenv cx es s0 /\
       storage_well_formed_on cx es (FST H) /\
       ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\
    ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
    s0.vs_inst_idx = LENGTH sa.cs_current_insts /\
    lookup_var dv s0 = SOME (n2w (B+32)) /\ lookup_var ov s0 = SOME ow /\
    not_fresh_at sa dv /\ not_fresh_at sa ov /\
    MEM binst (fn_insts func) /\ binst.inst_opcode = ALLOCA /\
    binst.inst_id < sa.cs_next_id /\
    FLOOKUP s0.vs_allocas binst.inst_id = SOME (B,bsz) /\
    MEM oinst (fn_insts func) /\ oinst.inst_opcode = ALLOCA /\
    oinst.inst_id < sa.cs_next_id /\
    FLOOKUP s0.vs_allocas oinst.inst_id = SOME (w2n ow,64) /\
    (!name lb lsz. local_region cenv es.scopes s0 name lb lsz ==>
       (B+bsz <= lb \/ lb+lsz <= B) /\
       (w2n ow+64 <= lb \/ lb+lsz <= w2n ow)) /\
    (B+bsz <= w2n ow \/ w2n ow+64 <= B) /\
    B+bsz < dimword (:256) /\ w2n ow+64 < dimword (:256) /\
    B+bsz <= s0.vs_alloca_next /\ w2n ow+64 <= s0.vs_alloca_next /\
    allocas_from lo s0 /\ lo <= s0.vs_alloca_next /\ lo <= B /\ lo <= w2n ow /\
    ptr_covers G0 tn0 dv s0 (bsz-32) /\ ptr_covers G0 tn0 ov s0 32 /\
    (!i. B+32 <= i /\ i < B+32+k ==> i NOTIN tn0.t_mem) /\
    (!i. w2n ow <= i /\ i < w2n ow+32 ==> i NOTIN tn0.t_mem) /\
    mload (w2n ow) s0 = n2w k /\ k <= P /\
    32+P+SUM (MAP concat_payload_capacity (MAP expr_type args)) <= bsz /\
    32+concat_data_bound P (MAP expr_type args) <= bsz
End
