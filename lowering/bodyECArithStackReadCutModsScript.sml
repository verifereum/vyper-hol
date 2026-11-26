(* Forcing a successfully materialized EC point uses the existing stack operand. *)
Theory bodyECArithStackReadCutMods
Ancestors
  bodyAggregateReadMods bodyAggregateReadPostMods bodyFullShared bodyFullPostsMods
  exprSimECArith exprLowering gasShadowCompile gasShadowState compileEnv
  vyperInterpreter vyperState
Libs monadsyntax

val ec_expr = ``Builtin a bt [e1;e2]``;

Theorem ec_stack_compile_cut[local]:
  (bt = ECAdd \/ bt = ECMul) /\
  lower_value compile_expr cenv ty (^ec_expr) sa = (op,sb) /\
  lower_value compile_expr (gas_shadow_env T cenv) ty
    (gas_shadow_expr (^ec_expr)) shadow_sa = (op,shadow_sb) /\
  gas_shadow_state sa shadow_sa ==>
  compile_expr cenv ty (^ec_expr) sa = (StackValue a op,sb) /\
  compile_expr (gas_shadow_env T cenv) ty
    (gas_shadow_expr (^ec_expr)) shadow_sa = (StackValue a op,shadow_sb)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `compile_expr cenv ty (Builtin a bt [e1;e2]) sa` >>
  qmatch_asmsub_rename_tac `compile_expr cenv ty (Builtin a bt [e1;e2]) sa = (out,_)` >>
  `?res. out = StackValue a res` by
    (qpat_assum `bt = ECAdd \/ bt = ECMul` strip_assume_tac >> gvs[]
     >- (drule_then strip_assume_tac (cj 2 compile_ec_operands) >>
         simp[as_stack_val_def]) >>
     drule_then strip_assume_tac (cj 1 compile_ec_operands) >>
     simp[as_stack_val_def]) >>
  Cases_on `compile_expr (gas_shadow_env T cenv) ty
    (gas_shadow_expr (Builtin a bt [e1;e2])) shadow_sa` >>
  `gas_shadow_compiles (compile_expr cenv ty (Builtin a bt [e1;e2]))
    (compile_expr (gas_shadow_env T cenv) ty
      (gas_shadow_expr (Builtin a bt [e1;e2])))` by
    irule (cj 1 gas_shadow_compile_expr_env |> SPEC_ALL |>
           Q.INST [`shadow` |-> `T`] |> REWRITE_RULE [COND_CLAUSES]) >>
  drule_all_then strip_assume_tac gas_shadow_step >>
  gvs[lower_value_def,comp_bind_def,unwrap_value_def,comp_return_def]
QED

Theorem ec_arith_stack_read_cut_mods:
  (bt = ECAdd \/ bt = ECMul) /\
  a = ArrayT (BaseT (UintT 256)) (Fixed 2) /\
  expr_type e1 = a /\
  expr_type e2 = (if bt = ECAdd then a else BaseT (UintT 256)) ==>
  !st0 sa sb shadow_sa shadow_sb op s0 G0 tn0.
    lower_value compile_expr cenv ty (^ec_expr) sa = (op,sb) /\
    lower_value compile_expr (gas_shadow_env T cenv) ty
      (gas_shadow_expr (^ec_expr)) shadow_sa = (op,shadow_sb) /\
    gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
    gas_shadow_context ctx shadow_ctx /\ ctx_inst_ids_distinct ctx /\
    gas_shadow_function func shadow_func /\ MEM func ctx.ctx_functions /\
    MEM shadow_func shadow_ctx.ctx_functions /\ fn_has_code sa sb func /\
    fn_has_code shadow_sa shadow_sb shadow_func /\
    fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
    (!H. dead_lo_ok_mods H (DF H) lo cenv cx) /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
    gas_admissible (bind (eval_expr cx (^ec_expr)) (read_result cx)) expr_res_ok es /\
    return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
    (!fn inst s. frag_reachable ctx func s0 fn inst s ==> dalloca_fmp_headroom inst s) /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      stmt_state_rel H ctx func cenv cx es s0 /\
      immutable_frame_mods func cenv cx es s0 /\
      storage_well_formed_on cx es (FST H) /\
      ghost_inv_at_mods (DF H) lo d cenv cx es G0 tn0 s0) /\ ~s0.vs_halted /\
    s0.vs_current_bb = sa.cs_current_bb /\ s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?vv. compile_expr cenv ty (^ec_expr) sa = (vv,sb) /\
      compile_expr (gas_shadow_env T cenv) ty (gas_shadow_expr (^ec_expr)) shadow_sa =
        (vv,shadow_sb) /\
      !H ee raw v G tn t. valid_horizon cx st0 H ee.storage_trace /\ raw = Value v /\
        vv_post_mods H ctx func cenv cx (^ec_expr) es sa sb s0 ee raw vv t /\
        vv_store_bound cx (post_value_type cenv (^ec_expr)) (lowered_value_type cenv (^ec_expr))
          ee raw vv t /\
        t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
        alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
        s0.vs_alloca_next <= t.vs_alloca_next /\
        ghost_inv_at_mods (DF H) lo d cenv cx ee G tn t /\
        ptr_vv_ok cx (post_value_type cenv (^ec_expr)) raw vv ee G tn t /\
        (!v. raw = Value v /\ ~is_word_type (post_value_type cenv (^ec_expr)) /\
             ~is_bytestring_type (post_value_type cenv (^ec_expr)) ==>
             vv_own cenv cx (post_value_type cenv (^ec_expr)) sa sb ee raw vv t /\
             (!t' p. vv = LocatedValue t' p ==> p.ptr_location = LocMemory)) /\
        (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
         ?val. read_result cx raw ee = (INL val,ee) /\
               !rt w. evaluate_type (get_tenv cx) (post_value_type cenv (^ec_expr)) = SOME rt /\
                      eval_operand (vv_operand vv) t = SOME w ==>
                      w2n w + type_memory_size rt <= lo /\
                      (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
                             val_in_memory rt val (w2n w) mem)) /\
        (!t' op'. vv = StackValue t' op' /\ ~is_word_type (post_value_type cenv (^ec_expr)) ==>
                  ptr_buf_ok cenv (^ec_expr) op' G t) /\
        (!t' p. vv = LocatedValue t' p /\ p.ptr_location = LocMemory ==>
                ptr_buf_ok cenv (^ec_expr) p.ptr_operand G t) /\
        ghost_kept_at lo cenv es sa G0 tn0 s0 G tn ==>
        expr_post_mods H ctx func cenv cx (^ec_expr) es sa sb s0 ee v op t /\
        expr_store_bound cx (post_value_type cenv (^ec_expr)) v op t /\
        t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
        alloca_history func t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
        s0.vs_alloca_next <= t.vs_alloca_next /\
        ghost_inv_at_mods (DF H) lo d cenv cx ee G tn t /\
        ptr_val_ok cx (post_value_type cenv (^ec_expr)) v op G tn t /\
        (~is_word_type (post_value_type cenv (^ec_expr)) ==> ptr_buf_ok cenv (^ec_expr) op G t) /\
        ghost_kept_at lo cenv es sa G0 tn0 s0 G tn
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `a = ArrayT _ _` kall_tac >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then strip_assume_tac ec_stack_compile_cut >>
  qexists_tac `StackValue a op` >> asm_rewrite_tac[] >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `raw = Value v` SUBST_ALL_TAC >>
  `~is_word_type (post_value_type cenv (Builtin a bt [e1;e2])) ==>
    ptr_buf_ok cenv (Builtin a bt [e1;e2]) op G t` by
    (qpat_assum `!t' op'. StackValue _ _ = StackValue t' op' /\ _ ==> _`
       (qspecl_then [`a`,`op`] mp_tac) >> simp[]) >>
  drule_all_then strip_assume_tac stack_value_read_post_mods >>
  asm_rewrite_tac[]
QED
