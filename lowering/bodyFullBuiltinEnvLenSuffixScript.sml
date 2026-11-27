(* A single fixed-endpoint Len suffix, including evolved pointer ghosts. *)
Theory bodyFullBuiltinEnvLenSuffix
Ancestors
  bodyFullBuiltinEnvLenScalar bodyFullBuiltinEnvLenCtor
  exprSimHypsDefs[qualified]

Theorem len_full_suffix:
  !mods DF lo d explicit ctx func PG cenv cx env e es st0 sa sm sb s0
   G0 tn0 ee tv vv t G tn op pvt tvt.
    expr_body_pre_mods mods cenv cx env (Builtin (BaseT (UintT 256)) Len [e]) es /\
    expr_body_pre_mods mods cenv cx env e es /\ is_sized_type (expr_type e) /\
    compile_builtin_len cenv.ce_is_ctor cenv.ce_imm_alloca (vv_operand vv)
      (case vv_location vv of NONE => LocMemory | SOME l => l) sm = (op,sb) /\
    fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
    (!H. dead_lo_ok H (DF H) lo cenv cx) /\
    type_widens_to (get_tenv cx) (post_value_type cenv e) (expr_type e) /\
    evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME pvt /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME tvt /\
    env.type_defs = get_tenv cx /\
    eval_result_typed (env,cx,ee) tv (Type (expr_type e)) /\
    (!v. read_result cx tv ee = (INL v,ee) ==> value_has_type tvt v) /\
    storage_trace_domain cx st0 ee.storage_trace /\ ~t.vs_halted /\
    t.vs_current_bb = sm.cs_current_bb /\ t.vs_inst_idx = LENGTH sm.cs_current_insts /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      vv_post H ctx func cenv cx e es sa sm s0 ee tv vv t /\
      vv_store_bound cx (post_value_type cenv e) (lowered_value_type cenv e) ee tv vv t /\
      alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
      ghost_inv_at (DF H) lo d cenv cx ee G tn t /\
      ptr_vv_ok cx (post_value_type cenv e) tv vv ee G tn t /\
      (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
       ?val. read_result cx tv ee = (INL val,ee) /\
         !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
           eval_operand (vv_operand vv) t = SOME w ==>
           w2n w + type_memory_size rt <= lo /\
           !mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
             val_in_memory rt val (w2n w) mem) /\
      (!t' op. vv = StackValue t' op /\ ~is_word_type (post_value_type cenv e) ==>
         ptr_buf_ok cenv e op G t) /\
      (!t' p. vv = LocatedValue t' p /\ p.ptr_location = LocMemory ==>
         ptr_buf_ok cenv e p.ptr_operand G t) /\
      ghost_kept_at lo cenv es sa G0 tn0 s0 G tn) ==>
    ?n z G2 tn2.
      result_array_length cx tv ee = (INL n,ee) /\
      !H. valid_horizon cx st0 H ee.storage_trace ==>
        gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (t,G,tn) [] (OK z,G2,tn2) /\
        expr_post H ctx func cenv cx (Builtin (BaseT (UintT 256)) Len [e])
          es sa sb s0 ee (IntV (&n)) op z /\
        expr_store_bound cx (BaseT (UintT 256)) (IntV (&n)) op z /\
        z.vs_current_bb = sb.cs_current_bb /\ z.vs_inst_idx = LENGTH sb.cs_current_insts /\
        alloca_history func z /\ (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
        s0.vs_alloca_next <= z.vs_alloca_next /\
        ghost_inv_at (DF H) lo d cenv cx ee G2 tn2 z /\
        ptr_val_ok cx (BaseT (UintT 256)) (IntV (&n)) op G2 tn2 z /\
        ghost_kept_at lo cenv es sa G0 tn0 s0 G2 tn2
Proof
  rpt gen_tac >> strip_tac >>
  (Cases_on `cenv.ce_is_ctor /\
    (case vv_location vv of NONE => LocMemory | SOME l => l) = LocCode`
  >| [qpat_x_assum `_ /\ _` strip_assume_tac >>
      `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace)
         ee.storage_trace` by fs[vyperStorageFootprintTheory.storage_trace_domain_def] >>
      qpat_assum `!H. valid_horizon cx st0 H ee.storage_trace ==> _`
        (drule_then strip_assume_tac) >>
      `stmt_state_rel (storage_trace_horizon ee.storage_trace) ctx func cenv cx ee t` by
        fs[loweringPostsTheory.vv_post_def] >>
      `ctx_has_dalloca ctx ==> allocas_below_fmp t` by
        (first_assum (ACCEPT_TAC o MATCH_MP
          bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp)) >>
      drule_all len_full_suffix_ctor,
      drule_all len_full_suffix_scalar]) >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  qexistsl_tac [`n`,`z`,`G2`,`tn2`] >> asm_rewrite_tac[] >>
  qx_gen_tac `H` >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H ee.storage_trace ==> _`
    (drule_then strip_assume_tac) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp z` by
    (qpat_assum `expr_post H ctx func cenv cx _ _ _ _ _ _ _ _ z`
       (ACCEPT_TAC o MATCH_MP
         bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp o
         CONJUNCT1 o REWRITE_RULE[loweringPostsTheory.expr_post_def])) >>
  asm_rewrite_tac[]
QED
