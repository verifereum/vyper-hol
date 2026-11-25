(* The Len suffix uses the same endpoint for the runner, scope and post. *)
Theory entryCreateBuiltinLength
Ancestors
  bodyFullBuiltinEnvLenScalar bodyFullBuiltinEnvLenCtor
  entryCreateBuiltinLenLayout entryCreateBuiltinLenCompose
  entryCreateBuiltinLenVisit entryCreateBuiltinCalldataLen entryCreateBuiltinStack
  entryCreateAdminSequence exprSimCalldata exprSimLen
  entryCreateFocusSpec entryCreateCompletedCut entryCreateIntervalLayout createSizeCutCode
  exprSimHypsDefs vyperTypeBuiltins fragExec venomState s1PrefixDefs
  vyperStorageFootprint loweringPosts fragGasOriginPtr list
  bodySimFull bodyPtrDefs exprSimMemDefs vyperTypeSystem
  bodyFullHashKeccakFixed[qualified,ignore_grammar]

Theorem len_run_scope[local]:
  compile_builtin_len ctor imm x loc sm = (op,sb) /\
  fn_has_code sm sb func /\ create_operand_at sm t /\ ~t.vs_halted /\
  run_inst_seq (emitted_insts sm sb) t = OK (z with vs_inst_idx := t.vs_inst_idx) /\
  z.vs_inst_idx = LENGTH sb.cs_current_insts ==>
  create_operand_full_scope sm sb explicit ctx func t [] (OK z)
Proof
  strip_tac >> drule compile_len_admin_layout >> strip_tac >>
  `create_operand_full_scope sm sb explicit ctx func t []
     (OK ((z with vs_inst_idx := t.vs_inst_idx) with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (irule create_admin_sequence_scope >> fs[EVERY_MEM]) >>
  `((z with vs_inst_idx := t.vs_inst_idx) with vs_inst_idx := LENGTH sb.cs_current_insts) = z` by
    (qpat_assum `z.vs_inst_idx = _` (SUBST1_TAC o SYM) >>
     simp[venom_state_component_equality]) >>
  metis_tac[]
QED

Theorem len_scoped_suffix:
  !DF lo d explicit ctx func PG cenv cx env e es st0 sa sm sb s0
     G0 tn0 ee tv vv t G tn op pvt tvt.
    expr_body_pre cenv cx env (Builtin (BaseT (UintT 256)) Len [e]) es /\
    expr_body_pre cenv cx env e es /\ is_sized_type (expr_type e) /\
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
      create_operand_full_scope sm sb explicit ctx func t [] (OK z) /\
      !H. valid_horizon cx st0 H ee.storage_trace ==>
        gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
          (t,G,tn) [] (OK z,G2,tn2) /\
        expr_post H ctx func cenv cx (Builtin (BaseT (UintT 256)) Len [e])
          es sa sb s0 ee (IntV (&n)) op z /\
        expr_store_bound cx (BaseT (UintT 256)) (IntV (&n)) op z /\
        z.vs_current_bb = sb.cs_current_bb /\
        z.vs_inst_idx = LENGTH sb.cs_current_insts /\
        alloca_history func z /\ (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
        s0.vs_alloca_next <= z.vs_alloca_next /\
        ghost_inv_at (DF H) lo d cenv cx ee G2 tn2 z /\
        ptr_val_ok cx (BaseT (UintT 256)) (IntV (&n)) op G2 tn2 z /\
        ghost_kept_at lo cenv es sa G0 tn0 s0 G2 tn2
Proof
  rpt gen_tac >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace`
    by fs[storage_trace_domain_def] >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp t` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
     fs[vv_post_def] >>
     first_assum (ACCEPT_TAC o MATCH_MP
       bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp)) >>
  (Cases_on `cenv.ce_is_ctor /\
     (case vv_location vv of NONE => LocMemory | SOME l => l) = LocCode`
   >> FIRST
      [drule_all len_full_suffix_scalar_run,
       qpat_x_assum `_ /\ _` strip_assume_tac >> drule_all len_full_suffix_ctor_run]) >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  `create_operand_full_scope sm sb explicit ctx func t [] (OK z)` by
    (qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
       (drule_then strip_assume_tac) >>
     irule len_run_scope >> first_assum (irule_at Any) >>
     simp[create_operand_at_def] >> goal_assum (drule_at Any) >> simp[]) >>
  qexistsl_tac [`n`,`z`,`G2`,`tn2`] >> asm_rewrite_tac[] >>
  qx_gen_tac `H` >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >> asm_rewrite_tac[] >>
  qpat_assum `expr_post H ctx func cenv cx _ _ _ _ _ _ _ _ z`
    (ACCEPT_TAC o MATCH_MP bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp o
     CONJUNCT1 o REWRITE_RULE[loweringPostsTheory.expr_post_def])
QED

Theorem length_stack_shape[local]:
  (bi = Len \/ bi = CalldataLen) /\
  expr_body_pre ce cx env (Builtin ann bi args) es ==>
  ann = BaseT (UintT 256) /\
  ?a op b. compile_expr ce ty (Builtin ann bi args) sa = (StackValue a op,b)
Proof
  strip_tac >> gvs[]
  >- (drule len_pre_args >> strip_tac >> gvs[compile_expr_len] >>
      pairarg_tac >> simp[exprBopLoweringTheory.as_stack_val_pair]) >>
  conj_tac >- gvs[expr_body_pre_def, cj 9 well_typed_expr_def, well_typed_builtin_app_def] >>
  simp[compile_calldata_len_stack]
QED

Theorem create_builtin_length_cases:
  (bi = Len \/ bi = CalldataLen) /\
  body_inv tops ctx ce cx /\ expr_body_pre ce cx env (Builtin ann bi args) es /\
  (bi = Len ==> builtin_args_length_ok Len (LENGTH args) ==>
    expr_vv_sim_scoped (DF,lo,d,ctx,shctx,PG,func,shfunc) ce cx ty (HD args) es) /\
  (bi = Len ==> !st0 sa sm sha shm vv s G tn.
    builtin_args_length_ok Len (LENGTH args) /\
    expr_body_pre ce cx env (HD args) es /\ create_layout sa sm /\
    expr_vv_sim_full_pre (DF,lo,d,ctx,shctx,PG,func,shfunc) ce cx ty (HD args)
      es (st0,sa,sm,sha,shm,vv,s,G,tn) ==>
    create_cut_code {} sa sm /\
    create_operand_cut sa sm (gas_explicit_sites ctx shctx) ctx func tops cx st0
      (eval_expr cx (HD args)) (es,s)) ==>
  (!st0 sa sb sha shb op s G tn.
    create_layout sa sb /\
    expr_sim_full_pre (DF,lo,d,ctx,shctx,PG,func,shfunc) ce cx ty
      (Builtin ann bi args) es (st0,sa,sb,sha,shb,op,s,G,tn) ==>
    scoped_operand_outcome (DF,lo,gas_explicit_sites ctx shctx,ctx,func,PG)
      (cx_tops cx) cx st0 sa sb (bind (eval_expr cx (Builtin ann bi args)) (read_result cx))
      (es,s,G,tn)
      (expr_sim_full_post (DF,lo,d,ctx,func) ce cx
        (Builtin ann bi args) (es,sa,sb,s,op,G,tn))
      (create_operand_exit_post ctx cx) /\
    create_operand_cut sa sb (gas_explicit_sites ctx shctx) ctx func tops cx st0
      (bind (eval_expr cx (Builtin ann bi args)) (read_result cx)) (es,s)) /\
  (!st0 sa sb sha shb vv s G tn.
    create_layout sa sb /\
    expr_vv_sim_full_pre (DF,lo,d,ctx,shctx,PG,func,shfunc) ce cx ty
      (Builtin ann bi args) es (st0,sa,sb,sha,shb,vv,s,G,tn) ==>
    scoped_operand_outcome (DF,lo,gas_explicit_sites ctx shctx,ctx,func,PG)
      (cx_tops cx) cx st0 sa sb (eval_expr cx (Builtin ann bi args)) (es,s,G,tn)
      (\H res ee G' tn' t.
         create_operand_vv_post (DF,lo,d,ctx,func) ce cx
           (Builtin ann bi args) (es,sa,sb,s,vv,G,tn) H res ee G' tn' t /\
         t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts)
      (create_operand_exit_post ctx cx) /\
    create_operand_cut sa sb (gas_explicit_sites ctx shctx) ctx func tops cx st0
      (eval_expr cx (Builtin ann bi args)) (es,s))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> conj_asm1_tac
  >- (rpt gen_tac >> strip_tac >> Cases_on `bi = Len`
      >- (gvs[] >> conj_tac
          >- (irule (MP len_value_scoped_from_suffix len_scoped_suffix) >>
              simp[] >> metis_tac[]) >>
          drule_at Any len_value_cut_from_layout >>
          disch_then irule >> simp[] >>
          conj_tac >- (rpt strip_tac >> drule compile_len_admin_layout >> simp[]) >>
          qexists_tac `env` >> simp[] >>
          rpt gen_tac >> strip_tac >> first_x_assum drule_all >> simp[]) >>
      `bi = CalldataLen` by metis_tac[] >> gvs[] >>
      drule_all create_calldatalen_value_site >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  `ann = BaseT (UintT 256) /\ ?a op. vv = StackValue a op` by
    (drule_all length_stack_shape >>
     disch_then (qspecl_then [`ty`,`sa`] strip_assume_tac) >>
     fs[expr_vv_sim_full_pre_def] >> metis_tac[]) >>
  qpat_x_assum `ann = BaseT (UintT 256)` SUBST_ALL_TAC >>
  qpat_x_assum `vv = StackValue _ _` SUBST_ALL_TAC >>
  irule create_builtin_stack_vv_at >>
  rpt (goal_assum (drule_at Any)) >>
  simp[vyperASTTheory.expr_type_def, compileEnvTheory.is_word_type_def] >>
  metis_tac[exprLoweringPropsTheory.eval_expr_builtin_value]
QED
