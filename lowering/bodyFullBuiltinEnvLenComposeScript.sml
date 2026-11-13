(* Len child-outcome composition, independent of suffix implementation. *)
Theory bodyFullBuiltinEnvLenCompose
Ancestors
  bodySimFull bodyFullGhostFrame exprSimLen exprSimSource exprSimHypsDefs
  exprSimHyps vyperTypeInvariants
  exprSimUnwrap exprLowering exprLoweringProps loweringPosts bodyPtrDefs
  fragGasSeqPtr fragGasOriginPtr gasOutcomeFull gasOutcomeFullCompose gasShadowState
  vyperStorageFootprint vyperStorageTrace vyperTypeSystem vyperTypeBuiltins vyperAST
  loweringStateRelDefs ptrDiscipline codegenRel contextCodegenRel
  instMemFrontier allocaHistory emitHelperProps compileEnv
  vyperInterpreter vyperState venomState venomInst list finite_map

Theorem len_full_compose:
  (!DF lo d explicit ctx func PG cenv cx env e es st0 sa sm sb s0
    G0 tn0 ee tv vv t G tn op pvt tvt.
    expr_body_pre cenv cx env (Builtin (BaseT (UintT 256)) Len [e]) es /\
    expr_body_pre cenv cx env e es /\ is_sized_type (expr_type e) /\
    compile_builtin_len cenv.ce_is_ctor cenv.ce_imm_alloca (vv_operand vv)
      (case vv_location vv of NONE => LocMemory | SOME l => l) sm = (op,sb) /\
    fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
    (!H. dead_lo_ok H (DF H) lo cenv cx) /\ ~ctx_has_dalloca ctx /\
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
      vv_store_bound cx (expr_type e) (lowered_value_type cenv e) ee tv vv t /\
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
        gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
          (t,G,tn) [] (OK z,G2,tn2) /\
        expr_post H ctx func cenv cx (Builtin (BaseT (UintT 256)) Len [e])
          es sa sb s0 ee (IntV (&n)) op z /\
        expr_store_bound cx (BaseT (UintT 256)) (IntV (&n)) op z /\
        z.vs_current_bb = sb.cs_current_bb /\
        z.vs_inst_idx = LENGTH sb.cs_current_insts /\
        alloca_history func z /\ s0.vs_alloca_next <= z.vs_alloca_next /\
        ghost_inv_at (DF H) lo d cenv cx ee G2 tn2 z /\
        ptr_val_ok cx (BaseT (UintT 256)) (IntV (&n)) op G2 tn2 z /\
        ghost_kept_at lo cenv es sa G0 tn0 s0 G2 tn2) ==>
  !DF lo d explicit ctx func PG cenv cx env e es st0 sa sm sb s0
    G0 tn0 vv op.
    expr_body_pre cenv cx env (Builtin (BaseT (UintT 256)) Len [e]) es /\
    expr_body_pre cenv cx env e es /\ is_sized_type (expr_type e) /\
    compile_builtin_len cenv.ce_is_ctor cenv.ce_imm_alloca (vv_operand vv)
      (case vv_location vv of NONE => LocMemory | SOME l => l) sm = (op,sb) /\
    fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var /\
    (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
    (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
    (!H. dead_lo_ok H (DF H) lo cenv cx) /\ ~ctx_has_dalloca ctx /\
    gas_outcome_full (DF,lo,explicit,ctx,func,PG) (cx_tops cx) cx st0
      (eval_expr cx e) (es,s0,G0,tn0)
      (\H res ee G tn t. ?tv. res = INL tv /\
        vv_post H ctx func cenv cx e es sa sm s0 ee tv vv t /\
        vv_store_bound cx (expr_type e) (lowered_value_type cenv e) ee tv vv t /\
        t.vs_current_bb = sm.cs_current_bb /\ t.vs_inst_idx = LENGTH sm.cs_current_insts /\
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
        ghost_kept_at lo cenv es sa G0 tn0 s0 G tn)
      (\H res ee gt r. expr_exit res r) ==>
    gas_outcome_full (DF,lo,explicit,ctx,func,PG) (cx_tops cx) cx st0
      (bind (eval_expr cx (Builtin (BaseT (UintT 256)) Len [e])) (read_result cx))
      (es,s0,G0,tn0)
      (\H res ee G tn t. ?v. res = INL v /\
        expr_post H ctx func cenv cx (Builtin (BaseT (UintT 256)) Len [e])
          es sa sb s0 ee v op t /\
        expr_store_bound cx (BaseT (UintT 256)) v op t /\
        t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
        alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
        ghost_inv_at (DF H) lo d cenv cx ee G tn t /\
        ptr_val_ok cx (post_value_type cenv (Builtin (BaseT (UintT 256)) Len [e])) v op G tn t /\
        (~is_word_type (post_value_type cenv (Builtin (BaseT (UintT 256)) Len [e])) ==>
          ptr_buf_ok cenv (Builtin (BaseT (UintT 256)) Len [e]) op G t) /\
        ghost_kept_at lo cenv es sa G0 tn0 s0 G tn)
      (\H res ee gt r. expr_exit res r)
Proof
  disch_tac >> rpt gen_tac >> strip_tac >>
  `bind (eval_expr cx (Builtin (BaseT (UintT 256)) Len [e])) (read_result cx) =
   bind (eval_expr cx e) (\tv. bind (result_array_length cx tv) (\n. return (IntV (&n))))` by
    (simp[len_source, bind_assoc, read_result_def, bind_return]) >>
  pop_assum SUBST1_TAC >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ Qchild _` >>
  match_mp_tac (Q.INST [`Q1` |-> `\H res ee G tn t. Qchild H res ee G tn t /\ ~t.vs_halted /\ ee.gas_obs = []`] gas_outcome_full_bind_all) >>
  conj_tac
  >- (irule gas_outcome_full_post_source >>
      qpat_assum `gas_outcome_full _ _ _ _ _ _ _ _` (irule_at Any) >>
      simp[] >> rpt gen_tac >> Cases_on `res` >> simp[] >>
      Cases_on `y` >> Cases_on `r` >>
      simp[exprSimDefsTheory.expr_exit_def] >>
      rename1 `Error err` >> Cases_on `err` >>
      simp[exprSimDefsTheory.expr_exit_def]) >>
  conj_tac >- suspend "continuation" >>
  conj_tac >- simp[evaluate_storage_trace_frame] >>
  conj_tac >- simp[storage_trace_frame_bind_all, storage_trace_frame_array_length,
                  storage_trace_frame_return] >>
  conj_tac >- (rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_error_result >> simp[]) >>
  rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_bind_result >> simp[] >> metis_tac[]
QED

Resume len_full_compose[continuation]:
  rpt gen_tac >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
    (qspec_then `storage_trace_horizon mid.storage_trace` mp_tac) >>
  (impl_tac >- simp[]) >>
  simp[NoAsms, Abbr `Qchild`] >> strip_tac >>
  disj1_tac >> qexists_tac `tv` >> simp[] >>
  `env.type_defs = get_tenv cx` by
    fs[expr_body_pre_def, expr_sim_inv_def, env_consistent_def,
       env_context_consistent_def] >>
  `type_widens_to (get_tenv cx) (post_value_type cenv e) (expr_type e)` by
    (`type_widens_to env.type_defs (post_value_type cenv e) (expr_type e)` suffices_by simp[] >>
     irule exprSimHypsTheory.post_value_type_widens >>
     fs[expr_body_pre_def] >> metis_tac[]) >>
  qpat_assum `expr_body_pre cenv cx env e es`
    (strip_assume_tac o MATCH_MP exprSimHypsTheory.post_type_evaluates) >>
  qpat_x_assum `res = INL tv` SUBST_ALL_TAC >>
  qpat_assum `!tail. eval_expr _ _ _ = _`
    (qspec_then `mid.gas_obs` (assume_tac o SIMP_RULE (srw_ss()) [])) >>
  drule_at (Pos last) expr_body_pre_runtime_typed >>
  disch_then (qspecl_then [`cenv`,`env`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  qmatch_goalsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ Qend _` >>
  `?n z G2 tn2.
     result_array_length cx tv mid = (INL n,mid) /\
     !H. valid_horizon cx st0 H mid.storage_trace ==>
       gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
         (t,G1,tn1) [] (OK z,G2,tn2) /\
       expr_post H ctx func cenv cx (Builtin (BaseT (UintT 256)) Len [e])
         es sa sb s0 mid (IntV (&n)) op z /\
       expr_store_bound cx (BaseT (UintT 256)) (IntV (&n)) op z /\
       z.vs_current_bb = sb.cs_current_bb /\ z.vs_inst_idx = LENGTH sb.cs_current_insts /\
       alloca_history func z /\ s0.vs_alloca_next <= z.vs_alloca_next /\
       ghost_inv_at (DF H) lo d cenv cx mid G2 tn2 z /\
       ptr_val_ok cx (BaseT (UintT 256)) (IntV (&n)) op G2 tn2 z /\
       ghost_kept_at lo cenv es sa G0 tn0 s0 G2 tn2` by
    (qpat_assum `!DF lo. _` irule >>
     simp[] >> conj_tac
     >- (qexistsl_tac [`sm`,`vv`] >> simp[] >>
         rpt strip_tac >>
         qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
           (qspec_then `H` mp_tac) >> simp[NoAsms] >> strip_tac >> gvs[]) >>
     qexists_tac `env` >> simp[] >>
     rpt strip_tac >>
     qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> _`
       (qspec_then `H` mp_tac) >> simp[NoAsms] >> strip_tac >> gvs[]) >>
  irule gas_outcome_full_pure >>
  reverse conj_tac >- simp[] >>
  qexistsl_tac [`G2`,`mid`,`INL (IntV (&n))`,`z`,`tn2`] >>
  simp[] >> conj_tac
  >- (drule len_ral_gas_obs >> strip_tac >> simp[bind_def, return_def]) >>
  rpt strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H mid.storage_trace ==> gas_origin_ptr_path _ _ _ _ /\ _`
    (qspec_then `H` mp_tac) >>
  simp[NoAsms] >> strip_tac >>
  `mid with gas_obs := [] = mid` by simp[vyperStateTheory.evaluation_state_component_equality] >>
  gvs[Abbr `Qend`, expr_type_def, is_word_type_def]
QED

Finalise len_full_compose
