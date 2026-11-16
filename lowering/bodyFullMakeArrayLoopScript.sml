(* Full-H composition of the MakeArray store loop. *)
Theory bodyFullMakeArrayLoop
Ancestors exprSimDefs[qualified,ignore_grammar]
  bodyFullMakeArrayStore exprSimAggregateLoops exprSimAggregateSource
  exprSimWordArgs gasOutcomeFullCompose exprSimSource exprLowering compileEnv
  valueEncoding gasShadowCompileHelpers gasShadowState gasShadow
  gasShadowCompileStmtHelpers gasShadowCompileContext gasShadowCompileConvert
  forPtrAllocationFrame

val _ = Parse.hide "base";

Theorem make_array_loop_full:
  !args tys dtvs off ps sa sb shadow_sa shadow_sb es s G tn.
    body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env ebase /\
    csbase.cs_next_id <= aid /\ csbase.cs_next_id <= sa.cs_next_id /\
    csbase.cs_next_var <= sa.cs_next_var /\
    local_ptrs_reserved cenv csbase /\ local_ptrs_reserved cenv sa /\
    ctx_inst_ids_distinct ctx /\ fn_inst_ids_distinct func /\
    gas_shadow_context ctx shadow_ctx /\ gas_shadow_function func shadow_func /\
    MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
    ~ctx_has_dalloca ctx /\ (!H. dead_lo_ok H (DF H) lo cenv cx) /\
    (!x n. cenv.ce_return_buf = SOME (PtrVar (Var x) n) ==>
           not_fresh_at csbase x) /\
    (!x n. cenv.ce_return_pc = SOME (PtrVar (Var x) n) ==>
           not_fresh_at csbase x) /\
    (!H. valid_horizon cx st0 H ebase.storage_trace ==>
         stmt_state_rel H ctx func cenv cx ebase sbase) /\
    body_exprs_full_ok cx args /\
    (!e ee. MEM e args /\ expr_sim_inv cenv cx env ee ==>
            expr_body_pre cenv cx env e ee) /\
    expr_sim_inv cenv cx env es /\
    LIST_REL (\ty e. arg_type_fits (expr_type e) ty) tys args /\
    OPT_MMAP (evaluate_type (get_tenv cx)) tys = SOME dtvs /\
    LIST_REL (\ty tv. type_memory_bytes cenv ty = type_memory_size tv) tys dtvs /\
    off + type_memory_size_list dtvs <= cap /\
    ((\cs ee s G tn.
    (?events. ee.storage_trace = ebase.storage_trace ++ events) /\
    FLOOKUP s.vs_allocas aid = SOME (base,cap) /\
    lookup_var q s = SOME (n2w base) /\
    ptr_covers G tn q s cap /\ not_fresh_at cs q /\
    aid < cs.cs_next_id /\ base+cap < dimword (:256) /\
    base+cap <= s.vs_alloca_next /\
    (!name b n. local_region cenv ee.scopes s name b n ==>
                loweringStateRelDefs$regions_disjoint base cap b n) /\
    alloca_history func s /\ sbase.vs_alloca_next <= s.vs_alloca_next /\
    (!a b. FLOOKUP sbase.vs_allocas a = SOME b ==>
           FLOOKUP s.vs_allocas a = SOME b) /\
    MAP FDOM ebase.scopes = MAP FDOM ee.scopes /\
    wb_frame cenv ebase ee csbase sbase s /\
    ghost_kept_at lo cenv ebase csbase Gbase tnbase sbase G tn /\
    return_buf_frame d cenv cs s /\ ~s.vs_halted /\
    s.vs_current_bb = cs.cs_current_bb /\
    s.vs_inst_idx = LENGTH cs.cs_current_insts /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
         stmt_state_rel H ctx func cenv cx ee s /\
         storage_well_formed_on cx ee (FST H) /\
         ghost_inv_at (DF H) lo d cenv cx ee G tn s))) sa es s G tn /\ ((\ps off s tn.
        EVERY (\(rt,v,p,n).
          val_wf rt v /\ val_footprint rt v <= n /\
          base <= p /\ p+n <= base+off /\
          (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
               val_in_memory rt v p m)) ps)) ps off s tn /\
    compile_make_tuple compile_expr cenv args tys (Var q) off sa = (Var q,sb) /\
    compile_make_tuple compile_expr cenv (MAP gas_shadow_expr args) tys
      (Var q) off shadow_sa = (Var q,shadow_sb) /\
    gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
    fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func ==>
    gas_outcome_full
      (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      (cx_tops cx) cx st0 (eval_exprs cx args) (es,s,G,tn)
      (\H res ee Gf tnf t.
        ?vs. res = INL vs /\ LIST_REL value_has_type dtvs vs /\
          LIST_REL val_wf dtvs vs /\ expr_sim_inv cenv cx env ee /\
          ((\cs ee s G tn.
    (?events. ee.storage_trace = ebase.storage_trace ++ events) /\
    FLOOKUP s.vs_allocas aid = SOME (base,cap) /\
    lookup_var q s = SOME (n2w base) /\
    ptr_covers G tn q s cap /\ not_fresh_at cs q /\
    aid < cs.cs_next_id /\ base+cap < dimword (:256) /\
    base+cap <= s.vs_alloca_next /\
    (!name b n. local_region cenv ee.scopes s name b n ==>
                loweringStateRelDefs$regions_disjoint base cap b n) /\
    alloca_history func s /\ sbase.vs_alloca_next <= s.vs_alloca_next /\
    (!a b. FLOOKUP sbase.vs_allocas a = SOME b ==>
           FLOOKUP s.vs_allocas a = SOME b) /\
    MAP FDOM ebase.scopes = MAP FDOM ee.scopes /\
    wb_frame cenv ebase ee csbase sbase s /\
    ghost_kept_at lo cenv ebase csbase Gbase tnbase sbase G tn /\
    return_buf_frame d cenv cs s /\ ~s.vs_halted /\
    s.vs_current_bb = cs.cs_current_bb /\
    s.vs_inst_idx = LENGTH cs.cs_current_insts /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
         stmt_state_rel H ctx func cenv cx ee s /\
         storage_well_formed_on cx ee (FST H) /\
         ghost_inv_at (DF H) lo d cenv cx ee G tn s))) sb ee t Gf tnf /\ ((\ps off s tn.
        EVERY (\(rt,v,p,n).
          val_wf rt v /\ val_footprint rt v <= n /\
          base <= p /\ p+n <= base+off /\
          (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
               val_in_memory rt v p m)) ps)) ps off t tnf /\
          (!m. mem_agree_outside tnf.t_mem t.vs_memory m ==>
               tuple_in_memory vs dtvs (base+off) m) /\
          (!p n. base+off+type_memory_size_list dtvs <= p /\ p+n <= base+cap ==>
                 mem_bytes_at p n t.vs_memory = mem_bytes_at p n s.vs_memory) /\
          (~EXISTS expr_has_effect args ==>
            (!name b n. local_region cenv es.scopes s name b n ==>
              mem_bytes_at b n t.vs_memory = mem_bytes_at b n s.vs_memory) /\
            !p n. (p+n <= base \/ base+cap <= p) /\
              (!inst b sz. MEM inst (fn_insts func) /\
                inst.inst_opcode = ALLOCA /\ sa.cs_next_id <= inst.inst_id /\
                FLOOKUP t.vs_allocas inst.inst_id = SOME (b,sz) ==>
                loweringStateRelDefs$regions_disjoint p n b sz) ==>
              mem_bytes_at p n t.vs_memory = mem_bytes_at p n s.vs_memory))
      (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r)
Proof
  qabbrev_tac `packet = (\cs ee s G tn.
    (?events. ee.storage_trace = ebase.storage_trace ++ events) /\
    FLOOKUP s.vs_allocas aid = SOME (base,cap) /\
    lookup_var q s = SOME (n2w base) /\
    ptr_covers G tn q s cap /\ not_fresh_at cs q /\
    aid < cs.cs_next_id /\ base+cap < dimword (:256) /\
    base+cap <= s.vs_alloca_next /\
    (!name b n. local_region cenv ee.scopes s name b n ==>
                loweringStateRelDefs$regions_disjoint base cap b n) /\
    alloca_history func s /\ sbase.vs_alloca_next <= s.vs_alloca_next /\
    (!a b. FLOOKUP sbase.vs_allocas a = SOME b ==>
           FLOOKUP s.vs_allocas a = SOME b) /\
    MAP FDOM ebase.scopes = MAP FDOM ee.scopes /\
    wb_frame cenv ebase ee csbase sbase s /\
    ghost_kept_at lo cenv ebase csbase Gbase tnbase sbase G tn /\
    return_buf_frame d cenv cs s /\ ~s.vs_halted /\
    s.vs_current_bb = cs.cs_current_bb /\
    s.vs_inst_idx = LENGTH cs.cs_current_insts /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
         stmt_state_rel H ctx func cenv cx ee s /\
         storage_well_formed_on cx ee (FST H) /\
         ghost_inv_at (DF H) lo d cenv cx ee G tn s))` >>
  qabbrev_tac `prefix = (\ps off s tn.
        EVERY (\(rt,v,p,n).
          val_wf rt v /\ val_footprint rt v <= n /\
          base <= p /\ p+n <= base+off /\
          (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
               val_in_memory rt v p m)) ps)` >>
  Induct_on `args`
  >- (rpt gen_tac >> simp[Abbr `packet`,Abbr `prefix`] >> strip_tac >>
      Cases_on `tys` >> gvs[] >>
      gvs[compile_make_tuple_def, comp_return_def] >>
      irule gas_outcome_full_pure >>
      reverse conj_tac >- simp[] >>
      qexistsl_tac [`G`,`es`,`INL []`,`s`,`tn`] >>
      simp[eval_exprs_nil, wb_frame_gas_obs,
           fragGasOriginPtrTheory.gas_origin_ptr_path_rules,
           valueEncodingDefsTheory.val_in_memory_def] >> rpt strip_tac
      >~ [`regions_disjoint base cap b n`]
      >- (first_x_assum irule >> goal_assum (drule_at Any))
      >~ [`storage_well_formed_on _ _ _`]
      >- (qpat_x_assum `!H. valid_horizon _ _ H _ ==> _ /\ _ /\ _`
            drule >>
          simp[bodyPtrDefsTheory.ghost_inv_at_def,
               vyperStorageFootprintTheory.storage_well_formed_on_def,
               oneline vyperStorageBackendTheory.get_storage_def])
      >~ [`ghost_inv_at _ _ _ _ _ _ _ _ _`]
      >- (qpat_x_assum `!H. valid_horizon _ _ H _ ==> _ /\ _ /\ _`
            drule >> strip_tac >>
          gvs[bodyPtrDefsTheory.ghost_inv_at_def] >> first_assum ACCEPT_TAC)
      >> (qpat_x_assum `!H. valid_horizon _ _ H _ ==> _ /\ _ /\ _`
            drule >> simp[bodyPtrDefsTheory.ghost_inv_at_def,
              fragGasOriginPtrTheory.gas_origin_ptr_path_rules]))
  >> rpt gen_tac >> strip_tac >>
  Cases_on `tys` >- gvs[] >> gvs[] >>
  qpat_assum `body_exprs_full_ok cx (h::args)`
    (strip_assume_tac o REWRITE_RULE[bodyFullPredsTheory.body_exprs_full_ok_def]) >>
  rename1 `evaluate_type (get_tenv cx) mty = SOME dtv` >>
  qpat_assum `compile_make_tuple _ _ (h::args) _ _ _ sa = _`
    (strip_assume_tac o MATCH_MP compile_make_tuple_cons) >>
  qpat_assum `compile_make_tuple _ _ (gas_shadow_expr h::_) _ _ _ shadow_sa = _`
    (strip_assume_tac o MATCH_MP compile_make_tuple_cons) >>
  `vv = vv' /\ gas_shadow_state sm sm'` by
    (mp_tac (Q.INST [`cenv` |-> `cenv`, `ty` |-> `expr_type h`, `e` |-> `h`]
       gas_shadow_stmt_compile_expr) >>
     rewrite_tac[gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`sa`,`shadow_sa`] mp_tac) >> gvs[]) >> gvs[] >>
  `dst = dst' /\ gas_shadow_state sn sn'` by
    (mp_tac (Q.INST [`opc` |-> `ADD`, `ops` |-> `[Var q; Lit (n2w off)]`]
      gas_shadow_compiles_emit_op_same) >>
     rewrite_tac[gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`sm`,`sm'`] mp_tac) >> simp[]) >> gvs[] >>
  `op = op' /\ gas_shadow_state su su'` by
    (mp_tac gasShadowCompileConvertTheory.gas_shadow_compiles_unwrap_value >>
     simp[gas_shadow_compiles_def] >> disch_then drule >> simp[] >> metis_tac[]) >> gvs[] >>
  `gas_shadow_state st st'` by
    (mp_tac (Q.INST [`src` |-> `op`, `dst_ty` |-> `mty`,
        `src_ty` |-> `lowered_value_type cenv h`]
        gas_shadow_compiles_store_memory) >>
     rewrite_tac[gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`su`,`su'`] mp_tac) >> simp[]) >>
  `cs_extends sa sm /\ cs_extends shadow_sa sm'` by
    metis_tac[exprSimUnwrapTheory.compile_expr_extends] >>
  `cs_extends sm sn /\ cs_extends sm' sn'` by
    (mp_tac (cj 2 fragExecTheory.cs_appends_emit_helpers) >>
     simp[fragExecTheory.cs_appends_def] >> metis_tac[]) >>
  `cs_extends sn su /\ cs_extends sn' su'` by
    metis_tac[exprSimUnwrapTheory.unwrap_value_extends] >>
  `cs_extends su st /\ cs_extends su' st'` by
    (qpat_assum `compile_store_memory _ _ _ _ _ su = _` mp_tac >>
     qpat_assum `compile_store_memory _ _ _ _ _ su' = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     metis_tac[externalEntryShapeTheory.compile_store_memory_labels,pairTheory.SND]) >>
  `cs_extends sa st /\ cs_extends shadow_sa st'` by
    metis_tac[compileEnvTheory.cs_extends_trans] >>
  `cs_extends st sb /\ cs_extends st' shadow_sb` by
    (mp_tac externalEntryShapeTheory.compile_make_tuple_labels >>
     disch_then (qspecl_then [`compile_expr`,`cenv`,`args`,`t`,`Var q`,
                             `off + type_memory_size dtv`,`st`] mp_tac) >>
     simp[externalEntryShapeTheory.compile_expr_labels] >> strip_tac >>
     mp_tac externalEntryShapeTheory.compile_make_tuple_labels >>
     disch_then (qspecl_then [`compile_expr`,`cenv`,`MAP gas_shadow_expr args`,`t`,`Var q`,
                             `off + type_memory_size dtv`,`st'`] mp_tac) >>
     simp[externalEntryShapeTheory.compile_expr_labels]) >>
  `fn_has_code sa st func /\ fn_has_code st sb func /\
   fn_has_code shadow_sa st' shadow_func /\ fn_has_code st' shadow_sb shadow_func` by
    metis_tac[fragExecTheory.fn_has_code_split] >>
  `expr_body_pre cenv cx env h es` by metis_tac[] >>
  `gas_admissible (bind (eval_expr cx h) (read_result cx)) expr_res_ok es` by
    metis_tac[expr_body_pre_gas_admissible] >>
  mp_tac (Q.INST [`e` |-> `h`, `dty` |-> `mty`,
                   `sb` |-> `st`, `shadow_sb` |-> `st'`]
      make_array_slot_full) >>
  (impl_tac >-
    (qunabbrev_tac `packet` >> qunabbrev_tac `prefix` >>
     simp[comp_bind_def, arithmeticTheory.ADD_COMM] >>
     gvs[typeLayoutPropsTheory.type_memory_size_list_sum])) >>
  disch_then assume_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ Qslot _` >>
  rewrite_tac[eval_exprs_cons_action] >>
  irule gas_outcome_full_bind_all >>
  conj_tac >-
    (gen_tac >> BETA_TAC >> irule vyperStorageTraceTheory.storage_trace_frame_bind_all >>
     simp[vyperStorageTraceTheory.evaluate_storage_trace_frame,
          vyperStorageTraceTheory.storage_trace_frame_return]) >>
  conj_tac >- suspend "right_cert" >>
  conj_tac >- suspend "left_cert" >>
  conj_tac >- suspend "head_frame" >>
  qexists_tac `Qslot` >>
  reverse conj_tac >- suspend "exit_packet" >>
  suspend "continuation"
QED

Resume make_array_loop_full[continuation]:
  rpt gen_tac >> strip_tac >>
  `Qslot (storage_trace_horizon mid.storage_trace) res mid G1 tn1 t''` by
    metis_tac[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qpat_x_assum `Qslot _ _ _ _ _ _` mp_tac >>
  simp[Abbr `Qslot`] >> strip_tac >>
  disj1_tac >> goal_assum (drule_at Any) >> BETA_TAC >>
  `expr_sim_inv cenv cx env mid` by
    (qpat_x_assum `!tail. bind _ _ _ = _` (qspec_then `[]` assume_tac) >>
     `expr_body_pre cenv cx env h
        (es with gas_obs := gas_explicit marks s.vs_gas_readings ++ [])` by simp[] >>
     drule_at (Pat `bind _ _ _ = _`)
       (SIMP_RULE (srw_ss() ++ ETA_ss) [] expr_body_pre_eval) >> simp[]) >>
  `body_exprs_full_ok cx args` by
    (qpat_assum `!tail. bind (eval_expr cx h) (read_result cx) _ = _`
       (qspec_then `[]` (assume_tac o SIMP_RULE (srw_ss()) [])) >>
     qpat_assum `(?s tv t s1 v t1. _ /\ _) ==> body_exprs_full_ok cx args` irule >>
     qpat_assum `bind (eval_expr cx h) (read_result cx) _ = (res,_)` mp_tac >>
     qpat_assum `res = INL v` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[vyperStateTheory.bind_def,AllCaseEqs()] >> rpt strip_tac >> metis_tac[]) >>
  `prefix ((dtv,v,base+off,type_memory_size dtv)::ps)
      (off+type_memory_size dtv) t'' tn1` by
    (simp[Abbr `prefix`, exprSimPropsTheory.val_footprint_le] >>
     qpat_x_assum `prefix ps off t'' tn1` mp_tac >>
     simp[listTheory.EVERY_MEM] >>
     strip_tac >> gen_tac >> PairCases_on `e` >> simp[] >>
     strip_tac >> first_x_assum drule >> simp[]) >>
  `sa.cs_next_var <= st.cs_next_var /\ sa.cs_next_id <= st.cs_next_id` by
    (mp_tac (Q.SPECL [`cenv`,`expr_type h`,`h`,`sa`]
       (cj 1 exprLoweringPropsTheory.compile_expr_ci_mono)) >>
     mp_tac (Q.SPECL [`ADD`,`[Var q; Lit (n2w off)]`,`sm`]
       exprLoweringPropsTheory.ci_mono_emit_op) >>
     mp_tac (Q.SPECL [`cenv`,`vv`,`sn`]
       exprLoweringPropsTheory.ci_mono_unwrap_value) >>
     mp_tac (Q.SPECL [`cenv`,`op`,`dst`,`mty`,`lowered_value_type cenv h`,`su`]
       exprLoweringPropsTheory.ci_mono_compile_store_memory) >>
     simp[exprLoweringPropsTheory.ci_mono_def] >> decide_tac) >>
  `local_ptrs_reserved cenv st` by
    metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var] >>
  first_x_assum (qspecl_then [`t`,`t'`,`off+type_memory_size dtv`,
    `(dtv,v,base+off,type_memory_size dtv)::ps`,`st`,`sb`,`st'`,`shadow_sb`,
    `mid`,`t''`,`G1`,`tn1`] mp_tac) >>
  (impl_tac >- suspend "tail_entry") >>
  disch_then assume_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ (eval_exprs cx args) _ Qtail0 _` >>
  `gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 (eval_exprs cx args) (mid,t'',G1,tn1)
    (\hh rr fin Gf tf out. Qtail0 hh rr fin Gf tf out /\
      !id entry. FLOOKUP t''.vs_allocas id = SOME entry ==>
        FLOOKUP out.vs_allocas id = SOME entry)
    (\hh rr fin gt r. expr_exit rr r /\ halt_exit hh cx fin rr r)` by
    (qpat_assum `gas_outcome_full _ _ _ _ (eval_exprs cx args) _ Qtail0 _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp_tac bool_ss [gasOutcomeFullTheory.gas_outcome_full_def] >>
     rpt strip_tac >> qexists_tac `marks`
     >- metis_tac[]
     >- (disj2_tac >> disj1_tac >>
         qexistsl_tac [`res`,`ee`,`r`,`G'`,`tn'`] >> simp[] >>
         rpt strip_tac >> res_tac >> gvs[] >>
         metis_tac[fragGasOriginPtrTheory.gas_origin_ptr_path_projections,
           forPtrAllocationFrameTheory.gas_path_ptr_old_allocations]) >>
     disj2_tac >> disj2_tac >> metis_tac[]) >>
  qpat_x_assum `gas_outcome_full _ _ _ _ (eval_exprs cx args) _ Qtail0 _` kall_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ (eval_exprs cx args) _ Qtail _` >>
  irule gas_outcome_full_bind_all >>
  conj_tac >- simp[vyperStorageTraceTheory.storage_trace_frame_return] >>
  conj_tac >- suspend "tail_right_cert" >>
  conj_tac >- suspend "tail_left_cert" >>
  conj_tac >- simp[vyperStorageTraceTheory.evaluate_storage_trace_frame] >>
  qexists_tac `Qtail` >>
  reverse conj_tac >- suspend "tail_exit" >>
  suspend "tail_return"
QED
Resume make_array_loop_full[tail_entry]:
  simp[] >> rpt conj_tac >> suspend "tail_entry_close"
QED
Resume make_array_loop_full[tail_entry_close]:
  gvs[typeLayoutPropsTheory.type_memory_size_list_sum]
QED
Resume make_array_loop_full[tail_right_cert]:
  BETA_TAC >> rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_bind_values >>
  goal_assum (drule_at Any) >> gvs[]
QED
Resume make_array_loop_full[tail_left_cert]:
  BETA_TAC >> rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_error_values >> simp[]
QED
Resume make_array_loop_full[tail_exit]:
  irule gasOutcomeFullTheory.gas_outcome_full_post_mono >>
  goal_assum (drule_at Any) >> simp[] >>
  POP_ASSUM_LIST (K all_tac) >>
  qx_genl_tac [`Hexit`,`res_exit`,`ee_exit`,`r_exit`] >>
  Cases_on `res_exit` >- simp[exprSimDefsTheory.expr_exit_INL] >>
  Cases_on `r_exit` >> Cases_on `y` >>
  simp[exprSimDefsTheory.expr_exit_def,exprSimDefsTheory.halt_exit_def] >>
  rename1 `Error err` >> Cases_on `err` >>
  simp[exprSimDefsTheory.expr_exit_def,exprSimDefsTheory.halt_exit_def]
QED
Resume make_array_loop_full[tail_return]:
  qx_genl_tac [`tailmarks`,`tailres`,`ee`,`G2`,`tn2`,`u`] >> BETA_TAC >> strip_tac >>
  `Qtail (storage_trace_horizon ee.storage_trace) tailres ee G2 tn2 u` by
    metis_tac[vyperStorageFootprintTheory.storage_trace_domain_def] >>
  qpat_x_assum `Qtail _ _ _ _ _ _` mp_tac >>
  simp[Abbr `Qtail`,Abbr `Qtail0`] >> strip_tac >>
  disj1_tac >> goal_assum (drule_at Any) >> BETA_TAC >>
  `~u.vs_halted` by
    (Q.UNDISCH_TAC `packet sb ee u G2 tn2` >> simp[Abbr `packet`]) >>
  irule gas_outcome_full_pure >> simp[] >>
  qexistsl_tac [`G2`,`ee`,`INL (v::vs)`,`u`,`tn2`] >>
  simp[vyperStateTheory.return_def,fragGasOriginPtrTheory.gas_origin_ptr_path_rules] >>
  suspend "tail_post"
QED
Resume make_array_loop_full[tail_post]:
  gen_tac >> disch_tac >> conj_tac
  >- (Q.UNDISCH_TAC `packet sb ee u G2 tn2` >>
      simp[Abbr `packet`,wb_frame_gas_obs] >>
      POP_ASSUM_LIST (K all_tac) >> rpt strip_tac
      >~ [`storage_well_formed_on _ _ _`]
      >- (res_tac >>
          gvs[vyperStorageFootprintTheory.storage_well_formed_on_def,
              oneline vyperStorageBackendTheory.get_storage_def] >> first_assum ACCEPT_TAC)
      >> (res_tac >> gvs[bodyPtrDefsTheory.ghost_inv_at_def,
            vyperStorageFootprintTheory.storage_well_formed_on_def,
            oneline vyperStorageBackendTheory.get_storage_def] >> first_assum ACCEPT_TAC)) >>
  conj_tac
  >- (Q.UNDISCH_TAC `prefix ps off s tn` >>
      Q.UNDISCH_TAC
        `prefix ((dtv,v,base+off,type_memory_size dtv)::ps)
           (off+type_memory_size dtv) u tn2` >>
      simp[Abbr `prefix`] >> POP_ASSUM_LIST (K all_tac) >>
      simp[listTheory.EVERY_MEM,pairTheory.FORALL_PROD] >> metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >> simp[Once valueEncodingDefsTheory.val_in_memory_def] >>
      Q.UNDISCH_TAC
        `prefix ((dtv,v,base+off,type_memory_size dtv)::ps)
           (off+type_memory_size dtv) u tn2` >>
      simp[Abbr `prefix`] >> strip_tac >> res_tac) >>
  conj_tac
  >- (simp[typeLayoutPropsTheory.type_memory_size_list_sum] >> first_assum ACCEPT_TAC) >>
  suspend "tail_pure"
QED
Resume make_array_loop_full[tail_pure]:
  disch_then (CONJUNCTS_THEN assume_tac) >>
  qpat_assum `~expr_has_effect h ==> _` mp_tac >> simp[] >> strip_tac >>
  qpat_assum `EVERY ($~ o expr_has_effect) args ==> _` mp_tac >> simp[] >> strip_tac >>
  Q.UNDISCH_TAC `packet sa es s G tn` >>
  Q.UNDISCH_TAC `packet st mid t'' G1 tn1` >>
  simp[Abbr `packet`] >> strip_tac >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace)
     ebase.storage_trace` by
    metis_tac[vyperStorageFootprintTheory.storage_trace_domain_def,
              gasOutcomeFullTheory.valid_horizon_append] >>
  `stmt_state_rel (storage_trace_horizon mid.storage_trace)
     ctx func cenv cx ebase sbase` by metis_tac[] >>
  `local_ptrs_rel func cenv ebase.scopes sbase` by
    (Q.UNDISCH_TAC `stmt_state_rel (storage_trace_horizon mid.storage_trace)
       ctx func cenv cx ebase sbase` >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[exprLoweringPropsTheory.stmt_state_rel_def,
          loweringStateRelDefsTheory.state_rel_def]) >>
  `!x w. not_fresh_at csbase x /\ lookup_var x sbase = SOME w ==>
     lookup_var x s = SOME w` by
    (Q.UNDISCH_TAC `wb_frame cenv ebase es csbase sbase s` >>
     POP_ASSUM_LIST (K all_tac) >> simp[loweringPostsTheory.wb_frame_def]) >>
  `!x w. not_fresh_at csbase x /\ lookup_var x sbase = SOME w ==>
     lookup_var x t'' = SOME w` by
    (Q.UNDISCH_TAC `wb_frame cenv ebase mid csbase sbase t''` >>
     POP_ASSUM_LIST (K all_tac) >> simp[loweringPostsTheory.wb_frame_def]) >>
  `!name b n. local_region cenv es.scopes s name b n ==>
     local_region cenv mid.scopes t'' name b n` by
    (rpt strip_tac >>
     `local_region cenv ebase.scopes sbase name b n` by
       (mp_tac (Q.SPECL [`func`,`cenv`,`ebase.scopes`,`sbase`,`csbase`,
           `es.scopes`,`s`,`name`,`b`,`n`]
           exprSimPropsTheory.local_region_frame) >>
        (impl_tac >- simp[]) >> simp[]) >>
     mp_tac (Q.SPECL [`cenv`,`ebase.scopes`,`csbase`,`mid.scopes`,
        `sbase`,`t''`,`name`,`b`,`n`]
        exprSimPropsTheory.local_region_frame_fwd) >>
     (impl_tac >- simp[]) >> simp[]) >>
  conj_tac
  >- (Q.UNDISCH_TAC `!name b n. local_region cenv es.scopes s name b n ==>
        local_region cenv mid.scopes t'' name b n` >>
      Q.UNDISCH_TAC `!name b n. local_region cenv es.scopes s name b n ==>
        mem_bytes_at b n t''.vs_memory = mem_bytes_at b n s.vs_memory` >>
      Q.UNDISCH_TAC `!name b n. local_region cenv mid.scopes t'' name b n ==>
        mem_bytes_at b n u.vs_memory = mem_bytes_at b n t''.vs_memory` >>
      POP_ASSUM_LIST (K all_tac) >> metis_tac[]) >>
  Q.UNDISCH_TAC `!p n. (n+p <= base \/ base+cap <= p) /\
    (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
      sa.cs_next_id <= inst.inst_id /\
      FLOOKUP t''.vs_allocas inst.inst_id = SOME (b,sz) ==>
      loweringStateRelDefs$regions_disjoint p n b sz) ==>
    mem_bytes_at p n t''.vs_memory = mem_bytes_at p n s.vs_memory` >>
  Q.UNDISCH_TAC `!p n. (n+p <= base \/ base+cap <= p) /\
    (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
      st.cs_next_id <= inst.inst_id /\
      FLOOKUP u.vs_allocas inst.inst_id = SOME (b,sz) ==>
      loweringStateRelDefs$regions_disjoint p n b sz) ==>
    mem_bytes_at p n u.vs_memory = mem_bytes_at p n t''.vs_memory` >>
  Q.UNDISCH_TAC `!id entry. FLOOKUP t''.vs_allocas id = SOME entry ==>
    FLOOKUP u.vs_allocas id = SOME entry` >>
  Q.UNDISCH_TAC `sa.cs_next_id <= st.cs_next_id` >>
  POP_ASSUM_LIST (K all_tac) >> disch_tac >> disch_tac >>
  disch_then (fn tail_frame => disch_then (fn head_frame =>
    qx_genl_tac [`p`,`n`] >>
    disch_then (CONJUNCTS_THEN2 assume_tac (fn final_disjoint =>
      `mem_bytes_at p n u.vs_memory = mem_bytes_at p n t''.vs_memory` by
        (irule (Q.SPECL [`p`,`n`] tail_frame) >> reverse conj_tac
         >- first_assum ACCEPT_TAC >>
         rpt gen_tac >> strip_tac >> irule final_disjoint >>
         qexists_tac `inst` >> simp[] >> decide_tac) >>
      `mem_bytes_at p n t''.vs_memory = mem_bytes_at p n s.vs_memory` by
        (irule (Q.SPECL [`p`,`n`] head_frame) >> reverse conj_tac
         >- first_assum ACCEPT_TAC >>
         rpt gen_tac >> strip_tac >> irule final_disjoint >>
         qexists_tac `inst` >> simp[] >> metis_tac[]) >> simp[]))))
QED
Resume make_array_loop_full[right_cert]:
  rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_bind_value >>
  goal_assum (drule_at Any) >> gvs[]
QED
Resume make_array_loop_full[left_cert]:
  rpt strip_tac >> irule gasExemptCertTheory.gas_exempt_cert_error_value >> simp[]
QED
Resume make_array_loop_full[head_frame]:
  irule vyperStorageTraceTheory.storage_trace_frame_bind_all >>
  simp[vyperStorageTraceTheory.evaluate_storage_trace_frame,
       vyperStorageTraceTheory.storage_trace_frame_read_result]
QED
Resume make_array_loop_full[exit_packet]:
  irule gasOutcomeFullTheory.gas_outcome_full_post_mono >>
  goal_assum (drule_at Any) >> simp[] >>
  POP_ASSUM_LIST (K all_tac) >>
  qx_genl_tac [`Hexit`,`res_exit`,`ee_exit`,`r_exit`] >>
  Cases_on `res_exit` >- simp[exprSimDefsTheory.expr_exit_INL] >>
  Cases_on `r_exit` >> Cases_on `y` >>
  simp[exprSimDefsTheory.expr_exit_def,exprSimDefsTheory.halt_exit_def] >>
  rename1 `Error err` >> Cases_on `err` >>
  simp[exprSimDefsTheory.expr_exit_def,exprSimDefsTheory.halt_exit_def]
QED
Finalise make_array_loop_full
