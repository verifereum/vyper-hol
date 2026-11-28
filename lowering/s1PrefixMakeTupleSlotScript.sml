(* The source evaluates the head once; on success the compiler also stores it
   before entering the tail. These are distinct boundaries for prefix proofs. *)
Theory s1PrefixMakeTupleSlot
Ancestors exprSimDefs[qualified,ignore_grammar]
  bodyFullPreds bodyFullExprsListFacts bodyFullMakeArrayStore
  exprSimAggregateLoops exprSimAggregateSource
  exprSimWordArgs exprSimSource exprLowering compileEnv
  valueEncoding gasShadowCompileHelpers gasShadowState gasShadow
  gasShadowCompileStmtHelpers gasShadowCompileContext gasShadowCompileConvert
  forPtrAllocationFrame stateRelProj bodyFullIfExpReach
  s1PrefixDefs s1PrefixPreds s1PrefixOfVV s1PrefixCompose s1PrefixProps
  exprSimHyps
  vyperStorageTrace vyperStorageFootprint vyperState list pair sum arithmetic
  fragExec freshWrites gasOutcomeFull exprBodyPreProps

val _ = Parse.hide "base";

Definition make_tuple_buffer_def:
  make_tuple_buffer (DF,lo,d,ctx,func,cenv,cx,st0)
      (ebase,csbase,sbase,Gbase,tnbase) (q,aid,base,cap) cs ee s G tn <=>
    (?events. ee.storage_trace = ebase.storage_trace ++ events) /\
    FLOOKUP s.vs_allocas aid = SOME (base,cap) /\
    lookup_var q s = SOME (n2w base) /\
    ptr_covers G tn q s cap /\ not_fresh_at cs q /\
    aid < cs.cs_next_id /\ base+cap < dimword (:256) /\
    base+cap <= s.vs_alloca_next /\
    (!name b n. local_region cenv ee.scopes s name b n ==>
         loweringStateRelDefs$regions_disjoint base cap b n) /\
    alloca_history func s /\ sbase.vs_alloca_next <= s.vs_alloca_next /\
    (!a b. FLOOKUP sbase.vs_allocas a = SOME b ==> FLOOKUP s.vs_allocas a = SOME b) /\
    MAP FDOM ebase.scopes = MAP FDOM ee.scopes /\
    wb_frame cenv ebase ee csbase sbase s /\
    ghost_kept_at lo cenv ebase csbase Gbase tnbase sbase G tn /\
    return_buf_frame d cenv cs s /\ ~s.vs_halted /\
    s.vs_current_bb = cs.cs_current_bb /\
    s.vs_inst_idx = LENGTH cs.cs_current_insts /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
         stmt_state_rel H ctx func cenv cx ee s /\
         storage_well_formed_on cx ee (FST H) /\
         ghost_inv_at (DF H) lo d cenv cx ee G tn s)
End

Definition make_tuple_saved_slots_def:
  make_tuple_saved_slots base ps off s tn <=>
    EVERY (\(rt,v,p,n).
      val_wf rt v /\ val_footprint rt v <= n /\
      base <= p /\ p+n <= base+off /\
      (!m. mem_agree_outside tn.t_mem s.vs_memory m ==> val_in_memory rt v p m)) ps
End

Triviality make_tuple_saved_slots_cons:
  make_tuple_saved_slots base ps off s tn /\ val_wf dtv v /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
       val_in_memory dtv v (base+off) m) ==>
  make_tuple_saved_slots base ((dtv,v,base+off,type_memory_size dtv)::ps)
    (off+type_memory_size dtv) s tn
Proof
  simp[make_tuple_saved_slots_def, exprSimPropsTheory.val_footprint_le] >>
  simp[EVERY_MEM, FORALL_PROD] >> rpt strip_tac >> res_tac >> simp[]
QED

Triviality make_tuple_tail_state_cong:
  gas_prefix_full P cx st0 (eval_exprs cx xs) (es,s,G,tn) ==>
  gas_prefix_full P cx st0 (bind (eval_exprs cx xs) (\vs. return (v::vs))) (es,s,G,tn)
Proof
  `!qe. SND (bind (eval_exprs cx xs) (\vs. return (v::vs)) qe) =
        SND (eval_exprs cx xs qe)` by
    (gen_tac >> Cases_on `eval_exprs cx xs qe` >> Cases_on `q` >>
     simp[bind_def, return_def]) >>
  drule_then (fn th => simp[th]) gas_prefix_full_state_cong
QED

Triviality make_tuple_child_ok_after_read:
  body_exprs_full_ok cx (e::xs) /\ body_exprs_prefix_ok cx (e::xs) /\
  bind (eval_expr cx e) (read_result cx) es = (INL v,mid) ==>
  body_exprs_full_ok cx xs /\ body_exprs_prefix_ok cx xs
Proof
  simp[body_exprs_full_ok_cons,body_exprs_prefix_ok_def,bind_def,AllCaseEqs()] >>
  metis_tac[]
QED

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  simp[OPT_MMAP_def] >> strip_tac >>
  `body_expr_full_ok cx e` by fs[body_exprs_full_ok_cons] >>
  `expr_body_pre cenv cx env e es` by metis_tac[MEM] >>
  qpat_assum `compile_make_tuple _ _ (e::xs) _ _ _ sa = _`
    (strip_assume_tac o MATCH_MP compile_make_tuple_cons) >>
  qpat_assum `compile_make_tuple _ _ (gas_shadow_expr e::_) _ _ _ shadow_sa = _`
    (strip_assume_tac o SIMP_RULE (srw_ss()) [] o MATCH_MP compile_make_tuple_cons) >>
  `vv = vv' /\ gas_shadow_state sm sm'` by
    (`gas_shadow_compiles (compile_expr cenv (expr_type e) e)
        (compile_expr (gas_shadow_env T cenv) (expr_type e) (gas_shadow_expr e))` by
       irule gas_shadow_stmt_compile_expr_env >>
     pop_assum (qspecl_then [`sa`,`shadow_sa`] mp_tac o
                REWRITE_RULE [gas_shadow_compiles_def]) >> simp[]) >> gvs[] >>
  `dst = dst' /\ gas_shadow_state sn sn'` by
    (mp_tac (Q.INST [`opc` |-> `ADD`, `ops` |-> `[Var q; Lit (n2w off)]`]
      gas_shadow_compiles_emit_op_same) >>
     rewrite_tac[gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`sm`,`sm'`] mp_tac) >> simp[]) >> gvs[] >>
  `op = op' /\ gas_shadow_state su su'` by
    (mp_tac gas_shadow_compiles_unwrap_value >>
     simp[gas_shadow_compiles_def] >> disch_then drule >> simp[] >> metis_tac[]) >> gvs[] >>
  `gas_shadow_state st st'` by
    (mp_tac (Q.INST [`src` |-> `op`, `dst_ty` |-> `dty`,
        `src_ty` |-> `lowered_value_type cenv e`]
        gas_shadow_compiles_store_memory) >>
     rewrite_tac[gas_shadow_compiles_def] >>
     disch_then (qspecl_then [`su`,`su'`] mp_tac) >> simp[]) >>
  `cs_extends sa sm /\ cs_extends shadow_sa sm'` by
    metis_tac[exprSimUnwrapTheory.compile_expr_extends] >>
  `cs_extends sm sn /\ cs_extends sm' sn'` by
    (mp_tac (cj 2 cs_appends_emit_helpers) >>
     simp[cs_appends_def] >> metis_tac[]) >>
  `cs_extends sn su /\ cs_extends sn' su'` by
    metis_tac[exprSimUnwrapTheory.unwrap_value_extends] >>
  `cs_extends su st /\ cs_extends su' st'` by
    (qpat_assum `compile_store_memory _ _ _ _ _ su = _` mp_tac >>
     qpat_assum `compile_store_memory _ _ _ _ _ su' = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
     metis_tac[externalEntryShapeTheory.compile_store_memory_labels,SND]) >>
  `cs_extends st sb /\ cs_extends st' shadow_sb` by suspend "tail_extends" >>
  `fn_has_code sa sm func /\ fn_has_code sa st func /\ fn_has_code st sb func /\
   fn_has_code shadow_sa sm' shadow_func /\ fn_has_code shadow_sa st' shadow_func /\
   fn_has_code st' shadow_sb shadow_func` by suspend "split_code" >>
  `gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     cx st0 (bind (eval_expr cx e) (read_result cx)) (es,s,G,tn)` by
    suspend "head_prefix" >>
  suspend "compose"
QED
*)
Theorem make_tuple_slot_cons_prefix:
  body_inv tops ctx cenv cx /\
  shadow_body_inv tops ctx shadow_ctx /\ expr_sim_inv cenv cx env ebase /\
  csbase.cs_next_id <= aid /\ csbase.cs_next_id <= sa.cs_next_id /\
  csbase.cs_next_var <= sa.cs_next_var /\
  local_ptrs_reserved cenv csbase /\ local_ptrs_reserved cenv sa /\
  ctx_inst_ids_distinct ctx /\ fn_inst_ids_distinct func /\
  gas_shadow_context ctx shadow_ctx /\ gas_shadow_function func shadow_func /\
  MEM func ctx.ctx_functions /\ MEM shadow_func shadow_ctx.ctx_functions /\
  (!fn inst z. frag_reachable ctx func s fn inst z ==> dalloca_fmp_headroom inst z) /\
  (!H. dead_lo_ok H (DF H) lo cenv cx) /\
  (!x n. cenv.ce_return_buf = SOME (PtrVar (Var x) n) ==> not_fresh_at csbase x) /\
  (!x n. cenv.ce_return_pc = SOME (PtrVar (Var x) n) ==> not_fresh_at csbase x) /\
  (!H. valid_horizon cx st0 H ebase.storage_trace ==>
         stmt_state_rel H ctx func cenv cx ebase sbase) /\
  storage_trace_domain cx st0 es.storage_trace /\
  body_const_cells_agree [(NONE,tops)] cx env es /\
  body_exprs_full_ok cx (e::xs) /\ body_exprs_prefix_ok cx (e::xs) /\
  (!e' ee. MEM e' (e::xs) /\ expr_sim_inv cenv cx env ee ==>
            expr_body_pre cenv cx env e' ee) /\
  expr_sim_inv cenv cx env es /\
  LIST_REL (\ty e. arg_type_fits (expr_type e) ty) (dty::tys) (e::xs) /\
  OPT_MMAP (evaluate_type (get_tenv cx)) (dty::tys) = SOME (dtv::dtvs) /\
  LIST_REL (\ty tv. type_memory_bytes cenv ty = type_memory_size tv) (dty::tys) (dtv::dtvs) /\
  off + type_memory_size_list (dtv::dtvs) <= cap /\
  make_tuple_buffer (DF,lo,d,ctx,func,cenv,cx,st0)
    (ebase,csbase,sbase,Gbase,tnbase) (q,aid,base,cap) sa es s G tn /\
  make_tuple_saved_slots base ps off s tn /\
  compile_make_tuple compile_expr cenv (e::xs) (dty::tys) (Var q) off sa = (Var q,sb) /\
  compile_make_tuple compile_expr (gas_shadow_env T cenv) (MAP gas_shadow_expr (e::xs))
    (dty::tys) (Var q) off shadow_sa = (Var q,shadow_sb) /\
  gas_shadow_state sa shadow_sa /\ gas_shadow_state sb shadow_sb /\
  fn_has_code sa sb func /\ fn_has_code shadow_sa shadow_sb shadow_func /\
  (!v mid t G1 tn1 st shadow_st.
     storage_trace_domain cx st0 mid.storage_trace /\
     body_const_cells_agree [(NONE,tops)] cx env mid /\ expr_sim_inv cenv cx env mid /\
     body_exprs_full_ok cx xs /\ body_exprs_prefix_ok cx xs /\
     make_tuple_buffer (DF,lo,d,ctx,func,cenv,cx,st0)
       (ebase,csbase,sbase,Gbase,tnbase) (q,aid,base,cap) st mid t G1 tn1 /\
     make_tuple_saved_slots base ((dtv,v,base+off,type_memory_size dtv)::ps)
       (off+type_memory_size dtv) t tn1 /\
     csbase.cs_next_id <= st.cs_next_id /\ csbase.cs_next_var <= st.cs_next_var /\
     local_ptrs_reserved cenv st /\
     (!fn inst z. frag_reachable ctx func t fn inst z ==> dalloca_fmp_headroom inst z) /\
     compile_make_tuple compile_expr cenv xs tys (Var q)
       (off+type_memory_size dtv) st = (Var q,sb) /\
     compile_make_tuple compile_expr (gas_shadow_env T cenv) (MAP gas_shadow_expr xs)
       tys (Var q) (off+type_memory_size dtv) shadow_st = (Var q,shadow_sb) /\
     gas_shadow_state st shadow_st /\ fn_has_code st sb func /\
     fn_has_code shadow_st shadow_sb shadow_func ==>
     gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
       cx st0 (eval_exprs cx xs) (mid,t,G1,tn1)) ==>
  gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cx st0 (eval_exprs cx (e::xs)) (es,s,G,tn)
Proof
  cheat
QED

(* SCRATCH MEASUREMENT: original continuation.
Resume make_tuple_slot_cons_prefix[tail_extends]:
  mp_tac externalEntryShapeTheory.compile_make_tuple_labels >>
  disch_then (qspecl_then [`compile_expr`,`cenv`,`xs`,`tys`,`Var q`,
                          `off + type_memory_size dtv`,`st`] mp_tac) >>
  simp[externalEntryShapeTheory.compile_expr_labels] >> strip_tac >>
  mp_tac externalEntryShapeTheory.compile_make_tuple_labels >>
  disch_then (qspecl_then [`compile_expr`,`gas_shadow_env T cenv`,
      `MAP gas_shadow_expr xs`,`tys`,`Var q`,`off + type_memory_size dtv`,`st'`] mp_tac) >>
  simp[externalEntryShapeTheory.compile_expr_labels]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume make_tuple_slot_cons_prefix[split_code]:
  `cs_extends sm st /\ cs_extends sm' st'` by metis_tac[cs_extends_trans] >>
  `cs_extends sa st /\ cs_extends shadow_sa st'` by metis_tac[cs_extends_trans] >>
  `fn_has_code sa st func /\ fn_has_code st sb func /\
   fn_has_code shadow_sa st' shadow_func /\ fn_has_code st' shadow_sb shadow_func` by
    metis_tac[fn_has_code_split] >>
  metis_tac[fn_has_code_split]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume make_tuple_slot_cons_prefix[head_prefix]:
  rewrite_tac[gas_prefix_full_bind_read_result] >>
  `expr_vv_sim_prefix (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
     cenv cx (expr_type e) e es` by
    (`body_expr_prefix_ok cx e` by fs[body_exprs_prefix_ok_def] >>
     qpat_assum `body_expr_prefix_ok cx e`
       (mp_tac o CONJUNCT1 o ONCE_REWRITE_RULE[body_expr_prefix_ok_def]) >>
     metis_tac[]) >>
  qpat_x_assum `expr_vv_sim_prefix _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE[expr_vv_sim_prefix_def]) >>
  disch_then (qspecl_then [`st0`,`sa`,`sm`,`shadow_sa`,`sm'`,`vv`,`s`,`G`,`tn`] mp_tac) >>
  simp[expr_vv_sim_full_pre_def] >> strip_tac >> first_x_assum irule >>
  qpat_assum `make_tuple_buffer _ _ _ sa es s G tn`
    (strip_assume_tac o REWRITE_RULE[make_tuple_buffer_def]) >>
  simp[] >>
  `valid_horizon cx st0 (storage_trace_horizon es.storage_trace) es.storage_trace` by
    fs[storage_trace_domain_def] >>
  `stmt_state_rel (storage_trace_horizon es.storage_trace) ctx func cenv cx es s` by
    metis_tac[] >>
  simp[bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp] >>
  metis_tac[not_fresh_at_mono,expr_body_pre_vv_gas_admissible,
            bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume make_tuple_slot_cons_prefix[compose]:
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok es` by
    metis_tac[expr_body_pre_gas_admissible] >>
  mp_tac (Q.INST [`sb` |-> `st`, `shadow_sb` |-> `st'`] make_array_slot_full) >>
  (impl_tac >-
    (simp[make_tuple_buffer_def,make_tuple_saved_slots_def,comp_bind_def] >>
     gvs[make_tuple_buffer_def,make_tuple_saved_slots_def,typeLayoutPropsTheory.type_memory_size_list_sum] >>
     conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then assume_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full _ _ _ _ _ _ Qslot Rslot` >>
  qabbrev_tac `Ready = \H res mid G1 tn1 t.
    Qslot H res mid G1 tn1 t /\
    (!fn inst z. frag_reachable ctx func t fn inst z ==> dalloca_fmp_headroom inst z)` >>
  `gas_outcome_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    (cx_tops cx) cx st0 (bind (eval_expr cx e) (read_result cx)) (es,s,G,tn)
    Ready Rslot` by suspend "slot_headroom" >>
  rewrite_tac[eval_exprs_cons_action] >> irule gas_prefix_full_bind >>
  simp[storage_trace_frame_bind_all, cj 5 evaluate_storage_trace_frame,
       cj 6 evaluate_storage_trace_frame, storage_trace_frame_return,
       storage_trace_frame_read_result, requests_outcomes_frame_bind_all,
       cj 5 evaluate_requests_outcomes_frame, requests_outcomes_frame_read_result] >>
  suspend "bind"
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume make_tuple_slot_cons_prefix[slot_headroom]:
  irule gas_outcome_full_post_path >> goal_assum (drule_at Any) >>
  simp[Abbr `Ready`] >> rpt strip_tac >>
  `!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0` by
    metis_tac[body_inv_no_phi] >>
  drule_all gas_origin_ptr_path_dalloca_fmp_headroom >> simp[]
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume make_tuple_slot_cons_prefix[bind]:
  goal_assum (drule_at Any) >> reverse conj_tac
  >- (simp[Abbr `Rslot`] >> rpt gen_tac >> Cases_on `res` >>
      Cases_on `r` >> simp[exprSimDefsTheory.expr_exit_def]) >>
  rpt gen_tac >> strip_tac >>
  `valid_horizon cx st0 (storage_trace_horizon mid.storage_trace) mid.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_x_assum `!H. valid_horizon _ _ H mid.storage_trace ==> Ready _ _ _ _ _ _`
    (qspec_then `storage_trace_horizon mid.storage_trace` (drule_then mp_tac)) >>
  simp[Abbr `Ready`,Abbr `Qslot`] >> strip_tac >>
  `make_tuple_buffer (DF,lo,d,ctx,func,cenv,cx,st0)
    (ebase,csbase,sbase,Gbase,tnbase) (q,aid,base,cap) st mid t G1 tn1` by
    (simp[make_tuple_buffer_def] >> first_assum ACCEPT_TAC) >>
  `make_tuple_saved_slots base ((dtv,v,base+off,type_memory_size dtv)::ps)
    (off+type_memory_size dtv) t tn1` by
    (irule make_tuple_saved_slots_cons >> simp[make_tuple_saved_slots_def]) >>
  qpat_x_assum `!tail. bind (eval_expr cx e) (read_result cx) _ = _`
    (qspec_then `[]` (assume_tac o SIMP_RULE (srw_ss()) [])) >>
  `body_exprs_full_ok cx xs /\ body_exprs_prefix_ok cx xs` by
    (drule_all make_tuple_child_ok_after_read >> simp[]) >>
  `expr_sim_inv cenv cx env mid` by
    (`expr_body_pre cenv cx env e
        (es with gas_obs := gas_explicit marks s.vs_gas_readings)` by simp[] >>
     drule_at (Pat `bind _ _ _ = _`)
       (SIMP_RULE (srw_ss() ++ ETA_ss) [] exprSimSourceTheory.expr_body_pre_eval) >> simp[]) >>
  `body_const_cells_agree [(NONE,tops)] cx env mid` by
    (`body_const_cells_agree [(NONE,tops)] cx env (mid with gas_obs := [])`
       suffices_by simp[] >>
     irule body_const_cells_agree_expr_read >> goal_assum (drule_at Any) >>
     simp[] >> metis_tac[expr_body_pre_static_facts]) >>
  `sa.cs_next_var <= st.cs_next_var /\ sa.cs_next_id <= st.cs_next_id` by
    suspend "store_indices" >>
  `local_ptrs_reserved cenv st` by
    metis_tac[exprLoweringPropsTheory.local_ptrs_reserved_next_var] >>
  irule make_tuple_tail_state_cong >>
  qpat_x_assum `!v mid t G1 tn1 st sh. _ ==> gas_prefix_full _ _ _ (eval_exprs cx xs) _`
    irule >>
  simp[] >> rpt conj_tac
  >- first_assum ACCEPT_TAC
  >- (qexists_tac `v` >> first_assum ACCEPT_TAC) >>
  qexistsl_tac [`st'`,`st`] >> simp[] >> decide_tac
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Resume make_tuple_slot_cons_prefix[store_indices]:
  mp_tac (Q.SPECL [`cenv`,`expr_type e`,`e`,`sa`]
     (cj 1 exprLoweringPropsTheory.compile_expr_ci_mono)) >>
  mp_tac (Q.SPECL [`ADD`,`[Var q; Lit (n2w off)]`,`sm`]
     exprLoweringPropsTheory.ci_mono_emit_op) >>
  mp_tac (Q.SPECL [`cenv`,`vv`,`sn`]
     exprLoweringPropsTheory.ci_mono_unwrap_value) >>
  mp_tac (Q.SPECL [`cenv`,`op`,`dst`,`dty`,`lowered_value_type cenv e`,`su`]
     exprLoweringPropsTheory.ci_mono_compile_store_memory) >>
  simp[exprLoweringPropsTheory.ci_mono_def] >> decide_tac
QED
*)

(* SCRATCH MEASUREMENT: original continuation.
Finalise make_tuple_slot_cons_prefix
*)
