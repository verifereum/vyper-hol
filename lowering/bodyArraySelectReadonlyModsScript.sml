(* Linked read-only transport for an owned array selector. *)
Theory bodyArraySelectReadonlyMods
Ancestors exprSimSubscriptArraySource[qualified,ignore_grammar] exprSimPopNestedLocalPath[qualified,ignore_grammar] exprSimDefs[qualified,ignore_grammar]
  bodyArrayOwnedSelectViewMods bodyArrayNoCopyCutsMods bodyArrayNoCopyKeyFramesMods
  bodyFullPostsMods bodyFullShadowBodyInv bodyForRangeScalarFrameMods
  bodyFullHashKeccakFixed bodyFullTargetArrayLoad assignTuplePtrLoadStep exprLoweringProps
  exprSimWordArgs bodyFullUnwrapRun loweringPosts bodyPtrDefs ptrDiscipline
  freshWrites compileEnv venomState stateFrame fragExec gasOutcomeFullMods gasSummary
  vyperStorageFootprint vyperInterpreter vyperState vyperAST context

(* A successful array-length frame changes only fresh variables and the
   instruction cursor.  The linked frames therefore survive the suffix. *)
Theorem array_select_readonly_suffix_mods[local]:
  array_length_frame st2 it Gi tni q Gq tq /\
  stmt_state_rel H ctx func cenv cx fin it /\
  immutable_frame_mods func cenv cx fin it /\
  storage_well_formed_on cx fin (FST H) /\
  ghost_inv_at_mods D lo d cenv cx fin Gi tni it /\
  wb_frame cenv es fin sa s0 it /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 Gi tni /\
  local_ptrs_reserved cenv st2 /\
  sa.cs_next_var <= st2.cs_next_var /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at st2 x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at st2 x) ==>
  stmt_state_rel H ctx func cenv cx fin q /\
  immutable_frame_mods func cenv cx fin q /\
  storage_well_formed_on cx fin (FST H) /\
  ghost_inv_at_mods D lo d cenv cx fin Gq tq q /\
  wb_frame cenv es fin sa s0 q /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 Gq tq /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp q) /\
  q.vs_alloca_next = it.vs_alloca_next /\
  (pure_frame cenv func es sa s0 it ==> pure_frame cenv func es sa s0 q)
Proof
  strip_tac >>
  qpat_assum `array_length_frame _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [array_length_frame_def]) >>
  `q = it with <|vs_vars := q.vs_vars; vs_inst_idx := q.vs_inst_idx|>` by
    (qpat_assum `q with <|vs_vars := _; vs_inst_idx := _|> = it`
       (fn th => CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [GSYM th]))) >> simp[]) >>
  `q.vs_memory = it.vs_memory /\ q.vs_data_section = it.vs_data_section /\
   q.vs_allocas = it.vs_allocas /\ q.vs_alloca_next = it.vs_alloca_next /\
   q.vs_call_ctx = it.vs_call_ctx /\ q.vs_accounts = it.vs_accounts /\
   q.vs_transient = it.vs_transient /\ q.vs_immutables = it.vs_immutables /\
   tq.t_mem = tni.t_mem /\ tq.t_stor = tni.t_stor /\
   tq.t_trans = tni.t_trans /\ tq.t_imm = tni.t_imm` by
    (fs[array_length_frame_def, venom_state_component_equality]) >>
  `!x. not_fresh_at st2 x ==> lookup_var x q = lookup_var x it /\
       FLOOKUP Gq x = FLOOKUP Gi x /\
       op_taint tq (Var x) = op_taint tni (Var x)` by
    (rpt strip_tac >>
     qpat_assum `array_length_frame _ _ _ _ _ _ _` mp_tac >>
     simp[array_length_frame_def] >>
     rpt strip_tac >> simp[op_taint_def] >> metis_tac[]) >>
  `!x. not_fresh_at sa x ==> lookup_var x q = lookup_var x it /\
       FLOOKUP Gq x = FLOOKUP Gi x /\
       op_taint tq (Var x) = op_taint tni (Var x)` by
    (rpt strip_tac >>
     `not_fresh_at st2 x` by metis_tac[not_fresh_at_mono] >>
     first_x_assum drule >> simp[] >> metis_tac[]) >>
  `state_frame q = state_frame (it with vs_inst_idx := q.vs_inst_idx)` by
    (rw[state_frame_eq_reconstruct] >>
     qpat_assum `q with <|vs_vars := _; vs_inst_idx := _|> = it`
       (fn th => once_rewrite_tac [GSYM th]) >> simp[]) >>
  `stmt_state_rel H ctx func cenv cx fin q` by
    (irule stmt_state_rel_old_vars_frame_ptr >> (metisTools.METIS_TAC [])) >>
  `immutable_frame_mods func cenv cx fin q` by
    (irule immutable_frame_mods_exterior_frame >> (metisTools.METIS_TAC [])) >>
  `ghost_inv_at_mods D lo d cenv cx fin Gq tq q` by
    (irule ghost_inv_at_mods_exterior_frame >>
     qexistsl [`Gi`,`fin`,`it`,`st2`,`tni`] >>
     (metisTools.METIS_TAC [])) >>
  `wb_frame cenv es fin sa s0 q` by
    (irule wb_frame_readonly_tail >> simp[] >> metis_tac[]) >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 Gq tq` by
    (irule ghost_kept_at_clean_suffix >>
     qexistsl [`Gi`,`tni`] >>
     (conj_tac >-
       (rpt strip_tac >>
        first_x_assum drule >>
        metisTools.METIS_TAC [])) >>
     (conj_tac >-
       (qpat_assum `tq.t_mem = tni.t_mem`
          (fn th => rw[th] >>
           metisTools.METIS_TAC [pred_setTheory.SUBSET_REFL])) >-
       (metisTools.METIS_TAC []))) >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp q` by
    metisTools.METIS_TAC [stmt_state_rel_allocas_below_fmp] >>
  simp[] >>
  strip_tac >>
  drule_all_then (fn th => fs[th]) pure_frame_state_cong
QED

Theorem array_select_readonly_frames_mods:
  stmt_state_rel H ctx func cenv cx fin it /\
  immutable_frame_mods func cenv cx fin it /\
  storage_well_formed_on cx fin (FST H) /\
  ghost_inv_at_mods D lo d cenv cx fin Gi tni it /\
  wb_frame cenv es fin sa s0 it /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 Gi tni /\
  array_length_frame st2 it Gi tni q Gq tq /\
  local_ptrs_reserved cenv st2 /\
  sa.cs_next_var <= st2.cs_next_var /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at st2 x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at st2 x) /\
  (!x. not_fresh_at sa x ==> lookup_var x it = lookup_var x s0) /\
  it.vs_alloca_next = q.vs_alloca_next /\
  (allocas_below_fmp it ==> allocas_below_fmp q) /\
  it.vs_current_bb = st2.cs_current_bb /\
  it.vs_inst_idx = LENGTH st2.cs_current_insts ==>
  stmt_state_rel H ctx func cenv cx fin q /\
  immutable_frame_mods func cenv cx fin q /\
  storage_well_formed_on cx fin (FST H) /\
  ghost_inv_at_mods D lo d cenv cx fin Gq tq q /\
  wb_frame cenv es fin sa s0 q /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 Gq tq /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp q)
Proof
  strip_tac >>
  drule_all_then strip_assume_tac (GEN_ALL array_select_readonly_suffix_mods) >>
  asm_rewrite_tac[]
QED

Theorem array_owned_raw_success_post_mods:
  array_length_frame st2 it Gi tni q Gq tq /\
  stmt_state_rel H ctx func cenv cx fin it /\
  immutable_frame_mods func cenv cx fin it /\
  storage_well_formed_on cx fin (FST H) /\
  ghost_inv_at_mods D lo d cenv cx fin Gi tni it /\
  wb_frame cenv es fin sa s0 it /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 Gi tni /\
  local_ptrs_reserved cenv st2 /\
  sa.cs_next_var <= st2.cs_next_var /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at st2 x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at st2 x) /\
  (~expr_has_effect (Subscript et obj idx) ==> pure_frame cenv func es sa s0 it) /\
  s0.vs_alloca_next <= it.vs_alloca_next /\
  q.vs_current_bb = sb.cs_current_bb /\ q.vs_inst_idx = LENGTH sb.cs_current_insts /\
  alloca_history func q /\
  (let vv = LocatedValue et (mk_ptr dst LocMemory) in
     vv_holds cenv cx et (Value child) vv fin q /\
     vv_at cenv cx et sa sb fin (Value child) vv q /\
     vv_store_bound cx et et fin (Value child) vv q /\
     ptr_vv_ok cx et (Value child) vv fin Gq tq q /\
     (~is_word_type et /\ ~is_bytestring_type et ==>
       vv_own cenv cx et sa sb fin (Value child) vv q) /\
     ptr_buf_ok cenv (Subscript et obj idx) dst Gq q)
  ==>
  let vv = LocatedValue et (mk_ptr dst LocMemory) in
    vv_post_mods H ctx func cenv cx (Subscript et obj idx) es sa sb s0 fin (Value child) vv q /\
    vv_store_bound cx et et fin (Value child) vv q /\
    q.vs_current_bb = sb.cs_current_bb /\ q.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func q /\ (ctx_has_dalloca ctx ==> allocas_below_fmp q) /\
    s0.vs_alloca_next <= q.vs_alloca_next /\
    ghost_inv_at_mods D lo d cenv cx fin Gq tq q /\
    ptr_vv_ok cx et (Value child) vv fin Gq tq q /\
    (~is_word_type et /\ ~is_bytestring_type et ==>
      vv_own cenv cx et sa sb fin (Value child) vv q) /\
    ptr_buf_ok cenv (Subscript et obj idx) dst Gq q /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 Gq tq
Proof
  strip_tac >>
  drule_all_then strip_assume_tac (GEN_ALL array_select_readonly_suffix_mods) >>
  qpat_assum `wb_frame cenv es fin sa s0 q`
    (strip_assume_tac o REWRITE_RULE [wb_frame_def]) >>
  fs[vv_post_mods_def,vv_holds_mods_def,vv_place_ptr_mods_def,
     vv_place_ptr_def,mk_ptr_def,expr_type_def] >>
  rpt strip_tac >>
  qpat_assum `!aid off sz. _ ==> mem_bytes_at off sz q.vs_memory = _`
    irule >>
  asm_rewrite_tac[] >>
  qexists `aid` >> asm_rewrite_tac[]
QED

(* Package a raw Value selector run as the linked selector outcome.  The
   physical run is deliberately supplied as a witness packet; this theorem
   only transports its entry-relative resources. *)
Theorem array_owned_run_outcome_mods:
  explicit = gas_explicit_sites ctx shadow_ctx /\
  array_owned_select_run_mods (lo,explicit,ctx,func,PG) cenv cx
      (et,bd,obj,idx) (sa,st2,sb,dst) (v,key) (fin,it,Gi,tni) /\
  fin.gas_obs = [] /\
  storage_trace_domain cx st0 fin.storage_trace /\
  wb_frame cenv es fin sa s0 it /\
  (~expr_has_effect (Subscript et obj idx) ==> pure_frame cenv func es sa s0 it) /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 Gi tni /\
  (!H. valid_horizon cx st0 H fin.storage_trace ==>
     stmt_state_rel H ctx func cenv cx fin it /\
     immutable_frame_mods func cenv cx fin it /\
     storage_well_formed_on cx fin (FST H) /\
     ghost_inv_at_mods (DF H) lo d cenv cx fin Gi tni it) /\
  local_ptrs_reserved cenv st2 /\
  sa.cs_next_var <= st2.cs_next_var /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at st2 x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at st2 x) /\
  s0.vs_alloca_next <= it.vs_alloca_next /\
  it.vs_current_bb = st2.cs_current_bb /\
  it.vs_inst_idx = LENGTH st2.cs_current_insts /\
  ~it.vs_halted
  ==>
  array_select_outcome_mods (DF,lo,d,ctx,shadow_ctx,PG,func)
      cenv cx et obj idx et bd st0
      (es,s0,G0,tn0) (sa,sb,dst,LocMemory) (Value v,key)
      (fin,it,Gi,tni)
Proof
  strip_tac >>
  qpat_x_assum `array_owned_select_run_mods _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[array_owned_select_run_mods_def] >>
  disch_then (qx_choosel_then [`res`,`r`,`Gq`,`tq`]
    (map_every assume_tac o CONJUNCTS)) >>
  (pop_assum DISJ_CASES_TAC) >-
    (qpat_x_assum `?q. r = Abort Revert_abort q /\ _`
       (qx_choosel_then [`q`] (map_every assume_tac o CONJUNCTS)) >>
     rewrite_tac[array_select_outcome_mods_def] >>
     simp[] >>
     irule gasOutcomeFullPostModsTheory.gas_outcome_full_mods_exit >>
     conj_tac
     >- (qexistsl [`Gq`,`fin`,`r`,`res`,`tq`] >>
         conj_tac
         >- simp[]
         >- (conj_tac
             >- (rpt gen_tac >> strip_tac >>
                 conj_tac
                 >- metisTools.METIS_TAC []
                 >- simp[exprSimDefsTheory.expr_exit_def,
                         exprSimDefsTheory.halt_exit_def])
             >- simp[fragExecTheory.exit_result_def]))
     >- simp[]) >-
    (qpat_x_assum `?q child. r = OK q /\ _`
       (qx_choosel_then [`q`,`child`] (map_every assume_tac o CONJUNCTS)) >>
     rewrite_tac[array_select_outcome_mods_def] >>
     simp[] >>
     irule gasOutcomeFullPostModsTheory.gas_outcome_full_mods_pure >>
     conj_tac
     >- (qexistsl [`Gq`,`fin`,`res`,`q`,`tq`] >>
         conj_tac
         >- simp[]
         >- (rpt gen_tac >> strip_tac >>
             conj_tac
             >- metisTools.METIS_TAC []
             >- (simp[] >>
                 qpat_assum `!H. valid_horizon _ _ H _ ==> _`
                   (drule_then strip_assume_tac) >>
                 `fin with gas_obs := [] = fin` by
                   simp[vyperStateTheory.evaluation_state_component_equality] >>
                 drule_all_then mp_tac (GEN_ALL array_owned_raw_success_post_mods) >>
                 simp[mk_ptr_def,expr_type_def,exprLoweringTheory.lowered_value_type_def,
                      vv_location_def])))
     >- simp[])
QED
