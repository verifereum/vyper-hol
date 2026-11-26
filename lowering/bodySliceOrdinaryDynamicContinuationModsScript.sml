(* Install a dynamic Slice capture and retain its typed payload through both reads. *)
Theory bodySliceOrdinaryDynamicContinuationMods
Ancestors
  bodySliceDynamicCaptureMods bodySliceOrdinaryDynamicLandingMods
  bodySliceWordEntryMods bodyExtractSavedDescriptorMods
  exprSimWordArgs stmtSimLogArgs exprOperandVar exprSimProps
  freshWrites bodyFullHashKeccakFixed bodyFullIfExpReach bodyPtrDefs venomInst
  bodyFullPostsMods loweringPosts loweringStateRelDefs exprLoweringProps
  vyperStorageFootprint vyperTypeExprSoundness vyperTypeValues valueCopyBytes
  compileEnv ptrDiscipline venomState vyperValue vyperTyping words
Libs horizonTypeLib

val entry = ``\es sa s0 G0 tn0.
  local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
  (!fn inst u. frag_reachable ctx func s0 fn inst u ==> dalloca_fmp_headroom inst u) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\ immutable_frame_mods func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\ s0.vs_inst_idx = LENGTH sa.cs_current_insts``;

val clean = ``\b (bs:word8 list) tn. !j. b <= j /\ j < b + LENGTH bs ==> j NOTIN tn.t_mem``;
val payload = ``\op bt v sa a es s q bs tn.
  expr_val_at cenv cx (BaseT bt) sa a es v op s /\
  eval_operand op s = SOME q /\
  mem_bytes_at (w2n q + 32) (LENGTH bs) s.vs_memory = bs /\
  ^clean (w2n q + 32) bs tn``;

Triviality dynamic_read_payload:
  ^payload op bt v sa a ea s q bs tn /\
  is_bytestring_type (BaseT bt) /\
  evaluate_type (get_tenv cx) (BaseT bt) = SOME tv /\
  32 + LENGTH bs <= val_footprint tv v /\
  (!z. op = Var z ==> not_fresh_at a z) /\ (!l. op <> Label l) /\
  stmt_state_rel (H:(bool # bytes32 # type_value) list # num list) ctx func cenv cx ea s /\
  local_ptrs_reserved cenv a /\ MAP FDOM ea.scopes = MAP FDOM eb.scopes /\
  a.cs_next_id <= b.cs_next_id /\
  expr_post_mods H ctx func cenv cx arg ea a b s eb w x t /\
  ghost_kept_at lo cenv ea a (G:string |-> num # num) tn s G' tn' /\
  expr_sim_inv_mods mods cenv cx env ea ==>
  ^payload op bt v sa b eb t q bs tn'
Proof
  BETA_TAC >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_post_mods_def]) >>
  drule_then assume_tac expr_post_frame >>
  `log_arg_clear cenv cx (BaseT bt) v` by
    (rw[log_arg_clear_def] >> drule evaluate_type_BaseT_cases >> strip_tac >> gvs[] >>
     `dynarray_free (BaseTV btv)` by simp[dynarray_free_base] >>
     drule_all extract_local_window_apart >> simp[]) >>
  qpat_assum `ghost_kept_at _ _ _ _ _ _ _ _ _`
    (mp_then Any mp_tac
      (horizonTypeLib.at_horizon_named "H" (BETA_RULE slice_ordinary_dynamic_landing_mods))) >>
  disch_then irule >>
  qpat_assum `stmt_state_rel _ _ _ _ _ ea s` (irule_at Any) >>
  asm_rewrite_tac[] >> qexists_tac `tv` >> asm_rewrite_tac[]
QED

Theorem slice_ordinary_dynamic_continuation_mods:
  compile_bytestring_src op sm = ((limit,data),sc) /\
  fn_has_code sm sc func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sc /\ ci_mono sm sc /\
  lower_value compile_expr cenv (expr_type src) src sa = (op,sm) /\
  local_ptrs_reserved cenv sa /\
  expr_type src = BaseT bt /\ is_bytestring_type (BaseT bt) /\
  value_runtime_typed env (expr_type src) v /\
  storage_trace_domain cx st0 ec.storage_trace /\
  (!H. valid_horizon cx st0 H ec.storage_trace ==>
    expr_post_mods H ctx func cenv cx src es sa sm s0 ec v op sms /\
    ptr_val_ok cx (post_value_type cenv src) v op Gm tm sms) /\
  ^entry ec sm sms Gm tm /\
  (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) ==>
  ?scs Gc tc lp root p bs.
    ((v = BytesV bs) \/ (?str. v = StringV str /\ bs = MAP (n2w o ORD) str)) /\
    limit = Var lp /\ data = Var root /\
    not_fresh_at sc lp /\ not_fresh_at sc root /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (sms,Gm,tm) [] (OK scs,Gc,tc)) /\
    ^entry ec sc scs Gc tc /\
    eval_operand limit scs = SOME (n2w (LENGTH bs)) /\
    op_taint tc limit = {} /\ op_prov Gc limit = NONE /\
    lookup_var root scs = SOME p /\ ptr_covers Gc tc root scs (LENGTH bs) /\
    w2n p + LENGTH bs < dimword (:256) /\ w2n p + LENGTH bs <= scs.vs_alloca_next /\
    (!x. not_fresh_at sm x ==> lookup_var x scs = lookup_var x sms /\
       FLOOKUP Gc x = FLOOKUP Gm x /\ op_taint tc (Var x) = op_taint tm (Var x)) /\
    scs.vs_memory = sms.vs_memory /\ scs.vs_allocas = sms.vs_allocas /\
    scs.vs_alloca_next = sms.vs_alloca_next /\ tc.t_mem = tm.t_mem /\
    (!H sd se start len e1 e2 v1 v2 op1 op2 sds ses Gd Ge td te env1.
      valid_horizon cx st0 H ec.storage_trace /\
      expr_sim_inv_mods mods cenv cx env ec /\ expr_sim_inv_mods mods cenv cx env1 e1 /\
      local_ptrs_reserved cenv sd /\ ci_mono sc sd /\ ci_mono sd se /\
      MAP FDOM ec.scopes = MAP FDOM e1.scopes /\ MAP FDOM e1.scopes = MAP FDOM e2.scopes /\
      expr_post_mods H ctx func cenv cx start ec sc sd scs e1 v1 op1 sds /\
      expr_post_mods H ctx func cenv cx len e1 sd se sds e2 v2 op2 ses /\
      ghost_kept_at lo cenv ec sc Gc tc scs Gd td /\
      ghost_kept_at lo cenv e1 sd Gd td sds Ge te ==>
      mem_bytes_at (w2n p) (LENGTH bs) ses.vs_memory = bs /\ ^clean (w2n p) bs te)
Proof
  BETA_TAC >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `evaluate_type (get_tenv cx) (BaseT bt) = SOME (BaseTV bt) /\ value_has_type (BaseTV bt) v` by
    (qpat_assum `value_runtime_typed _ _ _` (strip_assume_tac o REWRITE_RULE [value_runtime_typed_def]) >>
     Cases_on `bt` >> gvs[is_bytestring_type_def,evaluate_type_def,AllCaseEqs()] >>
     rename1 `BytesT bd` >> Cases_on `bd` >> gvs[is_bytestring_type_def,evaluate_type_def,AllCaseEqs()]) >>
  `post_value_type cenv src = BaseT bt` by simp[post_value_type_bytestring] >>
  `valid_horizon cx st0 (storage_trace_horizon ec.storage_trace) ec.storage_trace` by
    fs[storage_trace_domain_def] >>
  `ptr_val_ok cx (BaseT bt) v op Gm tm sms` by
    (qpat_assum `!H. valid_horizon _ _ _ _ ==> expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (qspec_then `storage_trace_horizon ec.storage_trace` (drule_then strip_assume_tac)) >>
     qpat_assum `post_value_type cenv src = BaseT bt` (SUBST1_TAC o SYM) >>
     first_assum ACCEPT_TAC) >>
  `!H. valid_horizon cx st0 H ec.storage_trace ==>
    expr_post_mods H ctx func cenv cx src es sa sm s0 ec v op sms /\
    storage_well_formed_on cx ec (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx ec Gm tm sms` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ _ _ ==> expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (drule_then strip_assume_tac) >>
     qpat_assum `!H. valid_horizon _ _ _ _ ==> stmt_state_rel _ _ _ _ _ _ sms /\ _`
       (drule_then strip_assume_tac) >> asm_rewrite_tac[]) >>
  `!x. op = Var x ==> not_fresh_at sm x` by (drule compile_lower_value_var >> simp[]) >>
  qmatch_asmsub_rename_tac `expr_post_mods _ ctx func cenv cx e es0 sa sm s0 ec v op s` >>
  qmatch_asmsub_rename_tac `ptr_val_ok _ (BaseT _) _ _ G tn s` >>
  mp_tac (Q.INST [`ce` |-> `cenv`, `es` |-> `ec`, `tv` |-> `BaseTV bt`]
    slice_dynamic_capture_source_run_mods) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choosel_then [`scs`,`Gc`,`tc`,`lp`,`root`,`p`,`bs`]
    (map_every assume_tac o CONJUNCTS)) >>
  suspend "install"
QED

Resume slice_ordinary_dynamic_continuation_mods[install]:
  `^entry ec sc scs Gc tc` by
    (BETA_TAC >> asm_rewrite_tac[] >> rpt conj_tac
     >- (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sm` >> fs[ci_mono_def])
     >- (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sm` >> fs[ci_mono_def])
     >- (qpat_assum `!H. valid_horizon _ _ _ _ ==> stmt_state_rel _ _ _ _ _ _ scs /\ _`
           (qspec_then `storage_trace_horizon ec.storage_trace` (drule_then strip_assume_tac)) >>
         qpat_assum `stmt_state_rel _ _ _ _ _ _ scs`
           (mp_then Any ACCEPT_TAC stmt_state_rel_allocas_below_fmp)) >>
     qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) [] _`
       (qspec_then `DF (storage_trace_horizon ec.storage_trace)` mp_tac) >>
     disch_then (mp_then Any mp_tac gas_origin_ptr_path_dalloca_fmp_headroom) >>
     asm_rewrite_tac[]) >>
  qpat_x_assum `?q raw. _` (qx_choosel_then [`q`,`raw`] (map_every assume_tac o CONJUNCTS)) >>
  qpat_x_assum `scs = raw with vs_inst_idx := _` kall_tac >>
  qpat_x_assum `p = q + 32w` kall_tac >>
  suspend "placement"
QED

Resume slice_ordinary_dynamic_continuation_mods[placement]:
  `32 + LENGTH bs <= val_footprint (BaseTV bt) v` by
    (qpat_assum `v = BytesV bs \/ _` strip_assume_tac >>
     Cases_on `bt` >> gvs[is_bytestring_type_def,val_footprint_def,value_has_type_def] >>
     rename1 `BytesT bd` >> Cases_on `bd` >>
     gvs[is_bytestring_type_def,val_footprint_def,value_has_type_def]) >>
  `!l. op <> Label l` by
    (`~is_word_type (BaseT bt)` by simp[is_bytestring_word_type] >>
     `ptr_mem_ok cx (BaseT bt) v op G tn s` by fs[ptr_val_ok_def] >>
     qpat_x_assum `ptr_mem_ok _ _ _ _ _ _ _`
       (qspecl_then [`BaseTV bt`,`q`] mp_tac o REWRITE_RULE [ptr_mem_ok_def]) >>
     asm_rewrite_tac[] >> strip_tac >>
     `val_footprint (BaseTV bt) v <> 0` by decide_tac >>
     first_x_assum (drule_then strip_assume_tac) >> simp[]) >>
  `wb_frame cenv ec ec sm s scs` by
    (pure_rewrite_tac [wb_frame_def] >> rpt conj_tac
     >- (rpt strip_tac >> qpat_assum `!x. not_fresh_at sm x ==> _`
           (drule_then strip_assume_tac) >> metis_tac[])
     >- (rpt strip_tac >> asm_rewrite_tac[])
     >- (rpt strip_tac >> asm_rewrite_tac[]) >>
     irule locals_kept_mem >> asm_rewrite_tac[]) >>
  `^payload op bt v sa sc ec scs q bs tc` by
    (BETA_TAC >>
     qpat_assum `w2n p = w2n q + 32` (pure_once_rewrite_tac o single o SYM) >>
     asm_rewrite_tac[] >> conj_tac
     >- (qpat_assum `!H. valid_horizon _ _ _ _ ==> expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
           (qspec_then `storage_trace_horizon ec.storage_trace` (drule_then strip_assume_tac)) >>
         qhdtm_x_assum `expr_post_mods` (strip_assume_tac o REWRITE_RULE [expr_post_mods_def]) >>
         qhdtm_x_assum `expr_post` (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
         qpat_assum `post_value_type cenv e = BaseT bt`
           (fn th => qpat_assum `expr_val_at _ _ _ sa sm ec v op s`
             (assume_tac o PURE_REWRITE_RULE [th])) >>
         qpat_assum `ci_mono sm sc` (strip_assume_tac o REWRITE_RULE [ci_mono_def]) >>
         qpat_assum `stmt_state_rel _ _ _ _ _ ec s` (mp_then Any mp_tac log_frame_placement) >>
         disch_then irule >> asm_rewrite_tac[] >> qexistsl_tac [`ec`,`sm`] >>
         asm_rewrite_tac[]) >>
     irule log_frame_operand >>
     qpat_assum `wb_frame _ _ _ sm s scs` (irule_at Any) >> asm_rewrite_tac[]) >>
  suspend "reads"
QED

Resume slice_ordinary_dynamic_continuation_mods[reads]:
  qexistsl_tac [`scs`,`Gc`,`tc`,`lp`,`root`,`p`,`bs`] >>
  qpat_assum `^entry ec sc scs Gc tc` (strip_assume_tac o BETA_RULE) >>
  asm_rewrite_tac[] >> rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `^payload op bt v sa sc ec scs q bs tc` (strip_assume_tac o BETA_RULE) >>
  `stmt_state_rel H ctx func cenv cx ec scs` by
    (qpat_assum `!H. valid_horizon _ _ _ _ ==> stmt_state_rel _ _ _ _ _ _ scs /\ _`
       (qspec_then `H` (drule_then strip_assume_tac)) >> first_assum ACCEPT_TAC) >>
  `!x. op = Var x ==> not_fresh_at sc x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sm` >> fs[ci_mono_def]) >>
  `!x. op = Var x ==> not_fresh_at sd x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sc` >> fs[ci_mono_def]) >>
  rpt (qhdtm_x_assum `ci_mono` (strip_assume_tac o REWRITE_RULE [ci_mono_def])) >>
  `^payload op bt v sa sd e1 sds q bs td` by
    (BETA_TAC >> qpat_assum `expr_post_mods H _ _ _ _ start _ _ _ _ _ _ _ _`
       (mp_then Any mp_tac (BETA_RULE dynamic_read_payload)) >>
     disch_then irule >> asm_rewrite_tac[] >> rpt conj_tac
     >- (qexists_tac `BaseTV bt` >> asm_rewrite_tac[])
     >- (qexistsl_tac [`env`,`mods`] >> first_assum ACCEPT_TAC) >>
     qpat_assum `ghost_kept_at _ _ ec sc Gc tc _ _ _` (irule_at Any) >> asm_rewrite_tac[]) >>
  qpat_x_assum `^payload op bt v sa sd e1 sds q bs td` (strip_assume_tac o BETA_RULE) >>
  `stmt_state_rel H ctx func cenv cx e1 sds` by
    (qpat_assum `expr_post_mods H _ _ _ _ start _ _ _ _ _ _ _ _`
      (strip_assume_tac o REWRITE_RULE [expr_post_mods_def]) >>
     drule_then ACCEPT_TAC expr_post_state) >>
  `^payload op bt v sa se e2 ses q bs te` by
    (BETA_TAC >> qpat_assum `expr_post_mods H _ _ _ _ len _ _ _ _ _ _ _ _`
       (mp_then Any mp_tac (BETA_RULE dynamic_read_payload)) >>
     disch_then irule >> asm_rewrite_tac[] >> rpt conj_tac
     >- (qexists_tac `BaseTV bt` >> asm_rewrite_tac[])
     >- (qexistsl_tac [`env1`,`mods`] >> first_assum ACCEPT_TAC) >>
     qpat_assum `ghost_kept_at _ _ e1 sd Gd td _ _ _` (irule_at Any) >> asm_rewrite_tac[]) >>
  qpat_x_assum `^payload op bt v sa se e2 ses q bs te` (strip_assume_tac o BETA_RULE) >>
  asm_rewrite_tac[]
QED

Finalise slice_ordinary_dynamic_continuation_mods
