Theory exprExtRequestAllocationEndpoint
Ancestors
  exprExtRequestMaterialize exprSimCopy exprSimStorageCopy loweringHalt exprSimAlloc
  exprExtRequestHistoryCompose exprExtRequestHistory
  exprSimProps exprLoweringProps fragGasSeq fragGasMode fragGasFresh
  freshWrites context compileEnv loweringStateRelDefs emitHelper emitHelperProps
  venomInst venomInstProofs venomExecSemantics venomState list rich_list
  arithmetic fragExec

Theorem extrequest_allocation_endpoint:
  compile_alloc_buffer sz sn = (buf,mid) /\ fn_has_code sn mid func /\
  stmt_state_rel ctx func cenv cx ee t /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sn /\ sz < dimword (:256) /\
  ~t.vs_halted /\ t.vs_current_bb = sn.cs_current_bb /\
  t.vs_inst_idx = LENGTH sn.cs_current_insts ==>
  ?u w. gas_marked_path F ctx func t 0 (OK u) /\
    stmt_state_rel ctx func cenv cx ee u /\
    extrequest_history_frame cenv cx ee sn t ee mid u /\
    ~u.vs_halted /\ u.vs_current_bb = mid.cs_current_bb /\
    u.vs_inst_idx = LENGTH mid.cs_current_insts /\
    eval_operand buf.buf_operand u = SOME w /\
    FLOOKUP u.vs_allocas sn.cs_next_id = SOME (w2n w,sz) /\
    w2n w + sz < dimword (:256) /\ u.vs_memory = t.vs_memory /\
    contract_storage u = contract_storage t /\
    contract_transient u = contract_transient t /\ u.vs_labels = t.vs_labels /\
    (!x. not_fresh_at sn x ==> lookup_var x u = lookup_var x t) /\
    (!aid entry. FLOOKUP t.vs_allocas aid = SOME entry ==>
       FLOOKUP u.vs_allocas aid = SOME entry) /\
    local_ptrs_reserved cenv mid /\ ci_mono sn mid /\
    (?p. buf.buf_operand = Var p /\ not_fresh_at mid p) /\
    (!aid b len. aid < sn.cs_next_id /\ FLOOKUP t.vs_allocas aid = SOME (b,len) ==>
       regions_disjoint (w2n w) sz b len) /\
    (!name b len. local_region cenv ee.scopes t name b len ==>
       regions_disjoint (w2n w) sz b len) /\
    (!name b len. local_region cenv ee.scopes u name b len ==>
       regions_disjoint (w2n w) sz b len) /\
    (cenv.ce_is_ctor ==> !name tv v off.
       FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
       FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
         | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (tv,v) ==>
       regions_disjoint (w2n w) sz off (type_memory_size tv))
Proof
  strip_tac >>
  drule_all extrequest_allocation_history >> strip_tac >>
  drule storage_copy_alloc_layout >> strip_tac >>
  `~t'.vs_halted /\ t'.vs_current_bb = mid.cs_current_bb /\
   contract_storage t' = contract_storage t /\
   contract_transient t' = contract_transient t /\ t'.vs_labels = t.vs_labels` by
    (qpat_x_assum `run_inst_seq _ _ = OK _` mp_tac >>
     simp[run_inst_seq_def, venomInstTheory.mk_inst_def,
       step_inst_base_def, eval_operand_def] >>
     simp[AllCaseEqs(), update_var_def, same_blocks_def] >>
     strip_tac >> gvs[exec_alloca_def, AllCaseEqs(), update_var_def,
       same_blocks_def, contract_storage_def, contract_transient_def]) >>
  `gas_marked_path F ctx func t 0
     (OK (t' with vs_inst_idx := LENGTH mid.cs_current_insts))` by
    (irule extrequest_straight_run_path >> simp[] >> qexists_tac `sn` >> simp[] >>
     conj_tac >- (qpat_x_assum `isPREFIX _ _` mp_tac >>
       simp[rich_listTheory.IS_PREFIX_APPEND] >> strip_tac >>
       fs[emitted_insts_def, listTheory.DROP_APPEND]) >>
     simp[venomInstTheory.mk_inst_def, is_terminator_def]) >>
  qabbrev_tac `u = t' with vs_inst_idx := LENGTH mid.cs_current_insts` >>
  `stmt_state_rel ctx func cenv cx ee u /\
   extrequest_history_frame cenv cx ee sn t ee mid u /\
   eval_operand buf.buf_operand u = SOME w /\
   ~u.vs_halted /\ u.vs_current_bb = mid.cs_current_bb /\
   u.vs_inst_idx = LENGTH mid.cs_current_insts` by
    (simp[Abbr `u`, stmt_state_rel_inst_idx, eval_operand_def, lookup_var_def] >>
     gvs[extrequest_history_frame_def, local_region_def, lookup_var_def]) >>
  `ci_mono sn mid` by
    (qspecl_then [`sz`, `sn`] mp_tac ci_mono_compile_alloc_buffer >> simp[]) >>
  `local_ptrs_reserved cenv mid` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sn` >> gvs[ci_mono_def]) >>
  `!name b len. local_region cenv ee.scopes t name b len ==>
       regions_disjoint (w2n w) sz b len` by
    (rpt strip_tac >> first_x_assum irule >>
     metis_tac[extrequest_history_local_regions]) >>
  `MEM (mk_inst sn.cs_next_id ALLOCA [Lit (n2w sz)]
        [STRING #"%" (toString sn.cs_next_var)]) (fn_insts func)` by
    metis_tac[exprSimAllocTheory.buffer_alloc_code] >>
  `(cenv.ce_is_ctor ==> !name tv v off.
     FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
     FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
       | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (tv,v) ==>
     regions_disjoint (w2n w) sz off (type_memory_size tv))` by
    (`immutable_alloca_sep func cenv cx ee t'` by fs[stmt_state_rel_def] >>
     rpt strip_tac >>
     qpat_x_assum `immutable_alloca_sep _ _ _ _ t'` mp_tac >>
     simp[immutable_alloca_sep_def] >>
     disch_then drule >> disch_then drule >> strip_tac >>
     qpat_x_assum `!inst b sz. _ ==> regions_disjoint _ _ b sz` drule >>
     simp[venomInstTheory.mk_inst_def, regions_disjoint_def]) >>
  `!x. not_fresh_at sn x ==> lookup_var x t' = lookup_var x t` by
    (qpat_x_assum `run_inst_seq _ _ = OK _` mp_tac >>
     simp[run_inst_seq_def, venomInstTheory.mk_inst_def,
       step_inst_base_def, eval_operand_def] >>
     simp[AllCaseEqs(), update_var_def] >> strip_tac >>
     gvs[exec_alloca_def, AllCaseEqs(), update_var_def, lookup_var_def] >>
     rpt strip_tac >> simp[finite_mapTheory.FLOOKUP_UPDATE] >> metis_tac[]) >>
  qexistsl_tac [`u`, `w`] >> simp[Abbr `u`] >>
  gvs[extrequest_history_frame_def, local_region_def, lookup_var_def,
      contract_storage_def, contract_transient_def] >>
  metis_tac[]
QED
