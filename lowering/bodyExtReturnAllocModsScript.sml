(* Allocation before writing or decoding an external return value. *)
Theory bodyExtReturnAllocMods
Ancestors
  bodyFullAllocaFresh bodyFullPostsMods bodyMethodIdScratchFrameMods
  exprSimExtCallCase exprSimWordArgs stateRelProj abiCallerAllocation
  abiCallerLocalScratch abiBuiltinAllocation emitHelperProps stmtReasonMemory
  bodyFullHashKeccakFixed[qualified,ignore_grammar] exprSimProps
  exprLoweringProps loweringSlice finite_map words venomState bodyInvSplit
  loweringStateRelDefs ptrDiscipline bodyFullShadowBodyInv bodyPtrDefs
  loweringPosts arithmetic

Theorem extreturn_alloc_new_site[local]:
  compile_alloc_buffer n sr = (buf,ar) /\
  run_inst_seq (emitted_insts sr ar) t = OK raw /\
  a = raw with vs_inst_idx := k /\ FLOOKUP a.vs_allocas aid = SOME (b,sz) ==>
  FLOOKUP t.vs_allocas aid = SOME (b,sz) \/ t.vs_alloca_next <= b
Proof
  strip_tac >> drule abi_builtin_alloc_buffer_shape >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  gvs[run_inst_seq_def, AllCaseEqs()] >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  simp[step_alloca_eq] >> Cases_on `FLOOKUP t.vs_allocas sr.cs_next_id` >>
  gvs[AllCaseEqs(), update_var_def] >>
  strip_tac >> Cases_on `aid = sr.cs_next_id` >> gvs[FLOOKUP_UPDATE]
QED

Theorem extreturn_alloc_immutable[local]:
  immutable_frame_mods func cenv cx ee t /\ local_ptrs_reserved cenv sr /\
  (!x. not_fresh_at sr x ==> lookup_var x a = lookup_var x t) /\
  a.vs_memory = t.vs_memory /\ a.vs_data_section = t.vs_data_section /\
  t.vs_alloca_next <= a.vs_alloca_next /\
  (!aid b sz. FLOOKUP a.vs_allocas aid = SOME (b,sz) ==>
    FLOOKUP t.vs_allocas aid = SOME (b,sz) \/ t.vs_alloca_next <= b) ==>
  immutable_frame_mods func cenv cx ee a
Proof
  simp[immutable_frame_mods_def, immutables_rel_mods_def,
       immutable_alloca_sep_mods_def] >> strip_tac >> conj_tac
  >- (rpt gen_tac >> disch_tac >> irule immutables_rel_mem_agree >>
      qexists_tac `t` >> simp[]) >>
  rpt gen_tac >> disch_tac >> irule immutable_alloca_sep_frame >>
  qexistsl_tac [`t`,`ee`] >> simp[] >> rpt strip_tac >>
  disj1_tac >> rename1 `local_region _ _ a name b sz` >> qexists_tac `name` >>
  fs[local_region_def, local_ptrs_reserved_def] >> metis_tac[]
QED

Theorem extreturn_alloc_ghost[local]:
  ghost_inv_at_mods D lo d cenv cx ee G tn t /\
  local_ptrs_rel func cenv ee.scopes t /\ local_ptrs_reserved cenv sr /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sr x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sr x) /\
  (!x. not_fresh_at sr x ==> lookup_var x a = lookup_var x t /\
       FLOOKUP J x = FLOOKUP G x /\ op_taint tm (Var x) = op_taint tn (Var x)) /\
  a with <| vs_vars := t.vs_vars; vs_allocas := t.vs_allocas;
            vs_alloca_next := t.vs_alloca_next; vs_inst_idx := t.vs_inst_idx |> = t /\
  a.vs_memory = t.vs_memory /\ allocas_from lo a /\
  t.vs_alloca_next <= a.vs_alloca_next /\
  tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
  (!i. i IN tm.t_mem <=> i IN tn.t_mem \/
      (t.vs_alloca_next <= i /\ i < e)) ==>
  ghost_inv_at_mods D lo d cenv cx ee J tm a
Proof
  strip_tac >> drule method_id_ghost_at_zero >> strip_tac >>
  `allocas_from 0 a` by simp[allocas_from_def] >>
  `ghost_inv_at D 0 d cenv cx ee J tm a` by
    (drule_all alloc_buffer_ghost_inv_at_locals >> simp[]) >>
  `lo <= t.vs_alloca_next` by fs[ghost_inv_at_mods_def] >>
  `!i. i < lo /\ i IN tm.t_mem ==> i IN tn.t_mem` by
    (rpt gen_tac >> simp[] >> decide_tac) >>
  qpat_x_assum `ghost_inv_at _ 0 _ _ _ _ _ _ a`
    (strip_assume_tac o REWRITE_RULE[ghost_inv_at_def]) >>
  qpat_x_assum `ghost_inv_at_mods _ _ _ _ _ _ _ _ t`
    (strip_assume_tac o REWRITE_RULE[ghost_inv_at_mods_def]) >>
  pure_rewrite_tac[ghost_inv_at_mods_def] >> rpt conj_tac
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- first_assum ACCEPT_TAC
  >- (rpt strip_tac >> simp[] >>
      qpat_assum `!i. i < lo /\ i IN tn.t_mem ==> imm_section_dead_mods _ _ i`
        irule >> metis_tac[])
  >- (rpt strip_tac >> `not_fresh_at sr x` by fs[local_ptrs_reserved_def] >>
      metis_tac[])
  >- first_assum ACCEPT_TAC >>
  decide_tac
QED

Theorem extreturn_alloc_kept[local]:
  ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
  (!x. not_fresh_at sr x ==> FLOOKUP J x = FLOOKUP G x /\
                             op_taint tm (Var x) = op_taint tn (Var x)) /\
  (!i. i IN tm.t_mem <=> i IN tn.t_mem \/ (t.vs_alloca_next <= i /\ i < e)) /\
  lo <= t.vs_alloca_next /\ wb_frame cenv es ee sa s0 t /\
  local_ptrs_rel func cenv ee.scopes t /\ alloca_inv t /\
  sa.cs_next_var <= sr.cs_next_var /\ local_ptrs_reserved cenv sa /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes ==>
  ghost_kept_at lo cenv es sa G0 tn0 s0 J tm
Proof
  strip_tac >> irule alloc_buffer_ghost_kept_at >>
  qexistsl_tac [`G`,`e`,`t`,`tn`] >> simp[] >> rpt conj_tac
  >- (gen_tac >> disch_tac >>
      `not_fresh_at sr x` by
        (irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
      simp[])
  >- (rpt strip_tac >>
      `local_region cenv ee.scopes t name b sz` by
        (irule local_region_frame_fwd >> qexistsl_tac [`s0`,`sa`,`es.scopes`] >>
         fs[wb_frame_def]) >>
      drule_all abi_caller_local_end >> simp[]) >>
  rpt strip_tac >> irule abi_caller_allocation_end >> simp[] >>
  qexistsl_tac [`sz`,`aid`,`off`] >> fs[wb_frame_def]
QED

Theorem extcall_return_alloc_cut_mods:
  extcall_returned st0 ctx func cenv cx rt es sa s0 sr addr src cap target
    has_default dop dt dopt bs ee t /\
  compile_alloc_buffer n sr = (buf,ar) /\ fn_has_code sr ar func /\
  fn_inst_ids_distinct func /\ n < dimword (:256) /\
  alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    ghost_inv_at_mods (DF H) lo d cenv cx ee G tn t /\
    immutable_frame_mods func cenv cx ee t) /\
  ghost_kept_at lo cenv es sa G0 tn0 s0 G tn /\
  local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (?H. valid_horizon cx st0 H ee.storage_trace) ==>
  ?q w a J tm.
    buf.buf_operand = Var q /\ not_fresh_at ar q /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (t,G,tn) [] (OK a,J,tm)) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      stmt_state_rel H ctx func cenv cx ee a /\
      storage_well_formed_on cx ee (FST H) /\
      ghost_inv_at_mods (DF H) lo d cenv cx ee J tm a /\
      immutable_frame_mods func cenv cx ee a) /\
    ghost_kept_at lo cenv es sa G0 tn0 s0 J tm /\ wb_frame cenv es ee sa s0 a /\
    ~a.vs_halted /\ a.vs_current_bb = ar.cs_current_bb /\
    a.vs_inst_idx = LENGTH ar.cs_current_insts /\ a.vs_returndata = bs /\
    alloca_history func a /\ allocas_from lo a /\
    lo <= t.vs_alloca_next /\ t.vs_alloca_next <= a.vs_alloca_next /\
    a.vs_memory = t.vs_memory /\ a.vs_accounts = t.vs_accounts /\
    lookup_var q a = SOME w /\ ptr_covers J tm q a n /\
    FLOOKUP a.vs_allocas sr.cs_next_id = SOME (w2n w,n) /\
    FLOOKUP J q = SOME (w2n w,n) /\
    w2n w + n < dimword (:256) /\ w2n w + n <= a.vs_alloca_next /\
    (!aid e. FLOOKUP t.vs_allocas aid = SOME e ==> FLOOKUP a.vs_allocas aid = SOME e) /\
    (!aid b len. aid < sr.cs_next_id /\ FLOOKUP t.vs_allocas aid = SOME (b,len) ==>
      regions_disjoint (w2n w) n b len) /\
    (!name b len. local_region cenv ee.scopes a name b len ==>
      regions_disjoint (w2n w) n b len) /\
    (!x. not_fresh_at sr x ==>
      lookup_var x a = lookup_var x t /\ FLOOKUP J x = FLOOKUP G x /\
      op_taint tm (Var x) = op_taint tn (Var x)) /\
    tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    (!i. i IN tm.t_mem <=> i IN tn.t_mem \/
      (t.vs_alloca_next <= i /\ i < w2n w + n))
Proof
  simp[extcall_returned_def] >> strip_tac >>
  rename1 `valid_horizon cx st0 h0 ee.storage_trace` >>
  qpat_assum `!H. _ ==> ghost_inv_at_mods _ _ _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  `allocas_from lo t /\ lo <= t.vs_alloca_next` by fs[ghost_inv_at_mods_def] >>
  drule_then strip_assume_tac stmt_state_rel_local_ptrs_alloca >>
  drule_then assume_tac bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp >>
  drule_all (INST_TYPE [alpha |-> ``:256``, beta |-> ``:256``]
    alloc_buffer_origin_ptr_path_with_raw_endpoint) >>
  disch_then (qspecl_then [`tn`,`explicit`,`PG`,`G`]
    (qx_choosel_then [`q`,`w`,`a`,`J`,`tm`,`raw`] strip_assume_tac)) >>
  `a.vs_halted = t.vs_halted /\ a.vs_memory = t.vs_memory /\
   a.vs_accounts = t.vs_accounts /\ a.vs_returndata = t.vs_returndata /\
   a.vs_data_section = t.vs_data_section` by
    (qpat_assum `a with <| vs_vars := _; vs_allocas := _;
          vs_alloca_next := _; vs_inst_idx := _ |> = t` (SUBST1_TAC o SYM) >> simp[]) >>
  `!aid b sz. FLOOKUP a.vs_allocas aid = SOME (b,sz) ==>
     FLOOKUP t.vs_allocas aid = SOME (b,sz) \/ t.vs_alloca_next <= b` by
    (rpt strip_tac >> drule_all extreturn_alloc_new_site >> simp[]) >>
  `immutable_frame_mods func cenv cx ee a` by
    (irule extreturn_alloc_immutable >> qexistsl_tac [`sr`,`t`] >> simp[]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sr x` by
    (gen_tac >> disch_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> simp[]) >>
  `wb_frame cenv es ee sa s0 a` by
    (irule wb_frame_readonly_tail >> qexistsl_tac [`sr`,`t`] >> simp[] >> metis_tac[]) >>
  qpat_x_assum `a = raw with vs_inst_idx := _` kall_tac >>
  qpat_x_assum `J = step_prov _ _ _ _` kall_tac >>
  qpat_x_assum `tm = step_taint _ _ _ _` kall_tac >>
  qpat_assum `!x. not_fresh_at sr x ==> lookup_var x a = _ /\ _`
    (strip_assume_tac o REWRITE_RULE[IMP_CONJ_THM, FORALL_AND_THM]) >>
  `ghost_kept_at lo cenv es sa G0 tn0 s0 J tm` by
    (irule extreturn_alloc_kept >> simp[] >>
     qexistsl_tac [`G`,`w2n w + n`,`ee`,`func`,`sr`,`t`,`tn`] >> simp[]) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
     stmt_state_rel H ctx func cenv cx ee a /\
     storage_well_formed_on cx ee (FST H) /\
     ghost_inv_at_mods (DF H) lo d cenv cx ee J tm a /\
     immutable_frame_mods func cenv cx ee a` by
    (qx_gen_tac `h` >> strip_tac >>
     qpat_assum `!H. _ ==> stmt_state_rel _ _ _ _ _ _ t /\ _`
       (qspec_then `h` (drule_then strip_assume_tac)) >>
     qpat_assum `!H. _ ==> ghost_inv_at_mods _ _ _ _ _ _ G tn t /\ _`
       (qspec_then `h` (drule_then strip_assume_tac)) >> simp[] >>
     irule extreturn_alloc_ghost >> simp[] >>
     qexistsl_tac [`G`,`w2n w + n`,`func`,`sr`,`t`,`tn`] >> fs[]) >>
  qexistsl_tac [`q`,`w`,`a`,`J`,`tm`] >> fs[] >>
  conj_tac >> first_assum ACCEPT_TAC
QED
