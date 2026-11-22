(* Carry the selected legacy hit through the installed entry checks. *)
Theory groupedLegacyCheckSeam
Ancestors
  groupedDispatchPath groupedInternalLabels groupedEntryCounters groupedEntryAllocation
  groupedEntryResources selectedAcceptedFold exprLoweringProps emitHelperProps
  fragGasOriginPtr fragGasOriginPtrLoop decoderOriginAllocationFrame bodyFullPathHistory
  allocaHistory abiAllocationHistory venomMemProofs
  ptrDiscipline venomState venomExecSemantics venomInst moduleLowering compileEnv
  arithmetic words finite_map list pair

Theorem grouped_legacy_check_seam:
  compile_external_groups (Var mid)
    (pre ++ ExternalSingle (sel,lbl,mincd) pkg::post) prelude = (jobs,dispatch_end) /\
  fn_has_code prelude dispatch_end fn /\ EVERY group_entry_labels_ok post /\
  compile_external_groups (Var mid) pre prelude = (prefix_jobs,skip_end) /\
  compile_selector_checks (Var mid) [(sel,lbl)] skip_end = ((),sel_end) /\
  ci_mono dispatch_end sd /\ ci_mono sd checks /\
  checks.cs_current_bb = lbl /\ checks.cs_current_insts = [] /\
  compile_entry_checks m pay checks = ((),reg) /\ fn_has_code checks reg fn /\
  hit.vs_current_bb = lbl /\ hit.vs_inst_idx = 0 /\ ~hit.vs_halted /\
  (!id entry. FLOOKUP hit.vs_allocas id = SOME entry ==> id < skip_end.cs_next_id) /\
  (!inst w b n. MEM inst (fn_insts fn) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_operands = [Lit w] /\ FLOOKUP hit.vs_allocas inst.inst_id = SOME (b,n) ==>
    n = w2n w) /\
  alloca_inv hit /\ alloca_frontier_inv ctx fn site hit /\ allocas_from 0 hit /\
  fresh_vars_wrt sel_end hit /\ selected_registration_frame vs entry_taint hit tnhit /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp hit /\
    hit.vs_alloca_next + pending_alloca_size fn hit <= w2n hit.vs_initial_fmp) /\
  (!D explicit. gas_origin_ptr_path (D,0,explicit,ctx,fn,[]) (s,FEMPTY,entry_taint)
    [] (OK hit,Ghit,tnhit)) /\
  fn_inst_ids_distinct fn /\ s.vs_allocas = FEMPTY /\
  s = vs with <|vs_prev_bb := NONE; vs_current_bb := "__entry"; vs_inst_idx := 0|> /\
  unit_alloca_budget ctx < dimword (:256) /\ vs.vs_fmp = vs.vs_initial_fmp /\
  (ctx_has_dalloca ctx ==> unit_alloca_budget ctx <= w2n vs.vs_initial_fmp /\
    w2n vs.vs_initial_fmp < 2 ** 254) ==>
  selected_registration_resources ctx fn site 0 checks hit /\
  ((pay \/ hit.vs_call_ctx.cc_callvalue = 0w) /\ m <= LENGTH hit.vs_call_ctx.cc_calldata /\
   LENGTH hit.vs_call_ctx.cc_calldata < dimword (:256) ==>
   ?u G tn.
     selected_registration_resources ctx fn site 0 reg u /\
     default_registration_resources ctx fn site 0 reg u (tn with t_mem := {}) /\
     selected_registration_frame vs entry_taint u tn /\
     (ctx_has_dalloca ctx ==> allocas_below_fmp u /\
       u.vs_alloca_next + pending_alloca_size fn u <= w2n u.vs_initial_fmp) /\
     (!D explicit. gas_origin_ptr_path (D,0,explicit,ctx,fn,[]) (s,FEMPTY,entry_taint)
       [] (OK u,G,tn)))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `ci_mono sel_end dispatch_end` by
    (drule_all compile_external_groups_append_layout >> strip_tac >>
     `?rest. compile_external_groups (Var mid) post sel_end = (rest,dispatch_end)` by
       metis_tac[compile_external_single_cons_layout, pairTheory.PAIR_EQ] >>
     metis_tac[compile_external_groups_ci_mono, pairTheory.SND]) >>
  `ci_mono skip_end sel_end` by
    metis_tac[compile_selector_checks_ci_mono, pairTheory.SND] >>
  `ci_mono sel_end checks` by metis_tac[ci_mono_trans] >>
  `ci_mono skip_end checks` by metis_tac[ci_mono_trans] >>
  `fresh_vars_wrt checks hit` by
    (irule fresh_vars_wrt_mono >> qexists_tac `sel_end` >> fs[ci_mono_def]) >>
  `selected_registration_resources ctx fn site 0 checks hit` by
    (simp[selected_registration_resources_def] >> conj_tac
     >- (fs[ci_mono_def] >> rpt strip_tac >> res_tac >> decide_tac) >>
     first_assum ACCEPT_TAC) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  mp_tac (Q.INST [`sa` |-> `checks`,`sb` |-> `reg`,`s` |-> `hit`,
    `lo` |-> `0`,`tn` |-> `tnhit`,`PG` |-> `[]`,`G` |-> `Ghit`]
    (SPEC_ALL grouped_default_checks_pass_origin)) >>
  impl_tac >- simp[] >>
  disch_then (qx_choosel_then [`u`,`G`,`tn`] (map_every assume_tac o CONJUNCTS)) >>
  `selected_registration_frame vs entry_taint u tn` by
    (fs[selected_registration_frame_def] >> metis_tac[]) >>
  `!D explicit. gas_origin_ptr_path (D,0,explicit,ctx,fn,[])
    (s,FEMPTY,entry_taint) [] (OK u,G,tn)` by
    metis_tac[gas_origin_ptr_path_trans] >>
  qexistsl_tac [`u`,`G`,`tn`] >> asm_rewrite_tac[] >>
  suspend "allocation"
QED

Resume grouped_legacy_check_seam[allocation]:
  qpat_assum `!D explicit. gas_origin_ptr_path _ _ [] (OK u,G,tn)`
    (qspecl_then [`ARB`,`ARB`] assume_tac) >>
  `s.vs_inst_idx = 0` by simp[] >>
  `alloca_history fn s /\ alloca_inv s /\ abi_alloca_history (fn_insts fn) s` by
    metis_tac[alloca_history_empty, alloca_inv_empty_proof, abi_alloca_history_empty] >>
  drule_all body_full_path_alloca_history >> disch_tac >>
  drule_all grouped_entry_path_abi_history >> disch_tac >>
  drule_all decoder_origin_path_allocation_frame >> strip_tac >>
  qpat_assum `selected_registration_frame vs entry_taint u tn`
    (strip_assume_tac o REWRITE_RULE [selected_registration_frame_def]) >>
  irule grouped_default_registration_resources >>
  simp[entry_taint_def] >>
  strip_tac >>
  qpat_assum `ctx_has_dalloca ctx ==> unit_alloca_budget ctx <= _ /\ _`
    (drule_then (ACCEPT_TAC o REWRITE_RULE [EVAL ``(2:num) ** 254``] o CONJUNCT2))
QED

Finalise grouped_legacy_check_seam
