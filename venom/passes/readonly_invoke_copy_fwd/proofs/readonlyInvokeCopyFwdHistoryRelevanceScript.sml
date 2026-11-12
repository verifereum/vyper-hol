(* A nonempty accepted copy has no intervening owner call.  Relevance
   ends after its selected call, not after an arbitrary unselected call. *)
Theory readonlyInvokeCopyFwdHistoryRelevance
Ancestors
  readonlyInvokeCopyFwdHistoryVisitAccess readonlyInvokeCopyFwdHistorySelected
  readonlyInvokeCopyFwdHistoryAnalysis readonlyInvokeCopyFwdProtectionLifetime
  readonlyInvokeCopyFwdProtectionProducers readonlyInvokeCopyFwdHistory
  readonlyInvokeCopyFwdPlan invokeCopyFwdCommonDefs list indexedLists
  venomWfProps venomWf venomInst

Theorem ricf_located_event_owner_call_cutoff:
  ricf_located_event (icf_build_ctx fm fs rma fn) fn log
    round b es prefix e current /\
  ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts fn)) /\
  (bp_get_read_location e.rfe_ctx.icf_bp
    (ricf_event_copy e current) AddrSp_Memory).ml_size <> SOME 0 /\
  ricf_selected_position e (EL b fn.fn_blocks) j /\
  e.rfe_index < k /\ k <= j /\
  k < LENGTH (EL b fn.fn_blocks).bb_instructions /\
  (EL k (EL b fn.fn_blocks).bb_instructions).inst_opcode = INVOKE ==>
  k = j
Proof
  strip_tac >>
  drule_all ricf_located_event_source_block >> strip_tac >>
  `MAP (\i. i.inst_id) (EL b fn.fn_blocks).bb_instructions =
   MAP (\i. i.inst_id) current.bb_instructions` by
    (fs[ricf_block_edit_def, LIST_REL_EL_EQN, LIST_EQ_REWRITE] >>
     rpt strip_tac >> first_x_assum (qspec_then `x` mp_tac) >>
     simp[ricf_inst_edit_def, EL_MAP]) >>
  `ricf_selected_position e current j` by
    (fs[ricf_selected_position_def] >>
     drule findi_inst_ids >> disch_then (qspec_then `inst.inst_id` assume_tac) >>
     metis_tac[]) >>
  Cases_on `k = j` >> simp[] >>
  `k < j` by decide_tac >>
  metis_tac[ricf_located_event_no_intervening_source_invoke]
QED

(* Recover the selected round record from an ORIGINAL block position. *)
Theorem ricf_located_event_selected_position_site:
  ricf_located_event ctx0 fn log round b es prefix e current /\
  ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts fn)) /\
  ricf_selected_position e (EL b fn.fn_blocks) j ==>
  ?pos. MEM (EL j (EL b round.fn_blocks).bb_instructions,pos) e.rfe_sites
Proof
  strip_tac >>
  drule ricf_located_event_validation >> strip_tac >>
  drule_all ricf_function_trace_edit >> strip_tac >>
  drule_all ricf_function_edit_ids >> strip_tac >>
  `MAP (\i. i.inst_id) (EL b fn.fn_blocks).bb_instructions =
   MAP (\i. i.inst_id) (EL b round.fn_blocks).bb_instructions` by
    (fs[ricf_function_edit_def, LIST_REL_EL_EQN] >>
     first_x_assum (qspec_then `b` mp_tac) >> simp[] >>
     simp[ricf_block_edit_def, LIST_REL_EL_EQN, LIST_EQ_REWRITE] >>
     rpt strip_tac >> first_x_assum (qspec_then `x` mp_tac) >>
     simp[ricf_inst_edit_def, EL_MAP]) >>
  fs[ricf_selected_position_def] >>
  drule findi_inst_ids >> disch_then (qspec_then `inst.inst_id` assume_tac) >>
  `findi (\i. i.inst_id = inst.inst_id)
      (EL b round.fn_blocks).bb_instructions = SOME j` by metis_tac[] >>
  drule_all findi_some_index >> strip_tac >> fs[] >>
  `e.rfe_ctx.icf_dfg = dfg_build_function round` by simp[] >>
  `MEM inst (fn_insts round)` by
    (irule (cj 1 ricf_event_sites_function) >> metis_tac[]) >>
  `fn_inst_ids_distinct round` by
    fs[fn_inst_ids_distinct_def, fn_insts_def, fn_insts_blocks_flat, MAP_FLAT, MAP_MAP_o, combinTheory.o_DEF] >>
  `EL j (EL b round.fn_blocks).bb_instructions = inst` by
    (irule fn_inst_ids_distinct_inj >> conj_tac >- simp[] >>
     qexists_tac `round` >> simp[fn_inst_ids_distinct_def] >>
     simp[fn_insts_def, fn_insts_blocks_flat, MEM_FLAT, MEM_MAP] >>
     metis_tac[EL_MEM]) >>
  metis_tac[]
QED

Theorem ricf_history_relevant_owner_call_site:
  ricf_history_cursor vs C (icf_build_ctx fm fs rma p.rpe_fn) log
    p [] PG G tn fn s /\
  active_inst fn callinst s /\ callinst.inst_opcode = INVOKE /\
  wf_function p.rpe_fn /\
  ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts p.rpe_fn)) /\
  ricf_located_event (icf_build_ctx fm fs rma p.rpe_fn) p.rpe_fn log
    round b es prefix p.rpe_event current /\
  p.rpe_block = EL b p.rpe_fn.fn_blocks /\
  (bp_get_read_location p.rpe_event.rfe_ctx.icf_bp
    (ricf_event_copy p.rpe_event current) AddrSp_Memory).ml_size <> SOME 0 /\
  ricf_remaining_selected_use p s ==>
  fn = p.rpe_fn /\ b < LENGTH fn.fn_blocks /\
  s.vs_inst_idx < LENGTH (EL b fn.fn_blocks).bb_instructions /\
  callinst = EL s.vs_inst_idx (EL b fn.fn_blocks).bb_instructions /\
  ?pos. MEM (EL s.vs_inst_idx (EL b round.fn_blocks).bb_instructions,pos)
    p.rpe_event.rfe_sites
Proof
  strip_tac >>
  drule_all ricf_history_cursor_owner_position >> strip_tac >>
  drule_all ricf_located_event_source_block >> strip_tac >>
  fs[ricf_remaining_selected_use_def] >>
  `s.vs_inst_idx = j` by
    (irule ricf_located_event_owner_call_cutoff >> metis_tac[]) >>
  simp[] >> conj_tac >- metis_tac[] >>
  irule ricf_located_event_selected_position_site >> metis_tac[]
QED

(* Endpoint protection is a consequence of remaining selected uses, not a
   premise about an arbitrary owner call.  The static nonempty-analysis
   condition is kept explicit; runtime positivity alone does not replace it. *)
Theorem ricf_history_relevant_call_endpoints:
  ricf_history_cursor vs C (icf_build_ctx fm fs rma fn) log p [] PG G tn fn s /\
  wf_function fn /\ p.rpe_fn = fn /\
  active_inst fn callinst s /\ callinst.inst_opcode = INVOKE /\
  ricf_located_event (icf_build_ctx fm fs rma fn) fn log
    round b es prefix p.rpe_event current /\
  p.rpe_block = EL b fn.fn_blocks /\
  (bp_get_read_location p.rpe_event.rfe_ctx.icf_bp
    (ricf_event_copy p.rpe_event current) AddrSp_Memory).ml_size <> SOME 0 /\
  ricf_remaining_selected_use p s /\
  ssa_form fn /\ ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts fn)) /\
  ricf_src_alloca fn /\
  (ricf_event_copy p.rpe_event (EL b fn.fn_blocks)).inst_operands =
    [Var dst;Var sv;sz] /\
  dfg_get_def (dfg_build_function fn)
    (icf_assign_root (dfg_build_function fn) {} dst) = SOME di /\
  icf_is_alloca di /\ MEM di (fn_insts fn) /\ di.inst_opcode = ALLOCA /\
  di.inst_outputs = [icf_assign_root (dfg_build_function fn) {} dst] /\
  dfg_get_def (dfg_build_function fn) sv = SOME ai /\
  MEM ai (fn_insts fn) /\ ai.inst_opcode = ALLOCA /\ ai.inst_outputs = [sv] /\
  fn_inst_wf fn /\ fn_inst_ids_distinct fn /\ occurrence_syntax_origin fn a H /\
  occurrence_annotation_ok n a U B HP H stk PG G s /\
  occurrence_natural_geometry lo a U B stk s /\
  FLOOKUP B (a,di.inst_id) = SOME (db,z) /\
  FLOOKUP B (a,ai.inst_id) = SOME (sb,z) /\ 0 < z /\
  decode_invoke callinst = SOME (nm,ops) ==>
  FLOOKUP s.vs_allocas di.inst_id = SOME (db,z) /\
  FLOOKUP s.vs_allocas ai.inst_id = SOME (sb,z) /\
  (!k. k < LENGTH ops /\ op_prov G (EL k ops) = SOME (db,z) ==>
    rma_is_readonly rma nm k) /\
  (!k. k < LENGTH ops /\ op_prov G (EL k ops) = SOME (sb,z) ==>
    EL k ops = Var sv /\ rma_is_readonly rma nm k)
Proof
  strip_tac >> qpat_x_assum `p.rpe_fn = fn` (SUBST_ALL_TAC o SYM) >>
  `?pos. MEM (EL s.vs_inst_idx (EL b round.fn_blocks).bb_instructions,pos)
     p.rpe_event.rfe_sites` by
    (drule_all ricf_history_relevant_owner_call_site >> simp[] >> metis_tac[]) >>
  drule_all ricf_history_cursor_owner_position >> strip_tac >>
  drule_all ricf_located_event_source_block >> strip_tac >>
  `b < LENGTH p.rpe_fn.fn_blocks /\
   s.vs_inst_idx < LENGTH (EL b p.rpe_fn.fn_blocks).bb_instructions /\
   callinst = EL s.vs_inst_idx (EL b p.rpe_fn.fn_blocks).bb_instructions` by metis_tac[] >>
  gvs[] >>
  drule_all ricf_history_selected_call_endpoints >> simp[icf_build_ctx_def]
QED

(* The accepted late mutable-call example is relevant at its selected call,
   but not at the following mutable call.  Reuse its checked acceptance and
   mutability facts from ProtectionProducers; this tests only the cutoff. *)
Theorem ricf_late_call_remaining_boundary:
  p.rpe_block = ricf_late_call_block /\
  p.rpe_event.rfe_sites =
    [(mk_inst 4 INVOKE [Label "reader";Var "dst"] [],1)] /\
  s.vs_current_bb = ricf_late_call_block.bb_label ==>
  ricf_remaining_selected_use p (s with vs_inst_idx := 3) /\
  ~ricf_remaining_selected_use p (s with vs_inst_idx := 4)
Proof
  simp[ricf_remaining_selected_use_def, ricf_selected_position_def,
       ricf_late_call_block_def, mk_inst_def,
       invokeCopyFwdCommonDefsTheory.findi_def, INDEX_FIND_def]
QED
