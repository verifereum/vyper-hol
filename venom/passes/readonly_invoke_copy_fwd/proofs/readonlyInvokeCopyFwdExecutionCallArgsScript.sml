(* Original-source allocation values produce selected call arguments. *)
Theory readonlyInvokeCopyFwdExecutionCallArgs
Ancestors
  readonlyInvokeCopyFwdExecution readonlyInvokeCopyFwdMapCopyGuards
  readonlyInvokeCopyFwdHeterogeneousMapOrigins readonlyInvokeCopyFwdOpaque
  readonlyInvokeCopyFwdRel readonlyInvokeCopyFwdValues
  readonlyInvokeCopyFwdHistory readonlyInvokeCopyFwdHeterogeneousLedger
  readonlyInvokeCopyFwdPlan o1LowerDloadRelocationKernel taintAgree
  readonlyInvokeCopyFwdSupportSeparation readonlyInvokeCopyFwdTraceOrigin
  readonlyInvokeCopyFwdProtectionSelected readonlyInvokeCopyFwdDefs
  readonlyInvokeCopyFwdHistoryReadExceptions o1PassContract
  readonlyInvokeCopyFwdHistoryCallPositions readonlyInvokeCopyFwdReadonlyPositions
  readonlyInvokeCopyFwdHistoryOperandOrigins
  readonlyInvokeCopyFwdExecutionCoverage readonlyInvokeCopyFwdMapCoverage
  readonlyInvokeCopyFwdHistoryPhase readonlyInvokeCopyFwdHistoryOrigin
  readonlyInvokeCopyFwdHistoryVisitAccess readonlyInvokeCopyFwdHistorySelected
  readonlyInvokeCopyFwdProtection
  readonlyInvokeCopyFwdHistoryRelevance readonlyInvokeCopyFwdProtectionLifetime
  readonlyInvokeCopyFwdHistoryUses
  readonlyInvokeCopyFwdAnalyzedOrigins readonlyMemoryArgsDefs
  readonlyInvokeCopyFwdExecutionHistory readonlyInvokeCopyFwdLiveCertificates
  readonlyInvokeCopyFwdAlignedOrigins internalReturnCopyFwdSim
  invokeCopyFwdCommonDefs
  internalReturnCopyFwdAlias internalReturnCopyFwdPlan
  occurrenceGeometry o1LowerDloadOccurrence ptrTaintClean ptrDiscipline
  frameViewFacts unitShapeDefs venomWf venomWfProps
  dfgAnalysisProps allocaRemapSSA
  venomExecSemantics venomState venomInst finite_map list pred_set words arithmetic

(* The source operand remains available after its copy.  The original call
   operand may be any ASSIGN alias of the destination allocation. *)
Theorem ricf_call_earlier_copy_values:
  occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H /\
  EVERY wf_ssa C.ctx_functions /\ EVERY wf_function C.ctx_functions /\
  EVERY fn_inst_wf C.ctx_functions /\ vs.vs_allocas = FEMPTY /\
  ~ctx_has_dalloca C /\
  inst.inst_opcode = INVOKE /\ MEM (Var dv) inst.inst_operands /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  e.rfe_index <= s.vs_inst_idx /\
  e.rfe_index < LENGTH bb.bb_instructions /\
  (ricf_event_copy e bb).inst_opcode = MCOPY /\
  (ricf_event_copy e bb).inst_operands = [Var dst;Var sv;Lit sz] /\
  MEM da (fn_insts fn) /\ da.inst_opcode = ALLOCA /\
  da.inst_outputs = [dr] /\ da.inst_operands = [Lit sz] /\
  MEM sa (fn_insts fn) /\ sa.inst_opcode = ALLOCA /\
  sa.inst_outputs = [sv] /\ sa.inst_operands = [Lit sz] /\
  ircf_alias fn dr dv ==>
  ?db sb.
    eval_operand (Var dv) s = SOME (n2w db) /\
    eval_operand (Var sv) s = SOME (n2w sb) /\
    FLOOKUP G dv = SOME (db,w2n sz) /\
    FLOOKUP G sv = SOME (sb,w2n sz) /\
    FLOOKUP B (a,da.inst_id) = SOME (db,w2n sz) /\
    FLOOKUP B (a,sa.inst_id) = SOME (sb,w2n sz)
Proof
  strip_tac >>
  `frame_reachable vs C stk PG G tn fn inst s` by
    metis_tac[occ_frame_reachable_projection] >>
  `ircf_alias_site_value fn s G dv` by
    (irule ircf_alias_reachable_operand >>
     qexistsl_tac [`C`,`PG`,`inst`,`stk`,`tn`,`vs`] >> simp[]) >>
  `ircf_alias_site_value fn s G sv` by
    (irule ircf_alias_reachable_earlier_operand >>
     conj_tac
     >- (qexistsl_tac [`bb`,`e.rfe_index`] >> fs[ricf_event_copy_def]) >>
     qexistsl_tac [`C`,`PG`,`inst`,`stk`,`tn`,`vs`] >> simp[]) >>
  `?db. lookup_var dv s = SOME (n2w db) /\
    FLOOKUP s.vs_allocas da.inst_id = SOME (db,w2n sz) /\
    FLOOKUP G dv = SOME (db,w2n sz)` by
    metis_tac[ircf_alias_site_value_elim] >>
  `?sb. lookup_var sv s = SOME (n2w sb) /\
    FLOOKUP s.vs_allocas sa.inst_id = SOME (sb,w2n sz) /\
    FLOOKUP G sv = SOME (sb,w2n sz)` by
    metis_tac[ircf_alias_site_value_elim, ircf_alias_refl] >>
  drule occ_frame_reachable_annotation >>
  simp[occurrence_annotation_ok_def, occurrence_allocas_ok_def] >>
  strip_tac >> simp[eval_operand_def] >> metis_tac[]
QED

(* Active translations belong to suspended callers.  A positive allocation
   owned by the current frame cannot have their source key. *)
Theorem ricf_call_current_alloca_not_relocated:
  occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H /\
  occurrence_natural_geometry lo a U B stk s /\
  FLOOKUP B (a,aid) = SOME (sb,len) /\ 0 < len /\
  ricf_sites_ok sites /\
  ricf_heterogeneous_map_origins vs C stk PG G tn fn inst s U B sites ==>
  (sb,len) NOTIN FDOM sites
Proof
  strip_tac >>
  mp_tac (SPEC_ALL ricf_heterogeneous_map_origins_current_copy_exclusion |>
    Q.INST [`id` |-> `(a,aid)`, `db` |-> `sb`]) >>
  (impl_tac >- simp[]) >> strip_tac >> strip_tac >>
  `?tr. FLOOKUP sites (sb,len) = SOME tr` by fs[FLOOKUP_DEF] >>
  PairCases_on `tr` >>
  `tr0 = sb /\ tr2 = len` by
    (fs[ricf_sites_ok_def] >> metis_tac[]) >> gvs[] >>
  ` (sb,tr1,len) IN ricf_site_triples sites` by
    (simp[ricf_site_triples_def] >> metis_tac[]) >>
  qpat_x_assum `!b c z k. _`
    (qspecl_then [`sb`,`tr1`,`len`,`0`] mp_tac) >> simp[]
QED

(* The boundary relation uses the actual source taint, not an arbitrary
   relational mask.  ALLOCA roots therefore have no masked value bits. *)
Theorem ricf_call_source_alloca_target_value:
  ricf_execution_invariant vs C D stk PG G tn fn inst s t
    n a U B HP H ledger E sites maps targets tn /\
  EVERY wf_ssa C.ctx_functions /\ ssa_form fn /\
  occurrence_natural_geometry lo a U B stk s /\
  MEM sa (fn_insts fn) /\ sa.inst_opcode = ALLOCA /\
  sa.inst_outputs = [sv] /\
  FLOOKUP B (a,sa.inst_id) = SOME (sb,len) /\ 0 < len /\
  FLOOKUP G sv = SOME (sb,len) /\
  eval_operand (Var sv) s = SOME (n2w sb) ==>
  eval_operand (Var sv) t = SOME (n2w sb)
Proof
  pure_rewrite_tac[ricf_execution_invariant_def] >> strip_tac >>
  `occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H` by
    fs[ricf_heterogeneous_source_ledger_def] >>
  `frame_reachable vs C stk PG G tn fn inst s` by
    metis_tac[occ_frame_reachable_projection] >>
  `EVERY ssa_form C.ctx_functions` by fs[EVERY_MEM, wf_ssa_def] >>
  `op_taint tn (Var sv) = {}` by
    metis_tac[frame_reachable_alloca_root_clean] >>
  `~retpc_var fn sv` by
    (irule noncopy_output_not_retpc >>
     simp[] >> qexists_tac `sa` >> simp[]) >>
  `ricf_sites_ok sites` by
    fs[ricf_opaque_frame_agree_def, ricf_frame_agree_def] >>
  `(sb,len) NOTIN FDOM sites` by
    (irule ricf_call_current_alloca_not_relocated >> metis_tac[]) >>
  mp_tac (SPEC_ALL ricf_opaque_frame_operand |>
    Q.INST [`op` |-> `Var sv`, `x` |-> `n2w sb`,
      `X` |-> `ircf_dead (ricf_original_copy_ids C) s stk`,
      `PG` |-> `ricf_complete_params PG s.vs_params`]) >>
  simp[] >> strip_tac >>
  gvs[ricf_opaque_value_agree_def, ricf_is_zero_prov_def, op_prov_def,
    ricf_value_agree_def] >>
  metis_tac[ld_value_agree_clean]
QED

(* The last-rewrite classification supplies the two allocation descriptors
   and destination alias.  Their actual values, including the target source
   root, follow from execution rather than from related-argument premises. *)
Theorem ricf_call_selected_argument_values:
  ricf_execution_invariant vs C D stk PG G tn fn inst s t
    n a U B HP H ledger E sites maps targets tn /\
  EVERY wf_ssa C.ctx_functions /\ EVERY wf_function C.ctx_functions /\
  EVERY fn_inst_wf C.ctx_functions /\ vs.vs_allocas = FEMPTY /\
  ~ctx_has_dalloca C /\
  ssa_form fn /\ occurrence_natural_geometry lo a U B stk s /\
  inst.inst_opcode = INVOKE /\ MEM (Var dv) inst.inst_operands /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  e.rfe_index <= s.vs_inst_idx /\
  e.rfe_index < LENGTH bb.bb_instructions /\
  (ricf_event_copy e bb).inst_opcode = MCOPY /\
  (ricf_event_copy e bb).inst_operands = [Var dst;Var sv;Lit sz] /\
  MEM da (fn_insts fn) /\ da.inst_opcode = ALLOCA /\
  da.inst_outputs = [dr] /\ da.inst_operands = [Lit sz] /\
  MEM sa (fn_insts fn) /\ sa.inst_opcode = ALLOCA /\
  sa.inst_outputs = [sv] /\ sa.inst_operands = [Lit sz] /\
  ircf_alias fn dr dv /\ 0 < w2n sz ==>
  ?db sb.
    eval_operand (Var dv) s = SOME (n2w db) /\
    eval_operand (Var sv) t = SOME (n2w sb) /\
    FLOOKUP G dv = SOME (db,w2n sz) /\
    FLOOKUP B (a,da.inst_id) = SOME (db,w2n sz) /\
    FLOOKUP B (a,sa.inst_id) = SOME (sb,w2n sz) /\
    (!callsites. ricf_sites_ok callsites /\
      FLOOKUP callsites (db,w2n sz) = SOME (db,sb,w2n sz) ==>
      ricf_opaque_value_agree callsites (op_prov G (Var dv)) {}
        (n2w db) (n2w sb))
Proof
  strip_tac >>
  `occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H` by
    fs[ricf_execution_invariant_def, ricf_heterogeneous_source_ledger_def] >>
  drule_all ricf_call_earlier_copy_values >> strip_tac >>
  `eval_operand (Var sv) t = SOME (n2w sb)` by
    (irule ricf_call_source_alloca_target_value >> metis_tac[]) >>
  qexistsl_tac [`db`,`sb`] >> simp[] >> rpt strip_tac >>
  `ricf_value_agree callsites (SOME (db,w2n sz)) {}
     (n2w db) (n2w sb)` by
    (drule_all ricf_value_agree_relocated >> simp[WORD_ADD_SUB2]) >>
  simp[ricf_opaque_value_agree_def, op_prov_def]
QED

(* Coverage finds the actual executed payload; its numerical cross agreement
   comes from the running invariant rather than from the static event. *)
Theorem ricf_call_selected_phase:
  ricf_execution_invariant vs C D stk PG G tn fn inst s t
    n a U B HP H certificates E sites maps targets tn /\
  ricf_copy_coverage ctx0 fn log a history s /\
  ricf_certificate_coverage s history certificates /\
  ricf_located_event ctx0 fn log round b es prefix e current /\
  b < LENGTH fn.fn_blocks /\
  (EL b fn.fn_blocks).bb_label = s.vs_current_bb /\
  (ricf_event_copy e (EL b fn.fn_blocks)).inst_opcode = MCOPY /\
  (ricf_event_copy e (EL b fn.fn_blocks)).inst_operands =
    [Var dst; Var sv; Lit sz] /\
  0 < w2n sz /\ e.rfe_index < s.vs_inst_idx /\
  ricf_selected_position e (EL b fn.fn_blocks) s.vs_inst_idx ==>
  ?p ctxP logP.
    MEM (p,[]) history /\ MEM (p,[]) certificates /\
    p.rpe_event = e /\ p.rpe_fn = fn /\
    p.rpe_block = EL b fn.fn_blocks /\ p.rpe_owner = a /\
    ricf_phase_entry vs C ctxP logP stk PG G tn fn s a U B (p,[]) /\
    ircf_cross tn {(p.rpe_db,p.rpe_sb,p.rpe_size)} s t
Proof
  strip_tac >>
  `?p. MEM (p,[]) history /\ p.rpe_event = e /\ p.rpe_fn = fn /\
    p.rpe_block = EL b fn.fn_blocks /\ p.rpe_owner = a` by
    (fs[ricf_copy_coverage_def] >> metis_tac[]) >>
  `ricf_remaining_selected_use p (ricf_visit_owner_state [] s)` by
    (simp[ricf_remaining_selected_use_def, ricf_visit_owner_state_def] >>
     qexists_tac `s.vs_inst_idx` >> simp[]) >>
  `MEM (p,[]) certificates` by
    (fs[ricf_certificate_coverage_def] >> metis_tac[]) >>
  `?ctxP logP.
    ricf_phase_entry vs C ctxP logP stk PG G tn fn s a U B (p,[])` by
    (fs[ricf_execution_invariant_def,
        ricf_heterogeneous_source_ledger_def, EVERY_MEM] >> metis_tac[]) >>
  qexistsl_tac [`p`,`ctxP`,`logP`] >> simp[] >>
  irule ircf_cross_subset >>
  qexists_tac `ricf_phase_ranges 0 certificates` >>
  fs[ricf_execution_invariant_def] >>
  simp[SUBSET_DEF, ricf_phase_ranges_def] >> metis_tac[]
QED

(* A selected payload becomes an exact head anchor in the actual callee.
   In particular its endpoints and readonly facts are produced here. *)
Theorem ricf_call_selected_payload_origin:
  ricf_execution_invariant vs C D stk PG G tn fn callinst s t
    n a U B HP H ledger E sites maps targets tn /\ MEM (p,[]) ledger /\
  ricf_analyzed_ledger vs C stk PG G tn fn s a U B ledger /\
  EVERY wf_ssa C.ctx_functions /\ EVERY wf_function C.ctx_functions /\
  EVERY fn_inst_wf C.ctx_functions /\ vs.vs_allocas = FEMPTY /\
  ~ctx_has_dalloca C /\
  wf_function fn /\ wf_ssa fn /\ fn_inst_wf fn /\ fn_inst_ids_distinct fn /\
  ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts fn)) /\
  ricf_full_alloca_copies fn /\ ricf_src_alloca fn /\
  occurrence_syntax_origin fn a H /\
  occurrence_natural_geometry lo a U B stk s /\
  s.vs_current_bb = p.rpe_block.bb_label /\
  ricf_selected_position p.rpe_event p.rpe_block s.vs_inst_idx /\
  active_inst fn callinst s /\ callinst.inst_opcode = INVOKE /\
  decode_invoke callinst = SOME (nm,ops) /\
  lookup_function nm C.ctx_functions = SOME callee /\
  eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs ==>
  ?ctxP logP.
    ctxP.icf_rma = readonly_mem_analyze C /\
    !s1 inst. enters_block callee cs s1 /\ active_inst callee inst s1 ==>
    ricf_aligned_translation_origin vs C ctxP logP
      (<|cf_fn := fn; cf_inst := callinst; cf_state := s;
         cf_params := PG; cf_prov := G; cf_tvar := tn.t_var|> :: stk)
      (MAP (op_prov G) ops) FEMPTY (tn with t_var := FEMPTY) callee inst s1
      (<|of_owner := a; of_prov := H; of_params := HP|> :: U) B
      (p.rpe_db,p.rpe_size) (p.rpe_db,p.rpe_sb,p.rpe_size)
Proof
  strip_tac >>
  `occ_frame_reachable vs C stk PG G tn fn callinst s n a U B HP H` by
    fs[ricf_execution_invariant_def, ricf_heterogeneous_source_ledger_def] >>
  `?ctxP logP. ctxP.icf_rma = readonly_mem_analyze C /\
    ricf_phase_entry vs C ctxP logP stk PG G tn fn s a U B (p,[])` by
    (fs[ricf_analyzed_ledger_def, EVERY_MEM] >> metis_tac[]) >>
  `ricf_history_cursor vs C ctxP logP p [] PG G tn fn s /\
    a = p.rpe_owner /\ 0 < p.rpe_size /\
    FLOOKUP B p.rpe_dst = SOME (p.rpe_db,p.rpe_size) /\
    FLOOKUP B p.rpe_src = SOME (p.rpe_sb,p.rpe_size)` by
    fs[ricf_phase_entry_def] >>
  `fn = p.rpe_fn` by metis_tac[ricf_history_cursor_owner_function] >>
  `ssa_form p.rpe_fn` by fs[wf_ssa_def] >>
  `wf_function p.rpe_fn /\ wf_ssa p.rpe_fn /\ fn_inst_wf p.rpe_fn /\
   fn_inst_ids_distinct p.rpe_fn /\
   ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts p.rpe_fn)) /\
   ricf_full_alloca_copies p.rpe_fn /\ ricf_src_alloca p.rpe_fn` by
    metis_tac[] >>
  `?ostk OPG OG OT. ricf_history_origin vs C ctxP logP p ostk OPG OG OT` by
    (fs[ricf_history_cursor_def] >> metis_tac[]) >>
  drule ricf_history_origin_original_allocas >>
  (impl_tac >- metis_tac[]) >> strip_tac >>
  `?round b es prefix current.
    ricf_located_event ctxP p.rpe_fn logP round b es prefix p.rpe_event current /\
    p.rpe_block = EL b p.rpe_fn.fn_blocks` by
    (fs[ricf_history_origin_def] >> metis_tac[]) >>
  drule_all ricf_history_cursor_owner_position >> strip_tac >>
  drule_all ricf_located_event_source_block >> strip_tac >>
  `?pos. MEM
    (EL s.vs_inst_idx (EL b round.fn_blocks).bb_instructions,pos)
    p.rpe_event.rfe_sites` by
    (irule ricf_located_event_selected_position_site >> metis_tac[]) >>
  `di = da` by
    metis_tac[dfg_build_function_correct, ssa_unique_output, MEM] >>
  qpat_x_assum `di = da` SUBST_ALL_TAC >>
  `dfg_get_def (dfg_build_function p.rpe_fn) sv = SOME sa` by
    (`?def. dfg_get_def (dfg_build_function p.rpe_fn) sv = SOME def` by
       metis_tac[dfg_build_function_defs_complete, MEM] >>
     `def = sa` by
       metis_tac[dfg_build_function_correct, ssa_unique_output, MEM] >>
     gvs[]) >>
  `occurrence_annotation_ok n a U B HP H stk PG G s` by
    metis_tac[occ_frame_reachable_annotation] >>
  `FLOOKUP s.vs_allocas da.inst_id = SOME (p.rpe_db,p.rpe_size) /\
   FLOOKUP s.vs_allocas sa.inst_id = SOME (p.rpe_sb,p.rpe_size) /\
   (!k. k < LENGTH ops /\ op_prov G (EL k ops) = SOME (p.rpe_db,p.rpe_size)
        ==> rma_is_readonly ctxP.icf_rma nm k) /\
   (!k. k < LENGTH ops /\ op_prov G (EL k ops) = SOME (p.rpe_sb,p.rpe_size)
        ==> EL k ops = Var sv /\ rma_is_readonly ctxP.icf_rma nm k)` by
    (irule ricf_history_selected_call_endpoints >> simp[] >> metis_tac[]) >>
  qexistsl_tac [`ctxP`,`logP`] >> simp[] >> rpt strip_tac >>
  simp[ricf_aligned_translation_origin_def] >>
  qexistsl_tac [`p`,`[]`,
    `<|cf_fn := fn; cf_inst := callinst; cf_state := s;
       cf_params := PG; cf_prov := G; cf_tvar := tn.t_var|>`,`stk`,`tn`] >>
  simp[] >> irule ricf_aligned_origin_selected >> simp[] >>
  metis_tac[occ_frame_reachable_projection]
QED

Theorem ricf_call_selected_payloads_map:
  ricf_execution_invariant vs C D stk PG G tn fn callinst s t
    n a U B HP H certificates E sites maps targets tn /\
  ricf_history_certificates vs C log_of stk PG G tn fn callinst s a U B
    history certificates /\
  ricf_analyzed_map_origins vs C stk PG G tn fn callinst s U B sites /\
  EVERY wf_ssa C.ctx_functions /\ EVERY wf_function C.ctx_functions /\
  EVERY fn_inst_wf C.ctx_functions /\ vs.vs_allocas = FEMPTY /\
  ~ctx_has_dalloca C /\
  wf_function fn /\ wf_ssa fn /\ fn_inst_wf fn /\ fn_inst_ids_distinct fn /\
  ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts fn)) /\
  ricf_full_alloca_copies fn /\ ricf_src_alloca fn /\
  occurrence_syntax_origin fn a H /\
  occurrence_natural_geometry lo a U B stk s /\
  active_inst fn callinst s /\ callinst.inst_opcode = INVOKE /\
  decode_invoke callinst = SOME (nm,ops) /\
  lookup_function nm C.ctx_functions = SOME callee /\
  eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
  EVERY (\p. MEM (p,[]) history /\
    s.vs_current_bb = p.rpe_block.bb_label /\
    ricf_selected_position p.rpe_event p.rpe_block s.vs_inst_idx) ps ==>
  ?callsites.
    callsites = FOLDR (\p m.
      m |+ ((p.rpe_db,p.rpe_size),(p.rpe_db,p.rpe_sb,p.rpe_size))) sites ps /\
    ricf_sites_ok callsites /\ FDOM sites SUBSET FDOM callsites /\
    ircf_cross tn (ricf_site_triples callsites) s t /\
    (!s1 inst. enters_block callee cs s1 /\ active_inst callee inst s1 ==>
      ricf_analyzed_map_origins vs C
        (<|cf_fn := fn; cf_inst := callinst; cf_state := s;
           cf_params := PG; cf_prov := G; cf_tvar := tn.t_var|> :: stk)
        (MAP (op_prov G) ops) FEMPTY (tn with t_var := FEMPTY) callee inst s1
        (<|of_owner := a; of_prov := H; of_params := HP|> :: U) B callsites /\
      ricf_heterogeneous_map_origins vs C
        (<|cf_fn := fn; cf_inst := callinst; cf_state := s;
           cf_params := PG; cf_prov := G; cf_tvar := tn.t_var|> :: stk)
        (MAP (op_prov G) ops) FEMPTY (tn with t_var := FEMPTY) callee inst s1
        (<|of_owner := a; of_prov := H; of_params := HP|> :: U) B callsites)
Proof
  strip_tac >>
  `ricf_analyzed_ledger vs C stk PG G tn fn s a U B certificates` by
    metis_tac[ricf_history_certificates_analyzed] >>
  `!p. MEM (p,[]) history /\
    s.vs_current_bb = p.rpe_block.bb_label /\
    ricf_selected_position p.rpe_event p.rpe_block s.vs_inst_idx ==>
    MEM (p,[]) certificates` by
    (rpt strip_tac >>
     `ricf_remaining_selected_use p (ricf_visit_owner_state [] s)` by
       (simp[ricf_remaining_selected_use_def, ricf_visit_owner_state_def] >>
        qexists_tac `s.vs_inst_idx` >> simp[]) >>
     fs[ricf_history_certificates_def, ricf_certificate_coverage_def] >>
     metis_tac[]) >>
  `ricf_sites_ok sites /\ ircf_cross tn (ricf_site_triples sites) s t` by
    fs[ricf_execution_invariant_def, ricf_opaque_frame_agree_def,
       ricf_frame_agree_def] >>
  qexists_tac `FOLDR (\p m.
    m |+ ((p.rpe_db,p.rpe_size),(p.rpe_db,p.rpe_sb,p.rpe_size))) sites ps` >>
  simp[] >>
  qpat_x_assum `EVERY _ ps` mp_tac >> Induct_on `ps`
  >- (simp[] >> rpt gen_tac >> strip_tac >>
      conj_tac
      >- (rw[ricf_analyzed_map_origins_def] >>
          qpat_x_assum `ricf_analyzed_map_origins _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
          simp[ricf_analyzed_map_origins_def] >> strip_tac >>
          first_x_assum drule >> strip_tac >>
          qexistsl_tac [`ctxP`,`logP`] >> simp[] >>
          fs[ricf_aligned_translation_origin_def] >>
          qexistsl_tac [`p`,
            `<|cf_fn := fn; cf_inst := callinst; cf_state := s;
               cf_params := PG; cf_prov := G; cf_tvar := tn.t_var|> :: pre`,
            `anchor`,`tail`,`atn`] >>
          irule ricf_aligned_origin_call >> metis_tac[]) >>
      irule ricf_heterogeneous_map_origins_call >>
      fs[ricf_execution_invariant_def] >> metis_tac[]) >>
  simp[EVERY_DEF, FOLDR] >> rpt gen_tac >> strip_tac >>
  first_x_assum drule >> strip_tac >> rpt conj_tac
  >- (rw[ricf_sites_ok_def, FLOOKUP_UPDATE] >>
      Cases_on `h.rpe_db = db /\ h.rpe_size = sz` >>
      gvs[ricf_sites_ok_def] >> metis_tac[])
  >- (simp[SUBSET_DEF] >> metis_tac[SUBSET_DEF])
  >- (`ircf_cross tn {(h.rpe_db,h.rpe_sb,h.rpe_size)} s t` by
        (irule ircf_cross_subset >>
         qexists_tac `ricf_phase_ranges 0 certificates` >>
         fs[ricf_execution_invariant_def] >>
         simp[SUBSET_DEF, ricf_phase_ranges_def] >> metis_tac[]) >>
      qpat_assum `ircf_cross tn {(h.rpe_db,h.rpe_sb,h.rpe_size)} s t` mp_tac >>
      qpat_assum `ircf_cross tn (ricf_site_triples (FOLDR _ sites ps)) s t` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >>
      rw[ircf_cross_def, ricf_site_triples_def, FLOOKUP_UPDATE] >>
      Cases_on `(h.rpe_db,h.rpe_size) = id` >> gvs[] >>
      metis_tac[ADD_COMM]) >>
  `?ctxP logP. ctxP.icf_rma = readonly_mem_analyze C /\
    !s1 inst. enters_block callee cs s1 /\ active_inst callee inst s1 ==>
    ricf_aligned_translation_origin vs C ctxP logP
      (<|cf_fn := fn; cf_inst := callinst; cf_state := s;
         cf_params := PG; cf_prov := G; cf_tvar := tn.t_var|> :: stk)
      (MAP (op_prov G) ops) FEMPTY (tn with t_var := FEMPTY) callee inst s1
      (<|of_owner := a; of_prov := H; of_params := HP|> :: U) B
      (h.rpe_db,h.rpe_size) (h.rpe_db,h.rpe_sb,h.rpe_size)` by
    (irule ricf_call_selected_payload_origin >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >> conj_tac
  >- (irule ricf_analyzed_map_origins_update >> metis_tac[]) >>
  irule ricf_heterogeneous_map_origins_update >> metis_tac[]
QED

(* A source installed by any earlier rewrite cannot be an alias of the
   destination root of another original MCOPY. *)
Theorem ricf_call_copy_source_not_destination_alias[local]:
  ssa_form fn /\ ricf_src_alloca fn /\
  MEM bb fn.fn_blocks /\ k < LENGTH bb.bb_instructions /\
  (EL k bb.bb_instructions).inst_opcode = MCOPY /\
  (EL k bb.bb_instructions).inst_operands = [Var dst;Var sv;sz] /\
  dfg_get_def (dfg_build_function fn)
    (icf_assign_root (dfg_build_function fn) {} dst) = SOME di /\
  icf_is_alloca di /\ ircf_alloca_of fn sv ssz /\
  MEM old (fn_insts fn) /\ old.inst_opcode = MCOPY /\
  old.inst_operands = [Var d;src;szop] /\ ircf_alias fn dr d ==>
  ~ircf_alias fn dr sv
Proof
  strip_tac >> strip_tac >>
  `dr = sv` by metis_tac[ircf_alloca_alias_root] >> gvs[] >>
  irule ricf_source_copy_not_destination >> metis_tac[]
QED

(* Recorded positions are positions of destination aliases in the DFG of
   the recorded round.  Only its ASSIGN graph is transported backwards. *)
Theorem ricf_call_recorded_site_alias[local]:
  ricf_located_event ctx0 original log round b es prefix e current /\
  ssa_form original /\
  ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts original)) /\
  (ricf_event_copy e (EL b original.fn_blocks)).inst_operands =
    [Var dst;src;sz] /\ MEM (ri,p) e.rfe_sites ==>
  ?v. p < LENGTH ri.inst_operands /\ EL p ri.inst_operands = Var v /\
    ircf_alias original
      (icf_assign_root (dfg_build_function original) {} dst) v
Proof
  strip_tac >> drule ricf_located_event_validation >> strip_tac >>
  drule_all ricf_located_event_source_descriptor >> strip_tac >>
  `?v. MEM (v,ri,p)
    (icf_alias_use_positions e.rfe_ctx.icf_dfg
      (icf_collect_aliases e.rfe_ctx.icf_dfg
        (icf_assign_root e.rfe_ctx.icf_dfg {} dst)))` by
    (qpat_x_assum `ricf_event_ok e current` mp_tac >>
     simp[ricf_event_ok_def, ricf_try_forward_def] >>
     strip_tac >> gvs[AllCaseEqs(), ricf_event_copy_def] >>
     drule (INST_TYPE [alpha |-> ``:string``] ricf_sites_fold_origin) >>
     disch_then drule >> simp[]) >>
  `e.rfe_ctx.icf_dfg = dfg_build_function round` by simp[] >>
  fs[ircf_alias_use_positions_mem] >>
  drule_all ricf_function_trace_assign_root >> strip_tac >>
  drule_all ricf_function_trace_collect_aliases >> strip_tac >>
  fs[icf_collect_aliases_ircf_alias, EXTENSION] >> metis_tac[]
QED

Theorem ricf_call_event_source_root:
  ricf_event_ok e bb /\ ricf_event_roots e bb = SOME (dr,Var sv,sz) ==>
  ricf_event_source e bb = Var sv
Proof
  simp[ricf_event_ok_def, ricf_event_roots_def,
    ricf_event_copy_def, ricf_try_forward_def] >>
  rpt strip_tac >> gvs[AllCaseEqs(), ricf_event_source_def,
    icf_assign_root_op_def]
QED

Theorem ricf_call_located_copy_member[local]:
  ricf_located_event ctx0 original log round b es prefix e current /\
  ssa_form original /\
  ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts original)) ==>
  MEM (ricf_event_copy e (EL b original.fn_blocks)) (fn_insts original) /\
  (ricf_event_copy e (EL b original.fn_blocks)).inst_opcode = MCOPY
Proof
  strip_tac >> drule ricf_located_event_validation >> strip_tac >>
  drule_all ricf_located_event_source_block >> strip_tac >>
  drule_all ricf_located_event_source_descriptor >> strip_tac >>
  drule ricf_event_copy_shape >> strip_tac >>
  `e.rfe_index < LENGTH (EL b original.fn_blocks).bb_instructions` by
    (fs[ricf_block_edit_def] >> metis_tac[LIST_REL_LENGTH]) >>
  simp[fn_insts_def, fn_insts_blocks_MEM, ricf_event_copy_def] >>
  conj_tac
  >- (qexists_tac `EL b original.fn_blocks` >> simp[EL_MEM]) >>
  fs[ricf_event_copy_def] >> metis_tac[]
QED

(* A selected operand cannot have been supplied by any previous accepted
   rewrite, even one from another round.  No instruction-record equality
   between the original function and the selected round is assumed. *)
Theorem ricf_call_recorded_site_not_forwarded_source:
  ricf_located_event ctx0 original log round b es prefix e current /\
  ricf_located_event ctxP original logP roundP bp esP prefixP f prior /\
  ssa_form original /\ fn_inst_wf original /\
  ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts original)) /\
  ricf_full_alloca_copies original /\ ricf_src_alloca original /\
  (ricf_event_copy e (EL b original.fn_blocks)).inst_operands =
    [Var dst;src;sz] /\ MEM (ri,p) e.rfe_sites ==>
  EL p ri.inst_operands <> ricf_event_source f prior
Proof
  strip_tac >> drule_all ricf_call_recorded_site_alias >> strip_tac >>
  qspecl_then [`ctxP`,`original`,`logP`,`roundP`,`bp`,`esP`,`prefixP`,`f`,`prior`]
    mp_tac ricf_located_event_validation >> simp[] >> strip_tac >>
  qspecl_then [`ctxP`,`original`,`logP`,`roundP`,`bp`,`esP`,`prefixP`,`f`,`prior`]
    mp_tac ricf_located_event_source_block >> simp[] >> strip_tac >>
  qpat_assum `ricf_event_ok f prior`
    (mp_then Any mp_tac ricf_later_round_alloca_witnesses) >>
  disch_then (qspecl_then
    [`roundP`,`original`,`ctxP`,`EL bp original.fn_blocks`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[EL_MEM])) >> strip_tac >>
  rename1 `(ricf_event_copy f (EL bp original.fn_blocks)).inst_operands =
    [Var fdst;Var fsv;Lit fsz]` >>
  `ricf_event_source f prior = Var fsv` by
    metis_tac[ricf_call_event_source_root] >>
  `ircf_alloca_of original fsv fsz` by
    (simp[ircf_alloca_of_def] >> metis_tac[]) >>
  `?di. dfg_get_def (dfg_build_function original)
      (icf_assign_root (dfg_build_function original) {} fdst) = SOME di /\
    icf_is_alloca di` by
    (qpat_assum `ricf_located_event ctxP original logP roundP bp esP prefixP f prior`
       (mp_then Any mp_tac ricf_located_event_original_destination_alloca) >>
     simp[]) >>
  `MEM (ricf_event_copy e (EL b original.fn_blocks)) (fn_insts original) /\
   (ricf_event_copy e (EL b original.fn_blocks)).inst_opcode = MCOPY` by
    (irule ricf_call_located_copy_member >> metis_tac[]) >>
  `~ircf_alias original
    (icf_assign_root (dfg_build_function original) {} dst) fsv` by
    (irule ricf_call_copy_source_not_destination_alias >>
     goal_assum (drule_at Any) >> simp[] >>
     fs[ricf_event_copy_def] >> metis_tac[ircf_assign_root_alias, EL_MEM]) >>
  strip_tac >> gvs[]
QED

Theorem ricf_call_recorded_site_original_operand:
  ricf_located_event ctx0 original log round b es prefix e current /\
  ssa_form original /\ fn_inst_wf original /\
  ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts original)) /\
  ricf_full_alloca_copies original /\ ricf_src_alloca original /\
  (ricf_event_copy e (EL b original.fn_blocks)).inst_operands =
    [Var dst;src;sz] /\ MEM (ri,p) e.rfe_sites ==>
  ?cb i v.
    cb < LENGTH original.fn_blocks /\
    i < LENGTH (EL cb original.fn_blocks).bb_instructions /\
    ri = EL i (EL cb round.fn_blocks).bb_instructions /\
    (EL i (EL cb original.fn_blocks).bb_instructions).inst_opcode = INVOKE /\
    p < LENGTH (EL i (EL cb original.fn_blocks).bb_instructions).inst_operands /\
    EL p (EL i (EL cb original.fn_blocks).bb_instructions).inst_operands =
      EL p ri.inst_operands /\
    EL p ri.inst_operands = Var v /\
    ircf_alias original
      (icf_assign_root (dfg_build_function original) {} dst) v
Proof
  strip_tac >> drule_all ricf_call_recorded_site_alias >> strip_tac >>
  drule_all ricf_located_event_call_position >> strip_tac >>
  `p < LENGTH (EL i (EL cb original.fn_blocks).bb_instructions).inst_operands` by
    (fs[decode_invoke_def, AllCaseEqs()] >> metis_tac[]) >>
  `?pre. ricf_logged_function_trace ctx0 original pre round` by
    (fs[ricf_located_event_def] >>
     drule_all ricf_logged_function_trace_prefix >> metis_tac[]) >>
  `EL p ri.inst_operands =
    EL p (EL i (EL cb original.fn_blocks).bb_instructions).inst_operands` by
    (qpat_assum `ricf_logged_function_trace ctx0 original pre round`
       (mp_then Any (qspecl_then [`cb`,`i`,`p`] mp_tac)
         ricf_logged_function_operand_origin) >>
     simp[] >> strip_tac >> gvs[] >>
     drule_all ricf_call_recorded_site_not_forwarded_source >> simp[]) >>
  qexistsl_tac [`cb`,`i`,`v`] >> simp[] >> metis_tac[]
QED
