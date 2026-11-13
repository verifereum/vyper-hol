(* The readonly-analysis witness follows each actual source history. *)
Theory readonlyInvokeCopyFwdAnalyzedLifecycle
Ancestors
  readonlyInvokeCopyFwdAnalyzedOrigins readonlyInvokeCopyFwdHeterogeneousLifecycle
  readonlyInvokeCopyFwdHeterogeneousMapOrigins readonlyInvokeCopyFwdAlignedOrigins
  readonlyInvokeCopyFwdHistoryPhase readonlyInvokeCopyFwdHistoryPhaseAllocation
  readonlyInvokeCopyFwdHistoryStackAlignment readonlyInvokeCopyFwdHistoryOrigin
  readonlyInvokeCopyFwdProtection
  o1LowerDloadOccurrence venomExecSemantics venomState finite_map list pred_set

Theorem ricf_analyzed_map_origins_block:
  ricf_analyzed_map_origins vs C stk PG G tn fn inst s U B sites /\
  active_inst fn inst s /\ is_terminator inst.inst_opcode /\
  step_inst fuel C inst s = OK u /\ ~u.vs_halted /\
  enters_block fn u s1 /\ active_inst fn next s1 ==>
  ricf_analyzed_map_origins vs C stk PG (entry_prov fn u G)
    (entry_taint_vars fn u tn) fn next s1 U B sites
Proof
  rw[ricf_analyzed_map_origins_def] >> first_x_assum drule >>
  rw[ricf_aligned_translation_origin_def] >>
  qexistsl_tac [`ctxP`,`logP`] >> simp[] >>
  qexistsl_tac [`p`,`pre`,`anchor`,`tail`,`atn`] >> irule ricf_aligned_origin_block >> metis_tac[]
QED

Theorem ricf_analyzed_saved_map_origins_block:
  ricf_analyzed_saved_map_origins vs C stk PG G tn fn inst s U B maps /\
  active_inst fn inst s /\ is_terminator inst.inst_opcode /\
  step_inst fuel C inst s = OK u /\ ~u.vs_halted /\
  enters_block fn u s1 /\ active_inst fn next s1 ==>
  ricf_analyzed_saved_map_origins vs C stk PG (entry_prov fn u G)
    (entry_taint_vars fn u tn) fn next s1 U B maps
Proof
  rw[ricf_analyzed_saved_map_origins_def] >>
  qpat_x_assum `!j key tr. _` (qspecl_then [`j`,`key`,`tr`] mp_tac) >>
  simp[] >> strip_tac >>
  qexistsl_tac [`ctxP`,`logP`,`p`,`pre`,`anchor`,`tail`,`atn`] >> simp[] >>
  irule ricf_aligned_origin_block >> metis_tac[]
QED

Theorem ricf_analyzed_map_origins_sites_step:
  ricf_analyzed_map_origins vs C stk PG G tn fn inst s U B sites /\
  occurrence_allocas_ok B a s0 /\ alloc_inst.inst_opcode = ALLOCA /\
  step_inst fuel C alloc_inst s0 = OK u ==>
  ricf_analyzed_map_origins vs C stk PG G tn fn inst s U
    (occurrence_sites_step a B alloc_inst u) sites
Proof
  rw[ricf_analyzed_map_origins_def] >> first_x_assum drule >>
  rw[ricf_aligned_translation_origin_def] >>
  qexistsl_tac [`ctxP`,`logP`] >> simp[] >>
  qexistsl_tac [`p`,`pre`,`anchor`,`tail`,`atn`] >> irule ricf_aligned_origin_sites_step >> metis_tac[]
QED

Theorem ricf_analyzed_saved_map_origins_sites_step:
  ricf_analyzed_saved_map_origins vs C stk PG G tn fn inst s U B maps /\
  occurrence_allocas_ok B a s0 /\ alloc_inst.inst_opcode = ALLOCA /\
  step_inst fuel C alloc_inst s0 = OK u ==>
  ricf_analyzed_saved_map_origins vs C stk PG G tn fn inst s U
    (occurrence_sites_step a B alloc_inst u) maps
Proof
  rw[ricf_analyzed_saved_map_origins_def] >>
  qpat_x_assum `!j key tr. _` (qspecl_then [`j`,`key`,`tr`] mp_tac) >>
  simp[] >> strip_tac >>
  qexistsl_tac [`ctxP`,`logP`,`p`,`pre`,`anchor`,`tail`,`atn`] >> simp[] >>
  irule ricf_aligned_origin_sites_step >> metis_tac[]
QED

Theorem ricf_analyzed_map_origins_call:
  ricf_analyzed_map_origins vs C stk PG G tn caller callinst s U B sites /\
  active_inst caller callinst s /\ callinst.inst_opcode = INVOKE /\
  decode_invoke callinst = SOME (nm,ops) /\
  lookup_function nm C.ctx_functions = SOME callee /\
  eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
  enters_block callee cs s1 /\ active_inst callee inst s1 /\
  f = <|cf_fn := caller; cf_inst := callinst; cf_state := s;
        cf_params := PG; cf_prov := G; cf_tvar := tn.t_var|> ==>
  ricf_analyzed_map_origins vs C (f::stk) (MAP (op_prov G) ops)
    FEMPTY (tn with t_var := FEMPTY) callee inst s1 (u::U) B sites
Proof
  rw[ricf_analyzed_map_origins_def] >> first_x_assum drule >>
  rw[ricf_aligned_translation_origin_def] >>
  qexistsl_tac [`ctxP`,`logP`] >> simp[] >>
  qexistsl_tac [`p`,
    `<|cf_fn := caller; cf_inst := callinst; cf_state := s;
       cf_params := PG; cf_prov := G; cf_tvar := tn.t_var|> :: pre`,
    `anchor`,`tail`,`atn`] >>
  irule ricf_aligned_origin_call >> metis_tac[]
QED

Theorem ricf_analyzed_saved_map_origins_call:
  ricf_analyzed_map_origins vs C stk PG G tn caller callinst s U B sites /\
  ricf_analyzed_saved_map_origins vs C stk PG G tn caller callinst s U B maps /\
  active_inst caller callinst s /\ callinst.inst_opcode = INVOKE /\
  decode_invoke callinst = SOME (nm,ops) /\
  lookup_function nm C.ctx_functions = SOME callee /\
  eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
  enters_block callee cs s1 /\ active_inst callee inst s1 /\
  f = <|cf_fn := caller; cf_inst := callinst; cf_state := s;
        cf_params := PG; cf_prov := G; cf_tvar := tn.t_var|> ==>
  ricf_analyzed_saved_map_origins vs C (f::stk) (MAP (op_prov G) ops)
    FEMPTY (tn with t_var := FEMPTY) callee inst s1 (u::U) B (sites::maps)
Proof
  rw[ricf_analyzed_saved_map_origins_def] >> Cases_on `j`
  >- (gvs[ricf_analyzed_map_origins_def] >>
      first_x_assum drule >> rw[ricf_aligned_translation_origin_def] >>
      qexistsl_tac [`ctxP`,`logP`,`p`,
        `<|cf_fn := caller; cf_inst := callinst; cf_state := s;
           cf_params := PG; cf_prov := G; cf_tvar := tn.t_var|> :: pre`,
        `anchor`,`tail`,`atn`] >> simp[] >>
      irule ricf_aligned_origin_call >> metis_tac[]) >>
  gvs[] >> rename1 `FLOOKUP (EL depth maps) key = SOME tr` >>
  qpat_x_assum `!j key tr. _` (qspecl_then [`depth`,`key`,`tr`] mp_tac) >>
  simp[] >> strip_tac >>
  qexistsl_tac [`ctxP`,`logP`,`p`,
    `<|cf_fn := caller; cf_inst := callinst; cf_state := s;
       cf_params := PG; cf_prov := G; cf_tvar := tn.t_var|> :: pre`,
    `anchor`,`tail`,`atn`] >> simp[] >>
  irule ricf_aligned_origin_call >> metis_tac[]
QED

Theorem ricf_analyzed_saved_map_origins_return:
  ricf_analyzed_saved_map_origins vs C (f::stk) PG G tn fn rinst s
    (u::U) B (sites::maps) /\
  occ_frame_reachable vs C (f::stk) PG G tn fn rinst s n a (u::U) B HP H /\
  active_inst fn rinst s /\ step_inst fuel C rinst s = IntRet ret se /\
  bind_outputs f.cf_inst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state f.cf_state se)) = SOME s' /\
  active_inst f.cf_fn next (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx) ==>
  ricf_analyzed_map_origins vs C stk f.cf_params
    (DRESTRICT f.cf_prov (COMPL (set f.cf_inst.inst_outputs)))
    (tn with t_var := DRESTRICT f.cf_tvar (COMPL (set f.cf_inst.inst_outputs)))
    f.cf_fn next (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx) U
    (DRESTRICT B {id | FST id <> a}) sites /\
  ricf_analyzed_saved_map_origins vs C stk f.cf_params
    (DRESTRICT f.cf_prov (COMPL (set f.cf_inst.inst_outputs)))
    (tn with t_var := DRESTRICT f.cf_tvar (COMPL (set f.cf_inst.inst_outputs)))
    f.cf_fn next (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx) U
    (DRESTRICT B {id | FST id <> a}) maps
Proof
  strip_tac >> drule occ_frame_reachable_owner_fresh >> strip_tac >>
  fs[ricf_analyzed_saved_map_origins_def] >>
  conj_tac
  >- (rw[ricf_analyzed_map_origins_def] >>
      qpat_x_assum `!j key tr. _` (qspecl_then [`0`,`key`,`tr`] mp_tac) >>
      simp[] >> strip_tac >>
      `p.rpe_owner <> a` by
        (`ALL_DISTINCT (a::MAP (\u. u.of_owner) (u::U))` by simp[] >>
         metis_tac[ricf_aligned_origin_owner_old]) >>
      Cases_on `pre` >> gvs[] >>
      rename1 `ricf_aligned_origin_at _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
        (inner::rest) _ _ _` >>
      `inner = f /\ rest ++ anchor::tail = stk` by fs[ricf_aligned_origin_at_def] >>
      gvs[] >>
      qexistsl_tac [`ctxP`,`logP`] >>
      simp[ricf_aligned_translation_origin_def] >>
      qexistsl_tac [`p`,`rest`,`anchor`,`tail`,`atn`] >>
      irule ricf_aligned_origin_restrict_owner >> simp[] >>
      drule_all ricf_aligned_origin_nested_return >>
      simp_tac std_ss [GSYM APPEND_ASSOC, APPEND]) >>
  rw[ricf_analyzed_saved_map_origins_def] >>
  qpat_x_assum `!j key tr. _` (qspecl_then [`SUC j`,`key`,`tr`] mp_tac) >>
  simp[] >> strip_tac >>
  `p.rpe_owner <> a` by
        (`ALL_DISTINCT (a::MAP (\u. u.of_owner) (u::U))` by simp[] >>
         metis_tac[ricf_aligned_origin_owner_old]) >>
  Cases_on `pre` >> gvs[] >>
  rename1 `ricf_aligned_origin_at _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
    (inner::rest) _ _ _` >>
  `inner = f /\ rest ++ anchor::tail = stk` by fs[ricf_aligned_origin_at_def] >>
  gvs[] >>
  qexistsl_tac [`ctxP`,`logP`,`p`,`rest`,`anchor`,`tail`,`atn`] >> simp[] >>
  irule ricf_aligned_origin_restrict_owner >> simp[] >>
  drule_all ricf_aligned_origin_nested_return >>
      simp_tac std_ss [GSYM APPEND_ASSOC, APPEND]
QED

Theorem ricf_analyzed_ledger_next:
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H /\
  ricf_analyzed_ledger vs C stk PG G tn fn s a U B ledger /\
  active_inst fn inst s /\ ~is_terminator inst.inst_opcode /\
  inst.inst_opcode <> INVOKE /\ step_inst fuel C inst s = OK u ==>
  ricf_analyzed_ledger vs C stk PG (step_prov PG G inst u)
    (step_taint inst s u tn) fn (u with vs_inst_idx := SUC s.vs_inst_idx)
    a U (occurrence_sites_step a B inst u) ledger
Proof
  simp[ricf_analyzed_ledger_def, EVERY_MEM] >> rpt strip_tac >>
  `occurrence_allocas_ok B a s` by
    (drule occ_frame_reachable_annotation >> simp[occurrence_annotation_ok_def]) >>
  first_x_assum drule >> strip_tac >>
  qexistsl_tac [`ctxP`,`logP`] >> simp[] >>
  Cases_on `inst.inst_opcode = ALLOCA`
  >- (irule ricf_phase_entry_alloca >> metis_tac[]) >>
  irule ricf_phase_entry_next >> metis_tac[]
QED

Theorem ricf_analyzed_ledger_call:
  ricf_analyzed_ledger vs C stk PG G tn caller s a U B ledger /\
  active_inst caller callinst s /\ callinst.inst_opcode = INVOKE /\
  decode_invoke callinst = SOME (nm,ops) /\
  lookup_function nm C.ctx_functions = SOME callee /\
  eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
  enters_block callee cs s1 ==>
  ricf_analyzed_ledger vs C
    (<|cf_fn := caller; cf_inst := callinst; cf_state := s;
       cf_params := PG; cf_prov := G; cf_tvar := tn.t_var|> :: stk)
    (MAP (op_prov G) ops) FEMPTY (tn with t_var := FEMPTY) callee s1
    n (<|of_owner := a; of_prov := H; of_params := HP|> :: U) B
    (ricf_phase_push
      <|cf_fn := caller; cf_inst := callinst; cf_state := s;
        cf_params := PG; cf_prov := G; cf_tvar := tn.t_var|> ledger)
Proof
  simp[ricf_analyzed_ledger_def, ricf_phase_push_def, EVERY_MAP, EVERY_MEM] >>
  rpt strip_tac >> gvs[MEM_MAP] >> rename1 `MEM entry ledger` >>
  Cases_on `entry` >> gvs[] >> first_x_assum drule >> strip_tac >>
  qexistsl_tac [`ctxP`,`logP`] >> simp[] >>
  irule ricf_phase_entry_call >> metis_tac[]
QED

Theorem ricf_analyzed_ledger_return:
  occ_frame_reachable vs C (f::stk) PG G tn fn inst s n a (u::U) B HP H /\
  ricf_analyzed_ledger vs C (f::stk) PG G tn fn s a (u::U) B ledger /\
  active_inst fn inst s /\ step_inst fuel C inst s = IntRet ret se /\
  bind_outputs f.cf_inst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state f.cf_state se)) = SOME s' /\
  active_inst f.cf_fn next (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx) ==>
  ricf_analyzed_ledger vs C stk f.cf_params
    (DRESTRICT f.cf_prov (COMPL (set f.cf_inst.inst_outputs)))
    (tn with t_var := DRESTRICT f.cf_tvar (COMPL (set f.cf_inst.inst_outputs)))
    f.cf_fn (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx)
    u.of_owner U (DRESTRICT B {id | FST id <> a}) (ricf_phase_pop ledger)
Proof
  strip_tac >>
  rw[ricf_analyzed_ledger_def, EVERY_MEM, ricf_phase_pop_def, MEM_MAP, MEM_FILTER] >>
  rename1 `MEM entry ledger` >>
  `?ctxP logP. ctxP.icf_rma = readonly_mem_analyze C /\
    ricf_phase_entry vs C ctxP logP (f::stk) PG G tn fn s a (u::U) B entry` by
    fs[ricf_analyzed_ledger_def, EVERY_MEM] >>
  `ricf_source_ledger vs C ctxP logP (f::stk) PG G tn fn inst s
    n a (u::U) B HP H [entry]` by simp[ricf_source_ledger_def] >>
  drule_all ricf_source_ledger_return >> strip_tac >>
  qexistsl_tac [`ctxP`,`logP`] >>
  Cases_on `entry` >> gvs[ricf_source_ledger_def, ricf_phase_pop_def]
QED

Theorem ricf_analyzed_origins_return:
  occ_frame_reachable vs C (f::stk) PG G tn fn inst s n a (u::U) B HP H /\
  ricf_analyzed_origins vs C (f::stk) PG G tn fn inst s a (u::U) B
    ledger current (sites::maps) /\
  active_inst fn inst s /\ step_inst fuel C inst s = IntRet ret se /\
  bind_outputs f.cf_inst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state f.cf_state se)) = SOME s' /\
  active_inst f.cf_fn next (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx) ==>
  ricf_analyzed_origins vs C stk f.cf_params
    (DRESTRICT f.cf_prov (COMPL (set f.cf_inst.inst_outputs)))
    (tn with t_var := DRESTRICT f.cf_tvar (COMPL (set f.cf_inst.inst_outputs)))
    f.cf_fn next (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx)
    u.of_owner U (DRESTRICT B {id | FST id <> a})
    (ricf_phase_pop ledger) sites maps
Proof
  simp[ricf_analyzed_origins_def] >> strip_tac >>
  drule_all ricf_analyzed_saved_map_origins_return >> strip_tac >> simp[] >>
  irule ricf_analyzed_ledger_return >> metis_tac[]
QED

Theorem ricf_analyzed_ledger_block:
  ricf_analyzed_ledger vs C stk PG G tn fn s a U B ledger /\
  active_inst fn inst s /\ is_terminator inst.inst_opcode /\
  step_inst fuel C inst s = OK u /\ ~u.vs_halted /\
  enters_block fn u s1 /\ active_inst fn next s1 ==>
  ricf_analyzed_ledger vs C stk PG (entry_prov fn u G)
    (entry_taint_vars fn u tn) fn s1 a U B
    (FILTER (\entry. SND entry <> []) ledger)
Proof
  simp[ricf_analyzed_ledger_def, EVERY_MEM, MEM_FILTER] >>
  rpt strip_tac >>
  first_x_assum drule >> strip_tac >>
  Cases_on `entry` >> gvs[ricf_phase_entry_def] >>
  qexistsl_tac [`ctxP`, `logP`] >> simp[ricf_phase_entry_def] >>
  fs[ricf_history_cursor_def] >> Cases_on `r` >> gvs[] >>
  metis_tac[ricf_visit_prefix_block]
QED

Theorem ricf_analyzed_origins_next:
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H /\
  ricf_analyzed_origins vs C stk PG G tn fn inst s a U B ledger sites maps /\
  active_inst fn inst s /\ ~is_terminator inst.inst_opcode /\
  inst.inst_opcode <> INVOKE /\ step_inst fuel C inst s = OK u /\
  active_inst fn next (u with vs_inst_idx := SUC s.vs_inst_idx) ==>
  ricf_analyzed_origins vs C stk PG (step_prov PG G inst u)
    (step_taint inst s u tn) fn next (u with vs_inst_idx := SUC s.vs_inst_idx)
    a U (occurrence_sites_step a B inst u) ledger sites maps
Proof
  strip_tac >> fs[ricf_analyzed_origins_def] >>
  `occurrence_allocas_ok B a s` by
    (drule occ_frame_reachable_annotation >> simp[occurrence_annotation_ok_def]) >>
  conj_tac >- (irule ricf_analyzed_ledger_next >> metis_tac[]) >>
  conj_tac
  >- (`ricf_analyzed_map_origins vs C stk PG (step_prov PG G inst u)
       (step_taint inst s u tn) fn next (u with vs_inst_idx := SUC s.vs_inst_idx)
       U B sites` by
        (irule ricf_analyzed_map_origins_next >> metis_tac[]) >>
      Cases_on `inst.inst_opcode = ALLOCA`
      >- (irule ricf_analyzed_map_origins_sites_step >> metis_tac[]) >>
      fs[occurrence_sites_step_def]) >>
  `ricf_analyzed_saved_map_origins vs C stk PG (step_prov PG G inst u)
     (step_taint inst s u tn) fn next (u with vs_inst_idx := SUC s.vs_inst_idx)
     U B maps` by
    (irule ricf_analyzed_saved_map_origins_next >> metis_tac[]) >>
  Cases_on `inst.inst_opcode = ALLOCA`
  >- (irule ricf_analyzed_saved_map_origins_sites_step >> metis_tac[]) >>
  fs[occurrence_sites_step_def]
QED
