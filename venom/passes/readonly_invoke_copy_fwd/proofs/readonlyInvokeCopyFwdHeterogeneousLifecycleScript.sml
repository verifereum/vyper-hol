(* Pointwise reuse of the source lifecycle for independently located histories. *)
Theory readonlyInvokeCopyFwdHeterogeneousLifecycle
Ancestors
  readonlyInvokeCopyFwdHeterogeneousLedger readonlyInvokeCopyFwdHistoryStackAlignment
  readonlyInvokeCopyFwdHistoryPhase o1LowerDloadOccurrence
  venomExecSemantics venomState finite_map list pred_set

Theorem ricf_outer_sites_step:
  DRESTRICT (occurrence_sites_step a B inst s) {id | FST id <> a} =
  DRESTRICT B {id | FST id <> a}
Proof
  rw[occurrence_sites_step_def] >> CASE_TAC >> simp[DRESTRICT_FUPDATE]
QED

Theorem ricf_outer_support_activate:
  {id | id IN E UNION {(a,k)} /\ FST id <> a} =
  {id | id IN E /\ FST id <> a}
Proof
  simp[EXTENSION, pairTheory.FORALL_PROD] >> metis_tac[]
QED

Theorem ricf_phase_pop_push:
  !ledger. ricf_phase_pop (ricf_phase_push f ledger) = ledger
Proof
  Induct >> simp[ricf_phase_push_def, ricf_phase_pop_def] >>
  Cases_on `h` >> simp[] >> gvs[ricf_phase_push_def, ricf_phase_pop_def]
QED

Theorem ricf_phase_push_outer:
  !ledger. FILTER (\entry. SND entry <> []) (ricf_phase_push f ledger) =
    ricf_phase_push f ledger
Proof
  Induct >> simp[ricf_phase_push_def] >> Cases_on `h` >>
  gvs[ricf_phase_push_def]
QED

Theorem ricf_phase_outer_retire:
  FILTER (\entry. SND entry <> [])
    (FILTER (\entry. SND entry <> []) ledger) =
  FILTER (\entry. SND entry <> []) ledger
Proof
  simp[rich_listTheory.FILTER_FILTER, combinTheory.o_DEF]
QED

Theorem ricf_phase_pop_outer:
  FILTER (\entry. SND entry <> []) ledger = ricf_phase_push f caller_ledger ==>
  ricf_phase_pop ledger = caller_ledger
Proof
  strip_tac >>
  `(\(p,pre). pre <> []) = (\entry. SND entry <> [])` by
    simp[FUN_EQ_THM, pairTheory.FORALL_PROD] >>
  `ricf_phase_pop ledger = ricf_phase_pop (ricf_phase_push f caller_ledger)` by
    (simp[ricf_phase_pop_def] >> metis_tac[ricf_phase_push_outer]) >>
  metis_tac[ricf_phase_pop_push]
QED

Theorem ricf_heterogeneous_source_ledger_call:
  ricf_heterogeneous_source_ledger vs C stk PG G tn caller callinst s n a U B HP H ledger /\
  active_inst caller callinst s /\ callinst.inst_opcode = INVOKE /\
  decode_invoke callinst = SOME (nm,ops) /\
  lookup_function nm C.ctx_functions = SOME callee /\
  eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
  enters_block callee cs s1 /\ active_inst callee inst s1 ==>
  ricf_heterogeneous_source_ledger vs C
    (<|cf_fn := caller; cf_inst := callinst; cf_state := s;
       cf_params := PG; cf_prov := G; cf_tvar := tn.t_var|> :: stk)
    (MAP (op_prov G) ops) FEMPTY (tn with t_var := FEMPTY) callee inst s1
    (SUC n) n (<|of_owner := a; of_prov := H; of_params := HP|> :: U)
    B (MAP (op_prov H) ops) FEMPTY
    (ricf_phase_push
      <|cf_fn := caller; cf_inst := callinst; cf_state := s;
        cf_params := PG; cf_prov := G; cf_tvar := tn.t_var|> ledger)
Proof
  simp[ricf_heterogeneous_source_ledger_def, ricf_phase_push_def,
       EVERY_MAP, EVERY_MEM] >> rpt strip_tac
  >- (irule occ_frame_reachable_call >> metis_tac[]) >>
  gvs[MEM_MAP] >> rename1 `MEM entry ledger` >>
  Cases_on `entry` >> gvs[] >> first_x_assum drule >> strip_tac >>
  qexistsl_tac [`ctxP`,`logP`] >>
  irule ricf_phase_entry_call >> metis_tac[]
QED

Theorem ricf_heterogeneous_source_ledger_return:
  ricf_heterogeneous_source_ledger vs C (f::stk) PG G tn fn inst s n a (u::U) B HP H ledger /\
  active_inst fn inst s /\ step_inst fuel C inst s = IntRet ret se /\
  bind_outputs f.cf_inst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state f.cf_state se)) = SOME s' /\
  active_inst f.cf_fn next (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx) ==>
  ricf_heterogeneous_source_ledger vs C stk f.cf_params
    (DRESTRICT f.cf_prov (COMPL (set f.cf_inst.inst_outputs)))
    (tn with t_var := DRESTRICT f.cf_tvar (COMPL (set f.cf_inst.inst_outputs)))
    f.cf_fn next (s' with vs_inst_idx := SUC f.cf_state.vs_inst_idx)
    n u.of_owner U (DRESTRICT B {id | FST id <> a}) u.of_params
    (DRESTRICT u.of_prov (COMPL (set f.cf_inst.inst_outputs)))
    (ricf_phase_pop ledger)
Proof
  simp[ricf_heterogeneous_source_ledger_def] >> strip_tac >>
  conj_tac >- (irule occ_frame_reachable_ret >> metis_tac[]) >>
  rw[EVERY_MEM, ricf_phase_pop_def, MEM_MAP, MEM_FILTER] >>
  rename1 `MEM entry ledger` >>
  `?ctxP logP. ricf_phase_entry vs C ctxP logP
    (f::stk) PG G tn fn s a (u::U) B entry` by fs[EVERY_MEM] >>
  `ricf_source_ledger vs C ctxP logP (f::stk) PG G tn fn inst s
    n a (u::U) B HP H [entry]` by simp[ricf_source_ledger_def] >>
  drule_all ricf_source_ledger_return >> strip_tac >>
  qexistsl_tac [`ctxP`,`logP`] >>
  Cases_on `entry` >> gvs[ricf_source_ledger_def, ricf_phase_pop_def]
QED
