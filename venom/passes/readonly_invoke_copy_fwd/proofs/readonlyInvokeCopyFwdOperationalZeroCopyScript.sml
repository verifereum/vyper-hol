(* Actual empty erased copies retain all relational and history indices. *)
Theory readonlyInvokeCopyFwdOperationalZeroCopy
Ancestors
  readonlyInvokeCopyFwdHistoryAvailability readonlyInvokeCopyFwdCopyFrontier
  readonlyInvokeCopyFwdCopyAnnotations readonlyInvokeCopyFwdHeterogeneousLedger
  readonlyInvokeCopyFwdGlobalSupport readonlyInvokeCopyFwdOperationalSupport
  readonlyInvokeCopyFwdRel internalReturnCopyFwdSim
  venomExecSemantics venomState ptrDiscipline taintAgree
  o1LowerDloadOccurrence readonlyInvokeCopyFwdStepsCore
  finite_map list pred_set words

Theorem ricf_cert_zero_copy:
  ricf_cert_core D ids stk PG G tn fn sites maps targets G0 tn0 cur curs s t ==>
  ricf_cert_core D ids stk PG G tn fn sites maps targets G0 tn0 cur curs
    (mcopy db sb 0 s) t
Proof
  strip_tac >>
  `ricf_cert_core D ids stk PG G
    (if s.vs_prev_bb = NONE then tn0 else entry_taint_vars fn s tn0)
    fn sites maps targets G0 tn0 (cur UNION {(db,sb,0)}) curs
    (mcopy db sb 0 s) t` by
    (irule ricf_cert_activate_copy_frontier >>
     simp[SUBSET_DEF, EXTENSION] >> metis_tac[arithmeticTheory.LESS_EQ_CASES]) >>
  `tn = if s.vs_prev_bb = NONE then tn0 else entry_taint_vars fn s tn0` by
    fs[ricf_cert_core_def, ricf_live_boundary_core_def] >>
  fs[ricf_cert_core_def, ircf_cross_def] >> metis_tac[]
QED

Theorem ricf_operational_zero_copy:
  EVERY wf_ssa C.ctx_functions /\ EVERY wf_function C.ctx_functions /\
  EVERY fn_inst_wf C.ctx_functions /\
  vs.vs_allocas = FEMPTY /\ ~ctx_has_dalloca C /\
  ricf_full_alloca_copies fn /\ ricf_src_alloca fn /\
  ALL_DISTINCT (MAP (\inst. inst.inst_id) (fn_insts fn)) /\
  ricf_located_event ctx0 fn log round b es prefix e current /\
  ricf_heterogeneous_source_ledger vs C stk PG G tn fn
    (ricf_event_copy e (EL b fn.fn_blocks)) s n a U B HP H ledger /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME (EL b fn.fn_blocks) /\
  s.vs_inst_idx = e.rfe_index /\
  active_inst fn (ricf_event_copy e (EL b fn.fn_blocks)) s /\
  (ricf_event_copy e (EL b fn.fn_blocks)).inst_operands = [Var dst;Var sv;Lit 0w] /\
  ricf_cert_core D ids stk PG G tn fn sites maps targets G0 tn0 cur curs s t /\
  ricf_global_support_origins vs C ctx0 a fn U stk B E /\
  ricf_support_agree B E tn s t /\
  nop.inst_opcode = NOP /\ nop.inst_operands = [] /\ nop.inst_outputs = [] ==>
  ?u.
    step_inst fuel C (ricf_event_copy e (EL b fn.fn_blocks)) s = OK u /\
    step_inst fuel C' nop t = OK t /\
    ricf_cert_core D ids stk PG
      (step_prov PG G (ricf_event_copy e (EL b fn.fn_blocks)) u)
      (step_taint (ricf_event_copy e (EL b fn.fn_blocks)) s u tn)
      fn sites maps targets G0 tn0 cur curs u t /\
    ricf_cert_core D ids stk PG
      (step_prov PG G (ricf_event_copy e (EL b fn.fn_blocks)) u)
      (step_taint (ricf_event_copy e (EL b fn.fn_blocks)) s u tn)
      fn sites maps targets G0 tn0 cur curs
      (u with vs_inst_idx := SUC s.vs_inst_idx)
      (t with vs_inst_idx := SUC t.vs_inst_idx) /\
    ricf_support_agree B E
      (step_taint (ricf_event_copy e (EL b fn.fn_blocks)) s u tn) u t /\
    ricf_global_support_origins vs C ctx0 a fn U stk
      (occurrence_sites_step a B (ricf_event_copy e (EL b fn.fn_blocks)) u) E /\
    (!next. active_inst fn next (u with vs_inst_idx := SUC s.vs_inst_idx) ==>
      ricf_heterogeneous_source_ledger vs C stk PG
        (step_prov PG G (ricf_event_copy e (EL b fn.fn_blocks)) u)
        (step_taint (ricf_event_copy e (EL b fn.fn_blocks)) s u tn) fn next
        (u with vs_inst_idx := SUC s.vs_inst_idx) n a U
        (occurrence_sites_step a B (ricf_event_copy e (EL b fn.fn_blocks)) u)
        HP (occurrence_step a HP H (ricf_event_copy e (EL b fn.fn_blocks)) u) ledger)
Proof
  strip_tac >>
  `occ_frame_reachable vs C stk PG G tn fn
    (ricf_event_copy e (EL b fn.fn_blocks)) s n a U B HP H` by
    fs[ricf_heterogeneous_source_ledger_def] >>
  drule_all ricf_located_event_operands_available >> strip_tac >> gvs[] >>
  qabbrev_tac `inst = ricf_event_copy e (EL b fn.fn_blocks)` >>
  `MEM fn C.ctx_functions` by metis_tac[occ_frame_reachable_annotation] >>
  `fn_inst_wf fn` by fs[EVERY_MEM] >>
  `inst.inst_outputs = []` by
    (`inst_wf inst` by
       (fs[venomWfTheory.fn_inst_wf_def, contextCodegenRelTheory.active_inst_def] >>
        metis_tac[EL_MEM]) >>
     gvs[venomWfTheory.inst_wf_def]) >>
  `G = ricf_effective_prov fn s G0 /\ tn = ricf_effective_taint fn s tn0 /\
   s.vs_inst_idx = t.vs_inst_idx` by
    (fs[ricf_cert_core_def, ricf_live_boundary_core_def,
        ricf_frame_agree_def, ricf_effective_prov_def, ricf_effective_taint_def,
        taint_agree_def, o1LowerDloadSharedTheory.ld_shared_agree_def] >>
     first_x_assum (mp_tac o AP_TERM ``\v:venom_state. v.vs_inst_idx``) >> simp[]) >>
  qmatch_goalsub_abbrev_tac `step_prov PG G inst u` >>
  `ricf_cert_core D ids stk PG G tn fn sites maps targets G0 tn0 cur curs u t` by
    (simp[Abbr `u`] >> irule ricf_cert_zero_copy >> metis_tac[]) >>
  `step_prov PG G inst u = G /\ step_taint inst s u tn = tn` by
    (`eval_operand (Var dst) s = SOME (n2w db) /\
      eval_operand (Var sv) s = SOME (n2w sb) /\
      eval_operand (Lit 0w) s = SOME 0w` by
       gvs[eval_operands_def, AllCaseEqs()] >>
     conj_tac >- simp[step_prov_def, set_prov_def, DRESTRICT_UNIV] >>
     drule_all step_taint_mcopy >>
     simp[Abbr `u`, EXTENSION]) >>
  `ricf_cert_core D ids stk PG (step_prov PG G inst u) (step_taint inst s u tn)
     fn sites maps targets G0 tn0 cur curs
     (u with vs_inst_idx := SUC s.vs_inst_idx)
     (t with vs_inst_idx := SUC s.vs_inst_idx)` by
    (irule ricf_cert_copy_successor >> simp[Abbr `u`] >>
     conj_tac
     >- (qexistsl_tac [`db MOD dimword (:256)`, `sb MOD dimword (:256)`] >> simp[]) >>
     fs[ricf_effective_taint_def] >> metis_tac[]) >>
  gvs[] >>
  conj_tac >- simp[Once step_inst_def, step_inst_base_def] >>
  conj_tac >- (simp[Abbr `u`] >> irule ricf_support_zero_copy >> simp[]) >>
  conj_tac >- (irule ricf_global_support_next >>
    `occurrence_allocas_ok B a s` by
      (drule occ_frame_reachable_annotation >> simp[occurrence_annotation_ok_def]) >>
    metis_tac[]) >>
  rpt strip_tac >>
  `~is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE` by
    simp[venomInstTheory.is_terminator_def] >>
  metis_tac[ricf_heterogeneous_source_ledger_actual_next]
QED
