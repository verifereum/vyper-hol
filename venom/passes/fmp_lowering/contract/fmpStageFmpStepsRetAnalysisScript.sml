Theory fmpStageFmpStepsRetAnalysis
Ancestors
  fmpStageRel fmpLowerReclaimPlan fmpLedgerProps fmpReclaimDefs
  fmpStageReclaimSound venomExecSemantics venomState venomInst
  dftGasInvCallPartner finite_map list

(* INVOKE transfers the already-popped stack, unless the callee publishes. *)
Theorem fmp_return_analysis_suc:
  fmp_reclaim_states infos fn = SOME states /\
  fmp_base_analyze (fn_insts fn) = SOME env /\
  ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks) /\
  MEM bb fn.fn_blocks /\ k < LENGTH bb.bb_instructions /\
  (EL k bb.bb_instructions).inst_opcode = INVOKE /\
  ~fmp_clears_marks infos (EL k bb.bb_instructions) /\
  df_at NONE states bb.bb_label k = SOME st ==>
  ?st'. df_at NONE states bb.bb_label (SUC k) = SOME st' /\
    st'.frs_stack = SND (fmp_pop_at infos fn (liveness_analyze fn) env
      (bb.bb_label,k) (EL k bb.bb_instructions) st)
Proof
  strip_tac >> drule_all fmp_reclaim_states_df_at_suc >>
  simp[fmp_transfer_def, fmp_reclaim_step_def] >>
  Cases_on `fmp_pop_at infos fn (liveness_analyze fn) env
    (bb.bb_label,k) (EL k bb.bb_instructions) st` >>
  simp[fmp_apply_effect_def] >> metis_tac[]
QED

Theorem fmp_return_covers:
  fmp_frame_covers sm env eb lo G ==>
  fmp_frame_covers sm env eb lo (DRESTRICT G A)
Proof
  simp[fmp_frame_covers_def, FLOOKUP_DRESTRICT] >>
  rpt strip_tac >> gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem fmp_return_ledger_bind:
  fmp_ledger_ok insts env t lo regions /\
  (!r. MEM r regions ==> ~MEM r.fr_mark outs) /\
  bind_outputs outs vals
    (adopt_return_fmp ret (merge_callee_state t callee)) = SOME t' ==>
  fmp_ledger_ok insts env (t' with vs_inst_idx := idx) lo regions
Proof
  strip_tac >> irule fmp_ledger_frame >>
  qexists_tac `t` >> simp[] >> rpt strip_tac >>
  `~MEM r.fr_mark outs` by metis_tac[] >>
  drule_all inv_bind_outputs_lookup_outside >>
  simp[lookup_var_def, adopt_return_fmp_def, merge_callee_state_def] >>
  Cases_on `ret.iret_adopt_fmp` >> simp[]
QED

(* The root-dependent conjunct, separated from control and environment transport.
   Lookup freshness is explicit: the caller boundary supplies it for the runner
   and the ledger marks from the unchanged INVOKE outputs. *)
Theorem fmp_return_root_analysis:
  fmp_base_analyze (fn_insts fn) = SOME env /\
  fmp_reclaim_states infos fn = SOME states /\
  ALL_DISTINCT (MAP (\b. b.bb_label) fn.fn_blocks) /\
  MEM bb fn.fn_blocks /\ k < LENGTH bb.bb_instructions /\
  (EL k bb.bb_instructions).inst_opcode = INVOKE /\
  ~fmp_clears_marks infos (EL k bb.bb_instructions) /\
  df_at NONE states bb.bb_label k = SOME st /\
  fmp_frame_covers sm env eb lo G /\
  (bb.bb_label = rl ==> rp <> SUC k) /\
  s1.vs_params = s.vs_params /\ t1.vs_params = t.vs_params /\
  bind_outputs outs vals
    (adopt_return_fmp ret (merge_callee_state t callee)) = SOME t1 /\
  ~MEM runner outs /\
  (!v. MEM v (SND (fmp_pop_at infos fn (liveness_analyze fn) env
     (bb.bb_label,k) (EL k bb.bb_instructions) st)) ==> ~MEM v outs) /\
  (if bb.bb_label = rl /\ k < rp then
     lo = elo /\
     SND (fmp_pop_at infos fn (liveness_analyze fn) env
       (bb.bb_label,k) (EL k bb.bb_instructions) st) = [] /\
     (fn_is_context_entry ctx fn ==> fmp0 = elo) /\
     (~fn_is_context_entry ctx fn ==>
       LENGTH s.vs_params = LENGTH (fn_user_param_insts fn) /\
       LENGTH s.vs_params < LENGTH t.vs_params /\
       EL (LENGTH s.vs_params) t.vs_params = n2w elo)
   else lookup_var runner t = SOME (n2w lo) /\
     ?regions. fmp_ledger_ok (fn_insts fn) env t lo regions /\
       MAP (\r. r.fr_mark) regions =
         SND (fmp_pop_at infos fn (liveness_analyze fn) env
           (bb.bb_label,k) (EL k bb.bb_instructions) st) /\
       EVERY (\r. elo <= r.fr_lo) regions /\
       fmp_ledger_link sm eb lo regions) ==>
  ?st1. df_at NONE states bb.bb_label (SUC k) = SOME st1 /\
    fmp_frame_covers sm env eb lo (DRESTRICT G A) /\
    (if bb.bb_label = rl /\ SUC k < rp then
       lo = elo /\ st1.frs_stack = [] /\
       (fn_is_context_entry ctx fn ==> fmp0 = elo) /\
       (~fn_is_context_entry ctx fn ==>
         LENGTH s1.vs_params = LENGTH (fn_user_param_insts fn) /\
         LENGTH s1.vs_params < LENGTH t1.vs_params /\
         EL (LENGTH s1.vs_params) t1.vs_params = n2w elo)
     else lookup_var runner t1 = SOME (n2w lo) /\
       ?regions. fmp_ledger_ok (fn_insts fn) env (t1 with vs_inst_idx := tidx)
           lo regions /\
         MAP (\r. r.fr_mark) regions = st1.frs_stack /\
         EVERY (\r. elo <= r.fr_lo) regions /\
         fmp_ledger_link sm eb lo regions)
Proof
  strip_tac >>
  `lookup_var runner t1 = lookup_var runner t` by
    (drule_all inv_bind_outputs_lookup_outside >>
     simp[lookup_var_def, adopt_return_fmp_def, merge_callee_state_def] >>
     Cases_on `ret.iret_adopt_fmp` >> simp[]) >>
  `bb.bb_label = rl /\ SUC k < rp <=> bb.bb_label = rl /\ k < rp` by
    (Cases_on `bb.bb_label = rl` >> gvs[] >> decide_tac) >>
  drule_all fmp_return_analysis_suc >> strip_tac >>
  qexists_tac `st'` >> simp[] >>
  conj_tac >- metis_tac[fmp_return_covers] >>
  Cases_on `bb.bb_label = rl` >> Cases_on `k < rp` >> gvs[] >>
  qexists_tac `regions` >> simp[] >>
  `!r. MEM r regions ==> ~MEM r.fr_mark outs` by
    (rpt strip_tac >>
     `MEM r.fr_mark (MAP (\r. r.fr_mark) regions)` by
       (simp[MEM_MAP] >> metis_tac[]) >>
     gvs[]) >>
  metis_tac[fmp_return_ledger_bind]
QED
