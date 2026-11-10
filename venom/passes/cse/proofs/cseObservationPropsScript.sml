Theory cseObservationProps
Ancestors cseHistoryProps venomInst venomInstProps venomExecSemantics venomState
  venomEffects venomInstProofs1 vfmState list availExprProofs dftBlockSim
Libs cseReplayLib

Theorem cse_prefix_observation_fold:
 !ctx fn fuel0 s0 events phase.
 cse_prefix ctx fn fuel0 s0 events phase ==>
 !obs survives.
 (!s k. obs (s with vs_inst_idx := k) = obs s) /\
 (!fuel bb s t. eval_phis s bb.bb_instructions = OK t ==>
    survives (CsePhi fuel bb s t) ==> obs t = obs s) /\
 (!fuel bb inst s t. step_inst fuel ctx inst s = OK t ==>
    survives (CseStep fuel bb inst s t) ==> obs t = obs s) ==>
 obs (cse_phase_state phase) =
 FOLDL (\acc ev. if survives ev then acc else obs (cse_event_output ev))
   (obs s0) events
Proof
 ho_match_mp_tac cse_prefix_strongind >> rpt conj_tac
 >- simp[cse_phase_state_def]
 >> rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
 simp[cse_phase_state_def, rich_listTheory.FOLDL_APPEND, cse_event_output_def] >>
 IF_CASES_TAC >> gvs[cse_phase_state_def] >> metis_tac[]
QED

Theorem cse_observation_fold_surviving:
 !events survives obs acc. EVERY survives events ==>
 FOLDL (\a ev. if survives ev then a else obs (cse_event_output ev)) acc events = acc
Proof
 Induct >> simp[]
QED

Theorem cse_prefix_surviving_observation:
 cse_prefix ctx fn fuel0 s0 pre ph0 /\
 cse_prefix ctx fn fuel0 s0 (pre ++ post) ph1 /\
 (!s k. obs (s with vs_inst_idx := k) = obs s) /\
 (!fuel bb s t. eval_phis s bb.bb_instructions = OK t ==>
    survives (CsePhi fuel bb s t) ==> obs t = obs s) /\
 (!fuel bb inst s t. step_inst fuel ctx inst s = OK t ==>
    survives (CseStep fuel bb inst s t) ==> obs t = obs s) /\
 EVERY survives post ==>
 obs (cse_phase_state ph1) = obs (cse_phase_state ph0)
Proof
 strip_tac >>
 drule_all cse_prefix_observation_fold >> strip_tac >>
 qpat_x_assum `cse_prefix ctx fn fuel0 s0 pre ph0`
   (mp_then Any mp_tac cse_prefix_observation_fold) >>
 simp[rich_listTheory.FOLDL_APPEND, cse_observation_fold_surviving] >> metis_tac[]
QED

Theorem cse_step_terminator_account_frame:
 step_inst fuel ctx inst s = OK t /\ is_terminator inst.inst_opcode ==>
 t.vs_accounts = s.vs_accounts /\ t.vs_call_ctx = s.vs_call_ctx
Proof
 strip_tac >>
 `inst.inst_opcode <> INVOKE` by
   (Cases_on `inst.inst_opcode` >> gvs[is_terminator_def]) >>
 drule_all step_inst_non_invoke >> strip_tac >>
 Cases_on `inst.inst_opcode` >> gvs[is_terminator_def] >>
 cseReplayLib.selected_base_tac >>
 gvs[AllCaseEqs()] >> simp[jump_to_def] >>
 pairarg_tac >> gvs[]
QED

Theorem cse_step_storage_frame:
 step_inst fuel ctx inst s = OK t /\ ~is_alloca_op inst.inst_opcode /\
 Eff_STORAGE NOTIN write_effects inst.inst_opcode ==>
 contract_storage t = contract_storage s
Proof
 strip_tac >> Cases_on `is_terminator inst.inst_opcode`
 >- (drule_all cse_step_terminator_account_frame >>
     simp[contract_storage_def]) >>
 metis_tac[write_effects_sound_storage]
QED

Theorem cse_step_balance_account_frame:
 step_inst fuel ctx inst s = OK t /\ ~is_alloca_op inst.inst_opcode /\
 Eff_BALANCE NOTIN write_effects inst.inst_opcode ==>
 !addr. (lookup_account addr t.vs_accounts).balance =
          (lookup_account addr s.vs_accounts).balance /\
        (lookup_account addr t.vs_accounts).nonce =
          (lookup_account addr s.vs_accounts).nonce /\
        (lookup_account addr t.vs_accounts).code =
          (lookup_account addr s.vs_accounts).code
Proof
 strip_tac >> Cases_on `is_terminator inst.inst_opcode`
 >- (drule_all cse_step_terminator_account_frame >> simp[]) >>
 Cases_on `Eff_STORAGE IN write_effects inst.inst_opcode`
 >- (`inst.inst_opcode = SSTORE` by
       (Cases_on `inst.inst_opcode` >>
        gvs[write_effects_def, all_effects_def, empty_effects_def]) >>
     `inst.inst_opcode <> INVOKE` by simp[] >>
     drule_all step_inst_non_invoke >> strip_tac >>
     cseReplayLib.selected_base_tac >>
     gvs[AllCaseEqs(), exec_write2_def] >>
     simp[sstore_def, lookup_account_def, combinTheory.APPLY_UPDATE_THM] >>
     gen_tac >> IF_CASES_TAC >> simp[]) >>
 drule_all write_effects_sound_accounts >> simp[]
QED

Theorem cse_step_extcode_frame:
 step_inst fuel ctx inst s = OK t /\ ~is_alloca_op inst.inst_opcode /\
 Eff_EXTCODE NOTIN write_effects inst.inst_opcode ==>
 !addr. (lookup_account addr t.vs_accounts).code =
          (lookup_account addr s.vs_accounts).code /\
        (account_empty (lookup_account addr t.vs_accounts) <=>
         account_empty (lookup_account addr s.vs_accounts))
Proof
 strip_tac >> Cases_on `is_terminator inst.inst_opcode`
 >- (drule_all cse_step_terminator_account_frame >> simp[]) >>
 `Eff_BALANCE NOTIN write_effects inst.inst_opcode` by
   (Cases_on `inst.inst_opcode` >>
    gvs[write_effects_def, all_effects_def, empty_effects_def, is_terminator_def]) >>
 drule_all cse_step_balance_account_frame >> simp[account_empty_def]
QED

Theorem cse_eval_phis_observation:
 (!out value s. obs (update_var out value s) = obs s) ==>
 !insts s t. eval_phis s insts = OK t ==> obs t = obs s
Proof
 strip_tac >> Induct >> simp[eval_phis_def] >>
 rpt gen_tac >> strip_tac >>
 gvs[AllCaseEqs()] >> metis_tac[]
QED

Theorem cse_phi_account_frame:
 eval_phis s insts = OK t ==>
 t.vs_accounts = s.vs_accounts /\ t.vs_call_ctx = s.vs_call_ctx
Proof
 strip_tac >> conj_tac
 >- (irule cse_eval_phis_observation >>
     simp[update_var_def] >> metis_tac[]) >>
 irule cse_eval_phis_observation >>
 simp[update_var_def] >> metis_tac[]
QED

Theorem cse_index_storage_observation:
 contract_storage (s with vs_inst_idx := k) = contract_storage s
Proof
 simp[contract_storage_def]
QED

(* A guard localizes frame requirements to the observed interval's prefix. *)
Theorem cse_prefix_interval_observation:
 cse_prefix ctx fn fuel0 s0 pre ph0 /\
 cse_prefix ctx fn fuel0 s0 (pre ++ post) ph1 /\
 (!s k. obs (s with vs_inst_idx := k) = obs s) /\
 (!fuel bb s t. eval_phis s bb.bb_instructions = OK t ==>
    obs t = obs s) /\
 (!fuel bb inst s t. MEM (CseStep fuel bb inst s t) (pre ++ post) /\
    step_inst fuel ctx inst s = OK t /\ avail_source_survives e inst ==>
    obs t = obs s) /\
 EVERY (cse_event_survives e) post ==>
 obs (cse_phase_state ph1) = obs (cse_phase_state ph0)
Proof
 strip_tac >>
 `!fuel bb s t. eval_phis s bb.bb_instructions = OK t ==>
   (\ev. cse_event_survives e ev /\ MEM ev (pre ++ post))
      (CsePhi fuel bb s t) ==> obs t = obs s` by metis_tac[] >>
 `!fuel bb inst s t. step_inst fuel ctx inst s = OK t ==>
   (\ev. cse_event_survives e ev /\ MEM ev (pre ++ post))
      (CseStep fuel bb inst s t) ==> obs t = obs s` by
   (simp[cse_event_survives_def] >> metis_tac[MEM_APPEND]) >>
 `EVERY (\ev. cse_event_survives e ev /\ MEM ev (pre ++ post)) post` by
   gvs[EVERY_MEM] >>
 drule_all cse_prefix_surviving_observation >> simp[]
QED

Theorem cse_surviving_step_storage:
 step_inst fuel ctx inst s = OK t /\ ~is_alloca_op inst.inst_opcode /\
 avail_source_survives e inst /\ Eff_STORAGE IN root_effects e ==>
 contract_storage t = contract_storage s
Proof
 strip_tac >> Cases_on `is_terminator inst.inst_opcode`
 >- (drule_all cse_step_terminator_account_frame >> simp[contract_storage_def]) >>
 irule cse_step_storage_frame >>
 qexistsl [`ctx`, `fuel`, `inst`] >> simp[] >>
 gvs[avail_source_survives_def] >>
 Cases_on `inst.inst_opcode` >>
 gvs[is_pseudo_def, is_terminator_def, write_effects_def,
     empty_effects_def, all_effects_def, pred_setTheory.DISJOINT_DEF,
     pred_setTheory.EXTENSION] >> metis_tac[]
QED

Theorem cse_prefix_interval_storage:
 cse_prefix ctx fn fuel0 s0 pre ph0 /\
 cse_prefix ctx fn fuel0 s0 (pre ++ post) ph1 /\
 EVERY (cse_event_survives e) post /\
 Eff_STORAGE IN root_effects e /\
 (!fuel bb inst s t. MEM (CseStep fuel bb inst s t) (pre ++ post) ==>
    ~is_alloca_op inst.inst_opcode) ==>
 contract_storage (cse_phase_state ph1) =
 contract_storage (cse_phase_state ph0)
Proof
 strip_tac >> irule cse_prefix_interval_observation >>
 conj_tac
 >- (rpt strip_tac >> drule cse_phi_account_frame >> simp[contract_storage_def]) >>
 simp[cse_index_storage_observation] >>
 qexistsl [`ctx`, `e`, `fn`, `fuel0`, `post`, `pre`, `s0`] >>
 simp[] >> metis_tac[cse_surviving_step_storage, MEM_APPEND]
QED

Theorem cse_surviving_step_balance:
 step_inst fuel ctx inst s = OK t /\ ~is_alloca_op inst.inst_opcode /\
 avail_source_survives e inst /\ Eff_BALANCE IN root_effects e ==>
 !addr. (lookup_account addr t.vs_accounts).balance =
        (lookup_account addr s.vs_accounts).balance
Proof
 strip_tac >> Cases_on `is_terminator inst.inst_opcode`
 >- (drule_all cse_step_terminator_account_frame >> simp[]) >>
 irule (cj 1 cse_step_balance_account_frame) >>
 qexistsl [`ctx`, `fuel`, `inst`] >> simp[] >>
 gvs[avail_source_survives_def] >>
 Cases_on `inst.inst_opcode` >>
 gvs[is_pseudo_def, is_terminator_def, write_effects_def,
     empty_effects_def, all_effects_def, pred_setTheory.DISJOINT_DEF,
     pred_setTheory.EXTENSION] >> metis_tac[]
QED

Theorem cse_surviving_step_extcode:
 step_inst fuel ctx inst s = OK t /\ ~is_alloca_op inst.inst_opcode /\
 avail_source_survives e inst /\ Eff_EXTCODE IN root_effects e ==>
 !addr. (lookup_account addr t.vs_accounts).code =
          (lookup_account addr s.vs_accounts).code /\
        (account_empty (lookup_account addr t.vs_accounts) <=>
         account_empty (lookup_account addr s.vs_accounts))
Proof
 strip_tac >> Cases_on `is_terminator inst.inst_opcode`
 >- (drule_all cse_step_terminator_account_frame >> simp[]) >>
 irule cse_step_extcode_frame >>
 qexistsl [`ctx`, `fuel`, `inst`] >> simp[] >>
 gvs[avail_source_survives_def] >>
 Cases_on `inst.inst_opcode` >>
 gvs[is_pseudo_def, is_terminator_def, write_effects_def,
     empty_effects_def, all_effects_def, pred_setTheory.DISJOINT_DEF,
     pred_setTheory.EXTENSION] >> metis_tac[]
QED

Theorem cse_prefix_interval_balance:
 cse_prefix ctx fn fuel0 s0 pre ph0 /\
 cse_prefix ctx fn fuel0 s0 (pre ++ post) ph1 /\
 EVERY (cse_event_survives e) post /\ Eff_BALANCE IN root_effects e /\
 (!fuel bb inst s t. MEM (CseStep fuel bb inst s t) (pre ++ post) ==>
    ~is_alloca_op inst.inst_opcode) ==>
 !addr. (lookup_account addr (cse_phase_state ph1).vs_accounts).balance =
        (lookup_account addr (cse_phase_state ph0).vs_accounts).balance
Proof
 strip_tac >> gen_tac >>
 irule (cse_prefix_interval_observation |> Q.GEN `obs` |>
   Q.ISPEC `\s. (lookup_account addr s.vs_accounts).balance` |> BETA_RULE) >>
 conj_tac
 >- (rpt strip_tac >> drule cse_phi_account_frame >> simp[]) >>
 simp[] >> qexistsl [`ctx`, `e`, `fn`, `fuel0`, `post`, `pre`, `s0`] >>
 simp[] >> metis_tac[cse_surviving_step_balance, MEM_APPEND]
QED

Theorem cse_prefix_interval_extcode:
 cse_prefix ctx fn fuel0 s0 pre ph0 /\
 cse_prefix ctx fn fuel0 s0 (pre ++ post) ph1 /\
 EVERY (cse_event_survives e) post /\ Eff_EXTCODE IN root_effects e /\
 (!fuel bb inst s t. MEM (CseStep fuel bb inst s t) (pre ++ post) ==>
    ~is_alloca_op inst.inst_opcode) ==>
 !addr. (lookup_account addr (cse_phase_state ph1).vs_accounts).code =
        (lookup_account addr (cse_phase_state ph0).vs_accounts).code /\
        (account_empty (lookup_account addr (cse_phase_state ph1).vs_accounts) <=>
         account_empty (lookup_account addr (cse_phase_state ph0).vs_accounts))
Proof
 strip_tac >> gen_tac >>
 `((lookup_account addr (cse_phase_state ph1).vs_accounts).code,
    account_empty (lookup_account addr (cse_phase_state ph1).vs_accounts)) =
  ((lookup_account addr (cse_phase_state ph0).vs_accounts).code,
    account_empty (lookup_account addr (cse_phase_state ph0).vs_accounts))`
 suffices_by simp[] >>
 irule (cse_prefix_interval_observation |> Q.GEN `obs` |>
   Q.ISPEC `\s. ((lookup_account addr s.vs_accounts).code,
                 account_empty (lookup_account addr s.vs_accounts))` |> BETA_RULE) >>
 conj_tac
 >- (rpt strip_tac >> drule cse_phi_account_frame >> simp[]) >>
 simp[] >> qexistsl [`ctx`, `e`, `fn`, `fuel0`, `post`, `pre`, `s0`] >>
 simp[] >> metis_tac[cse_surviving_step_extcode, MEM_APPEND]
QED

Theorem cse_prefix_step_allocation_free:
 wf_function fn /\ fn_inst_wf fn /\
 EVERY (\i. ~is_alloca_op i.inst_opcode) (fn_insts fn) /\
 cse_prefix ctx fn fuel0 s0 events phase /\
 MEM (CseStep n bb inst s t) events ==>
 ~is_alloca_op inst.inst_opcode
Proof
 strip_tac >> drule_all cse_prefix_event_provenance >>
 simp[] >> strip_tac >>
 `MEM bb fn.fn_blocks` by metis_tac[venomExecPropsTheory.lookup_block_MEM] >>
 `MEM inst bb.bb_instructions` by
   (gvs[get_instruction_def, AllCaseEqs()] >> metis_tac[MEM_EL]) >>
 gvs[fn_insts_def, EVERY_MEM] >>
 metis_tac[fmp_fn_insts_blocks_intro]
QED

Definition cse_fixed_observation_def:
 cse_fixed_observation s =
 (s.vs_call_ctx, s.vs_tx_ctx, s.vs_block_ctx, s.vs_data_section,
  s.vs_labels, s.vs_code, s.vs_prev_hashes, s.vs_initial_fmp)
End

Theorem cse_step_fixed_observation:
 step_inst fuel ctx inst s = OK t ==>
 cse_fixed_observation t = cse_fixed_observation s
Proof
 strip_tac >> Cases_on `inst.inst_opcode = INVOKE`
 >- (drule_all invoke_preserves_structural >> simp[cse_fixed_observation_def]) >>
 drule_all step_inst_non_invoke >> strip_tac >>
 Cases_on `is_terminator inst.inst_opcode`
 >- (Cases_on `inst.inst_opcode` >> gvs[is_terminator_def] >>
     cseReplayLib.selected_base_tac >> gvs[AllCaseEqs()] >>
     simp[cse_fixed_observation_def, jump_to_def] >>
     pairarg_tac >> gvs[]) >>
 gvs[] >> drule_all step_inst_base_preserves_all >> simp[cse_fixed_observation_def]
QED

Theorem cse_prefix_interval_fixed_observation:
 cse_prefix ctx fn fuel0 s0 pre ph0 /\
 cse_prefix ctx fn fuel0 s0 (pre ++ post) ph1 ==>
 cse_fixed_observation (cse_phase_state ph1) =
 cse_fixed_observation (cse_phase_state ph0)
Proof
 strip_tac >> irule cse_prefix_surviving_observation >>
 conj_tac >- simp[cse_fixed_observation_def] >>
 qexistsl [`ctx`, `fn`, `fuel0`, `post`, `pre`, `s0`, `\ev. T`] >>
 simp[] >> conj_tac >- metis_tac[cse_step_fixed_observation] >>
 rpt strip_tac >> irule cse_eval_phis_observation >>
 simp[cse_fixed_observation_def, update_var_def] >> metis_tac[]
QED

Definition cse_effect_observation_def:
 cse_effect_observation effects s =
 (if Eff_MEMORY IN effects then SOME s.vs_memory else NONE,
  if Eff_TRANSIENT IN effects then SOME s.vs_transient else NONE,
  if Eff_IMMUTABLES IN effects then SOME s.vs_immutables else NONE,
  if Eff_RETURNDATA IN effects then SOME s.vs_returndata else NONE,
  if Eff_FMP IN effects then SOME s.vs_fmp else NONE)
End

Theorem cse_step_terminator_effect_observation:
 step_inst fuel ctx inst s = OK t /\ is_terminator inst.inst_opcode ==>
 cse_effect_observation effects t = cse_effect_observation effects s
Proof
 strip_tac >>
 `inst.inst_opcode <> INVOKE` by
   (Cases_on `inst.inst_opcode` >> gvs[is_terminator_def]) >>
 drule_all step_inst_non_invoke >> strip_tac >>
 Cases_on `inst.inst_opcode` >> gvs[is_terminator_def] >>
 cseReplayLib.selected_base_tac >> gvs[AllCaseEqs()] >>
 simp[cse_effect_observation_def, jump_to_def] >> pairarg_tac >> gvs[]
QED

Theorem cse_surviving_step_effect_observation:
 step_inst fuel ctx inst s = OK t /\ ~is_alloca_op inst.inst_opcode /\
 avail_source_survives e inst ==>
 cse_effect_observation (root_effects e) t =
 cse_effect_observation (root_effects e) s
Proof
 strip_tac >> Cases_on `is_terminator inst.inst_opcode`
 >- metis_tac[cse_step_terminator_effect_observation] >>
 `!eff. eff IN root_effects e ==> eff NOTIN write_effects inst.inst_opcode` by
   (gvs[avail_source_survives_def] >>
    Cases_on `inst.inst_opcode` >>
    gvs[is_pseudo_def, write_effects_def, empty_effects_def,
        pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION] >> metis_tac[]) >>
 simp[cse_effect_observation_def] >> rpt conj_tac
 >- metis_tac[write_effects_sound_memory]
 >- metis_tac[write_effects_sound_transient]
 >- metis_tac[write_effects_sound_immutables]
 >- metis_tac[write_effects_sound_returndata] >>
 Cases_on `Eff_FMP IN root_effects e` >> simp[] >>
 `inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> SETFMP /\
  inst.inst_opcode <> DALLOCA` by
   (Cases_on `inst.inst_opcode` >>
    gvs[write_effects_def, all_effects_def, empty_effects_def] >> metis_tac[]) >>
 gvs[step_inst_non_invoke] >>
 drule_all step_inst_base_preserves_all >> simp[]
QED

Theorem cse_prefix_interval_effect_observation:
 cse_prefix ctx fn fuel0 s0 pre ph0 /\
 cse_prefix ctx fn fuel0 s0 (pre ++ post) ph1 /\
 EVERY (cse_event_survives e) post /\
 (!fuel bb inst s t. MEM (CseStep fuel bb inst s t) (pre ++ post) ==>
    ~is_alloca_op inst.inst_opcode) ==>
 cse_effect_observation (root_effects e) (cse_phase_state ph1) =
 cse_effect_observation (root_effects e) (cse_phase_state ph0)
Proof
 strip_tac >> irule cse_prefix_interval_observation >>
 conj_tac
 >- (rpt strip_tac >> irule cse_eval_phis_observation >>
     simp[cse_effect_observation_def, update_var_def] >> metis_tac[]) >>
 conj_tac >- simp[cse_effect_observation_def] >>
 qexistsl [`ctx`, `e`, `fn`, `fuel0`, `post`, `pre`, `s0`] >>
 simp[] >> metis_tac[cse_surviving_step_effect_observation, MEM_APPEND]
QED

Theorem cse_prefix_interval_observations:
 wf_function fn /\ fn_inst_wf fn /\
 EVERY (\i. ~is_alloca_op i.inst_opcode) (fn_insts fn) /\
 cse_prefix ctx fn fuel0 s0 pre ph0 /\
 cse_prefix ctx fn fuel0 s0 (pre ++ post) ph1 /\
 EVERY (cse_event_survives e) post /\
 cse_phase_state ph0 = u /\ cse_phase_state ph1 = s ==>
 s.vs_call_ctx = u.vs_call_ctx /\ s.vs_tx_ctx = u.vs_tx_ctx /\
 s.vs_block_ctx = u.vs_block_ctx /\ s.vs_data_section = u.vs_data_section /\
 s.vs_labels = u.vs_labels /\ s.vs_code = u.vs_code /\
 s.vs_prev_hashes = u.vs_prev_hashes /\ s.vs_initial_fmp = u.vs_initial_fmp /\
 (Eff_MEMORY IN root_effects e ==> s.vs_memory = u.vs_memory) /\
 (Eff_TRANSIENT IN root_effects e ==> s.vs_transient = u.vs_transient) /\
 (Eff_IMMUTABLES IN root_effects e ==> s.vs_immutables = u.vs_immutables) /\
 (Eff_RETURNDATA IN root_effects e ==> s.vs_returndata = u.vs_returndata) /\
 (Eff_FMP IN root_effects e ==> s.vs_fmp = u.vs_fmp) /\
 (Eff_STORAGE IN root_effects e ==> contract_storage s = contract_storage u) /\
 (Eff_BALANCE IN root_effects e ==>
    !addr. (lookup_account addr s.vs_accounts).balance =
           (lookup_account addr u.vs_accounts).balance) /\
 (Eff_EXTCODE IN root_effects e ==>
    !addr. (lookup_account addr s.vs_accounts).code =
           (lookup_account addr u.vs_accounts).code /\
           (account_empty (lookup_account addr s.vs_accounts) <=>
            account_empty (lookup_account addr u.vs_accounts)))
Proof
 strip_tac >>
 `!fuel bb inst a b. MEM (CseStep fuel bb inst a b) (pre ++ post) ==>
    ~is_alloca_op inst.inst_opcode` by
   metis_tac[cse_prefix_step_allocation_free] >>
 `cse_fixed_observation s = cse_fixed_observation u` by
   metis_tac[cse_prefix_interval_fixed_observation] >>
 `cse_effect_observation (root_effects e) s =
  cse_effect_observation (root_effects e) u` by
   metis_tac[cse_prefix_interval_effect_observation] >>
 gvs[cse_fixed_observation_def] >>
 rpt conj_tac >> rpt strip_tac
 >- gvs[cse_effect_observation_def]
 >- gvs[cse_effect_observation_def]
 >- gvs[cse_effect_observation_def]
 >- gvs[cse_effect_observation_def]
 >- gvs[cse_effect_observation_def]
 >- metis_tac[cse_prefix_interval_storage, MEM_APPEND]
 >- metis_tac[cse_prefix_interval_balance, MEM_APPEND]
 >> qpat_x_assum `!fuel bb inst a b. _` 
      (assume_tac o PURE_REWRITE_RULE [GSYM MEM_APPEND])
 >> drule_all cse_prefix_interval_extcode
 >> disch_then (qspec_then `addr` mp_tac) >> simp[]
QED

Theorem cse_step_read_observations:
 step_inst fuel ctx inst u = OK v /\ ~is_alloca_op inst.inst_opcode /\
 ~has_conflicting_effects inst.inst_opcode /\ ~is_terminator inst.inst_opcode ==>
 cse_fixed_observation v = cse_fixed_observation u /\
 cse_effect_observation (read_effects inst.inst_opcode) v =
 cse_effect_observation (read_effects inst.inst_opcode) u /\
 (Eff_STORAGE IN read_effects inst.inst_opcode ==> contract_storage v = contract_storage u) /\
 (Eff_BALANCE IN read_effects inst.inst_opcode ==>
   !addr. (lookup_account addr v.vs_accounts).balance =
          (lookup_account addr u.vs_accounts).balance) /\
 (Eff_EXTCODE IN read_effects inst.inst_opcode ==>
   !addr. (lookup_account addr v.vs_accounts).code =
          (lookup_account addr u.vs_accounts).code /\
          (account_empty (lookup_account addr v.vs_accounts) <=>
           account_empty (lookup_account addr u.vs_accounts)))
Proof
 strip_tac >>
 `!eff. eff IN read_effects inst.inst_opcode ==>
    eff NOTIN write_effects inst.inst_opcode` by
   (gvs[has_conflicting_effects_def, pred_setTheory.EXTENSION] >> metis_tac[]) >>
 conj_tac >- metis_tac[cse_step_fixed_observation] >>
 conj_tac
 >- (simp[cse_effect_observation_def] >> rpt conj_tac
     >- metis_tac[write_effects_sound_memory]
     >- metis_tac[write_effects_sound_transient]
     >- metis_tac[write_effects_sound_immutables]
     >- metis_tac[write_effects_sound_returndata] >>
     Cases_on `Eff_FMP IN read_effects inst.inst_opcode` >> simp[] >>
     `inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> SETFMP /\
      inst.inst_opcode <> DALLOCA` by
       (Cases_on `inst.inst_opcode` >>
        gvs[write_effects_def, all_effects_def, empty_effects_def] >> metis_tac[]) >>
     gvs[step_inst_non_invoke] >>
     drule_all step_inst_base_preserves_all >> simp[]) >>
 conj_tac >- metis_tac[cse_step_storage_frame] >>
 conj_tac >- metis_tac[cse_step_balance_account_frame] >>
 metis_tac[cse_step_extcode_frame]
QED
