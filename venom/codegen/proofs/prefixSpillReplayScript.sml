(* Replay a well-formed prefix in an extended, separated spill map. *)
Theory prefixSpillReplay
Ancestors mixedPrefixSim strongPrefixSim prefixSim stackPlanTypes stackModel finite_map list
          pred_set arithmetic
Libs BasicProvers

Definition spill_replay_view_def:
  spill_replay_view initial p q <=>
    p.ps_stack = q.ps_stack /\
    p.ps_alloc.sa_spill_base = q.ps_alloc.sa_spill_base /\
    (!key off. FLOOKUP p.ps_spilled key = SOME off ==>
       FLOOKUP q.ps_spilled key = SOME off) /\
    (!key off. FLOOKUP q.ps_spilled key = SOME off ==>
       FLOOKUP p.ps_spilled key = SOME off \/ FLOOKUP initial key = SOME off) /\
    (!key off key' off'.
       FLOOKUP q.ps_spilled key = SOME off /\
       FLOOKUP q.ps_spilled key' = SOME off' /\ key <> key' ==>
       off + 32 <= off' \/ off' + 32 <= off)
End

Definition spill_fresh_for_def:
  spill_fresh_for initial (SOSpill off) =
    (!key old. FLOOKUP initial key = SOME old ==>
       old + 32 <= off \/ off + 32 <= old) /\
  spill_fresh_for initial (SORestore off) = T /\
  spill_fresh_for initial (SOPush x) = T /\
  spill_fresh_for initial (SOPop n) = T /\
  spill_fresh_for initial (SOSwap n) = T /\
  spill_fresh_for initial (SODup n) = T /\
  spill_fresh_for initial (SOPoke n x) = T /\
  spill_fresh_for initial (SOEmit n) = T /\
  spill_fresh_for initial SOInitialFmp = T /\
  spill_fresh_for initial (SOLabel n) = T /\
  spill_fresh_for initial (SOPushLabel n) = T /\
  spill_fresh_for initial (SOPushOfst n off) = T
End

Theorem replay_spill_lookup_witness[local]:
  !fm off. (?key. FLOOKUP fm key = SOME off) ==>
    FLOOKUP fm (spill_lookup off fm) = SOME off
Proof
  simp[spill_lookup_def] >> metis_tac[SELECT_AX]
QED

Theorem replay_spill_lookup_equal[local]:
  !initial p q off.
    spill_replay_view initial p q /\
    (?key. FLOOKUP p.ps_spilled key = SOME off) ==>
    spill_lookup off p.ps_spilled = spill_lookup off q.ps_spilled
Proof
  rpt strip_tac >>
  `FLOOKUP p.ps_spilled (spill_lookup off p.ps_spilled) = SOME off` by
    (irule replay_spill_lookup_witness >> metis_tac[]) >>
  fs[spill_replay_view_def] >>
  `FLOOKUP q.ps_spilled (spill_lookup off q.ps_spilled) = SOME off` by
    (irule replay_spill_lookup_witness >>
     qexists `key` >> first_x_assum irule >> simp[]) >>
  Cases_on `spill_lookup off p.ps_spilled = spill_lookup off q.ps_spilled` >> simp[] >>
  first_x_assum (qspecl_then [`spill_lookup off p.ps_spilled`, `off`,
    `spill_lookup off q.ps_spilled`, `off`] mp_tac) >> simp[]
QED

Theorem spill_replay_step[local]:
  !initial p q op f lo.
    spill_replay_view initial p q /\ spill_op_wf p op /\
    spill_fresh_for initial op ==>
    spill_op_wf q op /\
    spill_replay_view initial
      (apply_prefix_op f lo op p) (apply_prefix_op f lo op q)
Proof
  rpt gen_tac >> Cases_on `op`
  >- (Cases_on `o'` >> rpt strip_tac >>
      gvs[spill_fresh_for_def, spill_op_wf_def, apply_prefix_op_def,
          apply_simple_op_def, spill_replay_view_def] >> metis_tac[])
  >- (rpt strip_tac >>
      gvs[spill_fresh_for_def, spill_op_wf_def, apply_prefix_op_def,
          apply_simple_op_def, spill_replay_view_def] >> metis_tac[])
  >- (rpt strip_tac >>
      gvs[spill_fresh_for_def, spill_op_wf_def, apply_prefix_op_def,
          apply_simple_op_def, spill_replay_view_def] >> metis_tac[])
  >- (rpt strip_tac >>
      gvs[spill_fresh_for_def, spill_op_wf_def, apply_prefix_op_def,
          apply_simple_op_def, spill_replay_view_def] >> metis_tac[])
  >- (rpt strip_tac >>
      gvs[spill_fresh_for_def, spill_op_wf_def, apply_prefix_op_def,
          apply_simple_op_def, spill_replay_view_def] >> metis_tac[])
  >- suspend "spill"
  >- suspend "restore"
  >> simp[spill_fresh_for_def, spill_op_wf_def, apply_prefix_op_def,
          apply_simple_op_def, spill_replay_view_def] >> metis_tac[]
QED

Resume spill_replay_step[spill]:
  rpt strip_tac >>
  fs[spill_replay_view_def, spill_fresh_for_def, spill_op_wf_def] >>
  `!key old. FLOOKUP q.ps_spilled key = SOME old ==>
     old + 32 <= n \/ n + 32 <= old` by metis_tac[] >>
  simp[spill_op_wf_def, apply_prefix_op_def, spill_replay_view_def,
       FLOOKUP_UPDATE] >>
  rpt conj_tac >> rpt gen_tac >>
  rpt (IF_CASES_TAC >> gvs[]) >> metis_tac[]
QED
Resume spill_replay_step[restore]:
  strip_tac >>
  `?key. FLOOKUP p.ps_spilled key = SOME n` by (fs[spill_op_wf_def] >> metis_tac[]) >>
  `spill_lookup n p.ps_spilled = spill_lookup n q.ps_spilled` by
    (irule replay_spill_lookup_equal >> metis_tac[]) >>
  fs[spill_replay_view_def, spill_fresh_for_def, spill_op_wf_def] >>
  simp[spill_op_wf_def, apply_prefix_op_def, spill_replay_view_def,
       DOMSUB_FLOOKUP_THM] >>
  rpt conj_tac >> rpt gen_tac >>
  rpt (IF_CASES_TAC >> gvs[]) >> metis_tac[]
QED
Finalise spill_replay_step

Theorem prefix_spill_wf_replay_view:
  !ops initial p q f lo.
    spill_replay_view initial p q /\
    EVERY (spill_fresh_for initial) ops /\
    prefix_spill_wf f lo ops p ==>
    prefix_spill_wf f lo ops q /\
    spill_replay_view initial
      (apply_prefix_ops f lo ops p) (apply_prefix_ops f lo ops q)
Proof
  Induct >> simp[prefix_spill_wf_def, apply_prefix_ops_def] >>
  rpt gen_tac >> strip_tac >>
  drule_all spill_replay_step >>
  disch_then (qspecl_then [`f`, `lo`] strip_assume_tac) >>
  metis_tac[]
QED

Theorem prefix_spill_wf_replay_extension:
  !ops p q f lo.
    p.ps_stack = q.ps_stack /\
    p.ps_alloc.sa_spill_base = q.ps_alloc.sa_spill_base /\
    (!key off. FLOOKUP p.ps_spilled key = SOME off ==>
       FLOOKUP q.ps_spilled key = SOME off) /\
    (!key off key' off'.
       FLOOKUP q.ps_spilled key = SOME off /\
       FLOOKUP q.ps_spilled key' = SOME off' /\ key <> key' ==>
       off + 32 <= off' \/ off' + 32 <= off) /\
    EVERY (spill_fresh_for q.ps_spilled) ops /\
    prefix_spill_wf f lo ops p ==>
    prefix_spill_wf f lo ops q
Proof
  rpt strip_tac >>
  `spill_replay_view q.ps_spilled p q` by
    (simp[spill_replay_view_def] >> metis_tac[]) >>
  drule_all prefix_spill_wf_replay_view >> simp[]
QED
