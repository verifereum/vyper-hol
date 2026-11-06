Theory entryReachBodyScratchPath
Ancestors
  entryReachBodyScratchSet entryReachBodyScratchExecution entryReachBodyOperationalPath
  abiEncoderObserver venomExecProofs venomExecSemantics relation

Definition entry_scratch_path_step_def:
  entry_scratch_path_step P ctx fn s t <=>
    entry_decode_step ctx fn s t /\
    (?bb inst. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
      get_instruction bb s.vs_inst_idx = SOME inst /\ P inst)
End

Definition entry_scratch_path_def:
  entry_scratch_path P ctx fn = RTC (entry_scratch_path_step P ctx fn)
End

Theorem scratch_instruction_ready[local]:
  entry_scratch_ready sites b cap s /\ b+cap < dimword (:256) /\
  step_inst_base inst s = OK t /\
  (inst.inst_opcode = ALLOCA ==> inst.inst_operands = [Lit 32w] /\
    (?out. inst.inst_outputs = [out]) /\ inst.inst_id IN sites) /\
  (inst.inst_opcode <> ALLOCA ==> t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next) ==>
  entry_scratch_ready sites b cap t
Proof
  strip_tac >> Cases_on `inst.inst_opcode = ALLOCA`
  >- (gvs[] >> drule_all entry_scratch_alloca_step >> strip_tac >> gvs[]) >>
  metis_tac[entry_scratch_step_frame]
QED

Theorem scratch_path_step_ready[local]:
  entry_scratch_path_step P ctx fn s t /\ entry_scratch_ready sites b cap s /\
  b+cap < dimword (:256) /\
  (!inst. P inst /\ inst.inst_opcode = ALLOCA ==>
    inst.inst_operands = [Lit 32w] /\ (?out. inst.inst_outputs = [out]) /\ inst.inst_id IN sites) /\
  (!inst u v. P inst /\ inst.inst_opcode <> ALLOCA /\ step_inst_base inst u = OK v ==>
    v.vs_allocas = u.vs_allocas /\ v.vs_alloca_next = u.vs_alloca_next) ==>
  entry_scratch_ready sites b cap t
Proof
  rw[entry_scratch_path_step_def, entry_decode_step_def, abi_observer_step_def] >>
  gvs[] >>
  `step_inst_base inst s = OK middle` by metis_tac[step_inst_non_invoke] >>
  `entry_scratch_ready sites b cap middle` by
    (irule scratch_instruction_ready >> goal_assum (drule_at Any) >> metis_tac[]) >>
  imp_res_tac eval_phis_preserves_alloca_fields >>
  qmatch_goalsub_abbrev_tac `entry_scratch_ready sites b cap final` >>
  `final.vs_allocas = middle.vs_allocas /\ final.vs_alloca_next = middle.vs_alloca_next` by
    simp[Abbr `final`] >>
  metis_tac[entry_scratch_ready_frame]
QED

Theorem entry_scratch_path_refl:
  entry_scratch_path P ctx fn s s
Proof
  simp[entry_scratch_path_def]
QED

Theorem entry_scratch_path_trans:
  entry_scratch_path P ctx fn s t /\ entry_scratch_path P ctx fn t u ==>
  entry_scratch_path P ctx fn s u
Proof
  metis_tac[entry_scratch_path_def, RTC_TRANSITIVE, transitive_def]
QED

Theorem entry_scratch_path_step:
  abi_observer_step ctx fn cut s t /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\ P inst ==>
  entry_scratch_path P ctx fn s t
Proof
  strip_tac >> rewrite_tac[entry_scratch_path_def] >> irule RTC_SINGLE >>
  simp[entry_scratch_path_step_def, entry_decode_step_def] >> metis_tac[]
QED

Theorem entry_scratch_path_decode:
  !s t. entry_scratch_path P ctx fn s t ==> entry_decode_path ctx fn s t
Proof
  rewrite_tac[entry_scratch_path_def] >> ho_match_mp_tac RTC_INDUCT >>
  rpt strip_tac >- simp[entry_decode_path_refl] >>
  irule entry_decode_path_trans >> goal_assum (drule_at Any) >>
  fs[entry_scratch_path_step_def, entry_decode_path_def] >>
  metis_tac[RTC_SINGLE]
QED

Theorem entry_scratch_path_ready:
  !s t. entry_scratch_path P ctx fn s t ==>
  entry_scratch_ready sites b cap s /\ b+cap < dimword (:256) /\
  (!inst. P inst /\ inst.inst_opcode = ALLOCA ==>
    inst.inst_operands = [Lit 32w] /\ (?out. inst.inst_outputs = [out]) /\ inst.inst_id IN sites) /\
  (!inst u v. P inst /\ inst.inst_opcode <> ALLOCA /\ step_inst_base inst u = OK v ==>
    v.vs_allocas = u.vs_allocas /\ v.vs_alloca_next = u.vs_alloca_next) ==>
  entry_scratch_ready sites b cap t
Proof
  rewrite_tac[entry_scratch_path_def] >> ho_match_mp_tac RTC_INDUCT >>
  rpt strip_tac >>
  drule_all scratch_path_step_ready >> strip_tac >>
  first_x_assum irule >> metis_tac[]
QED
