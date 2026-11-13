(* Instruction-site observations ignore caller control bookkeeping. *)
Theory simplifyCfgGasEventBoundary
Ancestors
  gasEventsFuel gasEventsContext simplifyCfgControlExec simplifyCfgMergeExec
  simplifyCfgMergeRuns simplifyCfgMergeSegment simplifyCfgMergeGlobalRuns
  simplifyCfgControl gasEvents venomExecSemantics
  simplifyCfgMergePaths simplifyCfgDefs venomInst venomState list rich_list
  o1PassLift passSimulationDefs

Theorem scfg_ctrl_gas_events_step:
  gas_events_step k C owner i (scfg_ctrl c p n s) =
  gas_events_step k C owner i s
Proof
  simp[gas_events_step_def]
QED

Theorem scfg_payload_gas_events_step:
  scfg_payload s t ==>
  gas_events_step k C owner i t = gas_events_step k C owner i s
Proof
  simp[scfg_payload_def] >> strip_tac >>
  qpat_x_assum `t = _` SUBST1_TAC >> simp[scfg_ctrl_gas_events_step]
QED

Theorem scfg_chain_transfer_gas_events:
  scfg_chain_hyp fn a b ==>
  gas_events_step k C owner (LAST a.bb_instructions) s = []
Proof
  strip_tac >> drule scfg_chain_transfer_shape >>
  strip_tac >> simp[gas_events_step_def]
QED

(* A completed first instruction can be synchronized with a partial tail. *)
Theorem scfg_chain_gas_events_block_distance[local]:
  !d fn a b C s0 s t bb bt k owner.
  LENGTH bt.bb_instructions - t.vs_inst_idx = d /\
  scfg_chain_hyp fn a b /\ fn_entry_state fn s0 /\ ~s.vs_halted /\
  (scfg_chain_segment a b s t \/ scfg_chain_splice a s t) /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  lookup_block t.vs_current_bb (scfg_chain fn a b).fn_blocks = SOME bt /\
  (!i. active_inst fn i s ==> frame_reach C fn s0 i s) ==>
  ?extra. gas_events_block k C owner bt t =
    gas_events_block k C owner bb s ++ extra
Proof
  completeInduct_on `d` >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `scfg_chain_splice a s t`
  >- suspend "splice" >>
  `scfg_chain_segment a b s t` by metis_tac[] >>
  Cases_on `get_instruction bb s.vs_inst_idx`
  >- (`gas_events_block k C owner bb s = []` by
        simp[Once gas_events_block_def] >> simp[]) >>
  rename1 `get_instruction bb s.vs_inst_idx = SOME i` >>
  Cases_on `i.inst_opcode = PHI`
  >- suspend "phi" >>
  `get_instruction bt t.vs_inst_idx = SOME i` by
    (drule_all scfg_chain_segment_instruction >> simp[] >> metis_tac[]) >>
  `scfg_payload s t` by metis_tac[scfg_chain_segment_payload] >>
  `gas_events_step k C owner i t = gas_events_step k C owner i s` by
    metis_tac[scfg_payload_gas_events_step] >>
  `scfg_result (step_inst k C i s) (step_inst k C i t)` by
    metis_tac[scfg_payload_step] >>
  Cases_on `step_inst k C i t` >> Cases_on `step_inst k C i s` >>
  gvs[scfg_result_def]
  >- suspend "ok" >>
  qexists_tac `[]` >> once_rewrite_tac[gas_events_block_def] >> simp[]
QED

Resume scfg_chain_gas_events_block_distance[splice]:
  `bb = a` by (fs[scfg_chain_splice_def, scfg_chain_hyp_def] >> gvs[]) >>
  gvs[] >>
  `get_instruction a s.vs_inst_idx = SOME (LAST a.bb_instructions)` by
    (fs[scfg_chain_splice_def, get_instruction_def] >>
     `a.bb_instructions <> []` by metis_tac[scfg_chain_blocks_nonempty] >>
     Cases_on `a.bb_instructions` >> gvs[LENGTH_FRONT, LAST_EL]) >>
  `is_terminator (LAST a.bb_instructions).inst_opcode` by
    (drule scfg_chain_transfer_shape >> strip_tac >> simp[is_terminator_def]) >>
  `step_inst k C (LAST a.bb_instructions) s = OK (jump_to b.bb_label s)` by
    metis_tac[scfg_chain_transfer_step, scfg_chain_splice_active] >>
  `gas_events_block k C owner a s = []` by
    (simp[Once gas_events_block_def] >>
     metis_tac[scfg_chain_transfer_gas_events]) >> simp[]
QED
Resume scfg_chain_gas_events_block_distance[phi]:
  `gas_events_block k C owner bb s = []` by
    (simp[Once gas_events_block_def, gas_events_step_def] >>
     Cases_on `i` >> gvs[step_inst_def, step_inst_base_def]) >>
  simp[]
QED
Resume scfg_chain_gas_events_block_distance[ok]:
  Cases_on `is_terminator i.inst_opcode`
  >- (qexists_tac `[]` >> once_rewrite_tac[gas_events_block_def] >> simp[]) >>
  drule_all scfg_chain_segment_rooted_advance >> strip_tac >> gvs[] >>
  `v.vs_current_bb = t.vs_current_bb` by
    metis_tac[venomInstPropsTheory.step_preserves_control_flow] >>
  `t.vs_inst_idx < LENGTH bt.bb_instructions` by
    gvs[get_instruction_def, AllCaseEqs()] >>
  `?extra. gas_events_block k C owner bt (v with vs_inst_idx := SUC t.vs_inst_idx) =
     gas_events_block k C owner bb (u with vs_inst_idx := SUC s.vs_inst_idx) ++ extra` by
    (first_x_assum irule >> simp[] >> metis_tac[]) >>
  qexists_tac `extra` >> once_rewrite_tac[gas_events_block_def] >>
  simp[APPEND_ASSOC]
QED
Finalise scfg_chain_gas_events_block_distance

Theorem scfg_chain_gas_events_block:
  scfg_chain_hyp fn a b /\ fn_entry_state fn s0 /\ ~s.vs_halted /\
  (scfg_chain_segment a b s t \/ scfg_chain_splice a s t) /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  lookup_block t.vs_current_bb (scfg_chain fn a b).fn_blocks = SOME bt /\
  (!i. active_inst fn i s ==> frame_reach C fn s0 i s) ==>
  ?extra. gas_events_block k C owner bt t =
    gas_events_block k C owner bb s ++ extra
Proof
  strip_tac >> irule scfg_chain_gas_events_block_distance >>
  simp[] >> metis_tac[]
QED

Theorem scfg_gas_events_step_transport:
  (!nm. OPTREL (\f g. fn_entry_label g = fn_entry_label f)
    (lookup_function nm C.ctx_functions) (lookup_function nm D.ctx_functions)) /\
  scfg_payload s t /\
  (!nm f g cs.
    lookup_function nm C.ctx_functions = SOME f /\
    lookup_function nm D.ctx_functions = SOME g /\ fn_entry_state f cs ==>
    ?m extra. gas_events_blocks m D g cs = gas_events_blocks n C f cs ++ extra /\
      (terminates (run_blocks n C f cs) ==> extra = [] /\
        frame_result_rel (run_blocks n C f cs) (run_blocks m D g cs))) ==>
  ?m extra.
    gas_events_step m D owner i t = gas_events_step n C owner i s ++ extra /\
    (terminates (step_inst n C i s) ==> extra = [] /\
      ((?u v. step_inst n C i s = OK u /\ step_inst m D i t = OK v /\
          scfg_payload u v) \/
        frame_result_rel (step_inst n C i s) (step_inst m D i t))) /\
    (!u. step_inst n C i s = OK u ==>
      ?v. step_inst m D i t = OK v /\ scfg_payload u v)
Proof
  strip_tac >> Cases_on `i.inst_opcode = INVOKE`
  >- suspend "invoke" >>
  qexistsl_tac [`n`, `[]`] >> simp[gas_events_step_def] >>
  `scfg_result (step_inst n C i s) (step_inst n C i t)` by
    metis_tac[scfg_payload_step] >>
  `step_inst n D i t = step_inst n C i t` by simp[step_inst_non_invoke] >>
  qpat_x_assum `!nm f g cs. _` kall_tac >>
  qpat_x_assum `!nm. OPTREL _ _ _` kall_tac >>
  Cases_on `step_inst n C i s` >> Cases_on `step_inst n C i t` >>
  gvs[scfg_result_def, terminates_def] >>
  simp_tac pure_ss [frame_result_rel_def, pairTheory.pair_case_def,
    exec_result_case_def] >> metis_tac[scfg_payload_frame]
QED

Resume scfg_gas_events_step_transport[invoke]:
  Cases_on `decode_invoke i`
  >- (qexistsl_tac [`n`, `[]`] >>
      simp[gas_events_step_def, step_inst_def, terminates_def]) >>
  PairCases_on `x` >>
  Cases_on `lookup_function x0 C.ctx_functions`
  >- (qpat_x_assum `!nm. OPTREL _ _ _` (qspec_then `x0` mp_tac) >>
      Cases_on `lookup_function x0 D.ctx_functions` >> simp[] >>
      qexistsl_tac [`n`, `[]`] >>
      simp[gas_events_step_def, step_inst_def, terminates_def]) >>
  rename1 `lookup_function x0 C.ctx_functions = SOME f` >>
  `?g. lookup_function x0 D.ctx_functions = SOME g /\
       fn_entry_label g = fn_entry_label f` by
    (qpat_x_assum `!nm. OPTREL _ _ _` (qspec_then `x0` mp_tac) >>
     Cases_on `lookup_function x0 D.ctx_functions` >> simp[]) >>
  `eval_operands x1 t = eval_operands x1 s` by metis_tac[scfg_payload_operands] >>
  Cases_on `eval_operands x1 s`
  >- (qexistsl_tac [`n`, `[]`] >>
      simp[gas_events_step_def, step_inst_def, terminates_def]) >>
  rename1 `eval_operands x1 s = SOME args` >>
  `setup_callee g args t = setup_callee f args s` by
    metis_tac[setup_callee_execution_frame, scfg_payload_frame] >>
  Cases_on `setup_callee f args s`
  >- (qexistsl_tac [`n`, `[]`] >>
      simp[gas_events_step_def, step_inst_def, terminates_def]) >>
  rename1 `setup_callee f args s = SOME cs` >>
  `fn_entry_state f cs` by metis_tac[setup_callee_fn_entry_state] >>
  qpat_x_assum `!nm f g cs. _` drule >>
  disch_then drule >> disch_then drule >> strip_tac >>
  qexistsl_tac [`m`, `extra`] >>
  simp[gas_events_step_def, step_inst_def] >>
  suspend "consume"
QED

Resume scfg_gas_events_step_transport[consume]:
  Cases_on `run_blocks n C f cs` >> gvs[terminates_def] >>
  Cases_on `run_blocks m D g cs` >>
  full_simp_tac pure_ss [frame_result_rel_def, pairTheory.pair_case_def,
    exec_result_case_def] >>
  simp[] >>
  drule execution_frame_merge_callee >>
  disch_then (qspec_then `s` assume_tac) >>
  qpat_x_assum `scfg_payload s t` mp_tac >>
  rewrite_tac[scfg_payload_def] >> disch_then SUBST1_TAC >>
  simp[scfg_ctrl_merge_callee, scfg_ctrl_adopt_return, scfg_ctrl_bind_outputs] >>
  Cases_on `bind_outputs i.inst_outputs i'.iret_values
    (adopt_return_fmp i' (merge_callee_state s v))` >> simp[scfg_ctrl_def]
QED
Finalise scfg_gas_events_step_transport

Theorem scfg_chain_gas_exec_nonleft_distance[local]:
  !d fn a b C s0 s t bb bt k owner.
  LENGTH bt.bb_instructions - t.vs_inst_idx = d /\
  scfg_chain_hyp fn a b /\ fn_entry_state fn s0 /\ ~s.vs_halted /\
  scfg_chain_segment a b s t /\ bb.bb_label <> a.bb_label /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  lookup_block t.vs_current_bb (scfg_chain fn a b).fn_blocks = SOME bt /\
  (!i. active_inst fn i s ==> frame_reach C fn s0 i s) ==>
  gas_events_block k C owner bt t = gas_events_block k C owner bb s /\
  scfg_result (exec_block k C bb s) (exec_block k C bt t) /\
  (!u v. exec_block k C bb s = OK u /\ exec_block k C bt t = OK v ==>
    scfg_chain_exit a b u v)
Proof
  completeInduct_on `d` >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `get_instruction bb s.vs_inst_idx`
  >- suspend "missing" >>
  rename1 `get_instruction bb s.vs_inst_idx = SOME i` >>
  Cases_on `i.inst_opcode = PHI`
  >- suspend "phi" >>
  `get_instruction bt t.vs_inst_idx = SOME i` by
    (drule_all scfg_chain_segment_instruction >> simp[] >> metis_tac[]) >>
  `scfg_payload s t` by metis_tac[scfg_chain_segment_payload] >>
  `gas_events_step k C owner i t = gas_events_step k C owner i s` by
    metis_tac[scfg_payload_gas_events_step] >>
  `scfg_result (step_inst k C i s) (step_inst k C i t)` by
    metis_tac[scfg_payload_step] >>
  Cases_on `step_inst k C i t` >> Cases_on `step_inst k C i s` >>
  gvs[scfg_result_def]
  >- suspend "ok" >>
  once_rewrite_tac[gas_events_block_def, exec_block_def] >>
  simp[scfg_result_def]
QED

Resume scfg_chain_gas_exec_nonleft_distance[missing]:
  `bb.bb_label = s.vs_current_bb` by metis_tac[lookup_block_member_label] >>
  `a.bb_label <> b.bb_label` by metis_tac[scfg_chain_distinct_labels] >>
  drule scfg_chain_lookup_eq >>
  disch_then (qspec_then `t.vs_current_bb` mp_tac) >>
  fs[scfg_chain_segment_def]
  >- (strip_tac >>
      `bb = b` by (fs[scfg_chain_hyp_def] >> gvs[]) >> gvs[] >>
      `lookup_block a.bb_label fn.fn_blocks = SOME a` by fs[scfg_chain_hyp_def] >>
      gvs[] >>
      `get_instruction (scfg_chain_block a b a)
          (LENGTH (FRONT a.bb_instructions) + s.vs_inst_idx) = NONE` by
        fs[get_instruction_def, scfg_chain_block_def] >>
      ntac 2 (once_rewrite_tac[gas_events_block_def, exec_block_def] >> simp[scfg_result_def])) >>
  strip_tac >> gvs[] >>
  `get_instruction (scfg_chain_block a b bb) s.vs_inst_idx = NONE` by
    fs[get_instruction_def, scfg_chain_block_def] >>
  ntac 2 (once_rewrite_tac[gas_events_block_def, exec_block_def] >> simp[scfg_result_def])
QED
Resume scfg_chain_gas_exec_nonleft_distance[phi]:
  `bb.bb_label = s.vs_current_bb` by metis_tac[lookup_block_member_label] >>
  `s.vs_current_bb <> b.bb_label` by
    (strip_tac >> `bb = b` by (fs[scfg_chain_hyp_def] >> gvs[]) >> gvs[] >>
     drule scfg_chain_no_phis >>
     simp[cfgTransformTheory.no_phis_def, EVERY_EL] >>
     gvs[get_instruction_def, AllCaseEqs()] >> metis_tac[]) >>
  `t.vs_current_bb = s.vs_current_bb /\ t.vs_inst_idx = s.vs_inst_idx` by
    fs[scfg_chain_segment_def] >>
  `bt = scfg_chain_block a b bb` by
    (drule scfg_chain_lookup_eq >> disch_then (qspec_then `t.vs_current_bb` mp_tac) >>
     simp[] >> metis_tac[optionTheory.SOME_11]) >> gvs[] >>
  `get_instruction (scfg_chain_block a b bb) t.vs_inst_idx =
    SOME (scfg_phi_image a b bb.bb_label i)` by
    fs[get_instruction_def, scfg_chain_block_def, EL_MAP, AllCaseEqs()] >>
  `step_inst k C i s = Error "phi outside prefix"` by
    (Cases_on `i` >> gvs[step_inst_def, step_inst_base_def]) >>
  `step_inst k C (scfg_phi_image a b bb.bb_label i) t = Error "phi outside prefix"` by
    (Cases_on `i` >> gvs[scfg_phi_image_def, cfgTransformTheory.subst_label_inst_def,
      step_inst_def, step_inst_base_def]) >>
  ntac 2 (once_rewrite_tac[gas_events_block_def, exec_block_def] >>
    simp[gas_events_step_def, scfg_result_def]) >> gvs[]
QED
Resume scfg_chain_gas_exec_nonleft_distance[ok]:
  rename1 `step_inst k C i s = OK u` >>
  Cases_on `is_terminator i.inst_opcode`
  >- (`active_inst fn i s` by
        (irule simplifyCfgFragmentsTheory.scfg_lookup_active >> qexistsl_tac [`s`, `bb`] >>
         metis_tac[lookup_block_member_label]) >>
      `frame_reach C fn s0 i s` by metis_tac[] >>
      `u.vs_halted = v.vs_halted` by
        (qpat_x_assum `scfg_payload u v` mp_tac >>
         simp[scfg_payload_def] >> strip_tac >>
         qpat_x_assum `v = _` SUBST1_TAC >> simp[scfg_ctrl_def]) >>
      Cases_on `u.vs_halted` >> fs[]
      >- (ntac 2 (once_rewrite_tac[gas_events_block_def, exec_block_def] >>
           simp[scfg_result_def])) >>
      drule_all scfg_chain_segment_terminator_exit >> strip_tac >> gvs[] >>
      ntac 2 (once_rewrite_tac[gas_events_block_def, exec_block_def] >>
        simp[scfg_result_def])) >>
  reverse (drule_all scfg_chain_segment_rooted_advance >> strip_tac >> gvs[])
  >- (fs[scfg_chain_splice_def] >>
      `u.vs_current_bb = s.vs_current_bb` by
        metis_tac[venomInstPropsTheory.step_preserves_control_flow] >>
      metis_tac[lookup_block_member_label]) >>
  `v.vs_current_bb = t.vs_current_bb` by
    metis_tac[venomInstPropsTheory.step_preserves_control_flow] >>
  `t.vs_inst_idx < LENGTH bt.bb_instructions` by
    gvs[get_instruction_def, AllCaseEqs()] >>
  `gas_events_block k C owner bt (v with vs_inst_idx := SUC t.vs_inst_idx) =
      gas_events_block k C owner bb (u with vs_inst_idx := SUC s.vs_inst_idx) /\
    scfg_result (exec_block k C bb (u with vs_inst_idx := SUC s.vs_inst_idx))
      (exec_block k C bt (v with vs_inst_idx := SUC t.vs_inst_idx)) /\
    (!x y. exec_block k C bb (u with vs_inst_idx := SUC s.vs_inst_idx) = OK x /\
      exec_block k C bt (v with vs_inst_idx := SUC t.vs_inst_idx) = OK y ==>
      scfg_chain_exit a b x y)` by
    (first_x_assum irule >> simp[] >> metis_tac[]) >>
  ntac 2 (once_rewrite_tac[gas_events_block_def, exec_block_def] >> simp[]) >>
  gvs[]
QED
Finalise scfg_chain_gas_exec_nonleft_distance

Theorem scfg_chain_gas_exec_forward_distance[local]:
  !d fn a b C s0 s t bb bt k n owner ev r.
  LENGTH bt.bb_instructions - t.vs_inst_idx = d /\
  scfg_chain_hyp fn a b /\ fn_entry_state fn s0 /\ ~s.vs_halted /\
  (scfg_chain_segment a b s t \/ scfg_chain_splice a s t) /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  lookup_block t.vs_current_bb (scfg_chain fn a b).fn_blocks = SOME bt /\
  (!i. active_inst fn i s ==> frame_reach C fn s0 i s) /\
  ((exec_block k C bb s = r /\
    (bb.bb_label <> a.bb_label \/ (!u. r <> OK u)) /\
    ev = gas_events_block k C owner bb s) \/
   (?x. bb.bb_label = a.bb_label /\ exec_block k C bb s = OK x /\
     ~x.vs_halted /\ x.vs_current_bb = b.bb_label /\
     r = run_block n C b x /\
     ev = gas_events_block k C owner bb s ++ gas_events_block n C owner b x)) ==>
  ?m extra. gas_events_block m C owner bt t = ev ++ extra /\
    (terminates r ==> extra = [] /\
      scfg_result r (exec_block m C bt t) /\
      (!u v. r = OK u /\ exec_block m C bt t = OK v ==>
        scfg_chain_exit a b u v))
Proof
  completeInduct_on `d` >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `bb.bb_label <> a.bb_label`
  >- suspend "nonleft" >>
  Cases_on `scfg_chain_splice a s t`
  >- suspend "splice" >>
  `scfg_chain_segment a b s t` by metis_tac[] >>
  Cases_on `get_instruction bb s.vs_inst_idx`
  >- suspend "missing" >>
  rename1 `get_instruction bb s.vs_inst_idx = SOME i` >>
  Cases_on `i.inst_opcode = PHI`
  >- suspend "phi" >>
  `get_instruction bt t.vs_inst_idx = SOME i` by
    (drule_all scfg_chain_segment_instruction >> simp[] >> metis_tac[]) >>
  `scfg_payload s t` by metis_tac[scfg_chain_segment_payload] >>
  `gas_events_step k C owner i t = gas_events_step k C owner i s` by
    metis_tac[scfg_payload_gas_events_step] >>
  `scfg_result (step_inst k C i s) (step_inst k C i t)` by
    metis_tac[scfg_payload_step] >>
  Cases_on `step_inst k C i t` >> Cases_on `step_inst k C i s` >>
  qpat_x_assum `scfg_result _ _` mp_tac >> simp[scfg_result_def] >> strip_tac
  >- suspend "ok" >>
  qpat_x_assum `!m. m < _ ==> _` kall_tac >>
  `exec_block k C bb s = step_inst k C i s` by
    (once_rewrite_tac[exec_block_def] >> simp[]) >>
  `exec_block k C bt t = step_inst k C i t` by
    (once_rewrite_tac[exec_block_def] >> simp[]) >>
  `gas_events_block k C owner bt t = gas_events_block k C owner bb s` by
    (ntac 2 (once_rewrite_tac[gas_events_block_def] >> simp[])) >>
  qexistsl_tac [`k`, `[]`] >> gvs[scfg_result_def, terminates_def] >>
  metis_tac[scfg_result_def]
QED

Resume scfg_chain_gas_exec_forward_distance[nonleft]:
  `scfg_chain_segment a b s t` by
    (gvs[scfg_chain_splice_def] >> metis_tac[lookup_block_member_label]) >>
  `gas_events_block k C owner bt t = gas_events_block k C owner bb s /\
    scfg_result (exec_block k C bb s) (exec_block k C bt t) /\
    (!u v. exec_block k C bb s = OK u /\ exec_block k C bt t = OK v ==>
      scfg_chain_exit a b u v)` by
    (irule scfg_chain_gas_exec_nonleft_distance >> simp[] >> metis_tac[]) >>
  qexistsl_tac [`k`, `[]`] >> gvs[]
QED
Resume scfg_chain_gas_exec_forward_distance[splice]:
  qpat_x_assum `!m. m < _ ==> _` kall_tac >>
  `bb = a` by (fs[scfg_chain_splice_def, scfg_chain_hyp_def] >> gvs[]) >> gvs[] >>
  `exec_block k C a s = OK (jump_to b.bb_label s)` by
    (irule scfg_chain_splice_exec >> metis_tac[]) >> gvs[] >>
  `get_instruction a s.vs_inst_idx = SOME (LAST a.bb_instructions)` by
    (fs[scfg_chain_splice_def, get_instruction_def] >>
     `a.bb_instructions <> []` by metis_tac[scfg_chain_blocks_nonempty] >>
     Cases_on `a.bb_instructions` >> gvs[LENGTH_FRONT, LAST_EL]) >>
  `is_terminator (LAST a.bb_instructions).inst_opcode` by
    (drule scfg_chain_transfer_shape >> strip_tac >> simp[is_terminator_def]) >>
  `step_inst k C (LAST a.bb_instructions) s = OK (jump_to b.bb_label s)` by
    metis_tac[scfg_chain_transfer_step, scfg_chain_splice_active] >>
  `gas_events_block k C owner a s = []` by
    (simp[Once gas_events_block_def] >> metis_tac[scfg_chain_transfer_gas_events]) >>
  drule_all scfg_chain_splice_rooted >> strip_tac >>
  `gas_events_block n C owner bt t = gas_events_block n C owner b (jump_to b.bb_label s) /\
    scfg_result (exec_block n C b (jump_to b.bb_label s)) (exec_block n C bt t) /\
    (!u v. exec_block n C b (jump_to b.bb_label s) = OK u /\
      exec_block n C bt t = OK v ==> scfg_chain_exit a b u v)` by
    (irule scfg_chain_gas_exec_nonleft_distance >> simp[] >>
     conj_tac >- metis_tac[scfg_chain_distinct_labels] >>
     qexistsl_tac [`fn`, `s0`] >> simp[] >>
     fs[scfg_chain_hyp_def, jump_to_def] >> metis_tac[scfg_chain_distinct_labels]) >>
  drule scfg_chain_run_right >> disch_then assume_tac >>
  qexistsl_tac [`n`, `[]`] >> gvs[]

QED
Resume scfg_chain_gas_exec_forward_distance[missing]:
  qpat_x_assum `!m. m < _ ==> _` kall_tac >>
  `gas_events_block k C owner bb s = []` by simp[Once gas_events_block_def] >>
  `(!x. exec_block k C bb s <> OK x) /\ ~terminates (exec_block k C bb s)` by
    (once_rewrite_tac[exec_block_def] >> simp[terminates_def]) >>
  gvs[] >> qexistsl_tac [`k`, `gas_events_block k C owner bt t`] >> simp[]
QED
Resume scfg_chain_gas_exec_forward_distance[phi]:
  qpat_x_assum `!m. m < _ ==> _` kall_tac >>
  `step_inst k C i s = Error "phi outside prefix"` by
    (Cases_on `i` >> gvs[step_inst_def, step_inst_base_def]) >>
  `gas_events_block k C owner bb s = []` by
    simp[Once gas_events_block_def, gas_events_step_def] >>
  `(!x. exec_block k C bb s <> OK x) /\ ~terminates (exec_block k C bb s)` by
    (once_rewrite_tac[exec_block_def] >> simp[terminates_def]) >>
  gvs[] >> qexistsl_tac [`k`, `gas_events_block k C owner bt t`] >> simp[]
QED
Resume scfg_chain_gas_exec_forward_distance[ok]:
  rename1 `step_inst k C i s = OK u` >>
  Cases_on `is_terminator i.inst_opcode`
  >- (`active_inst fn i s` by
        (irule simplifyCfgFragmentsTheory.scfg_lookup_active >> qexistsl_tac [`s`, `bb`] >>
         metis_tac[lookup_block_member_label]) >>
      `frame_reach C fn s0 i s` by metis_tac[] >>
      drule_all scfg_chain_segment_terminator_source >> strip_tac >>
      metis_tac[lookup_block_member_label]) >>
  `?e. ev = gas_events_step k C owner i s ++ e /\
    ((exec_block k C bb (u with vs_inst_idx := SUC s.vs_inst_idx) = r /\
      (!z. r <> OK z) /\
      e = gas_events_block k C owner bb (u with vs_inst_idx := SUC s.vs_inst_idx)) \/
     (?x. exec_block k C bb (u with vs_inst_idx := SUC s.vs_inst_idx) = OK x /\
       ~x.vs_halted /\ x.vs_current_bb = b.bb_label /\ r = run_block n C b x /\
       e = gas_events_block k C owner bb (u with vs_inst_idx := SUC s.vs_inst_idx) ++
         gas_events_block n C owner b x))` by
    (`exec_block k C bb s = exec_block k C bb (u with vs_inst_idx := SUC s.vs_inst_idx)` by
       (simp[Once exec_block_def, SimpLHS]) >>
     `gas_events_block k C owner bb s = gas_events_step k C owner i s ++
        gas_events_block k C owner bb (u with vs_inst_idx := SUC s.vs_inst_idx)` by
       simp[Once gas_events_block_def] >>
     qpat_x_assum `_ \/ (?x. _)` mp_tac >>
     strip_tac >> gvs[] >> metis_tac[]) >>
  drule_all scfg_chain_segment_rooted_advance >> strip_tac >>
  `v.vs_current_bb = t.vs_current_bb` by
    metis_tac[venomInstPropsTheory.step_preserves_control_flow] >>
  `t.vs_inst_idx < LENGTH bt.bb_instructions` by
    gvs[get_instruction_def, AllCaseEqs()] >>
  `?m extra. gas_events_block m C owner bt (v with vs_inst_idx := SUC t.vs_inst_idx) = e ++ extra /\
    (terminates r ==> extra = [] /\
      scfg_result r (exec_block m C bt (v with vs_inst_idx := SUC t.vs_inst_idx)) /\
      (!x y. r = OK x /\ exec_block m C bt (v with vs_inst_idx := SUC t.vs_inst_idx) = OK y ==>
        scfg_chain_exit a b x y))` by
    (first_x_assum irule >> simp[] >>
     qexistsl_tac [`bb`, `fn`, `k`, `n`, `u with vs_inst_idx := SUC s.vs_inst_idx`, `s0`] >>
     gvs[] >> metis_tac[]) >>
  drule_all gas_events_istep_continue >>
  disch_then (qspecl_then [`owner`, `m`] strip_assume_tac) >>
  qexistsl_tac [`m'`, `extra ++ extra'`] >>
  (conj_tac >- gvs[APPEND_ASSOC]) >>
  qpat_x_assum `!m. m < _ ==> _` kall_tac >>
  qpat_x_assum `_ \/ (?x. _)` kall_tac >>
  strip_tac >>
  `!err. exec_block m C bt (v with vs_inst_idx := SUC t.vs_inst_idx) <> Error err` by
    (Cases_on `r` >>
     Cases_on `exec_block m C bt (v with vs_inst_idx := SUC t.vs_inst_idx)` >>
     gvs[terminates_def, scfg_result_def]) >>
  gvs[]
QED
Finalise scfg_chain_gas_exec_forward_distance

Theorem scfg_chain_gas_exec_forward:
  !fn a b C s0 s t bb bt k n owner ev r.
  scfg_chain_hyp fn a b /\ fn_entry_state fn s0 /\ ~s.vs_halted /\
  (scfg_chain_segment a b s t \/ scfg_chain_splice a s t) /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  lookup_block t.vs_current_bb (scfg_chain fn a b).fn_blocks = SOME bt /\
  (!i. active_inst fn i s ==> frame_reach C fn s0 i s) /\
  ((exec_block k C bb s = r /\
    (bb.bb_label <> a.bb_label \/ (!u. r <> OK u)) /\
    ev = gas_events_block k C owner bb s) \/
   (?x. bb.bb_label = a.bb_label /\ exec_block k C bb s = OK x /\
     ~x.vs_halted /\ x.vs_current_bb = b.bb_label /\
     r = run_block n C b x /\
     ev = gas_events_block k C owner bb s ++ gas_events_block n C owner b x)) ==>
  ?m extra. gas_events_block m C owner bt t = ev ++ extra /\
    (terminates r ==> extra = [] /\
      scfg_result r (exec_block m C bt t) /\
      (!u v. r = OK u /\ exec_block m C bt t = OK v ==>
        scfg_chain_exit a b u v))
Proof
  rpt strip_tac >> irule scfg_chain_gas_exec_forward_distance >>
  simp[] >> metis_tac[]
QED

(* Context substitution inside an unchanged instruction sequence. *)
Theorem scfg_chain_enter_gas_exec_forward:
  scfg_chain_hyp fn a b /\ fn_entry_state fn s0 /\
  scfg_bprefix C fn s0 s /\ ~s.vs_halted /\ scfg_chain_exit a b s t /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\ enters_block fn s s1 /\
  ((run_block k C bb s = r /\
    (bb.bb_label <> a.bb_label \/ (!u. r <> OK u)) /\
    ev = gas_events_block k C owner bb s1) \/
   (?x. bb.bb_label = a.bb_label /\ run_block k C bb s = OK x /\
     ~x.vs_halted /\ x.vs_current_bb = b.bb_label /\
     r = run_block n C b x /\
     ev = gas_events_block k C owner bb s1 ++ gas_events_block n C owner b x)) ==>
  ?bt t1 m extra.
    lookup_block t.vs_current_bb (scfg_chain fn a b).fn_blocks = SOME bt /\
    enters_block (scfg_chain fn a b) t t1 /\
    gas_events_block m C owner bt t1 = ev ++ extra /\
    (terminates r ==> extra = [] /\ scfg_result r (run_block m C bt t) /\
      (!u v. r = OK u /\ run_block m C bt t = OK v ==> scfg_chain_exit a b u v))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `s.vs_current_bb <> b.bb_label` by fs[scfg_chain_exit_def] >>
  drule_all simplifyCfgMergeSemanticsTheory.scfg_chain_rooted_incoming >> strip_tac >>
  drule_all scfg_chain_enters_segment >> strip_tac >>
  drule simplifyCfgMergeSemanticsTheory.scfg_chain_exit_ctrl >> disch_then SUBST_ALL_TAC >>
  `?bt. lookup_block
      (scfg_ctrl s.vs_current_bb
        (OPTION_MAP (\p. if p = b.bb_label then a.bb_label else p) s.vs_prev_bb) 0 s).vs_current_bb
      (scfg_chain fn a b).fn_blocks = SOME bt` by
    (simp[scfg_ctrl_def, scfg_chain_lookup_eq] >> metis_tac[]) >>
  qpat_assum `enters_block fn s s1` (mp_then Any mp_tac scfg_enter_run_block) >>
  disch_then drule >> disch_then (qspec_then `C` strip_assume_tac) >>
  qpat_assum `enters_block (scfg_chain fn a b) _ t1`
    (mp_then Any mp_tac scfg_enter_run_block) >>
  disch_then drule >> disch_then (qspec_then `C` strip_assume_tac) >>
  `(!i. active_inst fn i s1 ==> frame_reach C fn s0 i s1)` by
    metis_tac[simplifyCfgFragmentsTheory.scfg_bprefix_enter_reach] >>
  `?m extra. gas_events_block m C owner bt t1 = ev ++ extra /\
    (terminates r ==> extra = [] /\ scfg_result r (exec_block m C bt t1) /\
      (!u v. r = OK u /\ exec_block m C bt t1 = OK v ==> scfg_chain_exit a b u v))` by
    (irule scfg_chain_gas_exec_forward >> simp[] >> metis_tac[]) >>
  qexistsl_tac [`bt`, `t1`, `m`, `extra`] >> simp[]
QED

Theorem scfg_chain_enter_gas_events_block:
  scfg_chain_hyp fn a b /\ fn_entry_state fn s0 /\
  scfg_bprefix C fn s0 s /\ ~s.vs_halted /\ scfg_chain_exit a b s t /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\ enters_block fn s s1 ==>
  ?bt t1 extra.
    lookup_block t.vs_current_bb (scfg_chain fn a b).fn_blocks = SOME bt /\
    enters_block (scfg_chain fn a b) t t1 /\
    gas_events_block k C owner bt t1 = gas_events_block k C owner bb s1 ++ extra
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `s.vs_current_bb <> b.bb_label` by fs[scfg_chain_exit_def] >>
  drule_all simplifyCfgMergeSemanticsTheory.scfg_chain_rooted_incoming >> strip_tac >>
  drule_all scfg_chain_enters_segment >> strip_tac >>
  drule simplifyCfgMergeSemanticsTheory.scfg_chain_exit_ctrl >> disch_then SUBST_ALL_TAC >>
  `?bt. lookup_block
      (scfg_ctrl s.vs_current_bb
        (OPTION_MAP (\p. if p = b.bb_label then a.bb_label else p) s.vs_prev_bb) 0 s).vs_current_bb
      (scfg_chain fn a b).fn_blocks = SOME bt` by
    (simp[scfg_ctrl_def, scfg_chain_lookup_eq] >> metis_tac[]) >>
  `(!i. active_inst fn i s1 ==> frame_reach C fn s0 i s1)` by
    metis_tac[simplifyCfgFragmentsTheory.scfg_bprefix_enter_reach] >>
  qpat_assum `enters_block fn s s1` (mp_then Any mp_tac scfg_enter_run_block) >>
  disch_then drule >> disch_then (qspec_then `C` strip_assume_tac) >>
  qpat_assum `enters_block (scfg_chain fn a b) _ t1`
    (mp_then Any mp_tac scfg_enter_run_block) >>
  disch_then drule >> disch_then (qspec_then `C` strip_assume_tac) >>
  `?extra. gas_events_block k C owner bt t1 = gas_events_block k C owner bb s1 ++ extra` by
    (irule scfg_chain_gas_events_block >> simp[] >> metis_tac[]) >>
  qexistsl_tac [`bt`, `t1`, `extra`] >> simp[]
QED

Theorem scfg_chain_gas_runs_forward:
  !n s t. scfg_chain_hyp fn a b /\ fn_entry_state fn s0 /\
    scfg_bprefix C fn s0 s /\ ~s.vs_halted /\ scfg_chain_exit a b s t ==>
    ?m extra.
      gas_events_blocks m C (scfg_chain fn a b) t = gas_events_blocks n C fn s ++ extra /\
      (terminates (run_blocks n C fn s) ==> extra = [] /\
        frame_result_rel (run_blocks n C fn s) (run_blocks m C (scfg_chain fn a b) t))
Proof
  completeInduct_on `n` >> Cases_on `n`
  >- (rpt strip_tac >> qexistsl_tac [`0`, `[]`] >>
      simp[Ntimes gas_events_blocks_def 2, Once run_blocks_def, terminates_def]) >>
  rename1 `SUC k` >> rpt gen_tac >> strip_tac >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks`
  >- (qexistsl_tac [`0`, `[]`] >>
      simp[Ntimes gas_events_blocks_def 2, Once run_blocks_def, terminates_def]) >>
  rename1 `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` >>
  Cases_on `?sp. eval_phis s bb.bb_instructions = OK sp`
  >- (pop_assum strip_assume_tac >> suspend "entry") >>
  `?e. eval_phis s bb.bb_instructions = Error e` by
    metis_tac[eval_phis_ok_or_error_defs] >>
  qexistsl_tac [`0`, `[]`] >>
  simp[Ntimes gas_events_blocks_def 2, Once run_blocks_def, run_block_def, terminates_def]
QED

Resume scfg_chain_gas_runs_forward[entry]:
  qabbrev_tac `s1 = sp with vs_inst_idx := phi_prefix_length bb.bb_instructions` >>
  `enters_block fn s s1` by
    (simp[contextCodegenRelTheory.enters_block_def, Abbr `s1`] >> metis_tac[]) >>
  Cases_on `?u. run_block k C bb s = OK u`
  >- (pop_assum strip_assume_tac >> suspend "ok") >>
  `?bt t1 m extra.
    lookup_block t.vs_current_bb (scfg_chain fn a b).fn_blocks = SOME bt /\
    enters_block (scfg_chain fn a b) t t1 /\
    gas_events_block m C fn.fn_name bt t1 = gas_events_block k C fn.fn_name bb s1 ++ extra /\
    (terminates (run_block k C bb s) ==> extra = [] /\
      scfg_result (run_block k C bb s) (run_block m C bt t) /\
      (!u v. run_block k C bb s = OK u /\ run_block m C bt t = OK v ==>
        scfg_chain_exit a b u v))` by
    (irule scfg_chain_enter_gas_exec_forward >> simp[] >> metis_tac[]) >>
  suspend "nonok"
QED

Resume scfg_chain_gas_runs_forward[ok]:
  `~u.vs_halted` by metis_tac[venomExecPropsTheory.run_block_OK_not_halted] >>
  `scfg_bprefix C fn s0 u` by
    metis_tac[simplifyCfgFragmentsTheory.scfg_bprefix_single,
      simplifyCfgFragmentsTheory.scfg_bprefix_trans] >>
  Cases_on `bb.bb_label = a.bb_label` >- suspend "pair" >>
  `?bt t1 m.
    lookup_block t.vs_current_bb (scfg_chain fn a b).fn_blocks = SOME bt /\
    enters_block (scfg_chain fn a b) t t1 /\
    gas_events_block m C fn.fn_name bt t1 = gas_events_block k C fn.fn_name bb s1 /\
    scfg_result (OK u) (run_block m C bt t) /\
    (!v. run_block m C bt t = OK v ==> scfg_chain_exit a b u v)` by
    (`?bt t1 m extra.
      lookup_block t.vs_current_bb (scfg_chain fn a b).fn_blocks = SOME bt /\
      enters_block (scfg_chain fn a b) t t1 /\
      gas_events_block m C fn.fn_name bt t1 = gas_events_block k C fn.fn_name bb s1 ++ extra /\
      (terminates (OK u) ==> extra = [] /\ scfg_result (OK u) (run_block m C bt t) /\
        (!u' v. OK u = OK u' /\ run_block m C bt t = OK v ==> scfg_chain_exit a b u' v))` by
      (irule scfg_chain_enter_gas_exec_forward >> simp[] >> metis_tac[]) >>
     gvs[terminates_def] >> metis_tac[]) >>
  `?w. run_block m C bt t = OK w /\ scfg_chain_exit a b u w` by
    (Cases_on `run_block m C bt t` >> gvs[scfg_result_def]) >>
  `?j tail. gas_events_blocks j C (scfg_chain fn a b) w = gas_events_blocks k C fn u ++ tail /\
    (terminates (run_blocks k C fn u) ==> tail = [] /\
      frame_result_rel (run_blocks k C fn u) (run_blocks j C (scfg_chain fn a b) w))` by
    (qpat_x_assum `!m. m < SUC k ==> _` irule >> simp[] >> metis_tac[]) >>
  suspend "single_sync"
QED

Resume scfg_chain_gas_runs_forward[pair]:
  `bb = a` by metis_tac[scfg_chain_old_wf, scfg_chain_hyp_def,
    venomWfTheory.wf_function_def, venomExecProofsTheory.same_label_same_block,
    lookup_block_member_label] >> gvs[] >>
  drule_all simplifyCfgMergeGlobalRunsTheory.scfg_chain_run_a_next >> strip_tac >>
  `lookup_block u.vs_current_bb fn.fn_blocks = SOME b` by fs[scfg_chain_hyp_def] >>
  Cases_on `k` >- suspend "pair_zero" >>
  rename1 `run_block (SUC h) C a s = OK u` >>
  suspend "pair_positive"
QED

Resume scfg_chain_gas_runs_forward[single_sync]:
  qpat_x_assum `!m. m < SUC k ==> _` kall_tac >>
  `?tp. eval_phis t bt.bb_instructions = OK tp /\
    t1 = tp with vs_inst_idx := phi_prefix_length bt.bb_instructions` by
    (fs[contextCodegenRelTheory.enters_block_def] >> gvs[]) >>
  `exec_block m C bt t1 = OK w` by metis_tac[scfg_enter_run_block] >>
  `exec_block k C bb s1 = OK u` by metis_tac[scfg_enter_run_block] >>
  `~w.vs_halted` by metis_tac[venomExecPropsTheory.run_block_OK_not_halted] >>
  `m <= MAX m j` by simp[] >>
  drule (cj 2 gas_events_fuel_extension) >>
  disch_then (qspecl_then [`C`, `fn.fn_name`, `bt`, `t1`] mp_tac) >>
  simp[] >> strip_tac >>
  `j <= MAX m j` by simp[] >>
  drule (cj 3 gas_events_fuel_extension) >>
  disch_then (qspecl_then [`C`, `scfg_chain fn a b`, `w`] strip_assume_tac) >>
  rename1 `gas_events_blocks (MAX m j) C (scfg_chain fn a b) w =
    gas_events_blocks j C (scfg_chain fn a b) w ++ more` >>
  `(scfg_chain fn a b).fn_name = fn.fn_name` by simp[scfg_chain_def] >>
  gvs[Abbr `s1`] >>
  qexistsl_tac [`SUC (MAX m j)`, `tail ++ more`] >>
  pure_once_rewrite_tac[gas_events_blocks_def, run_blocks_def] >>
  simp[APPEND_ASSOC] >>
  strip_tac >>
  `frame_result_rel (run_blocks k C fn u) (run_blocks j C (scfg_chain fn a b) w)` by metis_tac[] >>
  drule frame_result_rel_terminates >> strip_tac >>
  `!err. run_blocks j C (scfg_chain fn a b) w <> Error err` by
    (Cases_on `run_blocks j C (scfg_chain fn a b) w` >> gvs[terminates_def]) >>
  gvs[]
QED
Resume scfg_chain_gas_runs_forward[nonok]:
  qpat_x_assum `!m. m < SUC k ==> _` kall_tac >>
  `run_blocks (SUC k) C fn s = run_block k C bb s` by
    (Cases_on `run_block k C bb s` >> gvs[run_blocks_unfold]) >>
  `?tp. eval_phis t bt.bb_instructions = OK tp /\
    t1 = tp with vs_inst_idx := phi_prefix_length bt.bb_instructions` by
    (fs[contextCodegenRelTheory.enters_block_def] >> gvs[]) >>
  `run_block m C bt t = exec_block m C bt t1` by simp[run_block_def] >>
  `run_block k C bb s = exec_block k C bb s1` by simp[run_block_def, Abbr `s1`] >>
  `(terminates (run_block k C bb s) ==>
      frame_result_rel (run_block k C bb s) (run_block m C bt t))` by
    metis_tac[scfg_result_terminal] >>
  `(scfg_chain fn a b).fn_name = fn.fn_name` by simp[scfg_chain_def] >>
  gvs[Abbr `s1`] >>
  qexists_tac `SUC m` >>
  pure_once_rewrite_tac[gas_events_blocks_def] >> simp[] >>
  Cases_on `exec_block k C bb (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)` >>
  gvs[terminates_def, scfg_result_def] >>
  Cases_on `exec_block m C bt (tp with vs_inst_idx := phi_prefix_length bt.bb_instructions)` >>
  gvs[scfg_result_def, run_blocks_unfold] >> metis_tac[]
QED

Resume scfg_chain_gas_runs_forward[pair_zero]:
  `?bt t1 extra.
    lookup_block t.vs_current_bb (scfg_chain fn a b).fn_blocks = SOME bt /\
    enters_block (scfg_chain fn a b) t t1 /\
    gas_events_block 0 C fn.fn_name bt t1 = gas_events_block 0 C fn.fn_name a s1 ++ extra` by
    (irule scfg_chain_enter_gas_events_block >> simp[] >> metis_tac[]) >>
  suspend "pair_zero_finish"
QED

Resume scfg_chain_gas_runs_forward[pair_zero_finish]:
  qpat_x_assum `!m. m < SUC 0 ==> _` kall_tac >>
  `?tp. eval_phis t bt.bb_instructions = OK tp /\
    t1 = tp with vs_inst_idx := phi_prefix_length bt.bb_instructions` by
    (fs[contextCodegenRelTheory.enters_block_def] >> gvs[]) >>
  `exec_block 0 C a s1 = OK u` by metis_tac[scfg_enter_run_block] >>
  `(scfg_chain fn a b).fn_name = fn.fn_name` by simp[scfg_chain_def] >>
  qexists_tac `SUC 0` >>
  pure_once_rewrite_tac[gas_events_blocks_def, run_blocks_def] >>
  simp[Abbr `s1`, Once gas_events_blocks_def, Once run_blocks_def, terminates_def] >>
  Cases_on `exec_block 0 C bt (tp with vs_inst_idx := phi_prefix_length bt.bb_instructions)` >>
  gvs[] >> simp[gas_events_blocks_def]
QED

Resume scfg_chain_gas_runs_forward[pair_positive]:
  `EVERY (\i. i.inst_opcode <> PHI) b.bb_instructions` by
    metis_tac[simplifyCfgMergePathsTheory.scfg_chain_no_phis, cfgTransformTheory.no_phis_def] >>
  `eval_phis u b.bb_instructions = OK u /\ phi_prefix_length b.bb_instructions = 0` by
    metis_tac[venomExecProofsTheory.eval_phis_no_phis,
      venomExecProofsTheory.no_phis_phi_prefix_length_zero] >>
  `u.vs_inst_idx = 0` by metis_tac[venomExecPropsTheory.run_block_OK_inst_idx_0] >>
  `u with vs_inst_idx := 0 = u` by simp[venomStateTheory.venom_state_component_equality] >>
  `?bt t1 m extra.
    lookup_block t.vs_current_bb (scfg_chain fn a b).fn_blocks = SOME bt /\
    enters_block (scfg_chain fn a b) t t1 /\
    gas_events_block m C fn.fn_name bt t1 =
      (gas_events_block (SUC h) C fn.fn_name a s1 ++ gas_events_block h C fn.fn_name b u) ++ extra /\
    (terminates (run_block h C b u) ==> extra = [] /\
      scfg_result (run_block h C b u) (run_block m C bt t) /\
      (!v w. run_block h C b u = OK v /\ run_block m C bt t = OK w ==>
        scfg_chain_exit a b v w))` by
    (irule scfg_chain_enter_gas_exec_forward >> simp[] >> metis_tac[]) >>
  Cases_on `?v. run_block h C b u = OK v`
  >- (pop_assum strip_assume_tac >> suspend "pair_continue") >>
  suspend "pair_terminal"
QED

Resume scfg_chain_gas_runs_forward[pair_terminal]:
  qpat_x_assum `!m. m < SUC (SUC h) ==> _` kall_tac >>
  `exec_block (SUC h) C a s1 = OK u` by metis_tac[scfg_enter_run_block] >>
  `run_block h C b u = exec_block h C b u` by simp[run_block_def] >>
  `run_blocks (SUC (SUC h)) C fn s = run_block h C b u` by
    (simp[run_blocks_unfold] >> Cases_on `exec_block h C b u` >> gvs[]) >>
  `?tp. eval_phis t bt.bb_instructions = OK tp /\
    t1 = tp with vs_inst_idx := phi_prefix_length bt.bb_instructions` by
    (fs[contextCodegenRelTheory.enters_block_def] >> gvs[]) >>
  `run_block m C bt t = exec_block m C bt t1` by simp[run_block_def] >>
  `(terminates (run_block h C b u) ==>
      frame_result_rel (run_block h C b u) (run_block m C bt t))` by
    metis_tac[scfg_result_terminal] >>
  `(scfg_chain fn a b).fn_name = fn.fn_name` by simp[scfg_chain_def] >>
  qexists_tac `SUC m` >>
  pure_once_rewrite_tac[gas_events_blocks_def] >> simp[Abbr `s1`] >>
  pure_once_rewrite_tac[gas_events_blocks_def] >> simp[] >>
  Cases_on `exec_block h C b u` >> gvs[terminates_def, scfg_result_def] >>
  Cases_on `exec_block m C bt (tp with vs_inst_idx := phi_prefix_length bt.bb_instructions)` >>
  gvs[scfg_result_def, run_blocks_unfold, APPEND_ASSOC] >> metis_tac[]
QED

Resume scfg_chain_gas_runs_forward[pair_continue]:
  `extra = []` by fs[terminates_def] >> gvs[] >>
  `?w. run_block m C bt t = OK w /\ scfg_chain_exit a b v w` by
    (Cases_on `run_block m C bt t` >> gvs[scfg_result_def, terminates_def]) >>
  `~v.vs_halted` by metis_tac[venomExecPropsTheory.run_block_OK_not_halted] >>
  `scfg_bprefix C fn s0 v` by
    metis_tac[simplifyCfgFragmentsTheory.scfg_bprefix_single,
      simplifyCfgFragmentsTheory.scfg_bprefix_trans] >>
  `?j tail. gas_events_blocks j C (scfg_chain fn a b) w = gas_events_blocks h C fn v ++ tail /\
    (terminates (run_blocks h C fn v) ==> tail = [] /\
      frame_result_rel (run_blocks h C fn v) (run_blocks j C (scfg_chain fn a b) w))` by
    (qpat_x_assum `!m. m < SUC (SUC h) ==> _` irule >> simp[] >> metis_tac[]) >>
  suspend "pair_sync"
QED

Resume scfg_chain_gas_runs_forward[pair_sync]:
  qpat_x_assum `!m. m < SUC (SUC h) ==> _` kall_tac >>
  `?tp. eval_phis t bt.bb_instructions = OK tp /\
    t1 = tp with vs_inst_idx := phi_prefix_length bt.bb_instructions` by
    (fs[contextCodegenRelTheory.enters_block_def] >> gvs[]) >>
  `exec_block m C bt t1 = OK w` by metis_tac[scfg_enter_run_block] >>
  `exec_block (SUC h) C a s1 = OK u` by metis_tac[scfg_enter_run_block] >>
  `exec_block h C b u = OK v` by (fs[run_block_def] >> gvs[]) >>
  `~w.vs_halted` by metis_tac[venomExecPropsTheory.run_block_OK_not_halted] >>
  `m <= MAX m j` by simp[] >>
  drule (cj 2 gas_events_fuel_extension) >>
  disch_then (qspecl_then [`C`, `fn.fn_name`, `bt`, `t1`] mp_tac) >>
  simp[] >> strip_tac >>
  `j <= MAX m j` by simp[] >>
  drule (cj 3 gas_events_fuel_extension) >>
  disch_then (qspecl_then [`C`, `scfg_chain fn a b`, `w`] strip_assume_tac) >>
  rename1 `gas_events_blocks (MAX m j) C (scfg_chain fn a b) w =
    gas_events_blocks j C (scfg_chain fn a b) w ++ more` >>
  `(scfg_chain fn a b).fn_name = fn.fn_name` by simp[scfg_chain_def] >>
  gvs[Abbr `s1`] >>
  qexistsl_tac [`SUC (MAX m j)`, `tail ++ more`] >>
  `run_blocks (SUC (SUC h)) C fn s = run_blocks h C fn v` by
    simp[run_blocks_unfold] >>
  `gas_events_blocks (SUC (SUC h)) C fn s =
    gas_events_block (SUC h) C fn.fn_name a
      (sp with vs_inst_idx := phi_prefix_length a.bb_instructions) ++
    gas_events_block h C fn.fn_name b u ++ gas_events_blocks h C fn v` by
    (simp[Once gas_events_blocks_def] >> simp[Once gas_events_blocks_def]) >>
  `gas_events_blocks (SUC (MAX m j)) C (scfg_chain fn a b) t =
    gas_events_block (MAX m j) C fn.fn_name bt
      (tp with vs_inst_idx := phi_prefix_length bt.bb_instructions) ++
    gas_events_blocks (MAX m j) C (scfg_chain fn a b) w` by
    simp[Once gas_events_blocks_def] >>
  `run_blocks (SUC (MAX m j)) C (scfg_chain fn a b) t =
    run_blocks (MAX m j) C (scfg_chain fn a b) w` by
    simp[Once run_blocks_def] >>
  simp[APPEND_ASSOC] >>
  strip_tac >>
  `frame_result_rel (run_blocks h C fn v) (run_blocks j C (scfg_chain fn a b) w)` by metis_tac[] >>
  drule frame_result_rel_terminates >> strip_tac >>
  `!err. run_blocks j C (scfg_chain fn a b) w <> Error err` by
    (Cases_on `run_blocks j C (scfg_chain fn a b) w` >> gvs[terminates_def]) >>
  gvs[]
QED

Finalise scfg_chain_gas_runs_forward

Theorem scfg_chain_gas_entry_forward:
  scfg_chain_hyp fn a b /\ fn_entry_state fn s ==>
  !n. ?m extra.
    gas_events_blocks m C (scfg_chain fn a b) s = gas_events_blocks n C fn s ++ extra /\
    (terminates (run_blocks n C fn s) ==> extra = [] /\
      frame_result_rel (run_blocks n C fn s) (run_blocks m C (scfg_chain fn a b) s))
Proof
  rpt strip_tac >> irule scfg_chain_gas_runs_forward >>
  metis_tac[simplifyCfgMergeSemanticsTheory.scfg_chain_initial_exit,
    simplifyCfgFragmentsTheory.scfg_bprefix_rules, fn_entry_state_def]
QED
