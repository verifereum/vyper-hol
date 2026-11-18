(* A passing checker excludes operand-stack overflow in the checked frame.
   Unchecked external callees may fail; the checked caller's continuation
   includes their eventual result word. The initial frame has the EVM entry
   pc, stack and jump destination, and wf_state supplies decoded-code and
   suspended-parent invariants. *)
Theory stackBoundSoundness
Ancestors
  stackBoundClosure stackBoundReachability stackBoundRuntime stackBoundOverflow
  stackBoundInterface stackBoundFrames
  stackBoundDefs frameGas vfmExecution vfmExecutionProp vfmWfState
  vfmContext vfmConstants list pair

(* The shared join: every instruction reached in the checked frame is
   well-formed, decoded, and cannot overflow at that frame's depth. *)
Theorem sb_checked_frame_safe[local]:
  bytecode_stack_check fuel limit code /\ limit <= stack_limit /\
  wf_state es /\ es.contexts <> [] /\
  (FST (HD es.contexts)).msgParams.code = code /\
  (FST (HD es.contexts)).pc = 0 /\
  (FST (HD es.contexts)).stack = [] /\
  (FST (HD es.contexts)).jumpDest = NONE /\ frame_inst_at es s op ==>
  wf_state s /\ s.contexts <> [] /\
  sb_decoded (FST (HD s.contexts)) op /\
  !t. ~(step_inst op s = (INR (SOME StackOverflow),t) /\
        LENGTH t.contexts = LENGTH s.contexts)
Proof
  strip_tac >>
  drule bytecode_stack_check_closed >> strip_tac >>
  `!q q'. C q /\ MEM q' (sb_successors code q) ==> C q'` by
    (simp[sb_successors_def] >> metis_tac[]) >>
  `wf_state s /\ sb_decoded (FST (HD s.contexts)) op /\
   ?q. C q /\ sb_at code q (LENGTH es.contexts) s` by
    (irule sb_frame_inst_invariant >>
     simp[sb_step_simulates_thm, sb_deeper_preserved_thm] >>
     metis_tac[]) >>
  `s.contexts <> [] /\ LENGTH s.contexts = LENGTH es.contexts` by
    gvs[frame_inst_at_def] >>
  PairCases_on `q` >>
  `code = (FST (HD s.contexts)).msgParams.code /\
   (FST (HD s.contexts)).jumpDest = NONE /\
   q0 = (FST (HD s.contexts)).pc /\
   bytecode_stack_describes q1 (FST (HD s.contexts)).stack` by
    (Cases_on `s.contexts` >> gvs[sb_at_def]) >>
  `EVERY (\q. LENGTH (SND q) <= stack_limit)
    (sb_successors code (q0,q1))` by
    (simp[EVERY_MEM] >> rpt strip_tac >>
     `C q` by metis_tac[] >>
     PairCases_on `q` >>
     qpat_x_assum `!pc a. C (pc,a) ==> _` drule >>
     gvs[stack_limit_def]) >>
  qspec_then `op` mp_tac sb_all_opcode_contracts >>
  simp[sb_opcode_contract_def] >>
  disch_then (qspecl_then [`s`,`q1`] mp_tac) >>
  gvs[stack_limit_def] >> metis_tac[]
QED

Theorem bytecode_stack_check_no_overflow:
  !fuel limit code es.
    bytecode_stack_check fuel limit code /\
    limit <= stack_limit /\ wf_state es /\ es.contexts <> [] /\
    (FST (HD es.contexts)).msgParams.code = code /\
    (FST (HD es.contexts)).pc = 0 /\
    (FST (HD es.contexts)).stack = [] /\
    (FST (HD es.contexts)).jumpDest = NONE ==>
    ~frame_raises es StackOverflow
Proof
  rpt gen_tac >> strip_tac >>
  simp[frame_raises_def] >> rpt strip_tac >>
  drule_all sb_checked_frame_safe >> strip_tac >>
  `LENGTH s.contexts = LENGTH es.contexts` by
    gvs[frame_inst_at_def] >>
  metis_tac[]
QED

Theorem bytecode_stack_check_step_no_overflow:
  !fuel limit code es s op.
    bytecode_stack_check fuel limit code /\
    limit <= stack_limit /\ wf_state es /\ es.contexts <> [] /\
    (FST (HD es.contexts)).msgParams.code = code /\
    (FST (HD es.contexts)).pc = 0 /\
    (FST (HD es.contexts)).stack = [] /\
    (FST (HD es.contexts)).jumpDest = NONE /\
    frame_inst_at es s op ==>
    FST (step s) <> INR (SOME StackOverflow)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all sb_checked_frame_safe >> strip_tac >>
  irule sb_step_no_overflow_from_raw >> simp[] >>
  qexists `op` >> gvs[sb_decoded_def]
QED
