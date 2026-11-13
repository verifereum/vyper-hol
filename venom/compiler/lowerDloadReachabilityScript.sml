(* Completed-call boundaries for the LowerDload reachability proof.
 * These lemmas consume a completed callee execution; they do not assert
 * that ghost frame reachability alone supplies that execution.
 *)
Theory lowerDloadReachability
Ancestors
  contextRawReachable venomExecSemantics o1PassLift o1PassContract
  venomWf venomInst list ptrDiscipline contextCodegenRel venomExecProofs venomInstProofs

Theorem completed_callee_invoke_ok:
  callinst.inst_opcode = INVOKE /\
  decode_invoke callinst = SOME (nm, ops) /\
  lookup_function nm ctx.ctx_functions = SOME callee /\
  eval_operands ops s = SOME args /\
  setup_callee callee args s = SOME cs /\
  run_blocks fuel ctx callee cs = IntRet ret s_end /\
  bind_outputs callinst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state s s_end)) = SOME s' ==>
  step_inst fuel ctx callinst s = OK s'
Proof
  strip_tac >> simp[Once step_inst_def]
QED

Theorem raw_reachable_completed_call:
  raw_reachable vs0 ctx caller callinst s /\
  active_inst caller callinst s /\
  ~is_terminator callinst.inst_opcode /\
  callinst.inst_opcode = INVOKE /\
  decode_invoke callinst = SOME (nm, ops) /\
  lookup_function nm ctx.ctx_functions = SOME callee /\
  eval_operands ops s = SOME args /\
  setup_callee callee args s = SOME cs /\
  run_blocks fuel ctx callee cs = IntRet ret s_end /\
  bind_outputs callinst.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state s s_end)) = SOME s' /\
  active_inst caller inst' (s' with vs_inst_idx := SUC s.vs_inst_idx) ==>
  raw_reachable vs0 ctx caller inst'
    (s' with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  strip_tac >> drule_all completed_callee_invoke_ok >> strip_tac >>
  irule raw_reachable_next >> goal_assum drule >> simp[] >>
  metis_tac[]
QED

(* The stage shape supplies the uniqueness required when relating
 * active_inst's member block to lookup_block's selected block. *)
Theorem o1_ctx_shape_distinct_block_labels:
  o1_ctx_shape C ==>
  EVERY (\fn. ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks))
    C.ctx_functions
Proof
  simp[o1_ctx_shape_def, o1_fn_shape_def, wf_function_def,
       fn_labels_def, EVERY_MEM] >> metis_tac[]
QED

(* Saved caller prefixes certify each live frame's origin independently
 * of block-label uniqueness or any completed execution. *)
Inductive ld_stack_origin:
[~base:]
  (!vs C name fn lbl.
    C.ctx_entry = SOME name /\
    lookup_function name C.ctx_functions = SOME fn /\
    fn_entry_label fn = SOME lbl ==>
    ld_stack_origin vs C [] fn
      (vs with <|vs_prev_bb := NONE; vs_current_bb := lbl; vs_inst_idx := 0|>))
[~push:]
  (!vs C stk f caller0 nm ops callee args cs.
    ld_stack_origin vs C stk f.cf_fn caller0 /\
    frame_reach C f.cf_fn caller0 f.cf_inst f.cf_state /\
    f.cf_inst.inst_opcode = INVOKE /\
    decode_invoke f.cf_inst = SOME (nm, ops) /\
    lookup_function nm C.ctx_functions = SOME callee /\
    eval_operands ops f.cf_state = SOME args /\
    setup_callee callee args f.cf_state = SOME cs ==>
    ld_stack_origin vs C (f::stk) callee cs)
End

Theorem ld_stack_origin_cons:
  ld_stack_origin vs C (f::stk) callee cs <=>
  ?caller0 nm ops args.
    ld_stack_origin vs C stk f.cf_fn caller0 /\
    frame_reach C f.cf_fn caller0 f.cf_inst f.cf_state /\
    f.cf_inst.inst_opcode = INVOKE /\
    decode_invoke f.cf_inst = SOME (nm, ops) /\
    lookup_function nm C.ctx_functions = SOME callee /\
    eval_operands ops f.cf_state = SOME args /\
    setup_callee callee args f.cf_state = SOME cs
Proof
  simp[SimpLHS, Once ld_stack_origin_cases]
QED

Theorem ld_stack_origin_member:
  !vs C stk fn s0. ld_stack_origin vs C stk fn s0 ==>
    MEM fn C.ctx_functions
Proof
  ho_match_mp_tac ld_stack_origin_ind >> rpt strip_tac >>
  metis_tac[lookup_function_MEM]
QED

Theorem ld_stack_origin_raw_reachable:
  !vs C stk fn s0. ld_stack_origin vs C stk fn s0 ==>
    !inst s. frame_reach C fn s0 inst s ==>
      raw_reachable vs C fn inst s
Proof
  ho_match_mp_tac ld_stack_origin_ind >> rpt conj_tac >> rpt strip_tac
  >- (irule frame_reach_entry >> metis_tac[])
  >> irule frame_reach_callee >>
  metis_tac[frame_reach_active]
QED

Theorem ld_suffix_mono:
  (?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    (exec_block n C bb s = IntRet ret t \/
     ?u. exec_block n C bb s = OK u /\ ~u.vs_halted /\
         run_blocks n C fn u = IntRet ret t)) /\ n <= m ==>
  ?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    (exec_block m C bb s = IntRet ret t \/
     ?u. exec_block m C bb s = OK u /\ ~u.vs_halted /\
         run_blocks m C fn u = IntRet ret t)
Proof
  rpt strip_tac >> qexists_tac `bb` >> simp[]
  >- (`terminates (exec_block n C bb s)` by simp[terminates_not_error] >>
      drule_all exec_block_terminates_mono >> simp[])
  >> `terminates (exec_block n C bb s)` by simp[terminates_not_error] >>
  `terminates (run_blocks n C fn u)` by simp[terminates_not_error] >>
  drule_all exec_block_terminates_mono >>
  drule_all run_blocks_terminates_mono >> simp[]
QED

Theorem ld_suffix_entry:
  enters_block fn s0 s /\
  (?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    (exec_block n C bb s = IntRet ret t \/
     ?u. exec_block n C bb s = OK u /\ ~u.vs_halted /\
         run_blocks n C fn u = IntRet ret t)) ==>
  run_blocks (SUC n) C fn s0 = IntRet ret t
Proof
  rpt strip_tac >> fs[enters_block_def] >>
  drule eval_phis_preserves_current_bb >> strip_tac >>
  gvs[] >> simp[run_blocks_unfold, run_block_def]
QED

Theorem ld_suffix_return:
  ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks) /\
  active_inst fn i s /\ step_inst k C i s = IntRet ret t ==>
  ?n bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    (exec_block n C bb s = IntRet ret t \/
     ?u. exec_block n C bb s = OK u /\ ~u.vs_halted /\
         run_blocks n C fn u = IntRet ret t)
Proof
  strip_tac >> fs[active_inst_def] >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` by
    (irule MEM_lookup_block >> simp[]) >>
  qexistsl_tac [`k`, `bb`] >> simp[] >> disj1_tac >>
  simp[Once exec_block_def, get_instruction_def]
QED

Theorem ld_suffix_next:
  ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks) /\
  active_inst fn i s /\ ~is_terminator i.inst_opcode /\
  step_inst k C i s = OK u /\
  (?bb. lookup_block u.vs_current_bb fn.fn_blocks = SOME bb /\
    (exec_block n C bb (u with vs_inst_idx := SUC s.vs_inst_idx) = IntRet ret t \/
     ?v. exec_block n C bb (u with vs_inst_idx := SUC s.vs_inst_idx) = OK v /\
         ~v.vs_halted /\ run_blocks n C fn v = IntRet ret t)) ==>
  ?m bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    (exec_block m C bb s = IntRet ret t \/
     ?v. exec_block m C bb s = OK v /\ ~v.vs_halted /\
         run_blocks m C fn v = IntRet ret t)
Proof
  strip_tac >> drule_all step_preserves_control_flow >> strip_tac >>
  fs[active_inst_def] >> gvs[] >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb'` by
    (irule MEM_lookup_block >> simp[]) >>
  gvs[] >>
  `step_inst (MAX k n) C (EL s.vs_inst_idx bb.bb_instructions) s = OK u` by
    (`terminates (step_inst k C (EL s.vs_inst_idx bb.bb_instructions) s)` by
       simp[terminates_not_error] >>
     drule step_inst_terminates_mono >>
     disch_then (qspec_then `MAX k n` mp_tac) >> simp[]) >>
  `exec_block (MAX k n) C bb (u with vs_inst_idx := SUC s.vs_inst_idx) =
   exec_block n C bb (u with vs_inst_idx := SUC s.vs_inst_idx)` by
    (irule exec_block_terminates_mono >> simp[terminates_not_error]) >>
  `exec_block (MAX k n) C bb s =
   exec_block n C bb (u with vs_inst_idx := SUC s.vs_inst_idx)` by
    (simp[Once exec_block_def, get_instruction_def]) >>
  qexists_tac `MAX k n` >> simp[] >>
  `terminates (run_blocks n C fn v)` by simp[terminates_not_error] >>
  drule run_blocks_terminates_mono >>
  disch_then (qspec_then `MAX k n` mp_tac) >> simp[]
QED

Theorem ld_suffix_block:
  ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks) /\
  active_inst fn i s /\ is_terminator i.inst_opcode /\
  step_inst k C i s = OK u /\ ~u.vs_halted /\ enters_block fn u v /\
  (?bb. lookup_block v.vs_current_bb fn.fn_blocks = SOME bb /\
    (exec_block n C bb v = IntRet ret t \/
     ?w. exec_block n C bb v = OK w /\ ~w.vs_halted /\
         run_blocks n C fn w = IntRet ret t)) ==>
  ?m bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    (exec_block m C bb s = IntRet ret t \/
     ?w. exec_block m C bb s = OK w /\ ~w.vs_halted /\
         run_blocks m C fn w = IntRet ret t)
Proof
  strip_tac >>
  `run_blocks (SUC n) C fn u = IntRet ret t` by
    (irule ld_suffix_entry >> qexists_tac `v` >> metis_tac[]) >>
  qpat_x_assum `enters_block _ _ _` kall_tac >>
  fs[active_inst_def] >> gvs[] >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb'` by
    (irule MEM_lookup_block >> simp[]) >>
  `step_inst (MAX k (SUC n)) C (EL s.vs_inst_idx bb'.bb_instructions) s = OK u` by
    (`terminates (step_inst k C (EL s.vs_inst_idx bb'.bb_instructions) s)` by
       simp[terminates_not_error] >>
     drule step_inst_terminates_mono >>
     disch_then (qspec_then `MAX k (SUC n)` mp_tac) >> simp[]) >>
  qexistsl_tac [`MAX k (SUC n)`, `bb'`] >> simp[] >> disj2_tac >>
  qexists_tac `u` >>
  `exec_block (MAX k (SUC n)) C bb' s = OK u` by
    simp[Once exec_block_def, get_instruction_def] >> simp[] >>
  `terminates (run_blocks (SUC n) C fn u)` by simp[terminates_not_error] >>
  drule run_blocks_terminates_mono >>
  disch_then (qspec_then `MAX k (SUC n)` mp_tac) >> simp[]
QED

Theorem ld_frame_suffix_complete:
  !C fn s0 i s. frame_reach C fn s0 i s ==>
  ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks) ==>
  !n ret t.
  (?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    (exec_block n C bb s = IntRet ret t \/
     ?u. exec_block n C bb s = OK u /\ ~u.vs_halted /\
         run_blocks n C fn u = IntRet ret t)) ==>
  ?m. run_blocks m C fn s0 = IntRet ret t
Proof
  ho_match_mp_tac frame_reach_strongind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac >> disch_tac >> rpt gen_tac >> disch_tac
  >- metis_tac[ld_suffix_entry]
  >- (drule frame_reach_active >> strip_tac >>
      qpat_x_assum `?bb. _` mp_tac >> simp[] >> disch_tac >>
      drule_all ld_suffix_next >> strip_tac >>
      first_x_assum irule >> simp[] >> metis_tac[])
  >> drule frame_reach_active >> strip_tac >>
  drule_all ld_suffix_block >> strip_tac >>
  first_x_assum irule >> simp[] >> metis_tac[]
QED

Theorem ld_frame_return_complete:
  frame_reach C fn s0 i s /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks) /\
  step_inst k C i s = IntRet ret t ==>
  ?m. run_blocks m C fn s0 = IntRet ret t
Proof
  strip_tac >> drule frame_reach_active >> strip_tac >>
  drule_all ld_suffix_return >> strip_tac >>
  drule ld_frame_suffix_complete >> simp[] >>
  disch_then irule >> metis_tac[]
QED

Theorem ld_frame_reachable_prefix:
  !vs C stk PG G tn fn inst s.
  frame_reachable vs C stk PG G tn fn inst s ==>
  o1_ctx_shape C ==>
  ?s0. ld_stack_origin vs C stk fn s0 /\ frame_reach C fn s0 inst s
Proof
  ho_match_mp_tac frame_reachable_ind >> rpt conj_tac >> rpt strip_tac
  >- (irule_at Any ld_stack_origin_base >> simp[] >>
      metis_tac[frame_reach_start])
  >- (first_x_assum drule >> strip_tac >>
      qexists_tac `s0` >> simp[] >>
      irule frame_reach_next >> metis_tac[])
  >- (first_x_assum drule >> strip_tac >>
      qexists_tac `s0` >> simp[] >>
      irule frame_reach_block >> metis_tac[])
  >- (first_x_assum drule >> strip_tac >>
      qexists_tac `cs` >> conj_tac
      >- (irule ld_stack_origin_push >> simp[] >> metis_tac[])
      >> metis_tac[frame_reach_start])
  >> first_x_assum drule >> strip_tac >>
  `MEM fn C.ctx_functions` by metis_tac[ld_stack_origin_member] >>
  `ALL_DISTINCT (MAP (\bb. bb.bb_label) fn.fn_blocks)` by
    (drule o1_ctx_shape_distinct_block_labels >> simp[EVERY_MEM]) >>
  drule_all ld_frame_return_complete >> strip_tac >>
  fs[ld_stack_origin_cons] >>
  drule_all completed_callee_invoke_ok >> strip_tac >>
  qexists_tac `caller0` >> simp[] >>
  irule frame_reach_next >> simp[] >> qexistsl_tac [`m`, `f.cf_inst`] >>
  simp[is_terminator_def]
QED

Theorem ld_frame_reachable_raw:
  o1_ctx_shape C /\ frame_reachable vs C stk PG G tn fn inst s ==>
  raw_reachable vs C fn inst s
Proof
  strip_tac >> drule_all ld_frame_reachable_prefix >> strip_tac >>
  drule_all ld_stack_origin_raw_reachable >> simp[]
QED
