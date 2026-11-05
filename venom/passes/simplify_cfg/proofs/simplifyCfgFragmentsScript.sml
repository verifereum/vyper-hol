Theory simplifyCfgFragments
Ancestors
  simplifyCfgSimTools venomExecSemantics venomExecProps o1PassLift passSimulationDefs

Inductive scfg_iprefix:
[~refl:]
  (!C bb s. scfg_iprefix C bb s s)
[~step:]
  (!C bb s i k u t.
    get_instruction bb s.vs_inst_idx = SOME i /\
    ~is_terminator i.inst_opcode /\ step_inst k C i s = OK u /\
    scfg_iprefix C bb (u with vs_inst_idx := SUC s.vs_inst_idx) t ==>
    scfg_iprefix C bb s t)
End

Inductive scfg_bprefix:
[~refl:]
  (!C fn s. scfg_bprefix C fn s s)
[~step:]
  (!C fn s bb k u t.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    run_block k C bb s = OK u /\ ~u.vs_halted /\
    scfg_bprefix C fn u t ==> scfg_bprefix C fn s t)
End

Theorem scfg_iprefix_single:
  get_instruction bb s.vs_inst_idx = SOME i /\
  ~is_terminator i.inst_opcode /\ step_inst k C i s = OK u ==>
  scfg_iprefix C bb s (u with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  metis_tac[scfg_iprefix_rules]
QED

Theorem scfg_bprefix_single:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  run_block k C bb s = OK u /\ ~u.vs_halted ==>
  scfg_bprefix C fn s u
Proof
  metis_tac[scfg_bprefix_rules]
QED

Theorem scfg_iprefix_trans:
  !C bb s t. scfg_iprefix C bb s t ==>
  !v. scfg_iprefix C bb t v ==> scfg_iprefix C bb s v
Proof
  ho_match_mp_tac scfg_iprefix_ind >> rpt strip_tac >>
  metis_tac[scfg_iprefix_rules]
QED

Theorem scfg_bprefix_trans:
  !C fn s t. scfg_bprefix C fn s t ==>
  !v. scfg_bprefix C fn t v ==> scfg_bprefix C fn s v
Proof
  ho_match_mp_tac scfg_bprefix_ind >> rpt strip_tac >>
  metis_tac[scfg_bprefix_rules]
QED

Theorem scfg_bprefix_last:
  !C fn s0 s. scfg_bprefix C fn s0 s ==>
  s = s0 \/
  ?u pb k. scfg_bprefix C fn s0 u /\
    lookup_block u.vs_current_bb fn.fn_blocks = SOME pb /\
    run_block k C pb u = OK s /\ ~s.vs_halted
Proof
  ho_match_mp_tac scfg_bprefix_ind >> rpt strip_tac
  >- simp[]
  >- (disj2_tac >> metis_tac[scfg_bprefix_rules]) >>
  disj2_tac >> metis_tac[scfg_bprefix_rules]
QED

Theorem scfg_istep_continue:
  get_instruction bb s.vs_inst_idx = SOME i /\
  ~is_terminator i.inst_opcode /\ step_inst k C i s = OK u /\
  exec_block n C bb (u with vs_inst_idx := SUC s.vs_inst_idx) = r /\
  (!e. r <> Error e) ==> ?m. exec_block m C bb s = r
Proof
  rpt strip_tac >>
  `step_inst (MAX k n) C i s = OK u` by
    (irule (cj 1 fuel_mono) >> simp[] >> qexists_tac `k` >> simp[]) >>
  `exec_block (MAX k n) C bb
     (u with vs_inst_idx := SUC s.vs_inst_idx) = r` by
    (irule (cj 2 fuel_mono) >> simp[] >> qexists_tac `n` >> simp[]) >>
  qexists_tac `MAX k n` >> simp[Once exec_block_def]
QED

Theorem scfg_iprefix_continue:
  !C bb s t. scfg_iprefix C bb s t ==>
  !n r. exec_block n C bb t = r /\ (!e. r <> Error e) ==>
    ?m. exec_block m C bb s = r
Proof
  ho_match_mp_tac scfg_iprefix_ind >> rpt strip_tac
  >- metis_tac[] >>
  metis_tac[scfg_istep_continue]
QED

Theorem scfg_bstep_continue:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  run_block k C bb s = OK u /\ ~u.vs_halted /\
  run_blocks n C fn u = r /\ (!e. r <> Error e) ==>
  ?m. run_blocks m C fn s = r
Proof
  rpt strip_tac >>
  `run_block (MAX k n) C bb s = OK u` by
    (irule run_block_fuel_mono_OK >> qexists_tac `k` >> simp[]) >>
  `run_blocks (MAX k n) C fn u = r` by
    (irule (cj 3 fuel_mono) >> simp[] >> qexists_tac `n` >> simp[]) >>
  qexists_tac `SUC (MAX k n)` >> simp[run_blocks_unfold]
QED

Theorem scfg_bprefix_continue:
  !C fn s t. scfg_bprefix C fn s t ==>
  !n r. run_blocks n C fn t = r /\ (!e. r <> Error e) ==>
    ?m. run_blocks m C fn s = r
Proof
  ho_match_mp_tac scfg_bprefix_ind >> rpt strip_tac
  >- metis_tac[] >>
  metis_tac[scfg_bstep_continue]
QED

Theorem scfg_two_blocks_continue:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME b1 /\
  run_block k1 C b1 s = OK u /\ ~u.vs_halted /\
  lookup_block u.vs_current_bb fn.fn_blocks = SOME b2 /\
  run_block k2 C b2 u = OK t /\ ~t.vs_halted /\
  run_blocks n C fn t = r /\ (!e. r <> Error e) ==>
  ?m. run_blocks m C fn s = r
Proof
  rpt strip_tac >>
  `scfg_bprefix C fn s u` by metis_tac[scfg_bprefix_single] >>
  `scfg_bprefix C fn u t` by metis_tac[scfg_bprefix_single] >>
  metis_tac[scfg_bprefix_trans, scfg_bprefix_continue]
QED

Inductive scfg_rprefix:
[~refl:]
  (!C fn i s. scfg_rprefix C fn i s i s)
[~next:]
  (!C fn i s k u h j t.
    ~is_terminator i.inst_opcode /\ step_inst k C i s = OK u /\
    active_inst fn h (u with vs_inst_idx := SUC s.vs_inst_idx) /\
    scfg_rprefix C fn h (u with vs_inst_idx := SUC s.vs_inst_idx) j t ==>
    scfg_rprefix C fn i s j t)
[~block:]
  (!C fn i s k u v h j t.
    is_terminator i.inst_opcode /\ step_inst k C i s = OK u /\
    ~u.vs_halted /\ enters_block fn u v /\ active_inst fn h v /\
    scfg_rprefix C fn h v j t ==> scfg_rprefix C fn i s j t)
End

Theorem scfg_rprefix_trans:
  !C fn i s j t. scfg_rprefix C fn i s j t ==>
  !h v. scfg_rprefix C fn j t h v ==> scfg_rprefix C fn i s h v
Proof
  ho_match_mp_tac scfg_rprefix_ind >> rpt strip_tac >>
  metis_tac[scfg_rprefix_rules]
QED

Theorem scfg_rprefix_continue:
  !C fn i s j t. scfg_rprefix C fn i s j t ==>
  !s0. frame_reach C fn s0 i s ==> frame_reach C fn s0 j t
Proof
  ho_match_mp_tac scfg_rprefix_ind >> rpt strip_tac >>
  metis_tac[frame_reach_rules]
QED

Theorem scfg_rprefix_ctx_continue:
  ctx_bisim C C' /\ scfg_rprefix C' fn i s j t /\
  frame_reach C' fn s0 i s ==> frame_reach C fn s0 j t
Proof
  metis_tac[scfg_rprefix_continue, frame_reach_ctx_bisim]
QED

Theorem scfg_istep_cancel[local]:
  get_instruction bb s.vs_inst_idx = SOME i /\
  ~is_terminator i.inst_opcode /\ step_inst k C i s = OK u /\
  exec_block n C bb s = r /\ (!e. r <> Error e) ==>
  ?m. exec_block m C bb (u with vs_inst_idx := SUC s.vs_inst_idx) = r
Proof
  rpt strip_tac >>
  `step_inst (MAX k n) C i s = OK u` by
    (irule (cj 1 fuel_mono) >> simp[] >> qexists_tac `k` >> simp[]) >>
  `exec_block (MAX k n) C bb s = r` by
    (irule (cj 2 fuel_mono) >> simp[] >> qexists_tac `n` >> simp[]) >>
  qexists_tac `MAX k n` >>
  qpat_x_assum `exec_block (MAX _ _) _ _ _ = _` mp_tac >>
  simp[Once exec_block_def]
QED

Theorem scfg_iprefix_cancel:
  !C bb s t. scfg_iprefix C bb s t ==>
  !n r. exec_block n C bb s = r /\ (!e. r <> Error e) ==>
    ?m. exec_block m C bb t = r
Proof
  ho_match_mp_tac scfg_iprefix_ind >> rpt strip_tac
  >- metis_tac[] >>
  drule_all scfg_istep_cancel >> metis_tac[]
QED

Theorem scfg_step_inst_ok_unique:
  step_inst n C i s = OK u /\ step_inst m C i s = OK v ==> u = v
Proof
  strip_tac >>
  `step_inst (MAX n m) C i s = OK u` by
    (irule (cj 1 fuel_mono) >> simp[] >> qexists_tac `n` >> simp[]) >>
  `step_inst (MAX n m) C i s = OK v` by
    (irule (cj 1 fuel_mono) >> simp[] >> qexists_tac `m` >> simp[]) >>
  gvs[]
QED

Theorem scfg_iprefix_index:
  !C bb a b. scfg_iprefix C bb a b ==> a.vs_inst_idx <= b.vs_inst_idx
Proof
  ho_match_mp_tac scfg_iprefix_ind >> simp[] >> rpt strip_tac >> decide_tac
QED

Theorem scfg_iprefix_same_index:
  scfg_iprefix C bb a b /\ a.vs_inst_idx = b.vs_inst_idx ==> a = b
Proof
  strip_tac >> qpat_x_assum `scfg_iprefix _ _ _ _` mp_tac >>
  once_rewrite_tac[scfg_iprefix_cases] >> strip_tac >> gvs[] >>
  drule scfg_iprefix_index >> simp[]
QED

Theorem scfg_iprefix_compare:
  !C bb a b. scfg_iprefix C bb a b ==>
  !t. scfg_iprefix C bb a t ==>
    scfg_iprefix C bb t b \/ scfg_iprefix C bb b t
Proof
  ho_match_mp_tac scfg_iprefix_strongind >> rpt strip_tac
  >- metis_tac[] >>
  pop_assum (strip_assume_tac o ONCE_REWRITE_RULE [scfg_iprefix_cases])
  >- metis_tac[scfg_iprefix_rules] >>
  gvs[] >> metis_tac[scfg_step_inst_ok_unique]
QED

Theorem scfg_iprefix_cut:
  scfg_iprefix C bb a b /\ scfg_iprefix C bb a t /\
  b.vs_inst_idx <= t.vs_inst_idx ==> scfg_iprefix C bb b t
Proof
  rpt strip_tac >>
  qspecl_then [`C`, `bb`, `a`, `b`] mp_tac scfg_iprefix_compare >>
  simp[] >> disch_then (qspec_then `t` mp_tac) >> simp[] >> strip_tac
  >- (`t.vs_inst_idx <= b.vs_inst_idx` by metis_tac[scfg_iprefix_index] >>
      `t = b` by metis_tac[scfg_iprefix_same_index, arithmeticTheory.LESS_EQUAL_ANTISYM] >>
      gvs[scfg_iprefix_rules]) >>
  simp[]
QED

Theorem scfg_iprefix_same_tail:
  !C b a t. scfg_iprefix C b a t ==>
  !b'. (!n. a.vs_inst_idx <= n ==>
    get_instruction b n = get_instruction b' n) ==>
  scfg_iprefix C b' a t
Proof
  ho_match_mp_tac scfg_iprefix_ind >> rpt strip_tac
  >- simp[scfg_iprefix_rules] >>
  `get_instruction b' a.vs_inst_idx = SOME i` by metis_tac[arithmeticTheory.LESS_EQ_REFL] >>
  irule (cj 2 scfg_iprefix_rules) >> simp[] >>
  qexistsl_tac [`k`, `u`] >> simp[] >> first_x_assum irule >>
  simp[] >> rpt strip_tac >> first_x_assum irule >> decide_tac
QED

Theorem scfg_iprefix_same_tail_observe:
  (!n. a.vs_inst_idx <= n ==> get_instruction b n = get_instruction b' n) /\
  scfg_iprefix C b a t /\ get_instruction b t.vs_inst_idx = SOME j ==>
  get_instruction b' t.vs_inst_idx = SOME j
Proof
  metis_tac[scfg_iprefix_index]
QED

Theorem scfg_iprefix_frame_reach:
  !C bb a t. scfg_iprefix C bb a t ==>
  !fn s0 j. MEM bb fn.fn_blocks /\ bb.bb_label = a.vs_current_bb /\
  (!i. get_instruction bb a.vs_inst_idx = SOME i ==> frame_reach C fn s0 i a) /\
  get_instruction bb t.vs_inst_idx = SOME j ==>
  frame_reach C fn s0 j t
Proof
  ho_match_mp_tac scfg_iprefix_ind >> rpt strip_tac
  >- metis_tac[] >>
  `u.vs_current_bb = a.vs_current_bb` by
    metis_tac[venomInstPropsTheory.step_preserves_control_flow] >>
  first_x_assum irule >> simp[] >> rpt strip_tac >>
  irule (cj 2 frame_reach_rules) >>
  conj_tac
  >- (simp[contextCodegenRelTheory.active_inst_def] >> qexists_tac `bb` >>
      fs[venomInstTheory.get_instruction_def, AllCaseEqs()]) >>
  qexistsl_tac [`k`, `i`] >> simp[]
QED

Theorem scfg_exec_block_frame_continue:
  !n C bb a u. exec_block n C bb a = OK u /\ ~u.vs_halted ==>
  !fn s0 j t. MEM bb fn.fn_blocks /\ bb.bb_label = a.vs_current_bb /\
  (!i. get_instruction bb a.vs_inst_idx = SOME i ==> frame_reach C fn s0 i a) /\
  enters_block fn u t /\ active_inst fn j t ==> frame_reach C fn s0 j t
Proof
  rpt gen_tac >>
  measureInduct_on `LENGTH bb.bb_instructions - a.vs_inst_idx` >>
  rpt strip_tac >>
  qpat_x_assum `exec_block _ _ _ _ = OK _` mp_tac >>
  simp[Once exec_block_def] >>
  Cases_on `get_instruction bb a.vs_inst_idx` >> simp[] >>
  rename1 `get_instruction bb a.vs_inst_idx = SOME i` >>
  Cases_on `step_inst n C i a` >> simp[] >>
  rename1 `step_inst n C i a = OK next` >>
  Cases_on `is_terminator i.inst_opcode`
  >- (Cases_on `next.vs_halted` >> simp[] >> strip_tac >> gvs[] >>
      irule (cj 3 frame_reach_rules) >> metis_tac[]) >>
  simp[] >> strip_tac >>
  `a.vs_inst_idx < LENGTH bb.bb_instructions` by
    fs[venomInstTheory.get_instruction_def, AllCaseEqs()] >>
  `next.vs_current_bb = a.vs_current_bb` by
    metis_tac[venomInstPropsTheory.step_preserves_control_flow] >>
  first_x_assum (qspec_then `SUC a.vs_inst_idx` mp_tac) >>
  impl_tac >- decide_tac >>
  disch_then (qspec_then `next with vs_inst_idx := SUC a.vs_inst_idx` mp_tac) >>
  simp[] >> disch_then irule >> simp[] >> rpt strip_tac >>
  irule (cj 2 frame_reach_rules) >> conj_tac
  >- (simp[contextCodegenRelTheory.active_inst_def] >> qexists_tac `bb` >>
      fs[venomInstTheory.get_instruction_def, AllCaseEqs()]) >>
  qexistsl_tac [`n`, `i`] >> simp[]
QED

Theorem scfg_eval_phis_take_prefix:
  !xs s. eval_phis s xs = eval_phis s (TAKE (phi_prefix_length xs) xs)
Proof
  Induct >> simp[eval_phis_def, phi_prefix_length_def] >>
  rpt gen_tac >> Cases_on `h.inst_opcode = PHI` >>
  simp[eval_phis_def, phi_prefix_length_def]
QED

Theorem scfg_lookup_active:
  lookup_block a.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_label = t.vs_current_bb /\ get_instruction bb t.vs_inst_idx = SOME i ==>
  active_inst fn i t
Proof
  strip_tac >> drule simplifyCfgDefsTheory.lookup_block_member_label >>
  strip_tac >> simp[contextCodegenRelTheory.active_inst_def] >>
  qexists_tac `bb` >> fs[venomInstTheory.get_instruction_def, AllCaseEqs()]
QED

Theorem scfg_run_block_frame_continue:
  lookup_block a.vs_current_bb fn.fn_blocks = SOME bb /\
  run_block n C bb a = OK u /\ ~u.vs_halted /\
  (!i v. enters_block fn a v /\ active_inst fn i v ==> frame_reach C fn s0 i v) /\
  enters_block fn u t /\ active_inst fn j t ==> frame_reach C fn s0 j t
Proof
  strip_tac >>
  qpat_x_assum `run_block _ _ _ _ = _` mp_tac >>
  qspecl_then [`a`, `bb.bb_instructions`] strip_assume_tac eval_phis_ok_or_error_defs >>
  simp[run_block_def] >> strip_tac >>
  rename1 `eval_phis a bb.bb_instructions = OK v` >>
  `v.vs_current_bb = a.vs_current_bb` by
    metis_tac[venomExecProofsTheory.eval_phis_preserves_current_bb] >>
  drule simplifyCfgDefsTheory.lookup_block_member_label >> strip_tac >>
  drule scfg_exec_block_frame_continue >> simp[] >> disch_then irule >>
  simp[] >> rpt strip_tac >> first_x_assum irule >> conj_tac
  >- (simp[contextCodegenRelTheory.active_inst_def] >> qexists_tac `bb` >>
      fs[venomInstTheory.get_instruction_def, AllCaseEqs()]) >>
  simp[contextCodegenRelTheory.enters_block_def] >> metis_tac[]
QED

Theorem scfg_bprefix_frame_continue:
  !C fn a u. scfg_bprefix C fn a u ==>
  !s0. (!i v. enters_block fn a v /\ active_inst fn i v ==> frame_reach C fn s0 i v) ==>
  !j t. enters_block fn u t /\ active_inst fn j t ==> frame_reach C fn s0 j t
Proof
  ho_match_mp_tac scfg_bprefix_ind >> rpt strip_tac >>
  qpat_x_assum `!s0. _` (qspec_then `s0` mp_tac) >>
  impl_tac
  >- (rpt strip_tac >> irule scfg_run_block_frame_continue >>
      goal_assum (drule_at Any) >> metis_tac[]) >>
  disch_then irule >> simp[]
QED

Theorem scfg_bprefix_enter_reach:
  scfg_bprefix C fn s0 s /\ enters_block fn s a /\ active_inst fn i a ==>
  frame_reach C fn s0 i a
Proof
  strip_tac >> drule scfg_bprefix_frame_continue >>
  disch_then (qspec_then `s0` mp_tac) >>
  disch_then irule >> simp[] >> metis_tac[frame_reach_rules]
QED

Theorem scfg_rooted_prefix_frame_reach:
  scfg_bprefix C fn s0 s /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  eval_phis s (TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions) = OK v /\
  a = v with vs_inst_idx := phi_prefix_length bb.bb_instructions /\
  scfg_iprefix C bb a t /\ get_instruction bb t.vs_inst_idx = SOME j ==>
  frame_reach C fn s0 j t
Proof
  strip_tac >>
  `eval_phis s bb.bb_instructions = OK v` by metis_tac[scfg_eval_phis_take_prefix] >>
  `v.vs_current_bb = s.vs_current_bb` by
    metis_tac[venomExecProofsTheory.eval_phis_preserves_current_bb] >>
  drule simplifyCfgDefsTheory.lookup_block_member_label >> strip_tac >>
  drule scfg_iprefix_frame_reach >> disch_then irule >> simp[] >>
  rpt strip_tac >> irule scfg_bprefix_enter_reach >>
  conj_tac
  >- (irule scfg_lookup_active >> qexistsl_tac [`s`, `bb`] >> simp[]) >>
  qexists_tac `s` >> simp[contextCodegenRelTheory.enters_block_def] >> metis_tac[]
QED

Theorem scfg_iprefix_current_bb:
  !C bb s t. scfg_iprefix C bb s t ==> t.vs_current_bb = s.vs_current_bb
Proof
  ho_match_mp_tac scfg_iprefix_ind >> simp[] >> rpt strip_tac >>
  metis_tac[venomInstPropsTheory.step_preserves_control_flow]
QED

Theorem scfg_run_block_nonerror_unique[local]:
  run_block k C bb s = r /\ run_block n C bb s = q /\
  terminates r /\ terminates q ==> r = q
Proof
  strip_tac >>
  `!e. r <> Error e` by (Cases_on `r` >> fs[terminates_def]) >>
  `!e. q <> Error e` by (Cases_on `q` >> fs[terminates_def]) >>
  `run_block (MAX k n) C bb s = r` by
    (irule run_block_fuel_mono >> simp[] >> qexists_tac `k` >> simp[]) >>
  `run_block (MAX k n) C bb s = q` by
    (irule run_block_fuel_mono >> simp[] >> qexists_tac `n` >> simp[]) >>
  metis_tac[]
QED

Theorem scfg_bstep_cancel_bounded[local]:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  run_block k C bb s = OK u /\ ~u.vs_halted /\
  run_blocks n C fn s = r /\ terminates r ==>
  ?m. m < n /\ run_blocks m C fn u = r
Proof
  namedCases_on `n` ["", "n0"] >- simp[Once run_blocks_def, terminates_def] >>
  strip_tac >>
  qpat_x_assum `run_blocks _ _ _ _ = _` mp_tac >>
  rewrite_tac[run_blocks_unfold] >> simp[] >>
  Cases_on `run_block n0 C bb s` >> simp[] >> strip_tac
  >- (`OK u = OK v` by
        (irule scfg_run_block_nonerror_unique >>
         simp[terminates_def] >> metis_tac[]) >>
      gvs[] >> qexists_tac `n0` >> simp[]) >>
  gvs[terminates_def] >>
  `OK u = run_block n0 C bb s` by
    (irule scfg_run_block_nonerror_unique >>
     simp[terminates_def] >> metis_tac[]) >>
  Cases_on `run_block n0 C bb s` >> gvs[terminates_def]
QED

Theorem scfg_bprefix_cancel_bounded:
  !C fn s t. scfg_bprefix C fn s t ==>
  !n r. run_blocks n C fn s = r /\ terminates r ==>
  ?m. m <= n /\ run_blocks m C fn t = r
Proof
  ho_match_mp_tac scfg_bprefix_ind >> rpt strip_tac
  >- (qexists_tac `n` >> simp[]) >>
  drule_all scfg_bstep_cancel_bounded >> strip_tac >>
  first_x_assum drule >> simp[] >> strip_tac >>
  goal_assum (drule_at Any) >> decide_tac
QED
