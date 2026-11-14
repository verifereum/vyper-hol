(* Joint-path decorations of GAS-event prefixes.  Completed steps and blocks
   are decorated by decorated_step and decorated_block, with the same edges
   decorated_step's block_next and run_next rules use; a prefix ends at the
   decorated GAS config, after the callee entry of every INVOKE it is inside. *)
Theory frameDecoratedPrefix
Ancestors frameFinitePrefix frameDecorationComplete frameDecorationEntry
  frameFiniteControl frameFiniteJointDecoration frameFiniteJointTrace
  frameFiniteExecution frameJointTransition contextCodegenRelProps
  contextCodegenRel gasEvents gasCount gasOracleReplay venomExecSemantics venomExecProofs
  venomState venomInst list rich_list arithmetic

Inductive decorated_prefix:
[~gas:]
  (!C owner bb s i fn q n.
    decoration_at fn i s q /\ get_instruction bb s.vs_inst_idx = SOME i /\
    i.inst_opcode = GAS ==>
    decorated_block_prefix C owner bb s q n [] q [(owner,i.inst_id)])
[~invoke:]
  (!C owner bb s i name ops fn args cs caller q n qc wc qe es.
    decoration_at caller i s q /\ get_instruction bb s.vs_inst_idx = SOME i /\
    i.inst_opcode = INVOKE /\ decode_invoke i = SOME (name,ops) /\
    lookup_function name C.ctx_functions = SOME fn /\
    eval_operands ops s = SOME args /\ setup_callee fn args s = SOME cs /\
    joint_transition C q NONE qc /\
    decorated_run_prefix C fn cs qc (n+1) wc qe es ==>
    decorated_block_prefix C owner bb s q n ((NONE,qc)::wc) qe es)
[~next:]
  (!C owner bb s i k post fn q n ws qm ds ev qn wb qe es.
    decoration_at fn i s q /\ get_instruction bb s.vs_inst_idx = SOME i /\
    decorated_step C i s (OK post) q n ws qm ds /\
    ~is_terminator i.inst_opcode /\ step_inst k C i s = OK post /\
    decoration_consumes C i q post qm ev qn /\
    decoration_entry fn (post with vs_inst_idx := SUC s.vs_inst_idx) qn /\
    decorated_block_prefix C owner bb
      (post with vs_inst_idx := SUC s.vs_inst_idx)
      qn (n+LENGTH ws+1) wb qe es ==>
    decorated_block_prefix C owner bb s q n (ws++[(ev,qn)]++wb) qe
      (gas_events_step k C owner i s ++ es))
[~run_here:]
  (!C fn s bb phi q n w qe es.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    eval_phis s bb.bb_instructions = OK phi /\
    decoration_entry fn
      (phi with vs_inst_idx := phi_prefix_length bb.bb_instructions) q /\
    decorated_block_prefix C fn.fn_name bb
      (phi with vs_inst_idx := phi_prefix_length bb.bb_instructions)
      q n w qe es ==>
    decorated_run_prefix C fn s q n w qe es)
[~run_next:]
  (!C fn s bb phi k post q n wb qm db fuel qn wr qe es.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    eval_phis s bb.bb_instructions = OK phi /\
    decoration_entry fn
      (phi with vs_inst_idx := phi_prefix_length bb.bb_instructions) q /\
    decorated_block C bb (phi with vs_inst_idx :=
      phi_prefix_length bb.bb_instructions) (OK post) q n wb qm db /\
    exec_block k C bb (phi with vs_inst_idx :=
      phi_prefix_length bb.bb_instructions) = OK post /\
    ~post.vs_halted /\ local_pending C qm (OK post) /\
    (?stk PG G tn i si oms om hs h.
      qm = JointConfig stk PG G tn fn i si oms om hs h /\
      active_inst fn i si /\ is_terminator i.inst_opcode) /\
    joint_transition C qm (SOME (OriginBlock fuel post)) qn /\
    decorated_run_prefix C fn post qn (n+LENGTH wb+1) wr qe es ==>
    decorated_run_prefix C fn s q n
      (wb++[(SOME (OriginBlock fuel post),qn)]++wr) qe
      (gas_events_block k C fn.fn_name bb
         (phi with vs_inst_idx := phi_prefix_length bb.bb_instructions) ++ es))
End

Theorem decorated_prefix_erases:
  (!C owner bb s q n w qe es. decorated_block_prefix C owner bb s q n w qe es ==>
    finite_block_prefix C owner bb s es) /\
  (!C fn s q n w qe es. decorated_run_prefix C fn s q n w qe es ==>
    finite_run_prefix C fn s es)
Proof
  ho_match_mp_tac decorated_prefix_ind >> rpt conj_tac
  >- (rpt strip_tac >> irule finite_prefix_gas >> simp[])
  >- (rpt strip_tac >> irule finite_prefix_invoke >> metis_tac[])
  >- (rpt strip_tac >> irule finite_prefix_next >> metis_tac[])
  >- (rpt strip_tac >> irule finite_prefix_run_here >> metis_tac[])
  >> rpt strip_tac >> irule finite_prefix_run_next >> metis_tac[]
QED

Theorem decorated_prefix_segment:
  (!C owner bb s q n w qe es. decorated_block_prefix C owner bb s q n w qe es ==>
    joint_segment C q w qe) /\
  (!C fn s q n w qe es. decorated_run_prefix C fn s q n w qe es ==>
    joint_segment C q w qe)
Proof
  ho_match_mp_tac decorated_prefix_ind >> rpt strip_tac >>
  gvs[joint_segment_def, decoration_consumes_def] >>
  imp_res_tac decorated_execution_segment >>
  once_rewrite_tac[GSYM APPEND_ASSOC] >>
  irule joint_segment_append >> simp[joint_segment_def] >> metis_tac[]
QED

(* The prefix ends at a decorated GAS config whose state has consumed one
   reading fewer than the prefix has events. *)
Theorem decorated_prefix_end:
  (!C owner bb s q n w qe es. decorated_block_prefix C owner bb s q n w qe es ==>
    es <> [] /\
    ?fn i se. decoration_at fn i se qe /\ i.inst_opcode = GAS /\
      se.vs_gas_readings = DROP (LENGTH es - 1) s.vs_gas_readings) /\
  (!C fn s q n w qe es. decorated_run_prefix C fn s q n w qe es ==>
    es <> [] /\
    ?fn i se. decoration_at fn i se qe /\ i.inst_opcode = GAS /\
      se.vs_gas_readings = DROP (LENGTH es - 1) s.vs_gas_readings)
Proof
  ho_match_mp_tac decorated_prefix_ind >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >> simp[] >> metis_tac[])
  >- (rpt gen_tac >> strip_tac >> simp[] >>
      drule gas_setup_callee_readings >> strip_tac >> gvs[] >> metis_tac[])
  >- suspend "next"
  >- (rpt gen_tac >> strip_tac >> simp[] >>
      drule gas_count_phis_ok >> strip_tac >> gvs[] >> metis_tac[])
  >> suspend "run_next"
QED

Resume decorated_prefix_end[next]:
  rpt gen_tac >> strip_tac >>
  qmatch_asmsub_rename_tac `decoration_at fe ie se qe` >>
  conj_tac >- gvs[] >>
  qexistsl [`fe`, `ie`, `se`] >>
  `post.vs_gas_readings =
     DROP (gas_count_step k C i s) s.vs_gas_readings` by
    (mp_tac (cj 1 gas_count_suffix) >>
     disch_then (qspecl_then [`k`, `C`, `i`, `s`] mp_tac) >>
     gvs[gas_count_suffix_def]) >>
  Cases_on `es` >> gvs[DROP_DROP_T, cj 1 gas_events_length]
QED

Resume decorated_prefix_end[run_next]:
  rpt gen_tac >> strip_tac >>
  rename1 `~post.vs_halted` >>
  qmatch_asmsub_rename_tac `decoration_at fe ie se qe` >>
  conj_tac >- gvs[] >>
  qexistsl [`fe`, `ie`, `se`] >>
  drule gas_count_phis_ok >> strip_tac >>
  qabbrev_tac `p = phi with vs_inst_idx := phi_prefix_length bb.bb_instructions` >>
  `post.vs_gas_readings =
     DROP (gas_count_block k C bb p) s.vs_gas_readings` by
    (mp_tac (cj 2 gas_count_suffix) >>
     disch_then (qspecl_then [`k`, `C`, `bb`, `p`] mp_tac) >>
     gvs[gas_count_suffix_def, Abbr `p`]) >>
  Cases_on `es` >> gvs[DROP_DROP_T, cj 2 gas_events_length]
QED

Finalise decorated_prefix_end

(* ===== Completeness: every finite prefix has a decoration ===== *)

Theorem finite_prefix_entry:
  (!C owner bb s es. finite_block_prefix C owner bb s es ==>
    ?i. get_instruction bb s.vs_inst_idx = SOME i) /\
  (!C fn s es. finite_run_prefix C fn s es ==>
    ?p i. enters_block fn s p /\ active_inst fn i p)
Proof
  ho_match_mp_tac finite_prefix_ind >> rpt conj_tac >> rpt strip_tac
  >- metis_tac[]
  >- metis_tac[]
  >- metis_tac[]
  >- (drule eval_phis_preserves_current_bb >> strip_tac >>
      simp[enters_block_def, PULL_EXISTS] >>
      qexists `i` >>
      irule lookup_instruction_active >> qexists `bb` >> gvs[])
  >> rename1 `~post.vs_halted` >>
  drule eval_phis_preserves_current_bb >> strip_tac >>
  `finite_block C bb
     (phi with vs_inst_idx := phi_prefix_length bb.bb_instructions)
     (OK post)` by (simp[finite_block_iff] >> metis_tac[]) >>
  drule finite_block_entry_active >>
  disch_then (qspec_then `fn` mp_tac) >> simp[] >> strip_tac >>
  simp[enters_block_def, PULL_EXISTS] >> metis_tac[]
QED

Theorem finite_prefix_decoration_complete:
  (!C owner bb s es. finite_block_prefix C owner bb s es ==>
    !fn q n. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
      decoration_entry fn s q /\ ALL_DISTINCT (fn_labels fn) /\
      EVERY (\f. ALL_DISTINCT (fn_labels f)) C.ctx_functions ==>
      ?w qe. decorated_block_prefix C owner bb s q n w qe es) /\
  (!C fn s es. finite_run_prefix C fn s es ==>
    !q n p. enters_block fn s p /\ decoration_entry fn p q /\
      ALL_DISTINCT (fn_labels fn) /\
      EVERY (\f. ALL_DISTINCT (fn_labels f)) C.ctx_functions ==>
      ?w qe. decorated_run_prefix C fn s q n w qe es)
Proof
  ho_match_mp_tac finite_prefix_strongind >> rpt conj_tac
  >- (rpt strip_tac >> drule_all decoration_entry_instruction >>
      strip_tac >> irule_at Any decorated_prefix_gas >> metis_tac[])
  >- suspend "invoke"
  >- suspend "next"
  >- suspend "run_here"
  >> suspend "run_next"
QED

Resume finite_prefix_decoration_complete[invoke]:
  rpt strip_tac >> rename1 `lookup_block _ caller.fn_blocks = SOME bb` >>
  drule_all decoration_entry_instruction >> strip_tac >>
  `ALL_DISTINCT (fn_labels fn)` by
    (qpat_x_assum `EVERY _ C.ctx_functions` mp_tac >>
     simp[EVERY_MEM] >> disch_then irule >>
     fs[lookup_function_def] >> metis_tac[venomExecProofsTheory.FIND_MEM]) >>
  drule (cj 2 finite_prefix_entry) >> strip_tac >>
  `?qc. joint_transition C q NONE qc /\ decoration_entry fn p qc` by
    (Cases_on `q` >> gvs[decoration_at_def] >>
     irule_at (Pos hd) joint_transition_call >>
     simp[decoration_entry_def, decoration_at_def] >> metis_tac[]) >>
  first_x_assum (qspecl_then [`qc`, `n+1`, `p`] mp_tac) >>
  simp[] >> strip_tac >>
  irule_at Any decorated_prefix_invoke >> metis_tac[]
QED

Resume finite_prefix_decoration_complete[next]:
  rpt strip_tac >>
  drule_all decoration_entry_instruction >> strip_tac >>
  `finite_step C i s (OK post)` by (simp[finite_step_iff] >> metis_tac[]) >>
  drule_all (cj 1 finite_decoration_complete) >>
  disch_then (qspec_then `n` strip_assume_tac) >>
  drule_all finite_step_nonterminator_control >> strip_tac >>
  drule (cj 1 finite_prefix_entry) >>
  disch_then (qx_choose_then `inext` assume_tac) >>
  `active_inst fn inext (post with vs_inst_idx := SUC s.vs_inst_idx)` by
    (irule lookup_instruction_active >> qexists `bb` >> gvs[]) >>
  drule_all decorated_success_consumable >> strip_tac >>
  first_x_assum (qspecl_then [`fn`, `qn`, `n+LENGTH w+1`] mp_tac) >>
  simp[] >> strip_tac >>
  irule_at Any decorated_prefix_next >>
  goal_assum (drule_at (Pos hd)) >>
  goal_assum (drule_at (Pos hd)) >>
  goal_assum (drule_at (Pos hd)) >> simp[] >> metis_tac[]
QED

Resume finite_prefix_decoration_complete[run_here]:
  rpt strip_tac >>
  `p = phi with vs_inst_idx := phi_prefix_length bb.bb_instructions` by
    gvs[enters_block_def] >> gvs[] >>
  drule eval_phis_preserves_current_bb >> strip_tac >>
  first_x_assum (qspecl_then [`fn`, `q`, `n`] mp_tac) >>
  simp[] >> strip_tac >>
  irule_at Any decorated_prefix_run_here >> metis_tac[]
QED

Resume finite_prefix_decoration_complete[run_next]:
  rpt strip_tac >>
  rename1 `~post.vs_halted` >>
  `p = phi with vs_inst_idx := phi_prefix_length bb.bb_instructions` by
    gvs[enters_block_def] >> gvs[] >>
  drule eval_phis_preserves_current_bb >> strip_tac >>
  qabbrev_tac `p = phi with vs_inst_idx := phi_prefix_length bb.bb_instructions` >>
  `finite_block C bb p (OK post)` by (simp[finite_block_iff] >> metis_tac[]) >>
  `lookup_block p.vs_current_bb fn.fn_blocks = SOME bb` by simp[Abbr `p`] >>
  drule_all (cj 2 finite_decoration_complete) >>
  disch_then (qspec_then `n` strip_assume_tac) >>
  drule (cj 2 decorated_execution_ok_endpoint) >>
  fs[decoration_entry_def] >> disch_then drule >> strip_tac >>
  drule (cj 2 finite_prefix_entry) >>
  disch_then (qx_choosel_then [`pn`, `inext`] strip_assume_tac) >>
  gvs[local_pending_def] >>
  drule (cj 1 finite_execution_realizable) >> strip_tac >>
  rename1 `!k. m <= k ==> step_inst k C ti si = OK post` >>
  `step_inst m C ti si = OK post` by simp[] >>
  `?qn. joint_transition C
    (JointConfig stk PG G tn fn ti si oms om hs h)
    (SOME (OriginBlock m post)) qn /\ decoration_entry fn pn qn` by
    (irule_at (Pos hd) joint_transition_block >>
     simp[decoration_entry_def, decoration_at_def] >> metis_tac[]) >>
  first_x_assum (qspecl_then [`qn`, `n+LENGTH w+1`, `pn`] mp_tac) >>
  (impl_tac >- (fs[decoration_entry_def] >> metis_tac[])) >> strip_tac >>
  qunabbrev_tac `p` >>
  irule_at Any decorated_prefix_run_next >>
  gvs[decoration_entry_def, local_pending_def] >> metis_tac[]
QED

Finalise finite_prefix_decoration_complete
