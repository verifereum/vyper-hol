(* Replay a straight phase on the old entry block at its shadow label. *)
Theory bodyFullAbiDecodeCutEntryPhase
Ancestors
  bodyFullAbiDecodeCutPath exprSimAbiGasBridge exprSimAbiDecodePrefixExec
  fragFuel fragGasPath fragExec abiEncoderObserver venomInstProps
  venomInst venomExecSemantics venomState context compileEnv arithmetic
  exprLoweringProps rich_list list relation
Libs
  bodyFullAbiDecodeCutPathLib

Theorem entry_phase_path_cons:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  ~is_terminator i.inst_opcode /\ i.inst_opcode <> INVOKE /\
  gas_path ctx fn s n r ==>
  r = OK s \/
  (?v m. step_inst_base i s = OK v /\ ~v.vs_halted /\
         gas_path ctx fn (v with vs_inst_idx := SUC s.vs_inst_idx) m r) \/
  (?a v. r = Abort a v /\ step_inst_base i s = Abort a v) \/
  (!v. r <> OK v /\ !a. r <> Abort a v)
Proof
  strip_tac >> pop_assum mp_tac >> simp[Once gas_path_cases] >>
  simp[gas_path_edge_def] >> rpt strip_tac >>
  gvs[step_inst_non_invoke, exit_result_def]
  >- (disj2_tac >> disj1_tac >> qexists `m` >> first_assum ACCEPT_TAC) >>
  Cases_on `step_inst_base i s` >> gvs[exit_result_def]
QED

Theorem entry_phase_path_stop:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst j STOP [] []) /\
  gas_path ctx fn s n r ==>
  r = OK s \/ r = Halt (stop_view s)
Proof
  strip_tac >> pop_assum mp_tac >> simp[Once gas_path_cases] >>
  simp[gas_path_edge_def] >> rpt strip_tac >>
  FULL_SIMP_TAC (srw_ss())
    [step_inst_non_invoke, exit_result_def, step_inst_base_opcode_eqs,
     mk_inst_def, is_terminator_def, stop_view_def, halt_state_def]
QED

Theorem entry_phase_shadow_updates[local]:
  frag_relabel_state L entry u s /\ u.vs_current_bb = L ==>
  u = s with <|vs_current_bb := L; vs_prev_bb := u.vs_prev_bb|>
Proof
  rw[frag_relabel_state_def, venom_state_component_equality]
QED

Theorem entry_phase_shadow_step[local]:
  lookup_block L obs.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\ FST cut <> L /\
  u.vs_current_bb = L /\ frag_relabel_state L entry u s /\
  ~s.vs_halted /\ ~v.vs_halted /\
  i.inst_opcode <> INVOKE /\ i.inst_opcode <> PHI /\ ~is_terminator i.inst_opcode /\
  step_inst_base i s = OK v ==>
  ?w. abi_observer_step ctx obs cut u w /\ w.vs_current_bb = L /\
      frag_relabel_state L entry w (v with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  strip_tac >> drule frag_relabel_state_fields >> strip_tac >>
  `v.vs_current_bb = entry` by
    metis_tac[step_inst_non_invoke, step_preserves_control_flow] >>
  qabbrev_tac `t = v with vs_inst_idx := SUC s.vs_inst_idx` >>
  qexists `t with <|vs_current_bb := L; vs_prev_bb := u.vs_prev_bb|>` >>
  simp[] >> reverse conj_tac >-
    (simp[frag_relabel_state_def] >> qexists `t.vs_prev_bb` >>
     simp[venom_state_component_equality, Abbr `t`]) >>
  `step_inst_base i u = OK (v with <|vs_current_bb := L; vs_prev_bb := u.vs_prev_bb|>)` by
    (drule_all frag_relabel_base_nonphi >>
     drule_all entry_phase_shadow_updates >> strip_tac >> pop_assum SUBST1_TAC >> simp[]) >>
  Cases_on `cut` >> gvs[] >>
  simp[abi_observer_step_def, step_inst_non_invoke, Abbr `t`] >>
  qexists `v with <|vs_current_bb := u.vs_current_bb; vs_prev_bb := u.vs_prev_bb|>` >>
  simp[venom_state_component_equality]
QED

Theorem entry_phase_shadow_abort[local]:
  lookup_block L obs.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  u.vs_current_bb = L /\ frag_relabel_state L entry u s /\
  i.inst_opcode <> INVOKE /\ i.inst_opcode <> PHI /\ ~is_terminator i.inst_opcode /\
  step_inst_base i s = Abort Revert_abort v ==>
  ?w k. frag_relabel_state L entry w v /\
        run_from k ctx obs u = Abort Revert_abort w
Proof
  strip_tac >> drule frag_relabel_state_fields >> strip_tac >>
  drule_all frag_relabel_base_abort >> strip_tac >>
  `(s with <|vs_current_bb := entry; vs_prev_bb := s.vs_prev_bb|>) = s` by
    simp[venom_state_component_equality] >>
  `v.vs_prev_bb = s.vs_prev_bb /\ v.vs_current_bb = entry` by
    (qpat_x_assum `!p b. step_inst_base _ _ = _`
       (qspecl_then [`s.vs_prev_bb`,`entry`] mp_tac) >>
     asm_rewrite_tac[] >> simp[venom_state_component_equality]) >>
  qexistsl [`v with <|vs_current_bb := L; vs_prev_bb := u.vs_prev_bb|>`,`0`] >>
  conj_tac >-
    (simp[frag_relabel_state_def] >> qexists `s.vs_prev_bb` >>
     simp[venom_state_component_equality]) >>
  `step_inst_base i u = Abort Revert_abort
    (v with <|vs_current_bb := L; vs_prev_bb := u.vs_prev_bb|>)` by
    (drule_all entry_phase_shadow_updates >> strip_tac >> pop_assum SUBST1_TAC >> simp[]) >>
  `get_instruction bb u.vs_inst_idx = SOME i` by metis_tac[] >>
  `lookup_block u.vs_current_bb obs.fn_blocks = SOME bb` by simp[] >>
  drule_all run_from_nonterm >> simp[step_inst_non_invoke]
QED

(* The synthetic STOP enforces the phase boundary only on the source.
   In the shadow function all edges use the real, fixed outer cut. *)
Theorem entry_phase_replay[local]:
  !xs s n r u.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    lookup_block L obs.fn_blocks = SOME shadow /\
    DROP s.vs_inst_idx bb.bb_instructions = xs ++ [mk_inst j STOP [] []] /\
    isPREFIX xs (DROP s.vs_inst_idx shadow.bb_instructions) /\
    s.vs_inst_idx + LENGTH xs = phase_end /\ ~s.vs_halted /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> PHI /\
               ~is_terminator i.inst_opcode) xs /\
    gas_path ctx fn s n r /\
    ((?t. r = OK t /\ t.vs_inst_idx = phase_end) \/ (?t. r = Abort Revert_abort t)) /\
    u.vs_current_bb = L /\ frag_relabel_state L entry u s /\ FST cut <> L ==>
    (^(bodyFullAbiDecodeCutPathLib.shadow_result)) ctx obs cut L entry u (L,phase_end) r
Proof
  Induct >- suspend "stop" >>
  simp_tac pure_ss [LENGTH, EVERY_DEF, APPEND, BETA_THM] >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  rename1 `DROP _ bb.bb_instructions = i::(xs ++ _)` >>
  `isPREFIX (i::xs) (DROP s.vs_inst_idx bb.bb_instructions)` by simp[] >>
  every_drule_then strip_assume_tac abi_decode_contiguous_prefix_fetch >>
  drule_all entry_phase_path_cons >> strip_tac
  >- (qpat_x_assum `(?t. _ = OK t /\ _) \/ _` mp_tac >> simp[])
  >- suspend "continue"
  >- suspend "reject" >>
  qpat_x_assum `(?t. _ = OK t /\ _) \/ _` strip_assume_tac >> metis_tac[]
QED
Resume entry_phase_replay[stop]:
  simp_tac bool_ss [LENGTH, EVERY_DEF, APPEND, ADD_CLAUSES, BETA_THM] >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `isPREFIX [mk_inst j STOP [] []] (DROP s.vs_inst_idx bb.bb_instructions)` by simp[] >>
  drule abi_decode_contiguous_prefix_fetch >> strip_tac >>
  drule_all entry_phase_path_stop >> strip_tac
  >- (drule frag_relabel_state_fields >> strip_tac >>
      disj1_tac >> qexistsl [`s`,`u`] >> gvs[RTC_REFL]) >>
  metis_tac[exec_result_distinct]
QED
Resume entry_phase_replay[continue]:
  `v.vs_current_bb = s.vs_current_bb` by
    metis_tac[step_inst_non_invoke, step_preserves_control_flow] >>
  `DROP (SUC s.vs_inst_idx) bb.bb_instructions = xs ++ [mk_inst j STOP [] []]` by
    (Q_TAC (TRANS_TAC EQ_TRANS) `DROP 1 (DROP s.vs_inst_idx bb.bb_instructions)` >>
     conj_tac >- simp[NoAsms, DROP_DROP_T, ADD1, ADD_COMM] >> simp[]) >>
  drule_all entry_phase_shadow_step >> disch_then (qspec_then `ctx` strip_assume_tac) >>
  irule (BETA_RULE abi_decode_cut_prefix_bind) >>
  qexists `w` >> reverse conj_tac >- metis_tac[RTC_SINGLE] >>
  first_x_assum (qspecl_then [`v with vs_inst_idx := SUC s.vs_inst_idx`,`m`,`r`,`w`] mp_tac) >>
  simp[ADD_CLAUSES]
QED
Resume entry_phase_replay[reject]:
  `a = Revert_abort` by metis_tac[exec_result_distinct, exec_result_11] >>
  gvs[] >> irule entry_phase_shadow_abort >> simp[] >>
  qexistsl [`i`,`s`] >> simp[]
QED
Finalise entry_phase_replay

Theorem abi_decode_cut_entry_phase:
  cs_extends a b /\ a.cs_blocks = b.cs_blocks /\
  s.vs_current_bb = a.cs_current_bb /\ s.vs_inst_idx = LENGTH a.cs_current_insts /\
  ~s.vs_halted /\ u.vs_current_bb = L /\
  frag_relabel_state L a.cs_current_bb u s /\ FST cut <> L /\
  lookup_block L obs.fn_blocks = SOME shadow /\
  isPREFIX (emitted_insts a b) (DROP (LENGTH a.cs_current_insts) shadow.bb_instructions) /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> PHI /\
             ~is_terminator i.inst_opcode) (emitted_insts a b) /\
  (!fn. fn_has_code a b fn ==> gas_path ctx fn s 0 r) /\
  ((?t. r = OK t /\ t.vs_inst_idx = LENGTH b.cs_current_insts) \/
   (?t. r = Abort Revert_abort t)) ==>
  (^(bodyFullAbiDecodeCutPathLib.shadow_result)) ctx obs cut L a.cs_current_bb u
    (L,LENGTH b.cs_current_insts) r
Proof
  simp_tac pure_ss [BETA_THM] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `emitted_blocks a b = []` by simp[emitted_blocks_def] >>
  qpat_assum `emitted_blocks a b = []` (fn th =>
    drule_then (strip_assume_tac o SRULE [th]) frag_extends_emitted_shape) >>
  qabbrev_tac `bb = <|bb_label := b.cs_current_bb;
                       bb_instructions := b.cs_current_insts ++ [mk_inst 0 STOP [] []]|>` >>
  qabbrev_tac `source = (ARB : ir_function) with fn_blocks := [bb]` >>
  `lookup_block b.cs_current_bb source.fn_blocks = SOME bb` by
    simp[Abbr `source`, Abbr `bb`, lookup_block_def, FIND_thm] >>
  `fn_has_code a b source` by simp[fn_has_code_def, Abbr `bb`, IS_PREFIX_APPEND] >>
  `gas_path ctx source s 0 r` by metis_tac[] >>
  irule (BETA_RULE entry_phase_replay) >> simp[] >>
  qexistsl [`bb`,`source`,`0`,`0`,`s`,`emitted_insts a b`] >>
  simp[Abbr `bb`] >>
  qpat_x_assum `a.cs_current_insts ≼ b.cs_current_insts` mp_tac >>
  simp[IS_PREFIX_APPEND] >>
  disch_then (CHOOSE_THEN (fn th =>
    rewrite_tac [emitted_insts_def, th, GSYM listTheory.APPEND_ASSOC,
                 DROP_LENGTH_APPEND, LENGTH_APPEND])) >>
  metis_tac[]
QED
