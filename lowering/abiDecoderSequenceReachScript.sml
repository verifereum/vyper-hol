(* Generic straight-line execution reach, independent of encoder correctness. *)
Theory abiDecoderSequenceReach
Ancestors
  abiDecoderLoop abiDecoderContract fragExec exprLoweringProps emitHelperProps compileEnv
  venomExecSemantics venomExecProofs venomInstProofs venomState venomInst instIdxIndep list rich_list relation

Theorem abi_decoder_run_sequence_reach:
  st'.cs_blocks = st.cs_blocks /\ st'.cs_current_bb = st.cs_current_bb /\ inst_extends st st' /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) (emitted_insts st st') /\
  fn_has_code st st' func /\ run_inst_seq (emitted_insts st st') initial = OK encoded /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. t = encoded with vs_inst_idx := LENGTH st'.cs_current_insts /\
    t.vs_current_bb = st'.cs_current_bb /\ t.vs_inst_idx = LENGTH st'.cs_current_insts /\
    abi_decode_sim ctx func initial t
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  `isPREFIX st.cs_current_insts st'.cs_current_insts` by
    (gvs[inst_extends_def, IS_PREFIX_APPEND] >> metis_tac[]) >>
  `frag_exec ctx st st' (\s. s = initial)
    (\t. t = encoded with vs_inst_idx := LENGTH st'.cs_current_insts) (K F)` by
    (irule frag_exec_run_inst_seq >> simp[] >> qexists_tac `encoded` >> simp[]) >>
  drule abi_decode_sim_from_fragment >> disch_then drule >> simp[]
QED

Definition decoder_straight_step_def:
  decoder_straight_step fn s t <=>
    ~s.vs_halted /\ ?bb inst.
      lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
      get_instruction bb s.vs_inst_idx = SOME inst /\
      inst.inst_opcode <> INVOKE /\ block_step bb s = (OK t,F)
End

Definition decoder_straight_prefix_def:
  decoder_straight_prefix fn s t <=> RTC (decoder_straight_step fn) s t
End

Theorem decoder_straight_prefix_refl:
  decoder_straight_prefix fn s s
Proof
  simp[decoder_straight_prefix_def]
QED

Theorem decoder_straight_prefix_trans:
  decoder_straight_prefix fn s t /\ decoder_straight_prefix fn t u ==>
  decoder_straight_prefix fn s u
Proof
  metis_tac[decoder_straight_prefix_def, RTC_TRANSITIVE, transitive_def]
QED

Theorem decoder_straight_step_intro:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  inst.inst_opcode <> INVOKE /\ ~is_terminator inst.inst_opcode /\
  step_inst_base inst s = OK u ==>
  decoder_straight_step fn s (u with vs_inst_idx := SUC s.vs_inst_idx)
Proof
  rpt strip_tac >>
  `u.vs_inst_idx = s.vs_inst_idx` by
    metis_tac[step_preserves_control_flow, step_inst_non_invoke] >>
  simp[decoder_straight_step_def, block_step_def, next_inst_def, arithmeticTheory.ADD1]
QED

Theorem decoder_straight_prefix_step:
  decoder_straight_step fn s t ==> decoder_straight_prefix fn s t
Proof
  simp[decoder_straight_prefix_def, RTC_SINGLE]
QED

Theorem decoder_straight_prefix_run_inst_seq:
  !is s u bb fn.
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX is (DROP s.vs_inst_idx bb.bb_instructions) /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) is /\
  ~s.vs_halted /\ run_inst_seq is s = OK u ==>
  decoder_straight_prefix fn s (u with vs_inst_idx := s.vs_inst_idx + LENGTH is)
Proof
  Induct >> simp[run_inst_seq_def] >- simp[decoder_straight_prefix_refl] >>
  rpt gen_tac >> strip_tac >> fs[] >>
  `?rest. DROP s.vs_inst_idx bb.bb_instructions = h :: rest /\
          isPREFIX is rest` by
    (Cases_on `DROP s.vs_inst_idx bb.bb_instructions` >> gvs[]) >>
  `s.vs_inst_idx < LENGTH bb.bb_instructions /\
   EL s.vs_inst_idx bb.bb_instructions = h /\
   DROP (SUC s.vs_inst_idx) bb.bb_instructions = rest` by
    (qpat_x_assum `DROP _ _ = _` mp_tac >>
     map_every (fn (a,b) => Q.SPEC_TAC (a,b))
       [(`s.vs_inst_idx`,`n`), (`bb.bb_instructions`,`xs`)] >>
     Induct >> Cases_on `n` >> simp[] >> metis_tac[]) >>
  Cases_on `step_inst_base h s` >> gvs[] >>
  rename1 `step_inst_base h s = OK s1` >>
  `s1.vs_current_bb = s.vs_current_bb /\ s1.vs_inst_idx = s.vs_inst_idx /\
   s1.vs_halted = s.vs_halted` by
    metis_tac[step_preserves_control_flow, step_preserves_halted, step_inst_non_invoke] >>
  `decoder_straight_prefix fn s (s1 with vs_inst_idx := SUC s.vs_inst_idx)` by
    (irule decoder_straight_prefix_step >> irule decoder_straight_step_intro >>
     simp[] >> qexists_tac `h` >> simp[get_instruction_def] >>
     metis_tac[HD_DROP, HD]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) is` by fs[EVERY_MEM] >>
  first_x_assum (qspecl_then [`s1 with vs_inst_idx := SUC s.vs_inst_idx`,
    `u with vs_inst_idx := SUC s.vs_inst_idx`, `bb`, `fn`] mp_tac) >>
  simp[run_inst_seq_inst_idx, exec_result_map_def] >>
  strip_tac >>
  drule_all decoder_straight_prefix_trans >>
  simp[arithmeticTheory.ADD1]
QED

Theorem abi_decoder_sequence_placement[local]:
  st'.cs_current_bb = st.cs_current_bb /\ inst_extends st st' /\
  fn_has_code st st' func /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?bb. lookup_block initial.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX (emitted_insts st st') (DROP initial.vs_inst_idx bb.bb_instructions) /\
    initial.vs_inst_idx + LENGTH (emitted_insts st st') = LENGTH st'.cs_current_insts
Proof
  rpt strip_tac >>
  `isPREFIX st.cs_current_insts st'.cs_current_insts` by
    (gvs[inst_extends_def, IS_PREFIX_APPEND] >> metis_tac[]) >>
  `?bb. lookup_block st.cs_current_bb func.fn_blocks = SOME bb /\
        isPREFIX st'.cs_current_insts bb.bb_instructions` by
    (gvs[fn_has_code_def] >> metis_tac[]) >>
  qexists_tac `bb` >> gvs[IS_PREFIX_APPEND, emitted_insts_def] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >>
  metis_tac[]
QED

Theorem abi_decoder_run_sequence_prefix:
  st'.cs_blocks = st.cs_blocks /\ st'.cs_current_bb = st.cs_current_bb /\ inst_extends st st' /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) (emitted_insts st st') /\
  fn_has_code st st' func /\ run_inst_seq (emitted_insts st st') initial = OK encoded /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t. t = encoded with vs_inst_idx := LENGTH st'.cs_current_insts /\
    t.vs_current_bb = st'.cs_current_bb /\ t.vs_inst_idx = LENGTH st'.cs_current_insts /\
    decoder_straight_prefix func initial t
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decoder_sequence_placement >> strip_tac >>
  `decoder_straight_prefix func initial
    (encoded with vs_inst_idx := initial.vs_inst_idx + LENGTH (emitted_insts st st'))` by
    (irule decoder_straight_prefix_run_inst_seq >> gvs[]) >>
  `encoded.vs_current_bb = initial.vs_current_bb` by
    (mp_tac (Q.SPEC `emitted_insts st st'` exec_block_run_inst_seq) >>
     disch_then (qspecl_then [`initial`, `0`, `ctx`, `bb`] mp_tac) >> simp[]) >>
  qexists_tac `encoded with vs_inst_idx := LENGTH st'.cs_current_insts` >> gvs[]
QED

Theorem abi_decoder_run_sequence_abort:
  st'.cs_blocks = st.cs_blocks /\ st'.cs_current_bb = st.cs_current_bb /\ inst_extends st st' /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) (emitted_insts st st') /\
  fn_has_code st st' func /\ run_inst_seq (emitted_insts st st') initial = Abort a encoded /\
  ~initial.vs_halted /\ initial.vs_current_bb = st.cs_current_bb /\
  initial.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?bb n. lookup_block initial.vs_current_bb func.fn_blocks = SOME bb /\
    exec_block 0 ctx bb initial = Abort a (encoded with vs_inst_idx := n) /\
    run_from 0 ctx func initial = Abort a (encoded with vs_inst_idx := n)
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all abi_decoder_sequence_placement >> strip_tac >>
  `?n. exec_block 0 ctx bb initial = Abort a (encoded with vs_inst_idx := n)` by
    (mp_tac (Q.SPEC `emitted_insts st st'` exec_block_run_inst_seq) >>
     disch_then (qspecl_then [`initial`, `0`, `ctx`, `bb`] mp_tac) >> simp[]) >>
  qexistsl_tac [`bb`, `n`] >> simp[run_from_def]
QED
