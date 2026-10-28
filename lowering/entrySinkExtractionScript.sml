(*
 * Straight-line fragments: a successful run, recovered through a SINK
 * observer block.
 *
 * TOP-LEVEL:
 *   frag_exec_straight_run
 *
 * Helpers: halt_state_injective_nonhalted, synthetic_sink_endpoint,
 *   step_inst_base_nonterminator_no_exit, drop_cons_instruction,
 *   exec_block_sink_converse, run_inst_seq_preserves_entry_control,
 *   exec_block_sink_not_ok.
 *)
Theory entrySinkExtraction
Ancestors
  fragExec abiDecodeStaticProps venomExecProofs venomInstProofs
  exprLoweringProps venomExecSemantics venomInst venomState list rich_list
  instIdxIndep

Theorem halt_state_injective_nonhalted:
  !s t. ~s.vs_halted /\ ~t.vs_halted /\ halt_state s = halt_state t ==>
    s = t
Proof
  simp[halt_state_def, venom_state_component_equality] >> rpt strip_tac >> simp[]
QED

Theorem synthetic_sink_endpoint:
  !fuel ctx fn lbl pre id s.
    s.vs_current_bb = lbl /\ s.vs_inst_idx = LENGTH pre ==>
    run_from fuel ctx
      (fn with fn_blocks :=
        [<| bb_label := lbl;
            bb_instructions := pre ++ [mk_inst id SINK [] []] |>]) s =
    Halt (halt_state s)
Proof
  rpt strip_tac >>
  simp[run_from_def, lookup_block_def, Once exec_block_def,
       get_instruction_def, EL_APPEND_EQN, step_inst_non_invoke,
       step_inst_base_def, mk_inst_def, FIND_def, INDEX_FIND_def]
QED

Theorem step_inst_base_nonterminator_no_exit:
  !i s. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode ==>
    (!h. step_inst_base i s <> Halt h) /\
    (!v t. step_inst_base i s <> IntRet v t)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `i.inst_opcode` >> gvs[is_terminator_def] >>
  asm_simp_tac bool_ss [step_inst_base_opcode_eqs] >>
  simp[exec_pure1_def, exec_pure2_def, exec_pure3_def,
       exec_read0_def, exec_read1_def, exec_write2_def,
       exec_ext_call_def, exec_delegatecall_def, exec_create_def,
       exec_alloca_def, AllCaseEqs()]
QED

Theorem drop_cons_instruction[local]:
  !l n i rest. DROP n l = i::rest ==>
    n < LENGTH l /\ EL n l = i /\ DROP (SUC n) l = rest
Proof
  Induct >> simp[] >> Cases_on `n` >> simp[] >> rpt strip_tac >>
  first_x_assum drule >> simp[]
QED

Theorem exec_block_sink_converse:
  !is s bb fuel ctx id h.
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) is /\
    DROP s.vs_inst_idx bb.bb_instructions = is ++ [mk_inst id SINK [] []] /\
    exec_block fuel ctx bb s = Halt h ==>
    ?u. run_inst_seq is s = OK u /\
        h = halt_state (u with vs_inst_idx := s.vs_inst_idx + LENGTH is)
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- (fs[] >> drule drop_cons_instruction >> strip_tac >>
      qpat_x_assum `exec_block _ _ _ _ = _` mp_tac >>
      simp[Once exec_block_def, get_instruction_def, step_inst_non_invoke,
           step_inst_base_def, mk_inst_def] >> strip_tac >>
      simp[run_inst_seq_def]) >>
  gvs[] >> drule drop_cons_instruction >> strip_tac >>
  qpat_x_assum `exec_block _ _ _ _ = _` mp_tac >>
  simp[Once exec_block_def, get_instruction_def, step_inst_non_invoke] >>
  rename1 `step_inst_base inst s` >>
  `(!h. step_inst_base inst s <> Halt h) /\
   (!v t. step_inst_base inst s <> IntRet v t)` by
    (irule step_inst_base_nonterminator_no_exit >> simp[]) >>
  Cases_on `step_inst_base inst s` >> gvs[] >> strip_tac >>
  rename1 `step_inst_base inst s = OK s1` >>
  `s1.vs_inst_idx = s.vs_inst_idx` by
    metis_tac[step_preserves_control_flow, step_inst_non_invoke] >>
  first_x_assum (qspec_then `s1 with vs_inst_idx := SUC s.vs_inst_idx` mp_tac) >>
  disch_then (qspecl_then [`bb`, `fuel`, `ctx`, `id`] mp_tac) >>
  simp[] >> strip_tac >>
  `EVERY (\i. ~is_terminator i.inst_opcode) is` by fs[EVERY_MEM] >>
  qpat_x_assum `run_inst_seq is (_ with vs_inst_idx := _) = _` mp_tac >>
  simp[run_inst_seq_inst_idx] >>
  Cases_on `run_inst_seq is s1` >> simp[exec_result_map_def] >>
  strip_tac >> gvs[] >>
  simp[run_inst_seq_def, arithmeticTheory.ADD_CLAUSES]
QED

Theorem run_inst_seq_preserves_entry_control:
  !is s t.
    run_inst_seq is s = OK t /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) is ==>
    t.vs_halted = s.vs_halted /\
    t.vs_current_bb = s.vs_current_bb /\ t.vs_prev_bb = s.vs_prev_bb
Proof
  rpt gen_tac >> strip_tac >>
  irule (SRULE [] (Q.ISPEC
    `\s:venom_state. (s.vs_halted,s.vs_current_bb,s.vs_prev_bb)`
    run_inst_seq_preserves_field)) >>
  qexists_tac `is` >> simp[] >> rpt strip_tac >> fs[EVERY_MEM] >>
  metis_tac[step_preserves_halted, step_preserves_control_flow, step_inst_non_invoke]
QED

Theorem exec_block_sink_not_ok:
  !is s bb fuel ctx id v.
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) is /\
    DROP s.vs_inst_idx bb.bb_instructions = is ++ [mk_inst id SINK [] []] ==>
    exec_block fuel ctx bb s <> OK v
Proof
  Induct >> rpt gen_tac >> strip_tac >> fs[] >>
  drule drop_cons_instruction >> strip_tac
  >- simp[Once exec_block_def, get_instruction_def, step_inst_non_invoke,
          step_inst_base_def, mk_inst_def] >>
  simp[Once exec_block_def, get_instruction_def, step_inst_non_invoke] >>
  rename1 `step_inst_base inst s` >>
  Cases_on `step_inst_base inst s` >> simp[] >>
  rename1 `step_inst_base inst s = OK next` >>
  first_x_assum (qspec_then `next with vs_inst_idx := SUC s.vs_inst_idx` mp_tac) >>
  simp[] >> disch_then irule >> simp[] >> qexists_tac `id` >> simp[]
QED

Theorem frag_exec_straight_run:
  !ctx st st' P Q s.
    dec_straight st st' /\ frag_exec ctx st st' P Q (\r. F) /\
    P s /\ ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
    s.vs_inst_idx = LENGTH st.cs_current_insts ==>
    ?u. run_inst_seq (emitted_insts st st') s = OK u /\
        Q (u with vs_inst_idx := LENGTH st'.cs_current_insts) /\
        ~u.vs_halted /\ u.vs_current_bb = s.vs_current_bb /\
        u.vs_prev_bb = s.vs_prev_bb
Proof
  rpt strip_tac >>
  qabbrev_tac `bb = <|bb_label := st'.cs_current_bb;
    bb_instructions := st'.cs_current_insts ++ [mk_inst 0 SINK [] []]|>` >>
  qabbrev_tac `fn = (ARB:ir_function) with fn_blocks := [bb]` >>
  `fn_has_code st st' fn` by
    (gvs[Abbr `fn`, Abbr `bb`, dec_straight_def, fn_has_code_def,
         emitted_blocks_def, lookup_block_def, FIND_def, INDEX_FIND_def,
         IS_PREFIX_APPEND]) >>
  qpat_x_assum `frag_exec _ _ _ _ _ _` mp_tac >>
  rewrite_tac[frag_exec_def] >>
  disch_then (qspecl_then [`fn`, `s`] mp_tac) >> simp[] >> strip_tac >>
  rename1 `Q post` >>
  `run_from 0 ctx fn post = Halt (halt_state post)` by
    (simp[Abbr `fn`, Abbr `bb`] >> irule synthetic_sink_endpoint >> simp[]) >>
  qpat_x_assum `!fuel. _` (qspec_then `0` mp_tac) >>
  simp[] >> strip_tac >>
  `st'.cs_current_bb = st.cs_current_bb /\
   EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts st st')` by fs[dec_straight_def] >>
  `DROP s.vs_inst_idx bb.bb_instructions =
     emitted_insts st st' ++ [mk_inst 0 SINK [] []]` by
    (fs[dec_straight_def, emitHelperPropsTheory.inst_extends_def] >>
     simp[Abbr `bb`, Once emitHelperPropsTheory.inst_extends_def] >>
     qpat_x_assum `st'.cs_current_insts = _` (fn th => CONV_TAC (LAND_CONV (ONCE_DEPTH_CONV (REWR_CONV th)))) >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> REFL_TAC) >>
  `!v. exec_block fuel' ctx bb s <> OK v` by
    (gen_tac >> irule exec_block_sink_not_ok >> metis_tac[]) >>
  `exec_block fuel' ctx bb s = Halt (halt_state post)` by
    (qpat_x_assum `run_from _ _ _ s = _` mp_tac >>
     simp[run_from_def, Abbr `fn`, lookup_block_def,
          FIND_def, INDEX_FIND_def, Abbr `bb`] >>
     qmatch_goalsub_abbrev_tac `run_block_non_phis fuel' ctx blk s` >>
     `!v. exec_block fuel' ctx blk s <> OK v` by
       (simp[Abbr `blk`] >> metis_tac[]) >>
     Cases_on `exec_block fuel' ctx blk s` >> gvs[Abbr `blk`]) >>
  drule_all exec_block_sink_converse >> strip_tac >>
  `u.vs_halted = s.vs_halted /\
   u.vs_current_bb = s.vs_current_bb /\ u.vs_prev_bb = s.vs_prev_bb` by
    (irule run_inst_seq_preserves_entry_control >> metis_tac[]) >>
  `s.vs_inst_idx + LENGTH (emitted_insts st st') =
     LENGTH st'.cs_current_insts` by
    (fs[dec_straight_def, emitHelperPropsTheory.inst_extends_def] >>
     qpat_x_assum `st'.cs_current_insts = _` (mp_tac o AP_TERM ``LENGTH:instruction list -> num``) >> simp[]) >>
  `post = u with vs_inst_idx := LENGTH st'.cs_current_insts` by
    (irule halt_state_injective_nonhalted >> simp[] >> metis_tac[]) >>
  qexists_tac `u` >> gvs[]
QED
