(* Same-witness ghost frames, observed through a synthetic SINK block. *)
Theory straightFragmentFramePtr
Ancestors entrySinkExtraction abiDecodeStaticProps bodyPtrDefs ptrSafeRun ptrDiscipline
  venomExecSemantics venomInst venomState fragExec emitHelperProps list rich_list

Theorem drop_cons_instruction[local]:
  !l n i rest. DROP n l = i::rest ==>
    n < LENGTH l /\ EL n l = i /\ DROP (SUC n) l = rest
Proof
  Induct >> simp[] >> Cases_on `n` >> simp[] >> rpt strip_tac >>
  first_x_assum drule >> simp[]
QED

Theorem ghost_block_sink_imm[local]:
  !is s bb fuel ctx fn PG G tn id.
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) is /\
    EVERY (\i. !w w' t. (step_taint i w w' t).t_imm = t.t_imm) is /\
    DROP s.vs_inst_idx bb.bb_instructions = is ++ [mk_inst id SINK [] []] ==>
    (SND (ghost_block fuel ctx fn PG G tn bb s)).t_imm = tn.t_imm
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- (fs[] >> drule drop_cons_instruction >> strip_tac >>
      simp[Once ghost_block_def, get_instruction_def, step_inst_non_invoke,
        step_inst_base_def, mk_inst_def]) >>
  fs[] >> drule drop_cons_instruction >> strip_tac >>
  simp[Once ghost_block_def, get_instruction_def, step_inst_non_invoke] >>
  rename1 `step_inst_base inst s` >>
  Cases_on `step_inst_base inst s` >> simp[] >>
  rename1 `step_inst_base inst s = OK next` >>
  simp[ghost_step_def, step_inst_non_invoke] >>
  irule EQ_TRANS >> qexists_tac `(step_taint inst s next tn).t_imm` >>
  reverse conj_tac >- asm_rewrite_tac[] >>
  first_x_assum irule >> simp[] >> qexists_tac `id` >> simp[]
QED

Theorem frag_exec_ptr_straight_imm_frame:
  !cx ctx PG sa sb G tn s H u sf.
    dec_straight sa sb /\
    EVERY (\inst. !w w' t. (step_taint inst w w' t).t_imm = t.t_imm)
      (emitted_insts sa sb) /\
    frag_exec_ptr cx ctx PG sa sb
      (\g t w. g=G /\ t=tn /\ w=s)
      (\g t w. g=H /\ t=u /\ w=sf) (\gt r. F) /\
    ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    u.t_imm = tn.t_imm
Proof
  rpt strip_tac >>
  qabbrev_tac `bb = <|bb_label := sb.cs_current_bb;
    bb_instructions := sb.cs_current_insts ++ [mk_inst 0 SINK [] []]|>` >>
  qabbrev_tac `fn = (ARB:ir_function) with fn_blocks := [bb]` >>
  `fn_has_code sa sb fn` by
    (gvs[Abbr `fn`, Abbr `bb`, dec_straight_def, fn_has_code_def,
      emitted_blocks_def, lookup_block_def, FIND_def, INDEX_FIND_def,
      IS_PREFIX_APPEND]) >>
  qpat_x_assum `frag_exec_ptr _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[frag_exec_ptr_def] >>
  disch_then (qspecl_then [`fn`,`G`,`tn`,`s`] mp_tac) >> simp[] >> strip_tac >>
  `run_from 0 ctx fn sf = Halt (halt_state sf)` by
    (simp[Abbr `fn`, Abbr `bb`] >> irule synthetic_sink_endpoint >> simp[]) >>
  `ghost_run 0 ctx fn PG H u sf = (H,u)` by
    simp[ghost_run_def, Abbr `fn`, Abbr `bb`, lookup_block_def,
      FIND_def, INDEX_FIND_def, Once ghost_block_def, get_instruction_def,
      EL_APPEND_EQN, step_inst_non_invoke, step_inst_base_def, mk_inst_def] >>
  qpat_x_assum `!fuel. _` (qspec_then `0` mp_tac) >>
  simp[] >> strip_tac >>
  `DROP s.vs_inst_idx bb.bb_instructions =
    emitted_insts sa sb ++ [mk_inst 0 SINK [] []]` by
    (fs[dec_straight_def, inst_extends_def] >>
     simp[Abbr `bb`, Once inst_extends_def] >>
     qpat_x_assum `sb.cs_current_insts = _` (fn th =>
       CONV_TAC (LAND_CONV (ONCE_DEPTH_CONV (REWR_CONV th)))) >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> REFL_TAC) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb)` by fs[dec_straight_def] >>
  drule_all ghost_block_sink_imm >>
  disch_then (qspecl_then [`fuel'`,`ctx`,`fn`,`PG`,`G`,`tn`] mp_tac) >>
  `ghost_block fuel' ctx fn PG G tn bb s = (H,u)` by
    (qpat_x_assum `ghost_run fuel' _ _ _ _ _ _ = _` mp_tac >>
     simp[ghost_run_def, Abbr `fn`, lookup_block_def, Abbr `bb`,
       FIND_def, INDEX_FIND_def] >> fs[dec_straight_def]) >>
  asm_rewrite_tac[]
QED
