(* The straight-line parts of a slot unwrap, at their indexed endpoints. *)
Theory entryCreateSlotStraight
Ancestors
  fragGasOrigin frameGasEvents slotCopyExecution transientLockProps
  bufferAllocationExecution stmtReasonLitFragMemory fragExec exprLoweringProps
  emitHelperProps venomExecSemantics venomState venomInst
  relation arithmetic list rich_list words

Theorem slot_plain_origin_edge[local]:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  ~s.vs_halted /\ ~u.vs_halted /\ ~is_terminator i.inst_opcode /\
  i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
  step_inst_base i s = OK u ==>
  gas_origin_edge F explicit ctx fn s []
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >> simp[gas_origin_edge_def] >>
  qexists_tac `0` >> simp[step_inst_non_invoke, gas_events_step_plain]
QED

Theorem unwrap_alloc_cursor_walk:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id ALLOCA [Lit (n2w nb)] [root]) /\
  A s.vs_current_bb s.vs_inst_idx (mk_inst id ALLOCA [Lit (n2w nb)] [root]) /\
  ~s.vs_halted /\ u = update_var root d (buffer_allocation_fields s id nb) /\
  step_inst_base (mk_inst id ALLOCA [Lit (n2w nb)] [root]) s = OK u /\
  a = (u with vs_inst_idx := SUC s.vs_inst_idx) ==>
  RTC (\x y. ?b i. lookup_block x.vs_current_bb fn.fn_blocks = SOME b /\
      get_instruction b x.vs_inst_idx = SOME i /\
      A x.vs_current_bb x.vs_inst_idx i /\
      gas_origin_edge F explicit ctx fn x [] (OK y)) s a
Proof
  strip_tac >>
  `~u.vs_halted` by
    (simp[update_var_def, buffer_allocation_fields_def] >>
     CASE_TAC >> simp[]) >>
  irule RTC_SINGLE >> BETA_TAC >>
  qexistsl_tac [`bb`, `mk_inst id ALLOCA [Lit (n2w nb)] [root]`] >>
  asm_rewrite_tac[] >>
  irule slot_plain_origin_edge >> gvs[mk_inst_def, is_terminator_def]
QED

Theorem unwrap_single_slot_cursor_walk:
  (load = SLOAD \/ load = TLOAD) /\
  same_blocks sa sb /\ isPREFIX sa.cs_current_insts sb.cs_current_insts /\
  fn_has_code sa sb fn /\
  emitted_insts sa sb =
    [mk_inst id load [src] [out]; mk_inst (id+1) MSTORE [Var root;Var out] []] /\
  eval_operand src a = SOME key /\ root <> out /\ lookup_var root a = SOME addr /\
  ~a.vs_halted /\ a.vs_current_bb = sa.cs_current_bb /\
  a.vs_inst_idx = LENGTH sa.cs_current_insts /\
  A a.vs_current_bb a.vs_inst_idx (mk_inst id load [src] [out]) /\
  A a.vs_current_bb (SUC a.vs_inst_idx) (mk_inst (id+1) MSTORE [Var root;Var out] []) /\
  t = (mstore (w2n addr) (slot_copy_word load a key)
       (update_var out (slot_copy_word load a key) a)
         with vs_inst_idx := LENGTH sb.cs_current_insts) ==>
  RTC (\x y. ?b i. lookup_block x.vs_current_bb fn.fn_blocks = SOME b /\
      get_instruction b x.vs_inst_idx = SOME i /\
      A x.vs_current_bb x.vs_inst_idx i /\
      gas_origin_edge F explicit ctx fn x [] (OK y)) a t
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb` by
    fs[same_blocks_def, emitted_insts_def, prefix_drop_equiv] >>
  drule_all fn_has_code_code >> strip_tac >>
  qabbrev_tac `i = mk_inst id load [src] [out]` >>
  qabbrev_tac `j = mk_inst (id+1) MSTORE [Var root;Var out] []` >>
  `get_instruction bb a.vs_inst_idx = SOME i /\
   get_instruction bb (SUC a.vs_inst_idx) = SOME j` by
    (qpat_x_assum `isPREFIX _ (DROP _ _)`
       (strip_assume_tac o REWRITE_RULE[IS_PREFIX_APPEND]) >>
     `DROP a.vs_inst_idx bb.bb_instructions = i::j::l` by asm_rewrite_tac[APPEND] >>
     drule DROP_EQ_CONS >> strip_tac >>
     qpat_assum `DROP (SUC _) _ = _` (mp_tac o MATCH_MP DROP_EQ_CONS) >>
     simp[get_instruction_def]) >>
  qabbrev_tac `w = slot_copy_word load a key` >>
  qabbrev_tac `u = update_var out w a` >>
  qabbrev_tac `v = u with vs_inst_idx := SUC a.vs_inst_idx` >>
  `step_inst_base i a = OK u` by
    (qpat_x_assum `load = _ \/ load = _` strip_assume_tac >>
     simp[Abbr `i`, Abbr `u`, Abbr `w`, slot_copy_word_def, step_SLOAD, step_TLOAD]) >>
  `~u.vs_halted /\ ~v.vs_halted /\ v.vs_current_bb = a.vs_current_bb /\
   v.vs_inst_idx = SUC a.vs_inst_idx` by
    simp[Abbr `v`, Abbr `u`, update_var_def] >>
  `step_inst_base j v = OK (mstore (w2n addr) w v)` by
    (simp[Abbr `j`] >> irule step_MSTORE >>
     fs[Abbr `v`, Abbr `u`, eval_operand_def, lookup_var_def, update_var_def,
        finite_mapTheory.FLOOKUP_UPDATE]) >>
  `~(mstore (w2n addr) w v).vs_halted /\
   t = (mstore (w2n addr) w v with vs_inst_idx := SUC v.vs_inst_idx)` by
    simp[Abbr `v`, mstore_def, ADD1] >>
  `gas_origin_edge F explicit ctx fn a [] (OK v)` by
    (qunabbrev_tac `v` >> irule slot_plain_origin_edge >>
     qpat_x_assum `load = _ \/ load = _` strip_assume_tac >>
     gvs[Abbr `i`, mk_inst_def, is_terminator_def]) >>
  `gas_origin_edge F explicit ctx fn v [] (OK t)` by
    (qpat_assum `t = (mstore _ _ v with vs_inst_idx := _)` SUBST1_TAC >>
     irule slot_plain_origin_edge >>
     gvs[Abbr `j`, mk_inst_def, is_terminator_def]) >>
  irule RTC_TRANS >> qexists_tac `v` >> conj_tac
  >- (irule RTC_SINGLE >> BETA_TAC >> qexistsl_tac [`bb`, `i`] >>
      fs[Abbr `i`]) >>
  irule RTC_SINGLE >> BETA_TAC >> qexistsl_tac [`bb`, `j`] >>
  gvs[Abbr `j`]
QED
