Theory dftPacketFreshChildOccurrence
Ancestors
  dftPacketNativeSlice dftPacketClosedRowNative dftGasFromListTraceDefs
  dftIndexedExec venomExecSemantics venomInst venomState list rich_list arithmetic

Theorem dft_packet_fresh_child_prefix_occurrence:
  !e d budget entry sf bb sp m s k C u b.
  e = SUC d /\ e <= budget /\
  lookup_block entry.vs_current_bb sf.fn_blocks = SOME bb /\
  eval_phis entry bb.bb_instructions = OK sp /\
  m = phi_prefix_length bb.bb_instructions /\
  s = (sp with vs_inst_idx := m) /\
  k < LENGTH (DROP m bb.bb_instructions) /\
  EVERY (\i. ~is_terminator i.inst_opcode)
    (TAKE k (DROP m bb.bb_instructions)) /\
  FOLDR (dft_exec_cons (budget-e) C) OK
    (TAKE k (DROP m bb.bb_instructions)) s = OK u ==>
  u.vs_inst_idx = m + k /\
  ?after. trace_blocks b d (budget-d) C sf entry =
    trace_block b e (budget-e) C sf
      (bb with bb_instructions := TAKE (m+k) bb.bb_instructions) s ++
    [((b,e,(EL k (DROP m bb.bb_instructions)).inst_id),sf,
      EL k (DROP m bb.bb_instructions),u)] ++ after
Proof
  rpt gen_tac >> strip_tac >>
  `s.vs_inst_idx = m /\ m + k < LENGTH bb.bb_instructions` by
    gvs[LENGTH_DROP] >>
  `s.vs_inst_idx + k <= LENGTH bb.bb_instructions` by decide_tac >>
  `EVERY (\i. ~is_terminator i.inst_opcode)
      (TAKE k (DROP s.vs_inst_idx bb.bb_instructions)) /\
   FOLDR (dft_exec_cons (budget-e) C) OK
      (TAKE k (DROP s.vs_inst_idx bb.bb_instructions)) s = OK u` by metis_tac[] >>
  drule_all native_trace_block_prefix_split >>
  disch_then (qspecl_then [`b`,`sf`,`e`] strip_assume_tac) >>
  `get_instruction bb u.vs_inst_idx = SOME (EL k (DROP m bb.bb_instructions))` by
    simp[get_instruction_def,EL_DROP] >>
  `budget-d = SUC (budget-e)` by decide_tac >>
  drule_all trace_blocks_enter >>
  disch_then (qspecl_then [`b`,`budget-e`,`d`,`C`] assume_tac) >>
  drule trace_block_visit >>
  disch_then (qspecl_then [`b`,`budget-e`,`sf`,`e`,`C`] assume_tac) >>
  qpat_x_assum `e = SUC d`
    (fn th => RULE_ASSUM_TAC (REWRITE_RULE [GSYM th])) >>
  gvs[] >> simp[APPEND_ASSOC]
QED

Theorem dft_packet_pseudo_prefix_trace_gas:
  EVERY (\i. is_pseudo i.inst_opcode) pre /\
  DROP s.vs_inst_idx bb.bb_instructions = pre ++ rest /\
  FOLDR (dft_exec_cons fuel C) OK pre s = OK t ==>
  trace_gas (trace_block b e fuel C sf bb s) =
    trace_gas (trace_block b e fuel C sf bb t)
Proof
  Cases_on `pre = []` >- gvs[] >>
  strip_tac >>
  `0 < LENGTH pre` by (Cases_on `pre` >> gvs[]) >>
  `s.vs_inst_idx + LENGTH pre <= LENGTH bb.bb_instructions` by
    (qpat_x_assum `DROP _ _ = _` (mp_tac o AP_TERM ``LENGTH:instruction list -> num``) >>
     simp[LENGTH_DROP]) >>
  `TAKE (LENGTH pre) (DROP s.vs_inst_idx bb.bb_instructions) = pre` by (simp[] >> (MATCH_ACCEPT_TAC rich_listTheory.TAKE_LENGTH_APPEND)) >>
  irule native_trace_block_pseudo_skip >>
  qexists_tac `LENGTH pre` >> simp[]
QED
