Theory dftPacketPrefixVisitState
Ancestors
  dftPacketNativeSlice dftGasFromListTraceDefs dftIndexedExec
  rich_list list venomInst venomState

Theorem dft_packet_prefix_visit_state:
  ys = DROP be.vs_inst_idx bt.bb_instructions /\
  TAKE j R = TAKE hbe R ++ trace_block a e n C tf
    (bt with bb_instructions := TAKE (be.vs_inst_idx + ct) bt.bb_instructions) be /\
  ct <= LENGTH ys /\
  EVERY (\x. ~is_terminator x.inst_opcode) (TAKE ct ys) /\
  i < ct /\
  FOLDR (dft_exec_cons n C) OK (TAKE i ys) be = OK u ==>
  MEM ((a,e,(EL i ys).inst_id),tf,EL i ys,u) (TAKE j R)
Proof
  strip_tac >>
  qabbrev_tac `cut = bt with bb_instructions :=
    TAKE (be.vs_inst_idx + ct) bt.bb_instructions` >>
  `be.vs_inst_idx + ct <= LENGTH bt.bb_instructions` by
    (qpat_x_assum `ct <= LENGTH ys` mp_tac >> simp[LENGTH_DROP] >> decide_tac) >>
  `DROP be.vs_inst_idx cut.bb_instructions = TAKE ct ys` by
    simp[Abbr `cut`, DROP_TAKE] >>
  `LENGTH cut.bb_instructions = be.vs_inst_idx + ct` by
    simp[Abbr `cut`, LENGTH_TAKE] >>
  `TAKE i (DROP be.vs_inst_idx cut.bb_instructions) = TAKE i ys` by
    simp[TAKE_TAKE_T] >>
  `i <= ct` by decide_tac >>
  `EVERY (\x. ~is_terminator x.inst_opcode) (TAKE i ys)` by
    metis_tac[EVERY_TAKE, TAKE_TAKE_T] >>
  `be.vs_inst_idx + i <= LENGTH cut.bb_instructions /\
   EVERY (\x. ~is_terminator x.inst_opcode)
     (TAKE i (DROP be.vs_inst_idx cut.bb_instructions)) /\
   FOLDR (dft_exec_cons n C) OK
     (TAKE i (DROP be.vs_inst_idx cut.bb_instructions)) be = OK u` by
    gvs[] >>
  drule_all native_trace_block_prefix_split >>
  disch_then (qspecl_then [`a`,`tf`,`e`] strip_assume_tac) >>
  `get_instruction cut u.vs_inst_idx = SOME (EL i ys)` by
    simp[get_instruction_def, Abbr `cut`, EL_TAKE, listTheory.EL_DROP,
      arithmeticTheory.ADD_COMM] >>
  `?rest. trace_block a e n C tf cut u =
     ((a,e,(EL i ys).inst_id),tf,EL i ys,u)::rest` by
    (drule trace_block_visit >> simp[]) >>
  qpat_x_assum `TAKE j R = _` SUBST1_TAC >> simp[]
QED
