(* Interpret the recorded straight runs and taken branches at their own cursors. *)
Theory rawSlotChunksAdmin
Ancestors
  rawSlotCopyChunk rawSlotFetchExit rawSlotRunSpineOffExit rawCreateSlotEdges
  rawCreateAdminSpine venomExecSemantics venomInst venomState compileEnv
  instMemFrontier list relation

Theorem admin_slot_jump_spine_clear:
  ~s.vs_halted /\
  (s.vs_current_bb <> b.cs_current_bb \/
   s.vs_inst_idx <> LENGTH b.cs_current_insts) /\
  lookup_block s.vs_current_bb f.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  i.inst_id IN frag_ids a b /\
  (i.inst_opcode = JMP \/ i.inst_opcode = JNZ) /\
  step_inst_base i s = OK (jump_to lbl s) ==>
  admin_ok_spine a b E ctx f s (jump_to lbl s)
Proof
  strip_tac >>
  `gas_origin_edge T E ctx f s [] (OK (jump_to lbl s))` suffices_by
    (strip_tac >> irule admin_ok_spine_single >> simp[] >>
     qexistsl_tac [`bb`,`i`] >> simp[]) >>
  irule admin_slot_base_edge >> simp[] >>
  simp[is_terminator_def] >>
  conj_tac >> FIRST [irule below_frontier_no_ranges >> simp[],
                     qexists_tac `lbl` >> simp[]]
QED

Theorem slot_copy_chunk_admin:
  lookup_block b.cs_current_bb f.fn_blocks = SOME bb_exit /\
  get_instruction bb_exit (LENGTH b.cs_current_insts) = SOME i_exit /\
  i_exit.inst_id NOTIN frag_ids a b /\
  (!k. l <= k /\ k < h ==> k IN frag_ids a b) /\
  slot_copy_chunk l h ctx f s z ==>
  admin_ok_spine a b E ctx f s z
Proof
  disch_tac >>
  qpat_x_assum `(_ /\ _ /\ _ /\ _ /\ _)` strip_assume_tac >>
  `!p blk j. lookup_block p.vs_current_bb f.fn_blocks = SOME blk /\
    get_instruction blk p.vs_inst_idx = SOME j /\ j.inst_id IN frag_ids a b ==>
    (p.vs_current_bb <> b.cs_current_bb \/
     p.vs_inst_idx <> LENGTH b.cs_current_insts)` by
    (rpt gen_tac >> strip_tac >> metis_tac[slot_fetch_off_exit]) >>
  pop_assum $ mk_asm "clear" >>
  qpat_x_assum `slot_copy_chunk _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE[slot_copy_chunk_def]) >>
  `EVERY (\j. j.inst_id IN frag_ids a b /\
    j.inst_opcode <> INVOKE /\ j.inst_opcode <> GAS /\
    ~is_terminator j.inst_opcode) code` by fs[EVERY_MEM] >>
  `admin_ok_spine a b E ctx f s t` by
    (qpat_x_assum `t = u with vs_inst_idx := _` SUBST1_TAC >>
     irule admin_slot_run_spine_off_exit >> asm "clear" assume_tac >> simp[] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC,APPEND] >> metis_tac[]) >>
  `lookup_block t.vs_current_bb f.fn_blocks = SOME bb` by simp[] >>
  `i.inst_id IN frag_ids a b` by simp[] >>
  `t.vs_current_bb <> b.cs_current_bb \/ t.vs_inst_idx <> LENGTH b.cs_current_insts` by
    (asm "clear" (qspecl_then [`t`,`bb`,`i`] mp_tac) >> simp[]) >>
  `admin_ok_spine a b E ctx f t z` by
    (qpat_x_assum `z = jump_to _ _` SUBST1_TAC >>
     qpat_x_assum `t = u with vs_inst_idx := _` kall_tac >>
     irule admin_slot_jump_spine_clear >> simp[] >>
     qexists_tac `i` >> simp[]) >>
  irule admin_ok_spine_trans >> qexists_tac `t` >> simp[]
QED

Theorem slot_copy_chunks_admin:
  lookup_block b.cs_current_bb f.fn_blocks = SOME bb_exit /\
  get_instruction bb_exit (LENGTH b.cs_current_insts) = SOME i_exit /\
  i_exit.inst_id NOTIN frag_ids a b /\
  (!k. l <= k /\ k < h ==> k IN frag_ids a b) /\
  RTC (slot_copy_chunk l h ctx f) s z ==>
  admin_ok_spine a b E ctx f s z
Proof
  strip_tac >>
  `!p q. slot_copy_chunk l h ctx f p q ==> admin_ok_spine a b E ctx f p q` by
    (rpt strip_tac >> irule slot_copy_chunk_admin >>
     simp[] >> qexistsl_tac [`h`,`l`] >> simp[]) >>
  pop_assum $ mk_asm "one_chunk" >>
  qpat_x_assum `RTC _ _ _` mp_tac >>
  map_every qid_spec_tac [`z`,`s`] >>
  ho_match_mp_tac RTC_INDUCT >> simp[] >>
  rpt strip_tac >> asm "one_chunk" drule >> strip_tac >>
  irule admin_ok_spine_trans >> metis_tac[]
QED
