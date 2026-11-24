(* Straight-line administrative spines with an exit-fetch clearance rule. *)
Theory rawSlotRunSpine
Ancestors
  rawSlotRunSpineOffExit

Theorem admin_slot_run_spine_clear:
  (!p blk i.
    lookup_block p.vs_current_bb f.fn_blocks = SOME blk /\
    get_instruction blk p.vs_inst_idx = SOME i /\
    i.inst_id IN frag_ids a b ==>
      (p.vs_current_bb <> b.cs_current_bb /\
       p.vs_inst_idx <> LENGTH b.cs_current_insts)) ==>
  !code s u.
    ~s.vs_halted /\
    lookup_block s.vs_current_bb f.fn_blocks = SOME bb /\
    isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) /\
    EVERY (\i. i.inst_id IN frag_ids a b /\
      i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
      ~is_terminator i.inst_opcode) code /\
    run_inst_seq_mem_ok code s /\
    (!pre i post v. code = pre ++ i::post /\
      run_inst_seq pre s = OK v /\
      ctx_has_dalloca ctx ==> dalloca_no_wrap i v) /\
    run_inst_seq code s = OK u ==>
    admin_ok_spine a b E ctx f s
      (u with vs_inst_idx := s.vs_inst_idx + LENGTH code)
Proof
  rpt gen_tac >> strip_tac >>
  `!p blk i. lookup_block p.vs_current_bb f.fn_blocks = SOME blk /\
    get_instruction blk p.vs_inst_idx = SOME i /\
    i.inst_id IN frag_ids a b ==>
      (p.vs_current_bb <> b.cs_current_bb \/
       p.vs_inst_idx <> LENGTH b.cs_current_insts)` by
    (rpt strip_tac >> first_x_assum drule_all >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  irule admin_slot_run_spine_off_exit >> gvs[] >>
  rpt strip_tac >> first_x_assum drule_all >> simp[]
QED
