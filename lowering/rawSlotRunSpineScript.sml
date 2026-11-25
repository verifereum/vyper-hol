(* Straight-line administrative spines with an exit-fetch clearance rule. *)
Theory rawSlotRunSpine
Ancestors
  rawCreateSlotEdges rawCreateAdminSpine fragGasSeqAbort exprLoweringProps
  fragExecMem fragExec venomExecSemantics instIdxIndep checkedPrefixCursor
  list rich_list arithmetic

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
  Induct_on `code`
  >- simp[run_inst_seq_def]
  >> rpt gen_tac >> strip_tac
  >> drule instruction_prefix_cursor >> strip_tac
  >> Cases_on `step_inst_base h s`
  >> gvs[run_inst_seq_def,run_inst_seq_mem_ok_def]
  >> rename1 `step_inst_base h s = OK v`
  >> `step_inst 0 ctx h s = OK v` by simp[step_inst_non_invoke]
  >> `~v.vs_halted /\ v.vs_current_bb = s.vs_current_bb` by
       metis_tac[venomInstProofsTheory.step_preserves_halted,
                 venomInstProofsTheory.step_preserves_control_flow]
  >> `ctx_has_dalloca ctx ==> dalloca_no_wrap h s` by
       (strip_tac >> first_x_assum
          (qspecl_then [`[]`,`h`,`code`,`s`] mp_tac) >> simp[run_inst_seq_def])
  >> `gas_origin_edge T E ctx f s []
        (OK (v with vs_inst_idx := SUC s.vs_inst_idx))` by
       (irule admin_slot_base_edge >> simp[] >> qexistsl_tac [`bb`,`h`,`v`] >> simp[])
  >> `admin_ok_spine a b E ctx f s
        (v with vs_inst_idx := SUC s.vs_inst_idx)` by
       (irule admin_ok_spine_single >> simp[] >> qexistsl_tac [`bb`,`h`] >> simp[])
  >> `EVERY (\i. ~is_terminator i.inst_opcode) code` by fs[EVERY_MEM]
  >> `(ctx_has_dalloca ctx ==> !pre i post w. h::code = pre ++ i::post /\
        run_inst_seq pre s = OK w ==> dalloca_no_wrap i w)` by
       (rpt strip_tac >> first_assum irule >> simp[] >>
        qexistsl_tac [`post`,`pre`] >> simp[])
  >> `(ctx_has_dalloca ctx ==> !pre i post w. code = pre ++ i::post /\
        run_inst_seq pre (v with vs_inst_idx := SUC s.vs_inst_idx) = OK w ==>
        dalloca_no_wrap i w)` by
       (mp_tac (Q.INST [`h` |-> `h`,`s` |-> `s`,`xs` |-> `code`,
                        `k` |-> `SUC s.vs_inst_idx`] checked_prefix_tail_cursor) >>
        (impl_tac >- (pure_rewrite_tac [GSYM APPEND_ASSOC,APPEND] >>
                       rpt conj_tac >> first_assum ACCEPT_TAC)) >>
        pure_rewrite_tac [GSYM APPEND_ASSOC,APPEND] >> simp[])
  >> first_x_assum
       (qspecl_then [`v with vs_inst_idx := SUC s.vs_inst_idx`,
                     `u with vs_inst_idx := SUC s.vs_inst_idx`] mp_tac)
  >> simp[run_inst_seq_inst_idx,run_inst_seq_mem_ok_inst_idx,exec_result_map_def]
  >> impl_tac >- (pure_rewrite_tac[GSYM APPEND_ASSOC,APPEND] >> metis_tac[])
  >> strip_tac
  >> `LENGTH code + SUC s.vs_inst_idx = SUC (LENGTH code) + s.vs_inst_idx` by
       decide_tac
  >> pop_assum (SUBST_ALL_TAC) >> irule admin_ok_spine_trans
  >> qexists_tac `v with vs_inst_idx := SUC s.vs_inst_idx` >> simp[]
QED
