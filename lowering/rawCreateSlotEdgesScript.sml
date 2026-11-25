(* Exact edge observations used during registered slot copies. *)
Theory rawCreateSlotEdges
Ancestors
  rawCreateAdminSpine fragGasOrigin gasEvents gasCount fragExecMem instMemFrontier
  fragExec memSafeRun unitTransformDefs ptrDiscipline venomExecSemantics
  venomExecProofs venomState venomInst checkedPrefixCursor instIdxIndep
  fragGasSeqAbort exprLoweringProps context compileEnv fragExec list rich_list arithmetic

Theorem admin_slot_base_edge:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb f.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
  inst_mem_below_frontier i s /\ inst_dload_in_section i s /\
  (ctx_has_dalloca ctx ==> dalloca_no_wrap i s) /\
  step_inst_base i s = OK u /\
  (if is_terminator i.inst_opcode then (?lbl. u = jump_to lbl s /\ t = u)
   else ~u.vs_halted /\ t = u with vs_inst_idx := SUC s.vs_inst_idx) ==>
  gas_origin_edge T E ctx f s [] (OK t)
Proof
  strip_tac >> rewrite_tac[gas_origin_edge_def] >> simp[] >>
  qexists_tac `0` >>
  simp[step_inst_non_invoke,gas_events_step_def,mem_safe_step_non_invoke] >>
  Cases_on `is_terminator i.inst_opcode` >> gvs[] >> metis_tac[]
QED

(* Preserve the cursor at each actual straight-line step. The block is not
   the loop exit block; the branch that eventually enters it is separate. *)
Theorem admin_slot_run_spine:
  !code s u.
    ~s.vs_halted /\ s.vs_current_bb <> b.cs_current_bb /\
    lookup_block s.vs_current_bb f.fn_blocks = SOME bb /\
    isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) /\
    EVERY (\i. i.inst_id IN frag_ids a b /\ i.inst_opcode <> INVOKE /\
       i.inst_opcode <> GAS /\ ~is_terminator i.inst_opcode) code /\
    run_inst_seq_mem_ok code s /\
    (!pre i post v. code = pre ++ i::post /\ run_inst_seq pre s = OK v /\
      ctx_has_dalloca ctx ==> dalloca_no_wrap i v) /\
    run_inst_seq code s = OK u ==>
    admin_ok_spine a b E ctx f s
      (u with vs_inst_idx := s.vs_inst_idx + LENGTH code)
Proof
  Induct >- simp[run_inst_seq_def] >>
  rpt gen_tac >> strip_tac >>
  drule instruction_prefix_cursor >> strip_tac >>
  Cases_on `step_inst_base h s` >> gvs[run_inst_seq_def,run_inst_seq_mem_ok_def] >>
  rename1 `step_inst_base h s = OK v` >>
  `step_inst 0 ctx h s = OK v` by simp[step_inst_non_invoke] >>
  `~v.vs_halted /\ v.vs_current_bb = s.vs_current_bb` by
    metis_tac[venomInstProofsTheory.step_preserves_halted,
              venomInstProofsTheory.step_preserves_control_flow] >>
  `ctx_has_dalloca ctx ==> dalloca_no_wrap h s` by
    (strip_tac >> first_x_assum (qspecl_then [`[]`,`h`,`code`,`s`] mp_tac) >>
     simp[run_inst_seq_def]) >>
  `gas_origin_edge T E ctx f s [] (OK (v with vs_inst_idx := SUC s.vs_inst_idx))` by
    (irule admin_slot_base_edge >> simp[] >> qexistsl_tac [`bb`,`h`,`v`] >> simp[]) >>
  `admin_ok_spine a b E ctx f s (v with vs_inst_idx := SUC s.vs_inst_idx)` by
    (irule admin_ok_spine_single >> simp[] >> qexistsl_tac [`bb`,`h`] >> simp[]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode) code` by fs[EVERY_MEM] >>
  `(ctx_has_dalloca ctx ==> !pre i post w. h::code = pre ++ i::post /\
    run_inst_seq pre s = OK w ==> dalloca_no_wrap i w)` by
      (rpt strip_tac >> first_assum irule >> simp[] >> qexistsl_tac [`post`,`pre`] >> simp[]) >>
  `(ctx_has_dalloca ctx ==> !pre i post w. code = pre ++ i::post /\
    run_inst_seq pre (v with vs_inst_idx := SUC s.vs_inst_idx) = OK w ==> dalloca_no_wrap i w)` by
    (mp_tac (Q.INST [`h` |-> `h`,`s` |-> `s`,`xs` |-> `code`,
                    `k` |-> `SUC s.vs_inst_idx`] checked_prefix_tail_cursor) >>
     (impl_tac >- (pure_rewrite_tac [GSYM APPEND_ASSOC,APPEND] >>
                   rpt conj_tac >> first_assum ACCEPT_TAC)) >>
     pure_rewrite_tac [GSYM APPEND_ASSOC,APPEND] >> simp[]) >>
  first_x_assum (qspecl_then [`v with vs_inst_idx := SUC s.vs_inst_idx`,
      `u with vs_inst_idx := SUC s.vs_inst_idx`] mp_tac) >>
  simp[run_inst_seq_inst_idx,run_inst_seq_mem_ok_inst_idx,exec_result_map_def] >>
  impl_tac >- (pure_rewrite_tac[GSYM APPEND_ASSOC,APPEND] >> metis_tac[]) >>
  strip_tac >>
  `LENGTH code + SUC s.vs_inst_idx = SUC (LENGTH code) + s.vs_inst_idx` by decide_tac >>
  pop_assum (SUBST_ALL_TAC) >> irule admin_ok_spine_trans >>
  qexists_tac `v with vs_inst_idx := SUC s.vs_inst_idx` >> simp[]
QED

Theorem admin_slot_jump_spine:
  ~s.vs_halted /\ s.vs_current_bb <> b.cs_current_bb /\
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

Theorem admin_slot_spine_from_exit:
  s.vs_current_bb = b.cs_current_bb /\
  s.vs_inst_idx = LENGTH b.cs_current_insts /\
  admin_ok_spine a b E ctx f s t ==> t = s
Proof
  rw[admin_ok_spine_def] >>
  qpat_x_assum `RTC _ _ _` (mp_tac o ONCE_REWRITE_RULE [relationTheory.RTC_CASES1]) >>
  simp[] >> metis_tac[]
QED

(* Diagnostic: a synthetic compiler state can reuse the loop's fresh exit
   label. fn_has_code and distinct instruction IDs alone do not exclude it. *)
Theorem slot_snapshot_layout_exit_alias[local]:
  let a = <| cs_next_var := 0; cs_next_label := 0; cs_next_id := 0;
             cs_current_bb := "@wcopy_exit_2"; cs_current_insts := [];
             cs_blocks := []; cs_data_sections := [] |> in
  let (buf,m) = compile_alloc_buffer 32 a in
  let (_,b) = compile_word_copy_loop (Lit 0w) buf.buf_operand 1 LocStorage LocMemory F m in
  let f = ARB with fn_blocks := emitted_blocks a b in
    fn_has_code a b f /\ fn_inst_ids_distinct f /\
    a.cs_current_bb = b.cs_current_bb /\ a.cs_current_insts = b.cs_current_insts
Proof
  EVAL_TAC >> simp[DISJ_IMP_THM,FORALL_AND_THM] >>
  CONV_TAC (RAND_CONV (REWR_CONV (GSYM ETA_THM))) >> simp[]
QED
