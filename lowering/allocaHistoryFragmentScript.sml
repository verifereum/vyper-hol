(* A straight-line helper retains its raw cursor; use the actual code
   slice to recover allocation history at its normalized landing. *)
Theory allocaHistoryFragment
Ancestors
  allocaHistory exprLoweringProps instIdxIndep venomWf venomInst venomState
  venomExecSemantics venomMemDefs venomMemProofs list arithmetic

Theorem history_slice_head[local]:
  !xs p h tail. DROP p xs = h::tail ==>
    p < LENGTH xs /\ EL p xs = h /\ DROP (SUC p) xs = tail
Proof
  Induct >> Cases_on `p` >> simp[] >> metis_tac[]
QED

Theorem history_cursor_inv[local,simp]:
  alloca_inv (s with vs_inst_idx := p) <=> alloca_inv s
Proof
  simp[alloca_inv_def, allocas_non_overlapping_def, alloca_next_valid_def]
QED

Theorem history_seq_logical_cursor[local]:
  !insts func bb s rest t p.
    fn_inst_ids_distinct func /\ alloca_history func (s with vs_inst_idx := p) /\
    alloca_inv s /\ lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    DROP p bb.bb_instructions = insts ++ rest /\
    EVERY (\inst. ~is_terminator inst.inst_opcode) insts /\
    run_inst_seq insts s = OK t ==>
    alloca_history func (t with vs_inst_idx := p + LENGTH insts)
Proof
  Induct >- simp[run_inst_seq_def] >>
  rpt gen_tac >> strip_tac >>
  gvs[run_inst_seq_def, AllCaseEqs()] >>
  drule history_slice_head >> strip_tac >>
  `get_instruction bb p = SOME h` by simp[get_instruction_def] >>
  `step_inst_base h (s with vs_inst_idx := p) = OK (ss' with vs_inst_idx := p)` by
    simp[step_inst_inst_idx_indep, exec_result_map_def] >>
  `alloca_inv (s with vs_inst_idx := p)` by simp[] >>
  `lookup_block (s with vs_inst_idx := p).vs_current_bb func.fn_blocks = SOME bb`
    by simp[] >>
  `get_instruction bb (s with vs_inst_idx := p).vs_inst_idx = SOME h` by simp[] >>
  drule_all alloca_history_base_step >> simp[] >> strip_tac >>
  `alloca_inv ss'` by metis_tac[history_base_alloca_inv] >>
  `ss'.vs_current_bb = s.vs_current_bb` by metis_tac[history_base_control_flow] >>
  `alloca_history func (t with vs_inst_idx := SUC p + LENGTH insts)` suffices_by
    simp[ADD_CLAUSES] >>
  first_x_assum irule >> goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem alloca_history_run_inst_seq:
  !func bb s insts rest t.
    fn_inst_ids_distinct func /\ alloca_history func s /\ alloca_inv s /\
    lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    DROP s.vs_inst_idx bb.bb_instructions = insts ++ rest /\
    EVERY (\inst. ~is_terminator inst.inst_opcode) insts /\
    run_inst_seq insts s = OK t ==>
    alloca_history func
      (t with vs_inst_idx := s.vs_inst_idx + LENGTH insts)
Proof
  rpt gen_tac >> strip_tac >>
  irule history_seq_logical_cursor >> goal_assum (drule_at Any) >> simp[] >>
  qexistsl [`bb`, `rest`, `s`] >> simp[] >>
  gvs[alloca_history_def]
QED

val () =
  let val th = alloca_history_run_inst_seq
      val (oracles, axioms) = Tag.dest_tag (Thm.tag th)
  in if null axioms andalso null (Thm.hyp th) andalso
        List.all (fn name => name = "DISK_THM") oracles
     then print "ALLOCA_HISTORY_FRAGMENT_AUDIT OK\n"
     else raise Fail "allocation history fragment inherited admission"
  end;
