(* The EQ step and invariant at the header of a counted storage copy. *)
Theory fragGasStorageCopyHeaderProps
Ancestors
  exprSimPtrTopLevelStorageCopy exprSimStorageCopy fragGasSeqPtrContext fragGasSeqAbort
  fragGasSeqPtr exprLoweringProps ptrDiscipline ptrDisciplineTaintProps memLocDefs
  ptrSafeRun memSafeRun instMemFrontier fragExecMem fragExec codegenRel contextCodegenRel
  venomExecProofs venomExecSemantics venomState venomInst
  arithmetic words list finite_map

Theorem storage_copy_header_ptr_run:
  toplevel_copy_inv cv ds dst src loc a b n s0 G0 tn0 k G tn s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ allocas_from lo s /\ ~s.vs_halted /\
  cv <> tv /\ dst <> tv /\ (!x. src = Var x ==> x <> tv) /\ MEM tv ds /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX [mk_inst id EQ [Var cv;Lit (n2w n)] [tv];
            mk_inst (id+1) JNZ [Var tv;Label exit_lbl;Label body_lbl] []]
    (DROP s.vs_inst_idx bb.bb_instructions) ==>
  !D PG. ?u t G1 tn1.
    t = u with vs_inst_idx := s.vs_inst_idx + LENGTH [mk_inst id EQ [Var cv;Lit (n2w n)] [tv]] /\
    isPREFIX [mk_inst id EQ [Var cv;Lit (n2w n)] [tv]] (DROP s.vs_inst_idx bb.bb_instructions) /\
    get_instruction bb s.vs_inst_idx = SOME (mk_inst id EQ [Var cv;Lit (n2w n)] [tv]) /\
    get_instruction bb (SUC s.vs_inst_idx) = SOME (mk_inst (id+1) JNZ [Var tv;Label exit_lbl;Label body_lbl] []) /\
    run_inst_seq_mem_ok [mk_inst id EQ [Var cv;Lit (n2w n)] [tv]] s /\
    inst_seq_ptr D 0 ctx func PG G tn [mk_inst id EQ [Var cv;Lit (n2w n)] [tv]] s G1 tn1 /\
    run_inst_seq [mk_inst id EQ [Var cv;Lit (n2w n)] [tv]] s = OK u /\
    step_inst_base (mk_inst id EQ [Var cv;Lit (n2w n)] [tv]) s = OK u /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
                i.inst_opcode <> ALLOCA /\ i.inst_opcode <> GAS)
      [mk_inst id EQ [Var cv;Lit (n2w n)] [tv]] /\
    toplevel_copy_inv cv ds dst src loc a b n s0 G0 tn0 k G1 tn1 t /\
    op_taint tn1 (Var tv) = {} /\
    ~t.vs_halted /\ t.vs_current_bb = s.vs_current_bb /\
    t.vs_inst_idx = SUC s.vs_inst_idx /\ allocas_from lo t /\
    lookup_var tv t = SOME (bool_to_word (k=n)) /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp t)
Proof
  rpt strip_tac >>
  drule toplevel_copy_inv_bounds >> strip_tac >>
  drule toplevel_copy_inv_counter_value >> strip_tac >>
  drule toplevel_copy_inv_counter >> strip_tac >>
  `((n2w k):256 word = n2w n) <=> k=n` by
    (`k < 2**256` by decide_tac >>
     pure_rewrite_tac[n2w_11, dimword_def] >> gvs[LESS_MOD]) >>
  `step_inst_base (mk_inst id EQ [Var cv;Lit (n2w n)] [tv]) s =
     OK (update_var tv (bool_to_word (k=n)) s)` by
    simp[step_inst_base_def, exec_pure2_def, mk_inst_def,
         eval_operands_def, eval_operand_def] >>
  `taint_ok func tn (mk_inst id EQ [Var cv;Lit (n2w n)] [tv]) s` by
    (irule taint_ok_clean_step >>
     simp[mk_inst_def, source_memory_read_ranges_def, mem_read_ops_def, op_taint_def] >>
     fs[op_taint_def]) >>
  `ptr_inst_ok D 0 0 ctx func G tn
     (mk_inst id EQ [Var cv;Lit (n2w n)] [tv]) s` by
    (simp[ptr_inst_ok_def] >>
     simp[access_ok_def, allocas_from_def, mk_inst_def,
          source_memory_write_ranges_def, source_memory_read_ranges_def] >>
     simp[GSYM mk_inst_def, step_inst_non_invoke, update_var_def]) >>
  `run_inst_seq_mem_ok [mk_inst id EQ [Var cv;Lit (n2w n)] [tv]] s` by
    (simp[run_inst_seq_mem_ok_last, inst_dload_in_section_def, mk_inst_def] >>
     irule below_frontier_no_ranges >> simp[]) >>
  drule instruction_prefix_cursor >> strip_tac >>
  drule instruction_prefix_cursor >> strip_tac >>
  `isPREFIX [mk_inst id EQ [Var cv;Lit (n2w n)] [tv]]
     (DROP s.vs_inst_idx bb.bb_instructions)` by
    (qpat_x_assum `isPREFIX (_::_::_) _` mp_tac >>
     Cases_on `DROP s.vs_inst_idx bb.bb_instructions` >> simp[]) >>
  qabbrev_tac `i0 = mk_inst id EQ [Var cv;Lit (n2w n)] [tv]` >>
  qabbrev_tac `u = update_var tv (bool_to_word (k=n)) s` >>
  qabbrev_tac `G1 = step_prov PG G i0 u` >>
  qabbrev_tac `tn1 = step_taint i0 s u tn` >>
  `inst_seq_ptr D 0 ctx func PG G tn [i0] s G1 tn1` by
    simp[inst_seq_ptr_def, Abbr `G1`, Abbr `tn1`] >>
  `run_inst_seq [i0] s = OK u` by simp[run_inst_seq_def] >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
              i.inst_opcode <> ALLOCA /\ i.inst_opcode <> GAS) [i0]` by
    simp[Abbr `i0`, mk_inst_def, is_terminator_def] >>
  qabbrev_tac `t = u with vs_inst_idx := s.vs_inst_idx + LENGTH [i0]` >>
  `toplevel_copy_inv cv ds dst src loc a b n s0 G0 tn0 k G1 tn1 t` by
    (simp[Abbr `t`, Abbr `G1`, Abbr `tn1`, Abbr `u`, Abbr `i0`] >>
     irule toplevel_copy_test_inv >> simp[] >> metis_tac[]) >>
  `op_taint tn1 (Var tv) = {}` by
    simp[Abbr `tn1`, Abbr `i0`, step_taint_def, set_var_taint_def, out_taint_def,
         mk_inst_def, op_taint_def, FLOOKUP_UPDATE, eval_operand_def] >>
  `~t.vs_halted /\ t.vs_current_bb = s.vs_current_bb /\
    t.vs_inst_idx = SUC s.vs_inst_idx /\ allocas_from lo t /\
    lookup_var tv t = SOME (bool_to_word (k=n))` by
    (simp[Abbr `t`, Abbr `u`, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
     gvs[allocas_from_def, allocas_below_fmp_def, update_var_def] >> metis_tac[]) >>
  `(ctx_has_dalloca ctx ==> allocas_below_fmp t)` by
    (gvs[Abbr `t`, Abbr `u`, update_var_def, allocas_below_fmp_def] >> metis_tac[]) >>
  qexistsl_tac [`u`, `t`, `G1`, `tn1`] >>
  conj_tac >- simp[Abbr `t`] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED
