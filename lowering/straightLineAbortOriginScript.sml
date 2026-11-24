(* Peel a checked abort path along a concrete successful base run up to
   its final instruction. The base run omits cursor updates. *)
Theory straightLineAbortOrigin
Ancestors
  fragGasOriginPtr fragGasSeqAbort fragExec instIdxIndep
  exprLoweringProps venomExecSemantics venomState venomInst
  list rich_list arithmetic

Theorem origin_ptr_edge_straight_line[local]:
  gas_origin_ptr_edge (D,lo,E,C,f,PG) (s,G,tn) ms (r,H,tf) /\
  lookup_block s.vs_current_bb f.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode ==>
  ~s.vs_halted /\
  ((?v. step_inst_base i s = OK v /\
        r = OK (v with vs_inst_idx := SUC s.vs_inst_idx)) \/
   (exit_result r /\ step_inst_base i s = r))
Proof
  strip_tac >> drule gas_origin_ptr_edge_common_fuel >>
  simp[step_inst_non_invoke] >> metis_tac[]
QED

Theorem straight_line_abort_origin:
  !pre s G tn raw i a t bb.
    EVERY (\j. j.inst_opcode <> INVOKE /\ ~is_terminator j.inst_opcode) (pre ++ [i]) /\
    lookup_block s.vs_current_bb f.fn_blocks = SOME bb /\
    isPREFIX (pre ++ [i]) (DROP s.vs_inst_idx bb.bb_instructions) /\
    run_inst_seq pre s = OK raw /\
    (?v. step_inst_base i (raw with vs_inst_idx := s.vs_inst_idx + LENGTH pre) = Abort a v) /\
    gas_origin_ptr_path (D,lo,E,C,f,PG) (s,G,tn) [] (Abort a t,H,tf) ==>
    let mid = raw with vs_inst_idx := s.vs_inst_idx + LENGTH pre in
    ~mid.vs_halted /\ lookup_block mid.vs_current_bb f.fn_blocks = SOME bb /\
    get_instruction bb mid.vs_inst_idx = SOME i /\
    step_inst_base i mid = Abort a t /\
    ?K tk. gas_origin_ptr_path (D,lo,E,C,f,PG) (s,G,tn) [] (OK mid,K,tk) /\
           gas_origin_ptr_edge (D,lo,E,C,f,PG) (mid,K,tk) [] (Abort a t,H,tf)
Proof
  Induct_on `pre` >> rpt gen_tac >>
  pure_rewrite_tac[APPEND, LENGTH, EVERY_DEF, run_inst_seq_def, ADD_CLAUSES, LET_THM] >>
  strip_tac >>
  drule instruction_prefix_cursor >> strip_tac
  >- (gvs[] >> qpat_x_assum `gas_origin_ptr_path _ _ _ _` mp_tac >>
      simp[Once gas_origin_ptr_path_cases, exit_result_def] >> strip_tac
      >- (drule_all origin_ptr_edge_straight_line >> simp[exit_result_def]) >>
      drule_all origin_ptr_edge_straight_line >> simp[exit_result_def] >>
      strip_tac >> qexistsl [`G`,`tn`] >> simp[gas_origin_ptr_path_rules]) >>
  Cases_on `step_inst_base h s` >> gvs[] >>
  rename1 `step_inst_base h s = OK u` >>
  qpat_x_assum `gas_origin_ptr_path _ _ _ _` mp_tac >>
  simp[Once gas_origin_ptr_path_cases, exit_result_def] >> strip_tac
  >- (drule_all origin_ptr_edge_straight_line >> simp[exit_result_def] >>
      strip_tac >> gvs[] >>
      `step_inst 0 C h s = OK u` by simp[step_inst_non_invoke] >>
      `u.vs_current_bb = s.vs_current_bb` by metis_tac[venomInstProofsTheory.step_preserves_control_flow] >>
      `EVERY (\j. ~is_terminator j.inst_opcode) pre` by fs[EVERY_MEM] >>
      qabbrev_tac `m = u with vs_inst_idx := SUC s.vs_inst_idx` >>
      `run_inst_seq pre m = OK (raw with vs_inst_idx := SUC s.vs_inst_idx)` by
        simp[Abbr `m`, run_inst_seq_inst_idx, exec_result_map_def] >>
      first_x_assum (drule_at (Pat `run_inst_seq _ m = _`)) >>
      simp[Abbr `m`, ADD_CLAUSES, PULL_EXISTS] >>
      disch_then (drule_at (Pat `gas_origin_ptr_path _ _ _ _`)) >>
      simp[] >> disch_then (drule_at (Pat `step_inst_base _ _ = _`)) >>
      simp[] >> disch_then (qx_choosel_then [`J`,`tj`] strip_assume_tac) >>
      qexistsl [`J`,`tj`] >> simp[] >>
      drule (cj 2 gas_origin_ptr_path_rules) >> simp[] >> metis_tac[]) >>
  drule_all origin_ptr_edge_straight_line >> simp[exit_result_def]
QED
