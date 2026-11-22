Theory checkedPrefixCursor
Ancestors
  fragExec exprLoweringProps instIdxIndep ptrDiscipline unitTransformDefs list

(* The check on a successful-prefix state is independent of the cursor
   used to start the tail. *)
Theorem checked_prefix_tail_cursor:
  step_inst_base h s = OK v /\
  EVERY (\i. ~is_terminator i.inst_opcode) xs /\
  (ctx_has_dalloca ctx ==>
    !pre i post u. h::xs = pre ++ i::post /\
      run_inst_seq pre s = OK u ==> dalloca_no_wrap i u) ==>
  (ctx_has_dalloca ctx ==>
    !pre i post u. xs = pre ++ i::post /\
      run_inst_seq pre (v with vs_inst_idx := k) = OK u ==>
      dalloca_no_wrap i u)
Proof
  rpt strip_tac >>
  `EVERY (\i. ~is_terminator i.inst_opcode) pre` by fs[EVERY_APPEND] >>
  qpat_x_assum `run_inst_seq pre _ = OK u` mp_tac >>
  simp[run_inst_seq_inst_idx] >>
  Cases_on `run_inst_seq pre v` >> simp[exec_result_map_def] >>
  disch_then (SUBST1_TAC o SYM) >>
  rename1 `run_inst_seq pre v = OK r` >>
  qpat_assum `ctx_has_dalloca ctx ==> _` (mp_tac o UNDISCH) >>
  disch_then (qspecl_then [`h::pre`, `i`, `post`, `r`] mp_tac) >>
  simp[run_inst_seq_def, dalloca_no_wrap_def, eval_op_inst_idx]
QED
