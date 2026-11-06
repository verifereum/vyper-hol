(* Memory-counted execution of the raw_revert suffix. *)
Theory bodyMemRawRevertSuffix
Ancestors
  bodyMemRawRevertBounds exprSimRawRevertCore fragGasSeqMem
  fragGasPathMem instMemFrontier memSafeRun fragExec gasCount
  exprLoweringProps emitHelperProps compileEnv venomExecSemantics
  venomInstProofs venomExecProps venomState venomInst finite_map list rich_list arithmetic
  words ASCIInumbers

Theorem raw_revert_three_mem_path[local]:
  ~t.vs_halted /\ lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb t.vs_inst_idx = SOME i1 /\
  get_instruction bb (SUC t.vs_inst_idx) = SOME i2 /\
  get_instruction bb (SUC (SUC t.vs_inst_idx)) = SOME i3 /\
  i1.inst_opcode = MLOAD /\ i2.inst_opcode = ADD /\ i3.inst_opcode = REVERT /\
  step_inst_base i1 t = OK t1 /\
  step_inst_base i2 (t1 with vs_inst_idx := SUC t.vs_inst_idx) = OK t2 /\
  step_inst_base i3 (t2 with vs_inst_idx := SUC (SUC t.vs_inst_idx)) = Abort a w /\
  inst_mem_below_frontier i1 t /\
  inst_mem_below_frontier i2 (t1 with vs_inst_idx := SUC t.vs_inst_idx) /\
  inst_mem_below_frontier i3 (t2 with vs_inst_idx := SUC (SUC t.vs_inst_idx)) ==>
  gas_path_mem ctx func t 0 (Abort a w)
Proof
  strip_tac >>
  `step_inst 0 ctx i1 t = OK t1 /\
   step_inst 0 ctx i2 (t1 with vs_inst_idx := SUC t.vs_inst_idx) = OK t2` by
    simp[step_inst_non_invoke] >>
  `~t1.vs_halted /\ t1.vs_current_bb = t.vs_current_bb` by
    metis_tac[step_preserves_halted, step_preserves_control_flow, is_terminator_def] >>
  `~t2.vs_halted /\ t2.vs_current_bb = t.vs_current_bb` by
    (drule_at (Pat `step_inst _ _ i2 _ = _`) step_preserves_halted >>
     drule_at (Pat `step_inst _ _ i2 _ = _`) step_preserves_control_flow >>
     simp[is_terminator_def]) >>
  `gas_path_mem_edge ctx func t 0
     (OK (t1 with vs_inst_idx := SUC t.vs_inst_idx))` by
    (qpat_assum `step_inst_base i1 t = _`
       (mp_then Any mp_tac straight_line_mem_edge) >>
     simp[is_terminator_def, inst_dload_in_section_other] >>
     disch_then irule >> metis_tac[]) >>
  `gas_path_mem_edge ctx func (t1 with vs_inst_idx := SUC t.vs_inst_idx) 0
     (OK (t2 with vs_inst_idx := SUC (SUC t.vs_inst_idx)))` by
    (qpat_assum `step_inst_base i2 _ = _`
       (mp_then Any mp_tac straight_line_mem_edge) >>
     simp[is_terminator_def, inst_dload_in_section_other] >>
     disch_then irule >> metis_tac[]) >>
  `gas_path_mem_edge ctx func (t2 with vs_inst_idx := SUC (SUC t.vs_inst_idx)) 0
     (Abort a w)` by
    (simp[gas_path_mem_edge_def] >> qexists_tac `0` >>
     simp[step_inst_non_invoke, gas_count_step_def, mem_safe_step_non_invoke,
          inst_dload_in_section_other, exit_result_def] >> metis_tac[]) >>
  `gas_path_mem ctx func (t2 with vs_inst_idx := SUC (SUC t.vs_inst_idx)) 0
     (Abort a w)` by (irule (cj 3 gas_path_mem_rules) >> simp[exit_result_def]) >>
  metis_tac[cj 2 gas_path_mem_rules, ADD_CLAUSES]
QED

Theorem raw_revert_mem_layout[local]:
  compile_raw_revert data sm = (u,sb) /\ fn_has_code sm sb func /\
  (!v. data = Var v ==> not_fresh_at sm v) /\
  t.vs_current_bb = sm.cs_current_bb /\
  t.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?bb x y. lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
    data <> Var x /\ x <> y /\
    get_instruction bb t.vs_inst_idx =
      SOME (mk_inst sm.cs_next_id MLOAD [data] [x]) /\
    get_instruction bb (SUC t.vs_inst_idx) =
      SOME (mk_inst (sm.cs_next_id + 1) ADD [data; Lit 32w] [y]) /\
    get_instruction bb (SUC (SUC t.vs_inst_idx)) =
      SOME (mk_inst (sm.cs_next_id + 2) REVERT [Var y; Var x] [])
Proof
  strip_tac >> drule raw_revert_tail_layout >> strip_tac >>
  qmatch_asmsub_abbrev_tac `sb.cs_current_insts = sm.cs_current_insts ++ new` >>
  `?bb. lookup_block sm.cs_current_bb func.fn_blocks = SOME bb /\
    !i. i < LENGTH new ==>
      get_instruction bb (LENGTH sm.cs_current_insts + i) = SOME (EL i new)` by
    (irule fn_has_code_same_block >> qexists_tac `sb` >>
     gvs[same_blocks_def]) >>
  qexistsl_tac [`bb`, `STRING #"%" (toString sm.cs_next_var)`,
    `STRING #"%" (toString (sm.cs_next_var + 1))`] >>
  simp[ASCIInumbersTheory.toString_11] >>
  conj_tac
  >- (strip_tac >>
      `not_fresh_at sm (STRING #"%" (toString sm.cs_next_var))` by metis_tac[] >>
      fs[not_fresh_at_def] >> metis_tac[LESS_EQ_REFL]) >>
  rpt conj_tac
  >- (first_x_assum (qspec_then `0` mp_tac) >> simp[Abbr `new`])
  >- (first_x_assum (qspec_then `1` mp_tac) >> simp[Abbr `new`, ADD1]) >>
  first_x_assum (qspec_then `2` mp_tac) >> simp[Abbr `new`, ADD1]
QED

Theorem raw_revert_mem_steps[local]:
  data <> Var x /\ x <> y /\ eval_operand data t = SOME p /\
  mload (w2n p) t = n2w n /\ n < dimword (:256) /\
  w2n p + 32 <= t.vs_alloca_next /\
  w2n (p + 32w) + n <= t.vs_alloca_next ==>
  ?t1 t2 w.
    step_inst_base (mk_inst id MLOAD [data] [x]) t = OK t1 /\
    step_inst_base (mk_inst (id+1) ADD [data; Lit 32w] [y])
      (t1 with vs_inst_idx := SUC t.vs_inst_idx) = OK t2 /\
    step_inst_base (mk_inst (id+2) REVERT [Var y; Var x] [])
      (t2 with vs_inst_idx := SUC (SUC t.vs_inst_idx)) = Abort Revert_abort w /\
    inst_mem_below_frontier (mk_inst id MLOAD [data] [x]) t /\
    inst_mem_below_frontier (mk_inst (id+1) ADD [data; Lit 32w] [y])
      (t1 with vs_inst_idx := SUC t.vs_inst_idx) /\
    inst_mem_below_frontier (mk_inst (id+2) REVERT [Var y; Var x] [])
      (t2 with vs_inst_idx := SUC (SUC t.vs_inst_idx))
Proof
  strip_tac >>
  qabbrev_tac `t1 = update_var x (n2w n) t` >>
  qabbrev_tac `s1 = t1 with vs_inst_idx := SUC t.vs_inst_idx` >>
  `eval_operand data s1 = SOME p` by
    (Cases_on `data` >>
     gvs[Abbr `s1`, Abbr `t1`, eval_operand_def, lookup_var_def,
         update_var_def, FLOOKUP_UPDATE]) >>
  qexistsl_tac [`t1`, `update_var y (p + 32w) s1`] >>
  `step_inst_base (mk_inst id MLOAD [data] [x]) t = OK t1` by
    (qpat_assum `eval_operand data t = _`
       (mp_then Any mp_tac step_MLOAD) >> simp[Abbr `t1`]) >>
  `step_inst_base (mk_inst (id+1) ADD [data; Lit 32w] [y]) s1 =
    OK (update_var y (p + 32w) s1)` by
    (irule step_ADD >> simp[eval_operand_def]) >>
  fs[Abbr `s1`] >>
  irule_at Any (REWRITE_RULE [GSYM mk_inst_def] step_revert_behavior) >>
  simp[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE,
       Abbr `t1`] >>
  simp[below_frontier_MLOAD, below_frontier_REVERT,
       below_frontier_no_ranges, mk_inst_def, eval_operand_def,
       lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED

Theorem raw_revert_tail_path_mem:
  compile_raw_revert data sm = (u,sb) /\ fn_has_code sm sb func /\
  (!v. data = Var v ==> not_fresh_at sm v) /\
  eval_operand data t = SOME p /\ ~t.vs_halted /\
  t.vs_current_bb = sm.cs_current_bb /\
  t.vs_inst_idx = LENGTH sm.cs_current_insts /\
  mload (w2n p) t = n2w n /\ n < dimword (:256) /\
  w2n p + 32 <= t.vs_alloca_next /\
  w2n (p + 32w) + n <= t.vs_alloca_next ==>
  ?w. gas_path_mem ctx func t 0 (Abort Revert_abort w)
Proof
  strip_tac >> drule_all raw_revert_mem_layout >> strip_tac >>
  drule_all raw_revert_mem_steps >>
  disch_then (qspec_then `sm.cs_next_id` strip_assume_tac) >>
  qexists_tac `w` >> irule raw_revert_three_mem_path >>
  rpt (goal_assum (drule_at Any)) >> gvs[mk_inst_def]
QED
