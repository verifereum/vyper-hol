Theory fragGasSeqAbort
Ancestors
  fragGasMode fragGasSeq fragGasSeqMem fragExec fragExecMem
  exprLoweringProps venomInst venomState list rich_list
  fragGasPath fragGasPathMem gasCount memSafeRun venomExecSemantics
  venomInstProofs arithmetic instIdxIndep

Theorem gas_marked_path_step:
  !memory ctx func s bb i u n r.
    ~s.vs_halted /\
    lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME i /\
    i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
    (memory ==> inst_mem_below_frontier i s /\ inst_dload_in_section i s) /\
    step_inst_base i s = OK u /\
    gas_marked_path memory ctx func
      (u with vs_inst_idx := SUC s.vs_inst_idx) n r ==>
    gas_marked_path memory ctx func s
      ((if i.inst_opcode = GAS then 1 else 0) + n) r
Proof
  Cases_on `memory` >> simp[gas_marked_path_def] >> rpt strip_tac
  >- (`gas_path_mem_edge ctx func s (if i.inst_opcode = GAS then 1 else 0)
         (OK (u with vs_inst_idx := SUC s.vs_inst_idx))` by
        (irule straight_line_mem_edge >> metis_tac[]) >>
      drule (cj 2 gas_path_mem_rules) >> disch_then drule >> simp[]) >>
  `gas_path_edge ctx func s (if i.inst_opcode = GAS then 1 else 0)
     (OK (u with vs_inst_idx := SUC s.vs_inst_idx))` by
    (irule tuple_straight_line_edge >> metis_tac[]) >>
  drule (cj 2 gas_path_rules) >> disch_then drule >> simp[]
QED

Theorem gas_marked_path_abort:
  !memory ctx func s bb i a t.
    ~s.vs_halted /\
    lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME i /\
    i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
    (memory ==> inst_mem_below_frontier i s /\ inst_dload_in_section i s) /\
    step_inst_base i s = Abort a t ==>
    gas_marked_path memory ctx func s
      (if i.inst_opcode = GAS then 1 else 0) (Abort a t)
Proof
  Cases_on `memory` >> simp[gas_marked_path_def] >> rpt strip_tac
  >- (irule (cj 3 gas_path_mem_rules) >> simp[exit_result_def] >>
      `step_inst 0 ctx i s = Abort a t` by simp[step_inst_non_invoke] >>
      simp[gas_path_mem_edge_def] >> qexists_tac `0` >>
      simp[gas_count_step_def, mem_safe_step_non_invoke, exit_result_def]) >>
  irule (cj 3 gas_path_rules) >> simp[exit_result_def] >>
  `step_inst 0 ctx i s = Abort a t` by simp[step_inst_non_invoke] >>
  simp[gas_path_edge_def] >> qexists_tac `0` >>
  simp[gas_count_step_def, exit_result_def]
QED

Theorem instruction_prefix_cursor:
  isPREFIX (i::code) (DROP k bb.bb_instructions) ==>
  get_instruction bb k = SOME i /\
  isPREFIX code (DROP (SUC k) bb.bb_instructions)
Proof
  strip_tac >>
  `?rest. DROP k bb.bb_instructions = i::rest /\ isPREFIX code rest` by
    (Cases_on `DROP k bb.bb_instructions` >> gvs[]) >>
  `k < LENGTH bb.bb_instructions` by
    (qpat_x_assum `DROP _ _ = _` (mp_tac o Q.AP_TERM `LENGTH`) >>
     simp[LENGTH_DROP]) >>
  `get_instruction bb k = SOME i` by
    (simp[get_instruction_def] >>
     qpat_x_assum `DROP _ _ = _` (mp_tac o Q.AP_TERM `HD`) >>
     simp[HD_DROP]) >>
  `DROP (SUC k) bb.bb_instructions = rest` by
    (qpat_x_assum `DROP _ _ = _` (mp_tac o Q.AP_TERM `DROP 1`) >>
     simp[DROP_DROP, ADD1]) >> simp[]
QED

(* A failing instruction ends the executed prefix. Reads in the unexecuted
   remainder do not contribute to its count. *)
Theorem run_inst_seq_abort_gas_path:
  !memory code s t a ctx func bb.
    ~s.vs_halted /\
    lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) code /\
    (memory ==> run_inst_seq_mem_ok code s) /\
    run_inst_seq code s = Abort a t ==>
    ?n j. gas_marked_path memory ctx func s n
      (Abort a (t with vs_inst_idx := j))
Proof
  Induct_on `code` >- simp[run_inst_seq_def] >>
  rpt gen_tac >> strip_tac >>
  drule instruction_prefix_cursor >> strip_tac >>
  Cases_on `step_inst_base h s` >>
  gvs[run_inst_seq_def, run_inst_seq_mem_ok_def]
  >- suspend "continue"
  >> suspend "abort"
QED
Resume run_inst_seq_abort_gas_path[continue]:
  rename1 `step_inst_base h s = OK u` >>
  `step_inst 0 ctx h s = OK u` by simp[step_inst_non_invoke] >>
  `~u.vs_halted /\ u.vs_current_bb = s.vs_current_bb` by
    metis_tac[step_preserves_halted, step_preserves_control_flow] >>
  `EVERY (\i. ~is_terminator i.inst_opcode) code` by fs[EVERY_MEM] >>
  first_x_assum (qspec_then `memory` mp_tac) >>
  disch_then (qspec_then `u with vs_inst_idx := SUC s.vs_inst_idx` mp_tac) >>
  disch_then (qspec_then `t with vs_inst_idx := SUC s.vs_inst_idx` mp_tac) >>
  simp[run_inst_seq_inst_idx, exec_result_map_def] >>
  disch_then (qspecl_then [`ctx`, `func`, `bb`] mp_tac) >>
  simp[] >> strip_tac >>
  qexistsl [`(if h.inst_opcode = GAS then 1 else 0) + n`, `j`] >>
  irule gas_marked_path_step >> metis_tac[]
QED
Resume run_inst_seq_abort_gas_path[abort]:
  qexistsl [`if h.inst_opcode = GAS then 1 else 0`, `t.vs_inst_idx`] >>
  simp[] >> irule gas_marked_path_abort >> metis_tac[]
QED
Finalise run_inst_seq_abort_gas_path

Theorem run_inst_seq_abort_zero_path:
  !code s t a ctx func bb.
    ~s.vs_halted /\
    lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) /\
    EVERY (\i. i.inst_opcode <> GAS /\ i.inst_opcode <> INVOKE /\
               ~is_terminator i.inst_opcode) code /\
    run_inst_seq code s = Abort a t ==>
    ?j. gas_marked_path F ctx func s 0
      (Abort a (t with vs_inst_idx := j))
Proof
  Induct_on `code` >- simp[run_inst_seq_def] >>
  rpt gen_tac >> strip_tac >>
  drule instruction_prefix_cursor >> strip_tac >>
  Cases_on `step_inst_base h s` >>
  gvs[run_inst_seq_def]
  >- (rename1 `step_inst_base h s = OK u` >>
      `step_inst 0 ctx h s = OK u` by simp[step_inst_non_invoke] >>
      `~u.vs_halted /\ u.vs_current_bb = s.vs_current_bb` by
        metis_tac[step_preserves_halted, step_preserves_control_flow] >>
      `EVERY (\i. ~is_terminator i.inst_opcode) code` by fs[EVERY_MEM] >>
      first_x_assum (qspec_then `u with vs_inst_idx := SUC s.vs_inst_idx` mp_tac) >>
      disch_then (qspec_then `t with vs_inst_idx := SUC s.vs_inst_idx` mp_tac) >>
      simp[run_inst_seq_inst_idx, exec_result_map_def] >>
      disch_then (qspecl_then [`ctx`, `func`, `bb`] mp_tac) >>
      simp[] >> strip_tac >> qexists_tac `j` >>
      drule_at (Pat `step_inst_base _ _ = OK _`) gas_marked_path_step >>
      simp[] >> disch_then irule >> metis_tac[]) >>
  qexists_tac `t.vs_inst_idx` >> simp[] >>
  drule gas_marked_path_abort >> simp[] >> metis_tac[]
QED
