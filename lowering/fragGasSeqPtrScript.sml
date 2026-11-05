(* Straight-line instruction runs as counted pointer-checked paths: the
 * twins of fragGasSeq's and fragGasSeqMem's successful runs and of
 * fragGasSeqAbort's aborting ones, with the ghost carried past each
 * instruction as ghost_step carries it.
 *
 * TOP-LEVEL:
 *   inst_seq_ptr -- the pointer check along a straight-line run, and the
 *     ghost where the run stops
 *   gas_path_ptr_ok_suffix, gas_path_ptr_ok_not_halted -- what a path
 *     that goes on says of its end state
 *   straight_line_ptr_edge, gas_path_ptr_step, gas_path_ptr_abort -- one
 *     straight-line instruction
 *   run_inst_seq_gas_path_ptr, run_inst_seq_abort_gas_path_ptr -- a
 *     checked straight-line run that succeeds, or aborts, is a path
 *)
Theory fragGasSeqPtr
Ancestors
  fragGasPathPtr fragGasSeqAbort fragGasPath fragExec gasCount ptrSafeRun
  exprLoweringProps instIdxIndep venomExecSemantics venomInstProofs
  venomInst venomState list rich_list arithmetic

(* The pointer check along a straight-line run from s with the ghost
   (G, tn): each instruction the run executes passes ptr_inst_ok in the
   state the counted path reaches it in (the index past the instructions
   before it), and (G', tn') is the ghost where the run stops: past the
   last instruction, or at the one that fails. *)
Definition inst_seq_ptr_def:
  (inst_seq_ptr D lo ctx fn PG G tn [] s G' tn' <=> G' = G /\ tn' = tn) /\
  (inst_seq_ptr D lo ctx fn PG G tn (i::is) s G' tn' <=>
     ptr_inst_ok D lo 0 ctx fn G tn i s /\
     case step_inst_base i s of
       OK u =>
         inst_seq_ptr D lo ctx fn PG (step_prov PG G i u)
           (step_taint i s u tn) is
           (u with vs_inst_idx := SUC s.vs_inst_idx) G' tn'
     | _ => G' = G /\ tn' = tn)
End

Theorem gas_path_ptr_ok_suffix:
  gas_path_ptr D lo ctx fn PG G tn s n G' tn' (OK t) ==>
  t.vs_gas_readings = DROP n s.vs_gas_readings
Proof
  strip_tac >> drule gas_path_ptr_erase >> strip_tac >>
  drule gas_path_suffix >> simp[gas_count_suffix_def]
QED

Theorem gas_path_ptr_ok_not_halted:
  gas_path_ptr D lo ctx fn PG G tn s n G' tn' (OK t) ==> ~t.vs_halted
Proof
  metis_tac[gas_path_ptr_erase, gas_path_normal]
QED

Theorem straight_line_ptr_edge:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
  ptr_inst_ok D lo 0 ctx fn G tn i s /\
  step_inst_base i s = OK u ==>
  gas_path_ptr_edge D lo ctx fn PG G tn s
    (if i.inst_opcode = GAS then 1 else 0)
    (step_prov PG G i u) (step_taint i s u tn)
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >>
  `step_inst 0 ctx i s = OK u` by simp[step_inst_non_invoke] >>
  `~u.vs_halted` by metis_tac[step_preserves_halted] >>
  asm_rewrite_tac[gas_path_ptr_edge_def] >>
  qexistsl_tac [`0`, `bb`, `i`, `OK u`] >>
  simp[gas_count_step_def, ptr_safe_step_def, ghost_step_non_invoke]
QED

Theorem gas_path_ptr_step:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
  ptr_inst_ok D lo 0 ctx fn G tn i s /\
  step_inst_base i s = OK u /\
  gas_path_ptr D lo ctx fn PG (step_prov PG G i u) (step_taint i s u tn)
    (u with vs_inst_idx := SUC s.vs_inst_idx) n G' tn' r ==>
  gas_path_ptr D lo ctx fn PG G tn s
    ((if i.inst_opcode = GAS then 1 else 0) + n) G' tn' r
Proof
  strip_tac >>
  `gas_path_ptr_edge D lo ctx fn PG G tn s
     (if i.inst_opcode = GAS then 1 else 0)
     (step_prov PG G i u) (step_taint i s u tn)
     (OK (u with vs_inst_idx := SUC s.vs_inst_idx))` by
    metis_tac[straight_line_ptr_edge] >>
  drule (cj 2 gas_path_ptr_rules) >> disch_then drule >> simp[]
QED

Theorem gas_path_ptr_abort:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
  ptr_inst_ok D lo 0 ctx fn G tn i s /\
  step_inst_base i s = Abort a t ==>
  gas_path_ptr D lo ctx fn PG G tn s
    (if i.inst_opcode = GAS then 1 else 0) G tn (Abort a t)
Proof
  strip_tac >> irule (cj 3 gas_path_ptr_rules) >> simp[exit_result_def] >>
  `step_inst 0 ctx i s = Abort a t` by simp[step_inst_non_invoke] >>
  asm_rewrite_tac[gas_path_ptr_edge_def] >>
  qexistsl_tac [`0`, `bb`, `i`, `Abort a t`] >>
  simp[gas_count_step_def, ptr_safe_step_def, exit_result_def]
QED

Theorem run_inst_seq_gas_path_ptr:
  !code s t G tn G' tn' ctx fn bb.
    ~s.vs_halted /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) code /\
    inst_seq_ptr D lo ctx fn PG G tn code s G' tn' /\
    run_inst_seq code s = OK t ==>
    gas_path_ptr D lo ctx fn PG G tn s
      (LENGTH (FILTER (\i. i.inst_opcode = GAS) code)) G' tn'
      (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH code))
Proof
  Induct
  >- (simp[run_inst_seq_def, inst_seq_ptr_def] >> rpt strip_tac >>
      gvs[] >> irule (cj 1 gas_path_ptr_rules) >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  drule instruction_prefix_cursor >> strip_tac >>
  Cases_on `step_inst_base h s` >>
  gvs[run_inst_seq_def, inst_seq_ptr_def] >>
  rename1 `step_inst_base h s = OK u` >>
  `step_inst 0 ctx h s = OK u` by simp[step_inst_non_invoke] >>
  `~u.vs_halted /\ u.vs_current_bb = s.vs_current_bb` by
    metis_tac[step_preserves_halted, step_preserves_control_flow] >>
  `EVERY (\i. ~is_terminator i.inst_opcode) code` by fs[EVERY_MEM] >>
  first_x_assum (qspecl_then [`u with vs_inst_idx := SUC s.vs_inst_idx`,
    `t with vs_inst_idx := SUC s.vs_inst_idx`, `step_prov PG G h u`,
    `step_taint h s u tn`, `G'`, `tn'`, `ctx`, `fn`, `bb`] mp_tac) >>
  simp[run_inst_seq_inst_idx, exec_result_map_def] >> strip_tac >>
  drule_at (Pat `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ _`) gas_path_ptr_step >>
  simp[] >> Cases_on `h.inst_opcode = GAS` >> simp[ADD1]
QED

(* An aborting instruction ends the executed prefix: the instructions after
   it are neither counted nor checked. *)
Theorem run_inst_seq_abort_gas_path_ptr:
  !code s t a G tn G' tn' ctx fn bb.
    ~s.vs_halted /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) code /\
    inst_seq_ptr D lo ctx fn PG G tn code s G' tn' /\
    run_inst_seq code s = Abort a t ==>
    ?n j. gas_path_ptr D lo ctx fn PG G tn s n G' tn'
            (Abort a (t with vs_inst_idx := j))
Proof
  Induct >- simp[run_inst_seq_def] >>
  rpt gen_tac >> strip_tac >>
  drule instruction_prefix_cursor >> strip_tac >>
  Cases_on `step_inst_base h s` >>
  gvs[run_inst_seq_def, inst_seq_ptr_def]
  >~ [`step_inst_base h s = OK u`]
  >- (`step_inst 0 ctx h s = OK u` by simp[step_inst_non_invoke] >>
      `~u.vs_halted /\ u.vs_current_bb = s.vs_current_bb` by
        metis_tac[step_preserves_halted, step_preserves_control_flow] >>
      `EVERY (\i. ~is_terminator i.inst_opcode) code` by fs[EVERY_MEM] >>
      first_x_assum (qspecl_then [`u with vs_inst_idx := SUC s.vs_inst_idx`,
        `t with vs_inst_idx := SUC s.vs_inst_idx`, `a`, `step_prov PG G h u`,
        `step_taint h s u tn`, `G'`, `tn'`, `ctx`, `fn`, `bb`] mp_tac) >>
      simp[run_inst_seq_inst_idx, exec_result_map_def] >> strip_tac >>
      qexistsl_tac [`(if h.inst_opcode = GAS then 1 else 0) + n`, `j`] >>
      irule gas_path_ptr_step >> simp[] >> metis_tac[]) >>
  qexistsl_tac [`if h.inst_opcode = GAS then 1 else 0`, `t.vs_inst_idx`] >>
  simp[] >> irule gas_path_ptr_abort >> simp[] >> metis_tac[]
QED
