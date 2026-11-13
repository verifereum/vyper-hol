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
  ptrDiscipline codegenRel contextCodegenRel venomExecProofs
  exprLoweringProps instIdxIndep venomExecSemantics venomInstProofs
  venomInst venomState list rich_list arithmetic
  fragGasOriginPtr fragGasOrigin fragGasSeqMem fragExecMem gasEvents memSafeRun

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

(* The raw jump a break, continue or constructor return emits: a
   pointer-checked edge that keeps the ghost, above any bound lo the
   allocas respect. *)
Theorem emit_jump_path_ptr:
  sb.cs_blocks = sa.cs_blocks /\ sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_current_insts = sa.cs_current_insts ++
    [mk_inst sa.cs_next_id JMP [Label lbl] []] /\
  fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  allocas_from lo s ==>
  gas_path_ptr D lo ctx func PG G tn s 0 G tn (OK (jump_to lbl s))
Proof
  strip_tac >> drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb (LENGTH sa.cs_current_insts) =
    SOME (mk_inst sa.cs_next_id JMP [Label lbl] [])` by
    (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
  `ptr_safe_step D lo 0 ctx func PG G tn
     (mk_inst sa.cs_next_id JMP [Label lbl] []) s` by
    (simp[ptr_safe_step_def, ptr_inst_ok_def, access_ok_def, taint_ok_def,
          mk_inst_def, source_memory_write_ranges_def,
          source_memory_read_ranges_def, op_taint_def] >>
     simp[GSYM mk_inst_def, step_inst_non_invoke] >>
     simp[mk_inst_def, step_jmp_behavior, jump_to_def]) >>
  `gas_path_ptr_edge D lo ctx func PG G tn s 0 G tn (OK (jump_to lbl s))` by
    (rewrite_tac[gas_path_ptr_edge_def] >> simp[] >>
     qexists_tac `0:num` >>
     simp[step_inst_non_invoke, mk_inst_def, gas_count_step_def,
          step_jmp_behavior, is_terminator_def] >>
     fs[mk_inst_def] >> metis_tac[]) >>
  `~(jump_to lbl s).vs_halted` by simp[jump_to_def] >>
  metis_tac[gas_path_ptr_rules, arithmeticTheory.ADD_CLAUSES]
QED

(* A pointer-safe run that halts at a RETURN after plain instructions
   (no INVOKE, no GAS, no terminator) is a zero-count pointer-checked path
   to its halt. *)
Theorem halting_tail_gas_path_ptr:
  !pre ret s fuel ctx fn PG G tn bb final D lo.
    ~s.vs_halted /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX (pre ++ [ret]) (DROP s.vs_inst_idx bb.bb_instructions) /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\
               ~is_terminator i.inst_opcode) pre /\
    ret.inst_opcode = RETURN /\
    run_from fuel ctx fn s = Halt final /\
    ptr_safe_run D lo fuel ctx fn PG G tn s ==>
    ?G' tn'. gas_path_ptr D lo ctx fn PG G tn s 0 G' tn' (Halt final)
Proof
  Induct
  >- (rpt gen_tac >> strip_tac >>
      qpat_x_assum `isPREFIX _ _` (mp_tac o REWRITE_RULE [APPEND]) >>
      strip_tac >> drule instruction_prefix_cursor >> strip_tac >>
      `step_inst fuel ctx ret s = step_inst_base ret s` by
        simp[step_inst_non_invoke] >>
      `!t. step_inst_base ret s <> OK t` by
        (Cases_on `ret` >> gvs[] >>
         simp[step_inst_base_opcode_eqs, AllCaseEqs(), LET_THM]) >>
      `step_inst_base ret s = Halt final` by
        (qpat_x_assum `run_from _ _ _ _ = _` mp_tac >>
         simp[run_from_def, Once exec_block_def] >>
         Cases_on `step_inst_base ret s` >> gvs[is_terminator_def]) >>
      `ptr_safe_step D lo fuel ctx fn PG G tn ret s` by
        (qpat_x_assum `ptr_safe_run _ _ _ _ _ _ _ _ _` mp_tac >>
         simp[ptr_safe_run_def, Once ptr_safe_block_def]) >>
      qexistsl_tac [`G`, `tn`] >>
      irule (cj 3 gas_path_ptr_rules) >> simp[exit_result_def] >>
      rewrite_tac[gas_path_ptr_edge_def] >> simp[] >>
      qexists_tac `fuel` >> simp[gas_count_step_def, exit_result_def]) >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `isPREFIX _ _` (mp_tac o REWRITE_RULE [APPEND]) >>
  strip_tac >> drule instruction_prefix_cursor >> strip_tac >> fs[] >>
  `step_inst fuel ctx h s = step_inst_base h s` by simp[step_inst_non_invoke] >>
  `ptr_safe_step D lo fuel ctx fn PG G tn h s` by
    (qpat_x_assum `ptr_safe_run _ _ _ _ _ _ _ _ _` mp_tac >>
     simp[ptr_safe_run_def, Once ptr_safe_block_def]) >>
  Cases_on `step_inst_base h s`
  >~ [`step_inst_base h s = OK t`]
  >- (`~t.vs_halted /\ t.vs_current_bb = s.vs_current_bb` by
        metis_tac[step_preserves_halted, step_preserves_control_flow] >>
      `run_from fuel ctx fn (t with vs_inst_idx := SUC s.vs_inst_idx) =
         Halt final` by
        (qpat_x_assum `run_from _ _ _ _ = _` mp_tac >>
         simp[run_from_def, Once exec_block_def]) >>
      `ptr_safe_run D lo fuel ctx fn PG
         (FST (ghost_step fuel ctx PG G tn h s))
         (SND (ghost_step fuel ctx PG G tn h s))
         (t with vs_inst_idx := SUC s.vs_inst_idx)` by
        (qpat_x_assum `ptr_safe_run _ _ _ _ _ _ _ _ _` mp_tac >>
         simp[ptr_safe_run_def] >>
         drule_all ptr_safe_block_step >> simp[]) >>
      first_x_assum (qspecl_then [`ret`, `t with vs_inst_idx := SUC s.vs_inst_idx`,
          `fuel`, `ctx`, `fn`, `PG`, `FST (ghost_step fuel ctx PG G tn h s)`,
          `SND (ghost_step fuel ctx PG G tn h s)`, `bb`, `final`, `D`, `lo`] mp_tac) >>
      simp[] >> strip_tac >>
      qexistsl_tac [`G'`, `tn'`] >>
      `gas_path_ptr D lo ctx fn PG G tn s (0 + 0) G' tn' (Halt final)`
        suffices_by simp[] >>
      irule (cj 2 gas_path_ptr_rules) >>
      qexistsl_tac [`FST (ghost_step fuel ctx PG G tn h s)`,
                    `t with vs_inst_idx := SUC s.vs_inst_idx`,
                    `SND (ghost_step fuel ctx PG G tn h s)`] >>
      simp[] >> rewrite_tac[gas_path_ptr_edge_def] >> simp[] >>
      qexists_tac `fuel` >> simp[gas_count_step_def])
  >~ [`step_inst_base h s = Halt t`]
  >- (`t = final` by
        (qpat_x_assum `run_from _ _ _ _ = _` mp_tac >>
         simp[run_from_def, Once exec_block_def]) >>
      gvs[] >> qexistsl_tac [`G`, `tn`] >>
      irule (cj 3 gas_path_ptr_rules) >> simp[exit_result_def] >>
      rewrite_tac[gas_path_ptr_edge_def] >> simp[] >>
      qexists_tac `fuel` >> simp[gas_count_step_def, exit_result_def]) >>
  qpat_x_assum `run_from _ _ _ _ = _` mp_tac >>
  simp[run_from_def, Once exec_block_def]
QED

(* The checks and the recorded origin use this same concrete step. *)
Theorem straight_line_origin_ptr_edge:
  ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\
  inst_mem_below_frontier i s /\ inst_dload_in_section i s /\
  ptr_inst_ok D lo 0 ctx func G tn i s /\
  step_inst_base i s = OK u ==>
  gas_origin_ptr_edge (D, lo, explicit, ctx, func, PG) (s, G, tn)
    (if i.inst_opcode = GAS then [(func.fn_name, i.inst_id) IN explicit] else [])
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx),
     step_prov PG G i u, step_taint i s u tn)
Proof
  strip_tac >>
  `step_inst 0 ctx i s = OK u` by simp[step_inst_non_invoke] >>
  `~u.vs_halted` by metis_tac[step_preserves_halted] >>
  PURE_REWRITE_TAC[gas_origin_ptr_edge_def] >> conj_tac
  >- (rewrite_tac[gas_origin_edge_def] >> conj_tac >- simp[] >>
      qexistsl_tac [`0`, `bb`, `i`, `OK u`] >>
      Cases_on `i.inst_opcode = GAS` >>
      simp[gas_events_step_def, mem_safe_step_non_invoke]) >>
  drule_all straight_line_ptr_edge >>
  Cases_on `i.inst_opcode = GAS` >> simp[]
QED

Theorem run_inst_seq_gas_origin_ptr_path:
  !code s t G tn G' tn' ctx func bb.
    ~s.vs_halted /\
    lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) /\
    EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) code /\
    run_inst_seq_mem_ok code s /\
    inst_seq_ptr D lo ctx func PG G tn code s G' tn' /\
    run_inst_seq code s = OK t ==>
    gas_origin_ptr_path (D, lo, explicit, ctx, func, PG) (s, G, tn)
      (MAP (\i. (func.fn_name, i.inst_id) IN explicit)
        (FILTER (\i. i.inst_opcode = GAS) code))
      (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH code), G', tn')
Proof
  Induct
  >- (simp[run_inst_seq_def, inst_seq_ptr_def] >> rpt strip_tac >>
      gvs[] >> irule (cj 1 gas_origin_ptr_path_rules) >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  drule instruction_prefix_cursor >> strip_tac >>
  Cases_on `step_inst_base h s` >>
  gvs[run_inst_seq_def, inst_seq_ptr_def, run_inst_seq_mem_ok_def] >>
  rename1 `step_inst_base h s = OK u` >>
  `step_inst 0 ctx h s = OK u` by simp[step_inst_non_invoke] >>
  `~u.vs_halted /\ u.vs_current_bb = s.vs_current_bb` by
    metis_tac[step_preserves_halted, step_preserves_control_flow] >>
  `EVERY (\i. ~is_terminator i.inst_opcode) code` by fs[EVERY_MEM] >>
  first_x_assum (qspecl_then [`u with vs_inst_idx := SUC s.vs_inst_idx`,
    `t with vs_inst_idx := SUC s.vs_inst_idx`, `step_prov PG G h u`,
    `step_taint h s u tn`, `G'`, `tn'`, `ctx`, `func`, `bb`] mp_tac) >>
  simp[run_inst_seq_inst_idx, exec_result_map_def] >> strip_tac >>
  `gas_origin_ptr_edge (D, lo, explicit, ctx, func, PG) (s, G, tn)
    (if h.inst_opcode = GAS then [(func.fn_name, h.inst_id) IN explicit] else [])
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx),
     step_prov PG G h u, step_taint h s u tn)` by
    (irule straight_line_origin_ptr_edge >> simp[]) >>
  drule (cj 2 gas_origin_ptr_path_rules) >> disch_then drule >>
  Cases_on `h.inst_opcode = GAS` >> simp[ADD1]
QED
