(* Local memmerging phase: captured source replay and emission. *)
Theory mmLocalReplayProofs
Ancestors
  venomFnInstsProofs venomInst memoryReadRel
  mmSupplyWfProofs mmTransformSupply mmCopyEquiv dftGasFromListTraceDefs unitMemInv o1PassLift
  venomFnScheduleRunner allocaRemapSSA o1MakeSsaCfg makeSsaCurrentWfSsa
  cfgWf venomWf stateEquiv rich_list mmTransform mmScan mmCopy list sorting
  simplifyCfgPhiSemantics simplifyCfgFixupStatic basePtrProofs mmTraceProofs frameViewMemory dftCommutation
  regularMemorySim rangeAnalysisProofs dftIndexedExec removeUnusedProofs analysisSimProofsBase
  mmLocalStructureProofs
  mmLocalCaptureProofs
  mmLocalPendingProofs
  venomTransformStructureProps venomWriteReplayProps venomExecutionReplayProps irSupplyFreshProps
Libs
  wordsLib finite_mapLib stepInstBaseLib

Theorem mm_local_mem2mem_bulk_emission[local]:
  ~MEM inst.inst_id nop_set /\ ALOOKUP rep_map inst.inst_id = SOME g /\
  g.cg_length <> 32 ==>
  apply_groups_inst_supply Mem2Mem nop_set rep_map sk inst =
    ([mk_bulk_copy_inst Mem2Mem inst g],sk)
Proof
  simp[apply_groups_inst_supply_def]
QED

Theorem mm_local_mem2mem_bulk_step[local]:
  g.cg_dst < dimword (:256) /\ g.cg_src < dimword (:256) /\
  g.cg_length < dimword (:256) ==>
  step_inst fuel ctx (mk_bulk_copy_inst Mem2Mem inst g) t =
    OK (write_memory_with_expansion g.cg_dst
      (read_memory g.cg_src g.cg_length t) t)
Proof
  strip_tac >>
  simp[mk_bulk_copy_inst_def, mode_copy_opcode_def,
    venomExecSemanticsTheory.step_inst_non_invoke,
    venomExecSemanticsTheory.step_inst_base_def,
    venomStateTheory.eval_operand_def, wordsTheory.w2n_n2w,
    venomExecSemanticsTheory.mcopy_def, venomStateTheory.read_memory_def]
QED

Theorem mm_local_fixed_cut_source_replay_interval[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\ a <= j /\ j <= r /\ r < LENGTH is /\ r < N /\
  (!q. a <= q /\ q < r ==> (H (SUC q)).vs_memory =
    (case mm_local_write_capture is H N q of NONE => H q
     | SOME (d,bs) => write_memory_with_expansion d bs (H q)).vs_memory) /\
  s0 = FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem) empty_scan_state (TAKE j is) /\
  gs = (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
  (!q. a <= q /\ q < r ==> ?b. MEM b (mm_local_pending_indices is gs (SUC q))) /\
  ((?dj sj lj. (EL j is).inst_opcode = MCOPY /\
      (EL j is).inst_operands = [Lit dj; Lit sj; Lit lj] /\
      c = <|cg_dst := w2n dj; cg_src := w2n sj; cg_length := w2n lj;
             cg_inst_ids := [(EL j is).inst_id]|>) \/
   (?dj vj srcj. (EL j is).inst_opcode = MSTORE /\
      (EL j is).inst_operands = [Lit dj; Var vj] /\
      FLOOKUP s0.ss_loads vj = SOME srcj /\
      c = <|cg_dst := w2n dj; cg_src := srcj; cg_length := 32;
             cg_inst_ids := [(EL j is).inst_id] ++
               (case dfg_get_def (dfg_build_function fn0) vj of
                  NONE => [] | SOME li => [li.inst_id])|>)) /\
  (j = r \/ (?g. MEM g gs /\ MEM (EL j is).inst_id g.cg_inst_ids /\
    rep_of_group is g = SOME ((EL r is).inst_id,g))) /\
  t = FOLDL (\st q. if MEM q (mm_local_pending_indices is gs r) then st else
    case mm_local_write_capture is H N q of NONE => st
    | SOME (d,bs) => write_memory_with_expansion d bs st)
    (H a) (MAP (\q. a+q) (COUNT_LIST (r-a))) ==>
  read_memory c.cg_src c.cg_length t = read_memory c.cg_src c.cg_length (H j)
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  irule venomWriteReplayPropsTheory.selective_segment_replay >>
  qexistsl [`\q. MEM q (mm_local_pending_indices is gs r)`, `a`,
    `mm_local_write_capture is H N`, `r`] >> simp[] >>
  conj_tac
  >- (rpt strip_tac >>
      `c.cg_src+c.cg_length <= d \/ d+LENGTH bs <= c.cg_src \/ c.cg_length = 0 \/ bs = []`
        suffices_by simp[arithmeticTheory.ADD_COMM] >>
      mp_tac (Q.INST [`j` |-> `j`, `r` |-> `r`, `ss` |-> `s0`]
        (SPEC_ALL mm_local_pending_prefix_source_exclusion)) >>
      simp[] >> gvs[]) >>
  rpt strip_tac >>
  `j < r` by decide_tac >>
  `?g. MEM g gs /\ MEM (EL j is).inst_id g.cg_inst_ids /\
    rep_of_group is g = SOME ((EL r is).inst_id,g)` by (gvs[] >> metis_tac[]) >>
  `c.cg_src+c.cg_length <= d \/ d+LENGTH bs <= c.cg_src \/ c.cg_length = 0 \/ bs = []`
    suffices_by simp[arithmeticTheory.ADD_COMM] >>
  mp_tac (Q.INST [`j` |-> `j`, `r` |-> `r`, `s0` |-> `s0`,
    `ss` |-> `FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem) empty_scan_state (TAKE q is)`]
    (SPEC_ALL mm_local_pending_suffix_source_exclusion)) >>
  simp[] >> gvs[]
QED

Theorem mm_local_fixed_cut_source_replay[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\ a <= j /\ j <= r /\ r < LENGTH is /\ r < N /\
  mm_local_history is H N /\
  s0 = FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem) empty_scan_state (TAKE j is) /\
  gs = (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
  (!q. a <= q /\ q < r ==> ?b. MEM b (mm_local_pending_indices is gs (SUC q))) /\
  ((?dj sj lj. (EL j is).inst_opcode = MCOPY /\
      (EL j is).inst_operands = [Lit dj; Lit sj; Lit lj] /\
      c = <|cg_dst := w2n dj; cg_src := w2n sj; cg_length := w2n lj;
             cg_inst_ids := [(EL j is).inst_id]|>) \/
   (?dj vj srcj. (EL j is).inst_opcode = MSTORE /\
      (EL j is).inst_operands = [Lit dj; Var vj] /\
      FLOOKUP s0.ss_loads vj = SOME srcj /\
      c = <|cg_dst := w2n dj; cg_src := srcj; cg_length := 32;
             cg_inst_ids := [(EL j is).inst_id] ++
               (case dfg_get_def (dfg_build_function fn0) vj of
                  NONE => [] | SOME li => [li.inst_id])|>)) /\
  (j = r \/ (?g. MEM g gs /\ MEM (EL j is).inst_id g.cg_inst_ids /\
    rep_of_group is g = SOME ((EL r is).inst_id,g))) /\
  t = FOLDL (\st q. if MEM q (mm_local_pending_indices is gs r) then st else
    case mm_local_write_capture is H N q of NONE => st
    | SOME (d,bs) => write_memory_with_expansion d bs st)
    (H a) (MAP (\q. a+q) (COUNT_LIST (r-a))) ==>
  read_memory c.cg_src c.cg_length t = read_memory c.cg_src c.cg_length (H j)
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  irule mm_local_fixed_cut_source_replay_interval >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >>
  reverse conj_tac >- gvs[] >>
  `a <= r` by decide_tac >>
  mp_tac (Q.INST [`a` |-> `a`, `r` |-> `r`]
    (SPEC_ALL mm_local_fixed_cut_capture_recurrence)) >> simp[]
QED

Theorem mm_local_final_birth_ancestor[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\ j < LENGTH is /\
  gs = (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
  MEM g gs /\ MEM (EL j is).inst_id g.cg_inst_ids /\
  s0 = FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem) empty_scan_state (TAKE j is) /\
  ((?dj sj lj. (EL j is).inst_opcode = MCOPY /\
      (EL j is).inst_operands = [Lit dj; Lit sj; Lit lj] /\
      c = <|cg_dst := w2n dj; cg_src := w2n sj; cg_length := w2n lj;
             cg_inst_ids := [(EL j is).inst_id]|>) \/
   (?dj vj srcj. (EL j is).inst_opcode = MSTORE /\
      (EL j is).inst_operands = [Lit dj; Var vj] /\
      FLOOKUP s0.ss_loads vj = SOME srcj /\
      c = <|cg_dst := w2n dj; cg_src := srcj; cg_length := 32;
             cg_inst_ids := [(EL j is).inst_id] ++
               (case dfg_get_def (dfg_build_function fn0) vj of
                  NONE => [] | SOME li => [li.inst_id])|>)) ==>
  mm_local_copy_ancestor c g
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `?h. MEM h gs /\ mm_local_copy_ancestor c h` by
    (`?h. MEM h ((FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem)
        empty_scan_state is).ss_copies ++
        (FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem)
        empty_scan_state is).ss_flushed) /\ mm_local_copy_ancestor c h` by
       (qpat_x_assum `(?dj sj lj. (EL j is).inst_opcode = MCOPY /\ _) \/ _` strip_assume_tac
        >- (drule_at (Pat `_.inst_operands = _`)
              (Q.INST [`n` |-> `LENGTH is`, `dfg` |-> `dfg_build_function fn0`,
                `ss` |-> `FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem) empty_scan_state is`]
                (SPEC_ALL (REWRITE_RULE [mode_copy_opcode_def]
                  (Q.INST [`mode` |-> `Mem2Mem`] mm_local_bulk_cut_fragment)))) >> simp[]) >>
        drule_at (Pat `_.inst_operands = _`)
          (Q.INST [`n` |-> `LENGTH is`, `dfg` |-> `dfg_build_function fn0`,
            `ss` |-> `FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem) empty_scan_state is`]
            (SPEC_ALL (Q.INST [`mode` |-> `Mem2Mem`] mm_local_store_cut_fragment))) >> simp[] >> gvs[]) >>
     gvs[scan_block_def, hard_barrier_def] >> metis_tac[]) >>
  `MEM (EL j is).inst_id c.cg_inst_ids /\
    (EL j is).inst_opcode IN {MSTORE; MCOPY; CALLDATACOPY; DLOADBYTES}` by
    (qpat_x_assum `(?dj sj lj. (EL j is).inst_opcode = MCOPY /\ _) \/ _` strip_assume_tac >> gvs[]) >>
  `MEM (EL j is).inst_id h.cg_inst_ids` by gvs[mm_local_copy_ancestor_def] >>
  `MEM (EL j is) bb.bb_instructions` by metis_tac[EL_MEM] >>
  `h = g` by
    (irule mm_local_prefix_write_group_owner >> goal_assum (drule_at Any) >> metis_tac[]) >>
  gvs[]
QED

Theorem mm_local_canonical_due_birth_geometry:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\
  gs = (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
  r < LENGTH is /\ MEM g gs /\
  rep_of_group is g = SOME ((EL r is).inst_id,g) /\
  due = FILTER (\j. mm_local_rep_index is gs j = r) (mm_local_pending_indices is gs r) /\
  MEM j (due ++ [r]) /\
  s0 = FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem) empty_scan_state (TAKE j is) ==>
  j <= r /\ mm_local_epoch_start is gs r <= j /\
  ?c. g.cg_dst <= c.cg_dst /\
    c.cg_dst + c.cg_length <= g.cg_dst + g.cg_length /\
    c.cg_src = g.cg_src + (c.cg_dst - g.cg_dst) /\
    ((?dj sj lj. (EL j is).inst_opcode = MCOPY /\
        (EL j is).inst_operands = [Lit dj; Lit sj; Lit lj] /\
        c = <|cg_dst := w2n dj; cg_src := w2n sj; cg_length := w2n lj;
               cg_inst_ids := [(EL j is).inst_id]|>) \/
     (?dj vj srcj. (EL j is).inst_opcode = MSTORE /\
        (EL j is).inst_operands = [Lit dj; Var vj] /\
        FLOOKUP s0.ss_loads vj = SOME srcj /\
        c = <|cg_dst := w2n dj; cg_src := srcj; cg_length := 32;
               cg_inst_ids := [(EL j is).inst_id] ++
                 (case dfg_get_def (dfg_build_function fn0) vj of
                    NONE => [] | SOME li => [li.inst_id])|>))
Proof
  strip_tac >>
  `j < LENGTH is /\ MEM (EL j is).inst_id g.cg_inst_ids /\
    ?d l. mm_local_write_footprint (EL j is) = SOME (d,l)` by
    metis_tac[mm_local_canonical_due_footprint_indices] >>
  `j <= r` by
    (gvs[MEM_FILTER, mm_local_pending_indices_mem] >> decide_tac) >>
  `mm_local_epoch_start is gs r <= j` by
    (Cases_on `j = r` >- metis_tac[mm_local_epoch_start_bound] >>
     `MEM j (mm_local_pending_indices is gs r)` by gvs[MEM_FILTER] >>
     metis_tac[mm_local_epoch_start_pending_bound]) >>
  simp[] >>
  ` (EL j is).inst_opcode IN {MSTORE; MCOPY; CALLDATACOPY; DLOADBYTES}` by
    metis_tac[mm_local_write_footprint_opcode] >>
  `MEM g (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed` by metis_tac[] >>
  `?c. ((?dj sj lj. (EL j is).inst_opcode = MCOPY /\
      (EL j is).inst_operands = [Lit dj; Lit sj; Lit lj] /\
      c = <|cg_dst := w2n dj; cg_src := w2n sj; cg_length := w2n lj;
             cg_inst_ids := [(EL j is).inst_id]|>) \/
    (?dj vj srcj. (EL j is).inst_opcode = MSTORE /\
      (EL j is).inst_operands = [Lit dj; Var vj] /\
      FLOOKUP s0.ss_loads vj = SOME srcj /\
      c = <|cg_dst := w2n dj; cg_src := srcj; cg_length := 32;
             cg_inst_ids := [(EL j is).inst_id] ++
               (case dfg_get_def (dfg_build_function fn0) vj of
                  NONE => [] | SOME li => [li.inst_id])|>))` by
    (drule_all (REWRITE_RULE [mode_copy_opcode_def] (Q.INST [`mode` |-> `Mem2Mem`] mm_local_final_write_birth)) >> gvs[] >> metis_tac[]) >>
  `mm_local_copy_ancestor c g` by
    (irule mm_local_final_birth_ancestor >> goal_assum (drule_at Any) >> metis_tac[]) >>
  qexists `c` >> gvs[mm_local_copy_ancestor_def] >> decide_tac
QED

Theorem mm_local_epoch_source_read_interval[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\ a <= j /\ j <= r /\ r < LENGTH is /\ r < N /\
  (!q. a <= q /\ q < r ==> (H (SUC q)).vs_memory =
    (case mm_local_write_capture is H N q of NONE => H q
     | SOME (d,bs) => write_memory_with_expansion d bs (H q)).vs_memory) /\
  s0 = FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem) empty_scan_state (TAKE j is) /\
  gs = (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
  a = mm_local_epoch_start is gs r /\
  ((?dj sj lj. (EL j is).inst_opcode = MCOPY /\
      (EL j is).inst_operands = [Lit dj; Lit sj; Lit lj] /\
      c = <|cg_dst := w2n dj; cg_src := w2n sj; cg_length := w2n lj;
             cg_inst_ids := [(EL j is).inst_id]|>) \/
   (?dj vj srcj. (EL j is).inst_opcode = MSTORE /\
      (EL j is).inst_operands = [Lit dj; Var vj] /\
      FLOOKUP s0.ss_loads vj = SOME srcj /\
      c = <|cg_dst := w2n dj; cg_src := srcj; cg_length := 32;
             cg_inst_ids := [(EL j is).inst_id] ++
               (case dfg_get_def (dfg_build_function fn0) vj of
                  NONE => [] | SOME li => [li.inst_id])|>)) /\
  (j = r \/ (?g. MEM g gs /\ MEM (EL j is).inst_id g.cg_inst_ids /\
    rep_of_group is g = SOME ((EL r is).inst_id,g))) /\
  u = FOLDL (\st q. if MEM q (mm_local_pending_indices is gs r) then st else
    case mm_local_write_capture is H N q of NONE => st
    | SOME (d,bs) => write_memory_with_expansion d bs st)
    (H a) (MAP (\q. a+q) (COUNT_LIST (r-a))) /\
  t.vs_memory = u.vs_memory ==>
  read_memory c.cg_src c.cg_length t = read_memory c.cg_src c.cg_length (H j) /\
  ((!v src. FLOOKUP s0.ss_loads v = SOME src ==>
      lookup_var v (H j) = SOME (mload src (H j))) ==>
    mm_local_write_capture is H N j =
      SOME (c.cg_dst,read_memory c.cg_src c.cg_length t))
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `!q. a <= q /\ q < r ==> ?b. MEM b (mm_local_pending_indices is gs (SUC q))` by
    metis_tac[mm_local_epoch_start_nonempty] >>
  `read_memory c.cg_src c.cg_length u = read_memory c.cg_src c.cg_length (H j)` by
    (mp_tac (Q.INST [`t` |-> `u`] (SPEC_ALL mm_local_fixed_cut_source_replay_interval)) >> simp[]) >>
  `read_memory c.cg_src c.cg_length t = read_memory c.cg_src c.cg_length (H j)` by
    gvs[venomStateTheory.read_memory_def] >>
  conj_tac >- first_assum ACCEPT_TAC >> strip_tac >>
  `j < N` by decide_tac >>
  `mm_local_write_capture is H N j =
    SOME (c.cg_dst,read_memory c.cg_src c.cg_length (H j))` by
    (irule mm_local_selected_write_capture_bounds >> simp[] >>
     qpat_x_assum `(?dj sj lj. (EL j is).inst_opcode = MCOPY /\ _) \/ _` strip_assume_tac >>
     gvs[] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem mm_local_epoch_source_read[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\ a <= j /\ j <= r /\ r < LENGTH is /\ r < N /\
  mm_local_history is H N /\
  s0 = FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem) empty_scan_state (TAKE j is) /\
  gs = (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
  a = mm_local_epoch_start is gs r /\
  ((?dj sj lj. (EL j is).inst_opcode = MCOPY /\
      (EL j is).inst_operands = [Lit dj; Lit sj; Lit lj] /\
      c = <|cg_dst := w2n dj; cg_src := w2n sj; cg_length := w2n lj;
             cg_inst_ids := [(EL j is).inst_id]|>) \/
   (?dj vj srcj. (EL j is).inst_opcode = MSTORE /\
      (EL j is).inst_operands = [Lit dj; Var vj] /\
      FLOOKUP s0.ss_loads vj = SOME srcj /\
      c = <|cg_dst := w2n dj; cg_src := srcj; cg_length := 32;
             cg_inst_ids := [(EL j is).inst_id] ++
               (case dfg_get_def (dfg_build_function fn0) vj of
                  NONE => [] | SOME li => [li.inst_id])|>)) /\
  (j = r \/ (?g. MEM g gs /\ MEM (EL j is).inst_id g.cg_inst_ids /\
    rep_of_group is g = SOME ((EL r is).inst_id,g))) /\
  u = FOLDL (\st q. if MEM q (mm_local_pending_indices is gs r) then st else
    case mm_local_write_capture is H N q of NONE => st
    | SOME (d,bs) => write_memory_with_expansion d bs st)
    (H a) (MAP (\q. a+q) (COUNT_LIST (r-a))) /\
  t.vs_memory = u.vs_memory ==>
  read_memory c.cg_src c.cg_length t = read_memory c.cg_src c.cg_length (H j) /\
  ((!v src. FLOOKUP s0.ss_loads v = SOME src ==>
      lookup_var v (H j) = SOME (mload src (H j))) ==>
    mm_local_write_capture is H N j =
      SOME (c.cg_dst,read_memory c.cg_src c.cg_length t))
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `!q. a <= q /\ q < r ==> ?b. MEM b (mm_local_pending_indices is gs (SUC q))` by
    metis_tac[mm_local_epoch_start_nonempty] >>
  `a <= r` by decide_tac >>
  `!q. a <= q /\ q < r ==> (H (SUC q)).vs_memory =
    (case mm_local_write_capture is H N q of NONE => H q
     | SOME (d,bs) => write_memory_with_expansion d bs (H q)).vs_memory` by
    (mp_tac (Q.INST [`a` |-> `a`, `r` |-> `r`]
       (SPEC_ALL mm_local_fixed_cut_capture_recurrence)) >> simp[]) >>
  mp_tac (SPEC_ALL mm_local_epoch_source_read_interval) >> simp[]
QED

Theorem mm_local_canonical_due_index_payload_interval[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\
  gs = (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
  r < LENGTH is /\ MEM g gs /\
  (!q. a <= q /\ q < r ==> (H (SUC q)).vs_memory =
    (case mm_local_write_capture is H (SUC r) q of NONE => H q
     | SOME (d,bs) => write_memory_with_expansion d bs (H q)).vs_memory) /\
  rep_of_group is g = SOME ((EL r is).inst_id,g) /\
  cap = mm_local_write_capture is H (SUC r) /\
  due = FILTER (\j. mm_local_rep_index is gs j = r) (mm_local_pending_indices is gs r) /\
  MEM j (due ++ [r]) /\
  s0 = FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem) empty_scan_state (TAKE j is) /\
  (!v src. FLOOKUP s0.ss_loads v = SOME src ==>
    lookup_var v (H j) = SOME (mload src (H j))) /\
  a = mm_local_epoch_start is gs r /\
  u = FOLDL (\st q. if MEM q (mm_local_pending_indices is gs r) then st else
    case mm_local_write_capture is H (SUC r) q of NONE => st
    | SOME (d,bs) => write_memory_with_expansion d bs st)
    (H a) (MAP (\q. a+q) (COUNT_LIST (r-a))) /\
  t.vs_memory = u.vs_memory ==>
  ?d bs. cap j = SOME (d,bs) /\
    g.cg_dst <= d /\ d + LENGTH bs <= g.cg_dst + g.cg_length /\
    bs = read_memory (g.cg_src + (d-g.cg_dst)) (LENGTH bs) t
Proof
  strip_tac >>
  drule_all mm_local_canonical_due_footprint_indices >>
  disch_then (qspec_then `j` mp_tac) >> simp[] >> strip_tac >>
  drule_all mm_local_canonical_due_birth_geometry >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac (qx_choose_then `c`
      (REPEAT_TCL CONJUNCTS_THEN assume_tac)))) >>
  `mm_local_write_capture is H (SUC r) j =
    SOME (c.cg_dst, read_memory c.cg_src c.cg_length t)` by
    (mp_tac (Q.INST [`N` |-> `SUC r`] (SPEC_ALL mm_local_epoch_source_read_interval)) >>
     simp[] >> metis_tac[]) >>
  qexistsl [`c.cg_dst`, `read_memory c.cg_src c.cg_length t`] >>
  gvs[mm_local_read_memory_bytes, mm_local_bytes_length]
QED

Theorem mm_local_canonical_due_index_payload[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\
  gs = (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
  r < LENGTH is /\ mm_local_history is H (SUC r) /\ MEM g gs /\
  rep_of_group is g = SOME ((EL r is).inst_id,g) /\
  cap = mm_local_write_capture is H (SUC r) /\
  due = FILTER (\j. mm_local_rep_index is gs j = r) (mm_local_pending_indices is gs r) /\
  MEM j (due ++ [r]) /\
  s0 = FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem) empty_scan_state (TAKE j is) /\
  (!v src. FLOOKUP s0.ss_loads v = SOME src ==>
    lookup_var v (H j) = SOME (mload src (H j))) /\
  a = mm_local_epoch_start is gs r /\
  u = FOLDL (\st q. if MEM q (mm_local_pending_indices is gs r) then st else
    case mm_local_write_capture is H (SUC r) q of NONE => st
    | SOME (d,bs) => write_memory_with_expansion d bs st)
    (H a) (MAP (\q. a+q) (COUNT_LIST (r-a))) /\
  t.vs_memory = u.vs_memory ==>
  ?d bs. cap j = SOME (d,bs) /\
    g.cg_dst <= d /\ d + LENGTH bs <= g.cg_dst + g.cg_length /\
    bs = read_memory (g.cg_src + (d-g.cg_dst)) (LENGTH bs) t
Proof
  strip_tac >>
  `!q. a <= q /\ q < r ==> ?b. MEM b (mm_local_pending_indices is gs (SUC q))` by
    metis_tac[mm_local_epoch_start_nonempty] >>
  `a <= r` by metis_tac[mm_local_epoch_start_bound] >>
  `!q. a <= q /\ q < r ==> (H (SUC q)).vs_memory =
    (case mm_local_write_capture is H (SUC r) q of NONE => H q
     | SOME (d,bs) => write_memory_with_expansion d bs (H q)).vs_memory` by
    (mp_tac (Q.INST [`a` |-> `a`, `r` |-> `r`, `N` |-> `SUC r`]
       (SPEC_ALL mm_local_fixed_cut_capture_recurrence)) >> simp[]) >>
  mp_tac (SPEC_ALL mm_local_canonical_due_index_payload_interval) >> simp[]
QED

Theorem mm_local_canonical_due_log_payload_interval[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\
  gs = (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
  r < LENGTH is /\ MEM g gs /\
  (!q. a <= q /\ q < r ==> (H (SUC q)).vs_memory =
    (case mm_local_write_capture is H (SUC r) q of NONE => H q
     | SOME (d,bs) => write_memory_with_expansion d bs (H q)).vs_memory) /\
  rep_of_group is g = SOME ((EL r is).inst_id,g) /\
  cap = mm_local_write_capture is H (SUC r) /\
  due = FILTER (\j. mm_local_rep_index is gs j = r) (mm_local_pending_indices is gs r) /\
  ws = MAP (THE o cap) (due ++ [r]) /\
  (!j v src. MEM j (due ++ [r]) /\
    FLOOKUP (FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem)
      empty_scan_state (TAKE j is)).ss_loads v = SOME src ==>
    lookup_var v (H j) = SOME (mload src (H j))) /\
  a = mm_local_epoch_start is gs r /\
  u = FOLDL (\st q. if MEM q (mm_local_pending_indices is gs r) then st else
    case mm_local_write_capture is H (SUC r) q of NONE => st
    | SOME (d,bs) => write_memory_with_expansion d bs st)
    (H a) (MAP (\q. a+q) (COUNT_LIST (r-a))) /\
  t.vs_memory = u.vs_memory ==>
  (!d bs. MEM (d,bs) ws ==> g.cg_dst <= d /\
    d + LENGTH bs <= g.cg_dst + g.cg_length /\
    bs = read_memory (g.cg_src + (d-g.cg_dst)) (LENGTH bs) t) /\
  (!v. FOLDL (\st (d,bs). write_memory_with_expansion d bs st) v ws =
    write_memory_with_expansion g.cg_dst (read_memory g.cg_src g.cg_length t) v)
Proof
  strip_tac >>
  `!j. MEM j (due ++ [r]) ==> ?d bs. cap j = SOME (d,bs) /\
    g.cg_dst <= d /\ d + LENGTH bs <= g.cg_dst + g.cg_length /\
    bs = read_memory (g.cg_src + (d-g.cg_dst)) (LENGTH bs) t` by
    (rpt strip_tac >>
     mp_tac (Q.INST [`s0` |-> `FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem)
       empty_scan_state (TAKE j is)`] (SPEC_ALL mm_local_canonical_due_index_payload_interval)) >>
     simp[] >> metis_tac[]) >>
  conj_asm1_tac
  >- (rpt gen_tac >> disch_tac >>
      `?j. MEM j (due ++ [r]) /\ (d,bs) = (THE o cap) j` by
        (qpat_x_assum `MEM (d,bs) ws` mp_tac >>
         qpat_x_assum `ws = _` SUBST1_TAC >> rewrite_tac[MEM_MAP] >> metis_tac[]) >>
      qpat_x_assum `!j. MEM j (due ++ [r]) ==> _` (qspec_then `j` mp_tac) >>
      (impl_tac >- first_assum ACCEPT_TAC) >>
      disch_then (qx_choose_then `d0` (qx_choose_then `bs0` strip_assume_tac)) >>
      qpat_x_assum `cap j = SOME _` (fn th => fs[th]) >> gvs[]) >>
  `(!a. (g.cg_dst <= a /\ a < g.cg_dst + g.cg_length) <=>
      ?d bs. MEM (d,bs) ws /\ d <= a /\ a < d + LENGTH bs) /\
    (!d bs. MEM (d,bs) ws ==> d + LENGTH bs <= g.cg_dst + g.cg_length) /\
    MAX_LIST (MAP (\(d,bs). d + LENGTH bs) ws) = g.cg_dst + g.cg_length` by
    (irule mm_local_canonical_due_log_coverage_endpoint_captures >>
     goal_assum (drule_at Any) >> metis_tac[]) >>
  gen_tac >> pure_rewrite_tac[mm_local_read_memory_bytes] >>
  irule mm_local_write_log_realize >> simp[] >>
  gvs[mm_local_read_memory_bytes]
QED

Theorem mm_local_canonical_due_log_payload[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\
  gs = (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
  r < LENGTH is /\ mm_local_history is H (SUC r) /\ MEM g gs /\
  rep_of_group is g = SOME ((EL r is).inst_id,g) /\
  cap = mm_local_write_capture is H (SUC r) /\
  due = FILTER (\j. mm_local_rep_index is gs j = r) (mm_local_pending_indices is gs r) /\
  ws = MAP (THE o cap) (due ++ [r]) /\
  (!j v src. MEM j (due ++ [r]) /\
    FLOOKUP (FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem)
      empty_scan_state (TAKE j is)).ss_loads v = SOME src ==>
    lookup_var v (H j) = SOME (mload src (H j))) /\
  a = mm_local_epoch_start is gs r /\
  u = FOLDL (\st q. if MEM q (mm_local_pending_indices is gs r) then st else
    case mm_local_write_capture is H (SUC r) q of NONE => st
    | SOME (d,bs) => write_memory_with_expansion d bs st)
    (H a) (MAP (\q. a+q) (COUNT_LIST (r-a))) /\
  t.vs_memory = u.vs_memory ==>
  (!d bs. MEM (d,bs) ws ==> g.cg_dst <= d /\
    d + LENGTH bs <= g.cg_dst + g.cg_length /\
    bs = read_memory (g.cg_src + (d-g.cg_dst)) (LENGTH bs) t) /\
  (!v. FOLDL (\st (d,bs). write_memory_with_expansion d bs st) v ws =
    write_memory_with_expansion g.cg_dst (read_memory g.cg_src g.cg_length t) v)
Proof
  strip_tac >>
  `!q. a <= q /\ q < r ==> ?b. MEM b (mm_local_pending_indices is gs (SUC q))` by
    metis_tac[mm_local_epoch_start_nonempty] >>
  `a <= r` by metis_tac[mm_local_epoch_start_bound] >>
  `!q. a <= q /\ q < r ==> (H (SUC q)).vs_memory =
    (case mm_local_write_capture is H (SUC r) q of NONE => H q
     | SOME (d,bs) => write_memory_with_expansion d bs (H q)).vs_memory` by
    (mp_tac (Q.INST [`a` |-> `a`, `r` |-> `r`, `N` |-> `SUC r`]
       (SPEC_ALL mm_local_fixed_cut_capture_recurrence)) >> simp[]) >>
  mp_tac (SPEC_ALL mm_local_canonical_due_log_payload_interval) >> simp[] >> metis_tac[]
QED

Theorem mm_local_pending_copy_capture_replay[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\ b <= j /\ j <= r /\ r < LENGTH is /\ r < N /\
  mm_local_history is H N /\
  s0 = FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem) empty_scan_state (TAKE j is) /\
  gs = (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
  (b = r \/ MEM b (mm_local_pending_indices is gs r)) /\
  (EL j is).inst_opcode = MCOPY /\
  (EL j is).inst_operands = [Lit dj; Lit sj; Lit lj] /\
  c = <|cg_dst := w2n dj; cg_src := w2n sj; cg_length := w2n lj;
         cg_inst_ids := [(EL j is).inst_id]|> /\
  (j = r \/ (?g. MEM g gs /\ MEM (EL j is).inst_id g.cg_inst_ids /\
    rep_of_group is g = SOME ((EL r is).inst_id,g))) /\
  t = FOLDL (\st q. if MEM q (mm_local_pending_indices is gs r) then st else
    case mm_local_write_capture is H N q of NONE => st
    | SOME (d,bs) => write_memory_with_expansion d bs st)
    (H b) (MAP (\q. b+q) (COUNT_LIST (r-b))) /\
  B = (\i. if i < LENGTH t.vs_memory then EL i t.vs_memory else 0w) ==>
  mm_local_write_capture is H N j =
    SOME (c.cg_dst, mm_local_bytes B c.cg_src c.cg_length)
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `read_memory c.cg_src c.cg_length t = read_memory c.cg_src c.cg_length (H j)` by
    metis_tac[mm_local_pending_source_replay] >>
  `j < N` by decide_tac >>
  drule_all mm_local_write_capture_copy >>
  gvs[mm_local_read_memory_bytes]
QED

Theorem mm_local_pending_store_capture_replay[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\ b <= j /\ j <= r /\ r < LENGTH is /\ r < N /\
  mm_local_history is H N /\
  s0 = FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem) empty_scan_state (TAKE j is) /\
  gs = (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
  (b = r \/ MEM b (mm_local_pending_indices is gs r)) /\
  (EL j is).inst_opcode = MSTORE /\
  (EL j is).inst_operands = [Lit dj; Var v] /\
  FLOOKUP s0.ss_loads v = SOME srcj /\
  lookup_var v (H j) = SOME (mload srcj (H j)) /\
  c = <|cg_dst := w2n dj; cg_src := srcj; cg_length := 32;
         cg_inst_ids := [(EL j is).inst_id] ++
           (case dfg_get_def (dfg_build_function fn0) v of
              NONE => [] | SOME li => [li.inst_id])|> /\
  (j = r \/ (?g. MEM g gs /\ MEM (EL j is).inst_id g.cg_inst_ids /\
    rep_of_group is g = SOME ((EL r is).inst_id,g))) /\
  t = FOLDL (\st q. if MEM q (mm_local_pending_indices is gs r) then st else
    case mm_local_write_capture is H N q of NONE => st
    | SOME (d,bs) => write_memory_with_expansion d bs st)
    (H b) (MAP (\q. b+q) (COUNT_LIST (r-b))) /\
  B = (\i. if i < LENGTH t.vs_memory then EL i t.vs_memory else 0w) ==>
  mm_local_write_capture is H N j =
    SOME (c.cg_dst, mm_local_bytes B c.cg_src c.cg_length)
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `read_memory c.cg_src c.cg_length t = read_memory c.cg_src c.cg_length (H j)` by
    metis_tac[mm_local_pending_source_replay] >>
  `j < N` by decide_tac >>
  drule_all mm_local_write_capture_store >>
  gvs[venomWriteReplayPropsTheory.mload_bytes, mm_local_read_memory_bytes]
QED

Theorem mm_local_pending_store_capture_replay_post_phis[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\ b <= j /\ j <= r /\ r < LENGTH is /\ r < N /\
  mm_local_history is H N /\
  s0 = FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem) empty_scan_state (TAKE j is) /\
  gs = (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
  (b = r \/ MEM b (mm_local_pending_indices is gs r)) /\
  (EL j is).inst_opcode = MSTORE /\
  (EL j is).inst_operands = [Lit dj; Var v] /\
  FLOOKUP s0.ss_loads v = SOME srcj /\
  MEM (SOME Mem2Mem) (DROP k [NONE; SOME CalldataMerge; SOME DloadMerge; SOME Mem2Mem]) /\
  h = phi_prefix_length bb.bb_instructions /\ h <= j /\
  LENGTH states = SUC (j-h) /\
  eval_phis s bb.bb_instructions = OK s_phi /\
  EL 0 states = s_phi with vs_inst_idx := h /\
  H j = EL (j-h) states /\
  (!z. z < j-h ==>
    ~is_terminator (EL (h+z) bb.bb_instructions).inst_opcode /\
    ?u. step_inst fuel ctx (EL (h+z) bb.bb_instructions) (EL z states) = OK u /\
        EL (SUC z) states = u with vs_inst_idx := SUC (EL z states).vs_inst_idx) /\
  c = <|cg_dst := w2n dj; cg_src := srcj; cg_length := 32;
         cg_inst_ids := [(EL j is).inst_id] ++
           (case dfg_get_def (dfg_build_function fn0) v of
              NONE => [] | SOME li => [li.inst_id])|> /\
  (j = r \/ (?g. MEM g gs /\ MEM (EL j is).inst_id g.cg_inst_ids /\
    rep_of_group is g = SOME ((EL r is).inst_id,g))) /\
  t = FOLDL (\st q. if MEM q (mm_local_pending_indices is gs r) then st else
    case mm_local_write_capture is H N q of NONE => st
    | SOME (d,bs) => write_memory_with_expansion d bs st)
    (H b) (MAP (\q. b+q) (COUNT_LIST (r-b))) /\
  B = (\i. if i < LENGTH t.vs_memory then EL i t.vs_memory else 0w) ==>
  mm_local_write_capture is H N j =
    SOME (c.cg_dst, mm_local_bytes B c.cg_src c.cg_length)
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `j <= LENGTH bb.bb_instructions` by (gvs[] >> decide_tac) >>
  `!u a. FLOOKUP s0.ss_loads u = SOME a ==>
    lookup_var u (EL (j-h) states) = SOME (mload a (EL (j-h) states))` by
    (match_mp_tac mm_local_live_load_post_phis >> simp[]) >>
  `lookup_var v (H j) = SOME (mload srcj (H j))` by metis_tac[] >>
  drule_all mm_local_pending_store_capture_replay >> simp[]
QED

Theorem mm_local_collection_discharge[local]:
  mm_local_pending cap js s t /\
  (!pre j mid k post d bs a cs.
    js = pre ++ [j] ++ mid ++ [k] ++ post /\ ~P j /\ P k /\
    cap j = SOME (d,bs) /\ cap k = SOME (a,cs) ==>
    mm_local_write_compatible d bs a cs) /\
  LIST_REL (\j w. cap j = SOME w) (FILTER P js) old /\
  LIST_REL (\j w. cap j = SOME w) (FILTER (\j. ~P j) js) rest /\
  (!a bs. MEM (a,bs) (old ++ [(d,payload)]) ==>
    dst <= a /\ a + LENGTH bs <= dst+len /\
    bs = mm_local_bytes B (src+(a-dst)) (LENGTH bs)) /\
  (!a. dst <= a /\ a < dst+len ==>
    ?q bs. MEM (q,bs) (old ++ [(d,payload)]) /\ q <= a /\ a < q + LENGTH bs) /\
  MAX_LIST (MAP (\(a,bs). a + LENGTH bs) (old ++ [(d,payload)])) = dst+len /\
  EVERY (\(a,bs). mm_local_write_compatible a bs d payload) rest /\
  s'.vs_memory = (write_memory_with_expansion d payload s).vs_memory /\
  t'.vs_memory = (write_memory_with_expansion dst (mm_local_bytes B src len) t).vs_memory ==>
  mm_local_pending cap (FILTER (\j. ~P j) js) s' t'
Proof
  strip_tac >>
  `!v. write_memory_with_expansion d payload
    (FOLDL (\st (a,bs). write_memory_with_expansion a bs st) v old) =
    write_memory_with_expansion dst (mm_local_bytes B src len) v` by
   (gen_tac >>
    drule_all mm_local_write_log_realize >>
    disch_then (qspec_then `v` mp_tac) >> simp[FOLDL_APPEND]) >>
  drule_all mm_local_pending_compatible_discharge_filter >> simp[]
QED

(* Positive retained-history update; realization is an explicit premise. *)
Theorem mm_local_retained_log_emit[local]:
  (!pre j mid k post. js = pre ++ [j] ++ mid ++ [k] ++ post /\ P j /\ ~P k ==>
    mm_local_write_compatible (FST (wr j)) (SND (wr j))
      (FST (wr k)) (SND (wr k))) /\
  u.vs_memory =
    (FOLDL (\st (d,bs). write_memory_with_expansion d bs st) mem0
      (MAP wr (FILTER (\j. ~P j) js))).vs_memory /\
  (!v. (write_memory_with_expansion dst payload v).vs_memory =
    (FOLDL (\st (d,bs). write_memory_with_expansion d bs st) v
      (MAP wr (FILTER P js) ++ [last])).vs_memory) /\
  u'.vs_memory = (write_memory_with_expansion dst payload u).vs_memory ==>
  u'.vs_memory =
    (FOLDL (\st (d,bs). write_memory_with_expansion d bs st) mem0
      (MAP wr js ++ [last])).vs_memory
Proof
  strip_tac >>
  `FOLDL (\st j. write_memory_with_expansion (FST (wr j)) (SND (wr j)) st) mem0 js =
   FOLDL (\st j. write_memory_with_expansion (FST (wr j)) (SND (wr j)) st)
    (FOLDL (\st j. write_memory_with_expansion (FST (wr j)) (SND (wr j)) st)
      mem0 (FILTER (\j. ~P j) js)) (FILTER P js)` by
    (qspecl_then [`js`,`mem0`] mp_tac
       (Q.INST [`P` |-> `\j. ~P j`] mm_local_write_log_compatible_partition) >>
     simp[ETA_THM] >> metis_tac[]) >>
  `!ws. (FOLDL (\st (d,bs). write_memory_with_expansion d bs st) u ws).vs_memory =
    (FOLDL (\st (d,bs). write_memory_with_expansion d bs st)
      (FOLDL (\st (d,bs). write_memory_with_expansion d bs st) mem0
        (MAP wr (FILTER (\j. ~P j) js))) ws).vs_memory` by
    (gen_tac >> irule venomWriteReplayPropsTheory.write_log_memory_cong >> simp[]) >>
  first_x_assum (qspec_then `MAP wr (FILTER P js) ++ [last]` mp_tac) >>
  gvs[FOLDL_APPEND, FOLDL_MAP, pairTheory.UNCURRY, combinTheory.o_DEF]
QED

Theorem mm_local_indexed_future_nonbarrier:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\ j < l /\ l <= R /\ R < LENGTH is /\
  ss = FOLDL (scan_inst (dfg_build_function fn0) mode) empty_scan_state (TAKE l is) /\
  (EL j is).inst_opcode IN {MSTORE; MCOPY; CALLDATACOPY; DLOADBYTES} /\
  MEM A ss.ss_copies /\ MEM (EL j is).inst_id A.cg_inst_ids /\
  MEM g (scan_block (dfg_build_function fn0) mode bb).ss_flushed /\
  MEM (EL j is).inst_id g.cg_inst_ids /\
  rep_of_group is g = SOME ((EL R is).inst_id,g) ==>
  scan_inst (dfg_build_function fn0) mode ss (EL l is) <> hard_barrier ss
Proof
  strip_tac >> spose_not_then assume_tac >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) is)` by
    (gvs[] >> drule_all mm_local_prefix_wf_id_distinct >> simp[]) >>
  `~MEM (EL R is).inst_id (MAP (\i. i.inst_id) (TAKE l is))` by
    (irule venomTransformStructurePropsTheory.future_id_not_prefix >> simp[]) >>
  `l < LENGTH is /\ j < LENGTH is` by decide_tac >>
  `bb.bb_instructions = TAKE l is ++ EL l is::DROP (SUC l) is` by
    (qspec_then `l` (qspec_then `is` mp_tac) rich_listTheory.TAKE_DROP_SUC >> simp[]) >>
  `MEM A (scan_block (dfg_build_function fn0) mode bb).ss_flushed` by
    (qspecl_then [`DROP (SUC l) is`, `scan_inst (dfg_build_function fn0) mode ss (EL l is)`]
      strip_assume_tac (Q.INST [`dfg` |-> `dfg_build_function fn0`, `mode` |-> `mode`]
        mm_local_fold_flushed_extension) >>
     gvs[scan_block_def, FOLDL_APPEND, hard_barrier_def, MEM_APPEND]) >>
  qpat_x_assum `bb.bb_instructions = _ ++ _` kall_tac >>
  `MEM (EL j is) bb.bb_instructions` by metis_tac[EL_MEM] >>
  `A = g` by
    (drule_at (Pat `mm_local_prefix _ _ _ _ = _`) mm_local_prefix_write_group_owner >>
     disch_then irule >> metis_tac[]) >>
  `MEM (EL R is).inst_id A.cg_inst_ids` by metis_tac[mm_local_rep_member] >>
  `MEM (EL R is).inst_id (MAP (\i. i.inst_id) (TAKE l is))` by
    (drule_at (Pat `mm_local_prefix _ _ _ _ = _`) mm_local_prefix_fragment_ids_before_cut >>
     disch_then irule >> simp[] >> conj_tac
     >- (qexists `DROP l is` >> simp[]) >>
     qexistsl [`A`,`mode`] >> gvs[MEM_APPEND]) >>
  metis_tac[]
QED

Theorem mm_local_captured_nonbarrier_selected[local]:
  mm_local_write_capture is H N l = SOME (b,bs) /\
  scan_inst dfg Mem2Mem ss (EL l is) <> hard_barrier ss ==>
  ((?dst src len. (EL l is).inst_opcode = MCOPY /\
      (EL l is).inst_operands = [Lit dst; Lit src; Lit len]) \/
   (?dst v src. (EL l is).inst_opcode = MSTORE /\
      (EL l is).inst_operands = [Lit dst; Var v] /\
      FLOOKUP ss.ss_loads v = SOME src))
Proof
  strip_tac >>
  `(EL l is).inst_opcode = MSTORE \/ (EL l is).inst_opcode = MCOPY` by
    (Cases_on `(EL l is).inst_opcode = MSTORE` >>
     Cases_on `(EL l is).inst_opcode = MCOPY` >>
     gvs[mm_local_write_capture_def]) >>
  qpat_x_assum `scan_inst _ _ _ _ <> _` mp_tac >>
  simp[scan_inst_def, mode_load_opcode_def, mode_copy_opcode_def] >>
  strip_tac >>
  Cases_on `(EL l is).inst_opcode = MSTORE` >> gvs[]
  >- (qpat_x_assum `scan_store _ _ _ _ <> _` mp_tac >>
      simp[scan_store_def] >> rpt BasicProvers.TOP_CASE_TAC >>
      gvs[operand_var_def, operand_lit_val_def] >>
      rename1 `(EL l is).inst_operands = [a1;a2]` >>
      Cases_on `a1` >> Cases_on `a2` >>
      gvs[operand_var_def, operand_lit_val_def]) >>
  qpat_x_assum `scan_bulk_copy _ _ _ <> _` mp_tac >>
  simp[scan_bulk_copy_def] >> rpt BasicProvers.TOP_CASE_TAC >>
  gvs[operand_lit_val_def] >>
  rename1 `(EL l is).inst_operands = [a1;a2;a3]` >>
  map_every Cases_on [`a1`,`a2`,`a3`] >> gvs[operand_lit_val_def]
QED

Theorem mm_local_final_captures_compatible_interval[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\ j < l /\ l <= R /\ R < LENGTH is /\
  l < N /\
  (!q. j <= q /\ q < l ==> (H (SUC q)).vs_memory =
    (case mm_local_write_capture is H N q of NONE => H q
     | SOME (d,bs) => write_memory_with_expansion d bs (H q)).vs_memory) /\
  MEM g (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
  MEM (EL j is).inst_id g.cg_inst_ids /\
  rep_of_group is g = SOME ((EL R is).inst_id,g) /\
  MEM h (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
  MEM (EL l is).inst_id h.cg_inst_ids /\
  (EL j is).inst_opcode IN {MSTORE; MCOPY; CALLDATACOPY; DLOADBYTES} /\
  (EL l is).inst_opcode IN {MSTORE; MCOPY; CALLDATACOPY; DLOADBYTES} /\
  (!v src. FLOOKUP (FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem)
      empty_scan_state (TAKE j is)).ss_loads v = SOME src ==>
    lookup_var v (H j) = SOME (mload src (H j))) /\
  (!v src. FLOOKUP (FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem)
      empty_scan_state (TAKE l is)).ss_loads v = SOME src ==>
    lookup_var v (H l) = SOME (mload src (H l))) /\
  mm_local_write_capture is H N j = SOME (a,p) /\
  mm_local_write_capture is H N l = SOME (b,qbytes) ==>
  mm_local_write_compatible a p b qbytes
Proof
  strip_tac >>
  `j < LENGTH is /\ l < LENGTH is` by decide_tac >>
  `((?dst src len. (EL j is).inst_opcode = MCOPY /\
      (EL j is).inst_operands = [Lit dst; Lit src; Lit len]) \/
    (?dst v src. (EL j is).inst_opcode = MSTORE /\
      (EL j is).inst_operands = [Lit dst; Var v] /\
      FLOOKUP (FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem)
        empty_scan_state (TAKE j is)).ss_loads v = SOME src))` by
    metis_tac[REWRITE_RULE [mode_copy_opcode_def] (Q.INST [`mode` |-> `Mem2Mem`] mm_local_final_write_birth)] >>
  `((?dst src len. (EL l is).inst_opcode = MCOPY /\
      (EL l is).inst_operands = [Lit dst; Lit src; Lit len]) \/
    (?dst v src. (EL l is).inst_opcode = MSTORE /\
      (EL l is).inst_operands = [Lit dst; Var v] /\
      FLOOKUP (FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem)
        empty_scan_state (TAKE l is)).ss_loads v = SOME src))` by
    metis_tac[REWRITE_RULE [mode_copy_opcode_def] (Q.INST [`mode` |-> `Mem2Mem`] mm_local_final_write_birth)] >>
  drule_at (Pat `mm_local_prefix _ _ _ _ = _`) mm_local_indexed_selected_captures_compatible_interval >>
  disch_then (drule_at (Pat `rep_of_group _ _ = _`)) >>
  simp[] >> disch_then irule >> gvs[] >>
  goal_assum (drule_at (Pat `mm_local_write_capture _ _ _ _ = SOME (a,p)`)) >>
  goal_assum (drule_at (Pat `mm_local_write_capture _ _ _ _ = SOME (b,qbytes)`)) >>
  gvs[] >> metis_tac[]
QED

Theorem mm_local_final_captures_compatible[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\ j < l /\ l <= R /\ R < LENGTH is /\
  l < N /\ mm_local_history is H N /\
  MEM g (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
  MEM (EL j is).inst_id g.cg_inst_ids /\
  rep_of_group is g = SOME ((EL R is).inst_id,g) /\
  MEM h (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
  MEM (EL l is).inst_id h.cg_inst_ids /\
  (EL j is).inst_opcode IN {MSTORE; MCOPY; CALLDATACOPY; DLOADBYTES} /\
  (EL l is).inst_opcode IN {MSTORE; MCOPY; CALLDATACOPY; DLOADBYTES} /\
  (!v src. FLOOKUP (FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem)
      empty_scan_state (TAKE j is)).ss_loads v = SOME src ==>
    lookup_var v (H j) = SOME (mload src (H j))) /\
  (!v src. FLOOKUP (FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem)
      empty_scan_state (TAKE l is)).ss_loads v = SOME src ==>
    lookup_var v (H l) = SOME (mload src (H l))) /\
  mm_local_write_capture is H N j = SOME (a,p) /\
  mm_local_write_capture is H N l = SOME (b,qbytes) ==>
  mm_local_write_compatible a p b qbytes
Proof
  strip_tac >>
  `j <= l /\ l < LENGTH is` by decide_tac >>
  `!q. j <= q /\ q < l ==> ?b. MEM b
    (mm_local_pending_indices is
      (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed (SUC q))` by
    (rpt strip_tac >> qexists `j` >>
     simp[mm_local_pending_indices_mem] >> qexistsl [`g`,`R`] >> gvs[]) >>
  `!q. j <= q /\ q < l ==> (H (SUC q)).vs_memory =
    (case mm_local_write_capture is H N q of NONE => H q
     | SOME (d,bs) => write_memory_with_expansion d bs (H q)).vs_memory` by
    (mp_tac (Q.INST [`a` |-> `j`, `r` |-> `l`,
       `gs` |-> `(scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed`]
       (SPEC_ALL mm_local_fixed_cut_capture_recurrence)) >> simp[]) >>
  mp_tac (SPEC_ALL mm_local_final_captures_compatible_interval) >> simp[]
QED

Theorem mm_local_retained_captures_compatible_interval[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\ j < l /\ l <= R /\ R < LENGTH is /\
  l < N /\
  (!q. j <= q /\ q < l ==> (H (SUC q)).vs_memory =
    (case mm_local_write_capture is H N q of NONE => H q
     | SOME (d,bs) => write_memory_with_expansion d bs (H q)).vs_memory) /\
  MEM g (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
  MEM (EL j is).inst_id g.cg_inst_ids /\
  rep_of_group is g = SOME ((EL R is).inst_id,g) /\
  (EL j is).inst_opcode IN {MSTORE; MCOPY; CALLDATACOPY; DLOADBYTES} /\
  (!v src. FLOOKUP (FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem)
      empty_scan_state (TAKE j is)).ss_loads v = SOME src ==>
    lookup_var v (H j) = SOME (mload src (H j))) /\
  (!v src. FLOOKUP (FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem)
      empty_scan_state (TAKE l is)).ss_loads v = SOME src ==>
    lookup_var v (H l) = SOME (mload src (H l))) /\
  mm_local_write_capture is H N j = SOME (a,p) /\
  mm_local_write_capture is H N l = SOME (b,qbytes) ==>
  mm_local_write_compatible a p b qbytes
Proof
  strip_tac >>
  `j < LENGTH is /\ l < LENGTH is` by decide_tac >>
  `((?dst src len. (EL j is).inst_opcode = MCOPY /\
      (EL j is).inst_operands = [Lit dst; Lit src; Lit len]) \/
    (?dst v src. (EL j is).inst_opcode = MSTORE /\
      (EL j is).inst_operands = [Lit dst; Var v] /\
      FLOOKUP (FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem)
        empty_scan_state (TAKE j is)).ss_loads v = SOME src))` by
    metis_tac[REWRITE_RULE [mode_copy_opcode_def] (Q.INST [`mode` |-> `Mem2Mem`] mm_local_final_write_birth)] >>
  qabbrev_tac `ss = FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem)
    empty_scan_state (TAKE l is)` >>
  `?A. MEM A ss.ss_copies /\ MEM (EL j is).inst_id A.cg_inst_ids` by
    (`ss = FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem)
        empty_scan_state (TAKE l is)` by simp[Abbr `ss`] >>
     qpat_x_assum `Abbrev _` kall_tac >>
     Cases_on `(EL j is).inst_opcode = MCOPY`
     >- (fs[] >> drule_all (REWRITE_RULE [mode_copy_opcode_def]
    (Q.INST [`mode` |-> `Mem2Mem`] mm_local_indexed_bulk_owner)) >> metis_tac[]) >>
     fs[] >> drule_at (Pat `mm_local_prefix _ _ _ _ = _`) mm_local_indexed_store_owner >>
     disch_then (drule_at (Pat `rep_of_group _ _ = _`)) >>
     simp[] >> metis_tac[]) >>
  `scan_inst (dfg_build_function fn0) Mem2Mem ss (EL l is) <> hard_barrier ss` by
    (`ss = FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem)
        empty_scan_state (TAKE l is)` by simp[Abbr `ss`] >>
     drule_all mm_local_indexed_future_nonbarrier >> simp[]) >>
  `((?dst src len. (EL l is).inst_opcode = MCOPY /\
      (EL l is).inst_operands = [Lit dst; Lit src; Lit len]) \/
    (?dst v src. (EL l is).inst_opcode = MSTORE /\
      (EL l is).inst_operands = [Lit dst; Var v] /\
      FLOOKUP ss.ss_loads v = SOME src))` by
    (drule_all mm_local_captured_nonbarrier_selected >> simp[]) >>
  drule_at (Pat `mm_local_prefix _ _ _ _ = _`) mm_local_indexed_selected_captures_compatible_interval >>
  disch_then (drule_at (Pat `rep_of_group _ _ = _`)) >>
  simp[] >> disch_then irule >>
  gvs[Abbr `ss`] >>
  goal_assum (drule_at (Pat `mm_local_write_capture _ _ _ _ = SOME (a,p)`)) >>
  goal_assum (drule_at (Pat `mm_local_write_capture _ _ _ _ = SOME (b,qbytes)`)) >>
  gvs[] >> metis_tac[]
QED

Theorem mm_local_retained_captures_compatible[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\ j < l /\ l <= R /\ R < LENGTH is /\
  l < N /\ mm_local_history is H N /\
  MEM g (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
  MEM (EL j is).inst_id g.cg_inst_ids /\
  rep_of_group is g = SOME ((EL R is).inst_id,g) /\
  (EL j is).inst_opcode IN {MSTORE; MCOPY; CALLDATACOPY; DLOADBYTES} /\
  (!v src. FLOOKUP (FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem)
      empty_scan_state (TAKE j is)).ss_loads v = SOME src ==>
    lookup_var v (H j) = SOME (mload src (H j))) /\
  (!v src. FLOOKUP (FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem)
      empty_scan_state (TAKE l is)).ss_loads v = SOME src ==>
    lookup_var v (H l) = SOME (mload src (H l))) /\
  mm_local_write_capture is H N j = SOME (a,p) /\
  mm_local_write_capture is H N l = SOME (b,qbytes) ==>
  mm_local_write_compatible a p b qbytes
Proof
  strip_tac >>
  `j <= l /\ l < LENGTH is` by decide_tac >>
  `!q. j <= q /\ q < l ==> ?b. MEM b
    (mm_local_pending_indices is
      (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed (SUC q))` by
    (rpt strip_tac >> qexists `j` >>
     simp[mm_local_pending_indices_mem] >> qexistsl [`g`,`R`] >> gvs[]) >>
  `!q. j <= q /\ q < l ==> (H (SUC q)).vs_memory =
    (case mm_local_write_capture is H N q of NONE => H q
     | SOME (d,bs) => write_memory_with_expansion d bs (H q)).vs_memory` by
    (mp_tac (Q.INST [`a` |-> `j`, `r` |-> `l`,
       `gs` |-> `(scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed`]
       (SPEC_ALL mm_local_fixed_cut_capture_recurrence)) >> simp[]) >>
  mp_tac (SPEC_ALL mm_local_retained_captures_compatible_interval) >> simp[]
QED

Theorem mm_local_canonical_pending_captures_compatible_interval[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\
  gs = (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
  r < LENGTH is /\
  (!q. j <= q /\ q < l ==> (H (SUC q)).vs_memory =
    (case mm_local_write_capture is H (SUC r) q of NONE => H q
     | SOME (d,bs) => write_memory_with_expansion d bs (H q)).vs_memory) /\
  cap = mm_local_write_capture is H (SUC r) /\
  j < l /\ MEM j (mm_local_pending_indices is gs r) /\
  MEM l (mm_local_pending_indices is gs r ++ [r]) /\
  (l = r ==> ?h. MEM h gs /\ rep_of_group is h = SOME ((EL r is).inst_id,h)) /\
  (!x v src. MEM x [j;l] /\
    FLOOKUP (FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem)
      empty_scan_state (TAKE x is)).ss_loads v = SOME src ==>
    lookup_var v (H x) = SOME (mload src (H x))) /\
  cap j = SOME (a,p) /\ cap l = SOME (b,qbytes) ==>
  mm_local_write_compatible a p b qbytes
Proof
  strip_tac >>
  `l <= r` by (gvs[mm_local_pending_indices_mem] >> decide_tac) >>
  `?h. MEM h gs /\ MEM (EL l is).inst_id h.cg_inst_ids /\
     (EL l is).inst_opcode IN {MSTORE; MCOPY; CALLDATACOPY; DLOADBYTES}` by
    (Cases_on `l = r`
     >- (fs[] >>
         `MEM (EL r is).inst_id h.cg_inst_ids` by metis_tac[mm_local_rep_member] >>
         drule_all mm_local_canonical_rep_write >> strip_tac >>
         qexists `h` >> gvs[]) >>
     gvs[mm_local_pending_indices_mem] >> metis_tac[]) >>
  qpat_x_assum `MEM j (mm_local_pending_indices is gs r)` mp_tac >>
  rewrite_tac[mm_local_pending_indices_mem] >> strip_tac >>
  rename1 `rep_of_group is g = SOME ((EL R is).inst_id,g)` >>
  `l < SUC r /\ l <= R` by decide_tac >>
  drule_at (Pat `mm_local_prefix _ _ _ _ = _`) mm_local_final_captures_compatible_interval >>
  disch_then (drule_at (Pat `rep_of_group _ _ = _`)) >>
  simp[] >> disch_then irule >>
  (conj_tac >- gvs[]) >>
  qexistsl [`H`, `SUC r`, `h`, `j`, `l`] >>
  gvs[] >> metis_tac[]
QED

Theorem mm_local_canonical_pending_captures_compatible[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\
  gs = (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
  r < LENGTH is /\ mm_local_history is H (SUC r) /\
  cap = mm_local_write_capture is H (SUC r) /\
  j < l /\ MEM j (mm_local_pending_indices is gs r) /\
  MEM l (mm_local_pending_indices is gs r ++ [r]) /\
  (l = r ==> ?h. MEM h gs /\ rep_of_group is h = SOME ((EL r is).inst_id,h)) /\
  (!x v src. MEM x [j;l] /\
    FLOOKUP (FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem)
      empty_scan_state (TAKE x is)).ss_loads v = SOME src ==>
    lookup_var v (H x) = SOME (mload src (H x))) /\
  cap j = SOME (a,p) /\ cap l = SOME (b,qbytes) ==>
  mm_local_write_compatible a p b qbytes
Proof
  strip_tac >>
  `l <= r` by (gvs[mm_local_pending_indices_mem] >> decide_tac) >>
  `!q. j <= q /\ q < l ==> ?b. MEM b (mm_local_pending_indices is gs (SUC q))` by
    (rpt strip_tac >> qexists `j` >>
     qpat_x_assum `MEM j (mm_local_pending_indices is gs r)` mp_tac >>
     pure_rewrite_tac[mm_local_pending_indices_mem] >> strip_tac >>
     rename1 `rep_of_group is owner = SOME ((EL owner_r is).inst_id,owner)` >>
     simp[] >> qexistsl [`owner`,`owner_r`] >> gvs[]) >>
  `!q. j <= q /\ q < l ==> (H (SUC q)).vs_memory =
    (case mm_local_write_capture is H (SUC r) q of NONE => H q
     | SOME (d,bs) => write_memory_with_expansion d bs (H q)).vs_memory` by
    (mp_tac (Q.INST [`a` |-> `j`, `r` |-> `l`, `N` |-> `SUC r`]
       (SPEC_ALL mm_local_fixed_cut_capture_recurrence)) >> gvs[]) >>
  mp_tac (SPEC_ALL mm_local_canonical_pending_captures_compatible_interval) >> simp[]
QED

Theorem mm_local_canonical_pending_crossings_interval[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\
  gs = (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
  r < LENGTH is /\
  (!q. (?j. MEM j (mm_local_pending_indices is gs r) /\ j <= q) /\ q < r ==>
    (H (SUC q)).vs_memory =
    (case mm_local_write_capture is H (SUC r) q of NONE => H q
     | SOME (d,bs) => write_memory_with_expansion d bs (H q)).vs_memory) /\
  cap = mm_local_write_capture is H (SUC r) /\
  js = mm_local_pending_indices is gs r /\
  MEM g gs /\ rep_of_group is g = SOME ((EL r is).inst_id,g) /\ 
  (!x v src. MEM x (js ++ [r]) /\
    FLOOKUP (FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem)
      empty_scan_state (TAKE x is)).ss_loads v = SOME src ==>
    lookup_var v (H x) = SOME (mload src (H x))) ==>
  (!pre j mid l post a p b bs.
    js = pre ++ [j] ++ mid ++ [l] ++ post /\
    cap j = SOME (a,p) /\ cap l = SOME (b,bs) ==>
    mm_local_write_compatible a p b bs) /\
  (!j a p b bs. MEM j js /\ cap j = SOME (a,p) /\ cap r = SOME (b,bs) ==>
    mm_local_write_compatible a p b bs)
Proof
  strip_tac >>
  `!j l a p b bs. j < l /\ MEM j js /\ MEM l (js ++ [r]) /\
    cap j = SOME (a,p) /\ cap l = SOME (b,bs) ==>
    mm_local_write_compatible a p b bs` by
    (rpt strip_tac >>
     drule_at (Pat `mm_local_prefix _ _ _ _ = _`)
       mm_local_canonical_pending_captures_compatible_interval >>
     simp[] >> disch_then irule >>
     qexistsl [`H`, `j`, `l`, `r`] >>
     `l <= r` by
       (qpat_x_assum `MEM l (js ++ [r])` mp_tac >>
        simp[MEM_APPEND] >> strip_tac >> gvs[] >>
        qpat_x_assum `MEM l (mm_local_pending_indices _ _ _)` mp_tac >>
        simp[mm_local_pending_indices_mem] >> rpt strip_tac >> decide_tac) >>
     gvs[] >>
     metis_tac[arithmeticTheory.LESS_EQ_TRANS, arithmeticTheory.LESS_LESS_EQ_TRANS]) >>
  conj_tac
  >- (rpt strip_tac >>
      `SORTED $< js` by metis_tac[mm_local_pending_indices_order] >>
      `j < l` by
        (qpat_x_assum `SORTED $< js` mp_tac >>
         simp[sortingTheory.SORTED_APPEND, relationTheory.transitive_def] >>
         metis_tac[MEM_APPEND, MEM]) >>
      first_x_assum irule >> simp[] >> metis_tac[MEM_APPEND, MEM]) >>
  rpt strip_tac >> `j < r` by metis_tac[mm_local_pending_indices_mem] >>
  first_x_assum irule >> simp[] >> metis_tac[]
QED

Theorem mm_local_canonical_pending_crossings[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\
  gs = (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
  r < LENGTH is /\ mm_local_history is H (SUC r) /\
  cap = mm_local_write_capture is H (SUC r) /\
  js = mm_local_pending_indices is gs r /\
  MEM g gs /\ rep_of_group is g = SOME ((EL r is).inst_id,g) /\
  (!x v src. MEM x (js ++ [r]) /\
    FLOOKUP (FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem)
      empty_scan_state (TAKE x is)).ss_loads v = SOME src ==>
    lookup_var v (H x) = SOME (mload src (H x))) ==>
  (!pre j mid l post a p b bs.
    js = pre ++ [j] ++ mid ++ [l] ++ post /\
    cap j = SOME (a,p) /\ cap l = SOME (b,bs) ==>
    mm_local_write_compatible a p b bs) /\
  (!j a p b bs. MEM j js /\ cap j = SOME (a,p) /\ cap r = SOME (b,bs) ==>
    mm_local_write_compatible a p b bs)
Proof
  strip_tac >>
  `!q. (?j. MEM j (mm_local_pending_indices is gs r) /\ j <= q) /\ q < r ==>
    (H (SUC q)).vs_memory =
    (case mm_local_write_capture is H (SUC r) q of NONE => H q
     | SOME (d,bs) => write_memory_with_expansion d bs (H q)).vs_memory` by
    (rpt strip_tac >>
     `?b. MEM b (mm_local_pending_indices is gs (SUC q))` by
       (qexists `j` >>
        qpat_x_assum `MEM j (mm_local_pending_indices is gs r)` mp_tac >>
        pure_rewrite_tac[mm_local_pending_indices_mem] >> strip_tac >>
        rename1 `rep_of_group is owner = SOME ((EL owner_r is).inst_id,owner)` >>
        simp[] >> qexistsl [`owner`,`owner_r`] >> gvs[]) >>
     `b <= q /\ q < SUC q /\ SUC q < LENGTH is /\ SUC q < SUC r` by
       (gvs[mm_local_pending_indices_mem] >> decide_tac) >>
     drule_all mm_local_live_segment_capture_recurrence >> simp[]) >>
  mp_tac (SPEC_ALL mm_local_canonical_pending_crossings_interval) >> simp[]
QED

Theorem mm_local_capture_fold_emit[local]:
  SORTED $< (xs:num list) /\
  (!j l d bs e cs. MEM j xs /\ MEM l xs /\ j < l /\ P j /\ ~P l /\
    cap j = SOME (d,bs) /\ cap l = SOME (e,cs) ==>
    mm_local_write_compatible d bs e cs) /\
  u.vs_memory = (FOLDL (\st j. case cap j of NONE => st
      | SOME (d,bs) => write_memory_with_expansion d bs st)
    mem0 (FILTER (\j. ~P j) xs)).vs_memory /\
  cap r = SOME last /\
  (!v. write_memory_with_expansion dst payload v =
    FOLDL (\st j. case cap j of NONE => st
      | SOME (d,bs) => write_memory_with_expansion d bs st) v (FILTER P xs ++ [r])) /\
  u'.vs_memory = (write_memory_with_expansion dst payload u).vs_memory ==>
  u'.vs_memory = (FOLDL (\st j. case cap j of NONE => st
      | SOME (d,bs) => write_memory_with_expansion d bs st) mem0 (xs ++ [r])).vs_memory
Proof
  strip_tac >>
  `SORTED $< (FILTER (\j. IS_SOME (cap j)) xs)` by
    (irule sortingTheory.SORTED_FILTER >> simp[relationTheory.transitive_def] >> decide_tac) >>
  `!pre j mid l post. FILTER (\j. IS_SOME (cap j)) xs =
      pre ++ [j] ++ mid ++ [l] ++ post /\ P j /\ ~P l ==>
    mm_local_write_compatible (FST ((THE o cap) j)) (SND ((THE o cap) j))
      (FST ((THE o cap) l)) (SND ((THE o cap) l))` by
    (rpt strip_tac >>
     `j < l` by
       (qpat_x_assum `SORTED $< (FILTER _ xs)` mp_tac >>
        simp[sortingTheory.SORTED_APPEND, relationTheory.transitive_def] >>
        metis_tac[MEM_APPEND, MEM]) >>
     `MEM j (FILTER (\j. IS_SOME (cap j)) xs) /\
      MEM l (FILTER (\j. IS_SOME (cap j)) xs)` by simp[] >>
     `MEM j xs /\ IS_SOME (cap j) /\ MEM l xs /\ IS_SOME (cap l)` by
       fs[MEM_FILTER] >>
     Cases_on `cap j` >> Cases_on `cap l` >> gvs[] >>
     rename1 `cap j = SOME wj` >> rename1 `cap l = SOME wl` >>
     PairCases_on `wj` >> PairCases_on `wl` >> gvs[] >> metis_tac[]) >>
  `u.vs_memory = (FOLDL (\st (d,bs). write_memory_with_expansion d bs st) mem0
    (MAP (THE o cap) (FILTER (\j. ~P j) (FILTER (\j. IS_SOME (cap j)) xs)))).vs_memory` by
    (qpat_x_assum `u.vs_memory = _` mp_tac >>
     rewrite_tac[GSYM rich_listTheory.FOLDL_FILTER, venomWriteReplayPropsTheory.capture_fold, FILTER_FILTER] >>
     simp[CONJ_COMM]) >>
  `!v. (write_memory_with_expansion dst payload v).vs_memory =
    (FOLDL (\st (d,bs). write_memory_with_expansion d bs st) v
      (MAP (THE o cap) (FILTER P (FILTER (\j. IS_SOME (cap j)) xs)) ++ [last])).vs_memory` by
    (gen_tac >> first_x_assum (qspec_then `v` mp_tac) >>
     simp[venomWriteReplayPropsTheory.capture_fold, FILTER_APPEND, MAP_APPEND, FILTER_FILTER, CONJ_COMM]) >>
  drule_all mm_local_retained_log_emit >>
  simp[venomWriteReplayPropsTheory.capture_fold, FILTER_APPEND, MAP_APPEND]
QED

Theorem mm_local_epoch_pending_slice[local]:
  a = mm_local_epoch_start is gs r ==>
  FILTER (\j. MEM j (mm_local_pending_indices is gs r))
    (MAP (\q. a+q) (COUNT_LIST (r-a))) = mm_local_pending_indices is gs r
Proof
  strip_tac >>
  `SORTED $< (MAP (\q. a+q) (COUNT_LIST (r-a)))` by
    (pure_rewrite_tac[rich_listTheory.MAP_COUNT_LIST] >>
     CONV_TAC (DEPTH_CONV ETA_CONV) >>
     MATCH_ACCEPT_TAC sortingTheory.SORTED_GENLIST_PLUS) >>
  `SORTED $< (FILTER (\j. MEM j (mm_local_pending_indices is gs r))
      (MAP (\q. a+q) (COUNT_LIST (r-a))))` by
    (irule sortingTheory.SORTED_FILTER >> simp[relationTheory.transitive_def] >> decide_tac) >>
  irule (Q.ISPEC `$< : num -> num -> bool` sortingTheory.SORTED_ALL_DISTINCT_LIST_TO_SET_EQ) >>
  simp[relationTheory.transitive_def, relationTheory.antisymmetric_def] >>
  `SORTED $< (mm_local_pending_indices is gs r)` by
    metis_tac[mm_local_pending_indices_order] >>
  `!xs:num list. SORTED $< xs ==> ALL_DISTINCT xs` by
    (mp_tac (Q.ISPEC `$< : num -> num -> bool` (GEN_ALL sortingTheory.SORTED_ALL_DISTINCT)) >>
     simp[relationTheory.irreflexive_def, arithmeticTheory.transitive_LESS]) >>
  gvs[] >> simp[pred_setTheory.EXTENSION, MEM_FILTER, MEM_MAP, MEM_COUNT_LIST] >>
  gen_tac >> eq_tac >- metis_tac[] >> strip_tac >> simp[] >>
  `mm_local_epoch_start is gs r <= x /\ x < r` by
    metis_tac[mm_local_epoch_start_pending_bound, mm_local_pending_indices_mem] >>
  qexists `x-mm_local_epoch_start is gs r` >> simp[]
QED

Theorem mm_local_canonical_pending_discharge_interval[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\
  gs = (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
  r < LENGTH is /\ MEM g gs /\
  (!q. a <= q /\ q < r ==> (H (SUC q)).vs_memory =
    (case mm_local_write_capture is H (SUC r) q of NONE => H q
     | SOME (d,bs) => write_memory_with_expansion d bs (H q)).vs_memory) /\
  rep_of_group is g = SOME ((EL r is).inst_id,g) /\
  cap = mm_local_write_capture is H (SUC r) /\
  js = mm_local_pending_indices is gs r /\
  (!j v src. MEM j (js ++ [r]) /\
    FLOOKUP (FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem)
      empty_scan_state (TAKE j is)).ss_loads v = SOME src ==>
    lookup_var v (H j) = SOME (mload src (H j))) /\
  a = mm_local_epoch_start is gs r /\
  u = FOLDL (\st q. if MEM q js then st else
    case cap q of NONE => st
    | SOME (d,bs) => write_memory_with_expansion d bs st)
    (H a) (MAP (\q. a+q) (COUNT_LIST (r-a))) /\
  t.vs_memory = u.vs_memory /\ mm_local_pending cap js s t /\
  cap r = SOME (d,payload) /\
  s'.vs_memory = (write_memory_with_expansion d payload s).vs_memory /\
  t'.vs_memory = (write_memory_with_expansion g.cg_dst
    (read_memory g.cg_src g.cg_length t) t).vs_memory ==>
  mm_local_pending cap (FILTER (\j. mm_local_rep_index is gs j <> r) js) s' t'
Proof
  strip_tac >>
  `(!pre j mid l post a p b bs.
    js = pre ++ [j] ++ mid ++ [l] ++ post /\
    cap j = SOME (a,p) /\ cap l = SOME (b,bs) ==>
    mm_local_write_compatible a p b bs) /\
   (!j a p b bs. MEM j js /\ cap j = SOME (a,p) /\ cap r = SOME (b,bs) ==>
    mm_local_write_compatible a p b bs)` by
    (irule mm_local_canonical_pending_crossings_interval >>
     goal_assum (drule_at Any) >>
     goal_assum (drule_at (Pat `mm_local_prefix _ _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `rep_of_group _ _ = _`)) >>
     `!j. MEM j js ==> a <= j` by metis_tac[mm_local_epoch_start_pending_bound] >>
     gvs[] >> rpt strip_tac >>
     first_x_assum irule >> simp[] >>
     metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  `!j. MEM j js ==> cap j = SOME (THE (cap j))` by
    (qpat_x_assum `mm_local_pending cap js s t` mp_tac >>
     pure_rewrite_tac[mm_local_pending_def] >> strip_tac >> rpt strip_tac >>
     drule_all listTheory.LIST_REL_MEM_IMP >> strip_tac >> gvs[]) >>
  `!v. FOLDL (\st (d,bs). write_memory_with_expansion d bs st) v
    (MAP (THE o cap) ((FILTER (\j. mm_local_rep_index is gs j = r) js) ++ [r])) =
    write_memory_with_expansion g.cg_dst (read_memory g.cg_src g.cg_length t) v` by
    (drule_at (Pat `mm_local_prefix _ _ _ _ = _`)
       (cj 2 mm_local_canonical_due_log_payload_interval) >>
     disch_then (drule_at (Pat `rep_of_group _ _ = _`)) >>
     disch_then irule >>
     rpt (conj_tac >- first_assum ACCEPT_TAC) >>
     reverse conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl [`H`, `a`, `cap`,
       `FILTER (\j. mm_local_rep_index is gs j = r) js`, `gs`, `u`] >>
     gvs[MEM_FILTER] >> metis_tac[]) >>
  irule (BETA_RULE (Q.INST [`P` |-> `(\j. mm_local_rep_index is gs j = r)`]
    (SPEC_ALL (INST_TYPE [alpha |-> ``:num``] mm_local_pending_compatible_discharge_filter)))) >>
  conj_tac >- metis_tac[] >>
  qexistsl [`d`, `g.cg_dst`, `read_memory g.cg_src g.cg_length t`,
    `MAP (THE o cap) (FILTER (\j. mm_local_rep_index is gs j = r) js)`,
    `payload`, `MAP (THE o cap) (FILTER (\j. mm_local_rep_index is gs j <> r) js)`,
    `s`, `t`] >>
  conj_tac
  >- (qpat_x_assum `!v. FOLDL _ v _ = _` mp_tac >>
      simp[MAP_APPEND, FOLDL_APPEND]) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac
  >- (pure_rewrite_tac[EVERY_MAP, EVERY_MEM, MEM_FILTER] >>
      qx_gen_tac `j` >> strip_tac >>
      `cap j = SOME (THE (cap j))` by metis_tac[] >>
      Cases_on `THE (cap j)` >> gvs[] >> metis_tac[]) >>
  conj_tac
  >- (pure_rewrite_tac[LIST_REL_MAP2] >>
      irule EVERY2_refl >> pure_rewrite_tac[MEM_FILTER] >>
      rpt strip_tac >> gvs[]) >>
  conj_tac
  >- (pure_rewrite_tac[LIST_REL_MAP2] >>
      irule EVERY2_refl >> pure_rewrite_tac[MEM_FILTER] >>
      rpt strip_tac >> gvs[]) >>
  first_assum ACCEPT_TAC
QED

Theorem mm_local_canonical_pending_discharge[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\
  gs = (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
  r < LENGTH is /\ mm_local_history is H (SUC r) /\ MEM g gs /\
  rep_of_group is g = SOME ((EL r is).inst_id,g) /\
  cap = mm_local_write_capture is H (SUC r) /\
  js = mm_local_pending_indices is gs r /\
  (!j v src. MEM j (js ++ [r]) /\
    FLOOKUP (FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem)
      empty_scan_state (TAKE j is)).ss_loads v = SOME src ==>
    lookup_var v (H j) = SOME (mload src (H j))) /\
  a = mm_local_epoch_start is gs r /\
  u = FOLDL (\st q. if MEM q js then st else
    case cap q of NONE => st
    | SOME (d,bs) => write_memory_with_expansion d bs st)
    (H a) (MAP (\q. a+q) (COUNT_LIST (r-a))) /\
  t.vs_memory = u.vs_memory /\ mm_local_pending cap js s t /\
  cap r = SOME (d,payload) /\
  s'.vs_memory = (write_memory_with_expansion d payload s).vs_memory /\
  t'.vs_memory = (write_memory_with_expansion g.cg_dst
    (read_memory g.cg_src g.cg_length t) t).vs_memory ==>
  mm_local_pending cap (FILTER (\j. mm_local_rep_index is gs j <> r) js) s' t'
Proof
  strip_tac >>
  `!q. a <= q /\ q < r ==> ?b. MEM b (mm_local_pending_indices is gs (SUC q))` by
    metis_tac[mm_local_epoch_start_nonempty] >>
  `a <= r` by metis_tac[mm_local_epoch_start_bound] >>
  `!q. a <= q /\ q < r ==> (H (SUC q)).vs_memory =
    (case mm_local_write_capture is H (SUC r) q of NONE => H q
     | SOME (d,bs) => write_memory_with_expansion d bs (H q)).vs_memory` by
    (mp_tac (Q.INST [`a` |-> `a`, `r` |-> `r`, `N` |-> `SUC r`]
       (SPEC_ALL mm_local_fixed_cut_capture_recurrence)) >> simp[]) >>
  mp_tac (SPEC_ALL mm_local_canonical_pending_discharge_interval) >> simp[] >> metis_tac[]
QED

Theorem mm_local_canonical_retained_emit_interval[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\
  gs = (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
  r < LENGTH is /\ MEM g gs /\
  (!q. a <= q /\ q < r ==> (H (SUC q)).vs_memory =
    (case mm_local_write_capture is H (SUC r) q of NONE => H q
     | SOME (d,bs) => write_memory_with_expansion d bs (H q)).vs_memory) /\
  rep_of_group is g = SOME ((EL r is).inst_id,g) /\
  cap = mm_local_write_capture is H (SUC r) /\
  js = mm_local_pending_indices is gs r /\
  a = mm_local_epoch_start is gs r /\
  (!j v src. a <= j /\ j <= r /\
    FLOOKUP (FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem)
      empty_scan_state (TAKE j is)).ss_loads v = SOME src ==>
    lookup_var v (H j) = SOME (mload src (H j))) /\
  u = FOLDL (\st q. if MEM q js then st else
    case cap q of NONE => st | SOME (d,bs) => write_memory_with_expansion d bs st)
    (H a) (MAP (\q. a+q) (COUNT_LIST (r-a))) /\
  t.vs_memory = u.vs_memory /\
  t'.vs_memory = (write_memory_with_expansion g.cg_dst
    (read_memory g.cg_src g.cg_length t) t).vs_memory ==>
  t'.vs_memory = (FOLDL (\st q.
    if MEM q (FILTER (\j. mm_local_rep_index is gs j <> r) js) then st else
    case cap q of NONE => st | SOME (d,bs) => write_memory_with_expansion d bs st)
    (H a) (MAP (\q. a+q) (COUNT_LIST (SUC r-a)))).vs_memory
Proof
  strip_tac >>
  qabbrev_tac `due = FILTER (\j. mm_local_rep_index is gs j = r) js` >>
  qabbrev_tac `rest = FILTER (\j. mm_local_rep_index is gs j <> r) js` >>
  qabbrev_tac `epoch_js = MAP (\q. a+q) (COUNT_LIST (r-a))` >>
  `a <= r` by metis_tac[mm_local_epoch_start_bound] >>
  `FILTER (\j. MEM j js) epoch_js = js` by
    (drule mm_local_epoch_pending_slice >> simp[Abbr `epoch_js`]) >>
  `!j. MEM j (due ++ [r]) ==> a <= j /\ j <= r` by
    (gen_tac >> disch_tac >> Cases_on `j = r` >- gvs[] >>
     `MEM j js` by fs[Abbr `due`, MEM_FILTER] >>
     conj_tac
     >- (irule mm_local_epoch_start_pending_bound >> metis_tac[]) >>
     qpat_x_assum `MEM j js` mp_tac >>
     simp[mm_local_pending_indices_mem] >> rpt strip_tac >> decide_tac) >>
  `!j. MEM j (due ++ [r]) ==> ?d bs. cap j = SOME (d,bs)` by
    (rpt strip_tac >>
     `a <= j /\ j <= r` by metis_tac[] >>
     mp_tac (Q.INST [`s0` |-> `FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem)
       empty_scan_state (TAKE j is)`] (SPEC_ALL mm_local_canonical_due_index_payload_interval)) >>
     simp[Abbr `due`, Abbr `epoch_js`] >> metis_tac[]) >>
  `!v. FOLDL (\st (d,bs). write_memory_with_expansion d bs st) v
      (MAP (THE o cap) (due ++ [r])) =
    write_memory_with_expansion g.cg_dst (read_memory g.cg_src g.cg_length t) v` by
    (drule_at (Pat `mm_local_prefix _ _ _ _ = _`)
       (cj 2 mm_local_canonical_due_log_payload_interval) >>
     disch_then (drule_at (Pat `rep_of_group _ _ = _`)) >>
     simp[Abbr `due`, Abbr `epoch_js`] >>
     disch_then irule >>
     reverse conj_tac >- gvs[arithmeticTheory.ADD_COMM] >>
     rpt strip_tac >> first_x_assum irule >>
     gvs[] >> metis_tac[MEM_APPEND, MEM]) >>
  `!j. MEM j due ==> MEM (EL j is).inst_id g.cg_inst_ids /\
    (EL j is).inst_opcode IN {MSTORE; MCOPY; CALLDATACOPY; DLOADBYTES}` by
    (`due = FILTER (\j. j < r /\
        (EL j is).inst_opcode IN {MSTORE; MCOPY; CALLDATACOPY; DLOADBYTES} /\
        MEM (EL j is).inst_id g.cg_inst_ids) (COUNT_LIST r)` by
       (irule mm_local_canonical_due_group >> simp[Abbr `due`] >> metis_tac[]) >>
     simp[MEM_FILTER]) >>
  `!j l d bs e cs. MEM j epoch_js /\ MEM l epoch_js /\ j < l /\
    MEM j due /\ ~MEM l due /\ cap j = SOME (d,bs) /\ cap l = SOME (e,cs) ==>
    mm_local_write_compatible d bs e cs` by
    (rpt strip_tac >>
     `a <= j /\ j < r /\ a <= l /\ l < r` by
       (fs[Abbr `epoch_js`, MEM_MAP, MEM_COUNT_LIST] >> gvs[]) >>
     drule_at (Pat `mm_local_prefix _ _ _ _ = _`) mm_local_retained_captures_compatible_interval >>
     disch_then (drule_at (Pat `rep_of_group _ _ = _`)) >>
     simp[] >> disch_then irule >>
     conj_tac >- gvs[] >> qexistsl [`H`, `SUC r`, `j`, `l`] >>
     gvs[] >> rpt conj_tac >> rpt strip_tac >>
     metis_tac[arithmeticTheory.LESS_IMP_LESS_OR_EQ,
       arithmeticTheory.LESS_EQ_TRANS, arithmeticTheory.LESS_TRANS]) >>
  qabbrev_tac `kept = FILTER (\j. ~MEM j rest) epoch_js` >>
  `FILTER (\j. MEM j due) kept = due` by
    (simp[NoAsms, Abbr `kept`, Abbr `due`, Abbr `rest`, FILTER_FILTER] >>
     qpat_x_assum `FILTER _ epoch_js = js` (fn th =>
       GEN_REWRITE_TAC (RHS_CONV o RAND_CONV) empty_rewrites [GSYM th]) >>
     simp[NoAsms, FILTER_FILTER] >>
     AP_THM_TAC >> AP_TERM_TAC >>
     simp[NoAsms, FUN_EQ_THM, MEM_FILTER] >> metis_tac[]) >>
  `FILTER (\j. ~MEM j due) kept = FILTER (\j. ~MEM j js) epoch_js` by
    (simp[Abbr `kept`, Abbr `due`, Abbr `rest`, FILTER_FILTER] >>
     AP_THM_TAC >> AP_TERM_TAC >> simp[NoAsms, FUN_EQ_THM, MEM_FILTER] >>
     gen_tac >> Cases_on `mm_local_rep_index is gs j = r` >> gvs[]) >>
  `SORTED $< kept` by
    (simp[NoAsms, Abbr `kept`] >> irule sortingTheory.SORTED_FILTER >>
     simp[relationTheory.transitive_def] >>
     simp[NoAsms, Abbr `epoch_js`] >>
     pure_rewrite_tac[rich_listTheory.MAP_COUNT_LIST] >>
     CONV_TAC (DEPTH_CONV ETA_CONV) >>
     MATCH_ACCEPT_TAC sortingTheory.SORTED_GENLIST_PLUS) >>
  `t'.vs_memory = (FOLDL (\st j. case cap j of NONE => st
    | SOME (d,bs) => write_memory_with_expansion d bs st) (H a) (kept ++ [r])).vs_memory` by
    (irule (Q.INST [`P` |-> `\j. MEM j due`] mm_local_capture_fold_emit) >>
     reverse conj_tac >- metis_tac[MEM_APPEND, MEM] >>
     qexistsl [`g.cg_dst`, `due`, `read_memory g.cg_src g.cg_length t`, `t`] >>
     simp[NoAsms] >> rpt conj_tac
     >- (fs[Abbr `kept`, MEM_FILTER] >> metis_tac[])
     >- (`FILTER (\j. IS_SOME (cap j)) (due ++ [r]) = due ++ [r]` by
           (pure_rewrite_tac[FILTER_EQ_ID, EVERY_MEM] >> qx_gen_tac `j` >> disch_tac >>
            `?d bs. cap j = SOME (d,bs)` by metis_tac[] >> simp[]) >>
         simp[NoAsms] >> gen_tac >> rewrite_tac[venomWriteReplayPropsTheory.capture_fold] >>
         gvs[])
     >- (simp[] >> qpat_x_assum `t.vs_memory = _` mp_tac >>
         qpat_x_assum `u = _` SUBST1_TAC >>
         rewrite_tac[rich_listTheory.FOLDL_FILTER] >> disch_tac >>
         AP_TERM_TAC >> AP_THM_TAC >> AP_THM_TAC >> AP_TERM_TAC >>
         simp[NoAsms, FUN_EQ_THM] >> rpt gen_tac >> IF_CASES_TAC >> simp[])
     >- first_assum ACCEPT_TAC) >>
  `MAP (\q. a+q) (COUNT_LIST (SUC r-a)) = epoch_js ++ [r]` by
    (`SUC r-a = SUC (r-a)` by decide_tac >>
     qpat_x_assum `SUC r-a = _` (fn th => pure_rewrite_tac[th]) >>
     simp[NoAsms, Abbr `epoch_js`, rich_listTheory.COUNT_LIST_SNOC,
       MAP_SNOC, SNOC_APPEND] >> `a + (r-a) = r` by decide_tac >> simp[]) >>
  `~MEM r rest` by
    (simp[Abbr `rest`, MEM_FILTER, mm_local_pending_indices_def, MEM_COUNT_LIST]) >>
  `kept ++ [r] = FILTER (\j. ~MEM j rest) (epoch_js ++ [r])` by
    (simp[NoAsms, Abbr `kept`, FILTER_APPEND] >> simp[]) >>
  qpat_x_assum `MAP _ (COUNT_LIST (SUC r-a)) = _` (fn th => pure_rewrite_tac[th]) >>
  qpat_x_assum `t'.vs_memory = (FOLDL _ _ _) .vs_memory` mp_tac >>
  qpat_x_assum `kept ++ [r] = _` (fn th => pure_rewrite_tac[th]) >>
  rewrite_tac[rich_listTheory.FOLDL_FILTER] >>
  `!st q. (if ~MEM q rest then
      (case cap q of NONE => st | SOME (d,bs) => write_memory_with_expansion d bs st)
      else st) = (if MEM q rest then st else
      case cap q of NONE => st | SOME (d,bs) => write_memory_with_expansion d bs st)` by
    (rpt gen_tac >> Cases_on `MEM q rest` >> simp[]) >>
  gvs[]
QED

Theorem mm_local_canonical_retained_emit[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\
  gs = (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
  r < LENGTH is /\ mm_local_history is H (SUC r) /\ MEM g gs /\
  rep_of_group is g = SOME ((EL r is).inst_id,g) /\
  cap = mm_local_write_capture is H (SUC r) /\
  js = mm_local_pending_indices is gs r /\
  a = mm_local_epoch_start is gs r /\
  (!j v src. a <= j /\ j <= r /\
    FLOOKUP (FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem)
      empty_scan_state (TAKE j is)).ss_loads v = SOME src ==>
    lookup_var v (H j) = SOME (mload src (H j))) /\
  u = FOLDL (\st q. if MEM q js then st else
    case cap q of NONE => st | SOME (d,bs) => write_memory_with_expansion d bs st)
    (H a) (MAP (\q. a+q) (COUNT_LIST (r-a))) /\
  t.vs_memory = u.vs_memory /\
  t'.vs_memory = (write_memory_with_expansion g.cg_dst
    (read_memory g.cg_src g.cg_length t) t).vs_memory ==>
  t'.vs_memory = (FOLDL (\st q.
    if MEM q (FILTER (\j. mm_local_rep_index is gs j <> r) js) then st else
    case cap q of NONE => st | SOME (d,bs) => write_memory_with_expansion d bs st)
    (H a) (MAP (\q. a+q) (COUNT_LIST (SUC r-a)))).vs_memory
Proof
  strip_tac >>
  `!q. a <= q /\ q < r ==> ?b. MEM b (mm_local_pending_indices is gs (SUC q))` by
    metis_tac[mm_local_epoch_start_nonempty] >>
  `a <= r` by metis_tac[mm_local_epoch_start_bound] >>
  `!q. a <= q /\ q < r ==> (H (SUC q)).vs_memory =
    (case mm_local_write_capture is H (SUC r) q of NONE => H q
     | SOME (d,bs) => write_memory_with_expansion d bs (H q)).vs_memory` by
    (mp_tac (Q.INST [`a` |-> `a`, `r` |-> `r`, `N` |-> `SUC r`]
       (SPEC_ALL mm_local_fixed_cut_capture_recurrence)) >> simp[]) >>
  mp_tac (SPEC_ALL mm_local_canonical_retained_emit_interval) >> simp[] >> metis_tac[]
QED

Theorem mm_local_canonical_retained_renew_interval[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\
  gs = (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
  r < LENGTH is /\ MEM g gs /\
  (!q. a <= q /\ q < r ==> (H (SUC q)).vs_memory =
    (case mm_local_write_capture is H (SUC r) q of NONE => H q
     | SOME (d,bs) => write_memory_with_expansion d bs (H q)).vs_memory) /\
  (?d bs. cap r = SOME (d,bs) /\
    (H (SUC r)).vs_memory = (write_memory_with_expansion d bs (H r)).vs_memory) /\
  rep_of_group is g = SOME ((EL r is).inst_id,g) /\
  cap = mm_local_write_capture is H (SUC r) /\
  js = mm_local_pending_indices is gs r /\
  a = mm_local_epoch_start is gs r /\
  (!j v src. a <= j /\ j <= r /\
    FLOOKUP (FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem)
      empty_scan_state (TAKE j is)).ss_loads v = SOME src ==>
    lookup_var v (H j) = SOME (mload src (H j))) /\
  u = FOLDL (\st q. if MEM q js then st else
    case cap q of NONE => st | SOME (d,bs) => write_memory_with_expansion d bs st)
    (H a) (MAP (\q. a+q) (COUNT_LIST (r-a))) /\
  t.vs_memory = u.vs_memory /\ mm_local_pending cap js (H r) t /\
  t'.vs_memory = (write_memory_with_expansion g.cg_dst
    (read_memory g.cg_src g.cg_length t) t).vs_memory /\
  a' = mm_local_epoch_start is gs (SUC r) ==>
  t'.vs_memory = (FOLDL (\st q.
    if MEM q (mm_local_pending_indices is gs (SUC r)) then st else
    case cap q of NONE => st | SOME (d,bs) => write_memory_with_expansion d bs st)
    (H a') (MAP (\q. a'+q) (COUNT_LIST (SUC r-a')))).vs_memory
Proof
  strip_tac >>
  `~MEM r (mm_local_pending_indices is gs (SUC r))` by
    (strip_tac >>
     `MEM (EL r is).inst_id g.cg_inst_ids` by metis_tac[mm_local_rep_member] >>
     qpat_x_assum `MEM r (mm_local_pending_indices _ _ _)`
       (strip_assume_tac o REWRITE_RULE [mm_local_pending_indices_mem]) >>
     rename1 `rep_of_group is h = SOME ((EL R is).inst_id,h)` >>
     `r = R` by metis_tac[mm_local_write_rep_unique] >> decide_tac) >>
  `FILTER (\j. mm_local_rep_index is gs j <> r) js =
    mm_local_pending_indices is gs (SUC r)` by
    (`FILTER (\j. j < r) (mm_local_pending_indices is gs (SUC r)) =
        mm_local_pending_indices is gs (SUC r)` by
       (pure_rewrite_tac[FILTER_EQ_ID, EVERY_MEM] >> qx_gen_tac `j` >> strip_tac >>
        `j <> r` by metis_tac[] >>
        qpat_x_assum `MEM j (mm_local_pending_indices _ _ _)` mp_tac >>
        rewrite_tac[mm_local_pending_indices_mem] >> rpt strip_tac >> simp[]) >>
     `!j. MEM j js ==> r <= mm_local_rep_index is gs j` by
       (qx_gen_tac `j` >> strip_tac >>
        qpat_x_assum `js = _` SUBST_ALL_TAC >>
        qpat_x_assum `MEM j _` mp_tac >>
        rewrite_tac[mm_local_pending_indices_mem] >> strip_tac >>
        `j < LENGTH is` by decide_tac >>
        rename1 `rep_of_group is gj = SOME ((EL R is).inst_id,gj)` >>
        `mm_local_rep_index is gs j = R` by
          (qpat_x_assum `is = _` SUBST_ALL_TAC >>
           qpat_x_assum `gs = _` SUBST_ALL_TAC >>
           metis_tac[mm_local_rep_index_eq, pred_setTheory.IN_INSERT,
             pred_setTheory.NOT_IN_EMPTY]) >> simp[]) >>
     drule_at (Pat `mm_local_prefix _ _ _ _ = _`) mm_local_canonical_pending_keep >>
     disch_then (qspec_then `r` mp_tac) >> simp[] >> strip_tac >>
     `FILTER (\j. mm_local_rep_index is gs j <> r) js =
       FILTER (\j. SUC r <= mm_local_rep_index is gs j) js` by
       (rewrite_tac[rich_listTheory.FILTER_EQ] >> rpt strip_tac >>
        first_x_assum drule >> simp[]) >> gvs[]) >>
  `mm_local_pending cap (mm_local_pending_indices is gs (SUC r)) (H (SUC r)) t'` by
    (qpat_x_assum `FILTER _ js = _` (fn th => pure_rewrite_tac[GSYM th]) >>
     drule_at (Pat `mm_local_prefix _ _ _ _ = _`) mm_local_canonical_pending_discharge_interval >>
     disch_then (drule_at (Pat `rep_of_group _ _ = _`)) >>
     disch_then irule >>
     rpt (conj_tac >- first_assum ACCEPT_TAC) >>
     qexistsl [`H`, `a`, `d`, `bs`, `H r`, `t`, `u`] >>
     simp[] >> rpt strip_tac >>
     `a <= j` by
       (gvs[MEM_APPEND] >>
        metis_tac[mm_local_epoch_start_pending_bound, mm_local_epoch_start_bound]) >>
     `j <= r` by
       (gvs[MEM_APPEND, mm_local_pending_indices_def, MEM_FILTER, MEM_COUNT_LIST]) >>
     metis_tac[]) >>
  Cases_on `mm_local_pending_indices is gs (SUC r) = []`
  >- (gvs[mm_local_epoch_start_suc, mm_local_pending_empty,
       rich_listTheory.COUNT_LIST_def]) >>
  `a' = a` by gvs[mm_local_epoch_start_suc] >>
  drule_at (Pat `mm_local_prefix _ _ _ _ = _`) mm_local_canonical_retained_emit_interval >>
  disch_then (drule_at (Pat `rep_of_group _ _ = _`)) >>
  metis_tac[]
QED

Theorem mm_local_canonical_retained_renew[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\
  gs = (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
  r < LENGTH is /\ mm_local_history is H (SUC r) /\ MEM g gs /\
  rep_of_group is g = SOME ((EL r is).inst_id,g) /\
  cap = mm_local_write_capture is H (SUC r) /\
  js = mm_local_pending_indices is gs r /\
  a = mm_local_epoch_start is gs r /\
  (!j v src. a <= j /\ j <= r /\
    FLOOKUP (FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem)
      empty_scan_state (TAKE j is)).ss_loads v = SOME src ==>
    lookup_var v (H j) = SOME (mload src (H j))) /\
  u = FOLDL (\st q. if MEM q js then st else
    case cap q of NONE => st | SOME (d,bs) => write_memory_with_expansion d bs st)
    (H a) (MAP (\q. a+q) (COUNT_LIST (r-a))) /\
  t.vs_memory = u.vs_memory /\ mm_local_pending cap js (H r) t /\
  t'.vs_memory = (write_memory_with_expansion g.cg_dst
    (read_memory g.cg_src g.cg_length t) t).vs_memory /\
  a' = mm_local_epoch_start is gs (SUC r) ==>
  t'.vs_memory = (FOLDL (\st q.
    if MEM q (mm_local_pending_indices is gs (SUC r)) then st else
    case cap q of NONE => st | SOME (d,bs) => write_memory_with_expansion d bs st)
    (H a') (MAP (\q. a'+q) (COUNT_LIST (SUC r-a')))).vs_memory
Proof
  strip_tac >>
  `!q. a <= q /\ q < r ==> ?b. MEM b (mm_local_pending_indices is gs (SUC q))` by
    metis_tac[mm_local_epoch_start_nonempty] >>
  `a <= r` by metis_tac[mm_local_epoch_start_bound] >>
  `!q. a <= q /\ q < r ==> (H (SUC q)).vs_memory =
    (case mm_local_write_capture is H (SUC r) q of NONE => H q
     | SOME (d,bs) => write_memory_with_expansion d bs (H q)).vs_memory` by
    (mp_tac (Q.INST [`a` |-> `a`, `r` |-> `r`, `N` |-> `SUC r`]
       (SPEC_ALL mm_local_fixed_cut_capture_recurrence)) >> simp[]) >>
  `?d bs. cap r = SOME (d,bs) /\
    (H (SUC r)).vs_memory = (write_memory_with_expansion d bs (H r)).vs_memory` by
    (drule_all mm_local_canonical_rep_capture >> simp[]) >>
  mp_tac (SPEC_ALL mm_local_canonical_retained_renew_interval) >> simp[] >> metis_tac[]
QED

Theorem mm_local_mem2mem_word_emission[local]:
  ~MEM inst.inst_id nop_set /\ ALOOKUP rep_map inst.inst_id = SOME g /\
  g.cg_length = 32 /\ inst.inst_opcode <> MSTORE /\
  fresh_inst_id sk = (lid,sk1) /\ fresh_ir_var sk1 = (v,sk2) ==>
  apply_groups_inst_supply Mem2Mem nop_set rep_map sk inst =
    ([mk_load_inst Mem2Mem (inst with inst_id := lid) g.cg_src v;
      mk_mstore_from_load inst g.cg_dst v],sk2)
Proof
  simp[apply_groups_inst_supply_def]
QED

Theorem mm_local_mem2mem_word_steps[local]:
  g.cg_dst < dimword (:256) /\ g.cg_src < dimword (:256) ==>
  ?mid fin.
    step_inst fuel ctx
      (mk_load_inst Mem2Mem (inst with inst_id := lid) g.cg_src v) t = OK mid /\
    step_inst fuel ctx (mk_mstore_from_load inst g.cg_dst v) mid = OK fin /\
    mid = update_var v (mload g.cg_src t) t /\
    fin = update_var v (mload g.cg_src t)
      (write_memory_with_expansion g.cg_dst (read_memory g.cg_src 32 t) t) /\
    fin.vs_memory =
      (write_memory_with_expansion g.cg_dst (read_memory g.cg_src 32 t) t).vs_memory /\
    (!x. x <> v ==> lookup_var x fin = lookup_var x t)
Proof
  strip_tac >>
  `mstore g.cg_dst (mload g.cg_src t) (update_var v (mload g.cg_src t) t) =
    update_var v (mload g.cg_src t)
      (write_memory_with_expansion g.cg_dst (read_memory g.cg_src 32 t) t)` by
    (rewrite_tac[GSYM dftCommutationTheory.update_var_mstore_commute,
       mmCopyEquivTheory.mload_mstore_eq_mcopy_state] >>
     simp[venomExecSemanticsTheory.mcopy_def, venomStateTheory.read_memory_def]) >>
  qexistsl [`update_var v (mload g.cg_src t) t`,
    `mstore g.cg_dst (mload g.cg_src t) (update_var v (mload g.cg_src t) t)`] >>
  conj_tac
  >- simp[mk_load_inst_def, mode_load_opcode_def,
       venomExecSemanticsTheory.step_inst_non_invoke,
       venomExecSemanticsTheory.step_inst_base_def,
       venomExecSemanticsTheory.exec_read1_def,
       venomStateTheory.eval_operand_def, wordsTheory.w2n_n2w] >>
  conj_tac
  >- (simp[mk_mstore_from_load_def,
       venomExecSemanticsTheory.step_inst_non_invoke,
       venomExecSemanticsTheory.step_inst_base_def,
       venomExecSemanticsTheory.exec_write2_def,
       venomStateTheory.eval_operand_def, wordsTheory.w2n_n2w,
       venomStateTheory.lookup_var_def, venomStateTheory.update_var_def,
       finite_mapTheory.FLOOKUP_UPDATE] >>
       gvs[venomStateTheory.update_var_def]) >>
  asm_rewrite_tac[] >>
  simp[venomStateTheory.update_var_def, venomStateTheory.lookup_var_def,
    venomStateTheory.write_memory_with_expansion_def, finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem mm_local_history_live_load[local]:
  !j fn0 supply index k bb sk is H N.
  wf_ssa fn0 /\ wf_function fn0 /\ ir_supply_covers_fn supply fn0 /\
  index < LENGTH fn0.fn_blocks /\ k <= 3 /\
  mm_local_prefix fn0 supply index k = (bb,sk) /\ is = bb.bb_instructions /\
  mm_local_history is H N /\
  (!q. q < N ==> ~is_terminator (EL q is).inst_opcode) /\ j <= N ==>
  !v src. FLOOKUP (FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem)
    empty_scan_state (TAKE j is)).ss_loads v = SOME src ==>
    lookup_var v (H j) = SOME (mload src (H j))
Proof
  Induct_on `j`
  >- simp[empty_scan_state_def] >>
  rpt gen_tac >> strip_tac >>
  `!v src. FLOOKUP (FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem)
    empty_scan_state (TAKE j is)).ss_loads v = SOME src ==>
    lookup_var v (H j) = SOME (mload src (H j))` by
    (rpt strip_tac >> first_x_assum irule >>
     goal_assum (drule_at Any) >> simp[] >>
     goal_assum (drule_at Any) >> simp[] >>
     qexists `N` >> gvs[]) >>
  `j < LENGTH is /\ j < N` by gvs[mm_local_history_def] >>
  `step_inst_base (EL j is) (H j) = OK (H (SUC j))` by
    metis_tac[mm_local_history_def] >>
  `~is_terminator (EL j is).inst_opcode` by metis_tac[] >>
  `MEM (SOME Mem2Mem) (DROP k [NONE; SOME CalldataMerge; SOME DloadMerge; SOME Mem2Mem])` by
    (`k = 0 \/ k = 1 \/ k = 2 \/ k = 3` by decide_tac >> gvs[]) >>
  `!v src. FLOOKUP (FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem)
    empty_scan_state (TAKE j is)).ss_loads v = SOME src ==>
    ~MEM v (EL j is).inst_outputs` by
    (rpt gen_tac >> disch_tac >> gvs[] >> irule mm_local_live_cut_fresh >>
     goal_assum (drule_at Any) >> simp[] >>
     goal_assum (drule_at Any) >> simp[] >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `step_inst 0 ctx (EL j is) (H j) = OK (H (SUC j))` by
    (Cases_on `(EL j is).inst_opcode = INVOKE`
     >- gvs[venomExecSemanticsTheory.step_inst_base_def] >>
     simp[venomExecSemanticsTheory.step_inst_non_invoke]) >>
  simp[rich_listTheory.TAKE_SUC_BY_TAKE, rich_listTheory.FOLDL_SNOC] >>
  rpt gen_tac >> disch_tac >> irule mm_local_live_load_step >>
  goal_assum (drule_at Any) >> gvs[] >> metis_tac[]
QED

Theorem mm_local_history_pending_crossings[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 3 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\
  gs = (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
  r < LENGTH is /\ mm_local_history is H (SUC r) /\
  (!q. q < SUC r ==> ~is_terminator (EL q is).inst_opcode) /\
  cap = mm_local_write_capture is H (SUC r) /\
  js = mm_local_pending_indices is gs r /\
  MEM g gs /\ rep_of_group is g = SOME ((EL r is).inst_id,g) ==>
  (!pre j mid l post a p b bs.
    js = pre ++ [j] ++ mid ++ [l] ++ post /\
    cap j = SOME (a,p) /\ cap l = SOME (b,bs) ==>
    mm_local_write_compatible a p b bs) /\
  (!j a p b bs. MEM j js /\ cap j = SOME (a,p) /\ cap r = SOME (b,bs) ==>
    mm_local_write_compatible a p b bs)
Proof
  strip_tac >>
  `!j v src. j <= SUC r /\ FLOOKUP
    (FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem)
      empty_scan_state (TAKE j is)).ss_loads v = SOME src ==>
    lookup_var v (H j) = SOME (mload src (H j))` by
    (rpt strip_tac >> irule mm_local_history_live_load >>
     goal_assum (drule_at Any) >> simp[] >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  irule mm_local_canonical_pending_crossings >>
  goal_assum (drule_at Any) >> simp[] >>
  goal_assum (drule_at Any) >> simp[] >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  qexists `H` >> gvs[] >> rpt strip_tac >>
  first_x_assum irule >> simp[] >>
  gvs[mm_local_pending_indices_def, MEM_FILTER, MEM_COUNT_LIST]
QED

Theorem mm_local_history_pending_discharge[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 3 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\
  gs = (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
  r < LENGTH is /\ mm_local_history is H (SUC r) /\ MEM g gs /\
  (!q. q < SUC r ==> ~is_terminator (EL q is).inst_opcode) /\
  rep_of_group is g = SOME ((EL r is).inst_id,g) /\
  cap = mm_local_write_capture is H (SUC r) /\
  js = mm_local_pending_indices is gs r /\
  a = mm_local_epoch_start is gs r /\
  u = FOLDL (\st q. if MEM q js then st else
    case cap q of NONE => st
    | SOME (d,bs) => write_memory_with_expansion d bs st)
    (H a) (MAP (\q. a+q) (COUNT_LIST (r-a))) /\
  t.vs_memory = u.vs_memory /\ mm_local_pending cap js s t /\
  cap r = SOME (d,payload) /\
  s'.vs_memory = (write_memory_with_expansion d payload s).vs_memory /\
  t'.vs_memory = (write_memory_with_expansion g.cg_dst
    (read_memory g.cg_src g.cg_length t) t).vs_memory ==>
  mm_local_pending cap (FILTER (\j. mm_local_rep_index is gs j <> r) js) s' t'
Proof
  strip_tac >>
  `!j v src. j <= SUC r /\ FLOOKUP
    (FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem)
      empty_scan_state (TAKE j is)).ss_loads v = SOME src ==>
    lookup_var v (H j) = SOME (mload src (H j))` by
    (rpt strip_tac >> irule mm_local_history_live_load >>
     goal_assum (drule_at Any) >> simp[] >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  drule_at (Pat `mm_local_prefix _ _ _ _ = _`)
    mm_local_canonical_pending_discharge >>
  disch_then (drule_at (Pat `rep_of_group _ _ = _`)) >>
  disch_then irule >> simp[] >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  qexistsl [`H`, `s`, `t`] >> gvs[] >>
  rpt strip_tac >> first_x_assum irule >> simp[] >>
  gvs[mm_local_pending_indices_def, MEM_FILTER, MEM_COUNT_LIST]
QED

Theorem mm_local_history_retained_renew[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 3 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\
  gs = (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
  r < LENGTH is /\ mm_local_history is H (SUC r) /\ MEM g gs /\
  (!q. q < SUC r ==> ~is_terminator (EL q is).inst_opcode) /\
  rep_of_group is g = SOME ((EL r is).inst_id,g) /\
  cap = mm_local_write_capture is H (SUC r) /\
  js = mm_local_pending_indices is gs r /\
  a = mm_local_epoch_start is gs r /\
  u = FOLDL (\st q. if MEM q js then st else
    case cap q of NONE => st | SOME (d,bs) => write_memory_with_expansion d bs st)
    (H a) (MAP (\q. a+q) (COUNT_LIST (r-a))) /\
  t.vs_memory = u.vs_memory /\ mm_local_pending cap js (H r) t /\
  t'.vs_memory = (write_memory_with_expansion g.cg_dst
    (read_memory g.cg_src g.cg_length t) t).vs_memory /\
  a' = mm_local_epoch_start is gs (SUC r) ==>
  t'.vs_memory = (FOLDL (\st q.
    if MEM q (mm_local_pending_indices is gs (SUC r)) then st else
    case cap q of NONE => st | SOME (d,bs) => write_memory_with_expansion d bs st)
    (H a') (MAP (\q. a'+q) (COUNT_LIST (SUC r-a')))).vs_memory
Proof
  strip_tac >>
  `!j v src. j <= SUC r /\ FLOOKUP
    (FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem)
      empty_scan_state (TAKE j is)).ss_loads v = SOME src ==>
    lookup_var v (H j) = SOME (mload src (H j))` by
    (rpt strip_tac >> irule mm_local_history_live_load >>
     goal_assum (drule_at Any) >> simp[] >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  drule_at (Pat `mm_local_prefix _ _ _ _ = _`)
    mm_local_canonical_retained_renew >>
  disch_then (drule_at (Pat `rep_of_group _ _ = _`)) >>
  disch_then irule >> simp[] >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  qexists `t` >> gvs[]
QED

Theorem mm_local_interval_runtime_capture:
  q < n /\ n <= LENGTH is /\
  ((EL q is).inst_opcode = MSTORE \/ (EL q is).inst_opcode = MCOPY) /\
  step_inst fuel ctx (EL q is) (H q) = OK t /\
  H (SUC q) = t with vs_inst_idx := SUC (H q).vs_inst_idx ==>
  ?d bs. mm_local_write_capture is H n q = SOME (d,bs) /\
    (H (SUC q)).vs_memory = (write_memory_with_expansion d bs (H q)).vs_memory
Proof
  strip_tac >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[venomExecSemanticsTheory.step_inst_non_invoke,
    venomExecSemanticsTheory.step_inst_base_def,
    venomExecSemanticsTheory.exec_write2_def] >>
  gvs[AllCaseEqs()] >> strip_tac >>
  gvs[mm_local_write_capture_def, venomMemPropsTheory.mstore_eq_write_mem,
    venomExecSemanticsTheory.mcopy_def, venomStateTheory.read_memory_def]
QED

Theorem mm_local_interval_runtime_replay_one[local]:
  q < n /\ n <= LENGTH is /\
  ((EL q is).inst_opcode = MSTORE \/ (EL q is).inst_opcode = MCOPY) /\
  step_inst fuel ctx (EL q is) (H q) = OK t /\
  H (SUC q) = t with vs_inst_idx := SUC (H q).vs_inst_idx ==>
  (H (SUC q)).vs_memory = (FOLDL (\st j.
    case mm_local_write_capture is H n j of NONE => st
    | SOME (d,bs) => write_memory_with_expansion d bs st)
    (H q) (MAP (\j. q+j) (COUNT_LIST (SUC q-q)))).vs_memory
Proof
  strip_tac >> drule_at (Pat `step_inst _ _ _ _ = _`)
    mm_local_interval_runtime_capture >>
  disch_then (qspec_then `n` mp_tac) >> simp[] >> strip_tac >>
  simp[rich_listTheory.count_list_sub1, rich_listTheory.COUNT_LIST_def]
QED

Theorem mm_local_surviving_runtime_frame[local]:
  q < N /\ N <= LENGTH is /\ MEM c ss.ss_copies /\
  ~MEM c (scan_inst dfg Mem2Mem ss (EL q is)).ss_flushed /\
  ~is_terminator (EL q is).inst_opcode /\
  step_inst fuel ctx (EL q is) (H q) = OK t /\
  H (SUC q) = t with vs_inst_idx := SUC (H q).vs_inst_idx /\
  mm_local_write_capture is H N q = NONE ==>
  (H (SUC q)).vs_memory = (H q).vs_memory
Proof
  strip_tac >> drule_all mm_local_surviving_write_opcode >> strip_tac
  >- (drule_at (Pat `step_inst _ _ _ _ = _`) mm_local_interval_runtime_capture >>
      disch_then (qspec_then `N` mp_tac) >> simp[])
  >- (drule_at (Pat `step_inst _ _ _ _ = _`) mm_local_interval_runtime_capture >>
      disch_then (qspec_then `N` mp_tac) >> simp[]) >>
  Cases_on `is_alloca_op (EL q is).inst_opcode`
  >- (`(EL q is).inst_opcode <> INVOKE` by
        (Cases_on `(EL q is).inst_opcode` >> gvs[venomInstTheory.is_alloca_op_def]) >>
      drule_all venomMemPropsTheory.step_inst_alloca_preserves_memory >> simp[]) >>
  drule_all venomInstPropsTheory.write_effects_sound_memory >> simp[]
QED

Theorem mm_local_live_segment_runtime_recurrence[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\ r < LENGTH is /\ r < N /\ N <= LENGTH is /\
  gs = (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
  MEM b (mm_local_pending_indices is gs r) /\ b <= q /\ q < r /\
  ~is_terminator (EL q is).inst_opcode /\
  step_inst fuel ctx (EL q is) (H q) = OK t /\
  H (SUC q) = t with vs_inst_idx := SUC (H q).vs_inst_idx ==>
  (H (SUC q)).vs_memory =
    (case mm_local_write_capture is H N q of NONE => H q
     | SOME (d,bs) => write_memory_with_expansion d bs (H q)).vs_memory
Proof
  strip_tac >> `q < N` by decide_tac >>
  Cases_on `mm_local_write_capture is H N q`
  >- (simp[] >>
      Cases_on `b = q`
      >- (qpat_assum `MEM b (mm_local_pending_indices _ _ r)`
            (strip_assume_tac o REWRITE_RULE [mm_local_pending_indices_mem]) >>
          `b < LENGTH is` by decide_tac >>
          `MEM g (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed` by metis_tac[] >>
          drule_all (REWRITE_RULE [mode_copy_opcode_def] (Q.INST [`mode` |-> `Mem2Mem`] mm_local_final_write_birth)) >> strip_tac >> gvs[] >>
          drule_at (Pat `step_inst _ _ _ _ = _`) mm_local_interval_runtime_capture >>
          disch_then (qspec_then `N` mp_tac) >> simp[]) >>
      `MEM b (mm_local_pending_indices is gs q)` by
        (pure_rewrite_tac[mm_local_pending_indices_mem] >>
         qpat_assum `MEM b (mm_local_pending_indices _ _ r)`
           (strip_assume_tac o REWRITE_RULE [mm_local_pending_indices_mem]) >>
         conj_tac >- decide_tac >> conj_tac >- first_assum ACCEPT_TAC >>
         goal_assum (drule_at Any) >> simp[] >> decide_tac) >>
      qabbrev_tac `ss = FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem)
        empty_scan_state (TAKE q is)` >>
      `q <= LENGTH is` by decide_tac >>
      `?c. MEM c ss.ss_copies /\ MEM (EL b is).inst_id c.cg_inst_ids` by
        metis_tac[mm_local_canonical_pending_copy_owner] >>
      `~MEM c (scan_inst (dfg_build_function fn0) Mem2Mem ss (EL q is)).ss_flushed` by
        (qpat_x_assum `MEM b (mm_local_pending_indices _ _ r)`
           (strip_assume_tac o REWRITE_RULE [mm_local_pending_indices_mem]) >>
         `b < LENGTH is` by decide_tac >>
         `scan_inst (dfg_build_function fn0) Mem2Mem ss (EL q is) =
          FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem)
            empty_scan_state (TAKE (SUC q) is)` by
           (`q < LENGTH is` by decide_tac >>
            gvs[Abbr `ss`, rich_listTheory.TAKE_SUC,
              rich_listTheory.DROP_EL_CONS, FOLDL_APPEND]) >>
         rename1 `rep_of_group is g = SOME ((EL owner_r is).inst_id,g)` >>
         `SUC q <= owner_r` by decide_tac >>
         metis_tac[mm_local_indexed_future_not_flushed]) >>
      drule_all mm_local_surviving_runtime_frame >> simp[]) >>
  PairCases_on `x` >> simp[] >>
  `(EL q is).inst_opcode = MSTORE \/ (EL q is).inst_opcode = MCOPY` by
    (gvs[mm_local_write_capture_def, AllCaseEqs()] >> metis_tac[]) >>
  drule_at (Pat `step_inst _ _ _ _ = _`) mm_local_interval_runtime_capture >>
  disch_then (qspec_then `N` mp_tac) >> simp[]
QED

Theorem mm_local_fixed_cut_runtime_recurrence[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\ h <= a /\ a <= r /\ r < LENGTH is /\
  r < N /\ N <= LENGTH is /\
  gs = (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
  (!q. a <= q /\ q < r ==> ?b. MEM b (mm_local_pending_indices is gs (SUC q))) /\
  (!q. h <= q /\ q < r ==> ~is_terminator (EL q is).inst_opcode /\
    ?t. step_inst fuel ctx (EL q is) (H q) = OK t /\
      H (SUC q) = t with vs_inst_idx := SUC (H q).vs_inst_idx) ==>
  !q. a <= q /\ q < r ==>
  (H (SUC q)).vs_memory =
    (case mm_local_write_capture is H N q of NONE => H q
     | SOME (d,bs) => write_memory_with_expansion d bs (H q)).vs_memory
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  `?b. MEM b (mm_local_pending_indices is gs (SUC q))` by metis_tac[] >>
  `b < SUC q` by metis_tac[mm_local_pending_indices_mem] >>
  `b <= q /\ q < SUC q /\ SUC q < LENGTH is /\ SUC q < N /\ h <= q` by decide_tac >>
  `~is_terminator (EL q is).inst_opcode /\
    ?t. step_inst fuel ctx (EL q is) (H q) = OK t /\
      H (SUC q) = t with vs_inst_idx := SUC (H q).vs_inst_idx` by metis_tac[] >>
  drule_all mm_local_live_segment_runtime_recurrence >> simp[]
QED

Theorem mm_local_pending_indices_after_phis:
  MEM j (mm_local_pending_indices is gs n) ==> phi_prefix_length is <= j
Proof
  strip_tac >> spose_not_then assume_tac >>
  `j < phi_prefix_length is` by decide_tac >>
  drule venomExecProofsTheory.phi_prefix_length_el_phi >>
  gvs[mm_local_pending_indices_mem]
QED

Theorem mm_local_epoch_start_after_phis:
  phi_prefix_length is <= n ==> phi_prefix_length is <= mm_local_epoch_start is gs n
Proof
  strip_tac >>
  `mm_local_pending_indices is gs (phi_prefix_length is) = []` by
    (Cases_on `mm_local_pending_indices is gs (phi_prefix_length is)` >> simp[] >>
     rename1 `mm_local_pending_indices is gs (phi_prefix_length is) = j::js` >>
     `MEM j (mm_local_pending_indices is gs (phi_prefix_length is))` by simp[] >>
     drule mm_local_pending_indices_after_phis >>
     gvs[mm_local_pending_indices_mem]) >>
  rewrite_tac[mm_local_epoch_start_def] >>
  irule rich_listTheory.MAX_LIST_PROPERTY >> simp[MEM_FILTER, MEM_COUNT_LIST]
QED

Theorem mm_local_runtime_live_load[local]:
  wf_ssa fn0 /\ wf_function fn0 /\ ir_supply_covers_fn supply fn0 /\
  index < LENGTH fn0.fn_blocks /\ k <= 4 /\
  mm_local_prefix fn0 supply index k = (bb,sk) /\
  MEM (SOME Mem2Mem) (DROP k [NONE; SOME CalldataMerge; SOME DloadMerge; SOME Mem2Mem]) /\
  is = bb.bb_instructions /\ h = phi_prefix_length is /\
  h <= j /\ j <= LENGTH is /\
  (!q. h <= q /\ q < j ==> ~is_terminator (EL q is).inst_opcode /\
    ?t. step_inst fuel ctx (EL q is) (H q) = OK t /\
      H (SUC q) = t with vs_inst_idx := SUC (H q).vs_inst_idx) ==>
  !v src. FLOOKUP (FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem)
    empty_scan_state (TAKE j is)).ss_loads v = SOME src ==>
    lookup_var v (H j) = SOME (mload src (H j))
Proof
  strip_tac >>
  `h + (j-h) = j` by decide_tac >>
  mp_tac (Q.INST [`n` |-> `j-h`,
    `states` |-> `MAP (\q. H (h+q)) (COUNT_LIST (SUC (j-h)))`]
    (SPEC_ALL mm_local_live_load_cut)) >>
  qpat_x_assum `is = _` (fn th => rewrite_tac[GSYM th]) >>
  simp[EL_MAP, EL_COUNT_LIST, LENGTH_COUNT_LIST,
    mm_local_scan_phi_prefix, empty_scan_state_def] >>
  impl_tac >-
    (rpt strip_tac >>
     qpat_x_assum `!q. h <= q /\ q < j ==> _`
       (qspec_then `h+r` mp_tac) >>
     simp[arithmeticTheory.ADD_CLAUSES] >>
     gvs[arithmeticTheory.ADD_COMM]) >> simp[]
QED

Theorem mm_local_runtime_epoch_recurrence[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  is = bb.bb_instructions /\ h = phi_prefix_length is /\ h <= r /\ r < LENGTH is /\
  gs = (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\
  a = mm_local_epoch_start is gs r /\
  (!q. h <= q /\ q < r ==> ~is_terminator (EL q is).inst_opcode /\
    ?t. step_inst fuel ctx (EL q is) (H q) = OK t /\
      H (SUC q) = t with vs_inst_idx := SUC (H q).vs_inst_idx) ==>
  !q. a <= q /\ q < r ==> (H (SUC q)).vs_memory =
    (case mm_local_write_capture is H (SUC r) q of NONE => H q
     | SOME (d,bs) => write_memory_with_expansion d bs (H q)).vs_memory
Proof
  strip_tac >>
  `h <= a` by metis_tac[mm_local_epoch_start_after_phis] >>
  `a <= r` by metis_tac[mm_local_epoch_start_bound] >>
  `!q. a <= q /\ q < r ==> ?b. MEM b (mm_local_pending_indices is gs (SUC q))` by
    metis_tac[mm_local_epoch_start_nonempty] >>
  rpt gen_tac >> strip_tac >>
  drule_at (Pat `mm_local_prefix _ _ _ _ = _`) mm_local_fixed_cut_runtime_recurrence >>
  disch_then irule >> goal_assum (drule_at Any) >> simp[] >>
  conj_tac >- gvs[] >>
  qexistsl [`a`,`ctx`,`fuel`,`h`,`r`] >> gvs[]
QED

Theorem mm_local_runtime_pending_discharge:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  MEM (SOME Mem2Mem) (DROP k [NONE; SOME CalldataMerge; SOME DloadMerge; SOME Mem2Mem]) /\
  is = bb.bb_instructions /\ h = phi_prefix_length is /\ h <= r /\ r < LENGTH is /\
  gs = (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\ MEM g gs /\
  rep_of_group is g = SOME ((EL r is).inst_id,g) /\
  (!q. h <= q /\ q < r ==> ~is_terminator (EL q is).inst_opcode /\
    ?v. step_inst fuel ctx (EL q is) (H q) = OK v /\
      H (SUC q) = v with vs_inst_idx := SUC (H q).vs_inst_idx) /\
  cap = mm_local_write_capture is H (SUC r) /\
  js = mm_local_pending_indices is gs r /\ a = mm_local_epoch_start is gs r /\
  u = FOLDL (\st q. if MEM q js then st else
    case cap q of NONE => st | SOME (d,bs) => write_memory_with_expansion d bs st)
    (H a) (MAP (\q. a+q) (COUNT_LIST (r-a))) /\
  t.vs_memory = u.vs_memory /\ mm_local_pending cap js s t /\
  cap r = SOME (d,payload) /\
  s'.vs_memory = (write_memory_with_expansion d payload s).vs_memory /\
  t'.vs_memory = (write_memory_with_expansion g.cg_dst
    (read_memory g.cg_src g.cg_length t) t).vs_memory ==>
  mm_local_pending cap (FILTER (\j. mm_local_rep_index is gs j <> r) js) s' t'
Proof
  strip_tac >>
  `!q. a <= q /\ q < r ==> (H (SUC q)).vs_memory =
    (case cap q of NONE => H q
     | SOME (d,bs) => write_memory_with_expansion d bs (H q)).vs_memory` by
    (qpat_x_assum `cap = _` SUBST_ALL_TAC >>
     metis_tac[mm_local_runtime_epoch_recurrence]) >>
  `!j v src. MEM j (js ++ [r]) /\
    FLOOKUP (FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem)
      empty_scan_state (TAKE j is)).ss_loads v = SOME src ==>
    lookup_var v (H j) = SOME (mload src (H j))` by
    (rpt strip_tac >>
     `h <= j /\ j <= r` by
       (gvs[MEM_APPEND] >>
        metis_tac[mm_local_pending_indices_after_phis,
          mm_local_pending_indices_mem, arithmeticTheory.LESS_IMP_LESS_OR_EQ]) >>
     drule_at (Pat `mm_local_prefix _ _ _ _ = _`) mm_local_runtime_live_load >>
     disch_then irule >> goal_assum (drule_at Any) >> simp[] >>
     qexistsl [`ctx`,`fuel`] >> gvs[] >> metis_tac[]) >>
  drule_at (Pat `mm_local_prefix _ _ _ _ = _`) mm_local_canonical_pending_discharge_interval >>
  disch_then (drule_at (Pat `rep_of_group _ _ = _`)) >>
  metis_tac[]
QED

Theorem mm_local_runtime_retained_renew:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  MEM (SOME Mem2Mem) (DROP k [NONE; SOME CalldataMerge; SOME DloadMerge; SOME Mem2Mem]) /\
  is = bb.bb_instructions /\ h = phi_prefix_length is /\ h <= r /\ r < LENGTH is /\
  gs = (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\ MEM g gs /\
  rep_of_group is g = SOME ((EL r is).inst_id,g) /\
  (!q. h <= q /\ q <= r ==> ~is_terminator (EL q is).inst_opcode /\
    ?v. step_inst fuel ctx (EL q is) (H q) = OK v /\
      H (SUC q) = v with vs_inst_idx := SUC (H q).vs_inst_idx) /\
  cap = mm_local_write_capture is H (SUC r) /\
  js = mm_local_pending_indices is gs r /\ a = mm_local_epoch_start is gs r /\
  u = FOLDL (\st q. if MEM q js then st else
    case cap q of NONE => st | SOME (d,bs) => write_memory_with_expansion d bs st)
    (H a) (MAP (\q. a+q) (COUNT_LIST (r-a))) /\
  t.vs_memory = u.vs_memory /\ mm_local_pending cap js (H r) t /\
  t'.vs_memory = (write_memory_with_expansion g.cg_dst
    (read_memory g.cg_src g.cg_length t) t).vs_memory /\
  a' = mm_local_epoch_start is gs (SUC r) ==>
  t'.vs_memory = (FOLDL (\st q.
    if MEM q (mm_local_pending_indices is gs (SUC r)) then st else
    case cap q of NONE => st | SOME (d,bs) => write_memory_with_expansion d bs st)
    (H a') (MAP (\q. a'+q) (COUNT_LIST (SUC r-a')))).vs_memory
Proof
  strip_tac >>
  `!q. h <= q /\ q < r ==> ~is_terminator (EL q is).inst_opcode /\
    ?v. step_inst fuel ctx (EL q is) (H q) = OK v /\
      H (SUC q) = v with vs_inst_idx := SUC (H q).vs_inst_idx` by
    metis_tac[arithmeticTheory.LESS_IMP_LESS_OR_EQ] >>
  `!q. a <= q /\ q < r ==> (H (SUC q)).vs_memory =
    (case cap q of NONE => H q
     | SOME (d,bs) => write_memory_with_expansion d bs (H q)).vs_memory` by
    (qpat_x_assum `cap = _` SUBST_ALL_TAC >>
     metis_tac[mm_local_runtime_epoch_recurrence]) >>
  `!j v src. a <= j /\ j <= r /\
    FLOOKUP (FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem)
      empty_scan_state (TAKE j is)).ss_loads v = SOME src ==>
    lookup_var v (H j) = SOME (mload src (H j))` by
    (rpt strip_tac >>
     `h <= a` by metis_tac[mm_local_epoch_start_after_phis] >>
     drule_at (Pat `mm_local_prefix _ _ _ _ = _`) mm_local_runtime_live_load >>
     disch_then irule >> goal_assum (drule_at Any) >> simp[] >>
     qexistsl [`ctx`,`fuel`] >> gvs[] >> metis_tac[]) >>
  `(EL r is).inst_opcode IN {MSTORE; MCOPY; CALLDATACOPY; DLOADBYTES}` by
    metis_tac[mm_local_canonical_rep_write] >>
  `MEM (EL r is).inst_id g.cg_inst_ids` by metis_tac[mm_local_rep_member] >>
  `(EL r is).inst_opcode = MSTORE \/ (EL r is).inst_opcode = MCOPY` by
    (drule_at (Pat `mm_local_prefix _ _ _ _ = _`)
       (REWRITE_RULE [mode_copy_opcode_def]
         (Q.INST [`mode` |-> `Mem2Mem`] mm_local_final_write_birth)) >>
     disch_then (qspec_then `r` mp_tac) >> gvs[] >> metis_tac[]) >>
  `?d bs. cap r = SOME (d,bs) /\
    (H (SUC r)).vs_memory = (write_memory_with_expansion d bs (H r)).vs_memory` by
    (qpat_x_assum `cap = _` SUBST_ALL_TAC >>
     irule mm_local_interval_runtime_capture >> simp[] >>
     qpat_x_assum `!q. h <= q /\ q <= r ==> _` (qspec_then `r` mp_tac) >>
     gvs[] >> metis_tac[]) >>
  drule_at (Pat `mm_local_prefix _ _ _ _ = _`) mm_local_canonical_retained_renew_interval >>
  disch_then (drule_at (Pat `rep_of_group _ _ = _`)) >> metis_tac[]
QED

Theorem mm_local_surviving_demand_not_deleted:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\ k <= 4 /\
  mm_local_prefix fn0 supply index k = (bb,sk) /\
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  MEM q bb.bb_instructions /\ inst_wf q /\ MEM v q.inst_outputs /\
  MEM v (venomInst$inst_uses u) /\
  ((MEM u bb.bb_instructions /\
    apply_groups_inst_supply mode
      (nop_ids_of_groups (dfg_build_function fn0) mode bb.bb_instructions
        (scan_block (dfg_build_function fn0) mode bb).ss_flushed)
      (rep_map_of_groups bb.bb_instructions
        (scan_block (dfg_build_function fn0) mode bb).ss_flushed) s u = (out,t) /\
    MEM u out) \/
   (MEM u (fn_insts fn0) /\ ~MEM u (EL index fn0.fn_blocks).bb_instructions)) ==>
  ~MEM q.inst_id (nop_ids_of_groups (dfg_build_function fn0) mode bb.bb_instructions
    (scan_block (dfg_build_function fn0) mode bb).ss_flushed)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all mm_local_prefix_used_producer_unchanged >>
  disch_then (qspec_then `sk` assume_tac) >>
  strip_tac >> gvs[apply_groups_inst_supply_def, mk_nop_from_def] >>
  qpat_x_assum `_ with <|inst_opcode := NOP; inst_operands := []; inst_outputs := []|> = _`
    (mp_tac o AP_TERM ``\i:instruction. i.inst_outputs``) >> simp[] >> strip_tac >> gvs[]
QED

Theorem mm_local_emitted_demand_not_deleted[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\ k <= 4 /\
  mm_local_prefix fn0 supply index k = (bb,sk) /\
  ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions) /\
  MEM q bb.bb_instructions /\ inst_wf q /\ MEM v q.inst_outputs ==>
  !xs s ys t. EVERY (\i. MEM i bb.bb_instructions) xs /\ MEM v s.irs_used_vars /\
    mm_flat_map_supply (apply_groups_inst_supply mode
      (nop_ids_of_groups (dfg_build_function fn0) mode bb.bb_instructions
        (scan_block (dfg_build_function fn0) mode bb).ss_flushed)
      (rep_map_of_groups bb.bb_instructions
        (scan_block (dfg_build_function fn0) mode bb).ss_flushed)) s xs = (ys,t) ==>
    !u. MEM u ys /\ MEM v (venomInst$inst_uses u) ==>
    ~MEM q.inst_id (nop_ids_of_groups (dfg_build_function fn0) mode bb.bb_instructions
      (scan_block (dfg_build_function fn0) mode bb).ss_flushed)
Proof
  strip_tac >> Induct >> simp[mm_flat_map_supply_def] >>
  rpt gen_tac >> strip_tac >> gvs[AllCaseEqs()] >>
  drule_at (Pat `apply_groups_inst_supply _ _ _ _ _ = _`) mm_local_mode_old_use >>
  strip_tac >> rpt gen_tac >> strip_tac >>
  gvs[MEM_APPEND]
  >- (irule mm_local_surviving_demand_not_deleted >> metis_tac[]) >>
  first_x_assum irule >> goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem mm_local_mode_demands_exclude_deleted:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\ k <= 4 /\
  mm_local_prefix fn0 supply index k = (bb,sk) /\
  transform_block_mode_supply (dfg_build_function fn0) mode sk bb = (cc,t) /\
  ns = nop_ids_of_groups (dfg_build_function fn0) mode bb.bb_instructions
    (scan_block (dfg_build_function fn0) mode bb).ss_flushed /\
  excluded = {v | ?q. MEM q bb.bb_instructions /\ MEM q.inst_id ns /\ MEM v q.inst_outputs} ==>
  (!u v. MEM u cc.bb_instructions /\ MEM v (venomInst$inst_uses u) /\
    MEM v (irSupply$fn_ir_vars fn0) ==> v NOTIN excluded) /\
  (!u v. MEM u (fn_insts fn0) /\ ~MEM u (EL index fn0.fn_blocks).bb_instructions /\
    MEM v (venomInst$inst_uses u) ==> v NOTIN excluded)
Proof
  strip_tac >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)` by
    metis_tac[mm_local_prefix_wf_id_distinct] >>
  `fn_inst_wf (fn0 with fn_blocks := LUPDATE bb index fn0.fn_blocks)` by
    metis_tac[mm_local_prefix_inst_wf] >>
  `MEM bb (LUPDATE bb index fn0.fn_blocks)` by
    (simp[MEM_EL] >> qexists `index` >> simp[EL_LUPDATE]) >>
  `!q. MEM q bb.bb_instructions ==> inst_wf q` by
    (gvs[fn_inst_wf_def, EVERY_MEM] >> metis_tac[]) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `MEM v sk.irs_used_vars` by
        (irule mm_local_prefix_used_vars_mono >>
         goal_assum (drule_at (Pat `mm_local_prefix _ _ _ _ = _`)) >>
         gvs[ir_supply_covers_fn_def, list_subset_def, EVERY_MEM]) >>
      spose_not_then strip_assume_tac >> gvs[] >>
      qpat_x_assum `transform_block_mode_supply _ _ _ _ = _` mp_tac >>
      simp[transform_block_mode_supply_def, AllCaseEqs()] >> rpt strip_tac >>
      `inst_wf q` by metis_tac[] >>
      `EVERY (\i. MEM i bb.bb_instructions) bb.bb_instructions` by simp[EVERY_MEM] >>
      `MEM u insts` by (gvs[] ) >>
      drule_all mm_local_emitted_demand_not_deleted >> simp[]) >>
  rpt gen_tac >> strip_tac >> spose_not_then strip_assume_tac >> gvs[] >>
  metis_tac[mm_local_surviving_demand_not_deleted]
QED

Theorem mm_local_retained_mstore_lookup[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\ k <= 4 /\
  mm_local_prefix fn0 supply index k = (bb,sk) /\
  transform_block_mode_supply (dfg_build_function fn0) mode sk bb = (cc,t) /\
  ns = nop_ids_of_groups (dfg_build_function fn0) mode bb.bb_instructions
    (scan_block (dfg_build_function fn0) mode bb).ss_flushed /\
  excluded = {v | ?q. MEM q bb.bb_instructions /\ MEM q.inst_id ns /\ MEM v q.inst_outputs} /\
  (!v. v NOTIN excluded ==> lookup_var v s = lookup_var v s') /\
  MEM u cc.bb_instructions /\ u.inst_opcode = MSTORE /\
  MEM v (venomInst$inst_uses u) /\ MEM v (irSupply$fn_ir_vars fn0) ==>
  lookup_var v s = lookup_var v s'
Proof
  strip_tac >>
  drule_all mm_local_mode_demands_exclude_deleted >>
  strip_tac >> first_x_assum irule >> metis_tac[]
QED

Theorem mm_local_mem2mem_word_runtime:
  ~MEM inst.inst_id nop_set /\ ALOOKUP rep_map inst.inst_id = SOME g /\
  g.cg_length = 32 /\ inst.inst_opcode <> MSTORE /\
  fresh_inst_id sk = (lid,sk1) /\ fresh_ir_var sk1 = (v,sk2) /\
  g.cg_dst < dimword (:256) /\ g.cg_src < dimword (:256) /\
  (!x. x IN P ==> x <> v) ==>
  ?load store mid fin.
    apply_groups_inst_supply Mem2Mem nop_set rep_map sk inst = ([load;store],sk2) /\
    step_inst fuel ctx load t = OK mid /\
    step_inst fuel ctx store (mid with vs_inst_idx := SUC t.vs_inst_idx) = OK fin /\
    (fin with vs_inst_idx := SUC (SUC t.vs_inst_idx)) =
      (update_var v (mload g.cg_src t)
        (write_memory_with_expansion g.cg_dst (read_memory g.cg_src 32 t) t)
        with vs_inst_idx := SUC (SUC t.vs_inst_idx)) /\
    fin.vs_memory = (write_memory_with_expansion g.cg_dst (read_memory g.cg_src 32 t) t).vs_memory /\
    (!x. x IN P ==> lookup_var x fin = lookup_var x t)
Proof
  strip_tac >>
  drule_all mm_local_mem2mem_word_emission >> disch_tac >>
  mp_tac (SPEC_ALL mm_local_mem2mem_word_steps) >> simp[] >> strip_tac >>
  `~is_terminator (mk_mstore_from_load inst g.cg_dst v).inst_opcode` by
    simp[mk_mstore_from_load_def, venomInstTheory.is_terminator_def] >>
  drule_all dftIndexedExecTheory.dft_step_ok_idx >>
  disch_then (qspec_then `SUC t.vs_inst_idx` assume_tac) >>
  qexists `update_var v (mload g.cg_src t)
    (write_memory_with_expansion g.cg_dst (read_memory g.cg_src 32 t) t)
    with vs_inst_idx := SUC t.vs_inst_idx` >>
  gvs[venomStateTheory.lookup_var_def,
    venomStateTheory.update_var_def, venomStateTheory.write_memory_with_expansion_def] >>
  metis_tac[]
QED

Theorem mm_local_mem2mem_retained_runtime[local]:
  ~MEM inst.inst_id nop_set /\ ALOOKUP rep_map inst.inst_id = SOME g /\
  g.cg_length = 32 /\ inst.inst_opcode = MSTORE /\
  inst.inst_operands = [Lit dst; Var v] /\
  step_inst fuel ctx inst s = OK s' /\ lookup_var v s = lookup_var v t ==>
  ?w fin.
    apply_groups_inst_supply Mem2Mem nop_set rep_map sk inst = ([inst],sk) /\
    lookup_var v s = SOME w /\ s' = mstore (w2n dst) w s /\
    step_inst fuel ctx inst t = OK fin /\ fin = mstore (w2n dst) w t /\
    (fin with vs_inst_idx := SUC t.vs_inst_idx) =
      (mstore (w2n dst) w t with vs_inst_idx := SUC t.vs_inst_idx) /\
    (!x. lookup_var x fin = lookup_var x t)
Proof
  strip_tac >>
  qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  simp[venomExecSemanticsTheory.step_inst_non_invoke,
    venomExecSemanticsTheory.step_inst_base_opcode_eqs,
    venomExecSemanticsTheory.exec_write2_def, venomStateTheory.eval_operand_def] >>
  Cases_on `lookup_var v t` >> gvs[] >> strip_tac >>
  simp[apply_groups_inst_supply_def,
    venomExecSemanticsTheory.step_inst_non_invoke,
    venomExecSemanticsTheory.step_inst_base_def,
    venomExecSemanticsTheory.exec_write2_def, venomStateTheory.eval_operand_def,
    venomStateTheory.lookup_var_def, venomStateTheory.mstore_def]
QED

Theorem mm_local_mem2mem_retained_payload:
  ~MEM inst.inst_id nop_set /\ ALOOKUP rep_map inst.inst_id = SOME g /\
  g.cg_length = 32 /\ inst.inst_opcode = MSTORE /\
  inst.inst_operands = [Lit dst; Var v] /\ g.cg_dst = w2n dst /\
  step_inst fuel ctx inst s = OK s' /\ lookup_var v s = lookup_var v t /\
  lookup_var v s = SOME (mload g.cg_src t) ==>
  ?fin.
    apply_groups_inst_supply Mem2Mem nop_set rep_map sk inst = ([inst],sk) /\
    step_inst fuel ctx inst t = OK fin /\
    fin = write_memory_with_expansion g.cg_dst (read_memory g.cg_src g.cg_length t) t /\
    fin.vs_memory =
      (write_memory_with_expansion g.cg_dst (read_memory g.cg_src g.cg_length t) t).vs_memory /\
    (!x. lookup_var x fin = lookup_var x t)
Proof
  strip_tac >>
  drule_all mm_local_mem2mem_retained_runtime >>
  disch_then (qspec_then `sk` strip_assume_tac) >>
  gvs[mmCopyEquivTheory.mload_mstore_eq_mcopy_state,
    venomExecSemanticsTheory.mcopy_def, venomStateTheory.read_memory_def]
QED

Theorem mm_local_mem2mem_bulk_runtime:
  ~MEM inst.inst_id nop_set /\ ALOOKUP rep_map inst.inst_id = SOME g /\
  g.cg_length <> 32 /\ g.cg_dst < dimword (:256) /\
  g.cg_src < dimword (:256) /\ g.cg_length < dimword (:256) ==>
  ?out fin.
    apply_groups_inst_supply Mem2Mem nop_set rep_map sk inst = ([out],sk) /\
    step_inst fuel ctx out t = OK fin /\
    fin = write_memory_with_expansion g.cg_dst (read_memory g.cg_src g.cg_length t) t /\
    (fin with vs_inst_idx := SUC t.vs_inst_idx) =
      (write_memory_with_expansion g.cg_dst (read_memory g.cg_src g.cg_length t) t
        with vs_inst_idx := SUC t.vs_inst_idx) /\
    fin.vs_memory =
      (write_memory_with_expansion g.cg_dst (read_memory g.cg_src g.cg_length t) t).vs_memory /\
    (!x. lookup_var x fin = lookup_var x t)
Proof
  strip_tac >>
  qexistsl [`mk_bulk_copy_inst Mem2Mem inst g`,
    `write_memory_with_expansion g.cg_dst (read_memory g.cg_src g.cg_length t) t`] >>
  simp[mm_local_mem2mem_bulk_emission, mm_local_mem2mem_bulk_step,
    venomStateTheory.write_memory_with_expansion_def, venomStateTheory.lookup_var_def]
QED

Theorem mm_local_runtime_representative_store_payload:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\
  k <= 4 /\ mm_local_prefix fn0 supply index k = (bb,sk) /\
  MEM (SOME Mem2Mem) (DROP k [NONE; SOME CalldataMerge; SOME DloadMerge; SOME Mem2Mem]) /\
  is = bb.bb_instructions /\ h = phi_prefix_length is /\ h <= r /\ r < LENGTH is /\
  gs = (scan_block (dfg_build_function fn0) Mem2Mem bb).ss_flushed /\ MEM g gs /\
  rep_of_group is g = SOME ((EL r is).inst_id,g) /\
  (EL r is).inst_opcode = MSTORE /\ (EL r is).inst_operands = [Lit dst; Var v] /\
  g.cg_length = 32 /\
  (!q. h <= q /\ q < r ==> ~is_terminator (EL q is).inst_opcode /\
    ?z. step_inst fuel ctx (EL q is) (H q) = OK z /\
      H (SUC q) = z with vs_inst_idx := SUC (H q).vs_inst_idx) /\
  a = mm_local_epoch_start is gs r /\
  u = FOLDL (\st q. if MEM q (mm_local_pending_indices is gs r) then st else
    case mm_local_write_capture is H (SUC r) q of NONE => st
    | SOME (d,bs) => write_memory_with_expansion d bs st)
    (H a) (MAP (\q. a+q) (COUNT_LIST (r-a))) /\
  t.vs_memory = u.vs_memory ==>
  g.cg_dst = w2n dst /\ lookup_var v (H r) = SOME (mload g.cg_src t)
Proof
  strip_tac >>
  qabbrev_tac `due = FILTER (\j. mm_local_rep_index is gs j = r)
    (mm_local_pending_indices is gs r)` >>
  qabbrev_tac `s0 = FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem)
    empty_scan_state (TAKE r is)` >>
  `MEM r (due ++ [r])` by simp[] >>
  `due = FILTER (\j. mm_local_rep_index is gs j = r)
    (mm_local_pending_indices is gs r)` by simp[Abbr `due`] >>
  `s0 = FOLDL (scan_inst (dfg_build_function fn0) Mem2Mem)
    empty_scan_state (TAKE r is)` by simp[Abbr `s0`] >>
  drule_all mm_local_canonical_due_birth_geometry >> strip_tac
  >- (qpat_x_assum `(EL r is).inst_opcode = MCOPY` mp_tac >> simp[]) >>
  qpat_x_assum `(EL r is).inst_operands = [Lit dj; Var vj]` mp_tac >>
  simp[] >> strip_tac >>
  fs[] >>
  `g.cg_dst = w2n dj /\ srcj = g.cg_src` by fs[] >>
  `lookup_var vj (H r) = SOME (mload g.cg_src (H r))` by
    (drule_at (Pat `mm_local_prefix _ _ _ _ = _`) mm_local_runtime_live_load >>
     disch_then irule >> goal_assum (drule_at Any) >>
     simp[] >> qexistsl [`ctx`,`fuel`] >> gvs[]) >>
  `!q. a <= q /\ q < r ==> (H (SUC q)).vs_memory =
    (case mm_local_write_capture is H (SUC r) q of NONE => H q
     | SOME (d,bs) => write_memory_with_expansion d bs (H q)).vs_memory` by
    metis_tac[mm_local_runtime_epoch_recurrence] >>
  `read_memory c.cg_src c.cg_length t = read_memory c.cg_src c.cg_length (H r)` by
    (irule (cj 1 mm_local_epoch_source_read_interval) >>
     goal_assum (drule_at (Pat `mm_local_prefix _ _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `t.vs_memory = _`)) >>
     goal_assum (drule_at (Pat `a = mm_local_epoch_start _ _ _`)) >>
     gvs[]) >>
  qpat_x_assum `c = _` SUBST_ALL_TAC >>
  fs[venomStateTheory.mload_def, venomStateTheory.read_memory_def] >> gvs[]
QED

Theorem mm_local_retained_operand_not_deleted[local]:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\ k <= 4 /\
  mm_local_prefix fn0 supply index k = (bb,sk) /\
  ns = nop_ids_of_groups (dfg_build_function fn0) mode bb.bb_instructions
    (scan_block (dfg_build_function fn0) mode bb).ss_flushed /\
  rs = rep_map_of_groups bb.bb_instructions
    (scan_block (dfg_build_function fn0) mode bb).ss_flushed /\
  excluded = {v | ?q. MEM q bb.bb_instructions /\ MEM q.inst_id ns /\ MEM v q.inst_outputs} /\
  MEM inst bb.bb_instructions /\ MEM v (venomInst$inst_uses inst) /\
  apply_groups_inst_supply mode ns rs es inst = ([inst],es') ==>
  v NOTIN excluded
Proof
  strip_tac >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) bb.bb_instructions)` by
    metis_tac[mm_local_prefix_wf_id_distinct] >>
  `fn_inst_wf (fn0 with fn_blocks := LUPDATE bb index fn0.fn_blocks)` by
    metis_tac[mm_local_prefix_inst_wf] >>
  `MEM bb (LUPDATE bb index fn0.fn_blocks)` by
    (simp[MEM_EL] >> qexists `index` >> simp[EL_LUPDATE]) >>
  `!q. MEM q bb.bb_instructions ==> inst_wf q` by
    (gvs[fn_inst_wf_def, EVERY_MEM] >> metis_tac[]) >>
  `v NOTIN excluded` by
    (strip_tac >> gvs[] >>
     `~MEM q.inst_id
       (nop_ids_of_groups (dfg_build_function fn0) mode bb.bb_instructions
         (scan_block (dfg_build_function fn0) mode bb).ss_flushed)` by
       (irule mm_local_surviving_demand_not_deleted >>
        goal_assum (drule_at Any) >>
        goal_assum (drule_at Any) >> simp[] >>
        goal_assum (drule_at Any) >>
        goal_assum (drule_at Any) >> simp[] >>
        goal_assum (drule_at Any) >>
        goal_assum (drule_at Any) >> simp[] >>
        qexistsl [`[inst]`, `es`, `es'`] >> simp[]) >>
     gvs[]) >>
  metis_tac[]
QED

Theorem mm_local_retained_operand_agreement:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\ k <= 4 /\
  mm_local_prefix fn0 supply index k = (bb,sk) /\
  ns = nop_ids_of_groups (dfg_build_function fn0) mode bb.bb_instructions
    (scan_block (dfg_build_function fn0) mode bb).ss_flushed /\
  rs = rep_map_of_groups bb.bb_instructions
    (scan_block (dfg_build_function fn0) mode bb).ss_flushed /\
  excluded = {v | ?q. MEM q bb.bb_instructions /\ MEM q.inst_id ns /\ MEM v q.inst_outputs} /\
  (!v. v NOTIN excluded ==> lookup_var v s = lookup_var v t) /\
  MEM inst bb.bb_instructions /\ MEM v (venomInst$inst_uses inst) /\
  apply_groups_inst_supply mode ns rs es inst = ([inst],es') ==>
  lookup_var v s = lookup_var v t
Proof
  metis_tac[mm_local_retained_operand_not_deleted]
QED

Theorem mm_local_retained_operand_protected:
  wf_ssa fn0 /\ fn_inst_wf fn0 /\ wf_function fn0 /\
  ir_supply_covers_fn supply fn0 /\ index < LENGTH fn0.fn_blocks /\ k <= 4 /\
  mm_local_prefix fn0 supply index k = (bb,sk) /\
  ns = nop_ids_of_groups (dfg_build_function fn0) mode bb.bb_instructions
    (scan_block (dfg_build_function fn0) mode bb).ss_flushed /\
  rs = rep_map_of_groups bb.bb_instructions
    (scan_block (dfg_build_function fn0) mode bb).ss_flushed /\
  deleted = {v | ?q. MEM q bb.bb_instructions /\ MEM q.inst_id ns /\ MEM v q.inst_outputs} /\
  excluded = {v | ~MEM v sk.irs_used_vars \/ v IN deleted} /\
  MEM inst bb.bb_instructions /\ MEM v (venomInst$inst_uses inst) /\
  apply_groups_inst_supply mode ns rs es inst = ([inst],es') ==>
  MEM v sk.irs_used_vars /\ v NOTIN deleted /\ v NOTIN excluded
Proof
  strip_tac >>
  `v NOTIN deleted` by
    (irule mm_local_retained_operand_not_deleted >> metis_tac[]) >>
  `ir_supply_covers_fn sk (fn0 with fn_blocks := LUPDATE bb index fn0.fn_blocks)` by
    (irule mm_local_prefix_supply_covers >> metis_tac[]) >>
  `MEM bb (LUPDATE bb index fn0.fn_blocks)` by
    (simp[MEM_EL] >> qexists `index` >> simp[EL_LUPDATE]) >>
  `mm_local_inst_covered sk inst` by
    (gvs[mm_local_supply_coverage, EVERY_MEM] >> metis_tac[]) >>
  gvs[mm_local_inst_covered_def, irSupplyTheory.inst_ir_vars_def,
    list_subset_def, EVERY_MEM] >> metis_tac[]
QED

Theorem mm_local_emission_fresh_excluded:
  mm_flat_map_supply (apply_groups_inst_supply mode ns rs) sk xs = (out,es) /\
  fresh_inst_id es = (lid,es1) /\ fresh_ir_var es1 = (v,es2) /\
  excluded = {x | ~MEM x sk.irs_used_vars \/ x IN deleted} ==>
  v IN excluded
Proof
  strip_tac >>
  `ir_supply_extends sk es` by
    (drule_at (Pat `mm_flat_map_supply _ _ _ = _`) mm_local_list_resources >>
     (impl_tac >- metis_tac[mm_local_mode_resources]) >> simp[]) >>
  drule irSupplyTheory.fresh_ir_var_contract >>
  gvs[irSupplyTheory.fresh_inst_id_def, ir_supply_extends_def,
    list_subset_def, EVERY_MEM] >> metis_tac[]
QED

