Theory algebraicOptCmpRunProofs
Ancestors
  algebraicOptCmpBlockProofs algebraicOptCmpSimulationProofs
  algebraicOptCmpProvenanceProofs algebraicOptCmpCoherenceProofs
  algebraicOptCmpScanProofs algebraicOptDefs venomExecSemantics venomExecProps venomInst venomState
  stateEquiv stateFrame list rich_list pred_set alist irSupply
  venomFnScheduleRunner

Theorem ao_cmp_lookup_expanded_blocks:
  !bbs lbl C.
    lookup_block lbl (MAP (\bb. bb with bb_instructions :=
      FLAT (MAP C bb.bb_instructions)) bbs) =
    OPTION_MAP (\bb. bb with bb_instructions :=
      FLAT (MAP C bb.bb_instructions)) (lookup_block lbl bbs)
Proof
  Induct >> simp[lookup_block_def, FIND_thm] >> rpt gen_tac >>
  Cases_on `h.bb_label = lbl` >> gvs[lookup_block_def]
QED

Theorem ao_cmp_lookup_apply_fn:
  lookup_block lbl (ao_cmp_flip_apply_fn fs rs ns fn).fn_blocks =
  OPTION_MAP (\bb. bb with bb_instructions :=
    FLAT (MAP (ao_cmp_flip_apply_inst fs rs ns) bb.bb_instructions))
    (lookup_block lbl fn.fn_blocks)
Proof
  simp[ao_cmp_flip_apply_fn_def, ao_cmp_lookup_expanded_blocks]
QED

Theorem ao_cmp_run_blocks_lift:
  !fuel fn fn' B ignored flipped ctx s t.
    (!lbl. lookup_block lbl fn'.fn_blocks =
      OPTION_MAP B (lookup_block lbl fn.fn_blocks)) /\
    (!k bb u v. MEM bb fn.fn_blocks /\
      ao_cmp_state_rel ignored flipped u v /\
      u.vs_current_bb = v.vs_current_bb /\ u.vs_prev_bb = v.vs_prev_bb ==>
      (?e. run_block k ctx bb u = Error e) \/
      lift_result
        (\a b. ao_cmp_state_rel ignored flipped a b /\
          a.vs_current_bb = b.vs_current_bb /\ a.vs_prev_bb = b.vs_prev_bb)
        (execution_equiv UNIV) (execution_equiv UNIV)
        (run_block k ctx bb u) (run_block k ctx (B bb) v)) /\
    ao_cmp_state_rel ignored flipped s t /\
    s.vs_current_bb = t.vs_current_bb /\ s.vs_prev_bb = t.vs_prev_bb ==>
    (?e. run_blocks fuel ctx fn s = Error e) \/
    lift_result (state_equiv ignored) (execution_equiv UNIV) (execution_equiv UNIV)
      (run_blocks fuel ctx fn s) (run_blocks fuel ctx fn' t)
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- simp[Once run_blocks_def] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks`
  >- (disj1_tac >> simp[run_blocks_unfold]) >>
  rename1 `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` >>
  `MEM bb fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
  `(?e. run_block fuel ctx bb s = Error e) \/
    lift_result
      (\a b. ao_cmp_state_rel ignored flipped a b /\
        a.vs_current_bb = b.vs_current_bb /\ a.vs_prev_bb = b.vs_prev_bb)
      (execution_equiv UNIV) (execution_equiv UNIV)
      (run_block fuel ctx bb s) (run_block fuel ctx (B bb) t)` by
    (first_x_assum irule >> simp[])
  >- (disj1_tac >> simp[run_blocks_unfold]) >>
  `lookup_block t.vs_current_bb fn'.fn_blocks = SOME (B bb)` by
    (qpat_x_assum `!lbl. _` (qspec_then `s.vs_current_bb` mp_tac) >>
     pure_asm_rewrite_tac [] >> simp[]) >>
  simp[run_blocks_unfold] >>
  Cases_on `run_block fuel ctx bb s` >>
  Cases_on `run_block fuel ctx (B bb) t` >> gvs[lift_result_def]
  >- suspend "continue" >>
  metis_tac[]
QED

Resume ao_cmp_run_blocks_lift[continue]:
  `execution_frame v = execution_frame v'` by
    gvs[ao_cmp_state_rel_def] >>
  `v.vs_halted = v'.vs_halted` by
    (qpat_assum `execution_frame v = _`
       (mp_tac o AP_TERM ``\s:venom_state. s.vs_halted``) >>
     simp_tac (srw_ss()) [execution_frame_def]) >>
  Cases_on `v.vs_halted`
  >- gvs[lift_result_def, execution_equiv_def] >>
  qpat_x_assum `execution_frame v = _` kall_tac >>
  gvs[] >> first_x_assum irule >> simp[] >>
  qexistsl_tac [`B`, `flipped`] >> simp[]
QED

Finalise ao_cmp_run_blocks_lift

Theorem ao_cmp_run_blocks_expanded:
  !fn fs rs ins supply ns supply' fn' ignored flipped fuel ctx s t.
    ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn)) /\
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) (fn_insts fn))) /\
    ao_cmp_flip_scan (dfg_build_function fn) (fn_insts fn) = (fs,rs,ins) /\
    ao_name_inserts_supply supply ins = (ns,supply') /\
    ir_supply_inst_ok supply /\ ir_supply_covers_fn supply fn /\
    ignored = set supply'.irs_used_vars DIFF set supply.irs_used_vars /\
    flipped = ao_cmp_flipped (dfg_build_function fn) (fn_insts fn) fs /\
    (!i. MEM i (fn_insts fn) /\ (i.inst_opcode = ISZERO \/ i.inst_opcode = ASSERT) ==>
      LENGTH i.inst_operands = 1) /\
    fn' = ao_cmp_flip_apply_fn fs rs ns fn /\
    ao_cmp_state_rel ignored flipped s t /\
    s.vs_current_bb = t.vs_current_bb /\ s.vs_prev_bb = t.vs_prev_bb ==>
    (?e. run_blocks fuel ctx fn s = Error e) \/
    lift_result (state_equiv ignored) (execution_equiv UNIV) (execution_equiv UNIV)
      (run_blocks fuel ctx fn s) (run_blocks fuel ctx fn' t)
Proof
  rpt gen_tac >> strip_tac >>
  irule ao_cmp_run_blocks_lift >> simp[] >>
  qexistsl_tac [`\bb. bb with bb_instructions :=
    FLAT (MAP (ao_cmp_flip_apply_inst fs rs ns) bb.bb_instructions)`, `flipped`] >>
  conj_tac >- simp[ao_cmp_lookup_apply_fn] >>
  reverse conj_tac >- gvs[] >>
  rpt gen_tac >> strip_tac >>
  irule ao_cmp_run_block_expanded >> simp[] >>
  qexistsl_tac [`fn`, `fs`, `ins`, `ns`, `rs`, `supply`, `supply'`] >>
  simp[] >> rpt strip_tac >>
  `MEM i (fn_insts fn)` by
    (simp[fn_insts_def, unitShapeDefsTheory.MEM_fn_insts_blocks_iff,
       MEM_FLAT, MEM_MAP] >> metis_tac[]) >> metis_tac[]
QED

Theorem ao_cmp_flip_function_supply_run:
  !fn fs rs ins supply fn' supply' ignored fuel ctx s.
    ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn)) /\
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) (fn_insts fn))) /\
    ao_cmp_flip_scan (dfg_build_function fn) (fn_insts fn) = (fs,rs,ins) /\
    ir_supply_inst_ok supply /\ ir_supply_covers_fn supply fn /\
    (!i. MEM i (fn_insts fn) /\ (i.inst_opcode = ISZERO \/ i.inst_opcode = ASSERT) ==>
      LENGTH i.inst_operands = 1) /\
    (!v. v IN ao_cmp_flipped (dfg_build_function fn) (fn_insts fn) fs ==>
      lookup_var v s = NONE) /\
    ao_cmp_flip_function_supply (dfg_build_function fn) supply fn = (fn',supply') /\
    ignored = set supply'.irs_used_vars DIFF set supply.irs_used_vars ==>
    (?e. run_blocks fuel ctx fn s = Error e) \/
    lift_result (state_equiv ignored) (execution_equiv UNIV) (execution_equiv UNIV)
      (run_blocks fuel ctx fn s) (run_blocks fuel ctx fn' s)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `ao_cmp_flip_function_supply _ _ _ = _` mp_tac >>
  simp[ao_cmp_flip_function_supply_def] >>
  Cases_on `NULL fs`
  >- (strip_tac >> gvs[] >>
      Cases_on `run_blocks fuel ctx fn s` >>
      simp[lift_result_def, state_equiv_def, execution_equiv_def]) >>
  Cases_on `ao_name_inserts_supply supply ins` >>
  rename1 `ao_name_inserts_supply supply ins = (ns,sup1)` >>
  strip_tac >> gvs[] >>
  irule ao_cmp_run_blocks_expanded >> simp[] >>
  conj_tac >- metis_tac[] >>
  qexistsl_tac [`ns`, `supply`, `sup1`] >>
  simp[] >> irule ao_cmp_state_rel_initial >> simp[]
QED

Theorem ao_main_comparator_supply_run:
  !fn fn0 sup bbs sup1 mid fs rs ins fn' sup2 fuel ctx s.
    fn0 = fn with fn_blocks :=
      MAP (\bb. bb with bb_instructions :=
        MAP ao_handle_offset_inst bb.bb_instructions) fn.fn_blocks /\
    ao_transform_blocks_supply (dfg_build_function fn0) (range_analyze fn0)
      (ao_compute_fn_iszero_targets fn0) sup fn0.fn_blocks = (bbs,sup1) /\
    mid = fn0 with fn_blocks := bbs /\
    ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts mid)) /\
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) (fn_insts mid))) /\
    ao_cmp_flip_scan (dfg_build_function mid) (fn_insts mid) = (fs,rs,ins) /\
    ir_supply_inst_ok sup1 /\ ir_supply_covers_fn sup1 mid /\
    (!i. MEM i (fn_insts mid) /\ (i.inst_opcode = ISZERO \/ i.inst_opcode = ASSERT) ==>
      LENGTH i.inst_operands = 1) /\
    (!inst x. MEM inst (fn_insts fn) /\ MEM x inst.inst_outputs ==>
      lookup_var x s = NONE) /\
    ao_cmp_flip_function_supply (dfg_build_function mid) sup1 mid = (fn',sup2) ==>
    (?e. run_blocks fuel ctx mid s = Error e) \/
    lift_result (state_equiv (set sup2.irs_used_vars DIFF set sup1.irs_used_vars))
      (execution_equiv UNIV) (execution_equiv UNIV)
      (run_blocks fuel ctx mid s) (run_blocks fuel ctx fn' s)
Proof
  rpt gen_tac >> strip_tac >>
  `!v. v IN ao_cmp_flipped (dfg_build_function mid) (fn_insts mid) fs ==>
     lookup_var v s = NONE` by
    (`!out. MEM out (fn_insts mid) /\ is_comparator out.inst_opcode ==>
       ?inst. MEM inst (fn_insts fn) /\ out.inst_outputs = inst.inst_outputs` by
       (drule ao_main_function_comparator_outputs >>
        disch_then drule >> disch_then drule >> simp[]) >>
     simp[ao_cmp_flipped_def] >> rpt strip_tac >>
     `is_comparator inst.inst_opcode` by
       (qpat_x_assum `ao_cmp_flip_cert _ _ _` mp_tac >>
        simp[ao_cmp_flip_cert_def, ao_cmp_source_def] >> metis_tac[]) >>
     gvs[] >> qpat_x_assum `!out. _` drule_all >> strip_tac >> metis_tac[]) >>
  irule ao_cmp_flip_function_supply_run >> simp[] >>
  conj_tac >- gvs[] >>
  qexistsl_tac [`sup1`, `sup2`] >> gvs[]
QED
