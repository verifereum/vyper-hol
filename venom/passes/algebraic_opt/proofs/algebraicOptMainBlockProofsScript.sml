Theory algebraicOptMainBlockProofs
Ancestors
  algebraicOptMainStepProofs algebraicOptMainLayoutProofs
  algebraicOptMainEntryProofs algebraicOptCmpBlockProofs
  algebraicOptTraceProofs algebraicOptReachabilityProofs
  algebraicOptShapeProofs algebraicOptDefs venomExecSemantics venomWf
  venomInst venomState stateEquiv stateFrame venomExecProps unitShapeDefs
Libs
  listTheory rich_listTheory

Theorem ao_main_nonphi_suffix:
  !insts.
  (!i j. i < j /\ j < LENGTH insts /\
    (EL j insts).inst_opcode = PHI ==> (EL i insts).inst_opcode = PHI) ==>
  EVERY (\i. i.inst_opcode <> PHI) (DROP (phi_prefix_length insts) insts)
Proof
  Induct >> simp[phi_prefix_length_def] >> rpt strip_tac >>
  Cases_on `h.inst_opcode = PHI`
  >- (simp[phi_prefix_length_def] >> first_x_assum irule >>
      rpt strip_tac >> first_x_assum (qspecl_then [`SUC i`, `SUC j`] mp_tac) >> simp[]) >>
  simp[phi_prefix_length_def, EVERY_MEM] >> rpt strip_tac >> gvs[] >>
  `?j. j < LENGTH insts /\ EL j insts = i` by metis_tac[MEM_EL] >>
  first_x_assum (qspecl_then [`0`, `SUC j`] mp_tac) >> simp[]
QED

Theorem ao_main_block_nonphi_suffix:
  bb_well_formed bb ==>
  EVERY (\i. i.inst_opcode <> PHI)
    (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions)
Proof
  strip_tac >> irule ao_main_nonphi_suffix >> fs[bb_well_formed_def]
QED

Theorem ao_main_block_suffix:
  !ys xs s r pre mid.
  ao_source_prefix ctx fn s0 n k F s /\
  wf_function fn /\ wf_ssa fn /\ fn_inst_wf fn /\
  EVERY label_positions_ok (fn_insts fn) /\
  s0.vs_inst_idx = 0 /\ s0.vs_prev_bb = NONE /\
  fn_entry_label fn = SOME s0.vs_current_bb /\
  (!i x. MEM i (fn_insts fn) /\ MEM x i.inst_outputs ==> lookup_var x s0 = NONE) /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  bb.bb_instructions = xs ++ ys /\ s.vs_inst_idx = LENGTH xs /\
  ao_transform_insts_supply (dfg_build_function fn) (range_analyze fn)
    bb.bb_label (ao_compute_fn_iszero_targets fn) supply 0 xs = (pre,mid) /\
  ao_transform_insts_supply (dfg_build_function fn) (range_analyze fn)
    bb.bb_label (ao_compute_fn_iszero_targets fn) supply 0 bb.bb_instructions = (outs,last) /\
  r.vs_inst_idx = LENGTH pre /\ ao_main_observations fn V s r /\
  s with <|vs_vars := r.vs_vars; vs_inst_idx := r.vs_inst_idx|> = r /\
  (!i x. MEM i (fn_insts fn) /\
    (MEM (Var x) i.inst_operands \/ MEM x i.inst_outputs) ==> x IN V) /\
  ir_supply_inst_ok supply /\ V SUBSET set supply.irs_used_vars /\
  EVERY (\i. i.inst_opcode <> PHI) ys ==>
  (?e. exec_block k ctx bb s = Error e) \/
  lift_result
    (\t u. ao_main_observations fn V t u /\
      t with <|vs_vars := u.vs_vars; vs_inst_idx := u.vs_inst_idx|> = u /\
      t.vs_inst_idx = 0 /\ u.vs_inst_idx = 0 /\
      ao_source_prefix ctx fn s0 n k T t)
    (execution_equiv UNIV) (execution_equiv UNIV)
    (exec_block k ctx bb s)
    (exec_block k ctx (bb with bb_instructions := outs) r)
Proof
  Induct
  >- (rpt gen_tac >> strip_tac >> disj1_tac >>
      qexists `"block not terminated"` >>
      once_rewrite_tac[exec_block_def] >>
      simp[get_instruction_def]) >>
  rpt gen_tac >> strip_tac >>
  `get_instruction bb s.vs_inst_idx = SOME h` by
    simp[get_instruction_def, EL_APPEND_EQN] >>
  `MEM h (fn_insts fn)` by
    (simp[fn_insts_def, MEM_fn_insts_blocks_iff] >>
     qexists `bb` >> simp[] >> metis_tac[lookup_block_MEM]) >>
  `bb.bb_label = s.vs_current_bb` by metis_tac[lookup_block_label] >>
  `h.inst_opcode <> PHI /\ EVERY (\i. i.inst_opcode <> PHI) ys` by fs[] >>
  `?fr next post.
    ao_alloc_fresh mid = (fr,next) /\
    ao_transform_insts_supply (dfg_build_function fn) (range_analyze fn)
      bb.bb_label (ao_compute_fn_iszero_targets fn) next (SUC (LENGTH xs)) ys = (post,last) /\
    DROP (LENGTH pre) outs = ao_transform_inst (dfg_build_function fn) (range_analyze fn)
      bb.bb_label (LENGTH xs) (ao_compute_fn_iszero_targets fn) fr h ++ post /\
    ir_supply_inst_ok mid /\ V SUBSET set mid.irs_used_vars` by
    (`ao_transform_insts_supply (dfg_build_function fn) (range_analyze fn)
       bb.bb_label (ao_compute_fn_iszero_targets fn) supply 0 (xs ++ h::ys) = (outs,last)` by metis_tac[] >>
     drule_at (Pat `ao_transform_insts_supply _ _ _ _ _ _ (_ ++ _::_) = _`)
       ao_transform_insts_supply_cursor_step >> simp[] >> metis_tac[]) >>
  Cases_on `is_terminator h.inst_opcode`
  >- suspend "terminator" >>
  suspend "ordinary"
QED
Resume ao_main_block_suffix[terminator]:
  qpat_x_assum `!xs s r pre mid. _` kall_tac >>
  drule ao_source_prefix_has_trace >> strip_tac >>
  `!i x. MEM i (fn_insts fn) /\ MEM x i.inst_outputs ==>
    lookup_var x (SND (SND (HD trace))) = NONE` by (simp[] >> metis_tac[]) >>
  `ao_transform_inst (dfg_build_function fn) (range_analyze fn) bb.bb_label
    (LENGTH xs) (ao_compute_fn_iszero_targets fn) fr h =
    [ao_resolve_iszero_inst (ao_compute_fn_iszero_targets fn) h]` by
    (irule ao_transform_inst_control_owner >> simp[]) >>
  drule_all (cj 2 ao_main_terminator_step) >>
  disch_then (qspec_then `k` strip_assume_tac)
  >- (disj1_tac >> once_rewrite_tac[exec_block_def] >> simp[]) >>
  `get_instruction (bb with bb_instructions := outs) r.vs_inst_idx =
    SOME (ao_resolve_iszero_inst (ao_compute_fn_iszero_targets fn) h)` by
    (irule (cj 1 ao_cmp_get_instruction_drop) >> simp[] >> metis_tac[]) >>
  once_rewrite_tac[exec_block_def] >> simp[ao_resolve_iszero_inst_fields] >>
  Cases_on `step_inst k ctx h s` >>
  Cases_on `step_inst k ctx (ao_resolve_iszero_inst (ao_compute_fn_iszero_targets fn) h) r` >>
  gvs[lift_result_def] >>
  `v.vs_halted = v'.vs_halted` by gvs[venom_state_component_equality] >>
  Cases_on `v.vs_halted`
  >- gvs[lift_result_def, execution_equiv_def, execution_frame_def,
         venom_state_component_equality] >>
  simp[lift_result_def] >>
  `ao_source_step ctx fn (k,F,s) (k,T,v)` by
    (irule (cj 3 ao_source_step_rules) >> simp[] >> metis_tac[]) >>
  drule ao_source_step_prefix >> simp[] >>
  disch_then (qspecl_then [`s0`, `n`] mp_tac) >>
  gvs[lift_result_def]
QED
Resume ao_main_block_suffix[ordinary]:
  drule_all ao_main_ordinary_chunk >> strip_tac
  >- (disj1_tac >> once_rewrite_tac[exec_block_def] >> simp[]) >>
  `EVERY (\i. ~is_terminator i.inst_opcode)
    (ao_transform_inst (dfg_build_function fn) (range_analyze fn)
      bb.bb_label (LENGTH xs) (ao_compute_fn_iszero_targets fn) fr h)` by
    (irule algebraicOptMainShapeProofsTheory.ao_transform_inst_not_terminator >> simp[]) >>
  `exec_block k ctx (bb with bb_instructions := outs) r =
    case ao_cmp_exec_chunk k ctx
      (ao_transform_inst (dfg_build_function fn) (range_analyze fn)
        bb.bb_label (LENGTH xs) (ao_compute_fn_iszero_targets fn) fr h) r of
      OK u => exec_block k ctx (bb with bb_instructions := outs) u
    | IntRet vals u => IntRet vals u
    | Halt u => Halt u
    | Abort a u => Abort a u
    | Error e => Error e` by
    (irule ao_cmp_exec_block_chunk >> simp[] >> metis_tac[]) >>
  qpat_x_assum `exec_block _ _ _ r = _` (fn th => once_rewrite_tac[th]) >>
  CONV_TAC (LAND_CONV (BINDER_CONV (LAND_CONV (REWR_CONV (cj 2 run_defs))))) >>
  CONV_TAC (RAND_CONV (LAND_CONV (REWR_CONV (cj 2 run_defs)))) >> simp[] >>
  Cases_on `step_inst k ctx h s` >>
  Cases_on `ao_cmp_exec_chunk k ctx
      (ao_transform_inst (dfg_build_function fn) (range_analyze fn)
        bb.bb_label (LENGTH xs) (ao_compute_fn_iszero_targets fn) fr h) r` >>
  gvs[lift_result_def] >>
  `ao_source_step ctx fn (k,F,s) (k,F,v with vs_inst_idx := SUC (LENGTH xs))` by
    (qpat_assum `s.vs_inst_idx = _` (fn th => rewrite_tac[GSYM th]) >>
     irule (cj 2 ao_source_step_rules) >> simp[] >> metis_tac[]) >>
  `ao_source_prefix ctx fn s0 n k F (v with vs_inst_idx := SUC (LENGTH xs))` by
    (drule ao_source_step_prefix >> simp[] >>
     disch_then (qspecl_then [`s0`, `n`] mp_tac) >> simp[]) >>
  `v.vs_current_bb = s.vs_current_bb` by
    metis_tac[venomInstPropsTheory.step_preserves_control_flow] >>
  first_x_assum irule >> simp[] >>
  conj_tac >- metis_tac[] >> conj_tac >- metis_tac[] >>
  qexistsl [`next`, `pre ++ ao_transform_inst (dfg_build_function fn) (range_analyze fn)
    s.vs_current_bb (LENGTH xs) (ao_compute_fn_iszero_targets fn) fr h`] >>
  simp[ao_transform_insts_supply_append, Once ao_transform_insts_supply_def] >>
  simp[Once ao_transform_insts_supply_def]
QED
Finalise ao_main_block_suffix
