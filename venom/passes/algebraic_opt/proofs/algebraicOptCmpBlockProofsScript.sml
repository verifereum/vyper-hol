Theory algebraicOptCmpBlockProofs
Ancestors
  algebraicOptCmpChunkProofs algebraicOptCmpLayoutProofs
  venomExecSemantics venomInst venomState list rich_list
  algebraicOptCmpSimulationProofs stateEquiv stateFrame
  algebraicOptCmpCoherenceProofs algebraicOptCmpStepProofs
  algebraicOptCmpScanProofs algebraicOptDefs dfgDefs venomFnScheduleRunner
  irSupply pred_set alist

Theorem ao_cmp_get_instruction_drop:
  DROP n bb.bb_instructions = inst::rest ==>
  get_instruction bb n = SOME inst /\
  DROP (SUC n) bb.bb_instructions = rest
Proof
  strip_tac >>
  `n < LENGTH bb.bb_instructions` by
    (Cases_on `n < LENGTH bb.bb_instructions` >> simp[] >>
     gvs[DROP_LENGTH_TOO_LONG]) >>
  gvs[DROP_CONS_EL, get_instruction_def]
QED

Theorem ao_cmp_exec_block_chunk:
  !chunk bb s rest fuel ctx.
  DROP s.vs_inst_idx bb.bb_instructions = chunk ++ rest /\
  EVERY (\i. ~is_terminator i.inst_opcode) chunk ==>
  exec_block fuel ctx bb s =
    case ao_cmp_exec_chunk fuel ctx chunk s of
      OK u => exec_block fuel ctx bb u
    | IntRet vals u => IntRet vals u
    | Halt u => Halt u
    | Abort a u => Abort a u
    | Error e => Error e
Proof
  Induct >> simp[ao_cmp_exec_chunk_def] >>
  rpt gen_tac >> strip_tac >>
  drule ao_cmp_get_instruction_drop >> strip_tac >>
  CONV_TAC (LHS_CONV (REWR_CONV (cj 2 run_defs))) >> simp[] >>
  Cases_on `step_inst fuel ctx h s` >>
  simp[ao_cmp_exec_chunk_def] >>
  first_x_assum irule >> simp[]
QED

Theorem ao_cmp_exec_chunk_index:
  !chunk fuel ctx s u.
    ao_cmp_exec_chunk fuel ctx chunk s = OK u ==>
    u.vs_inst_idx = s.vs_inst_idx + LENGTH chunk
Proof
  Induct >> simp[ao_cmp_exec_chunk_def] >> rpt gen_tac >>
  Cases_on `step_inst fuel ctx h s` >> simp[] >> strip_tac >>
  first_x_assum drule >> simp[]
QED

(* Suffix induction is independent of how the comparator actions were found. *)
Theorem ao_cmp_exec_block_suffix:
  !xs bb bb' s t fuel ctx C ignored flipped.
    DROP s.vs_inst_idx bb.bb_instructions = xs /\
    DROP t.vs_inst_idx bb'.bb_instructions = FLAT (MAP C xs) /\
    ao_cmp_state_rel ignored flipped s t /\
    s.vs_current_bb = t.vs_current_bb /\ s.vs_prev_bb = t.vs_prev_bb /\
    (!i. MEM i xs ==>
      (is_terminator i.inst_opcode ==> C i = [i]) /\
      (~is_terminator i.inst_opcode ==>
        EVERY (\j. ~is_terminator j.inst_opcode) (C i))) /\
    (!i u v. MEM i xs /\ ao_cmp_state_rel ignored flipped u v /\
      u.vs_current_bb = v.vs_current_bb /\ u.vs_prev_bb = v.vs_prev_bb ==>
      (?e. step_inst fuel ctx i u = Error e) \/
      lift_result
        (\a b. ao_cmp_state_rel ignored flipped a b /\
          a.vs_current_bb = b.vs_current_bb /\ a.vs_prev_bb = b.vs_prev_bb)
        (execution_equiv UNIV) (execution_equiv UNIV)
        (step_inst fuel ctx i u)
        (if is_terminator i.inst_opcode then step_inst fuel ctx i v
         else ao_cmp_exec_chunk fuel ctx (C i) v)) ==>
    (?e. exec_block fuel ctx bb s = Error e) \/
    lift_result
      (\a b. ao_cmp_state_rel ignored flipped a b /\
        a.vs_current_bb = b.vs_current_bb /\ a.vs_prev_bb = b.vs_prev_bb)
      (execution_equiv UNIV) (execution_equiv UNIV)
      (exec_block fuel ctx bb s) (exec_block fuel ctx bb' t)
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- (`get_instruction bb s.vs_inst_idx = NONE` by
        (qpat_x_assum `DROP s.vs_inst_idx _ = []` mp_tac >>
         rewrite_tac[GSYM LENGTH_EQ_0, LENGTH_DROP] >>
         simp[get_instruction_def]) >>
      disj1_tac >> CONV_TAC (BINDER_CONV (LAND_CONV (REWR_CONV (cj 2 run_defs)))) >>
      simp[]) >>
  `get_instruction bb s.vs_inst_idx = SOME h /\
   DROP (SUC s.vs_inst_idx) bb.bb_instructions = xs` by
    metis_tac[ao_cmp_get_instruction_drop] >>
  `(?e. step_inst fuel ctx h s = Error e) \/
    lift_result
      (\a b. ao_cmp_state_rel ignored flipped a b /\
        a.vs_current_bb = b.vs_current_bb /\ a.vs_prev_bb = b.vs_prev_bb)
      (execution_equiv UNIV) (execution_equiv UNIV)
      (step_inst fuel ctx h s)
      (if is_terminator h.inst_opcode then step_inst fuel ctx h t
       else ao_cmp_exec_chunk fuel ctx (C h) t)` by
    (first_x_assum irule >> simp[]) 
  >- (disj1_tac >> CONV_TAC (BINDER_CONV (LAND_CONV (REWR_CONV (cj 2 run_defs)))) >>
      simp[]) >>
  Cases_on `is_terminator h.inst_opcode`
  >- suspend "terminator" >>
  suspend "nonterminator"
QED

Resume ao_cmp_exec_block_suffix[terminator]:
  `C h = [h]` by metis_tac[MEM] >>
  `get_instruction bb' t.vs_inst_idx = SOME h` by
    (irule (cj 1 ao_cmp_get_instruction_drop) >> simp[]) >>
  qpat_x_assum `lift_result _ _ _ _ _` mp_tac >>
  simp[] >> disch_tac >>
  CONV_TAC (LAND_CONV (BINDER_CONV (LAND_CONV (REWR_CONV (cj 2 run_defs))))) >>
  CONV_TAC (RAND_CONV (RAND_CONV (REWR_CONV (cj 2 run_defs)))) >>
  CONV_TAC (RAND_CONV (LAND_CONV (REWR_CONV (cj 2 run_defs)))) >>
  Cases_on `step_inst fuel ctx h s` >> Cases_on `step_inst fuel ctx h t` >>
  gvs[lift_result_def] >>
  qpat_x_assum `!bb bb' s t fuel ctx C ignored flipped. _` kall_tac >>
  qpat_x_assum `!i u v. _` kall_tac >>
  qpat_x_assum `!i. _` kall_tac >>
  `execution_frame v = execution_frame v'` by gvs[ao_cmp_state_rel_def] >>
  `v.vs_halted = v'.vs_halted` by
    (qpat_assum `execution_frame v = _`
       (mp_tac o AP_TERM ``\s:venom_state. s.vs_halted``) >> simp_tac (srw_ss()) [execution_frame_def]) >>
  Cases_on `v'.vs_halted` >> simp[lift_result_def, execution_equiv_def] >>
  qpat_x_assum `execution_frame v = _` mp_tac >>
  simp[execution_frame_def, venom_state_component_equality]
QED

Resume ao_cmp_exec_block_suffix[nonterminator]:
  `exec_block fuel ctx bb' t =
    case ao_cmp_exec_chunk fuel ctx (C h) t of
      OK u => exec_block fuel ctx bb' u
    | IntRet vals u => IntRet vals u
    | Halt u => Halt u
    | Abort a u => Abort a u
    | Error e => Error e` by
    (irule ao_cmp_exec_block_chunk >>
     conj_tac >- (qexists_tac `FLAT (MAP C xs)` >> simp[]) >>
     metis_tac[MEM]) >>
  CONV_TAC (LAND_CONV (BINDER_CONV (LAND_CONV (REWR_CONV (cj 2 run_defs))))) >>
  CONV_TAC (RAND_CONV (LAND_CONV (REWR_CONV (cj 2 run_defs)))) >>
  Cases_on `step_inst fuel ctx h s` >>
  Cases_on `ao_cmp_exec_chunk fuel ctx (C h) t` >>
  gvs[lift_result_def] >>
  drule ao_cmp_exec_chunk_index >> strip_tac >>
  `DROP v'.vs_inst_idx bb'.bb_instructions =
     FLAT (MAP C (DROP (SUC s.vs_inst_idx) bb.bb_instructions))` by
    (qpat_x_assum `DROP t.vs_inst_idx _ = _` mp_tac >>
     disch_then (mp_tac o Q.AP_TERM `DROP (LENGTH (C h))`) >>
     qpat_x_assum `v'.vs_inst_idx = _` SUBST1_TAC >>
     simp_tac (srw_ss()) [DROP_DROP_T, DROP_APPEND, arithmeticTheory.ADD_COMM]) >>
  first_x_assum irule >>
  simp[] >> conj_tac
  >- (qexists_tac `C` >> simp[] >> metis_tac[]) >>
  qpat_x_assum `ao_cmp_state_rel ignored flipped v v'` mp_tac >>
  simp_tac (srw_ss()) [ao_cmp_state_rel_def, execution_frame_updates, lookup_var_def]
QED

Finalise ao_cmp_exec_block_suffix

Theorem ao_cmp_instruction_boundary:
  !fn fs rs ins supply ns supply' inst ignored flipped fuel ctx s t.
    ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn)) /\
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) (fn_insts fn))) /\
    ao_cmp_flip_scan (dfg_build_function fn) (fn_insts fn) = (fs,rs,ins) /\
    ao_name_inserts_supply supply ins = (ns,supply') /\
    ir_supply_inst_ok supply /\ ir_supply_covers_fn supply fn /\
    ignored = set supply'.irs_used_vars DIFF set supply.irs_used_vars /\
    flipped = ao_cmp_flipped (dfg_build_function fn) (fn_insts fn) fs /\
    MEM inst (fn_insts fn) /\
    ((inst.inst_opcode = ISZERO \/ inst.inst_opcode = ASSERT) ==>
      LENGTH inst.inst_operands = 1) /\
    ao_cmp_state_rel ignored flipped s t /\
    s.vs_current_bb = t.vs_current_bb /\ s.vs_prev_bb = t.vs_prev_bb ==>
    (?e. step_inst fuel ctx inst s = Error e) \/
    lift_result
      (\u v. ao_cmp_state_rel ignored flipped u v /\
        u.vs_current_bb = v.vs_current_bb /\ u.vs_prev_bb = v.vs_prev_bb)
      (execution_equiv UNIV) (execution_equiv UNIV)
      (step_inst fuel ctx inst s)
      (if is_terminator inst.inst_opcode then step_inst fuel ctx inst t
       else ao_cmp_exec_chunk fuel ctx (ao_cmp_flip_apply_inst fs rs ns inst) t)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `ALOOKUP fs inst.inst_id <> NONE \/ MEM inst.inst_id rs \/
    ALOOKUP ns inst.inst_id <> NONE`
  >- (drule_all ao_cmp_selected_chunk_shape >> strip_tac >>
      simp[] >> irule ao_cmp_selected_chunk >> metis_tac[]) >>
  `ao_cmp_flip_apply_inst fs rs ns inst = [inst]` by
    (irule ao_cmp_untouched_apply >> gvs[]) >>
  `DISJOINT (set (operand_vars inst.inst_operands)) flipped /\
   DISJOINT (set inst.inst_outputs) flipped` by
    (gvs[] >> irule ao_cmp_untouched_vars >> gvs[] >> metis_tac[]) >>
  `DISJOINT (set (inst_ir_vars inst)) ignored` by
    (gvs[] >> irule ao_cmp_ignored_inst_vars >> metis_tac[]) >>
  `(?e. step_inst fuel ctx inst s = Error e) \/
    lift_result
      (\u v. ao_cmp_state_rel ignored flipped u v /\
        u.vs_current_bb = v.vs_current_bb /\ u.vs_prev_bb = v.vs_prev_bb)
      (execution_equiv UNIV) (execution_equiv UNIV)
      (step_inst fuel ctx inst s) (step_inst fuel ctx inst t)` by
    (irule ao_cmp_step >> simp[] >>
     gvs[DISJOINT_ALT, inst_ir_vars_def, inst_uses_def,
       passSharedDefsTheory.MEM_operand_vars_eq_Var,
       EVERY_MEM] >> metis_tac[]) 
  >- metis_tac[] >>
  Cases_on `is_terminator inst.inst_opcode` >- (gvs[] >> metis_tac[]) >>
  simp[ao_cmp_exec_chunk_single] >>
  Cases_on `step_inst fuel ctx inst s` >>
  Cases_on `step_inst fuel ctx inst t` >> gvs[lift_result_def] >>
  qpat_x_assum `ao_cmp_state_rel _ _ _ _` mp_tac >>
  simp_tac (srw_ss()) [ao_cmp_state_rel_def, execution_frame_updates, lookup_var_def] >>
  metis_tac[]
QED

Theorem ao_cmp_exec_block_expanded:
  !fn fs rs ins supply ns supply' bb bb' ignored flipped fuel ctx s t.
    ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn)) /\
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) (fn_insts fn))) /\
    ao_cmp_flip_scan (dfg_build_function fn) (fn_insts fn) = (fs,rs,ins) /\
    ao_name_inserts_supply supply ins = (ns,supply') /\
    ir_supply_inst_ok supply /\ ir_supply_covers_fn supply fn /\
    ignored = set supply'.irs_used_vars DIFF set supply.irs_used_vars /\
    flipped = ao_cmp_flipped (dfg_build_function fn) (fn_insts fn) fs /\
    (!i. MEM i bb.bb_instructions ==> MEM i (fn_insts fn) /\
      ((i.inst_opcode = ISZERO \/ i.inst_opcode = ASSERT) ==>
        LENGTH i.inst_operands = 1)) /\
    ao_cmp_state_rel ignored flipped s t /\
    s.vs_current_bb = t.vs_current_bb /\ s.vs_prev_bb = t.vs_prev_bb /\
    s.vs_inst_idx <= LENGTH bb.bb_instructions /\
    t.vs_inst_idx = LENGTH (FLAT (MAP (ao_cmp_flip_apply_inst fs rs ns)
      (TAKE s.vs_inst_idx bb.bb_instructions))) /\
    bb' = bb with bb_instructions :=
      FLAT (MAP (ao_cmp_flip_apply_inst fs rs ns) bb.bb_instructions) ==>
    (?e. exec_block fuel ctx bb s = Error e) \/
    lift_result
      (\u v. ao_cmp_state_rel ignored flipped u v /\
        u.vs_current_bb = v.vs_current_bb /\ u.vs_prev_bb = v.vs_prev_bb)
      (execution_equiv UNIV) (execution_equiv UNIV)
      (exec_block fuel ctx bb s) (exec_block fuel ctx bb' t)
Proof
  rpt gen_tac >> strip_tac >>
  irule ao_cmp_exec_block_suffix >>
  simp[] >> qexists_tac `ao_cmp_flip_apply_inst fs rs ns` >>
  simp[ao_cmp_expand_drop] >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `MEM i bb.bb_instructions` by
        (qpat_x_assum `MEM i (DROP _ _)` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         pure_rewrite_tac [MEM_DROP] >> metis_tac[MEM_EL]) >>
      `MEM i (fn_insts fn) /\
       ((i.inst_opcode = ISZERO \/ i.inst_opcode = ASSERT) ==>
         LENGTH i.inst_operands = 1)` by metis_tac[] >>
      irule ao_cmp_instruction_boundary >> simp[] >>
      conj_tac >- metis_tac[] >>
      qexistsl_tac [`fn`, `ins`, `supply`, `supply'`] >> simp[]) >>
  rpt gen_tac >> disch_tac >>
  `MEM i bb.bb_instructions` by
    (qpat_x_assum `MEM i (DROP _ _)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     pure_rewrite_tac [MEM_DROP] >> metis_tac[MEM_EL]) >>
  `MEM i (fn_insts fn)` by metis_tac[] >>
  Cases_on `ALOOKUP fs i.inst_id <> NONE \/ MEM i.inst_id rs \/
    ALOOKUP ns i.inst_id <> NONE`
  >- (drule_all ao_cmp_selected_chunk_shape >> simp[]) >>
  `ao_cmp_flip_apply_inst fs rs ns i = [i]` by
    (irule ao_cmp_untouched_apply >> gvs[]) >> simp[]
QED

Theorem ao_cmp_run_block_expanded:
  !fn fs rs ins supply ns supply' bb bb' ignored flipped fuel ctx s t.
    ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn)) /\
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) (fn_insts fn))) /\
    ao_cmp_flip_scan (dfg_build_function fn) (fn_insts fn) = (fs,rs,ins) /\
    ao_name_inserts_supply supply ins = (ns,supply') /\
    ir_supply_inst_ok supply /\ ir_supply_covers_fn supply fn /\
    ignored = set supply'.irs_used_vars DIFF set supply.irs_used_vars /\
    flipped = ao_cmp_flipped (dfg_build_function fn) (fn_insts fn) fs /\
    (!i. MEM i bb.bb_instructions ==> MEM i (fn_insts fn) /\
      ((i.inst_opcode = ISZERO \/ i.inst_opcode = ASSERT) ==>
        LENGTH i.inst_operands = 1)) /\
    ao_cmp_state_rel ignored flipped s t /\
    s.vs_current_bb = t.vs_current_bb /\ s.vs_prev_bb = t.vs_prev_bb /\
    bb' = bb with bb_instructions :=
      FLAT (MAP (ao_cmp_flip_apply_inst fs rs ns) bb.bb_instructions) ==>
    (?e. run_block fuel ctx bb s = Error e) \/
    lift_result
      (\u v. ao_cmp_state_rel ignored flipped u v /\
        u.vs_current_bb = v.vs_current_bb /\ u.vs_prev_bb = v.vs_prev_bb)
      (execution_equiv UNIV) (execution_equiv UNIV)
      (run_block fuel ctx bb s) (run_block fuel ctx bb' t)
Proof
  rpt gen_tac >> strip_tac >>
  `!i. MEM i bb.bb_instructions ==> MEM i (fn_insts fn)` by metis_tac[] >>
  `bb'.bb_instructions =
    FLAT (MAP (ao_cmp_flip_apply_inst fs rs ns) bb.bb_instructions)` by simp[] >>
  `phi_prefix_length bb'.bb_instructions = phi_prefix_length bb.bb_instructions /\
   ((?e. eval_phis s bb.bb_instructions = Error e /\
         eval_phis t bb'.bb_instructions = Error e) \/
    (?u v. eval_phis s bb.bb_instructions = OK u /\
      eval_phis t bb'.bb_instructions = OK v /\
      ao_cmp_state_rel ignored flipped
        (u with vs_inst_idx := phi_prefix_length bb.bb_instructions)
        (v with vs_inst_idx := phi_prefix_length bb'.bb_instructions) /\
      u.vs_prev_bb = v.vs_prev_bb /\ u.vs_current_bb = v.vs_current_bb))` by
    (irule ao_cmp_expanded_phi_entry >> simp[] >>
     qexistsl_tac [`fn`, `fs`, `ins`, `ns`, `rs`, `supply`, `supply'`] >> simp[])
  >- (disj1_tac >> simp[run_block_def]) >>
  `FLAT (MAP (ao_cmp_flip_apply_inst fs rs ns)
     (TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions)) =
     TAKE (phi_prefix_length bb.bb_instructions) bb.bb_instructions /\
   phi_prefix_length bb.bb_instructions <= LENGTH bb.bb_instructions` by
    (irule ao_cmp_expand_take_phis >> rpt strip_tac >>
     irule ao_cmp_phi_chunk >> metis_tac[]) >>
  simp[run_block_def] >>
  irule ao_cmp_exec_block_expanded >> simp[] >>
  reverse conj_tac >- gvs[] >>
  qexistsl_tac [`fn`, `fs`, `ins`, `ns`, `rs`, `supply`, `supply'`] >>
  simp[] >> metis_tac[]
QED
