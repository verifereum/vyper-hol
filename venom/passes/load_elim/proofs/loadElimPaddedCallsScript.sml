Theory loadElimPaddedCalls
Ancestors
  loadElimPaddedNoncall loadElimPaddedSimHelpers loadElimMemoryRel
  loadElimPhiTransport venomExecSemantics venomState stateFrame stateEquiv
  list finite_map

Theorem le_padded_setup_total:
  padded_exec_equiv V s t /\ setup_callee fn args s = SOME c ==>
  ?d. setup_callee fn args t = SOME d /\ le_padded_control {} c d
Proof
  strip_tac >>
  `~NULL fn.fn_blocks` by gvs[setup_callee_def] >>
  simp[setup_callee_def, le_padded_control_def] >>
  conj_tac
  >- (irule padded_exec_equiv_setup_callee >>
      goal_assum (drule_at Any) >>
      qexistsl [`t`, `V`] >> simp[setup_callee_def]) >>
  gvs[setup_callee_def, le_padded_control_def]
QED

Theorem le_padded_bind_total:
  le_padded_control V s t /\ bind_outputs outs vals s = SOME u ==>
  ?v. bind_outputs outs vals t = SOME v /\ le_padded_control V u v
Proof
  strip_tac >>
  `LENGTH outs = LENGTH vals` by gvs[bind_outputs_def] >>
  gvs[bind_outputs_def] >>
  pop_assum kall_tac >>
  qpat_x_assum `le_padded_control V s t` mp_tac >>
  qid_spec_tac `t` >> qid_spec_tac `s` >>
  qspec_tac (`ZIP (outs,vals)`, `pairs`) >>
  Induct >- simp[] >>
  Cases_on `h` >> simp[] >>
  rpt strip_tac >> first_x_assum irule >>
  irule le_padded_control_update_var >> simp[]
QED

Theorem le_padded_control_idx:
  le_padded_control V s t ==>
  le_padded_control V (s with vs_inst_idx := n) (t with vs_inst_idx := n)
Proof
  simp[le_padded_control_def, padded_exec_equiv_def, lookup_var_def,
       read_memory_def, execution_frame_def]
QED

Theorem le_padded_phis_total:
  le_padded_control {} s t /\ eval_phis s js = OK u ==>
  ?v. eval_phis t js = OK v /\ le_padded_control {} u v
Proof
  strip_tac >> irule le_eval_phis_transport >>
  conj_tac >- simp[le_padded_control_update_var] >>
  qexists_tac `s` >> simp[] >> rpt strip_tac >>
  irule le_eval_one_phi_agreement >>
  gvs[le_padded_control_def, padded_exec_equiv_def,
      execution_frame_def, venom_state_component_equality]
QED


Theorem le_padded_return_control:
  le_padded_control V s t /\ padded_exec_equiv callee_vars c d ==>
  le_padded_control V
    (adopt_return_fmp ir (merge_callee_state s c))
    (adopt_return_fmp ir (merge_callee_state t d))
Proof
  strip_tac >> rewrite_tac[le_padded_control_def] >> conj_tac
  >- (irule padded_exec_equiv_adopt_return >>
      irule padded_exec_equiv_merge_callee >>
      gvs[le_padded_control_def] >> metis_tac[]) >>
  Cases_on `ir.iret_adopt_fmp` >>
  gvs[adopt_return_fmp_def, merge_callee_state_def, le_padded_control_def]
QED

Theorem le_padded_full_weaken:
  padded_exec_equiv {} s t ==> padded_exec_equiv V s t
Proof
  simp[padded_exec_equiv_def]
QED

Theorem le_padded_invoke_return:
  le_padded_control V s t /\
  i.inst_opcode = INVOKE /\ decode_invoke i = SOME (name,ops) /\
  lookup_function name C.ctx_functions = SOME fn /\
  eval_operands ops s = SOME args /\ eval_operands ops t = SOME args /\
  setup_callee fn args s = SOME c /\ setup_callee fn args t = SOME d /\
  ((?e. run_blocks fuel C fn c = Error e) \/
   lift_result (le_padded_control {}) (padded_exec_equiv {}) (padded_exec_equiv {})
     (run_blocks fuel C fn c) (run_blocks fuel C fn d)) ==>
  (?e. step_inst fuel C i s = Error e) \/
  lift_result (le_padded_control V) (padded_exec_equiv V) (padded_exec_equiv V)
    (step_inst fuel C i s) (step_inst fuel C i t)
Proof
  strip_tac >> simp[step_inst_def] >>
  Cases_on `run_blocks fuel C fn c` >>
  Cases_on `run_blocks fuel C fn d` >>
  gvs[lift_result_def] >>
  simp[le_padded_full_weaken] >>
  qmatch_goalsub_rename_tac `bind_outputs i.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state s cs))` >>
  rename1 `padded_exec_equiv {} cs ct` >>
  Cases_on `bind_outputs i.inst_outputs ret.iret_values
    (adopt_return_fmp ret (merge_callee_state s cs))` >>
  simp[lift_result_def] >>
  `le_padded_control V (adopt_return_fmp ret (merge_callee_state s cs))
    (adopt_return_fmp ret (merge_callee_state t ct))` by
      (irule le_padded_return_control >> metis_tac[]) >>
  drule_all le_padded_bind_total >> strip_tac >> simp[lift_result_def]
QED

Theorem le_padded_same_program_mutual:
  (!fuel C i s. !t.
    le_padded_control {} s t /\ i.inst_opcode <> MEMTOP /\
    EVERY (\f. EVERY (\j. j.inst_opcode <> MEMTOP) (fn_insts f)) C.ctx_functions ==>
    (?e. step_inst fuel C i s = Error e) \/
    lift_result (le_padded_control {}) (padded_exec_equiv {}) (padded_exec_equiv {})
      (step_inst fuel C i s) (step_inst fuel C i t)) /\
  (!fuel C bb s. !t.
    le_padded_control {} s t /\ EVERY (\j. j.inst_opcode <> MEMTOP) bb.bb_instructions /\
    EVERY (\f. EVERY (\j. j.inst_opcode <> MEMTOP) (fn_insts f)) C.ctx_functions ==>
    (?e. exec_block fuel C bb s = Error e) \/
    lift_result (le_padded_control {}) (padded_exec_equiv {}) (padded_exec_equiv {})
      (exec_block fuel C bb s) (exec_block fuel C bb t)) /\
  (!fuel C fn s. !t.
    le_padded_control {} s t /\ EVERY (\j. j.inst_opcode <> MEMTOP) (fn_insts fn) /\
    EVERY (\f. EVERY (\j. j.inst_opcode <> MEMTOP) (fn_insts f)) C.ctx_functions ==>
    (?e. run_blocks fuel C fn s = Error e) \/
    lift_result (le_padded_control {}) (padded_exec_equiv {}) (padded_exec_equiv {})
      (run_blocks fuel C fn s) (run_blocks fuel C fn t))
Proof
  ho_match_mp_tac run_defs_ind >> rpt conj_tac
  >- suspend "step"
  >- suspend "block"
  >> suspend "run"
QED

Resume le_padded_same_program_mutual[step]:
  rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
      Cases_on `i.inst_opcode = INVOKE`
      >- (Cases_on `decode_invoke i` >- simp[step_inst_def] >>
          PairCases_on `x` >>
          Cases_on `lookup_function x0 C.ctx_functions` >- simp[step_inst_def] >>
          Cases_on `eval_operands x1 s` >- simp[step_inst_def] >>
          Cases_on `setup_callee x x' s` >- simp[step_inst_def] >>
          `padded_exec_equiv {} s t` by gvs[le_padded_control_def] >>
          `eval_operands x1 s = eval_operands x1 t` by
            (irule le_padded_operands_agreement >>
             gvs[padded_exec_equiv_def]) >>
          drule_all le_padded_setup_total >> strip_tac >>
          irule le_padded_invoke_return >>
          goal_assum (drule_at Any) >> simp[] >>
          qexistsl [`x'`, `x''`, `d`] >>
          `eval_operands x1 t = SOME x'` by metis_tac[] >> simp[] >>
          first_x_assum irule >> simp[] >>
          drule venomInstTheory.lookup_function_MEM >> strip_tac >>
          qpat_x_assum `EVERY _ C.ctx_functions` mp_tac >>
          simp[EVERY_MEM] >> disch_then drule >> simp[]) >>
      disj2_tac >> simp[step_inst_def] >> irule le_padded_noncall_step >>
      gvs[le_padded_control_def, padded_exec_equiv_def]
QED

Resume le_padded_same_program_mutual[block]:
  rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
      `s.vs_inst_idx = t.vs_inst_idx` by gvs[le_padded_control_def] >>
      Cases_on `get_instruction bb s.vs_inst_idx`
      >- simp[Once exec_block_def] >>
      `x.inst_opcode <> MEMTOP` by
        (gvs[venomInstTheory.get_instruction_def, EVERY_EL] >> metis_tac[]) >>
      qpat_x_assum `!i. _` (qspec_then `x` mp_tac) >> simp[] >>
      disch_then (qspec_then `t` mp_tac) >> simp[] >>
      Cases_on `step_inst fuel C x s` >>
      Cases_on `step_inst fuel C x t` >>
      gvs[lift_result_def]
      >- (strip_tac >>
          `exec_block fuel C bb s =
             if is_terminator x.inst_opcode then
               if v.vs_halted then Halt v else OK v
             else exec_block fuel C bb (v with vs_inst_idx := SUC t.vs_inst_idx)` by
            (CONV_TAC (LAND_CONV (REWR_CONV exec_block_def)) >> simp[]) >>
          `exec_block fuel C bb t =
             if is_terminator x.inst_opcode then
               if v'.vs_halted then Halt v' else OK v'
             else exec_block fuel C bb (v' with vs_inst_idx := SUC t.vs_inst_idx)` by
            (CONV_TAC (LAND_CONV (REWR_CONV exec_block_def)) >> simp[]) >>
          Cases_on `is_terminator x.inst_opcode`
          >- (simp[Once exec_block_def] >>
              `v.vs_halted = v'.vs_halted` by
                gvs[le_padded_control_def, padded_exec_equiv_def,
                    execution_frame_def, venom_state_component_equality] >>
              Cases_on `v'.vs_halted` >>
              gvs[lift_result_def, le_padded_control_def]) >>
          simp[] >> first_x_assum irule >>
          simp[le_padded_control_idx]) >>
      rpt strip_tac >> once_rewrite_tac[exec_block_def] >>
      simp[lift_result_def]
QED

Resume le_padded_same_program_mutual[run]:
  rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
  `s.vs_current_bb = t.vs_current_bb` by gvs[le_padded_control_def] >>
  Cases_on `fuel` >- simp[Once run_blocks_def] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks`
  >- simp[Once run_blocks_def] >>
  rename1 `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` >>
  `EVERY (\j. j.inst_opcode <> MEMTOP) bb.bb_instructions` by
    (gvs[EVERY_MEM] >> metis_tac[fragExecTheory.lookup_block_fn_insts]) >>
  qspecl_then [`s`, `bb.bb_instructions`] strip_assume_tac eval_phis_ok_or_error_defs
  >- (drule_all le_padded_phis_total >> strip_tac >>
      qpat_x_assum `!fuel' bb' s_phi. _` mp_tac >>
      simp[] >> disch_then (qspec_then
        `v with vs_inst_idx := phi_prefix_length bb.bb_instructions` mp_tac) >>
      simp[le_padded_control_idx] >>
      Cases_on `exec_block n C bb
        (s' with vs_inst_idx := phi_prefix_length bb.bb_instructions)` >>
      Cases_on `exec_block n C bb
        (v with vs_inst_idx := phi_prefix_length bb.bb_instructions)` >>
      gvs[lift_result_def]
      >- (strip_tac >>
          `run_blocks (SUC n) C fn s =
            if v'.vs_halted then Halt v' else run_blocks n C fn v'` by
            (CONV_TAC (LAND_CONV (REWR_CONV run_blocks_def)) >> simp[]) >>
          `run_blocks (SUC n) C fn t =
            if v''.vs_halted then Halt v'' else run_blocks n C fn v''` by
            (CONV_TAC (LAND_CONV (REWR_CONV run_blocks_def)) >> simp[]) >>
          `v'.vs_halted = v''.vs_halted` by
            gvs[le_padded_control_def, padded_exec_equiv_def,
                execution_frame_def, venom_state_component_equality] >>
          Cases_on `v''.vs_halted`
          >- gvs[lift_result_def, le_padded_control_def] >>
          simp[] >> first_x_assum irule >> simp[]) >>
      rpt strip_tac >> once_rewrite_tac[run_blocks_def] >> simp[lift_result_def]) >>
  simp[Once run_blocks_def]
QED

Finalise le_padded_same_program_mutual

Theorem le_padded_run_blocks:
  le_padded_control {} s t /\
  EVERY (\j. j.inst_opcode <> MEMTOP) (fn_insts fn) /\
  EVERY (\f. EVERY (\j. j.inst_opcode <> MEMTOP) (fn_insts f)) C.ctx_functions ==>
  (?e. run_blocks fuel C fn s = Error e) \/
  lift_result (le_padded_control {}) (padded_exec_equiv {}) (padded_exec_equiv {})
    (run_blocks fuel C fn s) (run_blocks fuel C fn t)
Proof
  metis_tac[le_padded_same_program_mutual]
QED

Theorem le_padded_invoke_step:
  le_padded_control V s t /\ i.inst_opcode = INVOKE /\
  (!name ops. decode_invoke i = SOME (name,ops) ==>
    eval_operands ops s = eval_operands ops t) /\
  EVERY (\f. EVERY (\j. j.inst_opcode <> MEMTOP) (fn_insts f)) C.ctx_functions ==>
  (?e. step_inst fuel C i s = Error e) \/
  lift_result (le_padded_control V) (padded_exec_equiv V) (padded_exec_equiv V)
    (step_inst fuel C i s) (step_inst fuel C i t)
Proof
  strip_tac >>
  Cases_on `decode_invoke i` >- simp[step_inst_def] >>
  PairCases_on `x` >>
  Cases_on `lookup_function x0 C.ctx_functions` >- simp[step_inst_def] >>
  Cases_on `eval_operands x1 s` >- simp[step_inst_def] >>
  Cases_on `setup_callee x x' s` >- simp[step_inst_def] >>
  `padded_exec_equiv V s t` by gvs[le_padded_control_def] >>
  `eval_operands x1 t = SOME x'` by metis_tac[] >>
  drule_all le_padded_setup_total >> strip_tac >>
  irule le_padded_invoke_return >> goal_assum (drule_at Any) >> simp[] >>
  irule le_padded_run_blocks >> simp[] >>
  drule venomInstTheory.lookup_function_MEM >> strip_tac >>
  qpat_x_assum `EVERY _ C.ctx_functions` mp_tac >>
  simp[EVERY_MEM] >> disch_then drule >> simp[]
QED
