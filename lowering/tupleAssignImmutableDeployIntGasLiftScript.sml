Theory tupleAssignImmutableDeployIntGasLift
Ancestors
  fragGasFocus fragGasMode gasSummary fragGasPath gasCount fragExec intCallStep
  venomExecSemantics venomExecProofs venomInstProofs venomState arithmetic list

(* Count the execution starting at an instruction, without re-entering PHIs.
   This task-private runner projection is needed only for counted reconstruction. *)
Definition tuple_immutable_count_from_def:
  tuple_immutable_count_from fuel ctx fn s =
    case lookup_block s.vs_current_bb fn.fn_blocks of
      NONE => 0
    | SOME bb => gas_count_block fuel ctx bb s +
        (case exec_block fuel ctx bb s of
           OK t => if t.vs_halted then 0 else gas_count_blocks fuel ctx fn t
         | _ => 0)
End

Theorem count_from_mono[local]:
  run_from n ctx fn s = r /\ (!e. r <> Error e) /\ n <= m ==>
  tuple_immutable_count_from n ctx fn s = tuple_immutable_count_from m ctx fn s
Proof
  rw[run_from_def, tuple_immutable_count_from_def] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >> gvs[] >>
  rename1 `lookup_block _ _ = SOME bb` >>
  Cases_on `exec_block n ctx bb s` >> gvs[] >>
  `exec_block m ctx bb s = exec_block n ctx bb s` by
    (irule (cj 2 fuel_mono) >> simp[] >> qexists_tac `n` >> simp[]) >>
  `gas_count_block n ctx bb s = gas_count_block m ctx bb s` by
    (irule (cj 2 gas_count_fuel_mono) >> simp[] >> metis_tac[]) >>
  gvs[] >> Cases_on `v.vs_halted` >> gvs[] >>
  irule (cj 3 gas_count_fuel_mono) >> metis_tac[exec_block_def]
QED

Theorem counted_enter[local]:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  eval_phis s bb.bb_instructions = OK p /\
  run_from fuel ctx fn (p with vs_inst_idx := phi_prefix_length bb.bb_instructions) = r ==>
  run_blocks (SUC fuel) ctx fn s = r /\
  gas_count_blocks (SUC fuel) ctx fn s =
    tuple_immutable_count_from fuel ctx fn
      (p with vs_inst_idx := phi_prefix_length bb.bb_instructions)
Proof
  rpt strip_tac
  >- metis_tac[run_blocks_run_from] >>
  `p.vs_current_bb = s.vs_current_bb` by metis_tac[eval_phis_preserves_current_bb] >>
  simp[Once gas_count_blocks_def, tuple_immutable_count_from_def]
QED

Theorem counted_edge_continue[local]:
  gas_path_edge ctx fn s n (OK t) /\
  run_from fuel ctx fn t = r /\ (!e. r <> Error e) ==>
  ?fuel'. run_from fuel' ctx fn s = r /\
    tuple_immutable_count_from fuel' ctx fn s =
      n + tuple_immutable_count_from fuel ctx fn t
Proof
  rw[gas_path_edge_def] >> gvs[exit_result_def]
  >- suspend "within"
  >- suspend "enter"
  >- suspend "jump"
  >> (Cases_on `step_inst fuel' ctx inst s` >> gvs[exit_result_def])
QED
Resume counted_edge_continue[within]:
  `step_inst (fuel' + fuel) ctx inst s = OK t'` by
    (irule (cj 1 fuel_mono) >> simp[] >> qexists_tac `fuel'` >> simp[]) >>
  `gas_count_step (fuel' + fuel) ctx inst s = gas_count_step fuel' ctx inst s` by
    (sym_tac >> irule (cj 1 gas_count_fuel_mono) >> simp[] >> metis_tac[]) >>
  `t'.vs_current_bb = s.vs_current_bb` by metis_tac[step_preserves_control_flow] >>
  `run_from (fuel' + fuel) ctx fn
      (t' with vs_inst_idx := SUC s.vs_inst_idx) =
    run_from fuel ctx fn (t' with vs_inst_idx := SUC s.vs_inst_idx)` by
    (irule gas_run_from_fuel_mono >> simp[] >> qexists_tac `fuel` >> simp[]) >>
  `tuple_immutable_count_from (fuel' + fuel) ctx fn
      (t' with vs_inst_idx := SUC s.vs_inst_idx) =
   tuple_immutable_count_from fuel ctx fn
      (t' with vs_inst_idx := SUC s.vs_inst_idx)` by
    (sym_tac >> irule count_from_mono >> simp[] >> metis_tac[]) >>
  qexists_tac `fuel' + fuel` >> conj_tac
  >- (qpat_x_assum `run_from (fuel' + fuel) _ _ _ = _` (fn th => rewrite_tac[GSYM th]) >>
      simp_tac (srw_ss()) [run_from_def] >>
      CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [exec_block_def])) >>
      asm_simp_tac (srw_ss()) []) >>
  qpat_x_assum `tuple_immutable_count_from (fuel' + fuel) _ _ _ = _`
    (fn th => rewrite_tac[GSYM th]) >>
  simp_tac (srw_ss()) [tuple_immutable_count_from_def] >>
  CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [exec_block_def])) >>
  CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [gas_count_block_def])) >>
  asm_simp_tac (srw_ss()) [ADD_ASSOC]
QED
Resume counted_edge_continue[enter]:
  `step_inst (SUC (fuel' + fuel)) ctx inst s = OK t'` by
    (irule (cj 1 fuel_mono) >> simp[] >> qexists_tac `fuel'` >> simp[]) >>
  `gas_count_step (SUC (fuel' + fuel)) ctx inst s = gas_count_step fuel' ctx inst s` by
    (sym_tac >> irule (cj 1 gas_count_fuel_mono) >> simp[] >> metis_tac[]) >>
  `run_from (fuel' + fuel) ctx fn
     (entered with vs_inst_idx := phi_prefix_length target.bb_instructions) =
   run_from fuel ctx fn
     (entered with vs_inst_idx := phi_prefix_length target.bb_instructions)` by
    (irule gas_run_from_fuel_mono >> simp[] >> qexists_tac `fuel` >> simp[]) >>
  `tuple_immutable_count_from (fuel' + fuel) ctx fn
     (entered with vs_inst_idx := phi_prefix_length target.bb_instructions) =
   tuple_immutable_count_from fuel ctx fn
     (entered with vs_inst_idx := phi_prefix_length target.bb_instructions)` by
    (sym_tac >> irule count_from_mono >> simp[] >> metis_tac[]) >>
  drule_all counted_enter >> strip_tac >>
  qexists_tac `SUC (fuel' + fuel)` >>
  simp_tac (srw_ss()) [run_from_def, tuple_immutable_count_from_def] >>
  CONV_TAC (LAND_CONV (LHS_CONV (ONCE_REWRITE_CONV [exec_block_def]))) >>
  CONV_TAC (RAND_CONV (LHS_CONV (ONCE_REWRITE_CONV [exec_block_def]))) >>
  CONV_TAC (RAND_CONV (LHS_CONV (ONCE_REWRITE_CONV [gas_count_block_def]))) >>
  asm_simp_tac (srw_ss()) [] >> simp[run_from_def, tuple_immutable_count_from_def]
QED
Resume counted_edge_continue[jump]:
  `?target. lookup_block lbl fn.fn_blocks = SOME target /\
      phi_prefix_length target.bb_instructions = 0` by
    (irule run_from_jump_target >> simp[] >> metis_tac[]) >>
  `eval_phis (jump_to lbl s) target.bb_instructions = OK (jump_to lbl s)` by
    metis_tac[eval_phis_no_phi] >>
  `run_blocks (SUC fuel) ctx fn (jump_to lbl s) =
    run_from fuel ctx fn (jump_to lbl s) /\
   gas_count_blocks (SUC fuel) ctx fn (jump_to lbl s) =
    tuple_immutable_count_from fuel ctx fn (jump_to lbl s)` by
    (drule_at Any counted_enter >> simp[jump_to_def]) >>
  `step_inst (SUC fuel) ctx inst s = OK (jump_to lbl s)` by
    metis_tac[step_inst_non_invoke] >>
  qexists_tac `SUC fuel` >>
  simp_tac (srw_ss()) [run_from_def, tuple_immutable_count_from_def] >>
  CONV_TAC (LAND_CONV (LHS_CONV (ONCE_REWRITE_CONV [exec_block_def]))) >>
  CONV_TAC (RAND_CONV (LHS_CONV (ONCE_REWRITE_CONV [exec_block_def]))) >>
  CONV_TAC (RAND_CONV (LHS_CONV (ONCE_REWRITE_CONV [gas_count_block_def]))) >>
  asm_simp_tac (srw_ss()) [jump_to_def, gas_count_step_def] >>
  gvs[run_from_def, tuple_immutable_count_from_def, jump_to_def]
QED
Finalise counted_edge_continue

Theorem counted_edge_exit[local]:
  gas_path_edge ctx fn s n r /\ exit_result r ==>
  ?fuel. run_from fuel ctx fn s = r /\
    tuple_immutable_count_from fuel ctx fn s = n
Proof
  rw[gas_path_edge_def] >> gvs[exit_result_def]
  >- (qexists_tac `fuel` >>
      simp_tac (srw_ss()) [run_from_def, tuple_immutable_count_from_def] >>
      CONV_TAC (LAND_CONV (LHS_CONV (ONCE_REWRITE_CONV [exec_block_def]))) >>
      CONV_TAC (RAND_CONV (LHS_CONV (ONCE_REWRITE_CONV [exec_block_def]))) >>
      CONV_TAC (RAND_CONV (LHS_CONV (ONCE_REWRITE_CONV [gas_count_block_def]))) >>
      asm_simp_tac (srw_ss()) []) >>
  qexists_tac `fuel` >>
  Cases_on `step_inst fuel ctx inst s` >> gvs[exit_result_def] >>
  simp_tac (srw_ss()) [run_from_def, tuple_immutable_count_from_def] >>
  CONV_TAC (LAND_CONV (LHS_CONV (ONCE_REWRITE_CONV [exec_block_def]))) >>
  CONV_TAC (RAND_CONV (LHS_CONV (ONCE_REWRITE_CONV [exec_block_def]))) >>
  CONV_TAC (RAND_CONV (LHS_CONV (ONCE_REWRITE_CONV [gas_count_block_def]))) >>
  asm_simp_tac (srw_ss()) []
QED

Theorem counted_path_exit[local]:
  !ctx fn s n r. gas_path ctx fn s n r ==>
  exit_result r ==> ?fuel. run_from fuel ctx fn s = r /\
    tuple_immutable_count_from fuel ctx fn s = n
Proof
  ho_match_mp_tac gas_path_ind >> rpt conj_tac
  >- simp[exit_result_def]
  >- (rpt strip_tac >> first_x_assum drule >> strip_tac >>
      `!e. r <> Error e` by metis_tac[exit_result_not_error] >>
      drule_all counted_edge_continue >> simp[])
  >> metis_tac[counted_edge_exit]
QED

Theorem tuple_immutable_callee_counted_run:
  gas_invoke_entry (ctx,func) t callee entered /\
  gas_marked_path F ctx callee entered n (IntRet ir cs') ==>
  ?fuel bb inst name arg_ops argv setup.
    lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb t.vs_inst_idx = SOME inst /\
    inst.inst_opcode = INVOKE /\
    decode_invoke inst = SOME (name,arg_ops) /\
    lookup_function name ctx.ctx_functions = SOME callee /\
    eval_operands arg_ops t = SOME argv /\
    setup_callee callee argv t = SOME setup /\
    run_blocks fuel ctx callee setup = IntRet ir cs' /\
    gas_count_step fuel ctx inst t = n
Proof
  strip_tac >>
  `gas_path ctx callee entered n (IntRet ir cs')` by
    metis_tac[gas_marked_path_exec] >>
  drule counted_path_exit >> simp[exit_result_def] >> strip_tac >>
  gvs[gas_invoke_entry_def] >>
  drule_all counted_enter >> strip_tac >>
  qexists_tac `SUC fuel` >>
  simp[gas_count_step_def]
QED

Theorem tuple_immutable_callee_marked_invoke:
  gas_invoke_entry (ctx,func) t callee entered /\
  gas_marked_exec F (ctx,callee) source (es,entered) marks res ee (IntRet ir cs') /\
  (!bb inst. lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb t.vs_inst_idx = SOME inst ==>
    LENGTH inst.inst_outputs = LENGTH ir.iret_values) ==>
  ?u bb inst.
    lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb t.vs_inst_idx = SOME inst /\
    bind_outputs inst.inst_outputs ir.iret_values
      (adopt_return_fmp ir (merge_callee_state t cs')) = SOME u /\
    gas_marked_exec F (ctx,func) source (es,t) marks res ee
      (OK (u with vs_inst_idx := SUC t.vs_inst_idx))
Proof
  strip_tac >>
  `entered.vs_gas_readings = t.vs_gas_readings` by
    metis_tac[gas_invoke_entry_readings] >>
  gvs[gas_marked_exec_def] >>
  drule_all tuple_immutable_callee_counted_run >> strip_tac >>
  `LENGTH inst.inst_outputs = LENGTH ir.iret_values` by metis_tac[] >>
  drule_all step_inst_invoke_intret >> strip_tac >>
  qmatch_asmsub_abbrev_tac `bind_outputs _ _ _ = SOME u` >>
  `~t.vs_halted` by gvs[gas_invoke_entry_def] >>
  `~u.vs_halted` by metis_tac[step_inst_invoke_OK_control] >>
  qexistsl_tac [`u`, `bb`, `inst`] >> simp[] >>
  simp[gas_marked_path_def] >>
  `gas_path_edge ctx func t (LENGTH marks)
      (OK (u with vs_inst_idx := SUC t.vs_inst_idx))` by
    (simp[gas_path_edge_def] >>
     qexists_tac `fuel` >>
     simp[venomInstTheory.is_terminator_def]) >>
  `~(u with vs_inst_idx := SUC t.vs_inst_idx).vs_halted` by simp[] >>
  metis_tac[gas_path_rules, ADD_0]
QED
