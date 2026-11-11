Theory bodyIntCallCountedPath
Ancestors
  fragGasPath gasCount fragExec venomExecSemantics venomExecProofs
  venomInstProofs venomState arithmetic list

Theorem counted_path_edge_exit:
  gas_path_edge ctx fn s n r /\ exit_result r ==>
  ?fuel bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    run_from fuel ctx fn s = r /\ gas_count_block fuel ctx bb s = n
Proof
  rw[gas_path_edge_def] >> gvs[exit_result_def]
  >- (qexists_tac `fuel` >> simp[] >>
      conj_tac
      >- (simp_tac (srw_ss()) [run_from_def] >>
          CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [exec_block_def])) >>
          asm_simp_tac (srw_ss()) []) >>
      simp[Once gas_count_block_def]) >>
  qexists_tac `fuel` >> simp[] >>
  Cases_on `step_inst fuel ctx inst s` >> gvs[exit_result_def] >>
  (conj_tac
   >- (simp_tac (srw_ss()) [run_from_def] >>
       CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [exec_block_def])) >>
       asm_simp_tac (srw_ss()) []) >>
   simp[Once gas_count_block_def])
QED

(* Unlike gas_count_block, this includes all blocks reached by run_from. *)
Definition gas_count_run_from_def:
  gas_count_run_from fuel ctx fn s =
    case lookup_block s.vs_current_bb fn.fn_blocks of
      NONE => 0
    | SOME bb =>
        gas_count_block fuel ctx bb s +
        (case exec_block fuel ctx bb s of
           OK t => if t.vs_halted then 0 else gas_count_blocks fuel ctx fn t
         | _ => 0)
End

Theorem gas_count_run_from_phis:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  eval_phis s bb.bb_instructions = OK entered ==>
  gas_count_blocks (SUC fuel) ctx fn s =
  gas_count_run_from fuel ctx fn
    (entered with vs_inst_idx := phi_prefix_length bb.bb_instructions)
Proof
  strip_tac >> drule eval_phis_preserves_current_bb >> strip_tac >>
  simp[Once gas_count_blocks_def, gas_count_run_from_def]
QED

Theorem gas_count_run_from_terminal:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  (!t. exec_block fuel ctx bb s = OK t ==> t.vs_halted) ==>
  gas_count_run_from fuel ctx fn s = gas_count_block fuel ctx bb s
Proof
  strip_tac >> simp[gas_count_run_from_def] >>
  Cases_on `exec_block fuel ctx bb s` >> simp[]
QED

Theorem gas_count_run_from_fuel_mono:
  run_from n ctx fn s = r /\ (!e. r <> Error e) /\ n <= m ==>
  gas_count_run_from n ctx fn s = gas_count_run_from m ctx fn s
Proof
  rw[run_from_def] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >> gvs[] >>
  rename1 `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` >>
  `!e. exec_block n ctx bb s <> Error e` by
    (Cases_on `exec_block n ctx bb s` >> gvs[]) >>
  `exec_block m ctx bb s = exec_block n ctx bb s` by
    (irule (cj 2 fuel_mono) >> simp[] >> qexists_tac `n` >> simp[]) >>
  `gas_count_block n ctx bb s = gas_count_block m ctx bb s` by
    (irule (cj 2 gas_count_fuel_mono) >> simp[] >>
     qexists_tac `exec_block n ctx bb s` >> simp[]) >>
  simp[gas_count_run_from_def] >>
  Cases_on `exec_block n ctx bb s` >> gvs[] >>
  rename1 `exec_block n ctx bb s = OK t` >>
  Cases_on `t.vs_halted` >> gvs[] >>
  irule (cj 3 gas_count_fuel_mono) >> simp[] >>
  qexists_tac `run_blocks n ctx fn t` >> simp[]
QED

Theorem counted_path_edge_exit_run_from:
  gas_path_edge ctx fn s n r /\ exit_result r ==>
  ?fuel. run_from fuel ctx fn s = r /\
    gas_count_run_from fuel ctx fn s = n
Proof
  rw[gas_path_edge_def] >> gvs[exit_result_def]
  >- (qexists_tac `fuel` >>
      simp_tac (srw_ss()) [run_from_def, gas_count_run_from_def] >>
      once_rewrite_tac [exec_block_def] >>
      asm_simp_tac (srw_ss()) [Once gas_count_block_def]) >>
  qexists_tac `fuel` >>
  Cases_on `step_inst fuel ctx inst s` >> gvs[exit_result_def] >>
  (simp_tac (srw_ss()) [run_from_def, gas_count_run_from_def] >>
   once_rewrite_tac [exec_block_def] >>
   asm_simp_tac (srw_ss()) [Once gas_count_block_def])
QED

Theorem counted_path_edge_continue:
  gas_path_edge ctx fn s n (OK t) /\
  run_from fuel ctx fn t = r /\ (!e. r <> Error e) /\
  gas_count_run_from fuel ctx fn t = m ==>
  ?fuel'. run_from fuel' ctx fn s = r /\
    gas_count_run_from fuel' ctx fn s = n + m
Proof
  rw[gas_path_edge_def] >> gvs[exit_result_def]
  >- suspend "within"
  >- suspend "enter"
  >- suspend "jump"
  >> (Cases_on `step_inst fuel' ctx inst s` >> gvs[exit_result_def])
QED
Resume counted_path_edge_continue[within]:
  qabbrev_tac `r = run_from fuel ctx fn
    (t' with vs_inst_idx := SUC s.vs_inst_idx)` >>
  `step_inst (fuel' + fuel) ctx inst s = OK t'` by
    (irule (cj 1 fuel_mono) >> simp[] >> qexists_tac `fuel'` >> simp[]) >>
  `gas_count_step (fuel' + fuel) ctx inst s = gas_count_step fuel' ctx inst s` by
    (sym_tac >> irule (cj 1 gas_count_fuel_mono) >> simp[] >>
     qexists_tac `OK t'` >> simp[]) >>
  `t'.vs_current_bb = s.vs_current_bb` by
    metis_tac[step_preserves_control_flow] >>
  `run_from (fuel' + fuel) ctx fn
     (t' with vs_inst_idx := SUC s.vs_inst_idx) = r` by
    (irule gas_run_from_fuel_mono >> simp[] >> qexists_tac `fuel` >> simp[]) >>
  `gas_count_run_from (fuel' + fuel) ctx fn
     (t' with vs_inst_idx := SUC s.vs_inst_idx) =
   gas_count_run_from fuel ctx fn
     (t' with vs_inst_idx := SUC s.vs_inst_idx)` by
    (sym_tac >> irule gas_count_run_from_fuel_mono >> simp[] >>
     qexists_tac `r` >> simp[]) >>
  qexists_tac `fuel' + fuel` >>
  conj_tac
  >- (simp_tac (srw_ss()) [run_from_def] >>
      once_rewrite_tac [exec_block_def] >> asm_simp_tac (srw_ss()) [] >>
      gvs[run_from_def]) >>
  gvs[gas_count_run_from_def] >>
  CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [exec_block_def])) >>
  CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [gas_count_block_def])) >>
  asm_simp_tac (srw_ss()) [] >> decide_tac
QED
Resume counted_path_edge_continue[enter]:
  qmatch_goalsub_abbrev_tac `run_from fuel ctx fn entry` >>
  `step_inst (SUC (fuel' + fuel)) ctx inst s = OK t'` by
    (irule (cj 1 fuel_mono) >> simp[] >> qexists_tac `fuel'` >> simp[]) >>
  `gas_count_step (SUC (fuel' + fuel)) ctx inst s = gas_count_step fuel' ctx inst s` by
    (sym_tac >> irule (cj 1 gas_count_fuel_mono) >> simp[] >>
     qexists_tac `OK t'` >> simp[]) >>
  `run_from (fuel' + fuel) ctx fn entry = run_from fuel ctx fn entry` by
    (irule gas_run_from_fuel_mono >> simp[] >> qexists_tac `fuel` >> simp[]) >>
  `gas_count_run_from (fuel' + fuel) ctx fn entry =
   gas_count_run_from fuel ctx fn entry` by
    (sym_tac >> irule gas_count_run_from_fuel_mono >> simp[] >>
     qexists_tac `run_from fuel ctx fn entry` >> simp[]) >>
  `run_blocks (SUC (fuel' + fuel)) ctx fn t' =
   run_from (fuel' + fuel) ctx fn entry` by
    (unabbrev_all_tac >> irule run_blocks_run_from >> simp[]) >>
  `gas_count_blocks (SUC (fuel' + fuel)) ctx fn t' =
   gas_count_run_from (fuel' + fuel) ctx fn entry` by
    (unabbrev_all_tac >> irule gas_count_run_from_phis >> simp[]) >>
  qexists_tac `SUC (fuel' + fuel)` >>
  conj_tac
  >- (CONV_TAC (LHS_CONV (REWR_CONV run_from_def)) >>
      asm_simp_tac (srw_ss()) [] >>
      CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [exec_block_def])) >>
      asm_simp_tac (srw_ss()) []) >>
  CONV_TAC (LHS_CONV (REWR_CONV gas_count_run_from_def)) >>
  asm_simp_tac (srw_ss()) [] >>
  CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [exec_block_def, gas_count_block_def])) >>
  asm_simp_tac (srw_ss()) [] >> decide_tac
QED
Resume counted_path_edge_continue[jump]:
  `step_inst_base inst s = OK (jump_to lbl s)` by
    metis_tac[step_inst_non_invoke] >>
  `?target. lookup_block lbl fn.fn_blocks = SOME target /\
    phi_prefix_length target.bb_instructions = 0` by
    (irule run_from_jump_target >> qexistsl_tac [`ctx`, `fuel`, `s`] >> simp[]) >>
  `eval_phis (jump_to lbl s) target.bb_instructions = OK (jump_to lbl s)` by
    simp[eval_phis_no_phi] >>
  `gas_count_blocks (SUC fuel) ctx fn (jump_to lbl s) =
   gas_count_run_from fuel ctx fn (jump_to lbl s)` by
    (`lookup_block (jump_to lbl s).vs_current_bb fn.fn_blocks = SOME target` by
       simp[jump_to_def] >>
     drule_all gas_count_run_from_phis >> simp[jump_to_def]) >>
  qexists_tac `SUC fuel` >>
  conj_tac
  >- (irule run_from_jump_result >> simp[] >>
      qexists_tac `lbl` >> simp[]) >>
  CONV_TAC (LHS_CONV (REWR_CONV gas_count_run_from_def)) >>
  asm_simp_tac (srw_ss()) [] >>
  CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [exec_block_def, gas_count_block_def])) >>
  asm_simp_tac (srw_ss()) [step_inst_non_invoke, jump_to_def] >>
  gvs[jump_to_def] >>
  simp[gas_count_step_def, ADD_COMM]
QED
Finalise counted_path_edge_continue

Theorem counted_path_exit_run_from:
  gas_path ctx fn s n r /\ exit_result r ==>
  ?fuel. run_from fuel ctx fn s = r /\
    gas_count_run_from fuel ctx fn s = n
Proof
  `!ctx fn s n r. gas_path ctx fn s n r ==>
    exit_result r ==> ?fuel. run_from fuel ctx fn s = r /\
      gas_count_run_from fuel ctx fn s = n` suffices_by metis_tac[] >>
  ho_match_mp_tac gas_path_ind >> rpt conj_tac
  >- simp[exit_result_def]
  >- (rpt strip_tac >> first_x_assum drule >> strip_tac >>
      irule counted_path_edge_continue >>
      conj_tac >- metis_tac[exit_result_not_error] >>
      goal_assum (drule_at Any) >> simp[] >>
      goal_assum (drule_at Any) >> simp[]) >>
  metis_tac[counted_path_edge_exit_run_from]
QED

Theorem counted_path_exit_run_blocks:
  lookup_block setup.vs_current_bb fn.fn_blocks = SOME first /\
  eval_phis setup first.bb_instructions = OK phi_state /\
  gas_path ctx fn
    (phi_state with vs_inst_idx := phi_prefix_length first.bb_instructions) n r /\
  exit_result r ==>
  ?fuel. run_blocks fuel ctx fn setup = r /\
    gas_count_blocks fuel ctx fn setup = n
Proof
  strip_tac >> drule_all counted_path_exit_run_from >> strip_tac >>
  qexists_tac `SUC fuel` >>
  drule_all run_blocks_run_from >>
  disch_then (qspec_then `fuel` assume_tac) >>
  drule_all gas_count_run_from_phis >>
  disch_then (qspecl_then [`fuel`, `ctx`] assume_tac) >> simp[]
QED

Theorem counted_invoke_intret:
  inst.inst_opcode = INVOKE /\
  decode_invoke inst = SOME (name, arg_ops) /\
  lookup_function name ctx.ctx_functions = SOME callee /\
  eval_operands arg_ops s = SOME args /\
  setup_callee callee args s = SOME setup /\
  lookup_block setup.vs_current_bb callee.fn_blocks = SOME first /\
  eval_phis setup first.bb_instructions = OK phi_state /\
  gas_path ctx callee
    (phi_state with vs_inst_idx := phi_prefix_length first.bb_instructions)
    n (IntRet ir cs) /\
  bind_outputs inst.inst_outputs ir.iret_values
    (adopt_return_fmp ir (merge_callee_state s cs)) = SOME u ==>
  ?fuel. step_inst fuel ctx inst s = OK u /\
    gas_count_step fuel ctx inst s = n
Proof
  strip_tac >>
  `?fuel. run_blocks fuel ctx callee setup = IntRet ir cs /\
    gas_count_blocks fuel ctx callee setup = n` by
    (irule counted_path_exit_run_blocks >> simp[exit_result_def] >>
     goal_assum (drule_at Any) >> simp[] >>
     goal_assum (drule_at Any) >> simp[]) >>
  qexists_tac `fuel` >> simp[Once step_inst_def, Once gas_count_step_def]
QED

Theorem counted_invoke_abort:
  inst.inst_opcode = INVOKE /\
  decode_invoke inst = SOME (name, arg_ops) /\
  lookup_function name ctx.ctx_functions = SOME callee /\
  eval_operands arg_ops s = SOME args /\
  setup_callee callee args s = SOME setup /\
  lookup_block setup.vs_current_bb callee.fn_blocks = SOME first /\
  eval_phis setup first.bb_instructions = OK phi_state /\
  gas_path ctx callee
    (phi_state with vs_inst_idx := phi_prefix_length first.bb_instructions)
    n (Abort a cs) ==>
  ?fuel. step_inst fuel ctx inst s = Abort a cs /\
    gas_count_step fuel ctx inst s = n
Proof
  strip_tac >>
  `?fuel. run_blocks fuel ctx callee setup = Abort a cs /\
    gas_count_blocks fuel ctx callee setup = n` by
    (irule counted_path_exit_run_blocks >> simp[exit_result_def] >>
     goal_assum (drule_at Any) >> simp[] >>
     goal_assum (drule_at Any) >> simp[]) >>
  qexists_tac `fuel` >> simp[Once step_inst_def, Once gas_count_step_def]
QED
