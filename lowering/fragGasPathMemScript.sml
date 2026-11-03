(* Counted fragment paths carrying the memory checks of the same steps,
   including callees and the runner's revert-forward exemption. *)
Theory fragGasPathMem
Ancestors
  fragGasPath gasCount fragExec fragExecMem memSafeRun unitTransformDefs
  venomExecSemantics venomExecProofs venomInstProofs venomState arithmetic list

Definition gas_path_mem_edge_def:
  gas_path_mem_edge ctx fn s n r <=>
    ~s.vs_halted /\
    ?fuel bb inst middle.
      lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
      get_instruction bb s.vs_inst_idx = SOME inst /\
      step_inst fuel ctx inst s = middle /\
      n = gas_count_step fuel ctx inst s /\
      (revert_forward_at bb s.vs_inst_idx \/
       mem_safe_step fuel ctx inst s) /\
      ((?t. middle = OK t /\ ~is_terminator inst.inst_opcode /\
            ~t.vs_halted /\
            r = OK (t with vs_inst_idx := SUC s.vs_inst_idx)) \/
       (?t. middle = OK t /\ is_terminator inst.inst_opcode /\
            t.vs_halted /\ r = Halt t) \/
       (?t target entered.
          middle = OK t /\ is_terminator inst.inst_opcode /\
          ~t.vs_halted /\
          lookup_block t.vs_current_bb fn.fn_blocks = SOME target /\
          eval_phis t target.bb_instructions = OK entered /\
          ~entered.vs_halted /\
          r = OK (entered with vs_inst_idx :=
                    phi_prefix_length target.bb_instructions)) \/
       (exit_result middle /\ r = middle))
End

Inductive gas_path_mem:
  (!ctx fn s.
     ~s.vs_halted ==> gas_path_mem ctx fn s 0 (OK s)) /\
  (!ctx fn s n t m r.
     gas_path_mem_edge ctx fn s n (OK t) /\
     gas_path_mem ctx fn t m r ==>
     gas_path_mem ctx fn s (n + m) r) /\
  (!ctx fn s n r.
     gas_path_mem_edge ctx fn s n r /\ exit_result r ==>
     gas_path_mem ctx fn s n r)
End

Theorem edge_check_mono[local]:
  (revert_forward_at bb s.vs_inst_idx \/ mem_safe_step a ctx inst s) /\
  (!e. step_inst a ctx inst s <> Error e) /\ a <= b ==>
  (revert_forward_at bb s.vs_inst_idx \/ mem_safe_step b ctx inst s)
Proof
  metis_tac[cj 1 mem_safe_fuel_mono_up]
QED

Theorem mem_jump_boundary[local]:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  step_inst (SUC k) ctx inst s = OK t /\
  is_terminator inst.inst_opcode /\ ~t.vs_halted /\
  lookup_block t.vs_current_bb fn.fn_blocks = SOME target /\
  eval_phis t target.bb_instructions = OK entered /\
  (revert_forward_at bb s.vs_inst_idx \/
   mem_safe_step (SUC k) ctx inst s) ==>
  run_from (SUC k) ctx fn s =
    run_from k ctx fn
      (entered with vs_inst_idx := phi_prefix_length target.bb_instructions) /\
  (mem_safe_run k ctx fn
      (entered with vs_inst_idx := phi_prefix_length target.bb_instructions) ==>
   mem_safe_run (SUC k) ctx fn s)
Proof
  strip_tac >> (
  `exec_block (SUC k) ctx bb s = OK t` by
    simp[Once exec_block_def] >>
  drule_all run_blocks_run_from >> strip_tac >>
  drule_all mem_safe_blocks_run >> strip_tac >>
  conj_tac
  >- (simp[Once run_from_def] >> metis_tac[]) >>
  disch_tac >>
  simp[Once mem_safe_run_def, Once mem_safe_block_def] >>
  metis_tac[])
QED

Theorem mem_edge_erase[local]:
  gas_path_mem_edge ctx fn s n r ==> gas_path_edge ctx fn s n r
Proof
  simp[gas_path_mem_edge_def, gas_path_edge_def] >> metis_tac[]
QED

Theorem mem_edge_normal[local]:
  gas_path_mem_edge ctx fn s n (OK t) ==> ~t.vs_halted
Proof
  metis_tac[mem_edge_erase, gas_path_edge_normal]
QED

Theorem mem_edge_exit[local]:
  gas_path_mem_edge ctx fn s n r /\ exit_result r ==>
  ?fuel. run_from fuel ctx fn s = r /\ mem_safe_run fuel ctx fn s
Proof
  rw[gas_path_mem_edge_def] >>
  gvs[fragExecTheory.exit_result_def] >>
  qexists_tac `fuel` >>
  simp[run_from_def, Once exec_block_def,
       mem_safe_run_def, Once mem_safe_block_def] >>
  simp[Once exec_block_def] >>
  Cases_on `step_inst fuel ctx inst s` >>
  gvs[fragExecTheory.exit_result_def] >>
  simp[Once exec_block_def]
QED

Theorem gas_path_mem_edge_continue[local]:
  gas_path_mem_edge ctx fn s n (OK t) /\
  run_from fuel ctx fn t = out /\ (!e. out <> Error e) ==>
  ?fuel'. run_from fuel' ctx fn s = out /\
    (mem_safe_run fuel ctx fn t ==> mem_safe_run fuel' ctx fn s)
Proof
  rw[gas_path_mem_edge_def] >> gvs[fragExecTheory.exit_result_def]
  >- suspend "within"
  >- suspend "enter"
  >- (Cases_on `step_inst fuel' ctx inst s` >>
      gvs[fragExecTheory.exit_result_def])
  >- suspend "within_check"
  >- suspend "enter_check"
  >> (Cases_on `step_inst fuel' ctx inst s` >>
      gvs[fragExecTheory.exit_result_def])
QED
Resume gas_path_mem_edge_continue[within]:
  all_tac >> (
  `step_inst (fuel' + fuel) ctx inst s = OK t'` by
    (irule (cj 1 fuel_mono) >> simp[] >> qexists_tac `fuel'` >> simp[]) >>
  `t'.vs_current_bb = s.vs_current_bb` by
    metis_tac[step_preserves_control_flow] >>
  `run_from (fuel' + fuel) ctx fn
     (t' with vs_inst_idx := SUC s.vs_inst_idx) =
   run_from fuel ctx fn (t' with vs_inst_idx := SUC s.vs_inst_idx)` by
    (irule gas_run_from_fuel_mono >> simp[] >> qexists_tac `fuel` >> simp[]) >>
  `run_from (fuel' + fuel) ctx fn s =
   run_from (fuel' + fuel) ctx fn
     (t' with vs_inst_idx := SUC s.vs_inst_idx)` by
    (simp_tac (srw_ss()) [run_from_def] >>
     CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [exec_block_def])) >>
     asm_simp_tac (srw_ss()) []) >>
  qexists_tac `fuel' + fuel` >> conj_tac >- metis_tac[] >>
  `revert_forward_at bb s.vs_inst_idx \/
   mem_safe_step (fuel' + fuel) ctx inst s` by
    (irule edge_check_mono >> qexists_tac `fuel'` >> simp[]) >>
  drule_all mem_safe_run_step >> strip_tac >>
  strip_tac >>
  `mem_safe_run (fuel' + fuel) ctx fn
     (t' with vs_inst_idx := SUC s.vs_inst_idx)` by
    (irule mem_safe_run_fuel_mono_up >> simp[] >>
     qexists_tac `fuel` >> simp[]) >>
  metis_tac[])
QED
Resume gas_path_mem_edge_continue[enter]:
  all_tac >> (
  `step_inst (SUC (fuel' + fuel)) ctx inst s = OK t'` by
    (irule (cj 1 fuel_mono) >> simp[] >> qexists_tac `fuel'` >> simp[]) >>

  `run_from (fuel' + fuel) ctx fn
     (entered with vs_inst_idx := phi_prefix_length target.bb_instructions) =
   run_from fuel ctx fn
     (entered with vs_inst_idx := phi_prefix_length target.bb_instructions)` by
    (irule gas_run_from_fuel_mono >> simp[] >> qexists_tac `fuel` >> simp[]) >>
  `run_from (SUC (fuel' + fuel)) ctx fn s =
     run_from (fuel' + fuel) ctx fn
       (entered with vs_inst_idx := phi_prefix_length target.bb_instructions) /\
   (mem_safe_run (fuel' + fuel) ctx fn
       (entered with vs_inst_idx := phi_prefix_length target.bb_instructions) ==>
    mem_safe_run (SUC (fuel' + fuel)) ctx fn s)` by
    (irule mem_jump_boundary >> simp[] >> metis_tac[ADD_COMM]) >>
  qexists_tac `SUC (fuel' + fuel)` >> conj_tac >- metis_tac[] >>
  strip_tac >>
  `mem_safe_run (fuel' + fuel) ctx fn
     (entered with vs_inst_idx := phi_prefix_length target.bb_instructions)` by
    (irule mem_safe_run_fuel_mono_up >> simp[] >>
     qexists_tac `fuel` >> simp[]) >>
  metis_tac[])
QED
Resume gas_path_mem_edge_continue[within_check]:
  `step_inst (fuel' + fuel) ctx inst s = OK t'` by
    (irule (cj 1 fuel_mono) >> simp[] >> qexists_tac `fuel'` >> simp[]) >>
  `t'.vs_current_bb = s.vs_current_bb` by
    metis_tac[step_preserves_control_flow] >>
  `run_from (fuel' + fuel) ctx fn
     (t' with vs_inst_idx := SUC s.vs_inst_idx) =
   run_from fuel ctx fn (t' with vs_inst_idx := SUC s.vs_inst_idx)` by
    (irule gas_run_from_fuel_mono >> simp[] >> qexists_tac `fuel` >> simp[]) >>
  `run_from (fuel' + fuel) ctx fn s =
   run_from (fuel' + fuel) ctx fn
     (t' with vs_inst_idx := SUC s.vs_inst_idx)` by
    (simp_tac (srw_ss()) [run_from_def] >>
     CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [exec_block_def])) >>
     asm_simp_tac (srw_ss()) []) >>
  qexists_tac `fuel' + fuel` >> conj_tac >- metis_tac[] >>
  `revert_forward_at bb s.vs_inst_idx \/
   mem_safe_step (fuel' + fuel) ctx inst s` by
    (irule edge_check_mono >> qexists_tac `fuel'` >> simp[]) >>
  drule_all mem_safe_run_step >> strip_tac >> strip_tac >>
  `mem_safe_run (fuel' + fuel) ctx fn
     (t' with vs_inst_idx := SUC s.vs_inst_idx)` by
    (irule mem_safe_run_fuel_mono_up >> simp[] >>
     qexists_tac `fuel` >> simp[]) >>
  metis_tac[]
QED
Resume gas_path_mem_edge_continue[enter_check]:
  `mem_safe_step (SUC (fuel' + fuel)) ctx inst s` by
    (irule (cj 1 mem_safe_fuel_mono_up) >> simp[] >>
     qexists_tac `fuel'` >> simp[]) >>
  `step_inst (SUC (fuel' + fuel)) ctx inst s = OK t'` by
    (irule (cj 1 fuel_mono) >> simp[] >> qexists_tac `fuel'` >> simp[]) >>

  `run_from (fuel' + fuel) ctx fn
     (entered with vs_inst_idx := phi_prefix_length target.bb_instructions) =
   run_from fuel ctx fn
     (entered with vs_inst_idx := phi_prefix_length target.bb_instructions)` by
    (irule gas_run_from_fuel_mono >> simp[] >> qexists_tac `fuel` >> simp[]) >>
  `run_from (SUC (fuel' + fuel)) ctx fn s =
     run_from (fuel' + fuel) ctx fn
       (entered with vs_inst_idx := phi_prefix_length target.bb_instructions) /\
   (mem_safe_run (fuel' + fuel) ctx fn
       (entered with vs_inst_idx := phi_prefix_length target.bb_instructions) ==>
    mem_safe_run (SUC (fuel' + fuel)) ctx fn s)` by
    (irule mem_jump_boundary >> simp[] >> metis_tac[ADD_COMM]) >>
  qexists_tac `SUC (fuel' + fuel)` >> conj_tac >- metis_tac[] >> strip_tac >>
  `mem_safe_run (fuel' + fuel) ctx fn
     (entered with vs_inst_idx := phi_prefix_length target.bb_instructions)` by
    (irule mem_safe_run_fuel_mono_up >> simp[] >>
     qexists_tac `fuel` >> simp[]) >>
  metis_tac[]
QED
Finalise gas_path_mem_edge_continue

(* A normal landing transfers the existing conditional continuation check;
   a terminal path supplies its own safe run. *)
Theorem gas_path_mem_exec:
  !ctx fn s n r.
    gas_path_mem ctx fn s n r ==>
    gas_path ctx fn s n r /\
    ((?t. r = OK t /\ ~t.vs_halted /\
          !fuel out.
            run_from fuel ctx fn t = out /\ (!e. out <> Error e) ==>
            ?fuel'. run_from fuel' ctx fn s = out /\
                    (mem_safe_run fuel ctx fn t ==>
                     mem_safe_run fuel' ctx fn s)) \/
     (exit_result r /\
      ?fuel. run_from fuel ctx fn s = r /\ mem_safe_run fuel ctx fn s))
Proof
  cheat
QED
