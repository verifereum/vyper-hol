(* Actual finite fragment paths with counts of all executed GAS instructions.
   Source-level explicit readings are selected by the lowering proofs. *)
Theory fragGasPath
Ancestors
  gasCount fragExec venomExecSemantics venomExecProofs venomInstProofs venomState arithmetic list

Definition gas_path_edge_def:
  gas_path_edge ctx fn s n r <=>
    ~s.vs_halted /\
    ?fuel bb inst middle.
      lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
      get_instruction bb s.vs_inst_idx = SOME inst /\
      step_inst fuel ctx inst s = middle /\
      n = gas_count_step fuel ctx inst s /\
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

Inductive gas_path:
  (!ctx fn s.
     ~s.vs_halted ==> gas_path ctx fn s 0 (OK s)) /\
  (!ctx fn s n t m r.
     gas_path_edge ctx fn s n (OK t) /\
     gas_path ctx fn t m r ==>
     gas_path ctx fn s (n + m) r) /\
  (!ctx fn s n r.
     gas_path_edge ctx fn s n r /\ exit_result r ==>
     gas_path ctx fn s n r)
End

Theorem gas_path_edge_suffix:
  gas_path_edge ctx fn s n r ==> gas_count_suffix n s r
Proof
  rw[gas_path_edge_def] >>
  qspecl_then [`fuel`, `ctx`, `inst`, `s`] mp_tac (cj 1 gas_count_suffix) >>
  gvs[gas_count_suffix_def, fragExecTheory.exit_result_def] >>
  metis_tac[gas_count_phis_ok]
QED

Theorem gas_path_edge_normal:
  gas_path_edge ctx fn s n (OK t) ==> ~t.vs_halted
Proof
  rw[gas_path_edge_def] >> gvs[fragExecTheory.exit_result_def] >>
  Cases_on `step_inst fuel ctx inst s` >> gvs[fragExecTheory.exit_result_def]
QED

Theorem gas_run_from_fuel_mono:
  run_from n ctx fn s = r /\ (!e. r <> Error e) /\ n <= m ==>
  run_from m ctx fn s = r
Proof
  rw[run_from_def] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >> gvs[] >>
  rename1 `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` >>
  Cases_on `exec_block n ctx bb s` >> gvs[] >>
  `exec_block m ctx bb s = exec_block n ctx bb s` by
    (irule (cj 2 fuel_mono) >> simp[] >> metis_tac[]) >>
  simp[] >> Cases_on `exec_block n ctx bb s` >> gvs[] >>
  Cases_on `v.vs_halted` >> gvs[] >>
  irule (cj 3 fuel_mono) >> simp[] >> qexists_tac `n` >> simp[]
QED

Theorem gas_path_edge_continue:
  gas_path_edge ctx fn s n (OK t) /\
  run_from fuel ctx fn t = r /\ (!e. r <> Error e) ==>
  ?fuel'. run_from fuel' ctx fn s = r
Proof
  rw[gas_path_edge_def] >> gvs[exit_result_def]
  >- suspend "within"
  >- suspend "enter"
  >> (Cases_on `step_inst fuel' ctx inst s` >> gvs[exit_result_def])
QED
Resume gas_path_edge_continue[within]:
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
  qexists_tac `fuel' + fuel` >> metis_tac[]
QED
Resume gas_path_edge_continue[enter]:
  `step_inst (SUC (fuel' + fuel)) ctx inst s = OK t'` by
    (irule (cj 1 fuel_mono) >> simp[] >> qexists_tac `fuel'` >> simp[]) >>
  `run_from (fuel' + fuel) ctx fn
     (entered with vs_inst_idx := phi_prefix_length target.bb_instructions) =
   run_from fuel ctx fn
     (entered with vs_inst_idx := phi_prefix_length target.bb_instructions)` by
    (irule gas_run_from_fuel_mono >> simp[] >> qexists_tac `fuel` >> simp[]) >>
  `run_blocks (SUC (fuel' + fuel)) ctx fn t' =
   run_from (fuel' + fuel) ctx fn
     (entered with vs_inst_idx := phi_prefix_length target.bb_instructions)` by
    (irule run_blocks_run_from >> simp[]) >>
  qexists_tac `SUC (fuel' + fuel)` >>
  asm_simp_tac (srw_ss()) [run_from_def] >>
  CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [exec_block_def])) >>
  asm_simp_tac (srw_ss()) [] >> simp[run_from_def]
QED
Finalise gas_path_edge_continue

Theorem gas_path_edge_exit:
  gas_path_edge ctx fn s n r /\ exit_result r ==>
  ?fuel. run_from fuel ctx fn s = r
Proof
  rw[gas_path_edge_def] >> gvs[exit_result_def]
  >- (qexists_tac `fuel` >> simp_tac (srw_ss()) [run_from_def] >>
      CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [exec_block_def])) >>
      asm_simp_tac (srw_ss()) []) >>
  qexists_tac `fuel` >>
  Cases_on `step_inst fuel ctx inst s` >> gvs[exit_result_def] >>
  simp_tac (srw_ss()) [run_from_def] >>
  CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [exec_block_def])) >>
  asm_simp_tac (srw_ss()) []
QED

Theorem gas_path_suffix:
  gas_path ctx fn s n r ==> gas_count_suffix n s r
Proof
  cheat
QED

Theorem gas_path_normal:
  gas_path ctx fn s n (OK t) ==>
  ~t.vs_halted /\
  !fuel r.
    run_from fuel ctx fn t = r /\ (!e. r <> Error e) ==>
    ?fuel'. run_from fuel' ctx fn s = r
Proof
  cheat
QED

Theorem gas_path_exit:
  gas_path ctx fn s n r /\ exit_result r ==>
  ?fuel. run_from fuel ctx fn s = r
Proof
  cheat
QED

Theorem gas_path_then:
  gas_path ctx fn s n (OK t) /\ gas_path ctx fn t m r ==>
  gas_path ctx fn s (n + m) r
Proof
  cheat
QED
