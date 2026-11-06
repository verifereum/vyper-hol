(* A run that leaves the function is a counted path: the converse of
   gas_path_exec for exits.  Counted statement simulations use it to turn
   a run_from-level suffix (frag_exec) into gas_path steps. *)
Theory runFromGasPath
Ancestors
  fragGasPath fragExec venomExecSemantics venomExecProofs venomState
  venomInstProofs venomInst gasCount arithmetic list

Theorem run_exit_edge[local]:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\ ~s.vs_halted /\
  step_inst fuel ctx inst s = r /\ exit_result r ==>
  ?n. gas_path_edge ctx fn s n r
Proof
  strip_tac >> simp[gas_path_edge_def] >> metis_tac[]
QED

Theorem run_halt_edge[local]:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\ ~s.vs_halted /\
  step_inst fuel ctx inst s = OK t /\
  is_terminator inst.inst_opcode /\ t.vs_halted ==>
  ?n. gas_path_edge ctx fn s n (Halt t)
Proof
  strip_tac >> simp[gas_path_edge_def] >> metis_tac[]
QED

Theorem run_next_edge[local]:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\ ~s.vs_halted /\
  run_from fuel ctx fn s = r /\
  step_inst fuel ctx inst s = OK t /\ ~is_terminator inst.inst_opcode ==>
  ?n. gas_path_edge ctx fn s n
        (OK (t with vs_inst_idx := SUC s.vs_inst_idx)) /\
      run_from fuel ctx fn (t with vs_inst_idx := SUC s.vs_inst_idx) = r /\
      ~(t with vs_inst_idx := SUC s.vs_inst_idx).vs_halted /\
      lookup_block (t with vs_inst_idx := SUC s.vs_inst_idx).vs_current_bb
        fn.fn_blocks = SOME bb /\
      LENGTH bb.bb_instructions - (t with vs_inst_idx := SUC s.vs_inst_idx).vs_inst_idx
        < LENGTH bb.bb_instructions - s.vs_inst_idx
Proof
  strip_tac >>
  drule_all venomInstProofsTheory.step_preserves_control_flow >> strip_tac >>
  drule_all venomInstProofsTheory.step_preserves_halted >> strip_tac >>
  `run_from fuel ctx fn s =
   run_from fuel ctx fn (t with vs_inst_idx := SUC s.vs_inst_idx)` by
    (simp_tac (srw_ss()) [run_from_def] >>
     asm_simp_tac (srw_ss()) [] >>
     CONV_TAC (LHS_CONV (ONCE_REWRITE_CONV [exec_block_def])) >>
     simp[]) >>
  `s.vs_inst_idx < LENGTH bb.bb_instructions` by
    (gvs[get_instruction_def, AllCaseEqs()]) >>
  qexists_tac `gas_count_step fuel ctx inst s` >>
  simp[] >> simp[gas_path_edge_def] >> metis_tac[]
QED

Theorem run_jump_edge[local]:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\ ~s.vs_halted /\
  run_from fuel ctx fn s = r /\ exit_result r /\
  step_inst fuel ctx inst s = OK t /\
  is_terminator inst.inst_opcode /\ ~t.vs_halted ==>
  ?k u n. fuel = SUC k /\ gas_path_edge ctx fn s n (OK u) /\
    run_from k ctx fn u = r /\ ~u.vs_halted
Proof
  strip_tac >>
  `run_blocks fuel ctx fn t = r` by
    (qpat_x_assum `run_from _ _ _ _ = _` mp_tac >>
     simp[run_from_def, Once exec_block_def]) >>
  Cases_on `fuel`
  >- gvs[Once run_blocks_def, exit_result_def] >>
  rename1 `run_blocks (SUC fuel') ctx fn t = r` >>
  Cases_on `lookup_block t.vs_current_bb fn.fn_blocks`
  >- gvs[Once run_blocks_def, exit_result_def] >>
  rename1 `lookup_block t.vs_current_bb fn.fn_blocks = SOME target` >>
  qspecl_then [`t`, `target.bb_instructions`] strip_assume_tac
    eval_phis_ok_or_error_defs
  >- (rename1 `eval_phis t target.bb_instructions = OK entered` >>
      drule_all run_blocks_run_from >> strip_tac >>
      `~entered.vs_halted` by
        metis_tac[venomExecProofsTheory.eval_phis_preserves_halted] >>
      qexistsl_tac [`fuel'`,
        `entered with vs_inst_idx := phi_prefix_length target.bb_instructions`,
        `gas_count_step (SUC fuel') ctx inst s`] >>
      simp[] >> simp[gas_path_edge_def] >> metis_tac[]) >>
  gvs[Once run_blocks_def] >> metis_tac[exit_result_not_error]
QED

Theorem run_block_paths[local]:
  !fuel ctx fn bb.
  (!k s r. k < fuel /\ run_from k ctx fn s = r /\ exit_result r /\
    ~s.vs_halted ==>
    ?n. gas_path ctx fn s n r) ==>
  !s r. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    run_from fuel ctx fn s = r /\ exit_result r /\ ~s.vs_halted ==>
    ?n. gas_path ctx fn s n r
Proof
  rpt gen_tac >> disch_tac >>
  completeInduct_on `LENGTH bb.bb_instructions - s.vs_inst_idx` >>
  rpt strip_tac >>
  Cases_on `get_instruction bb s.vs_inst_idx`
  >- (qpat_x_assum `run_from _ _ _ _ = _` mp_tac >>
      simp[run_from_def, Once exec_block_def] >>
      metis_tac[exit_result_not_error]) >>
  rename1 `get_instruction bb s.vs_inst_idx = SOME inst` >>
  Cases_on `step_inst fuel ctx inst s`
  >- (rename1 `step_inst fuel ctx inst s = OK t` >>
      Cases_on `is_terminator inst.inst_opcode`
      >- (Cases_on `t.vs_halted`
          >- (`r = Halt t` by
                (qpat_x_assum `run_from _ _ _ _ = _` mp_tac >>
                 simp[run_from_def, Once exec_block_def]) >>
              drule_all run_halt_edge >> strip_tac >>
              metis_tac[gas_path_rules]) >>
          drule_all run_jump_edge >> strip_tac >>
          `?m. gas_path ctx fn u m r` by
            (qpat_x_assum `!k s r. _` irule >> simp[] >> qexists_tac `k` >> simp[]) >>
          metis_tac[gas_path_rules]) >>
      drule_all run_next_edge >> strip_tac >>
      `?m. gas_path ctx fn (t with vs_inst_idx := SUC s.vs_inst_idx) m r` by
        (first_x_assum irule >> metis_tac[]) >>
      metis_tac[gas_path_rules]) >>
  `r = step_inst fuel ctx inst s` by
    (qpat_x_assum `run_from _ _ _ _ = _` mp_tac >>
     simp[run_from_def, Once exec_block_def]) >>
  `?n. gas_path_edge ctx fn s n r` by metis_tac[run_exit_edge] >>
  metis_tac[gas_path_rules]
QED

Theorem run_from_gas_path:
  !fuel ctx fn s r.
    run_from fuel ctx fn s = r /\ exit_result r /\ ~s.vs_halted ==>
    ?n. gas_path ctx fn s n r
Proof
  completeInduct_on `fuel` >> rpt gen_tac >> strip_tac >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks`
  >- (qpat_x_assum `run_from _ _ _ _ = _` mp_tac >>
      simp[run_from_def] >> metis_tac[exit_result_not_error]) >>
  irule run_block_paths >> simp[] >> qexists_tac `fuel` >> simp[] >>
  rpt strip_tac >> first_x_assum drule >> metis_tac[]
QED
