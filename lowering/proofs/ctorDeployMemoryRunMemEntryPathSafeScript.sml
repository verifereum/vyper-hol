Theory ctorDeployMemoryRunMemEntryPathSafe
Ancestors
  fragGasPathMem fragExecMem fragExec memSafeRun venomExecSemantics
  venomExecProofs venomInstProofs venomInst venomState list arithmetic

Theorem ctor_checked_edge_check_up[local]:
  (revert_forward_at bb s.vs_inst_idx \/ mem_safe_step a ctx inst s) /\
  step_inst a ctx inst s = OK t /\ a <= b ==>
  (revert_forward_at bb s.vs_inst_idx \/ mem_safe_step b ctx inst s)
Proof
  strip_tac >> simp[] >> disj2_tac >>
  irule (cj 1 mem_safe_fuel_mono_up) >>
  qexists_tac `a` >> simp[]
QED

Theorem ctor_checked_within_all_fuel[local]:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  step_inst a ctx inst s = OK t /\ ~is_terminator inst.inst_opcode /\
  (revert_forward_at bb s.vs_inst_idx \/ mem_safe_step a ctx inst s) /\
  (!fuel. mem_safe_run fuel ctx fn (t with vs_inst_idx := SUC s.vs_inst_idx)) ==>
  !fuel. mem_safe_run fuel ctx fn s
Proof
  rpt strip_tac >>
  `step_inst (a + fuel) ctx inst s = OK t` by
    (irule (cj 1 fuel_mono) >> simp[] >> qexists_tac `a` >> simp[]) >>
  `revert_forward_at bb s.vs_inst_idx \/ mem_safe_step (a + fuel) ctx inst s` by
    (irule ctor_checked_edge_check_up >> qexists_tac `a` >> metis_tac[LESS_EQ_ADD]) >>
  `mem_safe_run (a + fuel) ctx fn s` by
    (drule_all mem_safe_run_step >> metis_tac[]) >>
  irule mem_safe_run_fuel_mono_down >> qexists_tac `a + fuel` >> simp[]
QED

Theorem ctor_checked_enter_all_fuel[local]:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  step_inst a ctx inst s = OK t /\ is_terminator inst.inst_opcode /\
  ~t.vs_halted /\
  lookup_block t.vs_current_bb fn.fn_blocks = SOME target /\
  eval_phis t target.bb_instructions = OK entered /\
  (revert_forward_at bb s.vs_inst_idx \/ mem_safe_step a ctx inst s) /\
  (!fuel. mem_safe_run fuel ctx fn
    (entered with vs_inst_idx := phi_prefix_length target.bb_instructions)) ==>
  !fuel. mem_safe_run fuel ctx fn s
Proof
  rpt strip_tac >>
  `step_inst (SUC (a + fuel)) ctx inst s = OK t` by
    (irule (cj 1 fuel_mono) >> simp[] >> qexists_tac `a` >> simp[]) >>
  `revert_forward_at bb s.vs_inst_idx \/ mem_safe_step (SUC (a + fuel)) ctx inst s` by
    (irule ctor_checked_edge_check_up >> qexists_tac `a` >> metis_tac[LESS_EQ_ADD, LESS_EQ_SUC_REFL, LESS_EQ_TRANS]) >>
  `mem_safe_blocks (SUC (a + fuel)) ctx fn t` by
    (drule_all mem_safe_blocks_run >> simp[]) >>
  `mem_safe_run (SUC (a + fuel)) ctx fn s` by
    (simp[Once mem_safe_run_def, Once mem_safe_block_def, Once exec_block_def]) >>
  irule mem_safe_run_fuel_mono_down >>
  qexists_tac `SUC (a + fuel)` >> simp[]
QED

Theorem ctor_checked_phi_step_error[local]:
  !fuel ctx inst s. inst.inst_opcode = PHI ==>
  step_inst fuel ctx inst s = Error "phi outside prefix"
Proof
  rpt strip_tac >> simp[step_inst_non_invoke, step_inst_base_def]
QED

Theorem ctor_checked_ok_edge_zero_phi:
  !ctx fn s n t bb.
  gas_path_mem_edge ctx fn s n (OK t) /\
  s.vs_inst_idx = 0 /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb ==>
  phi_prefix_length bb.bb_instructions = 0
Proof
  rpt gen_tac >> simp[gas_path_mem_edge_def] >> rpt strip_tac >>
  gvs[exit_result_def] >>
  `inst.inst_opcode <> PHI` by
    (strip_tac >> gvs[ctor_checked_phi_step_error]) >>
  Cases_on `bb.bb_instructions` >>
  gvs[get_instruction_def, phi_prefix_length_def]
QED

Theorem ctor_checked_ok_path_zero_phi:
  !ctx fn s n t bb.
  gas_path_mem ctx fn s n (OK t) /\
  s.vs_inst_idx = 0 /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  (!last. lookup_block t.vs_current_bb fn.fn_blocks = SOME last /\
          t.vs_inst_idx = 0 ==> phi_prefix_length last.bb_instructions = 0) ==>
  phi_prefix_length bb.bb_instructions = 0
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `gas_path_mem _ _ _ _ _` mp_tac >>
  simp[Once gas_path_mem_cases] >> strip_tac >> gvs[exit_result_def] >>
  metis_tac[ctor_checked_ok_edge_zero_phi]
QED

Theorem ctor_checked_entry_blocks_bridge:
  !ctx fn s bb.
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  phi_prefix_length bb.bb_instructions = 0 /\ s.vs_inst_idx = 0 /\
  (!fuel. mem_safe_run fuel ctx fn s) ==>
  !fuel. mem_safe_blocks fuel ctx fn s
Proof
  rpt gen_tac >> strip_tac >> Cases >>
  simp[Once mem_safe_blocks_def, eval_phis_no_phi] >>
  `s with vs_inst_idx := 0 = s` by simp[venom_state_component_equality] >>
  gvs[mem_safe_run_def]
QED

Theorem ctor_checked_raw_jump_all_fuel[local]:
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME inst /\
  step_inst a ctx inst s = OK (jump_to lbl s) /\
  is_terminator inst.inst_opcode /\
  (revert_forward_at bb s.vs_inst_idx \/ mem_safe_step a ctx inst s) /\
  (!target. lookup_block lbl fn.fn_blocks = SOME target ==>
    phi_prefix_length target.bb_instructions = 0) /\
  (!fuel. mem_safe_run fuel ctx fn (jump_to lbl s)) ==>
  !fuel. mem_safe_run fuel ctx fn s
Proof
  rpt strip_tac >>
  `step_inst (SUC (a + fuel)) ctx inst s = OK (jump_to lbl s)` by
    (irule (cj 1 fuel_mono) >> simp[] >> qexists_tac `a` >> simp[]) >>
  `revert_forward_at bb s.vs_inst_idx \/ mem_safe_step (SUC (a + fuel)) ctx inst s` by
    (irule ctor_checked_edge_check_up >> qexists_tac `a` >>
     metis_tac[LESS_EQ_ADD, LESS_EQ_SUC_REFL, LESS_EQ_TRANS]) >>
  `mem_safe_blocks (SUC (a + fuel)) ctx fn (jump_to lbl s)` by
    (Cases_on `lookup_block lbl fn.fn_blocks` >>
     simp[Once mem_safe_blocks_def, jump_to_def] >>
     fs[] >>
     simp[eval_phis_no_phi] >>
     qpat_x_assum `!fuel. mem_safe_run _ _ _ _` (qspec_then `a + fuel` mp_tac) >>
     simp[Once mem_safe_run_def, jump_to_def]) >>
  `mem_safe_run (SUC (a + fuel)) ctx fn s` by
    (simp[Once mem_safe_run_def, Once mem_safe_block_def, Once exec_block_def] >>
     Cases_on `(jump_to lbl s).vs_halted` >> simp[]) >>
  irule mem_safe_run_fuel_mono_down >>
  qexists_tac `SUC (a + fuel)` >> simp[]
QED

Theorem ctor_checked_path_all_fuel:
  !ctx fn s n r. gas_path_mem ctx fn s n r ==>
  gas_path_mem ctx fn s n r /\
  (!t. r = OK t /\
    (!bb. lookup_block t.vs_current_bb fn.fn_blocks = SOME bb /\
      t.vs_inst_idx = 0 ==> phi_prefix_length bb.bb_instructions = 0) /\
    (!fuel. mem_safe_run fuel ctx fn t) ==>
    !fuel. mem_safe_run fuel ctx fn s)
Proof
  ho_match_mp_tac gas_path_mem_ind >> conj_tac
  >- (rpt strip_tac >> gvs[gas_path_mem_rules]) >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      conj_tac >- metis_tac[gas_path_mem_rules] >>
      gen_tac >> strip_tac >> gvs[] >>
      `!fuel. mem_safe_run fuel ctx fn t` by metis_tac[] >>
      qpat_x_assum `gas_path_mem_edge _ _ _ _ _` mp_tac >>
      simp[gas_path_mem_edge_def] >> strip_tac >> gvs[exit_result_def] >>
      FIRST
      [qpat_x_assum `~is_terminator _` assume_tac >>
         irule ctor_checked_within_all_fuel >> metis_tac[],
       qpat_x_assum `eval_phis _ _ = OK _` assume_tac >>
         irule ctor_checked_enter_all_fuel >> metis_tac[],
       qpat_x_assum `exit_result _` assume_tac >> metis_tac[exit_result_def],
       all_tac] >>
      `!target. lookup_block lbl fn.fn_blocks = SOME target ==>
         phi_prefix_length target.bb_instructions = 0` by
        (rpt strip_tac >> irule ctor_checked_ok_path_zero_phi >>
         qexistsl [`ctx`, `fn`, `n'`, `jump_to lbl s`, `t`] >>
         simp[jump_to_def] >> metis_tac[]) >>
      irule ctor_checked_raw_jump_all_fuel >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >> conj_tac
  >- metis_tac[gas_path_mem_rules] >>
  rpt strip_tac >> gvs[exit_result_def]
QED

Theorem ctor_checked_success_all_fuel:
  gas_path_mem ctx fn s n (OK t) /\
  (!bb. lookup_block t.vs_current_bb fn.fn_blocks = SOME bb /\
    t.vs_inst_idx = 0 ==> phi_prefix_length bb.bb_instructions = 0) /\
  (!fuel. mem_safe_run fuel ctx fn t) ==>
  !fuel. mem_safe_run fuel ctx fn s
Proof
  metis_tac[ctor_checked_path_all_fuel]
QED
