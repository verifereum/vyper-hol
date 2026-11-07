Theory aggregateCountedRawRelabel
Ancestors
  aggregateCountedCutBridge exprSimAbiGasBridge abiEncoderObserver
  fragGasPath gasCount venomExecSemantics venomExecProofs venomState
  venomInst emitHelper fragExec exprLoweringProps fragGasMode list rich_list
  venomInstProofs arithmetic

Theorem frag_relabel_off_cut_opcodes_raw:
  cs_extends sa sb /\ sa.cs_blocks <> sb.cs_blocks /\ frag_ops_free sa sb /\
  fn_has_code sa sb fn /\ LENGTH ids = LENGTH sa.cs_current_insts /\
  L <> sb.cs_current_bb /\
  ~MEM L (MAP (\bb. bb.bb_label) (emitted_blocks sa sb)) /\
  (u.vs_current_bb,u.vs_inst_idx) IN
    frag_observer_region (start_relabel L ids sa) (start_swap sa L ids sb) /\
  (u.vs_current_bb,u.vs_inst_idx) <> frag_observer_cut sb /\
  lookup_block u.vs_current_bb (frag_relabel_observer sa sb L ids fn id).fn_blocks = SOME bb /\
  get_instruction bb u.vs_inst_idx = SOME inst ==>
  inst.inst_opcode <> GAS /\ inst.inst_opcode <> INVOKE /\
  inst.inst_opcode <> PHI /\ inst.inst_opcode <> STOP /\ inst.inst_opcode <> RETURN
Proof
  strip_tac >>
  `(u.vs_current_bb = L ==> LENGTH sa.cs_current_insts <= u.vs_inst_idx)` by
    (fs[frag_observer_region_def, start_relabel_def] >> metis_tac[]) >>
  drule_all frag_relabel_code_provenance >> strip_tac >>
  fs[frag_ops_free_def, EVERY_MEM]
QED

Theorem frag_relabel_region_closed_raw:
  cs_extends sa sb /\ sa.cs_blocks <> sb.cs_blocks /\ frag_ops_free sa sb /\
  fn_has_code sa sb fn /\ LENGTH ids = LENGTH sa.cs_current_insts /\
  L <> sb.cs_current_bb /\
  ~MEM L (MAP (\bb. bb.bb_label) (emitted_blocks sa sb)) /\
  EVERY (\i. ~MEM (Label L) i.inst_operands) (frag_code sa sb) ==>
  observer_region_closed ctx (frag_relabel_observer sa sb L ids fn id)
    (frag_observer_cut sb)
    (frag_observer_region (start_relabel L ids sa) (start_swap sa L ids sb))
Proof
  strip_tac >> rw[observer_region_closed_def] >>
  fs[abi_observer_step_def] >>
  drule_all frag_relabel_off_cut_opcodes_raw >> strip_tac
  >- (drule_all step_preserves_control_flow >> strip_tac >>
      gvs[frag_observer_region_def] >> metis_tac[LESS_EQ_SUC_REFL, LESS_EQ_TRANS]) >>
  `MEM inst.inst_opcode [JMP; JNZ; DJMP]` by
    (Cases_on `inst.inst_opcode` >> fs[is_terminator_def] >>
     gvs[step_inst_non_invoke, step_inst_base_opcode_eqs, AllCaseEqs()] >>
     pairarg_tac >> gvs[]) >>
  `middle.vs_current_bb <> L` by
    (`(s.vs_current_bb = L ==> LENGTH sa.cs_current_insts <= s.vs_inst_idx)` by
       (fs[frag_observer_region_def, start_relabel_def] >> metis_tac[]) >>
     `step_inst_base inst s = OK middle` by metis_tac[step_inst_non_invoke] >>
     fs[EVERY_MEM] >>
     metis_tac[frag_relabel_jump_no_reentry, MEM]) >>
  drule eval_phis_preserves_current_bb >> strip_tac >>
  drule frag_relabel_observer_lookup_cases >> strip_tac >>
  drule_all start_swap_fields >> strip_tac >>
  gvs[frag_observer_region_def, start_relabel_def, MEM_MAP] >> metis_tac[]
QED

Theorem frag_relabel_target_phis_raw:
  cs_extends sa sb /\ sa.cs_blocks <> sb.cs_blocks /\ frag_ops_free sa sb /\
  fn_has_code sa sb fn /\ lbl <> L /\
  lookup_block lbl (frag_relabel_observer sa sb L ids fn id).fn_blocks = SOME bb ==>
  (lbl = sb.cs_current_bb /\ sb.cs_current_insts = [] /\
   bb = <|bb_label := sb.cs_current_bb;
          bb_instructions := [mk_inst id STOP [] []]|>) \/
  (?original. lookup_block lbl fn.fn_blocks = SOME original /\
    phi_prefix_length original.bb_instructions = 0 /\
    phi_prefix_length bb.bb_instructions = 0)
Proof
  strip_tac >>
  `emitted_blocks sa sb <> []` by
    (drule frag_extends_emitted_shape >> strip_tac >> gvs[]) >>
  drule frag_relabel_observer_lookup_cases >> strip_tac
  >- (gvs[] >> Cases_on `sb.cs_current_insts = []` >- simp[] >>
      disj2_tac >>
      `EVERY (\i. i.inst_opcode <> PHI) sb.cs_current_insts` by
        (fs[frag_ops_free_def, frag_code_def, NULL_EQ, EVERY_APPEND, EVERY_MEM] >>
         metis_tac[]) >>
      fs[fn_has_code_def, IS_PREFIX_APPEND] >>
      Cases_on `sb.cs_current_insts` >>
      fs[phi_prefix_length_def, mk_inst_def]) >>
  disj2_tac >>
  drule_all start_swap_emitted_blocks >> strip_tac >> fs[MEM_APPEND] >> gvs[] >>
  `MEM bb (emitted_blocks sa sb)` by
    (`emitted_blocks sa sb = FRONT (emitted_blocks sa sb) ++
       [LAST (emitted_blocks sa sb)]` by simp[APPEND_FRONT_LAST] >>
     metis_tac[MEM_APPEND]) >>
  drule_all frag_relabel_front_nonphi >> strip_tac >>
  qexists_tac `bb` >> conj_tac >- (fs[fn_has_code_def] >> metis_tac[]) >>
  Cases_on `bb.bb_instructions` >> fs[phi_prefix_length_def]
QED

Theorem frag_relabel_jump_control_raw[local]:
  MEM inst.inst_opcode [JMP; JNZ; DJMP] /\ step_inst_base inst u = OK middle ==>
  step_inst_base inst (u with <|vs_current_bb := b; vs_prev_bb := p|>) =
    OK (middle with vs_prev_bb := SOME b)
Proof
  `!op s b p. eval_operand op (s with <|vs_current_bb := b; vs_prev_bb := p|>) =
      eval_operand op s` by
    (Cases >> simp[eval_operand_def, lookup_var_def]) >>
  simp[MEM] >> strip_tac >>
  asm_simp_tac bool_ss [step_inst_base_opcode_eqs] >>
  simp[eval_operand_def, lookup_var_def] >>
  gvs[step_inst_base_opcode_eqs, AllCaseEqs()] >>
  simp[jump_to_def, venom_state_component_equality]
QED

Theorem frag_relabel_step_edge_raw:
  cs_extends sa sb /\ sa.cs_blocks <> sb.cs_blocks /\ frag_ops_free sa sb /\
  fn_has_code sa sb fn /\ LENGTH ids = LENGTH sa.cs_current_insts /\
  L <> sb.cs_current_bb /\
  ~MEM L (MAP (\bb. bb.bb_label) (emitted_blocks sa sb)) /\
  EVERY (\i. ~MEM (Label L) i.inst_operands) (frag_code sa sb) /\
  (u.vs_current_bb,u.vs_inst_idx) IN
    frag_observer_region (start_relabel L ids sa) (start_swap sa L ids sb) /\
  frag_relabel_state L sa.cs_current_bb u v /\
  abi_observer_step ctx (frag_relabel_observer sa sb L ids fn id)
    (frag_observer_cut sb) u u' ==>
  ?v'. gas_path_edge ctx fn v 0 (OK v') /\ frag_relabel_state L sa.cs_current_bb u' v'
Proof
  strip_tac >> fs[abi_observer_step_def] >>
  drule_all frag_relabel_off_cut_opcodes_raw >> strip_tac >>
  `(u.vs_current_bb = L ==> LENGTH sa.cs_current_insts <= u.vs_inst_idx)` by
    (fs[frag_observer_region_def, start_relabel_def] >> metis_tac[]) >>
  `?original. lookup_block
    (if u.vs_current_bb = L then sa.cs_current_bb else u.vs_current_bb)
      fn.fn_blocks = SOME original /\
    get_instruction original u.vs_inst_idx = SOME inst` by
    (drule_all frag_relabel_instruction_agrees >> simp[]) >>
  `step_inst_base inst u = OK middle` by metis_tac[step_inst_non_invoke] >>
  drule frag_relabel_state_fields >> strip_tac
  >- suspend "ordinary" >>
  `MEM inst.inst_opcode [JMP; JNZ; DJMP]` by
    (Cases_on `inst.inst_opcode` >> fs[is_terminator_def] >>
     gvs[step_inst_non_invoke, step_inst_base_opcode_eqs, AllCaseEqs()] >>
     pairarg_tac >> gvs[]) >>
  `middle.vs_current_bb <> L` by
    (fs[EVERY_MEM] >> metis_tac[frag_relabel_jump_no_reentry, MEM]) >>
  drule_all frag_relabel_target_phis_raw >> strip_tac
  >- suspend "raw_cut" >> suspend "entered"
QED

Resume frag_relabel_step_edge_raw[ordinary]:
  `middle.vs_current_bb = u.vs_current_bb` by
    metis_tac[step_preserves_control_flow, step_inst_non_invoke] >>
  `!b p. step_inst_base inst (u with <|vs_current_bb := b; vs_prev_bb := p|>) =
      OK (middle with <|vs_current_bb := b; vs_prev_bb := p|>)` by
    (Cases_on `is_pseudo inst.inst_opcode`
     >- (Cases_on `inst.inst_opcode` >> fs[is_pseudo_def] >>
         asm_simp_tac bool_ss [step_inst_base_opcode_eqs] >>
         rpt strip_tac >> gvs[step_inst_base_opcode_eqs, AllCaseEqs()] >>
         simp[update_var_def]) >>
     metis_tac[frag_relabel_base_ordinary]) >>
  fs[frag_relabel_state_def] >> gvs[] >>
  qexists_tac `middle with <|vs_current_bb :=
     (if u.vs_current_bb = L then sa.cs_current_bb else u.vs_current_bb);
     vs_prev_bb := p; vs_inst_idx := SUC u.vs_inst_idx|>` >>
  gvs[] >> conj_tac
  >- (simp[gas_path_edge_def] >> qexists_tac `0` >>
      simp[step_inst_non_invoke, gas_count_step_def]) >>
  qexists_tac `p` >> simp[venom_state_component_equality]
QED

Resume frag_relabel_step_edge_raw[raw_cut]:
  `middle = jump_to sb.cs_current_bb u` by
    (Cases_on `inst.inst_opcode` >> fs[MEM] >>
     gvs[step_inst_base_opcode_eqs, AllCaseEqs(), jump_to_def]) >>
  gvs[eval_phis_def, phi_prefix_length_def, mk_inst_def] >>
  qexists_tac `jump_to sb.cs_current_bb v` >>
  fs[frag_relabel_state_def] >> gvs[] >>
  `!b p. step_inst_base inst (u with <|vs_prev_bb := p; vs_current_bb := b|>) =
       OK (jump_to sb.cs_current_bb (u with <|vs_prev_bb := p; vs_current_bb := b|>))` by
    (rpt gen_tac >>
     `MEM inst.inst_opcode [JMP; JNZ; DJMP]` by simp[MEM] >>
     drule_all frag_relabel_jump_control_raw >> simp[jump_to_def]) >>
  (conj_tac
  >- (simp[gas_path_edge_def] >> qexists_tac `0` >>
      simp[step_inst_non_invoke, gas_count_step_def] >> disj2_tac >> disj1_tac >>
      qexists_tac `sb.cs_current_bb` >> simp[]) >>
  simp[jump_to_def, venom_state_component_equality])
QED

Resume frag_relabel_step_edge_raw[entered]:
  qpat_x_assum `eval_phis _ _ = _` mp_tac >>
  once_rewrite_tac[GSYM eval_phis_prefix] >> simp[eval_phis_def] >> strip_tac >> gvs[] >>
  fs[frag_relabel_state_def] >> gvs[] >>
  `step_inst_base inst (u with <|vs_current_bb :=
       (if u.vs_current_bb = L then sa.cs_current_bb else u.vs_current_bb);
       vs_prev_bb := p|>) =
    OK (entered with vs_prev_bb :=
       SOME (if u.vs_current_bb = L then sa.cs_current_bb else u.vs_current_bb))` by
    metis_tac[frag_relabel_jump_control_raw, MEM] >>
  qexists_tac `entered with <|vs_prev_bb :=
       SOME (if u.vs_current_bb = L then sa.cs_current_bb else u.vs_current_bb);
       vs_inst_idx := 0|>` >>
  gvs[] >> (conj_tac
  >- (simp[gas_path_edge_def] >> qexists_tac `0` >>
      simp[step_inst_non_invoke, gas_count_step_def] >>
      disj1_tac >>
      once_rewrite_tac[GSYM eval_phis_prefix] >> simp[eval_phis_def]) >>
  qexists_tac `SOME (if u.vs_current_bb = L then sa.cs_current_bb else u.vs_current_bb)` >>
  simp[venom_state_component_equality])
QED

Finalise frag_relabel_step_edge_raw

Theorem frag_relabel_prefix_path_raw:
  !ctx observed cut u t. local_prefix ctx observed cut u t ==>
  !sa sb L ids fn id v.
    observed = frag_relabel_observer sa sb L ids fn id /\
    cut = frag_observer_cut sb /\
    cs_extends sa sb /\ sa.cs_blocks <> sb.cs_blocks /\ frag_ops_free sa sb /\
    fn_has_code sa sb fn /\ LENGTH ids = LENGTH sa.cs_current_insts /\
    L <> sb.cs_current_bb /\
    ~MEM L (MAP (\bb. bb.bb_label) (emitted_blocks sa sb)) /\
    EVERY (\i. ~MEM (Label L) i.inst_operands) (frag_code sa sb) /\
    (u.vs_current_bb,u.vs_inst_idx) IN
      frag_observer_region (start_relabel L ids sa) (start_swap sa L ids sb) /\
    frag_relabel_state L sa.cs_current_bb u v ==>
    ?t'. gas_path ctx fn v 0 (OK t') /\
         frag_relabel_state L sa.cs_current_bb t t'
Proof
  ho_match_mp_tac local_prefix_ind >> conj_tac
  >- (rpt strip_tac >> qexists_tac `v` >> simp[] >>
      irule (cj 1 gas_path_rules) >>
      drule frag_relabel_state_fields >> simp[]) >>
  rpt strip_tac >> gvs[] >>
  drule_all frag_relabel_step_edge_raw >> strip_tac >>
  `observer_region_closed ctx (frag_relabel_observer sa sb L ids fn id)
    (frag_observer_cut sb)
    (frag_observer_region (start_relabel L ids sa) (start_swap sa L ids sb))` by
      (irule frag_relabel_region_closed_raw >> simp[]) >>
  `?t'. gas_path ctx fn v' 0 (OK t') /\
        frag_relabel_state L sa.cs_current_bb t t'` by
    (first_x_assum irule >> simp[] >>
     fs[observer_region_closed_def] >> metis_tac[]) >>
  qexists_tac `t'` >> simp[] >>
  metis_tac[cj 2 gas_path_rules, ADD]
QED


Theorem frag_relabel_observer_idempotent:
  cs_extends sa sb /\ sa.cs_blocks <> sb.cs_blocks /\
  L <> sb.cs_current_bb /\
  ~MEM sb.cs_current_bb (MAP (\bb. bb.bb_label) (FRONT (emitted_blocks sa sb))) ==>
  frag_observer (start_relabel L ids sa) (start_swap sa L ids sb)
    (frag_relabel_observer sa sb L ids fn id) id =
  frag_relabel_observer sa sb L ids fn id
Proof
  strip_tac >> drule_all start_swap_fields >> strip_tac >>
  `!bb. MEM bb (emitted_blocks (start_relabel L ids sa) (start_swap sa L ids sb)) ==>
    bb.bb_label <> sb.cs_current_bb` by
    (drule_all start_swap_emitted_blocks >> simp[MEM_APPEND, MEM] >>
     rpt strip_tac >> gvs[MEM_MAP] >> metis_tac[]) >>
  `~MEM <|bb_label := sb.cs_current_bb;
       bb_instructions := sb.cs_current_insts ++ [mk_inst id STOP [] []]|>
    (emitted_blocks (start_relabel L ids sa) (start_swap sa L ids sb))` by
    (strip_tac >> first_x_assum drule >> simp[]) >>
  simp[frag_observer_def, frag_relabel_observer_def, ir_function_component_equality, FILTER_EQ_ID, EVERY_MEM]
QED

Theorem frag_relabel_halt_prefix_raw:
  cs_extends sa sb /\ sa.cs_blocks <> sb.cs_blocks /\ frag_ops_free sa sb /\
  fn_has_code sa sb fn /\ LENGTH ids = LENGTH sa.cs_current_insts /\
  L <> sb.cs_current_bb /\
  ~MEM L (MAP (\bb. bb.bb_label) (emitted_blocks sa sb)) /\
  ~MEM sb.cs_current_bb (MAP (\bb. bb.bb_label) (FRONT (emitted_blocks sa sb))) /\
  EVERY (\i. ~MEM (Label L) i.inst_operands) (frag_code sa sb) /\
  (s.vs_current_bb,s.vs_inst_idx) IN
    frag_observer_region (start_relabel L ids sa) (start_swap sa L ids sb) /\
  ~s.vs_halted /\
  run_from fuel ctx (frag_relabel_observer sa sb L ids fn id) s = Halt h /\
  (h.vs_current_bb,h.vs_inst_idx) = frag_observer_cut sb ==>
  ?u. local_prefix ctx (frag_relabel_observer sa sb L ids fn id)
       (frag_observer_cut sb) s u /\ stop_view u = h
Proof
  strip_tac >>
  drule_all frag_relabel_observer_idempotent >> strip_tac >>
  drule_all frag_relabel_observer_has_code >> strip_tac >>
  drule_all start_relabel_gas_free >> strip_tac >>
  drule_all start_relabel_extends >> strip_tac >>
  drule_all start_swap_fields >> strip_tac >>
  mp_tac (Q.INST [`sa` |-> `start_relabel L ids sa`,
     `sb` |-> `start_swap sa L ids sb`,
     `fn` |-> `frag_relabel_observer sa sb L ids fn id`]
     frag_observer_halt_cut_prefix) >>
  simp[frag_observer_cut_def]
QED


Theorem exec_pure1_not_exit[local]:
  !f inst s. ~exit_result (exec_pure1 f inst s)
Proof
  rpt gen_tac >>
  simp[exec_pure1_def] >>
  rpt (BasicProvers.TOP_CASE_TAC >> simp[exit_result_def])
QED

Theorem exec_pure2_not_exit[local]:
  !f inst s. ~exit_result (exec_pure2 f inst s)
Proof
  rpt gen_tac >>
  simp[exec_pure2_def] >>
  rpt (BasicProvers.TOP_CASE_TAC >> simp[exit_result_def])
QED

Theorem exec_pure3_not_exit[local]:
  !f inst s. ~exit_result (exec_pure3 f inst s)
Proof
  rpt gen_tac >>
  simp[exec_pure3_def] >>
  rpt (BasicProvers.TOP_CASE_TAC >> simp[exit_result_def])
QED

Theorem exec_read0_not_exit[local]:
  !f inst s. ~exit_result (exec_read0 f inst s)
Proof
  rpt gen_tac >> simp[exec_read0_def] >>
  rpt (BasicProvers.TOP_CASE_TAC >> simp[exit_result_def])
QED

Theorem exec_read1_not_exit[local]:
  !f inst s. ~exit_result (exec_read1 f inst s)
Proof
  rpt gen_tac >> simp[exec_read1_def] >>
  rpt (BasicProvers.TOP_CASE_TAC >> simp[exit_result_def])
QED

Theorem exec_write2_not_exit[local]:
  !f inst s. ~exit_result (exec_write2 f inst s)
Proof
  rpt gen_tac >> simp[exec_write2_def] >>
  rpt (BasicProvers.TOP_CASE_TAC >> simp[exit_result_def])
QED

val raw_opcode_rewrites =
  map (fn th => (rhs (fst (dest_imp (snd (strip_forall (concl th))))), th))
    (CONJUNCTS step_inst_base_opcode_eqs);
fun raw_opcode_eq eq =
  let val (_, th) = valOf (List.find
        (fn (key, _) => aconv key (rhs (concl eq))) raw_opcode_rewrites)
  in RULE_ASSUM_TAC (PURE_REWRITE_RULE [MATCH_MP th eq]) >>
     PURE_ONCE_REWRITE_TAC [MATCH_MP th eq] end;

    val copy_tac = rpt strip_tac >>
      namedCases_on `inst.inst_operands` ["", "a ops"] >> gvs[exit_result_def] >>
      namedCases_on `ops` ["", "b ops2"] >> gvs[exit_result_def] >>
      namedCases_on `ops2` ["", "c ops3"] >> gvs[exit_result_def] >>
      Cases_on `ops3` >> gvs[exit_result_def] >>
      Cases_on `eval_operand a s` >> gvs[exit_result_def] >>
      Cases_on `eval_operand b s` >> gvs[exit_result_def] >>
      Cases_on `eval_operand c s` >> gvs[exit_result_def];
    val evalone_tac = rpt strip_tac >>
      namedCases_on `inst.inst_operands` ["", "a ops"] >> gvs[exit_result_def] >>
      Cases_on `ops` >> gvs[exit_result_def] >>
      Cases_on `eval_operand a s` >> gvs[exit_result_def] >>
      namedCases_on `inst.inst_outputs` ["", "out outs"] >> gvs[exit_result_def] >>
      Cases_on `outs` >> gvs[exit_result_def];
    val literal_tac = rpt strip_tac >>
      namedCases_on `inst.inst_operands` ["", "a ops"] >> gvs[exit_result_def] >>
      Cases_on `a` >> gvs[exit_result_def] >>
      Cases_on `ops` >> gvs[exit_result_def] >>
      rename1 `inst.inst_operands = [Lit idx]` >>
      Cases_on `w2n idx < LENGTH s.vs_params` >> gvs[exit_result_def] >>
      namedCases_on `inst.inst_outputs` ["", "out outs"] >> gvs[exit_result_def] >>
      Cases_on `outs` >> gvs[exit_result_def];
    val emptyops_tac = rpt strip_tac >>
      Cases_on `inst.inst_operands` >> gvs[exit_result_def] >>
      namedCases_on `inst.inst_outputs` ["", "out outs"] >> gvs[exit_result_def] >>
      Cases_on `outs` >> gvs[exit_result_def];
    val gas_tac = rpt strip_tac >>
      namedCases_on `inst.inst_outputs` ["", "out outs"] >> gvs[exit_result_def] >>
      Cases_on `outs` >> gvs[exit_result_def] >>
      Cases_on `s.vs_gas_readings` >> gvs[exit_result_def];

Theorem step_inst_exit_opcodes[local]:
  !inst s. exit_result (step_inst_base inst s) ==>
    MEM inst.inst_opcode
      [INVOKE; STOP; RETURN; SINK; RET; RETFMP; DRET; REVERT;
       ASSERT; ASSERT_UNREACHABLE; RETURNDATACOPY; LOG; SELFDESTRUCT;
       INVALID; CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2; SSTORE; TSTORE]
Proof
    rpt gen_tac >> Cases_on `inst.inst_opcode` >> simp[] >>
    first_assum raw_opcode_eq >>
    simp[exec_pure1_not_exit, exec_pure2_not_exit, exec_pure3_not_exit,
         exec_read0_not_exit, exec_read1_not_exit, exec_write2_not_exit,
         exec_alloca_def, exec_gas_def] >> all_tac
    >~ [`inst.inst_opcode = MCOPY`] >- copy_tac
    >~ [`inst.inst_opcode = CALLDATACOPY`] >- copy_tac
    >~ [`inst.inst_opcode = CODECOPY`] >- copy_tac
    >~ [`inst.inst_opcode = DLOADBYTES`] >- copy_tac
    >~ [`inst.inst_opcode = ASSIGN`] >- evalone_tac
    >~ [`inst.inst_opcode = DALLOCA`] >- evalone_tac
    >~ [`inst.inst_opcode = SETFMP`] >- evalone_tac
    >~ [`inst.inst_opcode = PARAM`] >- literal_tac
    >~ [`inst.inst_opcode = FMP_PARAM`] >- literal_tac
    >~ [`inst.inst_opcode = RETPC_PARAM`] >- literal_tac
    >~ [`inst.inst_opcode = GAS`] >- gas_tac
    >~ [`inst.inst_opcode = GETFMP`] >- emptyops_tac
    >~ [`inst.inst_opcode = INITIAL_FMP`] >- emptyops_tac >>
    rpt strip_tac >> gvs[exit_result_def]
    >~ [`inst.inst_opcode = ALLOCA`]
    >- (namedCases_on `inst.inst_operands` ["", "a ops"] >> gvs[exit_result_def] >>
        Cases_on `a` >> gvs[exit_result_def] >>
        Cases_on `ops` >> gvs[exit_result_def] >>
        namedCases_on `inst.inst_outputs` ["", "out outs"] >> gvs[exit_result_def] >>
        Cases_on `outs` >> gvs[exit_result_def] >>
        Cases_on `FLOOKUP s.vs_allocas inst.inst_id` >> gvs[exit_result_def] >>
        rename1 `FLOOKUP s.vs_allocas inst.inst_id = SOME pair` >>
        PairCases_on `pair` >> gvs[exit_result_def])
    >~ [`inst.inst_opcode = BUMP`]
    >- (namedCases_on `inst.inst_operands` ["", "a ops"] >> gvs[exit_result_def] >>
        namedCases_on `ops` ["", "b ops2"] >> gvs[exit_result_def] >>
        Cases_on `ops2` >> gvs[exit_result_def] >>
        namedCases_on `inst.inst_outputs` ["", "out outs"] >> gvs[exit_result_def] >>
        namedCases_on `outs` ["", "out2 outs2"] >> gvs[exit_result_def] >>
        Cases_on `outs2` >> gvs[exit_result_def] >>
        Cases_on `eval_operand a s` >> gvs[exit_result_def] >>
        Cases_on `eval_operand b s` >> gvs[exit_result_def])
    >~ [`inst.inst_opcode = DJMP`]
    >- (namedCases_on `inst.inst_operands` ["", "a ops"] >> gvs[exit_result_def] >>
        Cases_on `eval_operand a s` >> gvs[exit_result_def] >>
        Cases_on `extract_labels ops` >> gvs[exit_result_def] >>
        qpat_x_assum `exit_result _` mp_tac >>
        IF_CASES_TAC >> simp[exit_result_def])
    >~ [`inst.inst_opcode = EXTCODECOPY`]
    >- (namedCases_on `inst.inst_operands` ["", "a ops"] >> gvs[exit_result_def] >>
        namedCases_on `ops` ["", "b ops2"] >> gvs[exit_result_def] >>
        namedCases_on `ops2` ["", "c ops3"] >> gvs[exit_result_def] >>
        namedCases_on `ops3` ["", "d ops4"] >> gvs[exit_result_def] >>
        Cases_on `ops4` >> gvs[exit_result_def] >>
        Cases_on `eval_operand a s` >> gvs[exit_result_def] >>
        Cases_on `eval_operand b s` >> gvs[exit_result_def] >>
        Cases_on `eval_operand c s` >> gvs[exit_result_def] >>
        Cases_on `eval_operand d s` >> gvs[exit_result_def])
    >~ [`inst.inst_opcode = ISTORE`]
    >- (namedCases_on `inst.inst_operands` ["", "a ops"] >> gvs[exit_result_def] >>
        namedCases_on `ops` ["", "b ops2"] >> gvs[exit_result_def] >>
        Cases_on `ops2` >> gvs[exit_result_def] >>
        Cases_on `eval_operand a s` >> gvs[exit_result_def] >>
        Cases_on `eval_operand b s` >> gvs[exit_result_def])
    >~ [`inst.inst_opcode = JMP`]
    >- (namedCases_on `inst.inst_operands` ["", "a ops"] >> gvs[exit_result_def] >>
        Cases_on `a` >> gvs[exit_result_def] >>
        Cases_on `ops` >> gvs[exit_result_def])
    >~ [`inst.inst_opcode = JNZ`]
    >- (namedCases_on `inst.inst_operands` ["", "a ops"] >> gvs[exit_result_def] >>
        namedCases_on `ops` ["", "b ops2"] >> gvs[exit_result_def] >>
        Cases_on `b` >> gvs[exit_result_def] >>
        namedCases_on `ops2` ["", "c ops3"] >> gvs[exit_result_def] >>
        Cases_on `c` >> gvs[exit_result_def] >>
        Cases_on `ops3` >> gvs[exit_result_def] >>
        Cases_on `eval_operand a s` >> gvs[exit_result_def] >>
        qpat_x_assum `exit_result _` mp_tac >>
        IF_CASES_TAC >> simp[exit_result_def]) >>
    namedCases_on `inst.inst_operands` ["", "a ops"] >> gvs[exit_result_def] >>
    namedCases_on `ops` ["", "b ops2"] >> gvs[exit_result_def] >>
    Cases_on `ops2` >> gvs[exit_result_def] >>
    Cases_on `eval_operand a s` >> gvs[exit_result_def] >>
    Cases_on `eval_operand b s` >> gvs[exit_result_def] >>
    namedCases_on `inst.inst_outputs` ["", "out outs"] >> gvs[exit_result_def] >>
    Cases_on `outs` >> gvs[exit_result_def]
QED

Theorem raw_eval_operand_control[local]:
  !op s b p. eval_operand op (s with <|vs_prev_bb := p; vs_current_bb := b|>) =
    eval_operand op s
Proof
  Cases >> simp[eval_operand_def, lookup_var_def]
QED

Theorem raw_eval_operands_control[local]:
  !ops s b p. eval_operands ops (s with <|vs_prev_bb := p; vs_current_bb := b|>) =
    eval_operands ops s
Proof
  Induct >> simp[eval_operands_def, raw_eval_operand_control]
QED

Theorem raw_mcopy_control[local]:
  mcopy dst src sz (s with <|vs_prev_bb := p; vs_current_bb := b|>) =
    mcopy dst src sz s with <|vs_prev_bb := p; vs_current_bb := b|>
Proof
  simp[mcopy_def, read_memory_def, write_memory_with_expansion_def]
QED

Theorem raw_pack_dret_control[local]:
  !pairs cursor s b p.
    pack_dret_dynamic cursor pairs (s with <|vs_prev_bb := p; vs_current_bb := b|>) =
    (FST (pack_dret_dynamic cursor pairs s),
     FST (SND (pack_dret_dynamic cursor pairs s)),
     SND (SND (pack_dret_dynamic cursor pairs s)) with
       <|vs_prev_bb := p; vs_current_bb := b|>)
Proof
  Induct >- simp[pack_dret_dynamic_def] >>
  rpt gen_tac >> PairCases_on `h` >>
  simp[pack_dret_dynamic_def, raw_mcopy_control] >>
  first_x_assum (fn th => rewrite_tac[th]) >>
  pairarg_tac >> simp[]
QED

Theorem raw_ext_call_not_exit[local]:
  !inst s gas addr value ao az ro rz is_static.
    ~exit_result (exec_ext_call inst s gas addr value ao az ro rz is_static)
Proof
  rpt gen_tac >> simp[exec_ext_call_def] >>
  namedCases_on `inst.inst_outputs` ["", "out outs"] >> simp[exit_result_def] >>
  Cases_on `outs` >> simp[exit_result_def]
QED

Theorem raw_delegatecall_not_exit[local]:
  !inst s gas addr ao az ro rz.
    ~exit_result (exec_delegatecall inst s gas addr ao az ro rz)
Proof
  rpt gen_tac >> simp[exec_delegatecall_def] >>
  BasicProvers.TOP_CASE_TAC >> simp[exit_result_def] >>
  rename1 `SOME pair` >> PairCases_on `pair` >> simp[] >>
  namedCases_on `inst.inst_outputs` ["", "out outs"] >> simp[exit_result_def] >>
  Cases_on `outs` >> simp[exit_result_def]
QED

Theorem raw_exit_control[local]:
  inst.inst_opcode <> INVOKE /\ step_inst_base inst s = r /\
  exit_result r /\ (!h. r <> Halt h) ==>
  step_inst_base inst (s with <|vs_current_bb := b; vs_prev_bb := p|>) =
    exec_result_map (\t. t with <|vs_current_bb := b; vs_prev_bb := p|>) r
Proof
  strip_tac >>
  `MEM inst.inst_opcode
      [INVOKE; STOP; RETURN; SINK; RET; RETFMP; DRET; REVERT;
       ASSERT; ASSERT_UNREACHABLE; RETURNDATACOPY; LOG; SELFDESTRUCT;
       INVALID; CALL; STATICCALL; DELEGATECALL; CREATE; CREATE2; SSTORE; TSTORE]` by
    metis_tac[step_inst_exit_opcodes] >>
  Cases_on `r` >> gvs[exit_result_def] >>
  fs[MEM] >> gvs[] >> first_assum raw_opcode_eq >>
  simp[raw_eval_operand_control, raw_eval_operands_control, instIdxIndepTheory.exec_result_map_def,
       halt_state_def, revert_state_def, set_returndata_def] >>
  gvs[AllCaseEqs()] >>~-
    ([`inst.inst_opcode = DRET`],
     qpat_x_assum `_ (pack_dret_dynamic _ _ _) = _` mp_tac >>
     pairarg_tac >> simp[] >> strip_tac >>
     simp[raw_pack_dret_control] >> gvs[]) >>
  simp[halt_state_def, revert_state_def, set_returndata_def] >>
  gvs[exec_create_abort_iff, exec_create_not_IntRet] >>
  all_tac >>~-
    ([`exec_ext_call _ _ _ _ _ _ _ _ _ _ = _`],
     metis_tac[raw_ext_call_not_exit, exit_result_def]) >>~-
    ([`exec_delegatecall _ _ _ _ _ _ _ _ = _`],
     metis_tac[raw_delegatecall_not_exit, exit_result_def]) >>
  simp[halt_state_def, set_returndata_def] >>
  metis_tac[exec_write2_not_exit, exit_result_def]
QED

Theorem frag_relabel_exit_edge_raw:
  cs_extends sa sb /\ sa.cs_blocks <> sb.cs_blocks /\ frag_ops_free sa sb /\
  fn_has_code sa sb fn /\ LENGTH ids = LENGTH sa.cs_current_insts /\
  L <> sb.cs_current_bb /\
  ~MEM L (MAP (\bb. bb.bb_label) (emitted_blocks sa sb)) /\
  (u.vs_current_bb,u.vs_inst_idx) IN
    frag_observer_region (start_relabel L ids sa) (start_swap sa L ids sb) /\
  (u.vs_current_bb,u.vs_inst_idx) <> frag_observer_cut sb /\
  frag_relabel_state L sa.cs_current_bb u v /\ ~u.vs_halted /\
  lookup_block u.vs_current_bb (frag_relabel_observer sa sb L ids fn id).fn_blocks = SOME bb /\
  get_instruction bb u.vs_inst_idx = SOME inst /\
  step_inst_base inst u = r /\ exit_result r /\ (!h. r <> Halt h) ==>
  ?b p. gas_path_edge ctx fn v 0
    (exec_result_map (\t. t with <|vs_current_bb := b; vs_prev_bb := p|>) r)
Proof
  strip_tac >> drule_all frag_relabel_off_cut_opcodes_raw >> strip_tac >>
  `(u.vs_current_bb = L ==> LENGTH sa.cs_current_insts <= u.vs_inst_idx)` by
    (fs[frag_observer_region_def, start_relabel_def] >> metis_tac[]) >>
  `?original. lookup_block
    (if u.vs_current_bb = L then sa.cs_current_bb else u.vs_current_bb)
      fn.fn_blocks = SOME original /\
    get_instruction original u.vs_inst_idx = SOME inst` by
    (drule_all frag_relabel_instruction_agrees >> simp[]) >>
  fs[frag_relabel_state_def] >> gvs[] >>
  qexistsl_tac [`if u.vs_current_bb = L then sa.cs_current_bb else u.vs_current_bb`, `p`] >>
  `step_inst_base inst (u with <|vs_current_bb :=
     (if u.vs_current_bb = L then sa.cs_current_bb else u.vs_current_bb);
     vs_prev_bb := p|>) = exec_result_map (\t. t with <|vs_current_bb :=
     (if u.vs_current_bb = L then sa.cs_current_bb else u.vs_current_bb);
     vs_prev_bb := p|>) (step_inst_base inst u)` by
    (irule raw_exit_control >> simp[]) >>
  gvs[] >> simp[gas_path_edge_def] >> qexists_tac `0` >>
  simp[step_inst_non_invoke, gas_count_step_def] >>
  Cases_on `step_inst_base inst u` >>
  gvs[exit_result_def, instIdxIndepTheory.exec_result_map_def]
QED

Theorem frag_relabel_exit_path_raw_aux[local]:
  cs_extends sa sb /\ sa.cs_blocks <> sb.cs_blocks /\ frag_ops_free sa sb /\
  fn_has_code sa sb fn /\ LENGTH ids = LENGTH sa.cs_current_insts /\
  L <> sb.cs_current_bb /\
  ~MEM L (MAP (\bb. bb.bb_label) (emitted_blocks sa sb)) /\
  EVERY (\i. ~MEM (Label L) i.inst_operands) (frag_code sa sb) ==>
  !fuel n u bb r v.
    (u.vs_current_bb,u.vs_inst_idx) IN
      frag_observer_region (start_relabel L ids sa) (start_swap sa L ids sb) /\
    ~u.vs_halted /\
    lookup_block u.vs_current_bb (frag_relabel_observer sa sb L ids fn id).fn_blocks = SOME bb /\
    LENGTH bb.bb_instructions - u.vs_inst_idx = n /\
    run_from fuel ctx (frag_relabel_observer sa sb L ids fn id) u = r /\
    exit_result r /\ (!h. r <> Halt h) /\
    frag_relabel_state L sa.cs_current_bb u v ==>
    ?b p. gas_path ctx fn v 0
      (exec_result_map (\t. t with <|vs_current_bb := b; vs_prev_bb := p|>) r)
Proof
  strip_tac >> completeInduct_on `fuel` >> completeInduct_on `n` >>
  rpt strip_tac >>
  Cases_on `(u.vs_current_bb,u.vs_inst_idx) = frag_observer_cut sb`
  >- (`lookup_block u.vs_current_bb (frag_relabel_observer sa sb L ids fn id).fn_blocks =
         SOME <|bb_label := sb.cs_current_bb;
                bb_instructions := sb.cs_current_insts ++ [mk_inst id STOP [] []]|>` by
        gvs[frag_observer_cut_def, frag_relabel_observer_cut] >>
      `get_instruction bb u.vs_inst_idx = SOME (mk_inst id STOP [] [])` by
        (gvs[frag_observer_cut_def] >> simp[frag_observer_cut_instruction]) >>
      `run_from fuel ctx (frag_relabel_observer sa sb L ids fn id) u = Halt (stop_view u)` by
        (rewrite_tac[stop_view_def] >> irule run_from_halt >>
         qexistsl_tac [`bb`, `mk_inst id STOP [] []`] >>
         simp[step_inst_base_opcode_eqs, mk_inst_def] >> gvs[mk_inst_def]) >>
      metis_tac[]) >>
  Cases_on `get_instruction bb u.vs_inst_idx`
  >- (qpat_x_assum `run_from fuel _ _ u = r` mp_tac >>
      simp[Once run_from_def, Once exec_block_def] >>
      strip_tac >> gvs[exit_result_def]) >>
  rename1 `get_instruction bb u.vs_inst_idx = SOME inst` >>
  `inst.inst_opcode <> INVOKE` by metis_tac[frag_relabel_off_cut_opcodes_raw] >>
  Cases_on `step_inst_base inst u` >>
  qpat_x_assum `run_from fuel ctx (frag_relabel_observer sa sb L ids fn id) u = _` mp_tac >>
  simp[Once run_from_def, Once exec_block_def, step_inst_non_invoke] >> strip_tac
  >- (rename1 `step_inst_base inst u = OK middle` >>
      `~middle.vs_halted` by metis_tac[step_inst_base_OK_preserves_halted] >>
      Cases_on `is_terminator inst.inst_opcode`
      >- suspend "jump" >> suspend "ordinary")
  >- suspend "abort"
  >- suspend "intret" >> metis_tac[exit_result_def]
QED

Resume frag_relabel_exit_path_raw_aux[abort]:
  gvs[] >>
  `?b p. gas_path_edge ctx fn v 0
    (exec_result_map (\t. t with <|vs_current_bb := b; vs_prev_bb := p|>)
      (step_inst_base inst u))` by
    (irule frag_relabel_exit_edge_raw >> simp[] >> metis_tac[]) >>
  qexistsl_tac [`b`, `p`] >> irule (cj 3 gas_path_rules) >>
  Cases_on `step_inst_base inst u` >>
  gvs[exit_result_def, instIdxIndepTheory.exec_result_map_def]
QED

Resume frag_relabel_exit_path_raw_aux[intret]:
  gvs[] >>
  `?b p. gas_path_edge ctx fn v 0
    (exec_result_map (\t. t with <|vs_current_bb := b; vs_prev_bb := p|>)
      (step_inst_base inst u))` by
    (irule frag_relabel_exit_edge_raw >> simp[] >> metis_tac[]) >>
  qexistsl_tac [`b`, `p`] >> irule (cj 3 gas_path_rules) >>
  Cases_on `step_inst_base inst u` >>
  gvs[exit_result_def, instIdxIndepTheory.exec_result_map_def]
QED

Resume frag_relabel_exit_path_raw_aux[ordinary]:
  `middle.vs_current_bb = u.vs_current_bb` by
    metis_tac[venomInstProofsTheory.step_preserves_control_flow, step_inst_non_invoke] >>
  `abi_observer_step ctx (frag_relabel_observer sa sb L ids fn id) (frag_observer_cut sb) u
     (middle with vs_inst_idx := SUC u.vs_inst_idx)` by
    (simp[abi_observer_step_def, step_inst_non_invoke] >> metis_tac[]) >>
  drule_all frag_relabel_step_edge_raw >> strip_tac >>
  `(u.vs_current_bb,SUC u.vs_inst_idx) IN
    frag_observer_region (start_relabel L ids sa) (start_swap sa L ids sb)` by
    (drule_all frag_relabel_region_closed_raw >>
     rewrite_tac[observer_region_closed_def] >> disch_then drule >> simp[]) >>
  qpat_x_assum `!m. m < n ==> _`
    (qspec_then `LENGTH bb.bb_instructions - SUC u.vs_inst_idx` mp_tac) >>
  impl_tac >- gvs[get_instruction_def] >>
  disch_then (qspecl_then
    [`middle with vs_inst_idx := SUC u.vs_inst_idx`, `bb`, `r`, `v'`] mp_tac) >>
  simp[] >> impl_tac >- (gvs[run_from_def] >> metis_tac[]) >>
  strip_tac >> qexistsl_tac [`b`, `p`] >>
  metis_tac[cj 2 gas_path_rules, ADD]
QED

Resume frag_relabel_exit_path_raw_aux[jump]:
  gs[] >> Cases_on `fuel`
  >- gvs[Once run_blocks_def, exit_result_def] >>
  rename1 `run_blocks (SUC remaining) ctx (frag_relabel_observer sa sb L ids fn id) middle = r` >>
  qpat_x_assum `run_blocks _ _ _ _ = _` mp_tac >>
  simp[Once run_blocks_def] >>
  Cases_on `lookup_block middle.vs_current_bb (frag_relabel_observer sa sb L ids fn id).fn_blocks` >>
  simp[] >- (strip_tac >> gvs[exit_result_def]) >>
  rename1 `lookup_block middle.vs_current_bb (frag_relabel_observer sa sb L ids fn id).fn_blocks = SOME target` >>
  qspecl_then [`middle`, `target.bb_instructions`]
    strip_assume_tac eval_phis_ok_or_error_defs >> simp[] >> strip_tac
  >- suspend "entered" >> metis_tac[exit_result_def]
QED

Resume frag_relabel_exit_path_raw_aux[entered]:
  rename1 `eval_phis middle target.bb_instructions = OK entered` >>
  `entered.vs_current_bb = middle.vs_current_bb /\ ~entered.vs_halted` by
    metis_tac[eval_phis_preserves_current_bb, eval_phis_preserves_halted] >>
  `abi_observer_step ctx (frag_relabel_observer sa sb L ids fn id) (frag_observer_cut sb) u
     (entered with vs_inst_idx := phi_prefix_length target.bb_instructions)` by
    (simp[abi_observer_step_def, step_inst_non_invoke] >>
     qexistsl_tac [`bb`, `inst`, `middle`] >> simp[] >> metis_tac[]) >>
  drule_all frag_relabel_step_edge_raw >> strip_tac >>
  `(middle.vs_current_bb,phi_prefix_length target.bb_instructions) IN
    frag_observer_region (start_relabel L ids sa) (start_swap sa L ids sb)` by
    (drule_all frag_relabel_region_closed_raw >>
     rewrite_tac[observer_region_closed_def] >> disch_then drule >> simp[]) >>
  qpat_x_assum `!m. m < SUC remaining ==> _`
    (qspec_then `remaining` mp_tac) >> simp[] >>
  disch_then (qspecl_then
    [`entered with vs_inst_idx := phi_prefix_length target.bb_instructions`,
     `target`, `v'`] mp_tac) >>
  simp[] >> impl_tac >- (gvs[run_from_def] >> metis_tac[]) >>
  strip_tac >>
  `run_from remaining ctx (frag_relabel_observer sa sb L ids fn id)
     (entered with vs_inst_idx := phi_prefix_length target.bb_instructions) = r` by
    simp[run_from_def] >>
  qpat_x_assum `gas_path _ _ v' _ _` mp_tac >> simp[] >> strip_tac >>
  qexistsl_tac [`b`, `p`] >>
  qpat_x_assum `!m. _` kall_tac >>
  metis_tac[cj 2 gas_path_rules, ADD]
QED

Finalise frag_relabel_exit_path_raw_aux

Theorem frag_relabel_exit_path_raw:
  cs_extends sa sb /\ sa.cs_blocks <> sb.cs_blocks /\ frag_ops_free sa sb /\
  fn_has_code sa sb fn /\ LENGTH ids = LENGTH sa.cs_current_insts /\
  L <> sb.cs_current_bb /\
  ~MEM L (MAP (\bb. bb.bb_label) (emitted_blocks sa sb)) /\
  EVERY (\i. ~MEM (Label L) i.inst_operands) (frag_code sa sb) /\
  (u.vs_current_bb,u.vs_inst_idx) IN
    frag_observer_region (start_relabel L ids sa) (start_swap sa L ids sb) /\
  ~u.vs_halted /\
  run_from fuel ctx (frag_relabel_observer sa sb L ids fn id) u = r /\
  exit_result r /\ (!h. r <> Halt h) /\
  frag_relabel_state L sa.cs_current_bb u v ==>
  ?b p. gas_path ctx fn v 0
    (exec_result_map (\t. t with <|vs_current_bb := b; vs_prev_bb := p|>) r)
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  Cases_on `lookup_block u.vs_current_bb (frag_relabel_observer sa sb L ids fn id).fn_blocks`
  >- gvs[Once run_from_def, exit_result_def] >>
  irule frag_relabel_exit_path_raw_aux >> metis_tac[]
QED

Theorem frag_exec_gas_path_relabel_raw:
  !ctx sa sb Q R fn s.
    (!L ids fn'.
       LENGTH ids = LENGTH sa.cs_current_insts /\
       fn_has_code (start_relabel L ids sa) (start_swap sa L ids sb) fn' /\
       fn_inst_ids_distinct fn' /\ fn'.fn_name = fn.fn_name /\
       (!i. MEM i (fn_insts fn') /\ i.inst_opcode <> STOP /\
            i.inst_opcode <> NOP ==> MEM i (fn_insts fn)) /\
       (!i. MEM i (fn_insts fn') ==> i.inst_opcode <> INVOKE) /\
       (sb.cs_current_insts <> [] \/
        !bb. lookup_block sb.cs_current_bb fn'.fn_blocks = SOME bb ==>
             phi_prefix_length bb.bb_instructions = 0) ==>
       (?t. Q t /\ ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
            t.vs_inst_idx = LENGTH sb.cs_current_insts /\
            !fuel r. run_from fuel ctx fn' t = r /\ (!e. r <> Error e) ==>
                     ?fuel'. run_from fuel' ctx fn' (s with vs_current_bb := L) = r) \/
       (?fuel r. run_from fuel ctx fn' (s with vs_current_bb := L) = r /\
                 exit_result r /\ R r)) /\
    sa.cs_blocks <> sb.cs_blocks /\ cs_extends sa sb /\ frag_ops_free sa sb /\
    ~MEM sb.cs_current_bb (MAP (\bb. bb.bb_label) (FRONT (emitted_blocks sa sb))) /\
    ALL_DISTINCT (MAP (\i. i.inst_id) (frag_code sa sb)) /\
    (!t rd. Q t ==> Q (t with vs_returndata := rd)) /\
    (!t p. Q t ==> Q (t with vs_prev_bb := p)) /\ (!h. ~R (Halt h)) /\
    (!a t b p. R (Abort a t) ==>
       R (Abort a (t with <| vs_current_bb := b; vs_prev_bb := p |>))) /\
    (!v t b p. R (IntRet v t) ==>
       R (IntRet v (t with <| vs_current_bb := b; vs_prev_bb := p |>))) /\
    fn_has_code sa sb fn /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    (?t. gas_marked_path F ctx fn s 0 (OK t) /\ Q t /\ ~t.vs_halted /\
         t.vs_current_bb = sb.cs_current_bb /\
         t.vs_inst_idx = LENGTH sb.cs_current_insts) \/
    (?r. gas_marked_path F ctx fn s 0 r /\ exit_result r /\ R r)
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_all frag_relabel_observer_exists >> strip_tac >>
  `(s with vs_current_bb := L).vs_inst_idx = LENGTH (start_relabel L ids sa).cs_current_insts` by
    simp[start_relabel_def] >>
  `( (s with vs_current_bb := L).vs_current_bb,
     (s with vs_current_bb := L).vs_inst_idx) IN
    frag_observer_region (start_relabel L ids sa) (start_swap sa L ids sb)` by
    (mp_tac (Q.INST [`sa` |-> `start_relabel L ids sa`,
       `sb` |-> `start_swap sa L ids sb`] frag_observer_start_region) >>
     simp[start_relabel_def, start_relabel_extends]) >>
  `frag_relabel_state L sa.cs_current_bb (s with vs_current_bb := L) s` by
    (irule frag_relabel_state_initial >> simp[]) >>
  `(frag_relabel_observer sa sb L ids fn id).fn_name = fn.fn_name` by
    simp[frag_relabel_observer_def] >>
  qpat_x_assum `!L ids fn'. _`
    (qspecl_then [`L`, `ids`, `frag_relabel_observer sa sb L ids fn id`] mp_tac) >>
  simp[] >> strip_tac
  >- suspend "normal" >> suspend "exit"
QED

Resume frag_exec_gas_path_relabel_raw[normal]:
  rename1 `Q t` >>
  `run_from 0 ctx (frag_relabel_observer sa sb L ids fn id) t = Halt (stop_view t)` by
    (irule run_from_stop_view >>
     qexistsl_tac [`<|bb_label := sb.cs_current_bb;
       bb_instructions := sb.cs_current_insts ++ [mk_inst id STOP [] []]|>`, `id`] >>
     simp[frag_relabel_observer_cut, frag_observer_cut_instruction]) >>
  `?fuel. run_from fuel ctx (frag_relabel_observer sa sb L ids fn id)
     (s with vs_current_bb := L) = Halt (stop_view t)` by
    (qpat_x_assum `!fuel. _` (qspec_then `0` mp_tac) >> simp[]) >>
  `?u. local_prefix ctx (frag_relabel_observer sa sb L ids fn id)
     (frag_observer_cut sb) (s with vs_current_bb := L) u /\ stop_view u = stop_view t` by
    (irule frag_relabel_halt_prefix_raw >>
     gvs[frag_observer_cut_def, stop_view_def, halt_state_def] >> metis_tac[]) >>
  `?v. gas_path ctx fn s 0 (OK v) /\ frag_relabel_state L sa.cs_current_bb u v` by
    (drule frag_relabel_prefix_path_raw >> disch_then irule >> simp[] >>
     qexistsl_tac [`id`, `ids`, `sb`] >> gvs[]) >>
  drule local_prefix_endpoint >> strip_tac >>
  `Q u` by (irule stop_view_closed_post >> metis_tac[]) >>
  `Q v` by (irule frag_relabel_state_post >> gvs[frag_observer_cut_def] >> metis_tac[]) >>
  drule frag_relabel_state_fields >> strip_tac >>
  disj1_tac >> qexists_tac `v` >>
  gvs[gas_marked_path_def, frag_observer_cut_def]
QED

Resume frag_exec_gas_path_relabel_raw[exit]:
  qmatch_asmsub_abbrev_tac `R r` >>
  `!h. r <> Halt h` by metis_tac[] >>
  `?b p. gas_path ctx fn s 0
    (exec_result_map (\t. t with <|vs_current_bb := b; vs_prev_bb := p|>) r)` by
    (irule frag_relabel_exit_path_raw >>
     simp[Abbr `r`] >>
     qpat_assum `frag_relabel_state _ _ _ _`
       (irule_at (Pat `frag_relabel_state _ _ _ _`)) >>
     qexistsl_tac [`sb`, `ids`, `id`, `fuel`] >> gvs[]) >>
  disj2_tac >>
  qexists_tac `exec_result_map (\t. t with <|vs_current_bb := b; vs_prev_bb := p|>) r` >>
  simp[gas_marked_path_def] >>
  Cases_on `r` >> gvs[exit_result_def, instIdxIndepTheory.exec_result_map_def] >>
  metis_tac[]
QED

Finalise frag_exec_gas_path_relabel_raw
