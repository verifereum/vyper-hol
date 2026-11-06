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
