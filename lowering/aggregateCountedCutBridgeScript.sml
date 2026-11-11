Theory aggregateCountedCutBridge
Ancestors
  exprSimAbiGasBridge abiEncoderObserver fragGasPath gasCount
  venomExecSemantics venomExecProofs venomState venomInst emitHelper
  fragExec exprLoweringProps fragGasMode list rich_list compileEnv arithmetic

Theorem frag_observer_step_zero_edge_raw:
  cs_extends sa sb /\ fn_has_code sa sb fn /\ frag_gas_free sa sb /\
  (s.vs_current_bb,s.vs_inst_idx) IN frag_observer_region sa sb /\
  abi_observer_step ctx (frag_observer sa sb fn id) (frag_observer_cut sb) s t ==>
  gas_path_edge ctx fn s 0 (OK t)
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  Cases_on `sa.cs_blocks = sb.cs_blocks \/ sb.cs_current_insts <> [] \/
    !bb. lookup_block sb.cs_current_bb fn.fn_blocks = SOME bb ==>
         phi_prefix_length bb.bb_instructions = 0`
  >- (irule frag_observer_step_zero_edge >> metis_tac[]) >>
  gvs[] >>
  qpat_x_assum `abi_observer_step _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE[abi_observer_step_def]) >>
  drule_all frag_observer_instruction_agrees >> strip_tac >>
  drule_all frag_observer_off_cut_opcodes >> strip_tac
  >- (simp[gas_path_edge_def] >> qexists_tac `0` >>
      simp[gas_count_step_def] >> gvs[]) >>
  `middle = jump_to middle.vs_current_bb s` by
    (Cases_on `inst.inst_opcode` >> fs[is_terminator_def] >>
     gvs[step_inst_non_invoke, step_inst_base_opcode_eqs, AllCaseEqs(), jump_to_def] >>
     pairarg_tac >> gvs[]) >>
  qpat_assum `lookup_block middle.vs_current_bb _ = SOME target`
    (strip_assume_tac o MATCH_MP frag_observer_lookup_cases) >>
  gvs[]
  >- (gvs[eval_phis_def, phi_prefix_length_def, mk_inst_def, jump_to_def] >>
      simp[gas_path_edge_def] >> qexists_tac `0` >>
      simp[gas_count_step_def] >> disj2_tac >> disj1_tac >>
      qexists_tac `sb.cs_current_bb` >> simp[jump_to_def]) >>
  fs[fn_has_code_def] >>
  simp[gas_path_edge_def] >> qexists_tac `0` >>
  simp[gas_count_step_def] >> metis_tac[]
QED

Theorem frag_observer_prefix_zero_path_raw:
  !ctx observed cut s t. local_prefix ctx observed cut s t ==>
  !sa sb fn id.
  observed = frag_observer sa sb fn id /\ cut = frag_observer_cut sb /\
  cs_extends sa sb /\ fn_has_code sa sb fn /\ frag_gas_free sa sb /\
  (s.vs_current_bb,s.vs_inst_idx) IN frag_observer_region sa sb ==>
  gas_path ctx fn s 0 (OK t)
Proof
  ho_match_mp_tac local_prefix_ind >> conj_tac
  >- (rpt strip_tac >> irule (cj 1 gas_path_rules) >> simp[]) >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >> gvs[] >>
  rename1 `abi_observer_step ctx (frag_observer sa sb fn id) (frag_observer_cut sb) s middle` >>
  `gas_path_edge ctx fn s 0 (OK middle)` by
    (irule frag_observer_step_zero_edge_raw >> metis_tac[]) >>
  `gas_path ctx fn middle 0 (OK t)` by
    (first_x_assum irule >> simp[] >>
     metis_tac[observer_region_closed_def, frag_observer_region_closed]) >>
  metis_tac[cj 2 gas_path_rules, ADD]
QED

Theorem frag_observer_exit_path_raw_aux[local]:
  cs_extends sa sb /\ fn_has_code sa sb fn /\ frag_gas_free sa sb ==>
  !fuel n s bb r.
    (s.vs_current_bb,s.vs_inst_idx) IN frag_observer_region sa sb /\
    ~s.vs_halted /\
    lookup_block s.vs_current_bb (frag_observer sa sb fn id).fn_blocks = SOME bb /\
    LENGTH bb.bb_instructions - s.vs_inst_idx = n /\
    run_from fuel ctx (frag_observer sa sb fn id) s = r /\
    exit_result r /\ (!h. r <> Halt h) ==>
    gas_path ctx fn s 0 r
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  completeInduct_on `fuel` >> completeInduct_on `n` >> rpt strip_tac >>
  Cases_on `(s.vs_current_bb,s.vs_inst_idx) = frag_observer_cut sb`
  >- (`lookup_block s.vs_current_bb (frag_observer sa sb fn id).fn_blocks =
         SOME <|bb_label := sb.cs_current_bb;
                bb_instructions := sb.cs_current_insts ++ [mk_inst id STOP [] []]|>` by
        (gvs[frag_observer_cut_def, frag_observer_cut_lookup]) >>
      `get_instruction bb s.vs_inst_idx = SOME (mk_inst id STOP [] [])` by
        (gvs[frag_observer_cut_def] >> simp[frag_observer_cut_instruction]) >>
      `run_from fuel ctx (frag_observer sa sb fn id) s = Halt (stop_view s)` by
        (rewrite_tac[stop_view_def] >> irule run_from_halt >>
         qexistsl_tac [`bb`, `mk_inst id STOP [] []`] >>
         simp[step_inst_base_opcode_eqs, mk_inst_def] >>
         gvs[mk_inst_def]) >> metis_tac[]) >>
  Cases_on `get_instruction bb s.vs_inst_idx`
  >- (qpat_x_assum `run_from fuel _ _ s = r` mp_tac >>
      simp[Once run_from_def, Once exec_block_def] >>
      strip_tac >> gvs[exit_result_def]) >>
  rename1 `get_instruction bb s.vs_inst_idx = SOME inst` >>
  `inst.inst_opcode <> INVOKE` by metis_tac[frag_observer_off_cut_opcodes] >>
  Cases_on `step_inst_base inst s` >>
  qpat_x_assum `run_from fuel ctx (frag_observer sa sb fn id) s = _` mp_tac >>
  simp[Once run_from_def, Once exec_block_def, step_inst_non_invoke] >>
  strip_tac
  >- (rename1 `step_inst_base inst s = OK middle` >>
      `~middle.vs_halted` by metis_tac[step_inst_base_OK_preserves_halted] >>
      Cases_on `is_terminator inst.inst_opcode`
      >- suspend "jump" >> suspend "ordinary")
  >- suspend "abort"
  >- suspend "intret" >>
  metis_tac[exit_result_def]
QED

Resume frag_observer_exit_path_raw_aux[abort]:
  irule (cj 3 gas_path_rules) >> simp[] >>
  metis_tac[frag_observer_exit_zero_edge]
QED

Resume frag_observer_exit_path_raw_aux[intret]:
  irule (cj 3 gas_path_rules) >> simp[] >>
  metis_tac[frag_observer_exit_zero_edge]
QED

Resume frag_observer_exit_path_raw_aux[ordinary]:
  `middle.vs_current_bb = s.vs_current_bb` by
    metis_tac[venomInstProofsTheory.step_preserves_control_flow, step_inst_non_invoke] >>
  `abi_observer_step ctx (frag_observer sa sb fn id) (frag_observer_cut sb) s
     (middle with vs_inst_idx := SUC s.vs_inst_idx)` by
    (simp[abi_observer_step_def, step_inst_non_invoke] >> metis_tac[]) >>
  `gas_path_edge ctx fn s 0 (OK (middle with vs_inst_idx := SUC s.vs_inst_idx))` by
    (irule frag_observer_step_zero_edge_raw >> metis_tac[]) >>
  `(s.vs_current_bb,SUC s.vs_inst_idx) IN frag_observer_region sa sb` by
    (drule_all frag_observer_region_closed >>
     rewrite_tac[observer_region_closed_def] >> disch_then drule >> simp[]) >>
  qpat_x_assum `!m. m < n ==> _`
    (qspec_then `LENGTH bb.bb_instructions - SUC s.vs_inst_idx` mp_tac) >>
  impl_tac >- gvs[get_instruction_def] >>
  disch_then (qspecl_then
    [`middle with vs_inst_idx := SUC s.vs_inst_idx`, `bb`, `r`] mp_tac) >>
  simp[] >> impl_tac >- (gvs[run_from_def] >> metis_tac[]) >>
  metis_tac[gas_path_rules, ADD]
QED

Resume frag_observer_exit_path_raw_aux[jump]:
  gs[] >> Cases_on `fuel`
  >- gvs[Once run_blocks_def, exit_result_def] >>
  rename1 `run_blocks (SUC remaining) ctx (frag_observer sa sb fn id) middle = r` >>
  qpat_x_assum `run_blocks _ _ _ _ = _` mp_tac >>
  simp[Once run_blocks_def] >>
  Cases_on `lookup_block middle.vs_current_bb (frag_observer sa sb fn id).fn_blocks` >>
  simp[] >- (strip_tac >> gvs[exit_result_def]) >>
  rename1 `lookup_block middle.vs_current_bb (frag_observer sa sb fn id).fn_blocks = SOME target` >>
  qspecl_then [`middle`, `target.bb_instructions`]
    strip_assume_tac eval_phis_ok_or_error_defs >> simp[] >> strip_tac
  >- suspend "entered" >> metis_tac[exit_result_def]
QED

Resume frag_observer_exit_path_raw_aux[entered]:
  rename1 `eval_phis middle target.bb_instructions = OK entered` >>
  `entered.vs_current_bb = middle.vs_current_bb /\ ~entered.vs_halted` by
    metis_tac[eval_phis_preserves_current_bb, eval_phis_preserves_halted] >>
  `abi_observer_step ctx (frag_observer sa sb fn id) (frag_observer_cut sb) s
     (entered with vs_inst_idx := phi_prefix_length target.bb_instructions)` by
    (simp[abi_observer_step_def, step_inst_non_invoke] >>
     qexistsl_tac [`bb`, `inst`, `middle`] >> simp[] >> metis_tac[]) >>
  `gas_path_edge ctx fn s 0
     (OK (entered with vs_inst_idx := phi_prefix_length target.bb_instructions))` by
    (irule frag_observer_step_zero_edge_raw >> metis_tac[]) >>
  `(middle.vs_current_bb,phi_prefix_length target.bb_instructions) IN
     frag_observer_region sa sb` by
    (drule_all frag_observer_region_closed >>
     rewrite_tac[observer_region_closed_def] >> disch_then drule >> simp[]) >>
  qpat_x_assum `!m. m < SUC remaining ==> _`
    (qspec_then `remaining` mp_tac) >> simp[] >>
  disch_then (qspecl_then
    [`entered with vs_inst_idx := phi_prefix_length target.bb_instructions`, `target`] mp_tac) >>
  simp[] >> impl_tac >- (gvs[run_from_def] >> metis_tac[]) >>
  `run_from remaining ctx (frag_observer sa sb fn id)
     (entered with vs_inst_idx := phi_prefix_length target.bb_instructions) = r` by
    simp[run_from_def] >>
  simp[] >> strip_tac >> qpat_x_assum `!m. _` kall_tac >>
  metis_tac[cj 2 gas_path_rules, ADD]
QED

Finalise frag_observer_exit_path_raw_aux

Theorem frag_observer_exit_path_raw:
  cs_extends sa sb /\ fn_has_code sa sb fn /\ frag_gas_free sa sb /\
  (s.vs_current_bb,s.vs_inst_idx) IN frag_observer_region sa sb /\
  ~s.vs_halted /\
  run_from fuel ctx (frag_observer sa sb fn id) s = r /\
  exit_result r /\ (!h. r <> Halt h) ==>
  gas_path ctx fn s 0 r
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  Cases_on `lookup_block s.vs_current_bb (frag_observer sa sb fn id).fn_blocks`
  >- (gvs[Once run_from_def, exit_result_def]) >>
  irule frag_observer_exit_path_raw_aux >> metis_tac[]
QED

Theorem frag_exec_gas_path_raw:
  !ctx sa sb P Q R fn s.
    frag_exec ctx sa sb P Q R /\ cs_extends sa sb /\ frag_gas_free sa sb /\
    (!t rd. Q t ==> Q (t with vs_returndata := rd)) /\ (!h. ~R (Halt h)) /\
    fn_has_code sa sb fn /\
    P s /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    (?t. gas_marked_path F ctx fn s 0 (OK t) /\ Q t /\ ~t.vs_halted /\
         t.vs_current_bb = sb.cs_current_bb /\
         t.vs_inst_idx = LENGTH sb.cs_current_insts) \/
    (?r. gas_marked_path F ctx fn s 0 r /\ exit_result r /\ R r)
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `fn_has_code sa sb (frag_observer sa sb fn 0)` by
    metis_tac[frag_observer_has_code] >>
  `(s.vs_current_bb,s.vs_inst_idx) IN frag_observer_region sa sb` by
    metis_tac[frag_observer_start_region] >>
  qpat_x_assum `frag_exec _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE[frag_exec_def]) >>
  disch_then (qspecl_then [`frag_observer sa sb fn 0`, `s`] mp_tac) >>
  simp[] >> strip_tac
  >- suspend "normal" >> suspend "exit"
QED

Resume frag_exec_gas_path_raw[normal]:
  rename1 `Q t` >>
  `run_from 0 ctx (frag_observer sa sb fn 0) t = Halt (stop_view t)` by
    (irule run_from_stop_view >>
     qexistsl_tac [`<|bb_label := sb.cs_current_bb;
       bb_instructions := sb.cs_current_insts ++ [mk_inst 0 STOP [] []]|>`, `0`] >>
     simp[frag_observer_cut_lookup, frag_observer_cut_instruction]) >>
  `?fuel. run_from fuel ctx (frag_observer sa sb fn 0) s = Halt (stop_view t)` by
    (qpat_x_assum `!fuel. _` (qspec_then `0` mp_tac) >> simp[]) >>
  `(stop_view t).vs_current_bb = sb.cs_current_bb /\
   (stop_view t).vs_inst_idx = LENGTH sb.cs_current_insts` by
    simp[stop_view_def, halt_state_def] >>
  `?u. local_prefix ctx (frag_observer sa sb fn 0) (frag_observer_cut sb) s u /\
       stop_view u = stop_view t` by
    (irule frag_observer_halt_cut_prefix >> simp[frag_observer_cut_def] >>
     metis_tac[]) >>
  `gas_path ctx fn s 0 (OK u)` by
    (drule frag_observer_prefix_zero_path_raw >> simp[] >>
     disch_then irule >> metis_tac[]) >>
  drule local_prefix_endpoint >> strip_tac >>
  disj1_tac >> qexists_tac `u` >>
  simp[gas_marked_path_def] >>
  `Q u` by (irule stop_view_closed_post >> metis_tac[]) >>
  gvs[frag_observer_cut_def]
QED

Resume frag_exec_gas_path_raw[exit]:
  disj2_tac >> qexists_tac `run_from fuel ctx (frag_observer sa sb fn 0) s` >>
  simp[gas_marked_path_def] >>
  irule frag_observer_exit_path_raw >> metis_tac[]
QED

Finalise frag_exec_gas_path_raw
