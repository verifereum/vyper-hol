Theory exprSimAbiDecodeFreshTransfer
Ancestors
  exprSimAbiDecodeFreshBoundary exprSimAbiDecodeFreshControl exprSimAbiGasBridge
  fragExec fragGasPath gasCount abiEncoderObserver
  venomExecProofs venomInstProps venomInst venomExecSemantics venomState list
  instIdxIndep arithmetic

Theorem abi_decode_fresh_exit_edge:
  abi_decode_fresh_context sa sb L ids fn /\
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
  strip_tac >> drule_all abi_decode_fresh_off_cut_opcodes >> strip_tac >>
  `(u.vs_current_bb = L ==> LENGTH sa.cs_current_insts <= u.vs_inst_idx)` by
    (fs[abi_decode_fresh_context_def] >> metis_tac[abi_decode_fresh_region_entry_bound]) >>
  `?original. lookup_block
    (if u.vs_current_bb = L then sa.cs_current_bb else u.vs_current_bb)
      fn.fn_blocks = SOME original /\
    get_instruction original u.vs_inst_idx = SOME inst` by
    (fs[abi_decode_fresh_context_def] >> drule_all frag_relabel_instruction_agrees >> simp[]) >>
  fs[frag_relabel_state_def] >> gvs[] >>
  qexistsl_tac [`if u.vs_current_bb = L then sa.cs_current_bb else u.vs_current_bb`, `p`] >>
  `step_inst_base inst (u with <|vs_current_bb :=
     (if u.vs_current_bb = L then sa.cs_current_bb else u.vs_current_bb);
     vs_prev_bb := p|>) = exec_result_map (\t. t with <|vs_current_bb :=
     (if u.vs_current_bb = L then sa.cs_current_bb else u.vs_current_bb);
     vs_prev_bb := p|>) (step_inst_base inst u)` by
    (irule abi_decode_fresh_base_exit >> simp[]) >>
  gvs[] >> simp[gas_path_edge_def] >> qexists_tac `0` >>
  simp[step_inst_non_invoke, gas_count_step_def] >>
  Cases_on `step_inst_base inst u` >>
  gvs[exit_result_def, instIdxIndepTheory.exec_result_map_def]
QED

Theorem abi_decode_fresh_jump_result[local]:
  MEM inst.inst_opcode [JMP; JNZ; DJMP] /\ step_inst_base inst s = OK t ==>
  t = jump_to t.vs_current_bb s
Proof
  simp[MEM] >> strip_tac >>
  gvs[step_inst_base_opcode_eqs, AllCaseEqs(), jump_to_def]
QED

Theorem abi_decode_fresh_terminator_jump[local]:
  step_inst 0 ctx inst s = OK middle /\ ~middle.vs_halted /\
  is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
  inst.inst_opcode <> STOP /\ inst.inst_opcode <> RETURN ==>
  MEM inst.inst_opcode [JMP; JNZ; DJMP]
Proof
  strip_tac >> Cases_on `inst.inst_opcode` >> fs[is_terminator_def] >>
  gvs[step_inst_non_invoke, step_inst_base_opcode_eqs, AllCaseEqs()] >>
  pairarg_tac >> gvs[]
QED

Theorem abi_decode_fresh_step_edge:
  abi_decode_fresh_context sa sb L ids fn /\
  (u.vs_current_bb,u.vs_inst_idx) IN
    frag_observer_region (start_relabel L ids sa) (start_swap sa L ids sb) /\
  frag_relabel_state L sa.cs_current_bb u v /\
  abi_observer_step ctx (frag_relabel_observer sa sb L ids fn id)
    (frag_observer_cut sb) u u' ==>
  ?v'. gas_path_edge ctx fn v 0 (OK v') /\ frag_relabel_state L sa.cs_current_bb u' v'
Proof
  strip_tac >> fs[abi_observer_step_def] >>
  drule_all abi_decode_fresh_off_cut_opcodes >> strip_tac >>
  `(u.vs_current_bb = L ==> LENGTH sa.cs_current_insts <= u.vs_inst_idx)` by
    (fs[abi_decode_fresh_context_def] >> metis_tac[abi_decode_fresh_region_entry_bound]) >>
  `?original. lookup_block
    (if u.vs_current_bb = L then sa.cs_current_bb else u.vs_current_bb)
      fn.fn_blocks = SOME original /\ get_instruction original u.vs_inst_idx = SOME inst` by
    (fs[abi_decode_fresh_context_def] >> drule_all frag_relabel_instruction_agrees >> simp[]) >>
  `step_inst_base inst u = OK middle` by metis_tac[step_inst_non_invoke] >>
  drule frag_relabel_state_fields >> strip_tac
  >- (irule abi_decode_fresh_ordinary_edge >> goal_assum (drule_at Any) >> gvs[]) >>
  `MEM inst.inst_opcode [JMP; JNZ; DJMP]` by
    metis_tac[abi_decode_fresh_terminator_jump] >>
  `middle.vs_current_bb <> L` by
    (fs[abi_decode_fresh_context_def, EVERY_MEM] >>
     metis_tac[frag_relabel_jump_no_reentry, MEM]) >>
  Cases_on `middle.vs_current_bb = sb.cs_current_bb /\ sb.cs_current_insts = []`
  >- suspend "empty_cut" >>
  `?original_target. lookup_block middle.vs_current_bb fn.fn_blocks = SOME original_target /\
      phi_prefix_length original_target.bb_instructions = 0 /\
      phi_prefix_length target.bb_instructions = 0` by
    (fs[abi_decode_fresh_context_def] >> metis_tac[abi_decode_fresh_target_phis]) >>
  qpat_x_assum `eval_phis _ _ = _` mp_tac >>
  once_rewrite_tac[GSYM eval_phis_prefix] >> simp[eval_phis_def] >> strip_tac >> gvs[] >>
  fs[frag_relabel_state_def] >> gvs[] >>
  `step_inst_base inst (u with <|vs_current_bb :=
       (if u.vs_current_bb = L then sa.cs_current_bb else u.vs_current_bb);
       vs_prev_bb := p|>) =
    OK (entered with vs_prev_bb :=
       SOME (if u.vs_current_bb = L then sa.cs_current_bb else u.vs_current_bb))` by
    metis_tac[abi_decode_fresh_jump_control, MEM] >>
  qexists_tac `entered with <|vs_prev_bb :=
       SOME (if u.vs_current_bb = L then sa.cs_current_bb else u.vs_current_bb);
       vs_inst_idx := 0|>` >>
  gvs[] >> (conj_tac
  >- (simp[gas_path_edge_def] >> qexists_tac `0` >>
      simp[step_inst_non_invoke, gas_count_step_def] >> disj1_tac >>
      once_rewrite_tac[GSYM eval_phis_prefix] >> simp[eval_phis_def]) >>
  qexists_tac `SOME (if u.vs_current_bb = L then sa.cs_current_bb else u.vs_current_bb)` >>
  simp[venom_state_component_equality])
QED

Resume abi_decode_fresh_step_edge[empty_cut]:
  `!b p. step_inst_base inst (u with <|vs_current_bb := b; vs_prev_bb := p|>) =
    OK (middle with vs_prev_bb := SOME b)` by
    metis_tac[abi_decode_fresh_jump_control] >>
  `middle = jump_to sb.cs_current_bb u` by
    metis_tac[abi_decode_fresh_jump_result] >>
  `phi_prefix_length target.bb_instructions = 0` by
    (fs[abi_decode_fresh_context_def] >> metis_tac[abi_decode_fresh_empty_cut_phis]) >>
  qpat_x_assum `eval_phis _ _ = _` mp_tac >>
  once_rewrite_tac[GSYM eval_phis_prefix] >> simp[eval_phis_def] >> strip_tac >> gvs[] >>
  (`step_inst_base inst v = OK (jump_to sb.cs_current_bb v)` by
    (fs[frag_relabel_state_def] >>
     simp[jump_to_def, venom_state_component_equality]) >>
  qexists_tac `jump_to sb.cs_current_bb v` >>
  conj_tac
  >- (simp[gas_path_edge_def] >> qexists_tac `0` >>
      simp[step_inst_non_invoke, gas_count_step_def] >>
      metis_tac[]) >>
  gvs[frag_relabel_state_def, jump_to_def] >>
  simp[venom_state_component_equality])
QED
Finalise abi_decode_fresh_step_edge

Theorem abi_decode_fresh_empty_cut_step:
  abi_decode_fresh_context sa sb L ids fn /\
  (u.vs_current_bb,u.vs_inst_idx) IN
    frag_observer_region (start_relabel L ids sa) (start_swap sa L ids sb) /\
  frag_relabel_state L sa.cs_current_bb u v /\
  abi_observer_step ctx (frag_relabel_observer sa sb L ids fn id)
    (frag_observer_cut sb) u u' /\
  sb.cs_current_insts = [] /\ u'.vs_current_bb = sb.cs_current_bb ==>
  ?v'. gas_path_edge ctx fn v 0 (OK v') /\ frag_relabel_state L sa.cs_current_bb u' v'
Proof
  metis_tac[abi_decode_fresh_step_edge]
QED

Theorem abi_decode_fresh_prefix_path:
  !ctx observed cut u t. local_prefix ctx observed cut u t ==>
  !sa sb L ids fn id v.
    observed = frag_relabel_observer sa sb L ids fn id /\
    cut = frag_observer_cut sb /\
    abi_decode_fresh_context sa sb L ids fn /\
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
  drule_all abi_decode_fresh_step_edge >> strip_tac >>
  `observer_region_closed ctx (frag_relabel_observer sa sb L ids fn id)
    (frag_observer_cut sb)
    (frag_observer_region (start_relabel L ids sa) (start_swap sa L ids sb))` by
      (irule abi_decode_fresh_region_closed >> simp[]) >>
  `?t'. gas_path ctx fn v' 0 (OK t') /\
        frag_relabel_state L sa.cs_current_bb t t'` by
    (first_x_assum irule >> simp[] >>
     fs[observer_region_closed_def] >> metis_tac[]) >>
  qexists_tac `t'` >> simp[] >>
  metis_tac[cj 2 gas_path_rules, ADD]
QED

Theorem abi_decode_fresh_exit_path_aux[local]:
  abi_decode_fresh_context sa sb L ids fn ==>
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
  `inst.inst_opcode <> INVOKE` by metis_tac[abi_decode_fresh_off_cut_opcodes] >>
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

Resume abi_decode_fresh_exit_path_aux[abort]:
  gvs[] >>
  `?b p. gas_path_edge ctx fn v 0
    (exec_result_map (\t. t with <|vs_current_bb := b; vs_prev_bb := p|>)
      (step_inst_base inst u))` by
    (irule abi_decode_fresh_exit_edge >> simp[] >> metis_tac[]) >>
  qexistsl_tac [`b`, `p`] >> irule (cj 3 gas_path_rules) >>
  Cases_on `step_inst_base inst u` >>
  gvs[exit_result_def, instIdxIndepTheory.exec_result_map_def]
QED

Resume abi_decode_fresh_exit_path_aux[intret]:
  gvs[] >>
  `?b p. gas_path_edge ctx fn v 0
    (exec_result_map (\t. t with <|vs_current_bb := b; vs_prev_bb := p|>)
      (step_inst_base inst u))` by
    (irule abi_decode_fresh_exit_edge >> simp[] >> metis_tac[]) >>
  qexistsl_tac [`b`, `p`] >> irule (cj 3 gas_path_rules) >>
  Cases_on `step_inst_base inst u` >>
  gvs[exit_result_def, instIdxIndepTheory.exec_result_map_def]
QED

Resume abi_decode_fresh_exit_path_aux[ordinary]:
  `middle.vs_current_bb = u.vs_current_bb` by
    metis_tac[venomInstProofsTheory.step_preserves_control_flow, step_inst_non_invoke] >>
  `abi_observer_step ctx (frag_relabel_observer sa sb L ids fn id) (frag_observer_cut sb) u
     (middle with vs_inst_idx := SUC u.vs_inst_idx)` by
    (simp[abi_observer_step_def, step_inst_non_invoke] >> metis_tac[]) >>
  drule_all abi_decode_fresh_step_edge >> strip_tac >>
  `(u.vs_current_bb,SUC u.vs_inst_idx) IN
    frag_observer_region (start_relabel L ids sa) (start_swap sa L ids sb)` by
    (drule_all abi_decode_fresh_region_closed >>
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

Resume abi_decode_fresh_exit_path_aux[jump]:
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

Resume abi_decode_fresh_exit_path_aux[entered]:
  rename1 `eval_phis middle target.bb_instructions = OK entered` >>
  `entered.vs_current_bb = middle.vs_current_bb /\ ~entered.vs_halted` by
    metis_tac[eval_phis_preserves_current_bb, eval_phis_preserves_halted] >>
  `abi_observer_step ctx (frag_relabel_observer sa sb L ids fn id) (frag_observer_cut sb) u
     (entered with vs_inst_idx := phi_prefix_length target.bb_instructions)` by
    (simp[abi_observer_step_def, step_inst_non_invoke] >>
     qexistsl_tac [`bb`, `inst`, `middle`] >> simp[] >> metis_tac[]) >>
  drule_all abi_decode_fresh_step_edge >> strip_tac >>
  `(middle.vs_current_bb,phi_prefix_length target.bb_instructions) IN
    frag_observer_region (start_relabel L ids sa) (start_swap sa L ids sb)` by
    (drule_all abi_decode_fresh_region_closed >>
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

Finalise abi_decode_fresh_exit_path_aux

Theorem abi_decode_fresh_exit_path:
  abi_decode_fresh_context sa sb L ids fn /\
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
  irule abi_decode_fresh_exit_path_aux >> metis_tac[]
QED

Theorem abi_decode_fresh_cut_run_prefix_aux[local]:
  !fuel n s bb h.
    (!bb. lookup_block (FST cut) fn.fn_blocks = SOME bb ==>
      ?id. get_instruction bb (SND cut) = SOME (mk_inst id STOP [] [])) /\
    (!lbl idx bb inst. (lbl,idx) IN region /\ (lbl,idx) <> cut /\
      lookup_block lbl fn.fn_blocks = SOME bb /\
      get_instruction bb idx = SOME inst ==> inst.inst_opcode <> INVOKE) /\
    observer_region_closed ctx fn cut region /\
    (s.vs_current_bb,s.vs_inst_idx) IN region /\ ~s.vs_halted /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    LENGTH bb.bb_instructions - s.vs_inst_idx = n /\
    run_from fuel ctx fn s = Halt h /\
    (h.vs_current_bb,h.vs_inst_idx) = cut ==>
    ?u. local_prefix ctx fn cut s u /\ stop_view u = h
Proof
  completeInduct_on `fuel` >> completeInduct_on `n` >> rpt strip_tac >>
  Cases_on `(s.vs_current_bb,s.vs_inst_idx) = cut`
  >- (qexists_tac `s` >> conj_tac
      >- (irule (cj 1 local_prefix_rules) >> simp[]) >>
      `FST cut = s.vs_current_bb /\ SND cut = s.vs_inst_idx` by
        (Cases_on `cut` >> gvs[]) >>
      `?id. get_instruction bb s.vs_inst_idx = SOME (mk_inst id STOP [] [])` by
        metis_tac[] >>
      `run_from fuel ctx fn s = Halt (stop_view s)` by
        (rewrite_tac[stop_view_def] >> irule run_from_halt >>
         qexistsl_tac [`bb`, `mk_inst id STOP [] []`] >>
         simp[step_inst_base_opcode_eqs, mk_inst_def]) >> gvs[]) >>
  Cases_on `get_instruction bb s.vs_inst_idx`
  >- (qpat_x_assum `run_from fuel ctx fn s = _` mp_tac >>
      simp[Once run_from_def, Once exec_block_def]) >>
  rename1 `get_instruction bb s.vs_inst_idx = SOME inst` >>
  `inst.inst_opcode <> INVOKE` by metis_tac[] >>
  Cases_on `step_inst_base inst s` >>
  qpat_x_assum `run_from fuel ctx fn s = _` mp_tac >>
  simp[Once run_from_def, Once exec_block_def, step_inst_non_invoke] >>
  strip_tac >> gs[]
  >- (rename1 `step_inst_base inst s = OK middle` >>
      `~middle.vs_halted` by metis_tac[step_inst_base_OK_preserves_halted] >>
      Cases_on `is_terminator inst.inst_opcode`
      >- suspend "jump" >> suspend "ordinary") >>
  metis_tac[frag_halt_preserves_position]
QED

Resume abi_decode_fresh_cut_run_prefix_aux[ordinary]:
  `middle.vs_current_bb = s.vs_current_bb` by
    metis_tac[venomInstProofsTheory.step_preserves_control_flow, step_inst_non_invoke] >>
  `abi_observer_step ctx fn cut s
     (middle with vs_inst_idx := SUC s.vs_inst_idx)` by
    (simp[abi_observer_step_def, step_inst_non_invoke] >> metis_tac[]) >>
  qpat_assum `observer_region_closed ctx fn cut region`
    (mp_tac o REWRITE_RULE[observer_region_closed_def]) >>
  disch_then drule >> simp[] >> strip_tac >>
  qpat_x_assum `!m. m < n ==> _`
    (qspec_then `LENGTH bb.bb_instructions - SUC s.vs_inst_idx` mp_tac) >>
  impl_tac >- gvs[get_instruction_def] >>
  disch_then (qspecl_then
    [`middle with vs_inst_idx := SUC s.vs_inst_idx`, `bb`, `h`] mp_tac) >>
  simp[] >> impl_tac >- (gvs[run_from_def] >> metis_tac[]) >>
  strip_tac >> qexists_tac `u` >> simp[] >>
  irule (cj 2 local_prefix_rules) >>
  qexists_tac `middle with vs_inst_idx := SUC s.vs_inst_idx` >> simp[]
QED

Resume abi_decode_fresh_cut_run_prefix_aux[jump]:
  gs[] >> Cases_on `fuel`
  >- gvs[Once run_blocks_def] >>
  rename1 `run_blocks (SUC remaining) ctx fn middle = Halt h` >>
  qpat_x_assum `run_blocks _ _ _ _ = _` mp_tac >>
  simp[Once run_blocks_def] >>
  Cases_on `lookup_block middle.vs_current_bb fn.fn_blocks` >> simp[] >>
  rename1 `lookup_block middle.vs_current_bb fn.fn_blocks = SOME target` >>
  qspecl_then [`middle`, `target.bb_instructions`]
    strip_assume_tac eval_phis_ok_or_error_defs >> simp[] >> strip_tac >>
  rename1 `eval_phis middle target.bb_instructions = OK entered` >>
  `entered.vs_current_bb = middle.vs_current_bb /\ ~entered.vs_halted` by
    metis_tac[eval_phis_preserves_current_bb, eval_phis_preserves_halted] >>
  `abi_observer_step ctx fn cut s
     (entered with vs_inst_idx := phi_prefix_length target.bb_instructions)` by
    (simp[abi_observer_step_def, step_inst_non_invoke] >>
     qexistsl_tac [`bb`, `inst`, `middle`] >> simp[] >> metis_tac[]) >>
  qpat_assum `observer_region_closed ctx fn cut region`
    (mp_tac o REWRITE_RULE[observer_region_closed_def]) >>
  disch_then drule >> simp[] >> strip_tac >>
  qpat_x_assum `!m. m < SUC remaining ==> _`
    (qspec_then `remaining` mp_tac) >> simp[] >>
  disch_then (qspecl_then
    [`entered with vs_inst_idx := phi_prefix_length target.bb_instructions`,
     `target`, `h`] mp_tac) >>
  simp[] >> impl_tac >- (gvs[run_from_def] >> metis_tac[]) >>
  strip_tac >> qexists_tac `u` >> simp[] >>
  irule (cj 2 local_prefix_rules) >>
  qexists_tac `entered with vs_inst_idx := phi_prefix_length target.bb_instructions` >>
  simp[]
QED

Finalise abi_decode_fresh_cut_run_prefix_aux

Theorem abi_decode_fresh_halt_prefix:
  abi_decode_fresh_context sa sb L ids fn /\
  (s.vs_current_bb,s.vs_inst_idx) IN
    frag_observer_region (start_relabel L ids sa) (start_swap sa L ids sb) /\
  ~s.vs_halted /\
  run_from fuel ctx (frag_relabel_observer sa sb L ids fn id) s = Halt h /\
  (h.vs_current_bb,h.vs_inst_idx) = frag_observer_cut sb ==>
  ?u. local_prefix ctx (frag_relabel_observer sa sb L ids fn id)
       (frag_observer_cut sb) s u /\ stop_view u = h
Proof
  rpt strip_tac >>
  Cases_on `lookup_block s.vs_current_bb (frag_relabel_observer sa sb L ids fn id).fn_blocks`
  >- gvs[run_from_def] >>
  irule abi_decode_fresh_cut_run_prefix_aux >> simp[] >> conj_tac
  >- (simp[frag_observer_cut_def, frag_relabel_observer_cut] >>
      rpt strip_tac >> gvs[] >> metis_tac[frag_observer_cut_instruction]) >>
  conj_tac >- metis_tac[] >>
  qexists_tac `frag_observer_region (start_relabel L ids sa) (start_swap sa L ids sb)` >>
  simp[] >> conj_tac
  >- (rpt strip_tac >>
      mp_tac (Q.INST [`u` |-> `s with <|vs_current_bb := lbl; vs_inst_idx := idx|>`]
        (cj 2 abi_decode_fresh_off_cut_opcodes)) >> simp[]) >>
  metis_tac[abi_decode_fresh_region_closed]
QED
