(* Memory checks for entry-edge relabelled external-call return fragments. *)
Theory extcallRelabelMemory
Ancestors
  exprSimAbiGasBridge exprSimAbiGasBridgeEdge fragGasPathMem instMemFrontier memSafeRun
  unitTransformDefs contextCodegenRel codegenRel venomExecSemantics
  venomState venomInst list fragGasPath abiEncoderObserver fragExec
  venomExecProofs venomInstProofs instIdxIndep

Theorem relabel_memory_checks_control[local]:
  inst.inst_opcode <> INVOKE ==>
  (mem_safe_step fuel ctx inst
     (s with <|vs_prev_bb := p; vs_current_bb := b|>) <=>
   mem_safe_step fuel ctx inst s)
Proof
  strip_tac >> simp[mem_safe_step_non_invoke,
    inst_mem_below_frontier_def, inst_dload_in_section_def,
    source_memory_read_ranges_def, source_memory_write_ranges_def,
    memory_range_of_operands_def, dret_memory_read_ranges_def,
    fixed_source_write_range_def, sized_source_write_range_def,
    frag_relabel_edge_operand_control, edge_eval_operands_control]
QED

Theorem frag_relabel_memory_check:
  frag_relabel_state L entry u v /\ inst.inst_opcode <> INVOKE /\
  mem_safe_step fuel ctx inst u ==>
  mem_safe_step fuel' ctx' inst v
Proof
  simp[frag_relabel_state_def] >> rpt strip_tac >> gvs[] >>
  simp[relabel_memory_checks_control] >>
  gvs[mem_safe_step_non_invoke]
QED

Theorem gas_edge_with_memory_check[local]:
  gas_path_edge ctx fn s n r /\
  (!bb inst. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
     get_instruction bb s.vs_inst_idx = SOME inst ==>
     inst.inst_opcode <> INVOKE /\ mem_safe_step 0 ctx inst s) ==>
  gas_path_mem_edge ctx fn s n r
Proof
  simp[gas_path_edge_def, gas_path_mem_edge_def] >> rpt strip_tac >>
  qexists_tac `fuel` >> goal_assum (drule_at Any) >>
  simp[] >> metis_tac[mem_safe_step_non_invoke]
QED

Theorem frag_relabel_mem_edge_step:
  frag_relabel_edge_context sa sb L ids fn /\
  (u.vs_current_bb,u.vs_inst_idx) IN
    frag_observer_region (start_relabel L ids sa) (start_swap sa L ids sb) /\
  frag_relabel_state L sa.cs_current_bb u v /\
  abi_observer_step ctx (frag_relabel_observer sa sb L ids fn id)
    (frag_observer_cut sb) u u' /\
  (!bb inst. lookup_block u.vs_current_bb
       (frag_relabel_observer sa sb L ids fn id).fn_blocks = SOME bb /\
     get_instruction bb u.vs_inst_idx = SOME inst ==>
     mem_safe_step 0 ctx inst u) ==>
  ?v'. gas_path_mem_edge ctx fn v 0 (OK v') /\
       frag_relabel_state L sa.cs_current_bb u' v'
Proof
  strip_tac >> drule_all frag_relabel_edge_step >> strip_tac >>
  qexists_tac `v'` >> simp[] >> irule gas_edge_with_memory_check >> simp[] >>
  qpat_x_assum `abi_observer_step _ _ _ _ _` mp_tac >>
  simp[abi_observer_step_def] >> strip_tac >>
  `inst.inst_opcode <> INVOKE` by
    metis_tac[frag_relabel_edge_off_cut_opcodes] >>
  `(u.vs_current_bb = L ==> LENGTH sa.cs_current_insts <= u.vs_inst_idx)` by
    (fs[frag_relabel_edge_context_def] >>
     metis_tac[frag_relabel_edge_region_entry_bound]) >>
  `?original. lookup_block
    (if u.vs_current_bb = L then sa.cs_current_bb else u.vs_current_bb)
      fn.fn_blocks = SOME original /\
    get_instruction original u.vs_inst_idx = SOME inst` by
    (fs[frag_relabel_edge_context_def] >>
     drule_all frag_relabel_instruction_agrees >> simp[]) >>
  qpat_assum `frag_relabel_state L sa.cs_current_bb u v`
    (mp_then Any strip_assume_tac frag_relabel_state_fields) >>
  rpt strip_tac >> gvs[] >> irule frag_relabel_memory_check >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem frag_relabel_mem_prefix_path:
  !ctx observed cut u t. local_prefix ctx observed cut u t ==>
  !sa sb L ids fn id v P.
    observed = frag_relabel_observer sa sb L ids fn id /\
    cut = frag_observer_cut sb /\
    frag_relabel_edge_context sa sb L ids fn /\
    (u.vs_current_bb,u.vs_inst_idx) IN
      frag_observer_region (start_relabel L ids sa) (start_swap sa L ids sb) /\
    frag_relabel_state L sa.cs_current_bb u v /\ P u /\
    (!x y. P x /\
      (x.vs_current_bb,x.vs_inst_idx) IN
        frag_observer_region (start_relabel L ids sa) (start_swap sa L ids sb) /\
      abi_observer_step ctx observed cut x y ==> P y) /\
    (!x bb inst. P x /\
      (x.vs_current_bb,x.vs_inst_idx) IN
        frag_observer_region (start_relabel L ids sa) (start_swap sa L ids sb) /\
      (x.vs_current_bb,x.vs_inst_idx) <> cut /\
      lookup_block x.vs_current_bb observed.fn_blocks = SOME bb /\
      get_instruction bb x.vs_inst_idx = SOME inst ==>
      mem_safe_step 0 ctx inst x) ==>
    ?t'. gas_path_mem ctx fn v 0 (OK t') /\
         frag_relabel_state L sa.cs_current_bb t t'
Proof
  ho_match_mp_tac local_prefix_ind >> conj_tac
  >- (rpt strip_tac >> qexists_tac `v` >> simp[] >>
      irule (cj 1 gas_path_mem_rules) >>
      drule frag_relabel_state_fields >> simp[]) >>
  rpt strip_tac >> gvs[] >>
  rename1 `abi_observer_step ctx _ _ u next` >>
  `(u.vs_current_bb,u.vs_inst_idx) <> frag_observer_cut sb` by
    metis_tac[abi_observer_step_def] >>
  `?v'. gas_path_mem_edge ctx fn v 0 (OK v') /\
    frag_relabel_state L sa.cs_current_bb next v'` by
    (irule frag_relabel_mem_edge_step >> simp[] >>
     goal_assum (drule_at Any) >> metis_tac[]) >>
  `observer_region_closed ctx (frag_relabel_observer sa sb L ids fn id)
    (frag_observer_cut sb)
    (frag_observer_region (start_relabel L ids sa) (start_swap sa L ids sb))` by
    (irule frag_relabel_edge_region_closed >> simp[]) >>
  `?t'. gas_path_mem ctx fn v' 0 (OK t') /\
    frag_relabel_state L sa.cs_current_bb t t'` by
    (first_x_assum irule >> simp[] >>
     qexistsl_tac [`P`, `id`, `ids`, `sb`] >> simp[] >>
     fs[observer_region_closed_def] >> metis_tac[]) >>
  qexists_tac `t'` >> simp[] >>
  metis_tac[cj 2 gas_path_mem_rules, arithmeticTheory.ADD]
QED

Theorem frag_relabel_mem_exit_edge[local]:
  frag_relabel_edge_context sa sb L ids fn /\
  (u.vs_current_bb,u.vs_inst_idx) IN
    frag_observer_region (start_relabel L ids sa) (start_swap sa L ids sb) /\
  (u.vs_current_bb,u.vs_inst_idx) <> frag_observer_cut sb /\
  frag_relabel_state L sa.cs_current_bb u v /\ ~u.vs_halted /\
  lookup_block u.vs_current_bb
    (frag_relabel_observer sa sb L ids fn id).fn_blocks = SOME bb /\
  get_instruction bb u.vs_inst_idx = SOME inst /\
  step_inst_base inst u = r /\ exit_result r /\ (!h. r <> Halt h) /\
  mem_safe_step 0 ctx inst u ==>
  ?b p. gas_path_mem_edge ctx fn v 0
    (exec_result_map (\t. t with <|vs_current_bb := b; vs_prev_bb := p|>) r)
Proof
  strip_tac >> drule_all frag_relabel_edge_exit_edge >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexistsl_tac [`b`, `p`] >> irule gas_edge_with_memory_check >> simp[] >>
  drule_all frag_relabel_edge_off_cut_opcodes >> strip_tac >>
  `(u.vs_current_bb = L ==> LENGTH sa.cs_current_insts <= u.vs_inst_idx)` by
    (fs[frag_relabel_edge_context_def] >>
     metis_tac[frag_relabel_edge_region_entry_bound]) >>
  `?original. lookup_block
    (if u.vs_current_bb = L then sa.cs_current_bb else u.vs_current_bb)
      fn.fn_blocks = SOME original /\
    get_instruction original u.vs_inst_idx = SOME inst` by
    (fs[frag_relabel_edge_context_def] >>
     drule_all frag_relabel_instruction_agrees >> simp[]) >>
  qpat_assum `frag_relabel_state L sa.cs_current_bb u v`
    (mp_then Any strip_assume_tac frag_relabel_state_fields) >>
  rpt strip_tac >> gvs[] >> irule frag_relabel_memory_check >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem frag_relabel_mem_exit_path_aux[local]:
  frag_relabel_edge_context sa sb L ids fn /\
  (!x y. P x /\
    (x.vs_current_bb,x.vs_inst_idx) IN
      frag_observer_region (start_relabel L ids sa) (start_swap sa L ids sb) /\
    abi_observer_step ctx (frag_relabel_observer sa sb L ids fn id)
      (frag_observer_cut sb) x y ==> P y) /\
  (!x bb inst. P x /\
    (x.vs_current_bb,x.vs_inst_idx) IN
      frag_observer_region (start_relabel L ids sa) (start_swap sa L ids sb) /\
    (x.vs_current_bb,x.vs_inst_idx) <> frag_observer_cut sb /\
    lookup_block x.vs_current_bb
      (frag_relabel_observer sa sb L ids fn id).fn_blocks = SOME bb /\
    get_instruction bb x.vs_inst_idx = SOME inst ==>
    mem_safe_step 0 ctx inst x) ==>
  !fuel n u bb r v.
    (u.vs_current_bb,u.vs_inst_idx) IN
      frag_observer_region (start_relabel L ids sa) (start_swap sa L ids sb) /\
    ~u.vs_halted /\ P u /\
    lookup_block u.vs_current_bb
      (frag_relabel_observer sa sb L ids fn id).fn_blocks = SOME bb /\
    LENGTH bb.bb_instructions - u.vs_inst_idx = n /\
    run_from fuel ctx (frag_relabel_observer sa sb L ids fn id) u = r /\
    exit_result r /\ (!h. r <> Halt h) /\
    frag_relabel_state L sa.cs_current_bb u v ==>
    ?b p. gas_path_mem ctx fn v 0
      (exec_result_map (\t. t with <|vs_current_bb := b; vs_prev_bb := p|>) r)
Proof
  strip_tac >> completeInduct_on `fuel` >> completeInduct_on `n` >>
  rpt strip_tac >>
  Cases_on `(u.vs_current_bb,u.vs_inst_idx) = frag_observer_cut sb`
  >- (`lookup_block u.vs_current_bb
         (frag_relabel_observer sa sb L ids fn id).fn_blocks =
         SOME <|bb_label := sb.cs_current_bb;
           bb_instructions := sb.cs_current_insts ++ [mk_inst id STOP [] []]|>` by
        gvs[frag_observer_cut_def, frag_relabel_observer_cut] >>
      `get_instruction bb u.vs_inst_idx = SOME (mk_inst id STOP [] [])` by
        (gvs[frag_observer_cut_def] >> simp[frag_observer_cut_instruction]) >>
      `run_from fuel ctx (frag_relabel_observer sa sb L ids fn id) u =
         Halt (stop_view u)` by
        (rewrite_tac[stop_view_def] >> irule run_from_halt >>
         qexistsl_tac [`bb`, `mk_inst id STOP [] []`] >>
         simp[step_inst_base_opcode_eqs, mk_inst_def] >> gvs[mk_inst_def]) >>
      metis_tac[]) >>
  Cases_on `get_instruction bb u.vs_inst_idx`
  >- (qpat_x_assum `run_from fuel _ _ u = r` mp_tac >>
      simp[Once run_from_def, Once exec_block_def] >>
      strip_tac >> gvs[exit_result_def]) >>
  rename1 `get_instruction bb u.vs_inst_idx = SOME inst` >>
  `inst.inst_opcode <> INVOKE` by metis_tac[frag_relabel_edge_off_cut_opcodes] >>
  `mem_safe_step 0 ctx inst u` by metis_tac[] >>
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

Resume frag_relabel_mem_exit_path_aux[abort]:
  gvs[] >> `mem_safe_step 0 ctx inst u` by metis_tac[] >>
  `?b p. gas_path_mem_edge ctx fn v 0
    (exec_result_map (\t. t with <|vs_current_bb := b; vs_prev_bb := p|>)
      (step_inst_base inst u))` by
    (irule frag_relabel_mem_exit_edge >> simp[] >> metis_tac[]) >>
  qexistsl_tac [`b`, `p`] >> irule (cj 3 gas_path_mem_rules) >>
  Cases_on `step_inst_base inst u` >>
  gvs[exit_result_def, instIdxIndepTheory.exec_result_map_def]
QED

Resume frag_relabel_mem_exit_path_aux[intret]:
  gvs[] >> `mem_safe_step 0 ctx inst u` by metis_tac[] >>
  `?b p. gas_path_mem_edge ctx fn v 0
    (exec_result_map (\t. t with <|vs_current_bb := b; vs_prev_bb := p|>)
      (step_inst_base inst u))` by
    (irule frag_relabel_mem_exit_edge >> simp[] >> metis_tac[]) >>
  qexistsl_tac [`b`, `p`] >> irule (cj 3 gas_path_mem_rules) >>
  Cases_on `step_inst_base inst u` >>
  gvs[exit_result_def, instIdxIndepTheory.exec_result_map_def]
QED

Resume frag_relabel_mem_exit_path_aux[ordinary]:
  `middle.vs_current_bb = u.vs_current_bb` by
    metis_tac[venomInstProofsTheory.step_preserves_control_flow, step_inst_non_invoke] >>
  `abi_observer_step ctx (frag_relabel_observer sa sb L ids fn id)
     (frag_observer_cut sb) u
     (middle with vs_inst_idx := SUC u.vs_inst_idx)` by
    (simp[abi_observer_step_def, step_inst_non_invoke] >> metis_tac[]) >>
  `?v'. gas_path_mem_edge ctx fn v 0 (OK v') /\
    frag_relabel_state L sa.cs_current_bb
      (middle with vs_inst_idx := SUC u.vs_inst_idx) v'` by
    (irule frag_relabel_mem_edge_step >> simp[] >>
     goal_assum (drule_at Any) >> metis_tac[]) >>
  `(u.vs_current_bb,SUC u.vs_inst_idx) IN
    frag_observer_region (start_relabel L ids sa) (start_swap sa L ids sb)` by
    (drule_all frag_relabel_edge_region_closed >>
     rewrite_tac[observer_region_closed_def] >> disch_then drule >> simp[]) >>
  `P (middle with vs_inst_idx := SUC u.vs_inst_idx)` by metis_tac[] >>
  qpat_x_assum `!m. m < n ==> _`
    (qspec_then `LENGTH bb.bb_instructions - SUC u.vs_inst_idx` mp_tac) >>
  impl_tac >- gvs[get_instruction_def] >>
  disch_then (qspecl_then
    [`middle with vs_inst_idx := SUC u.vs_inst_idx`, `bb`, `r`, `v'`] mp_tac) >>
  simp[] >> impl_tac >- (gvs[run_from_def] >> metis_tac[]) >>
  strip_tac >> qexistsl_tac [`b`, `p`] >>
  metis_tac[cj 2 gas_path_mem_rules, arithmeticTheory.ADD]
QED

Resume frag_relabel_mem_exit_path_aux[jump]:
  gs[] >> Cases_on `fuel`
  >- gvs[Once run_blocks_def, exit_result_def] >>
  rename1 `run_blocks (SUC remaining) ctx (frag_relabel_observer sa sb L ids fn id) middle = r` >>
  qpat_x_assum `run_blocks _ _ _ _ = _` mp_tac >> simp[Once run_blocks_def] >>
  Cases_on `lookup_block middle.vs_current_bb
    (frag_relabel_observer sa sb L ids fn id).fn_blocks` >>
  simp[] >- (strip_tac >> gvs[exit_result_def]) >>
  rename1 `lookup_block middle.vs_current_bb
    (frag_relabel_observer sa sb L ids fn id).fn_blocks = SOME target` >>
  qspecl_then [`middle`, `target.bb_instructions`]
    strip_assume_tac eval_phis_ok_or_error_defs >> simp[] >> strip_tac
  >- suspend "entered" >> metis_tac[exit_result_def]
QED

Resume frag_relabel_mem_exit_path_aux[entered]:
  rename1 `eval_phis middle target.bb_instructions = OK entered` >>
  `entered.vs_current_bb = middle.vs_current_bb /\ ~entered.vs_halted` by
    metis_tac[eval_phis_preserves_current_bb, eval_phis_preserves_halted] >>
  `abi_observer_step ctx (frag_relabel_observer sa sb L ids fn id)
    (frag_observer_cut sb) u
    (entered with vs_inst_idx := phi_prefix_length target.bb_instructions)` by
    (simp[abi_observer_step_def, step_inst_non_invoke] >>
     qexistsl_tac [`bb`, `inst`, `middle`] >> simp[] >> metis_tac[]) >>
  `?v'. gas_path_mem_edge ctx fn v 0 (OK v') /\
    frag_relabel_state L sa.cs_current_bb
      (entered with vs_inst_idx := phi_prefix_length target.bb_instructions) v'` by
    (irule frag_relabel_mem_edge_step >> simp[] >>
     goal_assum (drule_at Any) >> metis_tac[]) >>
  `(middle.vs_current_bb,phi_prefix_length target.bb_instructions) IN
    frag_observer_region (start_relabel L ids sa) (start_swap sa L ids sb)` by
    (drule_all frag_relabel_edge_region_closed >>
     rewrite_tac[observer_region_closed_def] >> disch_then drule >> simp[]) >>
  `P (entered with vs_inst_idx := phi_prefix_length target.bb_instructions)` by
    metis_tac[] >>
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
  qpat_x_assum `gas_path_mem _ _ v' _ _` mp_tac >> simp[] >> strip_tac >>
  qexistsl_tac [`b`, `p`] >> qpat_x_assum `!m. _` kall_tac >>
  metis_tac[cj 2 gas_path_mem_rules, arithmeticTheory.ADD]
QED

Finalise frag_relabel_mem_exit_path_aux

Theorem frag_relabel_mem_exit_path:
  frag_relabel_edge_context sa sb L ids fn /\
  (u.vs_current_bb,u.vs_inst_idx) IN
    frag_observer_region (start_relabel L ids sa) (start_swap sa L ids sb) /\
  ~u.vs_halted /\ P u /\
  run_from fuel ctx (frag_relabel_observer sa sb L ids fn id) u = r /\
  exit_result r /\ (!h. r <> Halt h) /\
  frag_relabel_state L sa.cs_current_bb u v /\
  (!x y. P x /\
    (x.vs_current_bb,x.vs_inst_idx) IN
      frag_observer_region (start_relabel L ids sa) (start_swap sa L ids sb) /\
    abi_observer_step ctx (frag_relabel_observer sa sb L ids fn id)
      (frag_observer_cut sb) x y ==> P y) /\
  (!x bb inst. P x /\
    (x.vs_current_bb,x.vs_inst_idx) IN
      frag_observer_region (start_relabel L ids sa) (start_swap sa L ids sb) /\
    (x.vs_current_bb,x.vs_inst_idx) <> frag_observer_cut sb /\
    lookup_block x.vs_current_bb
      (frag_relabel_observer sa sb L ids fn id).fn_blocks = SOME bb /\
    get_instruction bb x.vs_inst_idx = SOME inst ==>
    mem_safe_step 0 ctx inst x) ==>
  ?b p. gas_path_mem ctx fn v 0
    (exec_result_map (\t. t with <|vs_current_bb := b; vs_prev_bb := p|>) r)
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  Cases_on `lookup_block u.vs_current_bb
    (frag_relabel_observer sa sb L ids fn id).fn_blocks`
  >- gvs[Once run_from_def, exit_result_def] >>
  irule frag_relabel_mem_exit_path_aux >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem observer_step_memory_continuation[local]:
  abi_observer_step ctx observed cut u t /\
  (!fuel. mem_safe_run fuel ctx observed u) ==>
  !fuel. mem_safe_run fuel ctx observed t
Proof
  simp[abi_observer_step_def] >> rpt strip_tac
  >- (qpat_x_assum `!fuel. mem_safe_run _ _ _ _`
        (qspec_then `fuel` mp_tac) >>
      `step_inst fuel ctx inst u = OK middle` by
        metis_tac[step_inst_non_invoke] >>
      drule_all mem_safe_run_step >> simp[]) >>
  `step_inst (SUC fuel) ctx inst u = OK middle` by
    metis_tac[step_inst_non_invoke] >>
  `mem_safe_blocks (SUC fuel) ctx observed middle` by
    (metis_tac[mem_safe_run_terminator]) >>
  drule_all mem_safe_blocks_run >> metis_tac[]
QED

Theorem frag_relabel_mem_prefix_run:
  local_prefix ctx (frag_relabel_observer sa sb L ids fn id)
    (frag_observer_cut sb) u t /\
  frag_relabel_edge_context sa sb L ids fn /\
  (u.vs_current_bb,u.vs_inst_idx) IN
    frag_observer_region (start_relabel L ids sa) (start_swap sa L ids sb) /\
  frag_relabel_state L sa.cs_current_bb u v /\
  (!fuel. mem_safe_run fuel ctx (frag_relabel_observer sa sb L ids fn id) u) /\
  (!x bb inst.
    RTC (abi_observer_step ctx (frag_relabel_observer sa sb L ids fn id)
      (frag_observer_cut sb)) u x /\
    (x.vs_current_bb,x.vs_inst_idx) IN
      frag_observer_region (start_relabel L ids sa) (start_swap sa L ids sb) /\
    (x.vs_current_bb,x.vs_inst_idx) <> frag_observer_cut sb /\
    lookup_block x.vs_current_bb
      (frag_relabel_observer sa sb L ids fn id).fn_blocks = SOME bb /\
    get_instruction bb x.vs_inst_idx = SOME inst /\
    revert_forward_at bb x.vs_inst_idx ==> mem_safe_step 0 ctx inst x) ==>
  ?t'. gas_path_mem ctx fn v 0 (OK t') /\
    frag_relabel_state L sa.cs_current_bb t t'
Proof
  strip_tac >> drule frag_relabel_mem_prefix_path >>
  disch_then irule >> simp[] >>
  qexistsl_tac [`\x. RTC (abi_observer_step ctx
    (frag_relabel_observer sa sb L ids fn id) (frag_observer_cut sb)) u x /\
    (!fuel. mem_safe_run fuel ctx (frag_relabel_observer sa sb L ids fn id) x)`,
    `id`, `ids`, `sb`] >> simp[relationTheory.RTC_REFL] >>
  conj_tac
  >- (rpt strip_tac >>
      `mem_safe_run 0 ctx (frag_relabel_observer sa sb L ids fn id) x` by simp[] >>
      drule_all mem_safe_run_head >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >> conj_tac
  >- metis_tac[relationTheory.RTC_RULES_RIGHT1] >>
  metis_tac[observer_step_memory_continuation]
QED

Theorem frag_relabel_mem_exit_run:
  frag_relabel_edge_context sa sb L ids fn /\
  (u.vs_current_bb,u.vs_inst_idx) IN
    frag_observer_region (start_relabel L ids sa) (start_swap sa L ids sb) /\
  ~u.vs_halted /\
  run_from fuel ctx (frag_relabel_observer sa sb L ids fn id) u = r /\
  exit_result r /\ (!h. r <> Halt h) /\
  frag_relabel_state L sa.cs_current_bb u v /\
  (!fuel. mem_safe_run fuel ctx (frag_relabel_observer sa sb L ids fn id) u) /\
  (!x bb inst.
    RTC (abi_observer_step ctx (frag_relabel_observer sa sb L ids fn id)
      (frag_observer_cut sb)) u x /\
    (x.vs_current_bb,x.vs_inst_idx) IN
      frag_observer_region (start_relabel L ids sa) (start_swap sa L ids sb) /\
    (x.vs_current_bb,x.vs_inst_idx) <> frag_observer_cut sb /\
    lookup_block x.vs_current_bb
      (frag_relabel_observer sa sb L ids fn id).fn_blocks = SOME bb /\
    get_instruction bb x.vs_inst_idx = SOME inst /\
    revert_forward_at bb x.vs_inst_idx ==> mem_safe_step 0 ctx inst x) ==>
  ?b p. gas_path_mem ctx fn v 0
    (exec_result_map (\t. t with <|vs_current_bb := b; vs_prev_bb := p|>) r)
Proof
  strip_tac >> irule frag_relabel_mem_exit_path >> simp[] >>
  qexistsl_tac [`L`, `\x. RTC (abi_observer_step ctx
    (frag_relabel_observer sa sb L ids fn id) (frag_observer_cut sb)) u x /\
    (!fuel. mem_safe_run fuel ctx (frag_relabel_observer sa sb L ids fn id) x)`,
    `fuel`, `id`, `ids`, `sa`, `sb`, `u`] >>
  simp[relationTheory.RTC_REFL] >> conj_tac
  >- (rpt strip_tac >>
      `mem_safe_run 0 ctx (frag_relabel_observer sa sb L ids fn id) x` by simp[] >>
      drule_all mem_safe_run_head >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >> conj_tac
  >- metis_tac[relationTheory.RTC_RULES_RIGHT1] >>
  metis_tac[observer_step_memory_continuation]
QED
