Theory aggregateCountedStraightExec
Ancestors
  aggregateCountedStraightStore aggregateCountedCutBridge abiEncoderObserver
  exprSimAbiGasBridge venomExecProofs venomInstProofs fragGasPath gasCount
  fragGasMode venomExecSemantics venomState venomInst list rich_list
  emitHelper exprLoweringProps fragExec compileEnv arithmetic

Theorem same_block_observer_instruction:
  cs_extends sa sb /\ sa.cs_blocks = sb.cs_blocks /\ fn_has_code sa sb fn /\
  (lbl,idx) IN frag_observer_region sa sb /\
  (lbl,idx) <> frag_observer_cut sb /\
  lookup_block lbl (frag_observer sa sb fn id).fn_blocks = SOME bb /\
  get_instruction bb idx = SOME inst ==>
  MEM inst (frag_code sa sb) /\
  ?original. lookup_block lbl fn.fn_blocks = SOME original /\
             get_instruction original idx = SOME inst
Proof
  strip_tac >>
  drule frag_extends_emitted_shape >> simp[emitted_blocks_def] >> strip_tac >>
  gvs[frag_observer_region_def, emitted_blocks_def] >>
  gvs[frag_observer_cut_lookup, frag_observer_cut_def] >>
  `idx < LENGTH sb.cs_current_insts` by
    (fs[get_instruction_def] >> decide_tac) >>
  conj_tac
  >- (simp[frag_code_def, emitted_blocks_def, emitted_insts_def] >>
      simp[MEM_EL] >> qexists_tac `idx - LENGTH sa.cs_current_insts` >>
      fs[get_instruction_def, EL_APPEND_EQN, EL_DROP]) >>
  fs[fn_has_code_def, IS_PREFIX_APPEND, get_instruction_def, EL_APPEND_EQN] >>
  gvs[EL_APPEND_EQN]
QED

Theorem same_block_observer_opcodes:
  cs_extends sa sb /\ sa.cs_blocks = sb.cs_blocks /\ fn_has_code sa sb fn /\
  frag_ops_free sa sb /\
  EVERY (\i. ~is_terminator i.inst_opcode) (frag_code sa sb) /\
  (lbl,idx) IN frag_observer_region sa sb /\
  (lbl,idx) <> frag_observer_cut sb /\
  lookup_block lbl (frag_observer sa sb fn id).fn_blocks = SOME bb /\
  get_instruction bb idx = SOME inst ==>
  inst.inst_opcode <> GAS /\ inst.inst_opcode <> INVOKE /\
  inst.inst_opcode <> PHI /\ inst.inst_opcode <> STOP /\
  inst.inst_opcode <> RETURN /\ ~is_terminator inst.inst_opcode
Proof
  strip_tac >> drule_all same_block_observer_instruction >> strip_tac >>
  fs[frag_ops_free_def, EVERY_MEM] >> metis_tac[]
QED

Theorem same_block_observer_closed:
  cs_extends sa sb /\ sa.cs_blocks = sb.cs_blocks /\ fn_has_code sa sb fn /\
  frag_ops_free sa sb /\
  EVERY (\i. ~is_terminator i.inst_opcode) (frag_code sa sb) ==>
  observer_region_closed ctx (frag_observer sa sb fn id)
    (frag_observer_cut sb) (frag_observer_region sa sb)
Proof
  strip_tac >> rw[observer_region_closed_def] >>
  fs[abi_observer_step_def] >>
  drule_all same_block_observer_opcodes >> strip_tac >>
  drule_all step_preserves_control_flow >> strip_tac >>
  gvs[frag_observer_region_def] >> metis_tac[LESS_EQ_SUC_REFL, LESS_EQ_TRANS]
QED


Theorem same_block_observer_zero_edge:
  cs_extends sa sb /\ sa.cs_blocks = sb.cs_blocks /\ fn_has_code sa sb fn /\
  frag_ops_free sa sb /\
  EVERY (\i. ~is_terminator i.inst_opcode) (frag_code sa sb) /\
  (s.vs_current_bb,s.vs_inst_idx) IN frag_observer_region sa sb /\
  abi_observer_step ctx (frag_observer sa sb fn id) (frag_observer_cut sb) s t ==>
  gas_path_edge ctx fn s 0 (OK t)
Proof
  strip_tac >> fs[abi_observer_step_def] >>
  drule_all same_block_observer_opcodes >> strip_tac >>
  drule_all same_block_observer_instruction >> strip_tac >>
  simp[gas_path_edge_def] >> qexists_tac `0` >>
  simp[gas_count_step_def] >> gvs[]
QED

Theorem same_block_halt_prefix_aux[local]:
  cs_extends sa sb /\ sa.cs_blocks = sb.cs_blocks /\ fn_has_code sa sb fn /\
  frag_ops_free sa sb /\
  EVERY (\i. ~is_terminator i.inst_opcode) (frag_code sa sb) ==>
  !n s bb fuel h.
    (s.vs_current_bb,s.vs_inst_idx) IN frag_observer_region sa sb /\
    ~s.vs_halted /\
    lookup_block s.vs_current_bb (frag_observer sa sb fn id).fn_blocks = SOME bb /\
    LENGTH bb.bb_instructions - s.vs_inst_idx = n /\
    run_from fuel ctx (frag_observer sa sb fn id) s = Halt h /\
    (h.vs_current_bb,h.vs_inst_idx) = frag_observer_cut sb ==>
    ?u. local_prefix ctx (frag_observer sa sb fn id) (frag_observer_cut sb) s u /\
        stop_view u = h
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  completeInduct_on `n` >> rpt strip_tac >>
  Cases_on `(s.vs_current_bb,s.vs_inst_idx) = frag_observer_cut sb`
  >- (qexists_tac `s` >> conj_tac
      >- (irule (cj 1 local_prefix_rules) >> simp[]) >>
      `get_instruction bb s.vs_inst_idx = SOME (mk_inst id STOP [] [])` by
        (gvs[frag_observer_cut_def, frag_observer_cut_lookup] >>
         simp[frag_observer_cut_instruction]) >>
      `run_from fuel ctx (frag_observer sa sb fn id) s = Halt (stop_view s)` by
        (rewrite_tac[stop_view_def] >> irule run_from_halt >>
         qexistsl_tac [`bb`, `mk_inst id STOP [] []`] >>
         simp[step_inst_base_opcode_eqs, mk_inst_def]) >> gvs[]) >>
  Cases_on `get_instruction bb s.vs_inst_idx`
  >- (qpat_x_assum `run_from fuel _ _ s = _` mp_tac >>
      simp[Once run_from_def, Once exec_block_def]) >>
  rename1 `get_instruction bb s.vs_inst_idx = SOME inst` >>
  drule_all same_block_observer_opcodes >> strip_tac >>
  Cases_on `step_inst_base inst s` >>
  qpat_x_assum `run_from fuel ctx (frag_observer sa sb fn id) s = _` mp_tac >>
  simp[Once run_from_def, Once exec_block_def, step_inst_non_invoke] >>
  strip_tac >> gs[]
  >- suspend "ordinary" >>
  metis_tac[frag_halt_preserves_position]
QED

Resume same_block_halt_prefix_aux[ordinary]:
  rename1 `step_inst_base inst s = OK middle` >>
  `~middle.vs_halted` by metis_tac[step_inst_base_OK_preserves_halted] >>
  `middle.vs_current_bb = s.vs_current_bb` by
    metis_tac[step_preserves_control_flow, step_inst_non_invoke] >>
  `abi_observer_step ctx (frag_observer sa sb fn id) (frag_observer_cut sb) s
     (middle with vs_inst_idx := SUC s.vs_inst_idx)` by
    (simp[abi_observer_step_def, step_inst_non_invoke] >> metis_tac[]) >>
  `(s.vs_current_bb,SUC s.vs_inst_idx) IN frag_observer_region sa sb` by
    (drule_all same_block_observer_closed >>
     rewrite_tac[observer_region_closed_def] >> disch_then drule >> simp[]) >>
  qpat_x_assum `!m. m < n ==> _`
    (qspec_then `LENGTH bb.bb_instructions - SUC s.vs_inst_idx` mp_tac) >>
  impl_tac >- gvs[get_instruction_def] >>
  disch_then (qspecl_then
    [`middle with vs_inst_idx := SUC s.vs_inst_idx`, `bb`, `fuel`, `h`] mp_tac) >>
  simp[] >> impl_tac >- (gvs[run_from_def] >> metis_tac[]) >>
  strip_tac >> qexists_tac `u` >> simp[] >>
  irule (cj 2 local_prefix_rules) >>
  qexists_tac `middle with vs_inst_idx := SUC s.vs_inst_idx` >> simp[]
QED

Finalise same_block_halt_prefix_aux

Theorem same_block_observer_halt_cut_prefix:
  cs_extends sa sb /\ sa.cs_blocks = sb.cs_blocks /\ fn_has_code sa sb fn /\
  frag_ops_free sa sb /\
  EVERY (\i. ~is_terminator i.inst_opcode) (frag_code sa sb) /\
  (s.vs_current_bb,s.vs_inst_idx) IN frag_observer_region sa sb /\
  ~s.vs_halted /\ run_from fuel ctx (frag_observer sa sb fn id) s = Halt h /\
  (h.vs_current_bb,h.vs_inst_idx) = frag_observer_cut sb ==>
  ?u. local_prefix ctx (frag_observer sa sb fn id) (frag_observer_cut sb) s u /\
      stop_view u = h
Proof
  rpt strip_tac >>
  Cases_on `lookup_block s.vs_current_bb (frag_observer sa sb fn id).fn_blocks`
  >- gvs[run_from_def] >>
  irule same_block_halt_prefix_aux >> metis_tac[]
QED

Theorem same_block_observer_prefix_zero_path:
  !ctx observed cut s t. local_prefix ctx observed cut s t ==>
  !sa sb fn id.
  observed = frag_observer sa sb fn id /\ cut = frag_observer_cut sb /\
  cs_extends sa sb /\ sa.cs_blocks = sb.cs_blocks /\ fn_has_code sa sb fn /\
  frag_ops_free sa sb /\
  EVERY (\i. ~is_terminator i.inst_opcode) (frag_code sa sb) /\
  (s.vs_current_bb,s.vs_inst_idx) IN frag_observer_region sa sb ==>
  gas_path ctx fn s 0 (OK t)
Proof
  ho_match_mp_tac local_prefix_ind >> conj_tac
  >- (rpt strip_tac >> irule (cj 1 gas_path_rules) >> simp[]) >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >> gvs[] >>
  rename1 `abi_observer_step ctx (frag_observer sa sb fn id) (frag_observer_cut sb) s middle` >>
  `gas_path_edge ctx fn s 0 (OK middle)` by
    (irule same_block_observer_zero_edge >> metis_tac[]) >>
  `gas_path ctx fn middle 0 (OK t)` by
    (first_x_assum irule >> simp[] >>
     metis_tac[observer_region_closed_def, same_block_observer_closed]) >>
  metis_tac[cj 2 gas_path_rules, ADD]
QED

Theorem frag_exec_same_block_gas_path:
  !ctx sa sb P Q fn s.
    frag_exec ctx sa sb P Q (\r. F) /\ cs_extends sa sb /\
    sa.cs_blocks = sb.cs_blocks /\ frag_ops_free sa sb /\
    EVERY (\i. ~is_terminator i.inst_opcode) (frag_code sa sb) /\
    (!t rd. Q t ==> Q (t with vs_returndata := rd)) /\
    fn_has_code sa sb fn /\ P s /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t. gas_marked_path F ctx fn s 0 (OK t) /\ Q t /\ ~t.vs_halted /\
        t.vs_current_bb = sb.cs_current_bb /\
        t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `fn_has_code sa sb (frag_observer sa sb fn 0)` by
    (simp[fn_has_code_def, emitted_blocks_def] >>
     qexists_tac `<|bb_label := sb.cs_current_bb;
       bb_instructions := sb.cs_current_insts ++ [mk_inst 0 STOP [] []]|>` >>
     simp[frag_observer_cut_lookup, IS_PREFIX_APPEND]) >>
  `(s.vs_current_bb,s.vs_inst_idx) IN frag_observer_region sa sb` by
    metis_tac[frag_observer_start_region] >>
  qpat_x_assum `frag_exec _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE[frag_exec_def]) >>
  disch_then (qspecl_then [`frag_observer sa sb fn 0`, `s`] mp_tac) >>
  simp[] >> strip_tac >> rename1 `Q t` >>
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
    (irule same_block_observer_halt_cut_prefix >> simp[frag_observer_cut_def] >>
     metis_tac[]) >>
  `gas_path ctx fn s 0 (OK u)` by
    (drule same_block_observer_prefix_zero_path >> simp[] >>
     disch_then irule >> metis_tac[]) >>
  drule local_prefix_endpoint >> strip_tac >>
  qexists_tac `u` >> simp[gas_marked_path_def] >>
  `Q u` by (irule stop_view_closed_post >> metis_tac[]) >>
  gvs[frag_observer_cut_def]
QED
