Theory lowerDloadCallEntryPosition
Ancestors
  lowerDloadTopEntryControl lowerDloadControlPosition lowerDloadSupplySegment
  o1ContractLowerDload lowerDloadDefs o1PassContract
  contextCodegenRel venomExecSemantics venomExecProps venomInst venomState list

Theorem ld_call_entry_position:
  !a child callee b xs s ss ys t cs ss1 ct j.
  lower_dload_function_supply a child = (callee,b) /\
  first_block_no_phi child /\
  ALL_DISTINCT (MAP (\bb. bb.bb_label) callee.fn_blocks) /\
  setup_callee child xs s = SOME ss /\
  setup_callee callee ys t = SOME cs /\
  enters_block child ss ss1 /\ enters_block callee cs ct /\
  active_inst callee j ct ==>
  ss1 = ss /\ ct = cs /\
  ?bb gb bpost qpost i post code tail amid aend.
    child.fn_blocks = bb::bpost /\ callee.fn_blocks = gb::qpost /\
    lower_dload_block_supply a bb = (gb,aend) /\
    lower_dload_blocks_supply aend bpost = (qpost,b) /\
    bb.bb_instructions = i::post /\
    lower_dload_inst_supply a i = (code,amid) /\
    lower_dload_insts_supply amid post = (tail,aend) /\
    gb.bb_instructions = code ++ tail /\ code <> [] /\
    lookup_block ss1.vs_current_bb child.fn_blocks = SOME bb /\
    lookup_block ct.vs_current_bb callee.fn_blocks = SOME gb /\
    active_inst child i ss1 /\ j = HD code /\
    ss1.vs_inst_idx = 0 /\ ct.vs_inst_idx = 0 /\
    ss1.vs_current_bb = ct.vs_current_bb /\
    ss1.vs_prev_bb = ct.vs_prev_bb
Proof
  rpt gen_tac >> strip_tac >>
  qpat_assum `lower_dload_function_supply a child = _`
    (mk_asm "supply") >>
  `enters_block child cs ct` by
    metis_tac[lower_dload_function_supply_enters_block] >>
  Cases_on `child.fn_blocks` >- gvs[setup_callee_def] >>
  rename1 `child.fn_blocks = bb::bpost` >>
  Cases_on `lower_dload_block_supply a bb` >>
  Cases_on `lower_dload_blocks_supply r bpost` >>
  gvs[lower_dload_function_supply_def, lower_dload_blocks_supply_def] >>
  `q.bb_label = bb.bb_label` by
    gvs[lower_dload_block_supply_def, AllCaseEqs()] >>
  `ss.vs_current_bb = bb.bb_label /\ ss.vs_prev_bb = NONE /\
   ss.vs_inst_idx = 0 /\ cs.vs_current_bb = bb.bb_label /\
   cs.vs_prev_bb = NONE /\ cs.vs_inst_idx = 0` by
    gvs[setup_callee_def] >>
  `ss1 = ss /\ ct = cs` by
    (qpat_x_assum `enters_block child ss ss1` mp_tac >>
     qpat_x_assum `enters_block child cs ct` mp_tac >>
     gvs[first_block_no_phi_def, enters_block_def, lookup_block_def,
         FIND_thm] >>
     Cases_on `bb.bb_instructions` >>
     simp[eval_phis_def, phi_prefix_length_def] >> rpt strip_tac >> gvs[]) >>
  gvs[] >>
  `lookup_block cs.vs_current_bb (q::q') = SOME q /\
   cs.vs_inst_idx < LENGTH q.bb_instructions /\
   EL cs.vs_inst_idx q.bb_instructions = j` by
    (qpat_x_assum `active_inst _ j cs` mp_tac >>
     simp[active_inst_def] >> strip_tac >>
     gvs[lookup_block_def, FIND_thm] >> metis_tac[MEM_MAP]) >>
  `fn_entry_label child = SOME bb.bb_label` by
    simp[fn_entry_label_def, entry_block_def] >>
  `cs = cs with <|vs_prev_bb := NONE; vs_current_bb := bb.bb_label;
                   vs_inst_idx := 0|>` by
    (qpat_x_assum `setup_callee _ ys t = SOME cs` mp_tac >>
     simp[setup_callee_def] >> strip_tac >> gvs[]) >>
  `lookup_block bb.bb_label (q::q') = SOME q` by
    simp[lookup_block_def, FIND_thm] >>
  asm "supply" (mp_then Any mp_tac lower_dload_top_entry_control) >>
  disch_then (qspecl_then [`cs`, `cs`, `cs`]
    (drule_all_then strip_assume_tac o SRULE [])) >>
  qpat_x_assum `cs = _` kall_tac >>
  gvs[lookup_block_def, FIND_thm] >>
  simp[active_inst_def] >> qexists_tac `bb` >> simp[]
QED
