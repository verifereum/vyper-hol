Theory gasFocusCutGuards
Ancestors
  gasFocusSourceProvider
  dftFinitePacket dftGasFromListTraceDefs
  o1ContractCfgNormJointCursors frameJointTrace frameJointTransition
  fnFramePrefixDriver fnFrameSymbolicPrefix codegenEntryRel
  o1PipelineCorrect o1SafeUpto o1PassContract o1PassLift unitMemInv
  venomPipelineRunner venomPassSchedule irSupply fcgDefs
  dftGasOracleDefs gasEvents gasEventsFuel contextRawReachable memSafeRun
  venomExecSemantics venomWf venomInst venomState unitShapeDefs
  codegenSymRel asmDataEnv asmFrameRel asmOptimizer asmSem asmSymSem symbolResolve
  contextCodegenRel lowerDloadDefs staticAbortDefs frameOutcome callTrace
  o1RequestContract unitTransformDefs ptrDiscipline passSimulationDefs
  vfmExecution codegen asmIR
  gasFocusCfgNormSpillRanges dftFinitePacketReachability
  dftGasInvCrossingProbe dftGasInvMemoryRanges ctxLookupAgree
  lowerDloadOracleCallAssembly stepWriteFootprintBase contextPlanLayoutProps
  codegenEntrySim dretDesugarDefs
  finite_map list rich_list words arithmetic
  o1ContractCfgNormCursors o1ContractCfgNorm cfgNormSupplySim
  o1LabelFlowLateCfgNorm o1LabelFlowLateDft lowerDloadPtrStatic codegenEntrySim

Theorem focus_split_old_code_end[local]:
  !g x. code_end_var g x ==>
    !f s pred target split repls t.
      wf_function f /\ ir_supply_covers_fn s f /\ ir_supply_inst_ok s /\
      MEM pred f.fn_blocks /\ MEM target f.fn_blocks /\
      build_split_block_supply s pred target = (split,repls,t) /\
      insert_split_supply s f pred target = (g,t) /\
      MEM x (fn_ir_vars f) ==> code_end_var f x
Proof
  Induct_on `code_end_var` >> rpt strip_tac >>
  `inst.inst_opcode <> PHI /\ ~is_terminator inst.inst_opcode` by
    simp[is_terminator_def] >>
  drule_all o1LabelFlowLateCfgNormTheory.cfg_split_ordinary_origin >>
  simp[] >> rpt strip_tac
  >- metis_tac[code_end_var_rules]
  >- (rename1 `inst.inst_operands = [Var y]` >>
      `MEM y (fn_ir_vars f)` by
        metis_tac[lowerDloadPtrStaticTheory.fn_ir_vars_operand, MEM] >>
      metis_tac[code_end_var_rules]) >>
  gvs[] >> metis_tac[cfgNormSupplySimTheory.supply_split_replacement_not_old]
QED

Theorem focus_cfg_cursor_code_end[local]:
  !C rs cs. cfg_norm_cursors C rs cs ==>
    (FST (FST (LAST cs))).inst_opcode = CODECOPY ==>
    FST (FST (HD cs)) = FST (FST (LAST cs)) /\
    !x. MEM (Var x) (FST (FST (LAST cs))).inst_operands /\
        code_end_var (FST (SND (LAST rs))) x ==>
      code_end_var (FST (SND (HD rs))) x /\
      eval_operand (Var x) (SND (FST (HD cs))) =
      eval_operand (Var x) (SND (FST (LAST cs)))
Proof
  ho_match_mp_tac cfg_norm_cursors_ind >> rpt conj_tac
  >- (pure_rewrite_tac [HD,LAST_CONS,pairTheory.FST,pairTheory.SND,NOT_CONS_NIL] >> simp[]) >>
  pure_rewrite_tac [HD,LAST_CONS,pairTheory.FST,pairTheory.SND,NOT_CONS_NIL] >>
  rpt gen_tac >> strip_tac >> disch_tac
  >- (rename1 `supply_state_agree fn a v` >>
      `next.inst_opcode = CODECOPY` by metis_tac[] >>
      `MEM inst (fn_insts fn)` by
        metis_tac[EL_MEM, fn_insts_def, MEM_fn_insts_blocks] >>
      `next = inst` by
        (`inst.inst_opcode = CODECOPY` by
           metis_tac[cfgNormSupplySimTheory.supply_block_image_index] >>
         `label_positions_ok inst` by metis_tac[EVERY_MEM] >>
         gvs[] >> irule o1ContractCfgNormTheory.supply_block_image_index_unchanged >>
         simp[]) >>
      conj_tac >- metis_tac[] >>
      qx_gen_tac `x` >> strip_tac >>
      `MEM (Var x) inst.inst_operands /\ code_end_var next_fn x` by metis_tac[] >>
      `MEM x (fn_ir_vars fn)` by metis_tac[lowerDloadPtrStaticTheory.fn_ir_vars_operand] >>
      `wf_function fn /\ ir_supply_covers_fn s fn /\ ir_supply_inst_ok s`
        by fs[cfgNormSupplySimTheory.supply_norm_inv_def] >>
      conj_tac >- metis_tac[focus_split_old_code_end] >>
      `eval_operand (Var x) a = eval_operand (Var x) v` by
        (irule cfgNormSupplySimTheory.supply_eval_operand_agree >>
         qexists_tac `fn` >> simp[]) >>
      metis_tac[]) >>
  rename1 `supply_state_agree fn a v` >>
  `next.inst_opcode = CODECOPY` by metis_tac[] >>
  `ir_supply_inst_ok s /\ ir_supply_covers_fn s fn`
    by fs[cfgNormSupplySimTheory.supply_norm_inv_def] >>
  drule_all cfgNormSupplySimTheory.supply_split_index_shape >> gvs[]
QED

Theorem focus_joint_cursor_code_end[local]:
  cfg_norm_joint_cursors C8 C9 (schedules,current,saved)
    (JointConfig stk8 PG8 G8 tn8 fn8 inst8 s8 oms8 om8 hs8 h8)
    (JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 h9) /\
  inst9.inst_opcode = CODECOPY ==>
  inst8 = inst9 /\
  !x. MEM (Var x) inst9.inst_operands /\ code_end_var fn9 x ==>
      code_end_var fn8 x /\ eval_operand (Var x) s8 = eval_operand (Var x) s9
Proof
  PairCases_on `current` >>
  simp[cfg_norm_joint_cursors_def] >> strip_tac >>
  qpat_x_assum `EVERY _ schedules` mp_tac >>
  simp[EVERY_MEM] >>
  disch_then (qspec_then `(fn8,fn9,current0)` mp_tac) >>
  simp[] >> strip_tac >>
  drule focus_cfg_cursor_code_end >> simp[]
QED

Theorem focus_dft_code_end_origin[local]:
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d
    (JointConfig stk PG G tn fn inst s oms om hs h) raw_slots sites unused /\
  FLOOKUP acts p = SOME (sf,fn,inc,entry,order,res,nrest) /\
  FLOOKUP blocks (p,d) =
    SOME (bb,bt,ps,xs,ys,row_order,in_state,h0,body_entry,done,front,closed,brest) /\
  inst.inst_opcode = CODECOPY ==>
  IS_SOME body_entry /\
  (!x. code_end_var fn x ==> code_end_var sf x) /\
  (!q z. q < LENGTH xs /\ z = DROP (phi_prefix_length bb.bb_instructions) ps ++ TAKE q xs ==>
    EL (LENGTH z) (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions) = EL q xs)
Proof
  strip_tac >> conj_tac
  >- (`~is_pseudo inst.inst_opcode` by simp[is_pseudo_def] >>
      drule_all dft_packet_return_data >> strip_tac >> gvs[]) >>
  qhdtm_x_assum `dft_focus_packet_rel`
    (strip_assume_tac o REWRITE_RULE [dft_focus_packet_rel_def]) >>
  map_every (fn pat => qpat_x_assum pat mp_tac)
    [`FLOOKUP acts p = SOME (sf,fn,inc,entry,order,res,nrest)`,
     `FLOOKUP blocks (p,d) = SOME (bb,bt,ps,xs,ys,row_order,in_state,h0,body_entry,done,front,closed,brest)`,
     `o1_ctx_shape C7`,
     `!a sf tf inc entry order res nrest.
       FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) ==>
       MEM sf C7.ctx_functions /\ tf = dft_fn sf /\ _`,
     `!a e bb bt ps xs ys row_order in_state h0 body_entry count front closed brest.
       FLOOKUP blocks (a,e) = _ ==> _`] >>
  POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >> conj_tac
  >- (qpat_x_assum `!a sf tf inc entry order res nrest.
          FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) ==>
          MEM sf C7.ctx_functions /\ tf = dft_fn sf /\ _` drule >>
      strip_tac >>
      `o1_fn_shape C7 sf` by metis_tac[o1_ctx_shape_def, EVERY_MEM] >>
      `EVERY label_positions_ok (fn_insts sf)` by
        metis_tac[o1ContractCfgNormTheory.o1_fn_shape_label_positions_ok] >>
      metis_tac[o1LabelFlowLateDftTheory.dft_code_end_var_reflect]) >>
  qpat_x_assum `!a e bb bt ps xs ys row_order in_state h0 body_entry count front closed brest. _`
    drule >> strip_tac >> rpt strip_tac >>
  drule_all dft_packet_cut_instruction >> simp[]
QED

Theorem focus_current_point_code_end[local]:
  cfg_norm_joint_cursors C8 C9 (schedules,current,saved)
    (JointConfig stk8 PG8 G8 tn8 fn8 inst8 s8 oms8 om8 hs8 hist8)
    (JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 hist9) /\
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry packet
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d
    (JointConfig stk8 PG8 G8 tn8 fn8 inst8 s8 oms8 om8 hs8 hist8)
    raw_slots sites unused /\
  FLOOKUP acts p = SOME (sf,fn8,inc,entry,order,res,nrest) /\
  FLOOKUP blocks (p,d) =
    SOME (bb,bt,ps,xs,ys,row_order,in_state,h0,body_entry,done,front,closed,brest) /\
  src_inst = EL (LENGTH z) (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions) /\
  (IS_SOME body_entry ==>
    q < LENGTH xs /\ EL q xs = inst8 /\
    z = DROP (phi_prefix_length bb.bb_instructions) ps ++ TAKE q xs) /\
  (IS_SOME body_entry /\ inv_memory_observation inst8.inst_opcode ==>
    !op. MEM op inst8.inst_operands ==> eval_operand op u = eval_operand op s8) /\
  raw_reachable (root_entry with vs_gas_readings := readings) C7 sf src_inst u /\
  code_end_offset_ok (\ctx fn i s. fn = sf /\ i = src_inst /\ s = u) C7 /\
  root_entry.vs_labels = vs0.vs_labels /\
  codegen_asm_entry_rel cpl prog vs0 ast0 ==>
  !dst x sz src off.
    inst9.inst_opcode = CODECOPY /\ inst9.inst_operands = [dst; Var x; sz] /\
    code_end_var fn9 x /\ eval_operand (Var x) s9 = SOME src /\
    FLOOKUP (SND (compute_label_offsets prog)) "code_end" = SOME off ==>
    w2n (src - n2w off) < dimword (:256) DIV 2
Proof
  rpt strip_tac >>
  drule_all focus_joint_cursor_code_end >> strip_tac >>
  `code_end_var fn8 x /\ eval_operand (Var x) s8 = SOME src` by
    (qpat_x_assum `!x. MEM (Var x) _ /\ code_end_var fn9 x ==> _`
       (qspec_then `x` mp_tac) >> simp[]) >>
  `inst8.inst_opcode = CODECOPY` by simp[] >>
  drule_all focus_dft_code_end_origin >> strip_tac >>
  `code_end_var sf x` by simp[] >>
  `src_inst = inst8` by
    (`q < LENGTH xs /\ EL q xs = inst8 /\
      z = DROP (phi_prefix_length bb.bb_instructions) ps ++ TAKE q xs` by simp[] >>
     qpat_x_assum `!q z. _ ==> EL _ _ = EL q xs` (qspecl_then [`q`,`z`] mp_tac) >>
     simp[]) >>
  `inv_memory_observation inst8.inst_opcode` by
    simp[dftGasInvCrossingProbeTheory.inv_memory_observation_def] >>
  `eval_operand (Var x) u = SOME src` by
    (qpat_x_assum `IS_SOME body_entry /\ inv_memory_observation _ ==> _` mp_tac >>
     simp[] >> disch_then (qspec_then `Var x` mp_tac) >> simp[]) >>
  `u.vs_labels = vs0.vs_labels` by
    (drule raw_reachable_labels >> simp[]) >>
  `FLOOKUP u.vs_labels "code_end" = SOME (n2w off)` by
    (qpat_x_assum `codegen_asm_entry_rel _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [codegenEntrySimTheory.codegen_asm_entry_rel_def]) >>
     simp[]) >>
  qpat_x_assum `code_end_offset_ok _ _` mp_tac >>
  simp[code_end_offset_ok_def] >>
  disch_then (qspecl_then [`dst`,`x`,`sz`,`src`,`n2w off`] mp_tac) >> simp[]
QED

Theorem focus_cut_replay_ranges[local]:
  inst.inst_opcode <> DRET /\ ~in_revert_forward fn s /\
  (~in_revert_forward fn s ==> ~in_revert_forward sf u) /\
  lowered_mem_fact eom C7 sf inst u /\
  (!op. MEM op inst.inst_operands ==> eval_operand op u = eval_operand op s) /\
  u.vs_initial_fmp = s.vs_initial_fmp ==>
  lowered_mem_fact eom C8 fn inst s
Proof
  strip_tac >>
  `inst_mem_ranges inst u = inst_mem_ranges inst s` by
    (irule inv_non_dret_ranges_cong >> simp[]) >>
  gvs[lowered_mem_fact_def, lowered_mem_ok_def]
QED

Theorem focus_current_point_ranges[local]:
  cfg_norm_joint_cursors C8 C9 (schedules,current,saved)
    (JointConfig stk8 PG8 G8 tn8 fn8 inst8 s8 oms8 om8 hs8 h8)
    (JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 h9) /\
  ~in_revert_forward fn9 s9 /\ generate_context_plan C9 = SOME cpl /\
  codegen_asm_entry_rel cpl prog vs0 (entry_asm_state vs0 es0) /\
  root_entry = vs0 with <|vs_prev_bb := NONE; vs_current_bb := lbl7; vs_inst_idx := 0|> /\
  C8.ctx_entry = SOME nm /\ lookup_function nm C8.ctx_functions = SOME root_tf /\
  fn_entry_label root_tf = SOME lbl7 /\
  j < LENGTH (trace_blocks [] 0 N C8 root_tf root_entry) /\
  EL j (trace_blocks [] 0 N C8 root_tf root_entry) = ((p,d,inst8.inst_id),fn8,inst8,s8) /\
  EVERY (o1_fn_shape C8) C8.ctx_functions /\
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry (j,obs)
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d
    (JointConfig stk8 PG8 G8 tn8 fn8 inst8 s8 oms8 om8 hs8 h8) raw_slots sites unused /\
  (inv_memory_observation inst8.inst_opcode ==>
    ?sf inc entry order res nrest bb bt ps xs ys rho in_state h0
      body_entry count front closed brest q z src_inst u.
      FLOOKUP acts p = SOME (sf,fn8,inc,entry,order,res,nrest) /\
      FLOOKUP blocks (p,d) =
        SOME (bb,bt,ps,xs,ys,rho,in_state,h0,body_entry,count,front,closed,brest) /\
      src_inst = EL (LENGTH z) (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions) /\
      ((IS_SOME body_entry /\ q < LENGTH xs /\ EL q xs = inst8 /\
        z = DROP (phi_prefix_length bb.bb_instructions) ps ++ TAKE q xs) \/
       body_entry = NONE) /\
      lowered_mem_fact cpl.cp_max_static_eom C7 sf src_inst u /\
      (~in_revert_forward fn8 s8 ==> ~in_revert_forward sf u) /\
      (IS_SOME body_entry ==>
        (!op. MEM op inst8.inst_operands ==> eval_operand op u = eval_operand op s8) /\
        u.vs_initial_fmp = s8.vs_initial_fmp)) ==>
  source_memory_reads_disjoint cpl inst9 s9 /\
  context_source_memory_writes_disjoint cpl inst9 s9
Proof
  strip_tac >> irule focus_cfg_norm_pre_edge_ranges >>
  qpat_assum `cfg_norm_joint_cursors _ _ _ _ _` (irule_at Any) >> simp[] >> strip_tac >>
  `MEM fn8 C8.ctx_functions` by
    (Cases_on `current` >> fs[cfg_norm_joint_cursors_def] >>
     metis_tac[MEM_MAP, pairTheory.FST]) >>
  `MEM ((p,d,inst8.inst_id),fn8,inst8,s8) (trace_blocks [] 0 N C8 root_tf root_entry)` by
    (simp[MEM_EL] >> qexists `j` >> gvs[]) >>
  `raw_reachable root_entry C8 fn8 inst8 s8` by
    (irule dft_packet_trace_raw_reachable >> gvs[] >> metis_tac[]) >>
  `cpl.cp_initial_fmp <= w2n s8.vs_initial_fmp` by
    (drule raw_reachable_initial_fmp >>
     fs[codegen_asm_entry_rel_def] >> strip_tac >>
     drule generate_context_plan_spill_gap >> strip_tac >>
     qpat_x_assum `n2w _ = vs0.vs_initial_fmp` (SUBST1_TAC o SYM) >>
     simp[LESS_MOD]) >>
  `o1_fn_shape C8 fn8` by metis_tac[EVERY_MEM] >>
  `active_inst fn8 inst8 s8` by metis_tac[raw_reachable_active] >>
  `inst_shape_ok inst8 /\ inst8.inst_opcode <> DRET` by
    (drule ld_active_inst_member >>
     fs[o1_fn_shape_def, fn_shape_ok_def, no_dret_def, EVERY_MEM]) >>
  `inv_memory_observation inst8.inst_opcode` by
    metis_tac[inv_memory_observation_covers_ranges] >>
  qpat_x_assum `inv_memory_observation _ ==> _` drule >> strip_tac >>
  drule dft_packet_guarded_cursor_structure >> (impl_tac >- simp[]) >>
  strip_tac >> gvs[] >>
  rename1 `FLOOKUP blocks _ = SOME (bb,_,ps,xs,ys,_,_,_,_,_,_,_,_)` >>
  rename1 `lowered_mem_fact _ _ _ (EL (_ + qi) _) _` >>
  `EL (LENGTH (DROP (phi_prefix_length bb.bb_instructions) ps ++ TAKE qi xs))
      (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions) = EL qi xs` by
    (irule dft_packet_cut_instruction >> fs[]) >>
  gvs[] >> irule focus_cut_replay_ranges >>
  qpat_assum `lowered_mem_fact _ _ _ _ _` (irule_at Any) >> simp[]
QED

(* A cut short of the marked prefix cannot replay to a stopped result:
   that result would make all the root events fit in the shorter cut. *)
Theorem focus_rooted_cut_ok_within_marks[local]:
  n <= LENGTH (gas_events_blocks f7 C7 root_sf s) /\ LENGTH Ecut < n /\
  (?extra. Ecut = FST (rooted_eval (MAX N f7) C7 levels s) ++ extra) /\
  (case SND (rooted_eval (MAX N f7) C7 levels s) of
     OK u => FST (rooted_eval (MAX N f7) C7 levels s) = Ecut
   | stopped =>
       run_blocks (MAX N f7) C7 root_sf s = stopped /\
       gas_events_blocks (MAX N f7) C7 root_sf s =
         FST (rooted_eval (MAX N f7) C7 levels s)) ==>
  ?u. rooted_eval (MAX N f7) C7 levels s = (Ecut,OK u)
Proof
  strip_tac >>
  `n <= LENGTH (gas_events_blocks (MAX N f7) C7 root_sf s)` by
    (qspec_then `f7` mp_tac (cj 3 gas_events_fuel_extension) >>
     disch_then (qspecl_then [`C7`,`root_sf`,`s`,`MAX N f7`] mp_tac) >>
     simp[] >> strip_tac >> simp[]) >>
  Cases_on `rooted_eval (MAX N f7) C7 levels s` >>
  rename1 `rooted_eval _ _ _ _ = (events,result)` >>
  Cases_on `result` >> gvs[] >> decide_tac
QED

Theorem focus_current_witness_guard[local]:
  cfg_norm_joint_cursors C8 C9 (schedules,current,saved)
    (JointConfig stk8 PG8 G8 tn8 fn8 inst8 s8 oms8 om8 hs8 hist8)
    (JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 hist9) /\
  generate_context_plan C9 = SOME cpl /\
  codegen_asm_entry_rel cpl prog vs0 (entry_asm_state vs0 es0) /\
  root_entry = vs0 with <|vs_prev_bb := NONE; vs_current_bb := lbl7; vs_inst_idx := 0|> /\
  C8.ctx_entry = SOME nm /\ lookup_function nm C8.ctx_functions = SOME root_tf /\
  fn_entry_label root_tf = SOME lbl7 /\
  j < LENGTH (trace_blocks [] 0 N C8 root_tf root_entry) /\
  EL j (trace_blocks [] 0 N C8 root_tf root_entry) = ((p,d,inst8.inst_id),fn8,inst8,s8) /\
  EVERY (o1_fn_shape C8) C8.ctx_functions /\
  dft_focus_packet_rel N C7 C8 root_sf root_tf root_entry (j,obs)
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d
    (JointConfig stk8 PG8 G8 tn8 fn8 inst8 s8 oms8 om8 hs8 hist8) raw_slots sites unused /\
  FLOOKUP acts p = SOME (sf,fn8,inc,entry,order,res,nrest) /\
  FLOOKUP blocks (p,d) =
    SOME (bb,bt,ps,xs,ys,row_order,in_state,h0,body_entry,done,front,closed,brest) /\
  src_inst = EL (LENGTH z) (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions) /\
  ((IS_SOME body_entry /\ q < LENGTH xs /\ EL q xs = inst8 /\
    z = DROP (phi_prefix_length bb.bb_instructions) ps ++ TAKE q xs) \/
   body_entry = NONE) /\
  ~in_revert_forward fn9 s9 /\
  raw_slots = Mcut ++ mr /\
  LIST_REL (\slot w. slot = NONE \/ slot = SOME w) raw_slots raw /\
  LENGTH Mcut = LENGTH Ecut /\ LENGTH Mcut < n /\
  n <= LENGTH (gas_events_blocks f7 C7 root_sf (root_entry with vs_gas_readings := raw ++ [0w])) /\
  (!F gs tail.
    N <= F /\ LIST_REL (\slot w. slot = NONE \/ slot = SOME w) Mcut gs ==>
    (?extra. Ecut = FST (rooted_eval F C7 levels
      (root_entry with vs_gas_readings := gs ++ tail)) ++ extra) /\
    (case SND (rooted_eval F C7 levels (root_entry with vs_gas_readings := gs ++ tail)) of
       OK u => FST (rooted_eval F C7 levels (root_entry with vs_gas_readings := gs ++ tail)) = Ecut
     | stopped =>
         run_blocks F C7 root_sf (root_entry with vs_gas_readings := gs ++ tail) = stopped /\
         gas_events_blocks F C7 root_sf (root_entry with vs_gas_readings := gs ++ tail) =
           FST (rooted_eval F C7 levels (root_entry with vs_gas_readings := gs ++ tail)))) /\
  (!F u.
    N <= F /\
    rooted_eval F C7 levels (root_entry with vs_gas_readings :=
      TAKE (LENGTH Mcut) raw ++ (DROP (LENGTH Mcut) raw ++ [0w])) = (Ecut,OK u) ==>
    raw_reachable (root_entry with vs_gas_readings :=
      TAKE (LENGTH Mcut) raw ++ (DROP (LENGTH Mcut) raw ++ [0w])) C7 sf src_inst u /\
    lowered_mem_fact cpl.cp_max_static_eom C7 sf src_inst u /\
    (fin = asm_opt_finalizer ==>
      code_end_offset_ok (\ctx fn i s. fn = sf /\ i = src_inst /\ s = u) C7) /\
    (~in_revert_forward fn8 s8 ==> ~in_revert_forward sf u) /\
    (inv_memory_observation inst8.inst_opcode ==>
      (!op. MEM op inst8.inst_operands ==> eval_operand op u = eval_operand op s8) /\
      u.vs_initial_fmp = s8.vs_initial_fmp)) ==>
  ~in_revert_forward fn9 s9 /\
  (inst9.inst_opcode <> INVOKE /\ ~is_terminator inst9.inst_opcode ==>
   source_memory_reads_disjoint cpl inst9 s9 /\
   context_source_memory_writes_disjoint cpl inst9 s9) /\
  (fin = asm_opt_finalizer ==>
   !dst x sz src off.
     inst9.inst_opcode = CODECOPY /\ inst9.inst_operands = [dst; Var x; sz] /\
     code_end_var fn9 x /\ eval_operand (Var x) s9 = SOME src /\
     FLOOKUP (SND (compute_label_offsets prog)) "code_end" = SOME off ==>
     w2n (src - n2w off) < dimword (:256) DIV 2)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `LIST_REL (\slot w. slot = NONE \/ slot = SOME w) Mcut (TAKE (LENGTH Mcut) raw)` by
    (drule LIST_REL_TAKE >> disch_then (qspec_then `LENGTH Mcut` mp_tac) >>
     simp[TAKE_APPEND1, IgnAsm `LENGTH Mcut = LENGTH Ecut`]) >>
  `?u. rooted_eval (MAX N f7) C7 levels
       (root_entry with vs_gas_readings := raw ++ [0w]) = (Ecut,OK u)` by
    (irule focus_rooted_cut_ok_within_marks >>
     qpat_assum `n <= LENGTH (gas_events_blocks f7 C7 root_sf _)` (irule_at Any) >>
     qpat_x_assum `!F gs tail. _`
       (qspecl_then [`MAX N f7`, `TAKE (LENGTH Mcut) raw`, `DROP (LENGTH Mcut) raw ++ [0w]`] mp_tac) >>
     simp[APPEND_ASSOC]) >>
  qpat_x_assum `!F u. _` (qspecl_then [`MAX N f7`,`u`] mp_tac) >>
  simp[NoAsms, APPEND_ASSOC] >> (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  conj_tac >- first_assum ACCEPT_TAC >> conj_tac
  >- (strip_tac >> irule focus_current_point_ranges >>
      qhdtm_assum `dft_focus_packet_rel` (irule_at Any) >>
      qpat_assum `cfg_norm_joint_cursors _ _ _ _ _` (irule_at Any) >>
      qpat_assum `codegen_asm_entry_rel _ _ _ _` (irule_at Any) >>
      qpat_assum `C8.ctx_entry = SOME nm` (irule_at Any) >>
      simp[] >> strip_tac >> qexistsl [`q`,`z`,`u`] >>
      qpat_assum `src_inst = _` (SUBST1_TAC o SYM) >> simp[])
  >> strip_tac >>
  `IS_SOME body_entry ==> q < LENGTH xs /\ EL q xs = inst8 /\
    z = DROP (phi_prefix_length bb.bb_instructions) ps ++ TAKE q xs` by
    (Cases_on `body_entry` >> fs[]) >>
  `IS_SOME body_entry /\ inv_memory_observation inst8.inst_opcode ==>
    !op. MEM op inst8.inst_operands ==> eval_operand op u = eval_operand op s8` by
    (strip_tac >> res_tac) >>
  `code_end_offset_ok (\ctx fn i s. fn = sf /\ i = src_inst /\ s = u) C7` by simp[] >>
  `root_entry.vs_labels = vs0.vs_labels` by simp[] >>
  rpt strip_tac >> irule focus_current_point_code_end >>
  qhdtm_assum `dft_focus_packet_rel` (irule_at Any) >>
  qhdtm_assum `cfg_norm_joint_cursors` (irule_at Any) >>
  qpat_assum `FLOOKUP acts p = SOME _` (irule_at Any) >>
  qpat_assum `FLOOKUP blocks (p,d) = SOME _` (irule_at Any) >>
  qhdtm_assum `raw_reachable` (irule_at Any) >>
  qhdtm_assum `codegen_asm_entry_rel` (irule_at Any) >>
  qpat_assum `inst9.inst_operands = [dst; Var x; sz]` (irule_at Any) >>
  qexistsl [`z`,`q`] >> simp[]
QED

fun reuse_witnesses th (asl, goal) =
  let
    val vars = map (variant (free_varsl (goal::asl)))
      (fst (strip_exists (concl th)))
  in
    (List.foldr (fn (v,t) => Thm_cont.X_CHOOSE_THEN v t)
       (map_every assume_tac o CONJUNCTS) vars th >>
     map_every EXISTS_TAC vars) (asl, goal)
  end

(* Scratch statement for elaboration and independent review.
   For the given compatible filling, use the H1 bounded family.
   The outcomes are continuation, beyond the marked cut, forwarding,
   or a non-error C7 prefix stop with its propagated root result and events. *)
Theorem focus_cut_guard_or_stop:
    o1PipelineCorrect$o1_pipeline rpolicy unit = SOME out /\
    o1_source_unit_ok unit /\ unit_entry_no_params unit /\
    unit_defs_reach_uses unit /\ unit_fmp_unsealed unit /\
    o1_initial_state_ok vs0 /\ vs0.vs_fmp = vs0.vs_initial_fmp /\
    code_layout_valid vs0 /\
    unit_shape_ok out.po_unit /\
    generate_context_plan out.po_unit.cu_context = SOME cpl /\
    codegen_assembly rpolicy out.po_unit = SOME prog /\
    fin IN accepted_finalizers /\ fin rpolicy prog = SOME prog' /\
    (fin = asm_opt_finalizer ==>
       label_flow_ok unit.cu_context /\
       (!fn inst. MEM fn unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) ==>
                  ~MEM (Label "code_end") inst.inst_operands) /\
       EVERY (\ds. EVERY (\di. case di of DataBytes _ => T | DataLabel _ => F)
                         ds.ds_items) unit.cu_data_segment /\
       ((?fn inst. MEM fn unit.cu_context.ctx_functions /\
                   MEM inst (fn_insts fn) /\
                   MEM (Label "runtime_begin") inst.inst_operands) ==>
        EXISTS (\ds. ds.ds_label = "runtime_begin") unit.cu_data_segment) /\
       LENGTH vs0.vs_data_section < dimword (:256) DIV 2) /\
    (vs0.vs_call_ctx.cc_static ==>
       !fn inst. MEM fn unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) ==>
                 ~MEM (Label "runtime_begin") inst.inst_operands) /\
    vs0.vs_code = assemble prog ++ vs0.vs_data_section /\
    codegen_asm_entry_rel cpl prog vs0 (entry_asm_state vs0 es0) /\
    asm_frame_rel_tail [] prog' vs0.vs_data_section es0
      (entry_asm_state vs0 es0 with
        as_code := assemble prog' ++ vs0.vs_data_section) es0 /\
    unit.cu_context.ctx_entry = SOME nm /\
    lookup_function nm unit.cu_context.ctx_functions = SOME entryfn /\
    fn_entry_label entryfn = SOME lbl /\
    w2n vs0.vs_initial_fmp <= w2n fmp /\ w2n fmp < 2 ** 254 /\
    unit_alloca_budget unit.cu_context +
      32 * ctx_dload_count unit.cu_context <= w2n fmp /\
    (!gs. ?D f extra.
      dead_wf D /\
      (fin = asm_opt_finalizer ==>
         !fn inst s.
           raw_reachable (vs0 with <|vs_gas_readings := gs; vs_fmp := fmp; vs_initial_fmp := fmp|>)
             unit.cu_context fn inst s /\
           gas_cut (MIN (LENGTH (markf gs)) (LENGTH gs))
             (vs0 with <|vs_gas_readings := gs; vs_fmp := fmp; vs_initial_fmp := fmp|>) s ==>
           inst_dload_in_section inst s) /\
      o1_safe_upto D lo (MIN (LENGTH (markf gs)) (LENGTH gs))
        unit.cu_context (vs0 with <|vs_gas_readings := gs; vs_fmp := fmp; vs_initial_fmp := fmp|>) /\
      MAP project
        (gas_events_blocks f unit.cu_context entryfn
          (vs0 with <|vs_gas_readings := gs; vs_fmp := fmp; vs_initial_fmp := fmp;
                      vs_prev_bb := NONE;
                      vs_current_bb := lbl; vs_inst_idx := 0|>)) =
        markf gs ++ extra) /\
    run_call es0 = SOME (result,final) /\
    ~frame_resource_starved es0 result final /\
    run_pipeline_stages rpolicy o1_pipeline_spec.ps_pre_walk_stages unit
      (init_ir_supply unit) = SOME (pre,t) /\
    pre.cu_context.ctx_entry = SOME nm /\
    run_callee_first rpolicy o1_fn_passes
      (fcg_postorder (fcg_analyze pre.cu_context) nm)
      (prune_unit_fcg_unreachable pre (fcg_analyze pre.cu_context)) t =
      SOME (out.po_unit,t') /\
    stage 0 = (prune_unit_fcg_unreachable pre (fcg_analyze pre.cu_context)).cu_context /\
    stage 9 = out.po_unit.cu_context /\
    (!k. k < 9 ==> ctx_pass_stage rpolicy (EL k o1_fn_passes) (o1_walk_view rpolicy k)
      (stage k) (stage (SUC k))) /\
    (!k. k <= 9 ==> o1_ctx_shape (stage k) /\
      EVERY (o1_fn_row k) (stage k).ctx_functions) /\
  0 < N /\
  root_entry = vs0 with <|vs_prev_bb := NONE; vs_current_bb := lbl7; vs_inst_idx := 0|> /\
  (stage 7).ctx_entry = SOME nm /\ (stage 8).ctx_entry = SOME nm /\
  lookup_function nm (stage 7).ctx_functions = SOME root_sf /\
  lookup_function nm (stage 8).ctx_functions = SOME root_tf /\
  fn_entry_label root_sf = SOME lbl7 /\ fn_entry_label root_tf = SOME lbl7 /\
  joint_initial vs0 (stage 8) q80 /\ joint_initial vs0 (stage 9) q90 /\
  joint_trace vs0 (stage 8) q80 evs8 qs8 (JointConfig stk8 PG8 G8 tn8 fn8 inst8 s8 oms8 om8 hs8 hist8) /\
  joint_trace vs0 (stage 9) q90 evs9 qs9 (JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 hist9) /\
  cfg_norm_joint_cursors (stage 8) (stage 9) (schedules,current,saved) (JointConfig stk8 PG8 G8 tn8 fn8
    inst8 s8 oms8 om8 hs8 hist8) (JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 hist9) /\
  asm_steps (SND (compute_label_offsets prog)) (build_offset_to_pc prog)
    prog asm_fuel (entry_asm_state vs0 es0) = AsmOK ast /\
  (fin = K SOME ==> normal_frame_plan rpolicy out.po_unit cpl prog (vs0 with
    <|vs_call_entry_fmp := n2w cpl.cp_initial_fmp; vs_return_pc_token := 0w;
    vs_inst_idx := 0|>) es0 (JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 hist9) ast) /\
  (fin = asm_opt_finalizer ==>
    sym_steps prog (asm_data_env prog vs0.vs_code) asm_fuel (sym_init (entry_asm_state vs0 es0)) = SymOK ss /\
    normal_frame_symbolic_plan (asm_data_env prog vs0.vs_code) rpolicy out.po_unit cpl prog vs0 es0
      (JointConfig stk9 PG9 G9 tn9 fn9 inst9 s9 oms9 om9 hs9 hist9) ast ss) /\
  dft_focus_packet_rel N (stage 7) (stage 8) root_sf root_tf root_entry (j,obs)
    acts blocks calls ms_tab es_tab ks_tab rooted_eval p d (JointConfig stk8 PG8 G8 tn8 fn8 inst8 s8 oms8
      om8 hs8 hist8) raw_slots sites unused /\
  j = LENGTH evs8 /\ LENGTH evs8 <= LENGTH evs9 /\ LENGTH (TAKE j (dftGasFromListTraceDefs$trace_blocks []
    0 N (stage 8) root_tf root_entry)) = j /\
  j < LENGTH (dftGasFromListTraceDefs$trace_blocks [] 0 N (stage 8) root_tf root_entry) /\ obs =
    dftGasFromListTraceDefs$trace_gas (TAKE j (dftGasFromListTraceDefs$trace_blocks [] 0 N (stage 8)
    root_tf root_entry)) /\
  EL j (dftGasFromListTraceDefs$trace_blocks [] 0 N (stage 8) root_tf root_entry) =
    ((p,d,inst8.inst_id),fn8,inst8,s8) /\
  LENGTH raw_slots = LENGTH sites /\
  PERM (MAP THE (FILTER IS_SOME raw_slots) ++ unused) (gas_readings es0) /\
  LIST_REL (\slot w. slot = NONE \/ slot = SOME w) raw_slots raw ==>
  (?sf inc entry order res nrest bb bt ps xs ys rho in_state h0
      body_entry count front closed brest.
      FLOOKUP acts p = SOME (sf,fn8,inc,entry,order,res,nrest) /\
      FLOOKUP blocks (p,d) =
        SOME (bb,bt,ps,xs,ys,rho,in_state,h0,body_entry,count,front,closed,brest) /\
      get_instruction bt s8.vs_inst_idx = SOME inst8 /\
      ((inv_memory_observation inst8.inst_opcode \/ is_fallible inst8 \/
        inst8.inst_opcode = INVOKE \/ is_terminator inst8.inst_opcode) ==>
      ?q z src_inst cuts levels Mcut Ecut Kcut mr er kr.
        src_inst = EL (LENGTH z)
          (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions) /\
        ((IS_SOME body_entry /\ LENGTH ps <= s8.vs_inst_idx /\
          s8.vs_inst_idx - LENGTH ps < LENGTH rho /\
          q = EL (s8.vs_inst_idx - LENGTH ps) rho /\ q < LENGTH xs /\
          EVERY (\i. ~is_terminator i.inst_opcode) (TAKE q xs) /\
          (!r. r < q /\ (EL r xs).inst_opcode = INVOKE ==> MEM r (TAKE count rho)) /\
          EL q xs = inst8 /\
          z = DROP (phi_prefix_length bb.bb_instructions) ps ++ TAKE q xs) \/
         (p = p /\ d = d /\ s8 = s8 /\ body_entry = NONE /\
          s8.vs_inst_idx < LENGTH ps /\ q = 0 /\
          z = DROP (phi_prefix_length bb.bb_instructions) (TAKE s8.vs_inst_idx ps))) /\
        MAP (\(ai,ds,ei,qi,zi). ai) cuts =
          REVERSE (GENLIST (\i. DROP i p) (SUC (LENGTH p))) /\
        LENGTH cuts = LENGTH levels /\
        (!i ai ds ei qi zi.
          i < LENGTH cuts /\ EL i cuts = (ai,ds,ei,qi,zi) ==>
          ?sfi tfi inci enti orderi resi nresti bbi bti psi xsi ysi rhoi
            ini hi bei counti fronti closedi resti later.
            FLOOKUP acts ai = SOME (sfi,tfi,inci,enti,orderi,resi,nresti) /\
            FLOOKUP blocks (ai,ei) =
              SOME (bbi,bti,psi,xsi,ysi,rhoi,ini,hi,bei,counti,fronti,closedi,resti) /\
            orderi = ds ++ ei::later /\
            (if SUC i = LENGTH cuts then
              ai = p /\ ei = d /\ qi = q /\ zi = z
            else
              ?cid h b0 done_at_call child_entry ret.
                EL (SUC i) (MAP (\(aj,djs,ej,qj,zj). aj) cuts) = (ei,cid)::ai /\
                FLOOKUP calls (ai,ei,cid) =
                  SOME (qi,h,b0,done_at_call,child_entry,ret) /\
                qi < LENGTH xsi /\ (EL qi xsi).inst_id = cid /\
                zi = DROP (phi_prefix_length bbi.bb_instructions) psi ++ TAKE qi xsi /\
                EVERY (\x. ~is_terminator x.inst_opcode) (TAKE qi xsi) /\
                (!r. r < qi /\ (EL r xsi).inst_opcode = INVOKE ==>
                  MEM r done_at_call)) /\
            EL i levels =
              (sfi,
               MAP (\f.
                 (FST (THE (FLOOKUP blocks (ai,f))),f,
                  DROP (phi_prefix_length
                    (FST (THE (FLOOKUP blocks (ai,f)))).bb_instructions)
                    (FST (THE (FLOOKUP blocks (ai,f)))).bb_instructions)) ds ++
                 [(bbi,ei,zi)],
               if SUC i = LENGTH cuts then NONE else SOME (EL qi xsi))) /\
        Mcut = FLAT (MAP (\(ai,ds,ei,qi,zi).
          FLAT (MAP (\f. FLAT (THE (FLOOKUP ms_tab (ai,f)))) ds) ++
          FLAT (TAKE qi (THE (FLOOKUP ms_tab (ai,ei))))) cuts) /\
        Ecut = FLAT (MAP (\(ai,ds,ei,qi,zi).
          FLAT (MAP (\f. FLAT (THE (FLOOKUP es_tab (ai,f)))) ds) ++
          FLAT (TAKE qi (THE (FLOOKUP es_tab (ai,ei))))) cuts) /\
        Kcut = FLAT (MAP (\(ai,ds,ei,qi,zi).
          FLAT (MAP (\f. FLAT (THE (FLOOKUP ks_tab (ai,f)))) ds) ++
          FLAT (TAKE qi (THE (FLOOKUP ks_tab (ai,ei))))) cuts) /\
        raw_slots = Mcut ++ mr /\ sites = Ecut ++ er /\ (FLAT (MAP (\e. FLAT (THE (FLOOKUP ks_tab
          ([],e)))) (FST (SND (SND (SND (SND (THE (FLOOKUP acts []))))))))) = Kcut ++ kr /\
        LENGTH Mcut = LENGTH Ecut /\ LENGTH Mcut = LENGTH Kcut /\
        (!F gs tail.
          N <= F /\
          LIST_REL (\slot w. slot = NONE \/ slot = SOME w) Mcut gs ==>
          (?extra. Ecut = FST (rooted_eval F (stage 7) levels
            (root_entry with vs_gas_readings := gs ++ tail)) ++ extra) /\
          (case SND (rooted_eval F (stage 7) levels (root_entry with vs_gas_readings := gs ++ tail)) of
            OK u =>
              FST (rooted_eval F (stage 7) levels
                (root_entry with vs_gas_readings := gs ++ tail)) = Ecut /\
              u.vs_gas_readings = tail /\
              (?before after.
                dftGasFromListTraceDefs$trace_blocks [] 0 F (stage 7) root_sf
                  (root_entry with vs_gas_readings := gs ++ tail) =
                  before ++ [((p,d,(EL (LENGTH z)
                    (DROP (phi_prefix_length bb.bb_instructions)
                      bb.bb_instructions)).inst_id),sf,
                    EL (LENGTH z) (DROP (phi_prefix_length bb.bb_instructions)
                      bb.bb_instructions),u)] ++ after /\
                dftGasFromListTraceDefs$trace_gas before = ZIP (Kcut,gs)) /\
              (!tail'. rooted_eval F (stage 7) levels
                (root_entry with vs_gas_readings := gs ++ tail') =
                  (Ecut,OK (u with vs_gas_readings := tail'))) /\
              (body_entry = NONE ==>
                u with vs_gas_readings := s8.vs_gas_readings = s8) /\
              (p = p /\ d = d /\ IS_SOME body_entry /\
               inv_memory_observation inst8.inst_opcode /\ EL q xs = inst8 ==>
                (!op. MEM op inst8.inst_operands ==>
                  eval_operand op u = eval_operand op s8) /\
                u.vs_initial_fmp = s8.vs_initial_fmp)
          | stopped =>
              run_blocks F (stage 7) root_sf
                (root_entry with vs_gas_readings := gs ++ tail) = stopped /\
              gas_events_blocks F (stage 7) root_sf
                (root_entry with vs_gas_readings := gs ++ tail) =
                  FST (rooted_eval F (stage 7) levels
                    (root_entry with vs_gas_readings := gs ++ tail)))) /\
        (!F gs tail n u.
          N <= F /\ LIST_REL (\slot w. slot = NONE \/ slot = SOME w) Mcut gs /\
          LENGTH Mcut < n /\
          mem_inv (\ctx src_fn src_inst src_state.
            gas_cut n (root_entry with vs_gas_readings := gs ++ tail) src_state ==>
              static_mem_ok cpl.cp_max_static_eom ctx src_fn src_inst src_state)
            (stage 7) (root_entry with vs_gas_readings := gs ++ tail) /\
          rooted_eval F (stage 7) levels (root_entry with vs_gas_readings := gs ++ tail) =
            (Ecut,OK u) ==>
          static_mem_ok cpl.cp_max_static_eom (stage 7) sf src_inst u /\
          (~in_revert_forward fn8 s8 ==> ~in_revert_forward sf u) /\
          (inv_memory_observation src_inst.inst_opcode ==>
            (!op. MEM op src_inst.inst_operands ==> eval_operand op u = eval_operand op s8) /\
            u.vs_initial_fmp = s8.vs_initial_fmp)) /\
  (!raw F u.
    LIST_REL (\slot w. slot = NONE \/ slot = SOME w) raw_slots raw ==>

    N <= F /\ LENGTH Mcut < (MIN (LENGTH (markf (raw ++ [0w]))) (LENGTH (raw ++ [0w]))) /\
    rooted_eval F (stage 7) levels (root_entry with vs_gas_readings := (TAKE (LENGTH Mcut) raw) ++ (DROP
      (LENGTH Mcut) raw ++ [0w])) = (Ecut,OK u) ==>
    raw_reachable (root_entry with vs_gas_readings := (TAKE (LENGTH Mcut) raw) ++ (DROP (LENGTH Mcut) raw
      ++ [0w])) (stage 7) sf src_inst u /\ gas_cut (MIN (LENGTH (markf (raw ++ [0w]))) (LENGTH (raw ++
      [0w]))) (root_entry with vs_gas_readings := (TAKE (LENGTH Mcut) raw) ++ (DROP (LENGTH Mcut) raw ++
      [0w])) u /\
    lowered_mem_fact cpl.cp_max_static_eom (stage 7) sf src_inst u /\
    u.vs_gas_readings = (DROP (LENGTH Mcut) raw ++ [0w]) /\
    (fin = asm_opt_finalizer ==>
      inst_dload_in_section src_inst u /\
      code_end_offset_ok (\ctx fn i s. fn = sf /\ i = src_inst /\ s = u) (stage 7)) /\
    (~in_revert_forward fn8 s8 ==> ~in_revert_forward sf u) /\
    (inv_memory_observation inst8.inst_opcode ==>
      (!op. MEM op inst8.inst_operands ==> eval_operand op u = eval_operand op s8) /\
      u.vs_initial_fmp = s8.vs_initial_fmp)) /\
  ((~in_revert_forward fn9 s9 /\
      (inst9.inst_opcode <> INVOKE /\ ~is_terminator inst9.inst_opcode ==>
       source_memory_reads_disjoint cpl inst9 s9 /\
       context_source_memory_writes_disjoint cpl inst9 s9) /\
      (fin = asm_opt_finalizer ==>
       !dst x sz src off.
         inst9.inst_opcode = CODECOPY /\ inst9.inst_operands = [dst; Var x; sz] /\
         code_end_var fn9 x /\ eval_operand (Var x) s9 = SOME src /\
         FLOOKUP (SND (compute_label_offsets prog)) "code_end" = SOME off ==>
         w2n (src - n2w off) < dimword (:256) DIV 2)) \/
     (MIN (LENGTH (markf (raw ++ [0w]))) (LENGTH (raw ++ [0w]))) <= LENGTH Mcut \/
     (LENGTH Mcut < (MIN (LENGTH (markf (raw ++ [0w]))) (LENGTH (raw ++ [0w]))) /\
       in_revert_forward fn9 s9) \/
     (LENGTH Mcut < (MIN (LENGTH (markf (raw ++ [0w]))) (LENGTH (raw ++ [0w]))) /\
      ?F events stopped.
        N <= F /\ LIST_REL (\slot w. slot = NONE \/ slot = SOME w) Mcut (TAKE (LENGTH Mcut) raw) /\
        rooted_eval F (stage 7) levels (root_entry with vs_gas_readings := (TAKE (LENGTH Mcut) raw) ++
          (DROP (LENGTH Mcut) raw ++ [0w])) = (events,stopped) /\
        (!u. stopped <> OK u) /\ (!err. stopped <> Error err) /\
        run_blocks F (stage 7) root_sf (root_entry with vs_gas_readings := (TAKE (LENGTH Mcut) raw) ++
          (DROP (LENGTH Mcut) raw ++ [0w])) = stopped /\
        gas_events_blocks F (stage 7) root_sf (root_entry with vs_gas_readings := (TAKE (LENGTH Mcut) raw)
          ++ (DROP (LENGTH Mcut) raw ++ [0w])) = events /\
        (?extra. Ecut = events ++ extra))))) /\
  (!h. h < j ==>
    ?a e tf inst visit_state stk PG G tn oms om hs hist.
      EL h (TAKE j (dftGasFromListTraceDefs$trace_blocks [] 0 N (stage 8) root_tf root_entry)) =
        ((a,e,inst.inst_id),tf,inst,visit_state) /\
      EL h (q80::qs8) = JointConfig stk PG G tn tf inst visit_state oms om hs hist /\
      ?sf inc entry order res nrest bb bt ps xs ys rho in_state h0
        body_entry count front closed brest.
        FLOOKUP acts a = SOME (sf,tf,inc,entry,order,res,nrest) /\
        FLOOKUP blocks (a,e) =
          SOME (bb,bt,ps,xs,ys,rho,in_state,h0,body_entry,count,front,closed,brest) /\
        get_instruction bt visit_state.vs_inst_idx = SOME inst /\
        ((inv_memory_observation inst.inst_opcode \/ is_fallible inst \/
          inst.inst_opcode = INVOKE) /\ ~in_revert_forward tf visit_state ==>
          ?q z src_inst cuts levels Mcut Ecut Kcut mr er kr.
            src_inst = EL (LENGTH z)
              (DROP (phi_prefix_length bb.bb_instructions) bb.bb_instructions) /\
            ((IS_SOME body_entry /\ LENGTH ps <= visit_state.vs_inst_idx /\
              visit_state.vs_inst_idx - LENGTH ps < LENGTH rho /\
              q = EL (visit_state.vs_inst_idx - LENGTH ps) rho /\ q < LENGTH xs /\
              (a <> p \/ e <> d \/ visit_state <> s8 \/
                (EVERY (\i. ~is_terminator i.inst_opcode) (TAKE q xs) /\
                 (!r. r < q /\ (EL r xs).inst_opcode = INVOKE ==> MEM r (TAKE count rho)))) /\
              (inv_memory_observation inst.inst_opcode \/ is_fallible inst \/
                 inst.inst_opcode = INVOKE ==> EL q xs = inst) /\
              z = DROP (phi_prefix_length bb.bb_instructions) ps ++ TAKE q xs) \/
             (a = p /\ e = d /\ visit_state = s8 /\ body_entry = NONE /\
              visit_state.vs_inst_idx < LENGTH ps /\ q = 0 /\
              z = DROP (phi_prefix_length bb.bb_instructions) (TAKE visit_state.vs_inst_idx ps))) /\
            MAP (\(ai,ds,ei,qi,zi). ai) cuts =
              REVERSE (GENLIST (\i. DROP i a) (SUC (LENGTH a))) /\
            LENGTH cuts = LENGTH levels /\
            (!i ai ds ei qi zi.
              i < LENGTH cuts /\ EL i cuts = (ai,ds,ei,qi,zi) ==>
              ?sfi tfi inci enti orderi resi nresti bbi bti psi xsi ysi rhoi
                ini hi bei counti fronti closedi resti later.
                FLOOKUP acts ai = SOME (sfi,tfi,inci,enti,orderi,resi,nresti) /\
                FLOOKUP blocks (ai,ei) =
                  SOME (bbi,bti,psi,xsi,ysi,rhoi,ini,hi,bei,counti,fronti,closedi,resti) /\
                orderi = ds ++ ei::later /\
                (if SUC i = LENGTH cuts then
                  ai = a /\ ei = e /\ qi = q /\ zi = z
                else
                  ?cid h b0 done_at_call child_entry ret.
                    EL (SUC i) (MAP (\(aj,djs,ej,qj,zj). aj) cuts) = (ei,cid)::ai /\
                    FLOOKUP calls (ai,ei,cid) =
                      SOME (qi,h,b0,done_at_call,child_entry,ret) /\
                    qi < LENGTH xsi /\ (EL qi xsi).inst_id = cid /\
                    zi = DROP (phi_prefix_length bbi.bb_instructions) psi ++ TAKE qi xsi /\
                    EVERY (\x. ~is_terminator x.inst_opcode) (TAKE qi xsi) /\
                    (!r. r < qi /\ (EL r xsi).inst_opcode = INVOKE ==>
                      MEM r done_at_call)) /\
                EL i levels =
                  (sfi,
                   MAP (\f.
                     (FST (THE (FLOOKUP blocks (ai,f))),f,
                      DROP (phi_prefix_length
                        (FST (THE (FLOOKUP blocks (ai,f)))).bb_instructions)
                        (FST (THE (FLOOKUP blocks (ai,f)))).bb_instructions)) ds ++
                     [(bbi,ei,zi)],
                   if SUC i = LENGTH cuts then NONE else SOME (EL qi xsi))) /\
            Mcut = FLAT (MAP (\(ai,ds,ei,qi,zi).
              FLAT (MAP (\f. FLAT (THE (FLOOKUP ms_tab (ai,f)))) ds) ++
              FLAT (TAKE qi (THE (FLOOKUP ms_tab (ai,ei))))) cuts) /\
            Ecut = FLAT (MAP (\(ai,ds,ei,qi,zi).
              FLAT (MAP (\f. FLAT (THE (FLOOKUP es_tab (ai,f)))) ds) ++
              FLAT (TAKE qi (THE (FLOOKUP es_tab (ai,ei))))) cuts) /\
            Kcut = FLAT (MAP (\(ai,ds,ei,qi,zi).
              FLAT (MAP (\f. FLAT (THE (FLOOKUP ks_tab (ai,f)))) ds) ++
              FLAT (TAKE qi (THE (FLOOKUP ks_tab (ai,ei))))) cuts) /\
            raw_slots = Mcut ++ mr /\ sites = Ecut ++ er /\ (FLAT (MAP (\e. FLAT (THE (FLOOKUP ks_tab
              ([],e)))) (FST (SND (SND (SND (SND (THE (FLOOKUP acts []))))))))) = Kcut ++ kr /\
            LENGTH Mcut = LENGTH Ecut /\ LENGTH Mcut = LENGTH Kcut /\
            (!F gs tail.
              N <= F /\
              LIST_REL (\slot w. slot = NONE \/ slot = SOME w) Mcut gs ==>
              (?extra. Ecut = FST (rooted_eval F (stage 7) levels
                (root_entry with vs_gas_readings := gs ++ tail)) ++ extra) /\
              (case SND (rooted_eval F (stage 7) levels (root_entry with vs_gas_readings := gs ++ tail)) of
                OK u =>
                  FST (rooted_eval F (stage 7) levels
                    (root_entry with vs_gas_readings := gs ++ tail)) = Ecut /\
                  u.vs_gas_readings = tail /\
                  (?before after.
                    dftGasFromListTraceDefs$trace_blocks [] 0 F (stage 7) root_sf
                      (root_entry with vs_gas_readings := gs ++ tail) =
                      before ++ [((a,e,(EL (LENGTH z)
                        (DROP (phi_prefix_length bb.bb_instructions)
                          bb.bb_instructions)).inst_id),sf,
                        EL (LENGTH z) (DROP (phi_prefix_length bb.bb_instructions)
                          bb.bb_instructions),u)] ++ after /\
                    dftGasFromListTraceDefs$trace_gas before = ZIP (Kcut,gs)) /\
                  (!tail'. rooted_eval F (stage 7) levels
                    (root_entry with vs_gas_readings := gs ++ tail') =
                      (Ecut,OK (u with vs_gas_readings := tail'))) /\
                  (body_entry = NONE ==>
                    u with vs_gas_readings := visit_state.vs_gas_readings = visit_state) /\
                  (a = p /\ e = d /\ IS_SOME body_entry /\
                   inv_memory_observation inst.inst_opcode /\ EL q xs = inst ==>
                    (!op. MEM op inst.inst_operands ==>
                      eval_operand op u = eval_operand op visit_state) /\
                    u.vs_initial_fmp = visit_state.vs_initial_fmp)
              | stopped =>
                  run_blocks F (stage 7) root_sf
                    (root_entry with vs_gas_readings := gs ++ tail) = stopped /\
                  gas_events_blocks F (stage 7) root_sf
                    (root_entry with vs_gas_readings := gs ++ tail) =
                      FST (rooted_eval F (stage 7) levels
                        (root_entry with vs_gas_readings := gs ++ tail)))) /\
            (!F gs tail n u.
              N <= F /\ LIST_REL (\slot w. slot = NONE \/ slot = SOME w) Mcut gs /\
              LENGTH Mcut < n /\
              mem_inv (\ctx src_fn src_inst src_state.
                gas_cut n (root_entry with vs_gas_readings := gs ++ tail) src_state ==>
                  static_mem_ok cpl.cp_max_static_eom ctx src_fn src_inst src_state)
                (stage 7) (root_entry with vs_gas_readings := gs ++ tail) /\
              rooted_eval F (stage 7) levels (root_entry with vs_gas_readings := gs ++ tail) =
                (Ecut,OK u) ==>
              static_mem_ok cpl.cp_max_static_eom (stage 7) sf src_inst u /\
              ~in_revert_forward sf u /\
              (inv_memory_observation src_inst.inst_opcode ==>
                (!op. MEM op src_inst.inst_operands ==> eval_operand op u = eval_operand op visit_state) /\
                u.vs_initial_fmp = visit_state.vs_initial_fmp)) /\
  (!raw F u.
    LIST_REL (\slot w. slot = NONE \/ slot = SOME w) raw_slots raw ==>

    N <= F /\ LENGTH Mcut < (MIN (LENGTH (markf (raw ++ [0w]))) (LENGTH (raw ++ [0w]))) /\
    rooted_eval F (stage 7) levels (root_entry with vs_gas_readings := (TAKE (LENGTH Mcut) raw) ++ (DROP
      (LENGTH Mcut) raw ++ [0w])) = (Ecut,OK u) ==>
    raw_reachable (root_entry with vs_gas_readings := (TAKE (LENGTH Mcut) raw) ++ (DROP (LENGTH Mcut) raw
      ++ [0w])) (stage 7) sf src_inst u /\ gas_cut (MIN (LENGTH (markf (raw ++ [0w]))) (LENGTH (raw ++
      [0w]))) (root_entry with vs_gas_readings := (TAKE (LENGTH Mcut) raw) ++ (DROP (LENGTH Mcut) raw ++
      [0w])) u /\
    lowered_mem_fact cpl.cp_max_static_eom (stage 7) sf src_inst u /\
    u.vs_gas_readings = (DROP (LENGTH Mcut) raw ++ [0w]) /\
    (fin = asm_opt_finalizer ==>
      inst_dload_in_section src_inst u /\
      code_end_offset_ok (\ctx fn i s. fn = sf /\ i = src_inst /\ s = u) (stage 7)) /\
    (~in_revert_forward tf visit_state ==> ~in_revert_forward sf u) /\
    (inv_memory_observation inst.inst_opcode ==>
      (!op. MEM op inst.inst_operands ==> eval_operand op u = eval_operand op visit_state) /\
      u.vs_initial_fmp = visit_state.vs_initial_fmp))))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  mp_tac focus_source_cut_provider >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (CONJUNCTS_THEN2 (mk_asm "current")
    (CONJUNCTS_THEN2 (mk_asm "history") (mk_asm "marks"))) >>
  reverse conj_tac >- asm "history" ACCEPT_TAC >>
  asm_x "current" reuse_witnesses >>
  ntac 3 (conj_tac >- first_assum ACCEPT_TAC) >>
  disch_then (fn gate => first_x_assum (fn th => mp_tac (MATCH_MP th gate))) >>
  disch_then reuse_witnesses >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  Cases_on `MIN (LENGTH (markf (raw ++ [0w]))) (LENGTH (raw ++ [0w])) <= LENGTH Mcut`
  >- (disj2_tac >> disj1_tac >> first_assum ACCEPT_TAC) >>
  qpat_assum `~(MIN (LENGTH (markf (raw ++ [0w]))) (LENGTH (raw ++ [0w])) <= LENGTH Mcut)`
    (assume_tac o REWRITE_RULE [NOT_LESS_EQUAL]) >>
  Cases_on `in_revert_forward fn9 s9`
  >- (disj2_tac >> disj2_tac >> disj1_tac >> conj_tac >> first_assum ACCEPT_TAC) >>
  disj1_tac >>
  asm_x "marks" (qspec_then `raw` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then strip_assume_tac >>
  irule focus_current_witness_guard >>
  qpat_assum `cfg_norm_joint_cursors _ _ _ _ _` (irule_at Any) >>
  qhdtm_assum `dft_focus_packet_rel` (irule_at Any) >>
  qpat_assum `FLOOKUP acts p = SOME _` (irule_at Any) >>
  qpat_assum `FLOOKUP blocks (p,d) = SOME _` (irule_at Any) >>
  qpat_assum `_ <= LENGTH (gas_events_blocks f7 _ _ _)` (irule_at Any) >>
  qexistsl [`z`,`vs0`,`src_inst`,`q`,`nm`,`mr`,`levels`,`lbl7`,`es0`,`Mcut`,`Ecut`] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (qpat_assum `stage 9 = out.po_unit.cu_context` SUBST1_TAC >>
      first_assum ACCEPT_TAC)
  >- (map_every qx_gen_tac [`fuel`,`readings`,`tail`] >> disch_tac >>
      qpat_assum `!F gs tail. N <= F /\ LIST_REL _ Mcut gs ==> _`
        (qspecl_then [`fuel`,`readings`,`tail`] mp_tac) >>
      (impl_tac >- first_assum ACCEPT_TAC) >>
      Cases_on `SND (rooted_eval fuel (stage 7) levels
        (root_entry with vs_gas_readings := readings ++ tail))` >>
      simp[NoAsms] >> strip_tac >> rpt conj_tac >> first_assum ACCEPT_TAC)
  >- (map_every qx_gen_tac [`fuel`,`u`] >>
      disch_then (map_every assume_tac o CONJUNCTS) >>
      qpat_assum `!raw F u. LIST_REL _ raw_slots raw ==> _`
        (qspecl_then [`raw`,`fuel`,`u`] mp_tac) >>
      (impl_tac >- first_assum ACCEPT_TAC) >>
      (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
      strip_tac >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      strip_tac >> first_x_assum drule >> simp[])
  >- (qpat_assum `!k. k <= 9 ==> o1_ctx_shape (stage k) /\ _`
        (qspec_then `8` mp_tac) >>
      simp[NoAsms,o1_ctx_shape_def])
  >- (qpat_assum `(IS_SOME body_entry /\ _) \/ (p = p /\ _)`
        (DISJ_CASES_THEN (map_every assume_tac o CONJUNCTS)) >| [
      disj1_tac >> rpt conj_tac >> first_assum ACCEPT_TAC,
      disj2_tac >> first_assum ACCEPT_TAC])
QED
