(* Conditional origin transport: the execution and pointer layers discharge
   the operation equations at the join, not in this companion theory. *)
Theory fragGasOriginFmpTransport
Ancestors
  fragGasOriginPtr fragGasPathPtr ptrDiscipline fragFuel instIdxIndep unitShapeDefs ctxLookupAgreeHelpers
  venomExecProofs gasEvents venomInst venomState list fragGasOrigin fragExec
  venomExecSemantics rawFmpTransportDefs

Theorem gas_events_fmp_update_under_execution:
  (!fuel ctx inst s p i e.
     EVERY (\fn. EVERY (\j. raw_opcode_ok j.inst_opcode /\
       j.inst_opcode <> DALLOCA) (fn_insts fn)) ctx.ctx_functions /\
     raw_opcode_ok inst.inst_opcode /\ inst.inst_opcode <> DALLOCA ==>
     raw_fmp_result_rel p i e (step_inst fuel ctx inst s)
       (step_inst fuel ctx inst
         (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>))) /\
  (!fuel ctx bb s p i e.
     EVERY (\fn. EVERY (\j. raw_opcode_ok j.inst_opcode /\
       j.inst_opcode <> DALLOCA) (fn_insts fn)) ctx.ctx_functions /\
     EVERY (\j. raw_opcode_ok j.inst_opcode /\ j.inst_opcode <> DALLOCA)
       bb.bb_instructions ==>
     raw_fmp_result_rel p i e (exec_block fuel ctx bb s)
       (exec_block fuel ctx bb
         (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>))) /\
  (!s xs p i e.
     eval_phis (s with <|vs_fmp := p; vs_initial_fmp := i;
       vs_call_entry_fmp := e|>) xs =
     exec_result_map (\t. t with <|vs_fmp := p; vs_initial_fmp := i;
       vs_call_entry_fmp := e|>) (eval_phis s xs)) /\
  (!fn args s p i e.
     setup_callee fn args
       (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>) =
     OPTION_MAP (\t. t with <|vs_fmp := p; vs_initial_fmp := i;
       vs_call_entry_fmp := p|>) (setup_callee fn args s)) /\
  (!ops s p i e.
     eval_operands ops (s with <|vs_fmp := p; vs_initial_fmp := i;
       vs_call_entry_fmp := e|>) = eval_operands ops s) ==>
  (!fuel ctx owner inst s.
     EVERY (\fn. EVERY (\j. raw_opcode_ok j.inst_opcode /\
       j.inst_opcode <> DALLOCA) (fn_insts fn)) ctx.ctx_functions /\
     raw_opcode_ok inst.inst_opcode /\ inst.inst_opcode <> DALLOCA ==>
     !p i e. gas_events_step fuel ctx owner inst
       (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>) =
       gas_events_step fuel ctx owner inst s) /\
  (!fuel ctx owner bb s.
     EVERY (\fn. EVERY (\j. raw_opcode_ok j.inst_opcode /\
       j.inst_opcode <> DALLOCA) (fn_insts fn)) ctx.ctx_functions /\
     EVERY (\j. raw_opcode_ok j.inst_opcode /\ j.inst_opcode <> DALLOCA)
       bb.bb_instructions ==>
     !p i e. gas_events_block fuel ctx owner bb
       (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>) =
       gas_events_block fuel ctx owner bb s) /\
  (!fuel ctx fn s.
     EVERY (\fn. EVERY (\j. raw_opcode_ok j.inst_opcode /\
       j.inst_opcode <> DALLOCA) (fn_insts fn)) ctx.ctx_functions /\
     EVERY (\j. raw_opcode_ok j.inst_opcode /\ j.inst_opcode <> DALLOCA)
       (fn_insts fn) ==>
     !p i e. gas_events_blocks fuel ctx fn
       (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>) =
       gas_events_blocks fuel ctx fn s)
Proof
  strip_tac >> ho_match_mp_tac gas_events_defs_ind >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >> strip_tac >> rpt gen_tac >>
      simp[gas_events_step_def] >>
      Cases_on `inst.inst_opcode = GAS` >> simp[] >>
      Cases_on `inst.inst_opcode = INVOKE` >> simp[] >>
      Cases_on `decode_invoke inst` >> gvs[] >>
      PairCases_on `x` >> gvs[] >>
      Cases_on `lookup_function x0 ctx.ctx_functions` >> gvs[] >>
      Cases_on `eval_operands x1 s` >> gvs[] >>
      Cases_on `setup_callee x x' s` >> gvs[] >>
      first_x_assum irule >> simp[] >>
      drule lookup_function_MEM >> strip_tac >>
      qpat_x_assum `EVERY _ ctx.ctx_functions` mp_tac >>
      simp[EVERY_MEM] >> metis_tac[])
  >- (rpt gen_tac >> strip_tac >> strip_tac >> rpt gen_tac >>
      once_rewrite_tac[gas_events_block_def] >> simp[] >>
      Cases_on `get_instruction bb s.vs_inst_idx` >> gvs[] >>
      rename1 `get_instruction bb s.vs_inst_idx = SOME inst` >>
      `raw_opcode_ok inst.inst_opcode /\ inst.inst_opcode <> DALLOCA` by
        (gvs[get_instruction_def, EVERY_EL] >> metis_tac[]) >>
      qpat_assum `!fuel ctx inst s p i e. _ ==> raw_fmp_result_rel _ _ _ _ _`
        (qspecl_then [`fuel`, `ctx`, `inst`, `s`, `p`, `i`, `e`] assume_tac) >>
      Cases_on `step_inst fuel ctx inst s` >>
      gvs[] >>
      Cases_on `is_terminator inst.inst_opcode` >> simp[] >>
      first_x_assum irule >> simp[])
  >> rpt gen_tac >> strip_tac >> strip_tac >> rpt gen_tac >>
  Cases_on `fuel` >> once_rewrite_tac[gas_events_blocks_def] >> simp[] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >> gvs[] >>
  rename1 `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` >>
  `EVERY (\j. raw_opcode_ok j.inst_opcode /\ j.inst_opcode <> DALLOCA)
      bb.bb_instructions` by
    (drule lookup_block_MEM >> strip_tac >>
     qpat_x_assum `EVERY _ (fn_insts fn)` mp_tac >>
     rewrite_tac[fn_insts_def, fn_insts_EVERY_block] >>
     simp[EVERY_MEM] >> metis_tac[]) >>
  Cases_on `eval_phis s bb.bb_instructions` >>
  gvs[exec_result_map_def] >>
  qpat_assum `!fuel ctx bb s p i e. _ ==> raw_fmp_result_rel _ _ _ (run_block_non_phis _ _ _ _) _`
    (qspecl_then [`n`, `ctx`, `bb`,
      `v with vs_inst_idx := phi_prefix_length bb.bb_instructions`, `p`, `i`, `e`]
      (assume_tac o SRULE [])) >>
  Cases_on `exec_block n ctx bb
    (v with vs_inst_idx := phi_prefix_length bb.bb_instructions)` >>
  gvs[] >>
  Cases_on `v'.vs_halted` >> simp[] >>
  first_x_assum irule >> simp[]
QED


Theorem raw_fmp_result_rel_exit:
  raw_fmp_result_rel p i e r r' /\ exit_result r ==> exit_result r'
Proof
  Cases_on `r` >> simp[exit_result_def] >> rpt strip_tac >> simp[exit_result_def]
QED

Theorem gas_origin_edge_fmp_update_under_transport:
  (!fuel inst s. MEM inst (fn_insts fn) ==>
     raw_fmp_result_rel p i e (step_inst fuel ctx inst s)
       (step_inst fuel ctx inst
         (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>))) /\
  (!s xs. eval_phis
       (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>) xs =
     exec_result_map (\t. t with <|vs_fmp := p; vs_initial_fmp := i;
       vs_call_entry_fmp := e|>) (eval_phis s xs)) /\
  (!fuel inst s. MEM inst (fn_insts fn) ==>
     gas_events_step fuel ctx fn.fn_name inst
       (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>) =
     gas_events_step fuel ctx fn.fn_name inst s) /\
  (!fuel inst s. MEM inst (fn_insts fn) /\ mem_safe_step fuel ctx inst s ==>
     mem_safe_step fuel ctx inst
       (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>)) ==>
  !s marks r. gas_origin_edge memory explicit ctx fn s marks r ==>
    ?r'. raw_fmp_result_rel p i e r r' /\
      gas_origin_edge memory explicit ctx fn
        (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>) marks r'
Proof
  strip_tac >> rpt gen_tac >> rewrite_tac[gas_origin_edge_def] >>
  strip_tac >>
  `MEM inst (fn_insts fn)` by
    metis_tac[lookup_block_get_instruction_fn_insts] >>
  `raw_fmp_result_rel p i e middle
    (step_inst fuel ctx inst
      (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>))` by
    metis_tac[] >>
  `memory ==> revert_forward_at bb s.vs_inst_idx \/
    mem_safe_step fuel ctx inst
      (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>)` by
    metis_tac[] >>
  gvs[]
  >- (qexists_tac `fuel` >> simp[])
  >- (qexists_tac `Halt (t with <|vs_fmp := p; vs_initial_fmp := i;
        vs_call_entry_fmp := e|>)` >> simp[] >>
      (conj_tac >- (qexists_tac `e` >> simp[])) >>
      qexists_tac `fuel` >> simp[])
  >- (qexists_tac `fuel` >> simp[exec_result_map_def])
  >- (qexists_tac `fuel` >> simp[jump_to_def] >>
      disj2_tac >> disj1_tac >> qexists_tac `lbl` >> simp[]) >>
  qexists_tac `venomExecSemantics$step_inst fuel ctx inst
    (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>)` >>
  (conj_asm1_tac >- simp[]) >>
  qexists_tac `fuel` >> simp[] >>
  disj2_tac >> disj2_tac >> disj2_tac >> disj2_tac >>
  metis_tac[raw_fmp_result_rel_exit]
QED

Theorem gas_origin_path_fmp_update_under_transport:
  (!s marks r. gas_origin_edge memory explicit ctx fn s marks r ==>
     ?r'. raw_fmp_result_rel p i e r r' /\
       gas_origin_edge memory explicit ctx fn
         (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>) marks r') ==>
  !s marks r. gas_origin_path memory explicit ctx fn s marks r ==>
    ?r'. raw_fmp_result_rel p i e r r' /\
      gas_origin_path memory explicit ctx fn
        (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>) marks r'
Proof
  strip_tac >>
  qsuff_tac `!memory' explicit' ctx' fn' s marks r.
    gas_origin_path memory' explicit' ctx' fn' s marks r ==>
    memory' = memory /\ explicit' = explicit /\ ctx' = ctx /\ fn' = fn ==>
    ?r'. raw_fmp_result_rel p i e r r' /\
      gas_origin_path memory explicit ctx fn
        (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>) marks r'`
  >- metis_tac[] >>
  ho_match_mp_tac gas_origin_path_ind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac >> strip_tac >> gvs[]
  >- (irule (cj 1 gas_origin_path_rules) >> simp[])
  >- (qpat_x_assum `!s marks r. gas_origin_edge _ _ _ _ _ _ _ ==> _`
        drule >> strip_tac >> gvs[] >>
      metis_tac[cj 2 gas_origin_path_rules]) >>
  qpat_x_assum `!s marks r. gas_origin_edge _ _ _ _ _ _ _ ==> _`
    drule >> strip_tac >>
  metis_tac[cj 3 gas_origin_path_rules, raw_fmp_result_rel_exit]
QED

Theorem gas_origin_ptr_edge_fmp_update_under_transport:
  (!fuel inst s. MEM inst (fn_insts fn) ==>
     raw_fmp_result_rel p i e (step_inst fuel ctx inst s)
       (step_inst fuel ctx inst
         (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>))) /\
  (!s xs. eval_phis
       (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>) xs =
     exec_result_map (\t. t with <|vs_fmp := p; vs_initial_fmp := i;
       vs_call_entry_fmp := e|>) (eval_phis s xs)) /\
  (!fuel inst s. MEM inst (fn_insts fn) ==>
     gas_events_step fuel ctx fn.fn_name inst
       (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>) =
     gas_events_step fuel ctx fn.fn_name inst s) /\
  (!fuel inst s. MEM inst (fn_insts fn) /\ mem_safe_step fuel ctx inst s ==>
     mem_safe_step fuel ctx inst
       (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>)) /\
  (!fuel inst s G tn. MEM inst (fn_insts fn) /\
     ptr_safe_step D lo fuel ctx fn PG G tn inst s ==>
     ptr_safe_step D lo fuel ctx fn PG G tn inst
       (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>)) /\
  (!fuel inst s G tn. MEM inst (fn_insts fn) ==>
     ghost_step fuel ctx PG G tn inst
       (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>) =
     ghost_step fuel ctx PG G tn inst s) ==>
  !s G tn marks r G' tn'.
    gas_origin_ptr_edge (D,lo,explicit,ctx,fn,PG) (s,G,tn) marks (r,G',tn') ==>
    ?r'. raw_fmp_result_rel p i e r r' /\
      gas_origin_ptr_edge (D,lo,explicit,ctx,fn,PG)
        (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>,G,tn)
        marks (r',G',tn')
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  drule gas_origin_ptr_edge_common_fuel >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (qx_choose_then `fuel` (qx_choose_then `bb` (qx_choose_then `inst`
      (qx_choose_then `middle` (REPEAT_TCL CONJUNCTS_THEN assume_tac)))))) >>
  qpat_x_assum `gas_origin_ptr_edge _ _ _ _` kall_tac >>
  `MEM inst (fn_insts fn)` by
    metis_tac[lookup_block_get_instruction_fn_insts] >>
  `raw_fmp_result_rel p i e middle
    (step_inst fuel ctx inst
      (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>))` by
    metis_tac[] >>
  (SUBGOAL_THEN
    ``revert_forward_at bb s.vs_inst_idx \/
      mem_safe_step fuel ctx inst
        (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>)``
    assume_tac >- metis_tac[]) >>
  `ptr_safe_step D lo fuel ctx fn PG G tn inst
      (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>)` by
    metis_tac[] >>
  `LENGTH (gas_events_step fuel ctx fn.fn_name inst s) =
    gas_count_step fuel ctx inst
      (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>)` by
    metis_tac[cj 1 gas_events_length] >>
  qpat_x_assum `(?t. _ /\ ~is_terminator _ /\ _) \/ _` mp_tac >>
  strip_tac >>
  gnvs[gas_origin_ptr_edge_def, gas_origin_edge_def, gas_path_ptr_edge_def]
  >- (conj_tac >> qexists_tac `fuel` >> simp[])
  >- (qexists_tac `Halt (t with <|vs_fmp := p; vs_initial_fmp := i;
        vs_call_entry_fmp := e|>)` >> simp[] >>
      (conj_tac >- (qexists_tac `e` >> simp[])) >>
      conj_tac >> qexists_tac `fuel` >> simp[])
  >- (conj_tac >> qexists_tac `fuel` >>
      simp[exec_result_map_def, entry_prov_def, entry_taint_vars_def])
  >- (conj_tac >> qexists_tac `fuel` >> simp[jump_to_def] >>
      metis_tac[]) >>
  qexists_tac `venomExecSemantics$step_inst fuel ctx inst
    (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>)` >>
  (conj_asm1_tac >- simp[]) >>
  `exit_result (step_inst fuel ctx inst
    (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>))` by
    (irule raw_fmp_result_rel_exit >> metis_tac[]) >>
  conj_tac >> qexists_tac `fuel` >> gnvs[]
QED

Theorem gas_origin_ptr_path_fmp_update_under_transport:
  (!s G tn marks r G' tn'.
     gas_origin_ptr_edge (D,lo,explicit,ctx,fn,PG) (s,G,tn) marks (r,G',tn') ==>
     ?r'. raw_fmp_result_rel p i e r r' /\
       gas_origin_ptr_edge (D,lo,explicit,ctx,fn,PG)
         (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>,G,tn)
         marks (r',G',tn')) ==>
  !s G tn marks r G' tn'.
    gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) marks (r,G',tn') ==>
    ?r'. raw_fmp_result_rel p i e r r' /\
      gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
        (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>,G,tn)
        marks (r',G',tn')
Proof
  strip_tac >>
  qsuff_tac `!cx st marks out. gas_origin_ptr_path cx st marks out ==>
    !s G tn r G' tn'.
      cx = (D,lo,explicit,ctx,fn,PG) /\ st = (s,G,tn) /\ out = (r,G',tn') ==>
      ?r'. raw_fmp_result_rel p i e r r' /\
        gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
          (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>,G,tn)
          marks (r',G',tn')`
  >- metis_tac[] >>
  ho_match_mp_tac gas_origin_ptr_path_ind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >> gvs[]
  >- (irule (cj 1 gas_origin_ptr_path_rules) >> simp[])
  >- (qpat_x_assum `!s G tn marks r G' tn'. gas_origin_ptr_edge _ _ _ _ ==> _`
        drule >> strip_tac >> gvs[] >>
      metis_tac[cj 2 gas_origin_ptr_path_rules]) >>
  qpat_x_assum `!s G tn marks r G' tn'. gas_origin_ptr_edge _ _ _ _ ==> _`
    drule >> strip_tac >>
  metis_tac[cj 3 gas_origin_ptr_path_rules, raw_fmp_result_rel_exit]
QED

Theorem gas_invoke_entry_fmp_update_under_transport:
  (!s xs p i e.
     eval_phis (s with <|vs_fmp := p; vs_initial_fmp := i;
       vs_call_entry_fmp := e|>) xs =
     exec_result_map (\t. t with <|vs_fmp := p; vs_initial_fmp := i;
       vs_call_entry_fmp := e|>) (eval_phis s xs)) /\
  (!fn args s p i e.
     setup_callee fn args
       (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>) =
     OPTION_MAP (\t. t with <|vs_fmp := p; vs_initial_fmp := i;
       vs_call_entry_fmp := p|>) (setup_callee fn args s)) /\
  (!ops s p i e.
     eval_operands ops (s with <|vs_fmp := p; vs_initial_fmp := i;
       vs_call_entry_fmp := e|>) = eval_operands ops s) ==>
  !ctx fn s callee entered p i e.
    gas_invoke_entry (ctx,fn) s callee entered ==>
    gas_invoke_entry (ctx,fn)
      (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>)
      callee
      (entered with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := p|>)
Proof
  strip_tac >> rpt gen_tac >> rewrite_tac[fragGasFocusTheory.gas_invoke_entry_def] >>
  strip_tac >> simp[] >>
  qexists_tac
    `phi_state with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := p|>` >>
  simp[exec_result_map_def] >>
  qpat_x_assum `!s xs p i e. eval_phis _ _ = _`
    (qspecl_then [`setup`, `first.bb_instructions`, `p`, `i`, `p`] mp_tac) >>
  simp[exec_result_map_def]
QED

Theorem gas_origin_ptr_focus_fmp_update_under_transport:
  (!fn PG s G tn marks r G' tn' p i e.
     MEM fn ctx.ctx_functions /\
     gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) marks (r,G',tn') ==>
     ?r'. raw_fmp_result_rel p i e r r' /\
       gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG)
         (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>,G,tn)
         marks (r',G',tn')) /\
  (!fn s callee entered p i e.
     gas_invoke_entry (ctx,fn) s callee entered ==>
     gas_invoke_entry (ctx,fn)
       (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>)
       callee
       (entered with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := p|>)) /\
  (!fn G tn inst s p i e.
     MEM fn ctx.ctx_functions /\ MEM inst (fn_insts fn) /\
     inst.inst_opcode = INVOKE /\ ptr_inst_ok D lo 0 ctx fn G tn inst s ==>
     ptr_inst_ok D lo 0 ctx fn G tn inst
       (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>)) ==>
  !fn PG s G tn marks leaf leaf_pg leaf_g leaf_tn finish p i e.
    MEM fn ctx.ctx_functions /\
    gas_origin_ptr_focus (D,lo,explicit,ctx,fn,PG) (s,G,tn)
      marks (leaf,leaf_pg,leaf_g,leaf_tn,finish) ==>
    ?finish'. gas_origin_ptr_focus (D,lo,explicit,ctx,fn,PG)
      (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>,G,tn)
      marks (leaf,leaf_pg,leaf_g,leaf_tn,finish')
Proof
  strip_tac >>
  qsuff_tac `!cx st marks out. gas_origin_ptr_focus cx st marks out ==>
    !fn PG s G tn leaf leaf_pg leaf_g leaf_tn finish p i e.
      cx = (D,lo,explicit,ctx,fn,PG) /\ st = (s,G,tn) /\
      out = (leaf,leaf_pg,leaf_g,leaf_tn,finish) /\ MEM fn ctx.ctx_functions ==>
      ?finish'. gas_origin_ptr_focus (D,lo,explicit,ctx,fn,PG)
        (s with <|vs_fmp := p; vs_initial_fmp := i; vs_call_entry_fmp := e|>,G,tn)
        marks (leaf,leaf_pg,leaf_g,leaf_tn,finish')`
  >- metis_tac[] >>
  ho_match_mp_tac gas_origin_ptr_focus_ind >> rpt conj_tac >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >> gvs[]
  >- (qpat_x_assum `!fn PG s G tn marks r G' tn' p i e. _`
        drule_all >> disch_then (qspecl_then [`p`, `i`, `e`] strip_assume_tac) >>
      gvs[] >> metis_tac[cj 1 gas_origin_ptr_focus_rules])
  >- (qpat_x_assum `!fn PG s G tn marks r G' tn' p i e. _`
        drule_all >> disch_then (qspecl_then [`p`, `i`, `e`] strip_assume_tac) >>
      gvs[] >> metis_tac[cj 2 gas_origin_ptr_focus_rules]) >>
  qpat_x_assum `!fn s callee entered p i e. gas_invoke_entry _ _ _ _ ==> _` drule >>
  disch_then (qspecl_then [`p`, `i`, `e`] (assume_tac o SRULE [])) >>
  `MEM inst (fn_insts fn)` by
    metis_tac[lookup_block_get_instruction_fn_insts] >>
  qpat_x_assum `!fn G tn inst s p i e. MEM _ _ /\ _ ==> _` drule_all >>
  disch_then (qspecl_then [`p`, `i`, `e`] (assume_tac o SRULE [])) >>
  `MEM callee ctx.ctx_functions` by
    (qpat_x_assum `gas_invoke_entry _ s _ _` mp_tac >>
     simp[fragGasFocusTheory.gas_invoke_entry_def] >>
     metis_tac[lookup_function_MEM]) >>
  qpat_x_assum `!p i e. _`
    (qspecl_then [`p`, `i`, `p`] mp_tac) >> simp[] >>
  disch_then (qx_choose_then `new_finish` assume_tac) >>
  qexists_tac `new_finish` >>
  irule (cj 3 gas_origin_ptr_focus_rules) >> simp[] >> metis_tac[]
QED
