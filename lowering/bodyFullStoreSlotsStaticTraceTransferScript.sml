Theory bodyFullStoreSlotsStaticTraceTransfer
Ancestors
  fragGasOriginPtr fragGasOrigin fragGasPathPtr
  exprSimAbiGasBridge exprSimAbiDecodeSetupObserve fragExec ptrSafeRun ptrDiscipline
  gasEvents gasCount memSafeRun venomExecSemantics venomState venomInst
  contextCodegenRel codegenRel unitTransformDefs list finite_map arithmetic

Theorem store_slots_observer_readonly_transfer:
  cs_extends sa sb /\ fn_has_code sa sb func /\ frag_gas_free sa sb /\
  (a.vs_current_bb,a.vs_inst_idx) IN frag_observer_region sa sb /\
  (a.vs_current_bb,a.vs_inst_idx) <> frag_observer_cut sb /\
  lookup_block a.vs_current_bb (frag_observer sa sb func id).fn_blocks = SOME bb /\
  get_instruction bb a.vs_inst_idx = SOME inst /\
  MEM inst.inst_opcode [ASSIGN;ADD;MUL;EQ;LT;ISZERO;SHR;MLOAD;JMP;JNZ] /\
  gas_origin_ptr_edge (D,lo,explicit,ctx,frag_observer sa sb func id,PG)
    (a,Ga,tna) [] (OK b,Gb,tnb) ==>
  gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (a,Ga,tna) [] (OK b,Gb,tnb)
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_all frag_observer_instruction_agrees >> strip_tac >>
  drule_all frag_observer_off_cut_opcodes >> strip_tac >>
  drule gas_origin_ptr_edge_common_fuel >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (qx_choose_then `fuel` (qx_choose_then `bb1` (qx_choose_then `i`
      (qx_choose_then `middle` (REPEAT_TCL CONJUNCTS_THEN assume_tac)))))) >>
  gnvs[Excl "MEM"] >>
  `~revert_forward_at bb a.vs_inst_idx` by
    (strip_tac >> drule_all revert_forward_at_opcode >> gvs[]) >>
  `~in_revert_forward (frag_observer sa sb func id) a` by
    (gvs[in_revert_forward_def]) >>
  `ptr_safe_step D lo fuel ctx func PG Ga tna i a` by
    (qpat_x_assum `ptr_safe_step _ _ _ _ _ _ _ _ _ _` mp_tac >>
     qpat_x_assum `_ = ASSIGN \/ _` mp_tac >> strip_tac >>
     simp[ptr_safe_step_def, ptr_inst_ok_def, access_ok_def, taint_ok_def,
          source_memory_read_ranges_def, source_memory_write_ranges_def] >>
     metis_tac[]) >>
  `gas_events_step fuel ctx func.fn_name i a = [] /\
   gas_count_step fuel ctx i a = 0` by
    (qpat_x_assum `_ = ASSIGN \/ _` mp_tac >> strip_tac >>
     simp[gas_events_step_def, gas_count_step_def]) >>
  `(?t. step_inst fuel ctx i a = OK t /\ ~is_terminator i.inst_opcode /\
         ~t.vs_halted /\ b = t with vs_inst_idx := SUC a.vs_inst_idx /\
         (Gb,tnb) = ghost_step fuel ctx PG Ga tna i a) \/
   (?lbl. is_terminator i.inst_opcode /\
     step_inst fuel ctx i a = OK (jump_to lbl a) /\ b = jump_to lbl a /\
     Gb = Ga /\ tnb = tna)` by
    (qpat_x_assum `(?t. step_inst _ _ _ _ = OK t /\ ~is_terminator _ /\ _) \/ _`
       strip_assume_tac
     >- metis_tac[]
     >- suspend "entry"
     >- (disj2_tac >> qexists_tac `lbl` >> gvs[]) >>
     qpat_x_assum `exit_result _` mp_tac >>
     qpat_x_assum `OK _ = step_inst _ _ _ _` (fn th => rewrite_tac[GSYM th]) >>
     simp[exit_result_def]) >>
  qpat_x_assum `(?t. step_inst _ _ _ _ = OK t /\ ~is_terminator _ /\ _) \/ _`
    kall_tac >>
  rewrite_tac[gas_origin_ptr_edge_def, gas_origin_edge_def, gas_path_ptr_edge_def] >>
  conj_tac >> simp[] >> qexists_tac `fuel` >> simp[] >> metis_tac[]
QED

Resume store_slots_observer_readonly_transfer[entry]:
  `MEM i.inst_opcode [JMP;JNZ;DJMP]` by gvs[is_terminator_def] >>
  `t.vs_current_bb <> sa.cs_current_bb` by
    (irule frag_observer_jump_no_reentry >>
     qexistsl_tac [`i`,`a`] >> metis_tac[step_inst_non_invoke]) >>
  `phi_prefix_length target.bb_instructions = 0` by
    metis_tac[abi_decode_observer_nonentry_phi_zero] >>
  `entered = t` by metis_tac[eval_phis_no_phi, exec_result_11] >>
  `entry_prov (frag_observer sa sb func id) t Ga = Ga /\
   entry_taint_vars (frag_observer sa sb func id) t tna = tna` by
    (simp[entry_prov_def, entry_taint_vars_def] >>
     Cases_on `target.bb_instructions` >>
     gvs[phi_prefix_length_def, phis_prov_def, phis_taint_def] >>
     rename1 `(if headinst.inst_opcode = PHI then _ else _) = 0` >>
     Cases_on `headinst.inst_opcode = PHI` >> gvs[]) >>
  `?lbl. t = jump_to lbl a` by
    (qpat_x_assum `step_inst fuel ctx i a = OK t` mp_tac >>
     qpat_x_assum `_ = ASSIGN \/ _` mp_tac >> strip_tac >>
     gvs[is_terminator_def] >>
     simp[step_inst_non_invoke, step_inst_base_opcode_eqs,
          AllCaseEqs()] >> metis_tac[]) >>
  disj2_tac >> qexists_tac `lbl` >> gvs[jump_to_def]
QED

Finalise store_slots_observer_readonly_transfer
