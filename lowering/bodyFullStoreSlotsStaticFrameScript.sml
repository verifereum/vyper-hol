Theory bodyFullStoreSlotsStaticFrame
Ancestors
  fragGasOriginPtr fragExec ptrSafeRun ptrDiscipline decoderGhostFramePtr
  stmtSimStoreCopy typedCopyArrayPtr venomExecSemantics venomState venomInst
  contextCodegenRel codegenRel unitTransformDefs list finite_map arithmetic

Theorem slots_readonly_machine_frame[local]:
  MEM i.inst_opcode [ASSIGN; ADD; MUL; EQ; LT; ISZERO; SHR; MLOAD; JMP; JNZ] /\
  step_inst fuel ctx i s = OK u ==>
  store_copy_normalize sbase u = store_copy_normalize sbase s /\
  (!x. ~MEM x i.inst_outputs ==> lookup_var x u = lookup_var x s)
Proof
  simp[MEM] >> strip_tac >>
  gvs[step_inst_non_invoke, step_inst_base_ASSIGN, step_inst_base_ADD,
      step_inst_base_MUL, step_inst_base_EQ, step_inst_base_LT,
      step_inst_base_ISZERO, step_inst_base_SHR, step_inst_base_MLOAD,
      step_inst_base_JMP, step_inst_base_JNZ,
      exec_pure1_def, exec_pure2_def, exec_read1_def, AllCaseEqs()] >>
  simp[store_copy_normalize_def, update_var_def, jump_to_def,
       lookup_var_def, FLOOKUP_UPDATE] >> metis_tac[]
QED

Theorem slots_readonly_ghost_frame[local]:
  MEM i.inst_opcode [ASSIGN; ADD; MUL; EQ; LT; ISZERO; SHR; MLOAD; JMP; JNZ] /\
  step_inst fuel ctx i s = OK u ==>
  (SND (ghost_step fuel ctx PG G tn i s)).t_mem = tn.t_mem /\
  (SND (ghost_step fuel ctx PG G tn i s)).t_imm = tn.t_imm /\
  (SND (ghost_step fuel ctx PG G tn i s)).t_stor = tn.t_stor /\
  (SND (ghost_step fuel ctx PG G tn i s)).t_trans = tn.t_trans /\
  (!x. ~MEM x i.inst_outputs ==>
    FLOOKUP (FST (ghost_step fuel ctx PG G tn i s)) x = FLOOKUP G x /\
    op_taint (SND (ghost_step fuel ctx PG G tn i s)) (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  drule_all slots_readonly_machine_frame >>
  disch_then (qspec_then `s` strip_assume_tac) >>
  `u.vs_allocas = s.vs_allocas /\ u.vs_fmp = s.vs_fmp` by
    (qpat_x_assum `store_copy_normalize _ _ = _` mp_tac >>
     simp[store_copy_normalize_def, venom_state_component_equality]) >>
  `written_taint tn i s = {}` by
    (gvs[MEM, written_taint_def] >> rpt (CASE_TAC >> simp[])) >>
  `new_site_bytes s u = {}` by
    (simp[new_site_bytes_def, FLOOKUP_DEF, pred_setTheory.EXTENSION] >>
     metis_tac[]) >>
  simp[ghost_step_def] >>
  `i.inst_opcode <> INVOKE` by gvs[MEM] >> simp[] >>
  `!x. ~MEM x i.inst_outputs ==>
     FLOOKUP (step_prov PG G i u) x = FLOOKUP G x /\
     op_taint (step_taint i s u tn) (Var x) = op_taint tn (Var x)` by
    metis_tac[step_prov_other_output, step_taint_other_output] >>
  simp[] >>
  gvs[MEM, step_taint_def, adopt_reset_def, mem_taint_def,
      step_writes_def, store_taint_def, imm_taint_def,
      source_memory_write_ranges_def, range_bytes_def]
QED

Theorem store_slots_readonly_edge_frame:
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME i /\
  MEM i.inst_opcode [ASSIGN; ADD; MUL; EQ; LT; ISZERO; SHR; MLOAD; JMP; JNZ] /\
  (!x. not_fresh_at sa x ==> ~MEM x i.inst_outputs) /\
  (!fuel mid target.
     step_inst fuel ctx i s = OK mid /\ is_terminator i.inst_opcode /\
     lookup_block mid.vs_current_bb func.fn_blocks = SOME target ==>
     phi_prefix_length target.bb_instructions = 0) /\
  gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,Gu,tnu) ==>
  (!sbase. store_copy_normalize sbase u = store_copy_normalize sbase s) /\
  (!x. not_fresh_at sa x ==>
     lookup_var x u = lookup_var x s /\ FLOOKUP Gu x = FLOOKUP G x /\
     op_taint tnu (Var x) = op_taint tn (Var x)) /\
  tnu.t_mem = tn.t_mem /\ tnu.t_imm = tn.t_imm /\
  tnu.t_stor = tn.t_stor /\ tnu.t_trans = tn.t_trans /\ ~u.vs_halted
Proof
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule gas_origin_ptr_edge_common_fuel >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (qx_choose_then `fuel` (qx_choose_then `bb1` (qx_choose_then `inst`
      (qx_choose_then `middle` (REPEAT_TCL CONJUNCTS_THEN assume_tac)))))) >>
  `?mid. middle = OK mid` by (gvs[exit_result_def] >> metis_tac[]) >>
  gnvs[Excl "MEM"] >>
  drule_all (SRULE[MEM] slots_readonly_machine_frame) >> strip_tac >>
  drule_all (SRULE[MEM] slots_readonly_ghost_frame) >>
  disch_then (qspecl_then [`tn`, `PG`, `G`] strip_assume_tac) >>
  Cases_on `ghost_step fuel ctx PG G tn i s` >> gnvs[Excl "MEM"] >>
  qpat_x_assum `_ = ASSIGN \/ _` kall_tac >>
  qpat_x_assum `_ \/ mem_safe_step _ _ _ _` kall_tac >>
  qpat_x_assum `~is_terminator _ /\ _ \/ _` mp_tac >> strip_tac >>
  gvs[exit_result_def]
  >- (simp[lookup_var_def] >> metis_tac[lookup_var_def])
  >- ( `phi_prefix_length target.bb_instructions = 0` by metis_tac[] >>
       drule eval_phis_no_phi >> disch_then (qspec_then `mid` assume_tac) >>
       gvs[] >> drule_all entry_ghost_no_phi >> strip_tac >>
       gvs[lookup_var_def]) >>
  gvs[jump_to_def, lookup_var_def, store_copy_normalize_def]
QED

Theorem slots_readonly_list_frame[local]:
  !L s G tn u Gu tnu.
  L <> [] /\ HD L = (s,G,tn) /\ LAST L = (u,Gu,tnu) /\ ~s.vs_halted /\
  (!n a Ga tna b Gb tnb.
    SUC n < LENGTH L /\ EL n L = (a,Ga,tna) /\ EL (SUC n) L = (b,Gb,tnb) ==>
    ?bb i.
      lookup_block a.vs_current_bb func.fn_blocks = SOME bb /\
      get_instruction bb a.vs_inst_idx = SOME i /\
      MEM i.inst_opcode [ASSIGN; ADD; MUL; EQ; LT; ISZERO; SHR; MLOAD; JMP; JNZ] /\
      (!x. not_fresh_at sa x ==> ~MEM x i.inst_outputs) /\
      (!fuel mid target.
        step_inst fuel ctx i a = OK mid /\ is_terminator i.inst_opcode /\
        lookup_block mid.vs_current_bb func.fn_blocks = SOME target ==>
        phi_prefix_length target.bb_instructions = 0) /\
      gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (a,Ga,tna) [] (OK b,Gb,tnb)) ==>
  (!sbase. store_copy_normalize sbase u = store_copy_normalize sbase s) /\
  (!x. not_fresh_at sa x ==>
    lookup_var x u = lookup_var x s /\ FLOOKUP Gu x = FLOOKUP G x /\
    op_taint tnu (Var x) = op_taint tn (Var x)) /\
  tnu.t_mem = tn.t_mem /\ tnu.t_imm = tn.t_imm /\
  tnu.t_stor = tn.t_stor /\ tnu.t_trans = tn.t_trans /\ ~u.vs_halted
Proof
  Induct_on `L` >- simp[] >>
  qx_gen_tac `head` >> Cases_on `L`
  >- (simp[] >> rpt strip_tac >> gvs[]) >>
  rpt gen_tac >> strip_tac >> gvs[HD] >> PairCases_on `h` >>
  rename1 `LAST ((b,Gb,tnb)::tail) = (u,Gu,tnu)` >>
  qpat_assum `!n a Ga tna b Gb tnb. _` (qspec_then `0` mp_tac) >> simp[] >>
  disch_then (qx_choose_then `bb` (qx_choose_then `i`
    (REPEAT_TCL CONJUNCTS_THEN assume_tac))) >>
  drule_all (SRULE[MEM] store_slots_readonly_edge_frame) >> strip_tac >>
  `(!sbase. store_copy_normalize sbase u = store_copy_normalize sbase b) /\
   (!x. not_fresh_at sa x ==>
     lookup_var x u = lookup_var x b /\ FLOOKUP Gu x = FLOOKUP Gb x /\
     op_taint tnu (Var x) = op_taint tnb (Var x)) /\
   tnu.t_mem = tnb.t_mem /\ tnu.t_imm = tnb.t_imm /\
   tnu.t_stor = tnb.t_stor /\ tnu.t_trans = tnb.t_trans /\ ~u.vs_halted` by
    (first_x_assum irule >> simp[] >>
     map_every qx_gen_tac [`n`, `a`, `Ga`, `tna`, `b1`, `Gb1`, `tnb1`] >>
     strip_tac >>
     qpat_x_assum `!n a Ga tna b Gb tnb. _` (qspec_then `SUC n` mp_tac) >> simp[]) >>
  qpat_x_assum `!s G tn. _` kall_tac >>
  qpat_x_assum `!n a Ga tna b Gb tnb. _` kall_tac >>
  qpat_x_assum `_ = ASSIGN \/ _` kall_tac >>
  simp[]
QED

Theorem store_slots_readonly_prefix_frame:
  L <> [] /\ HD L = (s,G,tn) /\ LAST L = (u,Gu,tnu) /\ ~s.vs_halted /\
  (!n a Ga tna b Gb tnb.
    SUC n < LENGTH L /\ EL n L = (a,Ga,tna) /\ EL (SUC n) L = (b,Gb,tnb) ==>
    ?bb i.
      lookup_block a.vs_current_bb func.fn_blocks = SOME bb /\
      get_instruction bb a.vs_inst_idx = SOME i /\
      MEM i.inst_opcode [ASSIGN; ADD; MUL; EQ; LT; ISZERO; SHR; MLOAD; JMP; JNZ] /\
      (!x. not_fresh_at sa x ==> ~MEM x i.inst_outputs) /\
      (!fuel mid target.
        step_inst fuel ctx i a = OK mid /\ is_terminator i.inst_opcode /\
        lookup_block mid.vs_current_bb func.fn_blocks = SOME target ==>
        phi_prefix_length target.bb_instructions = 0) /\
      gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (a,Ga,tna) [] (OK b,Gb,tnb)) ==>
  store_copy_normalize s u = s /\
  (!x. not_fresh_at sa x ==>
    lookup_var x u = lookup_var x s /\ FLOOKUP Gu x = FLOOKUP G x /\
    op_taint tnu (Var x) = op_taint tn (Var x)) /\
  tnu.t_mem = tn.t_mem /\ tnu.t_imm = tn.t_imm /\
  tnu.t_stor = tn.t_stor /\ tnu.t_trans = tn.t_trans /\
  u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas /\
  u.vs_alloca_next = s.vs_alloca_next /\ u.vs_fmp = s.vs_fmp /\
  u.vs_labels = s.vs_labels /\ u.vs_call_ctx = s.vs_call_ctx /\ ~u.vs_halted
Proof
  strip_tac >> drule_all slots_readonly_list_frame >> strip_tac >>
  `store_copy_normalize s u = s` by
    (first_x_assum (qspec_then `s` mp_tac) >> simp[store_copy_normalize_def]) >>
  gvs[store_copy_normalize_def, venom_state_component_equality]
QED
