Theory bodyFullForArrayFixedStart
Ancestors
  bodyFullForArray bodyFullAllocaFresh bodyFullGhostFrame
  fragGasOriginPtrLoop fragGasSeqPtr instSeqPtrLo
  venomExecSemantics venomState venomInst ptrDiscipline
  finite_map pred_set words forPtrCheckedScalar ptrSafeRun
  fragExec fragExecMem instMemFrontier memSafeRun codegenRel venomExecProofs
  contextCodegenRel exprLoweringProps loweringStateRelDefs
  bodyPtrDefs bodyMemoryDefs stmtSimProps vyperValue list exprSimOperands

(* The fixed entry's scalar certificate is generated here, not assumed
   from its caller.  These ghosts are independent of the horizon. *)
Theorem for_array_fixed_scalar_entry_full:
  lookup_block lbl func.fn_blocks = SOME
    <|bb_label := lbl; bb_instructions :=
      [mk_inst i ASSIGN [Lit 0w] [idx]; mk_inst j JMP [Label cond] []]|> /\
  s.vs_current_bb = lbl /\ s.vs_inst_idx = 0 /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ allocas_from lo s ==>
  (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (jump_to cond (update_var idx 0w s)),
     step_prov PG G (mk_inst i ASSIGN [Lit 0w] [idx]) (update_var idx 0w s),
     step_taint (mk_inst i ASSIGN [Lit 0w] [idx]) s (update_var idx 0w s) tn)) /\
  FLOOKUP (step_prov PG G (mk_inst i ASSIGN [Lit 0w] [idx])
    (update_var idx 0w s)) idx = NONE /\
  op_taint (step_taint (mk_inst i ASSIGN [Lit 0w] [idx]) s
    (update_var idx 0w s) tn) (Var idx) = {} /\
  (step_taint (mk_inst i ASSIGN [Lit 0w] [idx]) s
    (update_var idx 0w s) tn).t_mem = tn.t_mem /\
  (step_taint (mk_inst i ASSIGN [Lit 0w] [idx]) s
    (update_var idx 0w s) tn).t_stor = tn.t_stor /\
  (step_taint (mk_inst i ASSIGN [Lit 0w] [idx]) s
    (update_var idx 0w s) tn).t_trans = tn.t_trans /\
  (step_taint (mk_inst i ASSIGN [Lit 0w] [idx]) s
    (update_var idx 0w s) tn).t_imm = tn.t_imm /\
  (!v. v <> idx ==>
    FLOOKUP (step_prov PG G (mk_inst i ASSIGN [Lit 0w] [idx])
      (update_var idx 0w s)) v = FLOOKUP G v /\
    op_taint (step_taint (mk_inst i ASSIGN [Lit 0w] [idx]) s
      (update_var idx 0w s) tn) (Var v) = op_taint tn (Var v))
Proof
  strip_tac >>
  qabbrev_tac `u = update_var idx 0w s` >>
  qabbrev_tac `ai = mk_inst i ASSIGN [Lit 0w] [idx]` >>
  `step_taint ai s u tn = tn with t_var := tn.t_var |+ (idx,{})` by
    (simp[Abbr `ai`,Abbr `u`] >> irule for_checked_scalar_step_taint >>
     simp[op_taint_def,new_site_bytes_def,update_var_def,FLOOKUP_DEF] >> SET_TAC[]) >>
  `step_prov PG G ai u = DRESTRICT G (COMPL {idx})` by
    (simp[Abbr `ai`] >> irule for_checked_scalar_step_prov >>
     simp[] >> rpt strip_tac >> gvs[op_prov_def]) >>
  reverse conj_tac >- simp[FLOOKUP_DRESTRICT,op_taint_def,FLOOKUP_UPDATE] >>
  gen_tac >>
  `inst_seq_ptr D lo ctx func PG G tn [ai] s
    (step_prov PG G ai u) (step_taint ai s u tn)` by
    (simp[inst_seq_ptr_def,Abbr `ai`,Abbr `u`,
          step_inst_base_opcode_eqs,mk_inst_def,eval_operand_def] >>
     simp[ptr_inst_ok_def,access_ok_def,taint_ok_def,
          source_memory_write_ranges_def,source_memory_read_ranges_def,
          GSYM mk_inst_def,step_inst_non_invoke] >>
     simp[step_inst_base_opcode_eqs,mk_inst_def,eval_operand_def,
          update_var_def,allocas_from_def] >>
     gen_tac >> Cases_on `op` >> simp[op_taint_def]) >>
  `run_inst_seq [ai] s = OK u` by
    simp[run_inst_seq_def,Abbr `ai`,Abbr `u`,step_inst_base_opcode_eqs,
         mk_inst_def,eval_operand_def] >>
  `run_inst_seq_mem_ok [ai] s` by
    simp[run_inst_seq_mem_ok_def,Abbr `ai`,mk_inst_def,
         below_frontier_no_ranges,inst_dload_in_section_other,
         step_inst_base_opcode_eqs,eval_operand_def] >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (u with vs_inst_idx := 1),step_prov PG G ai u,step_taint ai s u tn)` by
    (drule_at (Pat `run_inst_seq _ _ = _`) run_inst_seq_gas_origin_ptr_path >>
     simp[Abbr `ai`,mk_inst_def,is_terminator_def] >>
     disch_then irule >> conj_tac
     >- (goal_assum (drule_at Any) >> gvs[mk_inst_def]) >>
     gvs[GSYM mk_inst_def]) >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (u with vs_inst_idx := 1,step_prov PG G ai u,step_taint ai s u tn) []
    (OK (jump_to cond (u with vs_inst_idx := 1)),
      step_prov PG G ai u,step_taint ai s u tn)` by
    (irule jmp_origin_ptr_path >>
     simp[Abbr `u`,update_var_def,get_instruction_def,allocas_from_def] >>
     qexists_tac `j` >> simp[]) >>
  drule_all gas_origin_ptr_path_trans >> simp[jump_to_def]
QED

Theorem for_array_fixed_entry_full:
  compile_alloc_buffer sz sa = (buf,sb) /\ buf.buf_operand = Var p /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  lookup_block sb.cs_current_bb func.fn_blocks = SOME
    <|bb_label := sb.cs_current_bb; bb_instructions :=
      sb.cs_current_insts ++ [mk_inst aj JMP [Label entry] []]|> /\
  lookup_block entry func.fn_blocks = SOME
    <|bb_label := entry; bb_instructions :=
      [mk_inst ei ASSIGN [Lit 0w] [idx]; mk_inst ej JMP [Label cond] []]|> /\
  sz < dimword (:256) /\ LENGTH vs < dimword (:256) /\
  p <> idx /\ (!x. not_fresh_at sa x ==> x <> idx) /\
  local_ptrs_reserved cenv sa /\
  (!x z. cenv.ce_return_buf = SOME (PtrVar (Var x) z) ==> not_fresh_at sa x) /\
  (!x z. cenv.ce_return_pc = SOME (PtrVar (Var x) z) ==> not_fresh_at sa x) /\
  (!x. saved_base = Var x ==> not_fresh_at sa x) /\
  expr_sim_inv cenv cx env es /\
  lookup_scopes name es.scopes = SOME ent /\
  ent.type = ArrayTV tv (Fixed (LENGTH vs)) /\ ent.value = ArrayV av /\
  vs = array_elements ent.type av /\
  eval_operand saved_base s0 = SOME array_base /\
  return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
  (?H. valid_horizon cx st0 H es.storage_trace) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx es G0 tn0 s0) /\
  ~ctx_has_dalloca ctx /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?dst cc Gentry tnentry.
    lookup_var p cc = SOME dst /\ ptr_covers Gentry tnentry p cc sz /\
    FLOOKUP cc.vs_allocas sa.cs_next_id = SOME (w2n dst,sz) /\
    w2n dst + sz < dimword (:256) /\ w2n dst + sz <= cc.vs_alloca_next /\
    (!nm b len. local_region cenv es.scopes cc nm b len ==>
      regions_disjoint (w2n dst) sz b len) /\
    ~cc.vs_halted /\ cc.vs_current_bb = cond /\ cc.vs_inst_idx = 0 /\
    lookup_var idx cc = SOME 0w /\ FLOOKUP Gentry idx = NONE /\
    op_taint tnentry (Var idx) = {} /\
    lookup_scopes name es.scopes = SOME ent /\
    ent.type = ArrayTV tv (Fixed (LENGTH vs)) /\ ent.value = ArrayV av /\
  vs = array_elements ent.type av /\
    eval_operand saved_base cc = SOME array_base /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
      expr_sim_inv cenv cx env es /\ stmt_state_rel H ctx func cenv cx es cc /\
      storage_well_formed_on cx es (FST H) /\
      return_buf_frame d cenv sa cc /\ alloca_history func cc /\
      s0.vs_alloca_next <= cc.vs_alloca_next /\ allocas_from lo cc /\
      ghost_inv_at (DF H) lo d cenv cx es Gentry tnentry cc) /\
    (!x v. not_fresh_at sa x /\ lookup_var x s0 = SOME v ==>
      lookup_var x cc = SOME v) /\
    (!aid bl. FLOOKUP s0.vs_allocas aid = SOME bl ==> FLOOKUP cc.vs_allocas aid = SOME bl) /\
    (!x. not_fresh_at sa x ==> FLOOKUP Gentry x = FLOOKUP G0 x /\
      op_taint tnentry (Var x) = op_taint tn0 (Var x)) /\
    (!H. gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s0,G0,tn0) []
      (OK cc,Gentry,tnentry))
Proof
  strip_tac >>
  `?H0. valid_horizon cx st0 H0 es.storage_trace` by metis_tac[] >>
  `stmt_state_rel H0 ctx func cenv cx es s0 /\
   ghost_inv_at (DF H0) lo d cenv cx es G0 tn0 s0` by metis_tac[] >>
  `allocas_from lo s0 /\ lo <= s0.vs_alloca_next` by fs[ghost_inv_at_def] >>
  drule_all (INST_TYPE [``:'b`` |-> ``:256``] alloc_buffer_origin_ptr_path) >>
  disch_then (qspecl_then [`tn0`,`explicit`,`PG`,`G0`] strip_assume_tac) >>
  `q = p` by metis_tac[operand_11] >> qpat_x_assum `q = p` SUBST_ALL_TAC >>
  `~t.vs_halted` by
    (qpat_assum `t with <|vs_vars := _; vs_allocas := _;
       vs_alloca_next := _; vs_inst_idx := _|> = s0`
       (mp_tac o AP_TERM ``\s:venom_state. s.vs_halted``) >> simp[]) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (t,G',tn') [] (OK (jump_to entry t),G',tn')` by
    (gen_tac >> irule jmp_origin_ptr_path >>
     simp[get_instruction_def,EL_APPEND_EQN] >> qexists_tac `aj` >> simp[]) >>
  qabbrev_tac `e0 = jump_to entry t` >>
  qpat_assum `lookup_block entry _ = _`
    (mp_then Any mp_tac for_array_fixed_scalar_entry_full) >>
  disch_then (qspecl_then [`tn'`,`e0`,`lo`,`explicit`,`ctx`,`PG`,`G'`] mp_tac) >>
  (impl_tac >- (simp[Abbr `e0`,jump_to_def,allocas_from_def] >>
    qpat_x_assum `allocas_from lo t` mp_tac >> simp[allocas_from_def])) >>
  strip_tac >>
  qabbrev_tac `cc = jump_to cond (update_var idx 0w e0)` >>
  qabbrev_tac `Ge = step_prov PG G' (mk_inst ei ASSIGN [Lit 0w] [idx])
    (update_var idx 0w e0)` >>
  qabbrev_tac `te = step_taint (mk_inst ei ASSIGN [Lit 0w] [idx]) e0
    (update_var idx 0w e0) tn'` >>
  qpat_x_assum `vs = array_elements _ _` (mk_asm "elements") >>
  `!x. not_fresh_at sa x ==>
    lookup_var x cc = lookup_var x s0 /\ FLOOKUP Ge x = FLOOKUP G0 x /\
    op_taint te (Var x) = op_taint tn0 (Var x)` by
    (gen_tac >> disch_tac >> `x <> idx` by metis_tac[] >>
     simp[Abbr `cc`,Abbr `e0`,jump_to_def,update_var_def,lookup_var_def,FLOOKUP_UPDATE] >>
     metis_tac[lookup_var_def]) >>
  `!H. valid_horizon cx st0 H es.storage_trace ==>
    ghost_inv_at (DF H) lo d cenv cx es G' tn' t` by
    (qx_gen_tac `HH` >> disch_tac >>
     `stmt_state_rel HH ctx func cenv cx es s0 /\
      ghost_inv_at (DF HH) lo d cenv cx es G0 tn0 s0` by metis_tac[] >>
     qpat_assum `ghost_inv_at (DF HH) lo d cenv cx es G0 tn0 s0`
       (mp_then Any mp_tac
       (INST_TYPE [alpha |-> ``:256``] alloc_buffer_ghost_inv_at)) >>
     disch_then irule >> simp[] >>
     conj_tac >- (qexists_tac `w2n w + sz` >> simp[]) >>
     conj_tac >- (qexists_tac `sa` >> simp[]) >> metis_tac[]) >>
  `!H. valid_horizon cx st0 H es.storage_trace ==>
    ghost_inv_at (DF H) lo d cenv cx es Ge te cc` by
    (qx_gen_tac `HH` >> disch_tac >> irule ghost_inv_at_exterior_frame >>
     qexistsl_tac [`G'`,`es`,`t`,`sa`,`tn'`] >>
     simp[Abbr `cc`,Abbr `e0`,jump_to_def,update_var_def] >>
     metis_tac[]) >>
  `not_local_ptr cenv es.scopes idx` by
    (irule fresh_not_local_ptr >> qexists_tac `sa` >> metis_tac[]) >>
  `!HH. valid_horizon cx st0 HH es.storage_trace ==>
    stmt_state_rel HH ctx func cenv cx es cc` by
    (qx_gen_tac `HH` >> disch_tac >>
     simp[Abbr `cc`,Abbr `e0`,stmt_state_rel_jump_to] >>
     irule stmt_state_rel_update_var >> simp[stmt_state_rel_jump_to] >>
     qpat_assum `!H. stmt_state_rel H _ _ _ _ _ s0 ==> _` irule >>
     qpat_assum `!H. valid_horizon _ _ _ _ ==> _ /\ _ /\ _`
       (qspec_then `HH` mp_tac) >> simp[]) >>
  `return_buf_frame d cenv sa cc` by
    (irule return_buf_frame_frame >>
     qexistsl_tac [`cenv`,`s0`,`sa`] >>
     simp[Abbr `cc`,Abbr `e0`,jump_to_def,update_var_def] >> metis_tac[]) >>
  qexistsl_tac [`w`,`cc`,`Ge`,`te`] >>
  simp[] >>
  conj_tac >- (simp[Abbr `cc`,Abbr `e0`,jump_to_def,update_var_def,lookup_var_def,FLOOKUP_UPDATE] >>
    metis_tac[lookup_var_def]) >>
  conj_tac >-
    (qpat_x_assum `ptr_covers G' tn' p t sz` mp_tac >>
     simp[ptr_covers_def,Abbr `cc`,Abbr `e0`,jump_to_def,update_var_def,
          lookup_var_def,FLOOKUP_UPDATE] >> metis_tac[lookup_var_def]) >>
  conj_tac >- simp[Abbr `cc`,Abbr `e0`,jump_to_def,update_var_def] >>
  conj_tac >- simp[Abbr `cc`,Abbr `e0`,jump_to_def,update_var_def] >>
  conj_tac >-
    (rpt strip_tac >> qpat_assum `!name b len. local_region _ _ t _ _ _ ==> _` irule >>
     qexists_tac `nm` >>
     qpat_x_assum `local_region _ _ cc _ _ _` mp_tac >>
     simp[local_region_def,Abbr `cc`,Abbr `e0`,jump_to_def,
          update_var_def,lookup_var_def,FLOOKUP_UPDATE] >>
     fs[not_local_ptr_def] >> metis_tac[]) >>
  simp[Abbr `cc`,Abbr `e0`,jump_to_def,update_var_def,lookup_var_def,FLOOKUP_UPDATE] >>
  conj_tac >- (asm "elements" mp_tac >> pure_asm_rewrite_tac[] >> simp[]) >>
  conj_tac >-
    (Cases_on `saved_base` >> fs[eval_operand_def]
     >- (qpat_assum `!x. not_fresh_at sa x ==> lookup_var x cc = _ /\ _`
           (qspec_then `s` mp_tac) >>
         fs[jump_to_def,update_var_def,lookup_var_def,FLOOKUP_UPDATE]) >>
     qpat_assum `t with <|vs_vars := _; vs_inst_idx := _;
       vs_allocas := _; vs_alloca_next := _|> = s0`
       (mp_tac o AP_TERM ``\s:venom_state. s.vs_labels``) >> simp[]) >>
  conj_tac >-
    (rpt strip_tac >-
       (irule allocaHistoryTheory.alloca_history_jump >> simp[] >> qexists_tac `t` >> simp[]) >>
     fs[allocas_from_def] >> metis_tac[]) >>
  gen_tac >> irule gas_origin_ptr_path_trans >>
  qexistsl_tac [`G'`,`t`,`tn'`] >> conj_tac >- simp[] >>
  irule gas_origin_ptr_path_trans >>
  qexistsl_tac [`G'`,`jump_to entry t`,`tn'`] >>
  simp[jump_to_def,update_var_def] >>
  qpat_x_assum `!D. gas_origin_ptr_path _ (jump_to entry t,G',tn') _ _`
    (qspec_then `DF H'` mp_tac) >>
  simp[jump_to_def,update_var_def]
QED
