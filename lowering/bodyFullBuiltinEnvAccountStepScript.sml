(* Joint finite account instruction boundary. *)
Theory bodyFullBuiltinEnvAccountStep
Ancestors
 exprSimAccounts bodyFullGhostFrame fragGasSeqPtr gasOutcomeFullCompose
 ptrSafeRun ptrDiscipline venomInst venomState vyperStorageTrace
 bodyPtrDefs venomExecSemantics fragGasOriginPtr
 loweringStateRelDefs exprLoweringProps decoderGhostFramePtr codegenRel
 fragExec emitHelperProps allocaHistory finite_map list compileEnv vyperStorageFootprint

Theorem account_emit_full_run:
 MEM (item,opc) [(Balance,BALANCE);(Codesize,EXTCODESIZE);
   (Codehash,EXTCODEHASH);(IsContract,EXTCODESIZE);(IsContract,GT)] /\
 (opc = GT ==> ?x. xs = [x; Lit 0w]) /\
 emit_op opc xs sa = (op,sb) /\ fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
 storage_trace_domain cx st0 ee.storage_trace /\ local_ptrs_reserved cenv sa /\
 (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
 (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
 EVERY (\x. op_taint tn x = {}) xs /\ ~ctx_has_dalloca ctx /\
 (!out. step_inst_base (mk_inst sa.cs_next_id opc xs [out]) s = OK (update_var out w s)) /\
 ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
 s.vs_inst_idx = LENGTH sa.cs_current_insts /\ alloca_history func s /\
 (!H. valid_horizon cx st0 H ee.storage_trace ==>
 stmt_state_rel H ctx func cenv cx ee s /\ storage_well_formed_on cx ee (FST H) /\
 ghost_inv_at (DF H) lo d cenv cx ee G tn s)
 ==>
 ?t G' tn'. ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
 t.vs_inst_idx = LENGTH sb.cs_current_insts /\ local_ptrs_reserved cenv sb /\
 alloca_history func t /\ t.vs_memory = s.vs_memory /\
 t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
 tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
 tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
 (!p. not_fresh_at sa p ==> lookup_var p t = lookup_var p s /\
   FLOOKUP G' p = FLOOKUP G p /\ op_taint tn' (Var p) = op_taint tn (Var p)) /\
 eval_operand op t = SOME w /\ op_taint tn' op = {} /\
 (!H. valid_horizon cx st0 H ee.storage_trace ==>
 gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn') /\
 stmt_state_rel H ctx func cenv cx ee t /\ storage_well_formed_on cx ee (FST H) /\
 ghost_inv_at (DF H) lo d cenv cx ee G' tn' t)
Proof
 strip_tac >>
 `MEM opc [BALANCE; EXTCODESIZE; EXTCODEHASH; GT]` by gvs[] >>
 qabbrev_tac `dst = STRING #"%" (toString sa.cs_next_var)` >>
 qabbrev_tac `inst = mk_inst sa.cs_next_id opc xs [dst]` >>
 qabbrev_tac `u = update_var dst w s` >>
 qexistsl_tac [`u with vs_inst_idx := SUC s.vs_inst_idx`,
   `step_prov PG G inst u`, `step_taint inst s u tn`] >>
 `op = Var dst /\ sb.cs_current_bb = sa.cs_current_bb /\
   LENGTH sb.cs_current_insts = SUC (LENGTH sa.cs_current_insts) /\
   sa.cs_next_var <= sb.cs_next_var` by
   gvs[Abbr `dst`, emitHelperTheory.emit_op_def, comp_bind_def,
     fresh_var_def, fresh_id_def, comp_ignore_bind_def, comp_return_def, emit_def] >>
 `!p. not_fresh_at sa p ==> p <> dst` by
   (simp[Abbr `dst`, not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
 `local_ptrs_reserved cenv sb` by metis_tac[local_ptrs_reserved_next_var] >>
 `!p. not_fresh_at sa p ==>
   lookup_var p (u with vs_inst_idx := SUC s.vs_inst_idx) = lookup_var p s /\
   FLOOKUP (step_prov PG G inst u) p = FLOOKUP G p /\
   op_taint (step_taint inst s u tn) (Var p) = op_taint tn (Var p)` by
   (rpt strip_tac >> `p <> dst` by metis_tac[] >>
    simp[Abbr `u`, Abbr `inst`, lookup_var_def, update_var_def,
      FLOOKUP_UPDATE, step_prov_other_output, step_taint_other_output, mk_inst_def]) >>
 `(step_taint inst s u tn).t_mem = tn.t_mem /\
  (step_taint inst s u tn).t_stor = tn.t_stor /\
  (step_taint inst s u tn).t_trans = tn.t_trans /\
  (step_taint inst s u tn).t_imm = tn.t_imm` by
   (qpat_x_assum `MEM opc _` mp_tac >> simp[] >> strip_tac >>
    gvs[Abbr `inst`, step_taint_def, mem_taint_def, step_writes_def,
     new_site_bytes_def, range_bytes_def, written_taint_def,
     source_memory_write_ranges_def, adopt_reset_def, store_taint_def,
     imm_taint_def, Abbr `u`, update_var_def, mk_inst_def,
     pred_setTheory.EXTENSION, FLOOKUP_DEF] >>
    rpt (BasicProvers.TOP_CASE_TAC >> fs[]) >> metis_tac[]) >>
 `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
   get_instruction bb s.vs_inst_idx = SOME inst` by
   (drule emitted_insts_emit_op >> strip_tac >>
    drule_all fn_has_code_same_block >> strip_tac >>
    first_x_assum (qspec_then `0` mp_tac) >>
    simp[Abbr `inst`, Abbr `dst`] >> metis_tac[]) >>
 `alloca_inv s` by
   (qpat_x_assum `!H. valid_horizon _ _ _ _ ==> _` mp_tac >>
    disch_then (qspec_then `storage_trace_horizon ee.storage_trace` mp_tac) >>
    fs[storage_trace_domain_def, stmt_state_rel_def]) >>
 `step_inst_base inst s = OK u` by simp[Abbr `inst`, Abbr `u`] >>
 `alloca_history func (u with vs_inst_idx := SUC s.vs_inst_idx)` by
   (drule_all alloca_history_base_step >>
    qpat_x_assum `MEM opc _` mp_tac >>
    simp[Abbr `inst`, mk_inst_def] >> strip_tac >>
    gvs[is_terminator_def]) >>
 `op_taint (step_taint inst s u tn) (Var dst) = {}` by
   (qpat_x_assum `MEM opc _` mp_tac >> simp[] >> strip_tac >>
    simp[Abbr `inst`, step_taint_def, op_taint_def, set_var_taint_def,
      mk_inst_def, FLOOKUP_UPDATE, out_taint_def] >>
    rpt (BasicProvers.TOP_CASE_TAC >> fs[])) >>
 `~u.vs_halted /\ u.vs_current_bb = s.vs_current_bb /\
  u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas /\
  u.vs_alloca_next = s.vs_alloca_next /\ eval_operand op u = SOME w` by
   simp[Abbr `u`, update_var_def, eval_operand_def, lookup_var_def, FLOOKUP_UPDATE] >>
 simp[] >>
 qx_gen_tac `H` >> strip_tac >>
 `stmt_state_rel H ctx func cenv cx ee s /\
   storage_well_formed_on cx ee (FST H) /\
   ghost_inv_at (DF H) lo d cenv cx ee G tn s` by metis_tac[] >>
 reverse conj_tac
 >- (reverse conj_tac
     >- (irule ghost_inv_at_exterior_frame >> qexistsl_tac [`G`, `ee`, `s`, `sa`, `tn`] >>
         simp[Abbr `u`, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >> metis_tac[]) >>
     simp[stmt_state_rel_inst_idx, Abbr `u`] >>
     irule stmt_state_rel_update_var >> simp[] >>
     irule exprSimOperandsTheory.fresh_not_local_ptr >>
     qexists_tac `sa` >> metis_tac[]) >>
 `gas_origin_ptr_edge (DF H,lo,explicit,ctx,func,PG) (s,G,tn) []
   (OK (u with vs_inst_idx := SUC s.vs_inst_idx), step_prov PG G inst u,
    step_taint inst s u tn)` by
   (`inst_mem_below_frontier inst s /\ inst_dload_in_section inst s` by
      (qpat_x_assum `MEM opc _` mp_tac >> simp[] >> strip_tac >>
       simp[Abbr `inst`, mk_inst_def, unitTransformDefsTheory.inst_mem_below_frontier_def,
        memSafeRunTheory.inst_dload_in_section_def, contextCodegenRelTheory.source_memory_read_ranges_def,
        source_memory_write_ranges_def]) >>
    `taint_ok func tn inst s` by
      (qpat_x_assum `MEM opc _` mp_tac >> simp[] >> strip_tac >>
       simp[taint_ok_def, Abbr `inst`, mk_inst_def,
        contextCodegenRelTheory.source_memory_read_ranges_def] >>
       fs[EVERY_MEM, GSYM IMP_DISJ_THM] >>
       rpt strip_tac >> gvs[] >> metis_tac[op_taint_def]) >>
    `ptr_inst_ok (DF H) lo 0 ctx func G tn inst s` by
      (simp[ptr_inst_ok_def] >>
       `allocas_from lo s` by fs[ghost_inv_at_def] >>
       `step_inst 0 ctx inst s = OK u` by
         (qpat_x_assum `MEM opc _` mp_tac >> simp[] >> strip_tac >>
          simp[step_inst_non_invoke, Abbr `inst`, mk_inst_def]) >>
       simp[] >>
       qpat_x_assum `MEM opc _` mp_tac >> simp[] >> strip_tac >>
       fs[Abbr `inst`, mk_inst_def, access_ok_def,
        contextCodegenRelTheory.source_memory_read_ranges_def, source_memory_write_ranges_def,
        EVERY_MEM, Abbr `u`, update_var_def]) >>
    `inst.inst_opcode <> INVOKE /\ ~is_terminator inst.inst_opcode /\
     inst.inst_opcode <> GAS` by
      (qpat_x_assum `MEM opc _` mp_tac >> simp[] >> strip_tac >>
       simp[Abbr `inst`, mk_inst_def, is_terminator_def]) >>
    drule_all straight_line_origin_ptr_edge >> simp[]) >>
 drule (cj 2 gas_origin_ptr_path_rules) >>
 disch_then (qspec_then `[]` mp_tac) >> simp[] >>
 disch_then irule >> irule (cj 1 gas_origin_ptr_path_rules) >> simp[]
QED
