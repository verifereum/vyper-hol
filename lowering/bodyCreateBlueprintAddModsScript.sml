(* The blueprint size and suffix address use the same clean ADD edge. *)
Theory bodyCreateBlueprintAddMods
Ancestors
  fragGasOriginPtr bodyFullRawCallCallOrigin[qualified]
  bodyPtrMakeArrayEmission[qualified] emitHelperProps[qualified]
  typedCopyPtr[qualified] ptrSafetyTransport[qualified]
  loweringShapeRules[qualified] decoderGhostFramePtr[qualified]
  ptrDiscipline memSafeRun unitTransformDefs venomExecSemantics
  venomInst venomState loweringStateRelDefs emitHelper codegenRel
  contextCodegenRel finite_map

Theorem blueprint_add_path_physical:
  emit_op ADD [left;right] sa = (dst,sb) /\ fn_has_code sa sb func /\
  eval_operand left s = SOME a /\ eval_operand right s = SOME b /\
  op_taint tn left = {} /\ op_taint tn right = {} /\ op_prov G right = NONE /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ allocas_from lo s /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?out t G' tn'. dst = Var out /\ not_fresh_at sb out /\
    t = (update_var out (a+b) s with vs_inst_idx := LENGTH sb.cs_current_insts) /\
    t.vs_current_bb = sb.cs_current_bb /\
    (!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn')) /\
    eval_operand dst t = SOME (a+b) /\
    FLOOKUP G' out = op_prov G left /\ op_taint tn' dst = {} /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!p. p <> out ==> lookup_var p t = lookup_var p s /\
      FLOOKUP G' p = FLOOKUP G p /\ op_taint tn' (Var p) = op_taint tn (Var p)) /\
    (!p. not_fresh_at sa p ==> p <> out)
Proof
  strip_tac >>
  drule_all bodyPtrMakeArrayEmissionTheory.emit_op_fetch_boundary >> strip_tac >>
  drule (cj 4 emitHelperPropsTheory.emitted_insts_emit_op) >> strip_tac >>
  qabbrev_tac `i = mk_inst sa.cs_next_id ADD [left;right] [tmp]` >>
  qabbrev_tac `u = update_var tmp (a+b) s` >>
  qabbrev_tac `gf = step_prov PG G i u` >>
  qabbrev_tac `tf = step_taint i s u tn` >>
  `not_fresh_at sb tmp` by simp[loweringShapeRulesTheory.fresh_output_props] >>
  `!D. ptr_inst_ok D lo 0 ctx func G tn i s` by
    (gen_tac >> simp[Abbr `i`] >>
     irule ptrSafetyTransportTheory.ptr_inst_ok_lower_bound_transport >>
     simp[] >> qexists `0` >> simp[typedCopyPtrTheory.ptr_inst_ok_copy_len_binop]) >>
  `step_inst_base i s = OK u` by
    simp[Abbr `i`,Abbr `u`,mk_inst_def,step_inst_base_opcode_eqs,exec_pure2_def] >>
  `i.inst_opcode <> INVOKE /\ i.inst_opcode <> GAS /\ ~is_terminator i.inst_opcode` by
    simp[Abbr `i`,mk_inst_def,is_terminator_def] >>
  `mem_safe_step 0 ctx i s` by
    simp[Abbr `i`,mk_inst_def,mem_safe_step_non_invoke,
         inst_mem_below_frontier_def,inst_dload_in_section_def,
         source_memory_read_ranges_def,source_memory_write_ranges_def] >>
  `!D explicit. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (u with vs_inst_idx := LENGTH sb.cs_current_insts),gf,tf)` by
    (rpt gen_tac >>
     qpat_assum `SUC s.vs_inst_idx = LENGTH sb.cs_current_insts`
       (PURE_ONCE_REWRITE_TAC o single o SYM) >>
     `gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (s,G,tn) []
        (OK (u with vs_inst_idx := SUC s.vs_inst_idx),gf,tf)` by
       (simp_tac bool_ss [Abbr `gf`,Abbr `tf`] >>
        irule bodyFullRawCallCallOriginTheory.non_gas_mem_safe_origin_ptr_edge >>
        simp[] >> metis_tac[]) >>
     drule (cj 2 gas_origin_ptr_path_rules) >>
     disch_then (qspec_then `[]` mp_tac) >> simp[] >> disch_then irule >>
     irule (cj 1 gas_origin_ptr_path_rules) >>
     simp[Abbr `u`,update_var_def]) >>
  `FLOOKUP gf tmp = op_prov G left` by
    (Cases_on `op_prov G left` >>
     simp[Abbr `gf`,Abbr `i`,step_prov_def,out_prov_def,first_prov_def,set_prov_def,
          mk_inst_def,FLOOKUP_UPDATE,FLOOKUP_DRESTRICT]) >>
  `op_taint tf (Var tmp) = {} /\ tf.t_mem = tn.t_mem /\
   tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
   (!p. p <> tmp ==> FLOOKUP gf p = FLOOKUP G p /\ op_taint tf (Var p) = op_taint tn (Var p))` by
    (simp[Abbr `gf`,Abbr `tf`,Abbr `i`,Abbr `u`,typedCopyPtrTheory.copy_len_binop_ghost_frame] >>
     irule (cj 3 decoderGhostFramePtrTheory.step_taint_nonmemory_frame) >> simp[mk_inst_def]) >>
  qexistsl [`tmp`,`u with vs_inst_idx := LENGTH sb.cs_current_insts`,`gf`,`tf`] >>
  qpat_x_assum `tmp = STRING _ _` SUBST_ALL_TAC >>
  simp[Abbr `u`,update_var_def,lookup_var_def,eval_operand_def,FLOOKUP_UPDATE] >>
  simp[not_fresh_at_def] >> qexists `sa.cs_next_var` >> simp[]
QED
