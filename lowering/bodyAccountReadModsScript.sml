(* Linked ordinary account access, including the active-frame CODESIZE path. *)
Theory bodyAccountReadMods
Ancestors
  bodyFullPredsMods bodyForRangeScalarFrameMods bodyFullShared
  bodySimStmtFacts exprBodyPreProps exprSimAccounts exprSimUnopComposeProps
  gasShadowCompileStmtHelpers gasOutcomeFullBindMods gasOutcomeFullPostMods
  gasExemptCertMods vyperStorageTrace exprSimProps exprSimWordArgs
  bodyFullBuiltinEnvAccountStep stateRelProj accountsRelProps
  allocaHistory fragGasSeqPtr typedCopyOriginPtrBase decoderGhostFramePtr
  vyperTypeInvariants vyperTypeBuiltins exprSimOperands emitHelperProps
  vyperStorageFootprint vyperContext vyperTypeSystem vyperInterpreter
  vyperState vyperAST loweringPosts loweringStateRelDefs exprSimMemDefs
  exprSimHypsDefs bodyPtrDefs exprLoweringProps exprLowering compileEnv
  ptrDiscipline ptrSafeRun memSafeRun venomExecSemantics venomInst venomState
  contextCodegenRel codegenRel list finite_map words allocLimits
  supportedExprTraverse vyperExprEffects vyperTypeCallGraph
  emitHelper unitTransformDefs fragExec fragGasOriginPtr

Theorem account_source_inputs[local]:
  expr_body_pre_mods mods cenv cx env (Builtin a (Acc item) args) es ==>
  item <> Code /\ ?e. args = [e] /\ a = account_item_type item /\
    expr_type e = BaseT AddressT
Proof
  strip_tac >> conj_tac
  >- fs[expr_body_pre_mods_def, alloc_limits_expr_def] >>
  drule expr_body_pre_mods_well_typed >>
  simp[Once well_typed_expr_def, well_typed_builtin_app_def] >>
  Cases_on `args` >> simp[] >> rename1 `h::t` >> Cases_on `t` >> simp[]
QED

Theorem account_operand_pre[local]:
  item <> Code /\
  expr_body_pre_mods mods cenv cx env (Builtin a (Acc item) [e]) es ==>
  expr_body_pre_mods mods cenv cx env e es
Proof
  simp[expr_body_pre_mods_def, Once well_typed_expr_def,
       well_typed_builtin_app_def, byte_widths_expr_def, alloc_limits_expr_def,
       constSubstCorrectTheory.frame_well_typed_exprs_every,
       int_calls_expr_def, expr_has_evm_run_thm, supported_expr_exists_def]
QED

val account_code = ``\item x. case item of
    Balance => emit_op BALANCE [x]
  | Codesize => emit_op EXTCODESIZE [x]
  | Codehash => emit_op EXTCODEHASH [x]
  | IsContract => comp_bind (emit_op EXTCODESIZE [x]) (\c. emit_op GT [c; Lit 0w])
  | Address => comp_return x | Code => comp_return x``;

Theorem account_suffix_extends[local]:
  ^account_code item x sa = (op,sb) ==>
  cs_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var
Proof
  Cases_on `item` >> simp[comp_return_def, cs_extends_refl, comp_bind_def] >>
  rpt (pairarg_tac >> simp[]) >>
  rpt strip_tac >> drule emit_op_extends_next_var >>
  metis_tac[emit_op_extends_next_var, cs_extends_trans, arithmeticTheory.LESS_EQ_TRANS]
QED

Theorem account_read_emit[local]:
  MEM opc [BALANCE; EXTCODESIZE; EXTCODEHASH; GT; CODESIZE] /\
  (opc = GT ==> ?x. xs = [x;Lit 0w]) /\
  emit_op opc xs sa = (op,sb) /\ fn_has_code sa sb func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
  EVERY (\x. op_taint tn x = {}) xs /\
  (!out. step_inst_base (mk_inst sa.cs_next_id opc xs [out]) s = OK (update_var out w s)) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ alloca_history func s /\
  alloca_inv s /\ allocas_from lo s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?t G' tn'. ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ local_ptrs_reserved cenv sb /\
    alloca_history func t /\
    (t with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!p. not_fresh_at sa p ==> lookup_var p t = lookup_var p s /\
      FLOOKUP G' p = FLOOKUP G p /\ op_taint tn' (Var p) = op_taint tn (Var p)) /\
    eval_operand op t = SOME w /\ op_taint tn' op = {} /\ op_prov G' op = NONE /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn')) /\
    (!H. stmt_state_rel H ctx func cenv cx ee s ==> stmt_state_rel H ctx func cenv cx ee t)
Proof
  strip_tac >>
  qabbrev_tac `dst = STRING #"%" (toString sa.cs_next_var)` >>
  qabbrev_tac `inst = mk_inst sa.cs_next_id opc xs [dst]` >>
  qabbrev_tac `u = update_var dst w s` >>
  qexistsl_tac [`u with vs_inst_idx := SUC s.vs_inst_idx`,
    `step_prov PG G inst u`, `step_taint inst s u tn`] >>
  `op = Var dst /\ sb.cs_current_bb = sa.cs_current_bb /\
   LENGTH sb.cs_current_insts = SUC (LENGTH sa.cs_current_insts) /\
   sa.cs_next_var <= sb.cs_next_var` by
    gvs[Abbr `dst`, emit_op_def, comp_bind_def,
        fresh_var_def, fresh_id_def, comp_ignore_bind_def, comp_return_def, emit_def] >>
  `!p. not_fresh_at sa p ==> p <> dst` by simp[Abbr `dst`, not_fresh_at_def] >>
  `local_ptrs_reserved cenv sb` by metis_tac[local_ptrs_reserved_next_var] >>
  `!p. not_fresh_at sa p ==>
   lookup_var p (u with vs_inst_idx := SUC s.vs_inst_idx) = lookup_var p s /\
   FLOOKUP (step_prov PG G inst u) p = FLOOKUP G p /\
   op_taint (step_taint inst s u tn) (Var p) = op_taint tn (Var p)` by
    (rpt strip_tac >> `p <> dst` by metis_tac[] >>
     simp[Abbr `u`, Abbr `inst`, lookup_var_def, update_var_def,
       FLOOKUP_UPDATE, step_prov_other_output, step_taint_other_output, mk_inst_def]) >>
  suspend "taint"
QED

Resume account_read_emit[taint]:
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
  `op_taint (step_taint inst s u tn) (Var dst) = {}` by
    (qpat_x_assum `MEM opc _` mp_tac >> simp[] >> strip_tac >>
     simp[Abbr `inst`, step_taint_def, op_taint_def, set_var_taint_def,
       mk_inst_def, FLOOKUP_UPDATE, out_taint_def] >>
     rpt (BasicProvers.TOP_CASE_TAC >> fs[])) >>
  `op_prov (step_prov PG G inst u) (Var dst) = NONE` by
    (irule step_prov_out_none >>
     qpat_x_assum `MEM opc _` mp_tac >> simp[] >> strip_tac >>
     simp[Abbr `inst`, mk_inst_def, out_prov_def]) >>
  `?bb. lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
        get_instruction bb s.vs_inst_idx = SOME inst` by
    (drule emitted_insts_emit_op >> strip_tac >>
     drule_all fn_has_code_same_block >> strip_tac >>
     first_x_assum (qspec_then `0` mp_tac) >>
     simp[Abbr `inst`, Abbr `dst`] >> metis_tac[]) >>
  `step_inst_base inst s = OK u` by simp[Abbr `inst`, Abbr `u`] >>
  `alloca_history func (u with vs_inst_idx := SUC s.vs_inst_idx)` by
    (drule_all alloca_history_base_step >>
     qpat_x_assum `MEM opc _` mp_tac >>
     simp[Abbr `inst`, mk_inst_def] >> strip_tac >> gvs[is_terminator_def]) >>
  simp[] >>
  conj_tac >- simp[Abbr `u`, update_var_def, eval_operand_def, lookup_var_def, FLOOKUP_UPDATE] >>
  suspend "path"
QED

Resume account_read_emit[path]:
  `(u with <|vs_vars := s.vs_vars; vs_inst_idx := LENGTH sa.cs_current_insts|>) = s /\
   u.vs_current_bb = s.vs_current_bb /\ ~u.vs_halted /\
   eval_operand (Var dst) u = SOME w` by
    simp[Abbr `u`, update_var_def, venom_state_component_equality,
         eval_operand_def, lookup_var_def, FLOOKUP_UPDATE] >>
  simp[] >> reverse conj_tac
  >- (simp[stmt_state_rel_inst_idx, Abbr `u`] >> rpt strip_tac >>
      irule stmt_state_rel_update_var >> simp[] >>
      irule fresh_not_local_ptr >> qexists_tac `sa` >> simp[Abbr `dst`, not_fresh_at_def]) >>
  qx_gen_tac `D` >>
  `inst_mem_below_frontier inst s /\ inst_dload_in_section inst s` by
    (qpat_x_assum `MEM opc _` mp_tac >> simp[] >> strip_tac >>
     simp[Abbr `inst`, mk_inst_def, unitTransformDefsTheory.inst_mem_below_frontier_def,
          inst_dload_in_section_def, source_memory_read_ranges_def, source_memory_write_ranges_def]) >>
  `taint_ok func tn inst s` by
    (qpat_x_assum `MEM opc _` mp_tac >> simp[] >> strip_tac >>
     simp[taint_ok_def, Abbr `inst`, mk_inst_def, source_memory_read_ranges_def] >>
     fs[EVERY_MEM, GSYM IMP_DISJ_THM] >> rpt strip_tac >> gvs[] >> metis_tac[op_taint_def]) >>
  `inst.inst_opcode <> INVOKE /\ ~is_terminator inst.inst_opcode /\
   inst.inst_opcode <> GAS /\ inst.inst_opcode <> DALLOCA` by
    (qpat_x_assum `MEM opc _` mp_tac >> simp[] >> strip_tac >>
     simp[Abbr `inst`, mk_inst_def, is_terminator_def]) >>
  `ptr_inst_ok D lo 0 ctx func G tn inst s` by
    (simp[ptr_inst_ok_def, step_inst_non_invoke] >>
     qpat_x_assum `MEM opc _` mp_tac >> simp[] >> strip_tac >>
     fs[Abbr `inst`, mk_inst_def, access_ok_def, source_memory_read_ranges_def,
        source_memory_write_ranges_def, EVERY_MEM, Abbr `u`, update_var_def]) >>
  `gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (s,G,tn) []
     (OK (u with vs_inst_idx := SUC s.vs_inst_idx), step_prov PG G inst u,
       step_taint inst s u tn)` by
    (`ctx_has_dalloca ctx ==> unitTransformDefs$dalloca_no_wrap inst s` by
       simp[dalloca_no_wrap_non_dalloca] >>
     drule_all straight_line_origin_ptr_edge >> simp[]) >>
  drule (cj 2 gas_origin_ptr_path_rules) >>
  disch_then (qspec_then `[]` mp_tac) >> simp[] >>
  disch_then irule >> irule (cj 1 gas_origin_ptr_path_rules) >> simp[]
QED

Finalise account_read_emit
