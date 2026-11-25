(* Location-independent fixed array bounds and address execution. *)
Theory bodyArrayFixedCountedPathMods
Ancestors
  bodyFullTargetArraySuffix bodyFullTargetArrayLoad bodyBinopFragMemory
  stmtReasonLitFragMemory
  exprSimArrayIndex exprLoweringProps emitHelperProps emitHelper freshWrites
  fragExec fragGasOriginPtr compileEnv ptrDiscipline venomInst venomState
  venomExecSemantics words rich_list list
  exprSimSubscriptArraySource exprSimSubscriptArraySuffix vyperArray
  overflowElimHelpers integer_word vyperState vyperValue finite_map
  exprSimVVFrame exprSimSubscriptArrayFramed loweringPosts context
  typedCopyLayoutPtr bodyPtrDefs bodyPtrBopHashFootprint exprSimCopy
  valueEncoding vyperLookupStorage vyperAssignPreservesType vyperTyping
  valueTypingMemoryProps exprSimMemDefs exprSimProps loweringStateRelDefs
  bodyFullTargetAttribute bodyFullUnwrapRun bodyPtrSignedConvertSourceFrame
  exprSimWordArgs exprSimHash exprSimDefs gasOutcomeFullCompose exprLowering
  vyperAST

Theorem array_fixed_counted_path_mods:
  compile_array_subscript bop iop F n ws esz sgn loader sn = (dst,sb) /\
  fn_has_code sn sb fn /\
  eval_operand bop u = SOME a /\
  eval_operand iop u = SOME iw /\
  op_taint tn bop = {} /\
  op_taint tn iop = {} /\
  op_prov G iop = NONE /\
  (!x. bop = Var x ==> not_fresh_at sn x) /\
  (!x. iop = Var x ==> not_fresh_at sn x) /\
  allocas_from lo u /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
  ~u.vs_halted /\
  u.vs_current_bb = sn.cs_current_bb /\
  u.vs_inst_idx = LENGTH sn.cs_current_insts /\
  alloca_history fn u ==>
  ?q Gq tq.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (u,G,tn) []
      (if idx_in_range sgn iw (n2w n) then OK q else Abort Revert_abort q,Gq,tq)) /\
    (idx_in_range sgn iw (n2w n) ==>
      ~q.vs_halted /\
      q.vs_current_bb = sb.cs_current_bb /\
      q.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_history fn q /\
      eval_operand dst q = SOME (a + iw * n2w esz) /\
      op_prov Gq dst = op_prov G bop /\
      op_taint tq dst = {} /\
      array_length_frame sn u G tn q Gq tq)
Proof
  strip_tac >>
  qpat_x_assum `_ = (dst,sb)` mp_tac >>
  simp[compile_array_subscript_split, comp_bind_def, comp_ignore_bind_def,
      comp_return_def] >> pairarg_tac >> simp[] >> strip_tac >>
  rename1 `array_bounds_check _ _ _ sn = (unit,sc)` >>
  Cases_on `unit` >> gvs[] >>
  `same_blocks sn sc /\
   sc.cs_current_insts = sn.cs_current_insts ++ emitted_insts sn sc /\
   EVERY (\ins. ins.inst_opcode <> INVOKE /\ ins.inst_opcode <> GAS /\
                ~is_terminator ins.inst_opcode) (emitted_insts sn sc) /\
   EVERY (\ins. ins.inst_opcode <> ALLOCA) (emitted_insts sn sc)` by
    (qpat_x_assum `array_bounds_check _ _ _ _ = _` mp_tac >>
     simp[array_bounds_check_def, comp_bind_def] >> pairarg_tac >> simp[] >> strip_tac >>
     qpat_x_assum `array_bounds_valid _ _ _ _ = _` mp_tac >>
     simp[array_bounds_valid_def, comp_bind_def] >>
     Cases_on `sgn` >> simp[comp_return_def] >>
     rpt (pairarg_tac >> simp[]) >> strip_tac >>
     imp_res_tac emitted_insts_emit_op >> imp_res_tac emitted_insts_emit_void >>
     imp_res_tac emit_op_extends >> imp_res_tac emit_void_extends >>
     rpt (qpat_x_assum `_.cs_current_insts = _.cs_current_insts ++ emitted_insts _ _` kall_tac) >>
     gvs[same_blocks_def] >>
     simp[emitted_insts_def, DROP_LENGTH_APPEND, APPEND_ASSOC,
          mk_inst_def, is_terminator_def]) >>
  `same_blocks sc sb /\
   sb.cs_current_insts = sc.cs_current_insts ++ emitted_insts sc sb /\
   EVERY (\ins. ins.inst_opcode <> INVOKE /\ ins.inst_opcode <> GAS /\
                ~is_terminator ins.inst_opcode) (emitted_insts sc sb) /\
   EVERY (\ins. ins.inst_opcode <> ALLOCA) (emitted_insts sc sb)` by
    (qpat_x_assum `sc.cs_current_insts = _.cs_current_insts ++ _` kall_tac >>
     qpat_x_assum `array_elem_ptr _ _ _ _ _ _ = _` mp_tac >>
     simp[array_elem_ptr_def, comp_bind_def, comp_return_def] >>
     rpt (pairarg_tac >> simp[]) >> strip_tac >>
     imp_res_tac emit_op_extends >> imp_res_tac emitted_insts_emit_op >>
     rpt (qpat_x_assum `_.cs_current_insts = _.cs_current_insts ++ emitted_insts _ _` kall_tac) >>
     gvs[same_blocks_def] >>
     simp[emitted_insts_def, DROP_LENGTH_APPEND, APPEND_ASSOC,
          mk_inst_def, is_terminator_def]) >>
  `cs_extends sn sc /\ cs_extends sc sb` by
     fs[cs_extends_def, same_blocks_def, IS_PREFIX_APPEND] >>
  drule_all_then strip_assume_tac fn_has_code_split >>
  `eval_operand (Lit (n2w n)) u = SOME (n2w n) /\
   (!x. Lit (n2w n) = Var x ==> not_fresh_at sn x) /\
   op_prov G (Lit (n2w n)) = NONE /\
   op_taint tn (Lit (n2w n)) = {}` by
    simp[eval_operand_def, op_prov_def, op_taint_def] >>
  drule_all array_tail_scalar_uniform >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choosel_then [`q`,`Gq`,`tq`] strip_assume_tac)) >>
  qexistsl [`q`,`Gq`,`tq`] >> simp[] >> strip_tac >>
  `q.vs_allocas = u.vs_allocas /\ q.vs_current_bb = u.vs_current_bb` by
    fs[venom_state_component_equality] >>
  `alloca_history fn q` by
    (`emitted_insts sn sb = emitted_insts sn sc ++ emitted_insts sc sb` by
       metis_tac[emitted_insts_append] >>
     `sb.cs_current_insts = sn.cs_current_insts ++ emitted_insts sn sb /\
      EVERY (\i. i.inst_opcode <> ALLOCA) (emitted_insts sn sb)` by
       simp[APPEND_ASSOC] >>
     `sb.cs_current_bb = sn.cs_current_bb` by fs[same_blocks_def] >>
     drule_all_then strip_assume_tac fn_has_code_code >> fs[IS_PREFIX_APPEND] >>
     `q.vs_inst_idx = u.vs_inst_idx + LENGTH (emitted_insts sn sb)` by simp[] >>
     `alloca_history fn (q with vs_inst_idx := q.vs_inst_idx)` suffices_by simp[] >>
     qpat_assum `q.vs_inst_idx = u.vs_inst_idx + _` SUBST1_TAC >>
     irule alloca_history_no_alloca_slice >> simp[] >> qexistsl [`bb`,`l`] >> simp[]) >>
  fs[array_length_frame_def, lookup_var_def, venom_state_component_equality]
QED
