(* Immutable literal loads retain the complete RHS-entry frame. *)
Theory augAssignFullLoadImmutableFrame
Ancestors
  augAssignFullLoadImmutableJoin augAssignFullLoadFrame bodyFullTargetDefs
  emitHelperProps exprLoweringProps freshWrites ptrDiscipline venomInst
  venomState stateFrame finite_map words list arithmetic loweringShapeRules

Theorem augassign_immutable_load_framed_joint:
  body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env es /\
  supported_immutable_type tops (src,id) = SOME ity /\
  type_stmt env ret_ty (AugAssign ty (TopLevelNameTarget (src,id)) bop e) = SOME env' /\
  stmt_exprs_ok cenv (AugAssign ty (TopLevelNameTarget (src,id)) bop e) /\
  call_evaluation_safe cx
    (int_calls_stmt (AugAssign ty (TopLevelNameTarget (src,id)) bop e)) /\
  (!H. horizon_ok H ==>
    dead_lo_ok H (DF H) lo cenv cx /\
    stmt_state_rel H ctx func cenv cx es s /\
    ghost_inv_at (DF H) lo d cenv cx es G tn s /\
    ghost_kept_at lo cenv es entry G0 tn0 s0 G tn) /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ alloca_history func s
  ==>
  ?off tv cur.
    cx.in_deploy /\ src = cenv.ce_module /\ cenv.ce_is_ctor /\ ty = ity /\
    FLOOKUP cenv.ce_module_vars (src,id) = SOME (ImmutableLoc off) /\
    cenv.ce_module_var_type (src,id) = SOME ty /\ is_word_type ty /\
    evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv cur /\
    eval_target_place cx (TopLevelNameTarget (src,id)) es =
      (INL (ImmutablePlace src id []),es) /\
    read_place cx (ImmutablePlace src id []) es = (INL cur,es) /\
    place_type_value cx (ImmutablePlace src id []) es = (INL tv,es) /\
    (!sa old sb.
      emit_op MLOAD [Lit (n2w off)] sa = (old,sb) /\
      fn_has_code sa sb func /\ ~s.vs_halted /\
      s.vs_current_bb = sa.cs_current_bb /\
      s.vs_inst_idx = LENGTH sa.cs_current_insts /\
      local_ptrs_reserved cenv sa /\
      (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
      (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
      entry.cs_next_var <= sa.cs_next_var /\ return_buf_frame d cenv sa s
      ==>
      ?u G1 tn1.
        !H. horizon_ok H ==>
          off + 32 <= lo /\ w2n ((n2w off):bytes32) = off /\
          mload off s = typed_val_to_w256 tv cur /\
          gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
            (s,G,tn) [] (OK u,G1,tn1) /\
          eval_operand old u = SOME (typed_val_to_w256 tv cur) /\
          eval_operand (Lit (n2w off)) u = SOME (n2w off) /\
          op_taint tn1 old = {} /\ op_prov G1 old = NONE /\
          (!x. old = Var x ==> not_fresh_at sb x) /\
          local_ptrs_reserved cenv sb /\
          (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sb x) /\
          (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sb x) /\
          stmt_state_rel H ctx func cenv cx es u /\
          ghost_inv_at (DF H) lo d cenv cx es G1 tn1 u /\
          target_ptr_ok cenv (PlaceR (ImmutablePlace src id []))
            (Lit (n2w off),SOME LocMemory,SOME (ValPT ty)) G1 tn1 u /\
          ghost_kept_at lo cenv es entry G0 tn0 s0 G1 tn1 /\
          return_buf_frame d cenv sb u /\ alloca_history func u /\
          u.vs_alloca_next = s.vs_alloca_next /\
          (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
          ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
          u.vs_inst_idx = LENGTH sb.cs_current_insts)
Proof
  strip_tac >>
  mp_tac augassign_immutable_load_joint >>
  disch_then (drule_at (Pos hd)) >>
  (impl_tac >- metis_tac[]) >> strip_tac >>
  qexistsl_tac [`off`, `tv`, `cur`] >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  rpt gen_tac >> strip_tac >>
  first_x_assum (drule_at (Pos hd)) >>
  (impl_tac >- metis_tac[]) >> strip_tac >>
  qexistsl_tac [`u`, `G1`, `tn1`] >>
  qx_gen_tac `H` >> disch_tac >>
  qpat_x_assum `!H. horizon_ok H ==> _` (qspec_then `H` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  qpat_x_assum `!H. horizon_ok H ==> _` (qspec_then `H` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule emit_op_extends >> simp[same_blocks_def] >> strip_tac >>
  `sa.cs_next_var <= sb.cs_next_var` by simp[] >>
  `target_ptr_ok cenv (PlaceR (ImmutablePlace src id []))
     (Lit (n2w off),SOME LocMemory,SOME (ValPT ty)) G tn s` by
    simp[target_ptr_ok_def, op_taint_def] >>
  drule_at (Pos (el 3)) augassign_load_endpoint_frame >>
  disch_then drule >> disch_then drule >> disch_then drule >>
  disch_then (drule_at (Pat `state_frame _ = _`)) >>
  disch_then (drule_at (Pos (el 11))) >>
  disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  disch_then (qspec_then `n2w off` mp_tac) >>
  (impl_tac >- simp[eval_operand_def, mk_inst_def]) >> strip_tac >>
  drule emit_op_facts >> strip_tac >> gvs[] >>
  conj_tac >- (irule local_ptrs_reserved_next_var >> goal_assum (drule_at Any) >> simp[]) >>
  conj_tac >> rpt strip_tac >>
  irule freshWritesTheory.not_fresh_at_mono >>
  qexists_tac `sa` >> simp[]
QED
