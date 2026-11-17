(* Literal immutable loads use one endpoint before the horizon is chosen. *)
Theory augAssignFullLoadImmutableJoin
Ancestors
  augAssignFullImmutableSetup augAssignFullLoadImmutableResources
  augAssignFullLoadMemoryStep bodyImmutableAugAssignFacts
  vyperTypeCallStackSoundness bodyPtrDefs exprSimHypsDefs stmtSimAugAssignPlace
  gasOutcomeFull ptrDiscipline venomExecSemantics venomInst venomState
  stateFrame compileEnv finite_map words list arithmetic

Theorem augassign_immutable_load_joint:
  body_inv tops ctx cenv cx /\ expr_sim_inv cenv cx env es /\
  supported_immutable_type tops (src,id) = SOME ity /\
  type_stmt env ret_ty
    (AugAssign ty (TopLevelNameTarget (src,id)) bop e) = SOME env' /\
  stmt_exprs_ok cenv (AugAssign ty (TopLevelNameTarget (src,id)) bop e) /\
  call_evaluation_safe cx
    (int_calls_stmt (AugAssign ty (TopLevelNameTarget (src,id)) bop e)) /\
  (!H. horizon_ok H ==> dead_lo_ok H (DF H) lo cenv cx /\
    stmt_state_rel H ctx func cenv cx es s /\
    ghost_inv_at (DF H) lo d cenv cx es G tn s) /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s)
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
      s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
      ?x i raw u G1 tn1.
        x = STRING #"%" (toString sa.cs_next_var) /\
        i = mk_inst sa.cs_next_id MLOAD [Lit (n2w off)] [x] /\
        raw = update_var x (mload off s) s /\
        u = (raw with vs_inst_idx := SUC s.vs_inst_idx) /\
        G1 = step_prov PG G i raw /\ tn1 = step_taint i s raw tn /\
        (!H. horizon_ok H ==>
          off + 32 <= lo /\ w2n ((n2w off):bytes32) = off /\
          mload off s = typed_val_to_w256 tv cur /\
          gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG)
            (s,G,tn) [] (OK u,G1,tn1) /\
          eval_operand old u = SOME (typed_val_to_w256 tv cur) /\
          eval_operand (Lit (n2w off)) u = SOME (n2w off) /\
          op_taint tn1 old = {} /\ op_prov G1 old = NONE /\
          ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
          u.vs_inst_idx = LENGTH sb.cs_current_insts /\
          state_frame u = state_frame (s with vs_inst_idx := u.vs_inst_idx) /\
          tn1.t_mem = tn.t_mem /\ tn1.t_stor = tn.t_stor /\
          tn1.t_trans = tn.t_trans /\ tn1.t_imm = tn.t_imm /\
          (!q. not_fresh_at sa q ==> lookup_var q u = lookup_var q s /\
            FLOOKUP G1 q = FLOOKUP G q /\
            op_taint tn1 (Var q) = op_taint tn (Var q))))
Proof
  strip_tac >>
  `cx.in_deploy` by metis_tac[augassign_immutable_in_deploy] >>
  `call_evaluation_safe cx []` by
    (irule call_evaluation_safe_mono >> goal_assum (drule_at Any) >> simp[]) >>
  drule_all immutable_augassign_metadata >> strip_tac >>
  drule_all immutable_augassign_entry >> strip_tac >>
  drule_all immutable_augassign_source_prefix >> strip_tac >>
  qexistsl_tac [`off`, `tv`, `v`] >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `x = STRING #"%" (toString sa.cs_next_var)` >>
  qabbrev_tac `i = mk_inst sa.cs_next_id MLOAD [Lit (n2w off)] [x]` >>
  qabbrev_tac `raw = update_var x (mload off s) s` >>
  qabbrev_tac `u = (raw with vs_inst_idx := SUC s.vs_inst_idx)` >>
  qabbrev_tac `G1 = step_prov PG G i raw` >>
  qabbrev_tac `tn1 = step_taint i s raw tn` >>
  qexistsl_tac [`x`, `i`, `raw`, `u`, `G1`, `tn1`] >>
  rpt (conj_tac >- (simp_tac bool_ss [Abbr `x`, Abbr `i`, Abbr `raw`,
    Abbr `u`, Abbr `G1`, Abbr `tn1`])) >>
  qx_gen_tac `H` >> disch_tac >>
  qpat_x_assum `!H. horizon_ok H ==> _` (qspec_then `H` mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
  drule_all augassign_immutable_load_resources >> strip_tac >>
  gvs[] >>
  qpat_assum `!iid out. ptr_inst_ok _ _ _ _ _ _ _ _ _`
    (qspecl_then [`sa.cs_next_id`, `STRING #"%" (toString sa.cs_next_var)`] assume_tac) >>
  qspecl_then [`\h. T`, `\h. DF H`] (mp_tac o SRULE [])
    augassign_mload_joint_step >>
  disch_then (drule_at (Pos last)) >>
  disch_then (drule_at (Pos hd)) >>
  disch_then (drule_at (Pos hd)) >>
  disch_then (qspecl_then [`explicit`, `PG`, `n2w off`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  gvs[Abbr `x`, Abbr `i`, Abbr `raw`, Abbr `u`, Abbr `G1`, Abbr `tn1`,
    update_var_def]
QED
