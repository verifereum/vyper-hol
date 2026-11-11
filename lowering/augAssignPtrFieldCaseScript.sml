(* Counted local-struct-field augmented assignment. *)
Theory augAssignPtrFieldCase
Ancestors
  augAssignPtrFieldInputs augAssignPtrFieldLayout augAssignPtrFieldLoadClean
  augAssignPtrFieldSource augAssignPtrFieldCertificates augAssignPtrFieldWriteSource augAssignPtrFieldStoreCase
  augAssignPtrLocalCase augAssignPtrLocalCertificates augAssignPtrOperator
  augAssignPtrTypedContinuation augAssignPtrSource augAssignPtrRhsFrame
  bodyPtrPreds bodyPtrDefs stmtFragPtr stmtSimAugAssignAttr stmtSimAugAssign
  exprSimHyps exprSimProps exprSimHypsDefs exprSimSource exprLoweringProps
  gasSummaryComposePtr fragGasPathPtr fragGasPath gasSummary gasCount gasContext
  vyperInterpreter vyperState vyperTypeSystem vyperAST loweringPosts compileEnv loweringStateRelDefs
  emitHelper list rich_list stmtSimProps exprReasonOperand exprOperandVar
  exprBopSimProps ptrDiscipline venomState venomExecSemantics vyperTypeBuiltins stmtSimDeclMem

Theorem compile_augassign_attr_local_case_ptr:
  body_expr_ptr_ok cx e /\ body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env e es /\
  FLOOKUP env.var_types id = SOME (StructT sid) /\
  ALOOKUP (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid))
    fld = SOME (ty,fsz) /\
  (bop = Exp ==> nonneg_int_literal e) /\
  (bop = ShL \/ bop = ShR ==> shift_amount_ok e) /\
  well_typed_binop ty bop ty (expr_type e) /\ bop <> In /\ bop <> NotIn ==>
  stmt_frag_ptr d ctx PG func cx lctx RetQ cenv
    (stmt_env cenv lctx ty0
      (AugAssign ty (AttributeTarget (NameTarget id) fld) bop e))
    (eval_stmt cx (AugAssign ty (AttributeTarget (NameTarget id) fld) bop e)) es
Proof
  strip_tac >> simp[stmt_frag_ptr_def] >> rpt gen_tac >> strip_tac >>
  `expr_sim_inv cenv cx env es` by fs[expr_body_pre_def] >>
  `word_value_type ty /\ word_value_type (expr_type e)` by
    metis_tac[well_typed_binop_augassign_word] >>
  `is_word_type ty` by metis_tac[word_value_type_word] >>
  drule_all augassign_attr_field_inputs_ptr >> strip_tac >>
  drule_all augassign_attr_local_layout_ptr >> strip_tac >> gvs[] >>
  `?dstv. dst = Var dstv` by metis_tac[emitted_insts_emit_op_local] >> gvs[] >>
  `?out. cur = Var out` by metis_tac[emitted_insts_emit_op_local] >> gvs[] >>
  drule_all augassign_field_load_clean_ptr >>
  disch_then (qspecl_then [`PG`, `cx_dead cx`] strip_assume_tac) >>
  `expr_body_pre cenv cx env e (es with gas_obs := [])` by
    fs[expr_body_pre_def] >>
  `expr_sim_ptr d ctx PG func cenv cx ty e (es with gas_obs := [])` by
    (qpat_x_assum `body_expr_ptr_ok _ _`
       (mp_tac o REWRITE_RULE [body_expr_ptr_ok_def]) >>
     disch_then (irule o cj 1 o CONJUNCT1) >> metis_tac[]) >>
  `gas_admissible (bind (eval_expr cx e) (read_result cx)) expr_res_ok
     (es with gas_obs := [])` by
    (simp[] >> irule augassign_attr_rhs_admissible_ptr >>
     rpt (goal_assum (drule_at Any)) >> simp[]) >>
  suspend "rhs_entry"
QED

Resume compile_augassign_attr_local_case_ptr[rhs_entry]:
  `stmt_state_rel ctx func cenv cx (es with gas_obs := []) t` by
    simp[] >>
  `ghost_inv d cenv cx (es with gas_obs := []) H tm t` by
    simp[ghost_inv_gas_obs] >>
  `(!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==>
       not_fresh_at s1 x) /\
   (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==>
       not_fresh_at s1 x)` by
    (conj_tac >> rpt strip_tac >>
     irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sa` >>
     `s1.cs_next_var = sa.cs_next_var + 2` by
       (qpat_x_assum `emit_op ADD _ _ = _` mp_tac >>
        qpat_x_assum `emit_op MLOAD _ _ = _` mp_tac >>
        rpt (disch_then (strip_assume_tac o
          MATCH_MP emitted_insts_emit_op_local)) >> simp[]) >>
     fs[ret_pc_ok_def]) >>
  qpat_x_assum `expr_sim_ptr _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_sim_ptr_def]) >>
  disch_then (qspecl_then [`s1`, `s2`, `rhs`, `t`, `H`, `tm`] mp_tac) >>
  (impl_tac >- simp[]) >> disch_tac >>
  suspend "rhs_continuation"
QED
Resume compile_augassign_attr_local_case_ptr[rhs_continuation]:
  qpat_x_assum `gas_outcome_ptr _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [gas_outcome_ptr_def])
  >- suspend "rhs_summary" >> suspend "rhs_exempt"
QED
Resume compile_augassign_attr_local_case_ptr[rhs_summary]:
  qpat_x_assum `gas_summary_ptr_at _ _ _ _ _ _ _ _` mp_tac >>
  simp[gas_summary_ptr_at_def] >> strip_tac
  >- suspend "rhs_normal" >> suspend "rhs_exception"
QED

Resume compile_augassign_attr_local_case_ptr[rhs_exception]:
  `?ex. res = INR ex` by
    (Cases_on `res` >> gvs[exprSimDefsTheory.expr_exit_def]) >> gvs[] >>
  `gas_marked_exec_ptr (cx_dead cx) (ctx,func) PG
     (bind (eval_expr cx e) (read_result cx))
     (es with gas_obs := [],t,H,tm) marks (INR ex) es_end G tn r` by
    simp[gas_marked_exec_ptr_def] >>
  drule_all augassign_attr_rhs_exception_exec_ptr >>
  disch_then (qspecl_then [`ty`, `bop`] assume_tac) >>
  simp[gas_outcome_ptr_def] >> qexists_tac `marks` >> disj1_tac >>
  simp[gas_summary_ptr_at_marked] >>
  goal_assum (drule_at Any) >> disj2_tac >>
  simp[stmt_exit_ptr_def] >> metis_tac[stmtSimPropsTheory.expr_exit_INR_type]
QED

Resume compile_augassign_attr_local_case_ptr[rhs_exempt]:
  `gas_marked_exec_ptr (cx_dead cx) (ctx,func) PG
     (eval_target_place cx (AttributeTarget (NameTarget id) fld))
     (es,s0,G0,tn0) [] (INL (MemoryPlace id [AttrSubscript fld])) es H tm (OK t)` by
    (simp[gas_marked_exec_ptr_def, gas_explicit_def] >>
     gen_tac >> irule (cj 1 augassign_attr_place_reads_ptr) >>
     rpt (goal_assum (drule_at Any)) >> simp[]) >>
  drule_all augassign_attr_rhs_exempt_ptr >> disch_tac >>
  simp[gas_outcome_ptr_def] >> metis_tac[]
QED

Resume compile_augassign_attr_local_case_ptr[rhs_normal]:
  gvs[] >>
  `bind (eval_expr cx e) (read_result cx)
     (es with gas_obs := gas_explicit marks t.vs_gas_readings) =
     (INL v,es_end with gas_obs := [])` by
    (first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  `!gs. eval_target_place cx (AttributeTarget (NameTarget id) fld)
          (es with gas_obs := gs) =
          (INL (MemoryPlace id [AttrSubscript fld]),es with gas_obs := gs) /\
        read_place cx (MemoryPlace id [AttrSubscript fld]) (es with gas_obs := gs) =
          (INL fv,es with gas_obs := gs) /\
        place_type_value cx (MemoryPlace id [AttrSubscript fld]) (es with gas_obs := gs) =
          (INL ftv,es with gas_obs := gs)` by
    (gen_tac >> irule augassign_attr_place_reads_ptr >>
     rpt (goal_assum (drule_at Any)) >> simp[]) >>
  drule_all augassign_pure_prefix_binop_admissible >> disch_tac >>
  `expr_body_pre cenv cx env e
     (es with gas_obs := gas_explicit marks t.vs_gas_readings)` by
    fs[expr_body_pre_def] >>
  drule_all (REWRITE_RULE [ETA_AX] expr_body_pre_word_result) >>
  strip_tac >> gvs[] >>
  `eval_operand (Var out) t = SOME (val_to_w256 fv)` by
    simp[eval_operand_def] >>
  `eval_operand rhs t' = SOME (val_to_w256 v)` by
    (irule expr_val_rel_word >> fs[expr_post_def] >>
     goal_assum (drule_at Any) >> simp[word_value_type_word]) >>
  `eval_operand (Var out) t' = SOME (val_to_w256 fv)` by
    (irule eval_operand_frame >> simp[] >> qexistsl [`s1`, `t`] >>
     fs[expr_post_def]) >>
  `op_prov G (Var out) = NONE /\ op_taint tn (Var out) = {}` by
    (drule_all ghost_kept_old_operand >> fs[op_prov_def]) >>
  `op_prov G rhs = NONE /\ op_taint tn rhs = {}` by
    (qpat_x_assum `ptr_val_ok _ _ _ _ _ _ _` mp_tac >>
     simp[ptr_val_ok_def, word_value_type_word]) >>
  suspend "operator_inputs"
QED
Resume compile_augassign_attr_local_case_ptr[operator_inputs]:
  `!id ty. FLOOKUP env.var_types id = SOME ty ==>
     ?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)` by
    fs[expr_sim_inv_def] >>
  `well_typed_expr env e` by fs[expr_body_pre_def] >>
  `!l. Var out <> Label l /\ rhs <> Label l` by
    (simp[] >> drule_all lower_compile_expr_not_label >> simp[]) >>
  `well_formed_type (get_tenv cx) ty` by
    simp[well_formed_type_def] >>
  `type_bits ty MOD 8 = 0` by metis_tac[well_formed_type_bits] >>
  drule (cj 2 compile_expr_grows) >> strip_tac >>
  `not_fresh_at s2 out /\ local_ptrs_reserved cenv s2` by
    (conj_tac
     >- (irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `s1` >>
         fs[cs_extends_def]) >>
     irule local_ptrs_reserved_next_var >> qexists_tac `s1` >>
     fs[cs_extends_def]) >>
  `stmt_state_rel ctx func cenv cx (es_end with gas_obs := []) t'` by
    fs[expr_post_def] >>
  `~t'.vs_halted` by
    metis_tac[gas_path_ptr_erase, fragGasPathTheory.gas_path_normal] >>
  `(!z. Var out = Var z ==> not_fresh_at s2 z) /\
   (!z. rhs = Var z ==> not_fresh_at s2 z)` by
    (simp[] >> metis_tac[compile_lower_value_var]) >>
  `(!z sz. cenv.ce_return_pc = SOME (PtrVar (Var z) sz) ==>
       not_fresh_at s2 z) /\
   (!z sz. cenv.ce_return_buf = SOME (PtrVar (Var z) sz) ==>
       not_fresh_at s2 z)` by
    (conj_tac >> rpt strip_tac >>
     irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `s1` >> fs[cs_extends_def]) >>
  suspend "literal_inputs"
QED
Resume compile_augassign_attr_local_case_ptr[literal_inputs]:
  `?tv er. eval_expr cx e
       (es with gas_obs := gas_explicit marks t.vs_gas_readings) = (INL tv,er) /\
     read_result cx tv er = (INL v,es_end with gas_obs := [])` by
    (qpat_x_assum `bind _ _ _ = _` mp_tac >>
     simp[bind_def, AllCaseEqs()] >> metis_tac[]) >>
  `(bop = ShL \/ bop = ShR ==> ?i. v = IntV i /\ 0 <= i)` by
    metis_tac[eval_expr_shift_amount] >>
  `(bop = Exp ==> (?n. expr_int_literal e = SOME n /\ 0 <= n) /\
     (!n. expr_int_literal e = SOME n ==> v = IntV n))` by
    (strip_tac >> gvs[] >>
     `!n. expr_int_literal e = SOME n ==> v = IntV n` by
       metis_tac[eval_expr_int_literal_agrees] >>
     fs[nonneg_int_literal_def, GSYM expr_int_literal_value] >>
     Cases_on `expr_int_literal e` >> gvs[]) >>
  `!z. not_fresh_at s1 z ==> not_fresh_at s2 z` by
    metis_tac[freshWritesTheory.not_fresh_at_mono] >>
  drule augassign_clean_operator_ptr >>
  disch_then (drule_at (Pat `eval_operand _ _ = _`)) >>
  disch_then (drule_at (Pat `eval_operand _ _ = _`)) >>
  disch_then drule_all >>
  disch_then (qspecl_then [`PG`, `cx_dead cx`] strip_assume_tac)
  >- suspend "operator_normal" >> suspend "operator_abort"
QED
Resume compile_augassign_attr_local_case_ptr[operator_abort]:
  `bop_result cx ty bop [ty;expr_type e] fv v es_end =
     case evaluate_binop
       (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
       ftv bop fv v of INL z => INL z | INR err => INR (Error err)` by
    (irule bop_result_augassign >> simp[]) >>
  `evaluate_binop
      (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
      ftv bop fv v = INR (RuntimeError msg)` by
    (qpat_x_assum `bop_result _ _ _ _ _ _ _ = (case _ of INL z => _ | INR err => _)` mp_tac >>
     simp[CaseEq "sum"]) >>
  `gas_marked_exec_ptr (cx_dead cx) (ctx,func) PG
     (bind (eval_expr cx e) (read_result cx))
     (es with gas_obs := [],t,H,tm) marks (INL v) es_end G tn (OK t')` by
    simp[gas_marked_exec_ptr_def] >>
  drule_all augassign_attr_error_continuation_exec_ptr >>
  disch_then (qspecl_then [`id`, `fld`, `es_end with gas_obs := []`, `cx`] assume_tac) >>
  drule_all augassign_attr_rhs_normal_exec_ptr >> strip_tac >>
  simp[gas_outcome_ptr_def] >> qexists_tac `marks` >> disj1_tac >>
  simp[gas_summary_ptr_at_marked] >>
  goal_assum (drule_at Any) >> disj2_tac >>
  simp[stmt_exit_ptr_def, exprSimDefsTheory.expr_exit_def,
       fragExecTheory.exit_result_def]
QED
Resume compile_augassign_attr_local_case_ptr[operator_normal]:
  rename1 `bop_result cx ty bop [ty;expr_type e] fv v es_end = INL result` >>
  `bop_result cx ty bop [ty;expr_type e] fv v es_end =
     case evaluate_binop
       (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
       ftv bop fv v of INL z => INL z | INR err => INR (Error err)` by
    (irule bop_result_augassign >> simp[]) >>
  `evaluate_binop
      (case type_to_int_bound ty of SOME b => b | NONE => Unsigned 0)
      ftv bop fv v = INL result` by
    (qpat_x_assum `bop_result _ _ _ _ _ _ _ = (case _ of INL z => _ | INR err => _)` mp_tac >>
     simp[CaseEq "sum"]) >>
  Cases_on `write_place cx (MemoryPlace id [AttrSubscript fld]) result
      (es_end with gas_obs := [])` >>
  rename1 `write_place cx (MemoryPlace id [AttrSubscript fld]) result _ = (wr,fin)` >>
  `!m. wr <> INR (Error (TypeError m))` by
    (irule augassign_attr_write_admissible_ptr >>
     rpt (goal_assum (drule_at Any)) >> simp[] >>
     qexists_tac `es_end` >> simp[]) >>
  `value_has_type ftv result` by
    (irule (Q.INST [`t1` |-> `ty`, `t2` |-> `expr_type e`]
       vyperTypeBuiltinsTheory.well_typed_binop_success_type) >>
     goal_assum (drule_at (Pat `evaluate_binop _ _ _ _ _ = _`)) >>
     qexistsl [`e`, `get_tenv cx`, `ftv`, `tyv`, `ty`] >> simp[]) >>
  `expr_sim_inv cenv cx env (es_end with gas_obs := [])` by simp[] >>
  drule_all augassign_attr_write_all_obs_ptr >> strip_tac >> gvs[] >>
  suspend "store_entry"
QED
Resume compile_augassign_attr_local_case_ptr[store_entry]:
  qmatch_asmsub_abbrev_tac `gas_path_ptr (cx_dead cx) 0 ctx func PG G tn t' 0 H' tm' (OK u)` >>
  `!z w. not_fresh_at s1 z /\ lookup_var z t = SOME w ==>
      lookup_var z u = SOME w` by
    (rpt strip_tac >>
     `not_fresh_at s2 z` by metis_tac[] >>
     `lookup_var z t' = SOME w` by metis_tac[expr_post_def] >>
     metis_tac[]) >>
  `ptr_covers H' tm' dstv u 32` by
    (fs[ptr_covers_def, ghost_kept_def] >> metis_tac[]) >>
  `lookup_var dstv u = SOME (a + n2w (struct_field_offset
      (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid)) fld))` by
    metis_tac[] >>
  `stmt_state_rel ctx func cenv cx es_end u /\
   ghost_inv d cenv cx es_end H' tm' u` by
    (fs[Abbr `u`, ghost_inv_gas_obs, ghost_inv_jump_to]) >>
  suspend "field_store_inputs"
QED
Resume compile_augassign_attr_local_case_ptr[field_store_inputs]:
  `not_fresh_at sa p` by metis_tac[local_ptrs_reserved_def] >>
  `not_fresh_at s1 p` by
    (irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sa` >>
     `s1.cs_next_var = sa.cs_next_var + 2` by
       (qpat_x_assum `emit_op ADD _ _ = _` mp_tac >>
        qpat_x_assum `emit_op MLOAD _ _ = _` mp_tac >>
        rpt (disch_then (strip_assume_tac o MATCH_MP emitted_insts_emit_op_local)) >> simp[]) >>
     simp[]) >>
  `lookup_var p t = SOME a` by metis_tac[] >>
  `lookup_var p u = SOME a` by metis_tac[] >>
  `lookup_scopes id es_end.scopes = SOME entry'` by
    metis_tac[vyperLookupTheory.find_containing_scope_lookup] >>
  `local_ptrs_rel func cenv es_end.scopes u` by
    fs[stmt_state_rel_def, state_rel_def] >>
  `val_wf entry'.type entry'.value /\ w2n a + sz <= u.vs_alloca_next` by
    (qpat_x_assum `local_ptrs_rel func cenv es_end.scopes u` mp_tac >>
     simp[local_ptrs_rel_def] >> strip_tac >>
     qpat_x_assum `!name ent q sq. _` drule_all >> simp[]) >>
  `fields_val_wf vals' fs'` by
    (qpat_x_assum `val_wf entry'.type entry'.value` mp_tac >>
     simp[valueEncodingDefsTheory.val_wf_def]) >>
  `w2n (a + n2w (struct_field_offset
      (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid)) fld)) =
     w2n a + struct_field_offset
      (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid)) fld` by
    (irule buffer_offset_no_wrap >>
     qexists_tac `struct_field_offset
       (get_struct_fields cenv.ce_struct_fields (nsid_to_string sid)) fld` >> simp[]) >>
  `~u.vs_halted /\ u.vs_current_bb = s3.cs_current_bb /\
   u.vs_inst_idx = LENGTH s3.cs_current_insts` by simp[Abbr `u`] >>
  `eval_operand res_op u = SOME (val_to_w256 result)` by simp[Abbr `u`] >>
  drule_all augassign_field_store_case_ptr >>
  disch_then (qspecl_then [`PG`, `cx_dead cx`] strip_assume_tac) >>
  suspend "compose_store"
QED
Resume compile_augassign_attr_local_case_ptr[compose_store]:
  `gas_path_ptr (cx_dead cx) 0 ctx func PG G tn t' 0 H' tnf (OK sf)` by
    (qpat_assum `gas_path_ptr _ _ _ _ _ G tn t' _ _ _ _`
       (mp_then Any mp_tac gas_path_ptr_then) >>
     disch_then drule_all >> simp[]) >>
  qmatch_asmsub_abbrev_tac `stmt_state_rel ctx func cenv cx fin0 sf` >>
  `gas_marked_exec_ptr (cx_dead cx) (ctx,func) PG
     (write_place cx (MemoryPlace id [AttrSubscript fld]) result)
     (es_end with gas_obs := [],t',G,tn) [] (INL ())
     (fin0 with gas_obs := []) H' tnf (OK sf)` by
    (simp[gas_marked_exec_ptr_def, gas_explicit_def, Abbr `fin0`] >>
     gen_tac >> simp[]) >>
  drule_all augassign_attr_store_continuation_exec_ptr >> disch_tac >>
  `gas_marked_exec_ptr (cx_dead cx) (ctx,func) PG
     (bind (eval_expr cx e) (read_result cx))
     (es with gas_obs := [],t,H,tm) marks (INL v) es_end G tn (OK t')` by
    simp[gas_marked_exec_ptr_def] >>
  drule_all augassign_attr_rhs_normal_exec_ptr >> disch_tac >>
  suspend "field_frames"
QED
Resume compile_augassign_attr_local_case_ptr[field_frames]:
  `!x. not_fresh_at sa x ==> not_fresh_at s1 x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sa` >>
     `s1.cs_next_var = sa.cs_next_var + 2` by
       (qpat_x_assum `emit_op ADD _ _ = _` mp_tac >>
        qpat_x_assum `emit_op MLOAD _ _ = _` mp_tac >>
        rpt (disch_then (strip_assume_tac o MATCH_MP emitted_insts_emit_op_local)) >> simp[]) >>
     simp[]) >>
  `!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
      lookup_var x sf = SOME w` by
    (rpt strip_tac >>
     `lookup_var x t = SOME w` by metis_tac[] >> metis_tac[]) >>
  `!x. not_fresh_at sa x ==> FLOOKUP H' x = FLOOKUP G0 x /\
       op_taint tnf (Var x) = op_taint tn0 (Var x)` by
    (rpt strip_tac >>
     qpat_x_assum `ghost_kept cenv es sa _ _ _ _ _` mp_tac >>
     qpat_x_assum `ghost_kept _ _ s1 _ _ _ H' tm'` mp_tac >>
     simp[ghost_kept_def, op_taint_def] >> metis_tac[]) >>
  suspend "normal_outcome"
QED
Resume compile_augassign_attr_local_case_ptr[normal_outcome]:
  `~block_is_terminated sb` by
    (irule emit_void_nonterminator_open >>
     goal_assum (drule_at Any) >> simp[venomInstTheory.is_terminator_def]) >>
  simp[gas_outcome_ptr_def] >> qexists_tac `marks` >> disj1_tac >>
  simp[gas_summary_ptr_at_marked] >> goal_assum (drule_at Any) >>
  disj1_tac >> simp[stmt_lands_def, cenv_top_ext_refl, ghost_inv_gas_obs]
QED
Finalise compile_augassign_attr_local_case_ptr
