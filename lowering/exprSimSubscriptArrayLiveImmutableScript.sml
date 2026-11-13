(* Join current immutable representation to the counted array suffix. *)
Theory exprSimSubscriptArrayLiveImmutable
Ancestors
  exprSimSubscriptArrayLiveImmutableMetadata exprSimSubscriptArrayLiveImmutableEndpoint
  exprSimSubscriptArrayLiveImmutableSuffix exprSimSubscriptArraySuffix
  exprSimSubscriptArraySource exprSimWordArgs exprSimProps exprLoweringProps
  exprSimHypsDefs exprSimSource loweringPosts vyperPlaceTyping vyperValueOperation
  vyperTypeSystem compileEnv loweringStateRelDefs finite_map words

Theorem live_immutable_array_suffix_summary:
  expr_body_pre cenv cx env (Subscript ann obj idx) es /\
  expr_type obj = ArrayT et bd /\ post_value_type cenv obj = expr_type obj /\
  eval_expr cx obj es = (INL (PlaceR (ImmutablePlace src id path)),t) /\
  eval_expr cx idx t = (INL ir,ee) /\ read_result cx ir ee = (INL iv,ee) /\
  ee.gas_obs = [] /\
  (!itv v. FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of
     NONE => FEMPTY | SOME imms => get_source_immutables src imms) id = SOME (itv,v) ==>
     ?v'. evaluate_subscripts itv v path = INL v') /\
  vv_post ctx func cenv cx obj es sa sb s0 t (PlaceR (ImmutablePlace src id path))
    (LocatedValue (ArrayT et bd) p) u /\
  expr_post ctx func cenv cx idx t sb sc u ee iv iop s /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sb x) /\
  (!l. p.ptr_operand <> Label l) /\
  (!x. iop = Var x ==> not_fresh_at sc x) /\ (!l. iop <> Label l) /\
  expr_sim_inv cenv cx env t /\ stmt_state_rel ctx func cenv cx es s0 /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sb /\ local_ptrs_reserved cenv sc /\
  MAP FDOM es.scopes = MAP FDOM t.scopes /\
  sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id /\
  sb.cs_next_var <= sc.cs_next_var /\ sb.cs_next_id <= sc.cs_next_id /\
  compile_array_subscript p.ptr_operand iop
    (case bd of Fixed _ => F | Dynamic _ => T)
    (case bd of Fixed n => n | Dynamic _ => 0)
    (word_scale p.ptr_location) (elem_size_in_location cenv p.ptr_location et)
    (is_signed_type (expr_type idx))
    (compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca p.ptr_location) sc = (dst,sd) /\
  fn_has_code sc sd func /\ ~s.vs_halted /\
  s.vs_current_bb = sc.cs_current_bb /\ s.vs_inst_idx = LENGTH sc.cs_current_insts ==>
  gas_summary_at F (ctx,func) []
    (select_result cx (ArrayT et bd) (PlaceR (ImmutablePlace src id path)) (ValueSubscript iv)) (ee,s)
    (\res ee' q. ?child. res = INL child /\
      vv_post ctx func cenv cx (Subscript ann obj idx) es sa sd s0 ee' child
        (LocatedValue ann (mk_ptr dst p.ptr_location)) q /\
      q.vs_current_bb = sd.cs_current_bb /\ q.vs_inst_idx = LENGTH sd.cs_current_insts)
    (\res ee' outcome. expr_exit res outcome)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then assume_tac expr_body_pre_array_subscript_base >>
  drule_all_then assume_tac expr_body_pre_array_subscript_index_after_base >>
  drule_all_then strip_assume_tac expr_body_pre_runtime_typed >>
  `value_has_type tvt iv` by metis_tac[] >>
  drule_all framed_array_index_post_view >> strip_tac >>
  `expr_sim_inv cenv cx env ee` by
    (drule_all exprSimSourceTheory.expr_body_pre_eval_result >> simp[]) >>
  `stmt_state_rel ctx func cenv cx ee s` by fs[expr_post_def] >>
  `vv_place_ptr cenv cx t u (PlaceR (ImmutablePlace src id path))
     (LocatedValue (ArrayT et bd) p)` by fs[vv_post_def] >>
  drule_all expr_body_pre_place_metadata >> strip_tac >>
  `?etv. evaluate_type (get_tenv cx) et = SOME etv /\
     evaluate_type (get_tenv cx) (ArrayT et bd) = SOME (ArrayTV etv bd) /\
     runtime_place_typed cx t (ImmutablePlace src id path) (ArrayTV etv bd)` by
    (qpat_x_assum `evaluate_type _ (expr_type obj) = _` mp_tac >>
     simp[Once vyperValueTheory.evaluate_type_def, AllCaseEqs()] >>
     rpt strip_tac >> gvs[] >> simp[vyperValueTheory.evaluate_type_def]) >>
  `!w. eval_operand p.ptr_operand u = SOME w ==> eval_operand p.ptr_operand s = SOME w` by
    (rpt strip_tac >> irule exprBopSimPropsTheory.eval_operand_frame >> simp[] >>
     qexistsl_tac [`sb`,`u`] >> simp[] >>
     drule_all expr_post_frame >> simp[wb_frame_def] >> metis_tac[]) >>
  suspend "current_array"
QED

Resume live_immutable_array_suffix_summary[current_array]:
  drule_all live_immutable_captured_array_view >> strip_tac >>
  `?av. v = ArrayV av` by
    (Cases_on `v` >> gvs[vyperTypingTheory.value_has_type_def]) >>
  qpat_x_assum `v = ArrayV av` SUBST_ALL_TAC >>
  `val_wf (ArrayTV etv bd) (ArrayV av)` by
    metis_tac[valueTypingMemoryPropsTheory.value_has_type_memory_wf] >>
  `array_length (ArrayTV etv bd) av < dimword (:256) /\
   (!al. av = SArrayV al ==> ?n. bd = Fixed n)` by
    (qpat_assum `evaluate_type _ (ArrayT et bd) = _` mp_tac >>
     pure_rewrite_tac[Once vyperValueTheory.evaluate_type_def] >>
     simp[] >> strip_tac >>
     Cases_on `bd` >> Cases_on `av` >>
     gvs[vyperTypingTheory.value_has_type_def, vyperTypingTheory.well_formed_type_value_def,
         vyperValueTheory.type_slot_size_def, vyperValueOperationTheory.array_length_def] >>
     `n * 1 <= n * type_slot_size etv` by simp[arithmeticTheory.LE_MULT_LCANCEL] >>
     decide_tac) >>
  `ann = et` by
    (qpat_x_assum `expr_body_pre _ _ _ (Subscript _ _ _) _` mp_tac >>
     simp[exprSimHypsDefsTheory.expr_body_pre_def,
          Once vyperTypeSystemTheory.well_typed_expr_def] >>
     strip_tac >> gvs[vyperTypeSystemTheory.subscript_type_ok_def] >>
     drule placeTypingPropsTheory.type_place_expr_vtype_annotation >>
     strip_tac >> Cases_on `vt` >>
     gvs[vyperTypeSystemTheory.vtype_annotation_ok_def] >>
     gvs[vyperTypeSystemTheory.subscript_vtype_def, AllCaseEqs()]) >>
  `type_memory_bytes cenv et = type_memory_size etv` by
    (irule exprSimHypsTheory.expr_sim_inv_memory_size >>
     goal_assum (drule_at Any) >> qexistsl_tac [`env`,`es`] >>
     fs[exprSimHypsDefsTheory.expr_body_pre_def]) >>
  `is_word_type (expr_type idx)` by
    (qpat_x_assum `value_has_type tvt iv` mp_tac >>
     qpat_x_assum `evaluate_type _ (expr_type idx) = _` mp_tac >>
     qpat_assum `iv = IntV i` SUBST1_TAC >> rpt (pop_assum kall_tac) >>
     Cases_on `expr_type idx` >>
     simp[vyperValueTheory.evaluate_type_def, AllCaseEqs(),
          vyperTypingTheory.value_has_type_def, compileEnvTheory.is_word_type_def] >>
     rpt strip_tac >> gvs[vyperTypingTheory.value_has_type_def, compileEnvTheory.is_word_type_def]) >>
  `cs_extends sc sd /\ sc.cs_next_var <= sd.cs_next_var /\ sc.cs_next_id <= sd.cs_next_id` by
    (qpat_x_assum `compile_array_subscript _ _ _ _ _ _ _ _ sc = _`
       (mp_tac o Q.AP_TERM `SND`) >> simp[] >> disch_then (SUBST1_TAC o SYM) >>
     rewrite_tac[GSYM exprLoweringPropsTheory.ci_mono_def] >>
     irule exprLoweringPropsTheory.ci_mono_compile_array_subscript >>
     simp[exprLoweringPropsTheory.ci_mono_compile_ptr_load]) >>
  suspend "readonly_endpoint"
QED

Resume live_immutable_array_suffix_summary[readonly_endpoint]:
  `!q. (!x z. not_fresh_at sc x /\ lookup_var x s = SOME z ==> lookup_var x q = SOME z) /\
       (!aid a. FLOOKUP s.vs_allocas aid = SOME a ==> FLOOKUP q.vs_allocas aid = SOME a) /\
       q.vs_memory = s.vs_memory /\ stmt_state_rel ctx func cenv cx ee q ==>
       vv_post ctx func cenv cx (Subscript (ArrayT et bd) obj idx) es sa sd s0 ee
         (PlaceR (ImmutablePlace src id path)) (LocatedValue (ArrayT et bd) p) q` by
    (rpt strip_tac >>
     `!w. eval_operand p.ptr_operand u = SOME w ==> eval_operand p.ptr_operand q = SOME w` by
       (rpt strip_tac >> irule exprBopSimPropsTheory.eval_operand_frame >> simp[] >>
        qexistsl_tac [`sc`,`s`] >> simp[] >>
        rpt strip_tac >> qpat_x_assum `!x. p.ptr_operand = Var x ==> _` drule >>
        simp[not_fresh_at_def]) >>
     drule_all live_immutable_captured_array_view >> strip_tac >>
     irule live_immutable_base_endpoint >> simp[] >>
     conj_tac
     >- (simp[vv_holds_def] >> gvs[]) >>
     qpat_x_assum `src = cenv.ce_module` SUBST_ALL_TAC >>
     goal_assum (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
     simp[]) >>
  suspend "counted_suffix"
QED

Resume live_immutable_array_suffix_summary[counted_suffix]:
  qpat_x_assum `ann = et` SUBST_ALL_TAC >>
  qpat_x_assum `iv = IntV i` SUBST_ALL_TAC >>
  irule live_immutable_represented_suffix_summary >>
  simp[SF SFY_ss] >>
  reverse conj_tac >- gvs[] >>
  qexistsl_tac [`iop`,`iw`,`sc`] >> simp[] >>
  qpat_x_assum `src = cenv.ce_module` SUBST_ALL_TAC >>
  simp[] >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!x. p.ptr_operand = Var x ==> _` drule >>
      gvs[not_fresh_at_def]) >>
  conj_tac
  >- (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
  gvs[]
QED

Finalise live_immutable_array_suffix_summary
