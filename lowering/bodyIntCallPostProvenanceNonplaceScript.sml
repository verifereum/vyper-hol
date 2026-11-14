(* Structural join of raw effect-free expression ownership certificates. *)
Theory bodyIntCallPostProvenanceNonplace
Ancestors
  bodyIntCallPostProvenanceOrdinary bodyIntCallPostProvenanceTypedCases
  bodyIntCallPostProvenanceLiveSource bodyIntCallPostProvenanceLivePost
  bodyIntCallPostProvenanceStruct bodyIntCallPostProvenanceMakeArray
  bodyIntCallPostProvenanceEmpty bodyIntCallPostProvenanceDecode
  bodyIntCallPostProvenanceConditionalJoin bodyIntCallPostProvenanceSelectorCases
  bodyIntCallPostProvenanceCapturedOutcome bodyIntCallPostProvenanceCaptureAlignment
  bodyIntCallProducerRoots bodyIntCallTopLevelProducer
  bodyIntCallPostProvenanceAttributeSelector bodyIntCallPostProvenanceCallbacks
  exprSimSource exprSimHyps exprLoweringProps exprLowering bodySim
  bodyIntCallArgType bodyIntCallProducerInterface loweringPosts compileEnv
  exprSimDefs exprSimHypsDefs gasOutcome gasSummary vyperAST vyperState context
  list vyperTypeSystem vyperSubscriptOverlap placeTypingProps exprSimSubscriptArraySource

Theorem intcall_type_builtin_expected_type[local]:
  (tb = Empty \/ ?b. tb = AbiDecode b) ==>
  compile_expr ce expected (TypeBuiltin ann tb target args) sa =
  compile_expr ce ann (TypeBuiltin ann tb target args) sa
Proof
  strip_tac >> gvs[] >>
  simp[compile_expr_type_builtin_dispatch,
       compile_type_builtin_dispatch_component_eq,
       compile_type_builtin_dispatch_body_def]
QED

Theorem intcall_dynarray_free_post[local]:
  vv_post ctx func ce cx e es sa sb s0 ee raw vv t /\
  ~expr_has_effect e /\
  (!tv. evaluate_type (get_tenv cx) (expr_type e) = SOME tv ==> dynarray_free tv) ==>
  intcall_vv_provenance ce cx (expr_type e) sa sb ee raw vv t
Proof
  strip_tac >>
  `post_value_type ce e = expr_type e` by metis_tac[effect_free_post_value_type] >>
  gvs[vv_post_def, intcall_vv_provenance_def] >>
  Cases_on `vv` >> gvs[vv_at_def, expr_val_at_def, vv_holds_def, immutable_holds_def] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem intcall_ordinary_outcome[local]:
  expr_vv_case F ctx func ce cx e /\
  expr_body_pre ce cx env e es /\
  (!gs raw ee t. eval_expr cx e (es with gas_obs := gs) = (INL raw,ee) /\
    vv_post ctx func ce cx e es sa sb s0 ee raw vv t ==>
    intcall_vv_provenance ce cx (expr_type e) sa sb ee raw vv t) /\
  compile_expr ce ty e sa = (vv,sb) /\ fn_has_code sa sb func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa /\
  gas_admissible (eval_expr cx e) expr_vv_res_ok es /\
  stmt_state_rel ctx func ce cx es s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome F (cx_tops cx) (ctx,func) (eval_expr cx e) (es,s0)
    (\res ee t. ?raw. res = INL raw /\
      vv_post ctx func ce cx e es sa sb s0 ee raw vv t /\
      t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      intcall_vv_provenance ce cx (expr_type e) sa sb ee raw vv t)
    (\res ee r. expr_exit res r)
Proof
  strip_tac >>
  `expr_vv_sim ctx func ce cx ty e es` by metis_tac[expr_vv_case_def] >>
  drule (iffLR expr_vv_sim_def) >> disch_then drule_all >>
  rewrite_tac[gas_outcome_def] >> strip_tac
  >- (qexists_tac `marks` >> disj1_tac >>
  qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [gas_summary_at_def]) >>
  simp[gas_summary_at_def] >>
  qexistsl_tac [`res`,`es_end`,`r`] >> simp[] >>
  gvs[] >>
  `intcall_vv_provenance ce cx (expr_type e) sa sb (es_end with gas_obs := []) tv vv t` by
    (qpat_x_assum `!gs raw ee t. _` irule >> simp[] >>
     qexists_tac `gas_explicit marks s0.vs_gas_readings` >>
     gvs[gas_marked_exec_def] >> first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  gvs[]) >>
  qexists_tac `marks` >> disj2_tac >> metis_tac[]
QED

Theorem intcall_effect_free_general[local]:
  !e tops ctx ce cx env ty es sa sb vv s0 func.
  body_inv tops ctx ce cx /\ expr_body_pre ce cx env e es /\ ~expr_has_effect e /\
  compile_expr ce ty e sa = (vv,sb) /\ fn_has_code sa sb func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa /\
  gas_admissible (eval_expr cx e) expr_vv_res_ok es /\
  stmt_state_rel ctx func ce cx es s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome F (cx_tops cx) (ctx,func) (eval_expr cx e) (es,s0)
    (\res ee t. ?raw. res = INL raw /\
      vv_post ctx func ce cx e es sa sb s0 ee raw vv t /\
      t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      intcall_vv_provenance ce cx (expr_type e) sa sb ee raw vv t)
    (\res ee r. expr_exit res r)
Proof
  measureInduct_on `expr_size e` >> rpt gen_tac >> strip_tac >>
  `acyclic_struct_metadata ce.ce_struct_fields` by fs[body_inv_def] >>
  Cases_on `e` >> gvs[expr_type_def]
  >~ [`Name ann id`]
  >- (irule compile_name_value_provenance >> simp[expr_sim_pre_body, effect_free_int_calls] >>
      metis_tac[])
  >~ [`TopLevelName ann nsid`]
  >- (irule compile_toplevel_name_provenance >> simp[expr_sim_pre_body, effect_free_int_calls] >>
      metis_tac[])
  >~ [`Attribute ann obj fld`]
  >- (irule intcall_attribute_outcome >> simp[] >>
      conj_tac >- (rpt gen_tac >> strip_tac >>
        qpat_x_assum `!y. _` (qspec_then `obj` mp_tac) >>
        simp[] >> disch_then irule >> metis_tac[]) >> metis_tac[])
  >~ [`IfExp ann c a b`] >- suspend "conditional"
  >~ [`Subscript ann obj idx`] >- suspend "subscript"
  >~ [`StructLit ann nsid fields`] >- suspend "struct"
  >~ [`Builtin ann blt args`] >- suspend "builtin"
  >~ [`TypeBuiltin ann tb target args`] >- suspend "typebuiltin"
  >~ [`Literal ann lit`] >- suspend "literal"
  >~ [`FlagMember ann fid mid`] >- suspend "flag"
QED

Resume intcall_effect_free_general[conditional]:
  irule intcall_ifexp_outcome >> simp[] >>
  reverse conj_tac >- metis_tac[ordinary_effect_free_cases] >>
  qexists_tac `ty` >> simp[] >> rpt gen_tac >> strip_tac >> gvs[] >>
  qpat_x_assum `!y. _` irule >> simp[] >> metis_tac[]
QED

Resume intcall_effect_free_general[struct]:
  irule (SRULE [expr_type_def] intcall_struct_literal_outcome) >> simp[] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- metis_tac[] >>
  irule ordinary_effect_free_exprs >> gvs[EVERY_MAP, EVERY_MEM, combinTheory.o_DEF]
QED

Resume intcall_effect_free_general[literal]:
  irule (SRULE [expr_type_def] (Q.INST [`e` |-> `Literal ann lit`] intcall_ordinary_outcome)) >> simp[] >>
  conj_tac >- (rpt strip_tac >>
    irule (SRULE [expr_type_def] (Q.INST [`e` |-> `Literal ann lit`] intcall_dynarray_free_post)) >>
    simp[] >> reverse conj_tac >- metis_tac[] >>
    rpt strip_tac >> irule typed_literal_dynarray_free >>
    fs[expr_body_pre_def] >> metis_tac[]) >>
  conj_tac >- metis_tac[] >> conj_tac >- metis_tac[] >>
  irule (cj 2 ordinary_effect_free_cases) >> simp[]
QED

Resume intcall_effect_free_general[flag]:
  irule (SRULE [expr_type_def] (Q.INST [`e` |-> `FlagMember ann fid mid`] intcall_ordinary_outcome)) >> simp[] >>
  conj_tac >- (rpt strip_tac >>
    irule (SRULE [expr_type_def] (Q.INST [`e` |-> `FlagMember ann fid mid`] intcall_dynarray_free_post)) >>
    simp[] >> reverse conj_tac >- metis_tac[] >>
    rpt strip_tac >> irule typed_flag_member_dynarray_free >>
    fs[expr_body_pre_def] >> metis_tac[]) >>
  conj_tac >- metis_tac[] >> conj_tac >- metis_tac[] >>
  irule (cj 2 ordinary_effect_free_cases) >> simp[]
QED

Resume intcall_effect_free_general[builtin]:
  Cases_on `?et bd. blt = MakeArray et bd`
  >- (pop_assum strip_assume_tac >> gvs[] >> Cases_on `et`
      >- (irule (SRULE [expr_type_def] intcall_tuple_literal_outcome) >>
          simp[] >> metis_tac[ordinary_effect_free_exprs]) >>
      irule (SRULE [expr_type_def] intcall_array_literal_outcome) >>
      simp[] >> metis_tac[ordinary_effect_free_exprs]) >>
  irule (SRULE [expr_type_def] (Q.INST [`e` |-> `Builtin ann blt args`] intcall_ordinary_outcome)) >> simp[] >>
  conj_tac
  >- (rpt strip_tac >>
      irule (SRULE [expr_type_def] (Q.INST [`e` |-> `Builtin ann blt args`] intcall_dynarray_free_post)) >>
      simp[] >> reverse conj_tac >- metis_tac[] >>
      rpt strip_tac >> irule typed_builtin_dynarray_free >>
      fs[expr_body_pre_def, Once well_typed_expr_def] >> metis_tac[]) >>
  conj_tac >- metis_tac[] >> conj_tac >- metis_tac[] >>
  irule (cj 2 ordinary_effect_free_cases) >> simp[]
QED

Resume intcall_effect_free_general[typebuiltin]:
  Cases_on `tb = Empty`
  >- (gvs[] >> irule (SRULE [expr_type_def] intcall_empty_outcome) >>
      simp[] >> metis_tac[intcall_type_builtin_expected_type]) >>
  Cases_on `?unwrap. tb = AbiDecode unwrap`
  >- (pop_assum strip_assume_tac >> gvs[] >>
      irule (SRULE [expr_type_def] intcall_abi_decode_outcome) >> simp[] >>
      conj_tac >- metis_tac[intcall_type_builtin_expected_type] >>
      metis_tac[ordinary_effect_free_exprs]) >>
  irule (SRULE [expr_type_def] (Q.INST [`e` |-> `TypeBuiltin ann tb target args`] intcall_ordinary_outcome)) >> simp[] >>
  conj_tac
  >- (rpt strip_tac >>
      irule (SRULE [expr_type_def] (Q.INST [`e` |-> `TypeBuiltin ann tb target args`] intcall_dynarray_free_post)) >>
      simp[] >> reverse conj_tac >- metis_tac[] >>
      rpt strip_tac >> irule typed_type_builtin_dynarray_free >>
      fs[expr_body_pre_def] >> metis_tac[]) >>
  conj_tac >- metis_tac[] >> conj_tac >- metis_tac[] >>
  irule (cj 2 ordinary_effect_free_cases) >> simp[]
QED

Resume intcall_effect_free_general[subscript]:
  `copies_subscript_base ce obj idx <=> subscript_reads_base cx obj idx` by
    metis_tac[body_inv_copies_subscript_base_source] >>
  Cases_on `copies_subscript_base ce obj idx`
  >- suspend "capture" >>
  irule intcall_noncapturing_subscript_outcome >> simp[] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> qpat_x_assum `!y. _` irule >> simp[] >> metis_tac[]) >>
  metis_tac[ordinary_effect_free_cases]
QED

Resume intcall_effect_free_general[capture]:
  `?et bd. expr_type obj = ArrayT et bd` by
    (fs[copies_subscript_base_def] >>
     drule subscript_overlap_through_dynarray >>
     Cases_on `expr_type obj` >> simp[]) >>
  `place_type ce obj = ValPT (ArrayT et bd)` by
    (qpat_assum `expr_type obj = _` (fn th => once_rewrite_tac[GSYM th]) >>
     irule place_type_well_typed_on_defined >>
     drule_all expr_body_pre_array_subscript_base >>
     gvs[expr_body_pre_def, expr_sim_inv_def] >> metis_tac[]) >>
  irule (SRULE [expr_type_def] intcall_captured_subscript_outcome) >>
  simp[] >> metis_tac[ordinary_effect_free_cases]
QED

Finalise intcall_effect_free_general

Theorem intcall_effect_free_provenance_outcome:
  body_inv tops ctx ce cx /\ expr_body_pre ce cx env e es /\ ~expr_has_effect e /\
  compile_expr ce (expr_type e) e sa = (vv,sb) /\ fn_has_code sa sb func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa /\
  gas_admissible (eval_expr cx e) expr_vv_res_ok es /\
  stmt_state_rel ctx func ce cx es s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  gas_outcome F (cx_tops cx) (ctx,func) (eval_expr cx e) (es,s0)
    (\res ee t. ?raw. res = INL raw /\
      vv_post ctx func ce cx e es sa sb s0 ee raw vv t /\
      t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      intcall_vv_provenance ce cx (expr_type e) sa sb ee raw vv t)
    (\res ee r. expr_exit res r)
Proof
  metis_tac[intcall_effect_free_general]
QED
