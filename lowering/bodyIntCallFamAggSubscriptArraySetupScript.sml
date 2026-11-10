(* Compiler frontiers for the array base, forced index and suffix. *)
Theory bodyIntCallFamAggSubscriptArraySetup
Ancestors
  exprSimSubscriptArrayEndpoint exprLoweringProps fragExec compileEnv
  exprSimHypsDefs placeTypingProps

Theorem intcall_array_compile_cuts:
  compile_expr ce ty obj sa = (bvv,sm) /\
  lower_value compile_expr ce ity idx sm = (iop,sc) /\
  compile_array_subscript base_op iop dyn cnt ws esz sgn
    (compile_ptr_load ce.ce_is_ctor ce.ce_imm_alloca loc) sc = (dst,sb) /\
  fn_has_code sa sb func ==>
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  sm.cs_next_var <= sc.cs_next_var /\ sm.cs_next_id <= sc.cs_next_id /\
  cs_extends sa sm /\ cs_extends sm sc /\ cs_extends sc sb /\
  fn_has_code sa sm func /\ fn_has_code sm sc func /\ fn_has_code sc sb func
Proof
  strip_tac >>
  `cs_extends sa sm /\ sa.cs_next_var <= sm.cs_next_var /\
   sa.cs_next_id <= sm.cs_next_id` by
    (drule (cj 1 compile_expr_grows) >> simp[]) >>
  `cs_extends sm sc /\ sm.cs_next_var <= sc.cs_next_var /\
   sm.cs_next_id <= sc.cs_next_id` by
    (drule (cj 2 compile_expr_grows) >> simp[]) >>
  `cs_extends sc sb` by
    (drule array_subscript_grows >> simp[ci_mono_compile_ptr_load]) >>
  `cs_extends sm sb` by metis_tac[cs_extends_trans] >>
  metis_tac[fn_has_code_split]
QED

Theorem intcall_array_subscript_annotation:
  expr_body_pre ce cx env (Subscript ann obj idx) es /\
  expr_type obj = ArrayT et bd ==>
  ann = et /\ is_word_type (expr_type idx)
Proof
  strip_tac >>
  qpat_x_assum `expr_body_pre _ _ _ _ _` mp_tac >>
  simp[expr_body_pre_def, Once vyperTypeSystemTheory.well_typed_expr_def] >>
  strip_tac >>
  `ann = et /\ is_int_type (expr_type idx)` by
    (gvs[vyperTypeSystemTheory.subscript_type_ok_def] >>
     drule placeTypingPropsTheory.type_place_expr_vtype_annotation >> simp[] >>
     strip_tac >> Cases_on `vt` >>
     gvs[vyperTypeSystemTheory.vtype_annotation_ok_def,
         vyperTypeSystemTheory.subscript_vtype_def]) >>
  simp[] >> qpat_x_assum `is_int_type _` mp_tac >>
  rpt (pop_assum kall_tac) >>
  Cases_on `expr_type idx` >> simp[vyperTypeSystemTheory.is_int_type_def] >>
  rename1 `is_int_type (BaseT bt)` >> Cases_on `bt` >>
  simp[vyperTypeSystemTheory.is_int_type_def, is_word_type_def]
QED

Theorem intcall_array_pointer_regime:
  compile_expr ce ty obj sa = (LocatedValue tp p,sm) /\
  ((~ce.ce_is_ctor /\
    !ty st. vv_location (FST (compile_expr ce ty obj st)) = SOME LocCode) \/
   ((?n. bd = vyperAST$Fixed n) /\
    (!tv. evaluate_type (get_tenv cx) et = SOME tv ==> dynarray_free tv) /\
    !ty st. vv_location (FST (compile_expr ce ty obj st)) = SOME LocMemory)) ==>
  ((?ty. vv_location (FST (compile_expr ce ty obj sa)) = SOME LocCode) \/
   (?n. bd = vyperAST$Fixed n)) /\
  ((~ce.ce_is_ctor /\ p.ptr_location = LocCode) \/
   ((?n. bd = vyperAST$Fixed n) /\
    (!tv. evaluate_type (get_tenv cx) et = SOME tv ==> dynarray_free tv) /\
    p.ptr_location = LocMemory))
Proof
  strip_tac
  >- (first_x_assum (qspecl_then [`ty`,`sa`] assume_tac) >>
      gvs[contextTheory.vv_location_def] >>
      disj1_tac >> qexists_tac `ty` >> simp[contextTheory.vv_location_def]) >>
  first_x_assum (qspecl_then [`ty`,`sa`] assume_tac) >>
  gvs[contextTheory.vv_location_def] >> metis_tac[]
QED
