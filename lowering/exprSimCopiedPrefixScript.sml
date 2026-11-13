Theory exprSimCopiedPrefix
Ancestors
  exprSimCopiedCompile exprLoweringProps exprLowering exprCallBounds vyperAST
  compileEnv valueEncoding

Theorem compile_expr_array_subscript_copied_base_prefix:
  compile_expr ce ty (Subscript ann obj idx) sa = (vv,sb) /\
  place_type ce obj = ValPT (ArrayT et bd) /\
  copies_subscript_base ce obj idx ==>
  ?bvv sm. compile_expr ce ty obj sa = (bvv,sm) /\ cs_extends sm sb
Proof
  strip_tac >>
  qpat_x_assum `compile_expr _ _ (Subscript _ _ _) _ = _` mp_tac >>
  simp[Once (CONJUNCT1 compile_expr_raw_def), compile_expr_body_def,
       compile_subscript_def, expr_child_callback_def,
       comp_bind_def, comp_return_def, expr_size_def, expr_type_def] >>
  rpt (pairarg_tac >> gvs[]) >> strip_tac >>
  `!ce ty e st. ci_mono st
      (SND (expr_child_callback
        (expr_size idx + (expr_size obj + (type_size ann + 1)))
        compile_expr ce ty e st))` by
    (irule ci_mono_expr_child_callback >> simp[cj 1 compile_expr_ci_mono]) >>
  drule ci_mono_lower_value_cfn >> strip_tac >>
  rename1 `compile_snapshot_vv ce T base_vv0 sm = (base_vv,sn)` >>
  rename1 `lower_value _ ce ty idx sn = (idx_op,si)` >>
  `ci_mono sm sn` by
    (qspec_then `ce` mp_tac ci_mono_compile_snapshot_vv >>
     disch_then (qspecl_then [`T`, `base_vv0`, `sm`] mp_tac) >> simp[]) >>
  `ci_mono sn si` by
    (first_x_assum (qspecl_then [`ce`, `ty`, `idx`, `sn`] mp_tac) >> fs[SF ETA_ss]) >>
  `ci_mono si sb` by
    (qpat_x_assum `compile_array_subscript _ _ _ _ _ _ _ _ _ = _` mp_tac >>
     qmatch_goalsub_abbrev_tac `compile_array_subscript bop iop dyn cnt ws es signed loader si` >>
     `!op st. ci_mono st (SND (loader op st))` by
       simp[Abbr `loader`, ci_mono_compile_ptr_load] >>
     drule ci_mono_compile_array_subscript >>
     disch_then (qspecl_then [`bop`, `iop`, `dyn`, `cnt`, `ws`, `es`, `signed`, `si`] mp_tac) >>
     rpt strip_tac >> gvs[]) >>
  metis_tac[ci_mono_def, cs_extends_trans]
QED
