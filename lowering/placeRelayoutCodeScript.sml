(* Assignment slices in raw RHS / target / no-op unwrap / store order. *)
Theory placeRelayoutCode
Ancestors
  exprSimIfExpWidenedCounted stmtSimAssignMem stmtLoweringMono
  exprLoweringProps stmtLowering exprLowering context compileEnv fragExec

Theorem assign_place_relayout_code_parts:
  stmt_env cenv lctx ty (Assign (BaseTarget bt) e) sa = (c,sf) /\
  post_value_type cenv e <> expr_type e /\
  ~is_word_type (post_value_type cenv e) /\
  ~(has_length_word (expr_type e) /\ is_empty_value_expr e) /\
  fn_has_code sa sf func ==>
  c = cenv /\
  ?vv sv tr st.
    compile_expr cenv (expr_type e) e sa = (vv,sv) /\
    compile_get_target_ptr compile_expr cenv bt sv = (tr,st) /\
    (!sm. unwrap_value cenv vv sm = (vv_operand vv,sm)) /\
    ci_mono sa sv /\ ci_mono sv st /\ ci_mono st sf /\
    fn_has_code sa sv func /\ fn_has_code sv st func /\ fn_has_code st sf func /\
    (!dst loc dty. tr = (dst,SOME loc,SOME (ValPT dty)) ==>
      compile_assign_value cenv dst loc (vv_operand vv) (is_word_type dty)
        (vv_location vv) dty (lowered_value_type cenv e)
        (case dty of ArrayT et (Dynamic _) =>
          SOME ((type_memory_bytes cenv et + 31) DIV 32, type_memory_bytes cenv et)
         | _ => NONE) (type_memory_bytes cenv dty) st = ((),sf))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule stmt_env_assign >> strip_tac >>
  qpat_x_assum `c = cenv` SUBST_ALL_TAC >>
  Cases_on `compile_expr cenv (expr_type e) e sa` >>
  rename1 `compile_expr _ _ _ _ = (vv,sv)` >>
  Cases_on `compile_get_target_ptr compile_expr cenv bt sv` >>
  rename1 `compile_get_target_ptr _ _ _ _ = (tr,st)` >>
  `!sm. unwrap_value cenv vv sm = (vv_operand vv,sm)` by
    (drule_all compile_changed_physical_unwrap_shape >> strip_tac >>
     gvs[unwrap_value_def, vv_operand_def, comp_return_def]) >>
  `ci_mono sa sv /\ ci_mono sv st` by
    (metis_tac[cj 1 compile_expr_grows, ci_mono_def,
               ci_mono_compile_get_target_ptr, pairTheory.SND]) >>
  qpat_x_assum `compile_stmt _ _ _ _ _ = _` mp_tac >>
  asm_simp_tac (srw_ss())
    [Once compile_stmt_def, comp_bind_def, comp_ignore_bind_def, comp_return_def, LET_THM] >>
  strip_tac >>
  `ci_mono st sf` by
    (Cases_on `FST (SND tr)` >>
     fs[] >> metis_tac[cj 1 ci_mono_stmt_helpers, ci_mono_emit_void, pairTheory.SND]) >>
  `cs_extends sa sv /\ cs_extends sv st /\ cs_extends st sf` by fs[ci_mono_def] >>
  `fn_has_code sa sv func /\ fn_has_code sv st func /\ fn_has_code st sf func` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  simp[] >> rpt strip_tac >> gvs[]
QED
