(* Narrow source-semantic boundaries for the joint RaiseReason proof. *)
Theory bodyFullRaiseReasonSource
Ancestors
  reasonSourceProps exprSimDefs exprSimProps exprSimMemorySource stmtSimDefs
  loweringPosts gasSummary gasContext supportedStmts vyperTypeSystem
  vyperInterpreter vyperState vyperValue vyperAST
Libs
  monadsyntax

Theorem reason_vv_read_success[local]:
  vv_holds cenv cx ty tv vv ee t ==>
  ?v. read_result cx tv ee = (INL v, ee)
Proof
  Cases_on `vv` >> simp[vv_holds_def] >> rpt strip_tac
  >- metis_tac[] >>
  Cases_on `p.ptr_location` >>
  gvs[storage_holds_def, immutable_holds_def] >> metis_tac[]
QED

Theorem raise_reason_raw_string:
  gas_admissible (eval_stmt cx (Raise (RaiseReason r)))
    (stmt_res_ok lctx) es /\
  (!tail. eval_expr cx r
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
    (INL tv, ee with gas_obs := tail)) /\
  vv_post H ctx func cenv cx r es sa sm s0 (ee with gas_obs := []) tv vv t ==>
  ?str. read_result cx tv (ee with gas_obs := []) =
      (INL (StringV str), ee with gas_obs := []) /\
    !tail. (do v <- read_result cx tv;
        msg <- lift_option_type (dest_StringV v) "not StringV";
        raise (AssertException msg) od)
      (ee with gas_obs := tail) =
    (INR (AssertException str) : unit + exception, ee with gas_obs := tail)
Proof
  rpt strip_tac >>
  `?v. read_result cx tv (ee with gas_obs := []) =
       (INL v, ee with gas_obs := [])` by
    (irule reason_vv_read_success >> gvs[vv_post_def] >> metis_tac[]) >>
  drule read_result_gas_obs >> simp[] >> strip_tac >>
  qpat_assum `!tail. eval_expr _ _ _ = _`
    (qspec_then `[]` assume_tac) >> fs[] >>
  qpat_x_assum `gas_admissible _ _ _` mp_tac >>
  simp[gas_admissible_def] >>
  disch_then (qspec_then `gas_explicit marks s0.vs_gas_readings ++ []` mp_tac) >>
  simp[eval_raise_reason_bind, bind_def] >>
  Cases_on `v` >>
  simp[dest_StringV_def, lift_option_type_def, raise_def, return_def,
       stmt_res_ok_def] >>
  strip_tac >> rename1 `StringV str` >> qexists_tac `str` >>
  simp[bind_def, dest_StringV_def, lift_option_type_def, raise_def, return_def]
QED

Theorem supported_reason_string_type:
  !tops e.
    supported_string_reason tops e /\
    (!ml str. e <> Literal (BaseT (StringT ml)) (StringL str)) /\
    well_typed_expr env e ==>
    ?n. expr_type e = BaseT (StringT n)
Proof
  rpt strip_tac >>
  Cases_on `?t str. e = Literal t (StringL str)`
  >- (gvs[well_typed_expr_def, expr_type_def] >>
      Cases_on `t` >> gvs[well_typed_literal_def] >>
      rename1 `BaseT b` >> Cases_on `b` >> gvs[well_typed_literal_def]) >>
  `case expr_type e of BaseT (StringT _) => T | _ => F` by
    (Cases_on `e` >> fs[supported_string_reason_def] >>
     rename1 `Literal _ lit` >> Cases_on `lit` >>
     fs[supported_string_reason_def]) >>
  Cases_on `expr_type e` >> fs[] >>
  rename1 `BaseT b` >> Cases_on `b` >> fs[]
QED
