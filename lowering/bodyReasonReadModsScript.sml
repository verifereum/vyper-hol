(* Source read and capacity at a reached linked reason-expression endpoint. *)
Theory bodyReasonReadMods
Ancestors
  bodyFullPostsMods exprBodyPreProps exprSimHyps exprSimAttribute
  reasonSourceProps reasonResourcesPtr exprSimMemorySource gasContext stmtSimDefs
  allocLimits compileEnv exprSimHypsDefs valueEncoding
  vyperTypeSystem vyperValue vyperState vfmConstants words
Libs
  monadsyntax

Theorem vv_holds_mods_read_success[local]:
  vv_holds_mods cenv cx ty tv vv ee t ==>
  ?v. read_result cx tv ee = (INL v,ee)
Proof
  Cases_on `vv` >> simp[vv_holds_mods_def]
  >- (strip_tac >> drule reason_vv_read_success >> simp[]) >>
  rename1 `p.ptr_location = LocCode` >> Cases_on `p.ptr_location = LocCode`
  >- (simp[immutable_holds_mods_def] >>
      rpt strip_tac >> drule immutable_holds_read >> simp[]) >>
  simp[] >> strip_tac >> drule reason_vv_read_success >> simp[]
QED

Theorem raise_reason_raw_string_mods:
  gas_admissible (eval_stmt cx (Raise (RaiseReason r)))
    (stmt_res_ok lctx) es /\
  (!tail. eval_expr cx r
    (es with gas_obs := gas_explicit marks s0.vs_gas_readings ++ tail) =
    (INL tv, ee with gas_obs := tail)) /\
  vv_post_mods H ctx func cenv cx r es sa sm s0 (ee with gas_obs := []) tv vv t ==>
  ?str. read_result cx tv (ee with gas_obs := []) =
      (INL (StringV str), ee with gas_obs := []) /\
    !tail. (do v <- read_result cx tv;
        msg <- lift_option_type (dest_StringV v) "not StringV";
        raise (AssertException msg) od)
      (ee with gas_obs := tail) =
    (INR (AssertException str) : unit + exception, ee with gas_obs := tail)
Proof
  strip_tac >>
  `?v. read_result cx tv (ee with gas_obs := []) =
       (INL v, ee with gas_obs := [])` by
    (qpat_assum `vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [vv_post_mods_def]) >>
     drule vv_holds_mods_read_success >> simp[]) >>
  drule read_result_gas_obs >> simp[] >> strip_tac >>
  qpat_assum `!tail. eval_expr _ _ _ = _` (qspec_then `[]` assume_tac) >>
  fs[] >>
  qpat_x_assum `gas_admissible _ _ _` mp_tac >>
  simp[gas_admissible_def] >>
  disch_then (qspec_then `gas_explicit marks s0.vs_gas_readings` mp_tac) >>
  simp[eval_raise_reason_bind, bind_def] >>
  Cases_on `v` >>
  simp[dest_StringV_def, lift_option_type_def, raise_def, return_def,
       stmt_res_ok_def] >>
  strip_tac >> rename1 `StringV str` >> qexists_tac `str` >>
  simp[bind_def, dest_StringV_def, lift_option_type_def, raise_def, return_def]
QED

Theorem reason_encoder_size_mods:
  expr_body_pre_mods mods cenv cx env e es /\
  supported_string_reason tops e /\
  (!ml str. e <> Literal (BaseT (StringT ml)) (StringL str)) ==>
  ?cap. expr_type e = BaseT (StringT cap) /\
        post_value_type cenv e = expr_type e /\
        type_alloc_ok cenv (BaseT (StringT cap)) /\
        64 + type_memory_bytes cenv (BaseT (StringT cap)) < dimword(:256) /\
        (!rt. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt ==>
              type_memory_bytes cenv (post_value_type cenv e) = type_memory_size rt /\
              type_memory_size rt < 2 ** 64)
Proof
  strip_tac >>
  drule_then assume_tac expr_body_pre_mods_well_typed >>
  drule_all_then strip_assume_tac supported_reason_string_type >>
  rename1 `expr_type e = BaseT (StringT cap)` >>
  `alloc_limits_expr cenv e` by fs[expr_body_pre_mods_def] >>
  `type_alloc_ok cenv (BaseT (StringT cap))` by
    (drule alloc_limits_expr_type_alloc_ok >> simp[]) >>
  drule_then assume_tac reason_encoder_allocation_limit >>
  `post_value_type cenv e = expr_type e` by simp[is_bytestring_type_def] >>
  qexists_tac `cap` >> simp[] >>
  simp[evaluate_type_def, type_memory_bytes_def, type_memory_size_def, word_size_def] >>
  fs[type_alloc_ok_def, is_word_type_def, type_memory_bytes_def]
QED
