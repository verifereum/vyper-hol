(* Compiler inversion for root constructor immutable assignment. *)
Theory immutableAssignCode
Ancestors
  stmtSimAssignMem stmtSimProps exprLoweringProps stmtLowering exprLowering loweringPosts
  compileEnv finite_map stmtLoweringMono fragExec

Theorem immutable_assign_empty_code:
  stmt_env ce lctx ty (Assign (BaseTarget (TopLevelNameTarget nsid)) e) sa = (ce',sb) /\
  compile_get_target_ptr compile_expr ce (TopLevelNameTarget nsid) =
    comp_return (Lit (n2w off), SOME LocCode, SOME (ValPT ity)) /\
  has_length_word (expr_type e) /\ is_empty_value_expr e ==>
  ce' = ce /\
  compile_store_at_loc ce.ce_imm_alloca (Lit (n2w off)) (Lit 0w) (SOME LocCode) sa = ((),sb)
Proof
  strip_tac >> drule stmt_env_assign >> strip_tac >> gvs[] >>
  qpat_x_assum `compile_stmt _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_stmt_def, comp_bind_def, comp_return_def]
QED

Theorem immutable_assign_code_parts:
  stmt_env ce lctx ty (Assign (BaseTarget (TopLevelNameTarget nsid)) e) sa = (ce',sb) /\
  compile_get_target_ptr compile_expr ce (TopLevelNameTarget nsid) =
    comp_return (Lit (n2w off), SOME LocCode, SOME (ValPT ity)) /\
  ~(has_length_word (expr_type e) /\ is_empty_value_expr e) /\
  fn_has_code sa sb func ==>
  ce' = ce /\
  ?vv sm op su.
    compile_expr ce (expr_type e) e sa = (vv,sm) /\
    unwrap_value ce vv sm = (op,su) /\
    lower_value compile_expr ce (expr_type e) e sa = (op,su) /\
    compile_assign_value ce (Lit (n2w off)) LocCode op (is_word_type ity)
      (vv_location vv) ity (lowered_value_type ce e)
      (case ity of ArrayT et (Dynamic _) =>
         SOME ((type_memory_bytes ce et + 31) DIV 32, type_memory_bytes ce et)
       | _ => NONE) (type_memory_bytes ce ity) su = ((),sb) /\
    cs_extends sa sm /\ cs_extends sm su /\ cs_extends su sb /\
    fn_has_code sa sm func /\ fn_has_code sm su func /\ fn_has_code su sb func
Proof
  strip_tac >> drule stmt_env_assign >> strip_tac >> gvs[] >>
  qpat_x_assum `compile_stmt _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_stmt_def, comp_bind_def, comp_return_def] >>
  Cases_on `compile_expr ce (expr_type e) e sa` >>
  rename1 `compile_expr _ _ _ _ = (vv,sm)` >>
  Cases_on `unwrap_value ce vv sm` >>
  rename1 `unwrap_value _ _ _ = (op,su)` >>
  simp[] >> strip_tac >>
  `lower_value compile_expr ce (expr_type e) e sa = (op,su)` by
    simp[lower_value_def, comp_bind_def] >>
  `cs_extends sa sm` by metis_tac[cj 1 compile_expr_grows] >>
  `cs_extends sm su` by metis_tac[ci_mono_unwrap_value, pairTheory.SND, ci_mono_def] >>
  `cs_extends su sb` by metis_tac[cj 1 ci_mono_stmt_helpers, pairTheory.SND, ci_mono_def] >>
  `fn_has_code sa sm func /\ fn_has_code sm su func /\ fn_has_code su sb func` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  simp[]
QED
