(* Nonself slice value dispatch and forced-result adaptation. *)
Theory bodyMemSliceNonselfResult
Ancestors
  bodyMemSliceOrdinary bodyMemSliceExtcodeTyped bodyExprForceMemory
  exprSimSliceSource exprSimSource exprSimHypsDefs exprSimMemDefs
  exprLowering exprLoweringProps exprBopLowering vyperInterpreter vyperTypeSystem vyperAST

Theorem slice_nonself_vv_mem:
  body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env (Builtin ann (Slice n) args) es /\
  ~is_self_code (HD args) /\
  (code_slice_source (Slice n) args = NONE ==> body_exprs_mem_ok cx args) /\
  (!ct a. code_slice_source (Slice n) args = SOME (ct,a) ==>
    body_exprs_mem_ok cx (TL args) /\
    ((?s vs t. eval_exprs cx (TL args) s = (INL vs,t)) ==> body_exprs_mem_ok cx [a])) ==>
  expr_vv_sim_mem ctx func cenv cx ty (Builtin ann (Slice n) args) es
Proof
  strip_tac >> Cases_on `code_slice_source (Slice n) args`
  >- (irule slice_ordinary_vv_mem >> simp[] >>
      reverse conj_tac >- metis_tac[] >>
      `well_typed_expr env (Builtin ann (Slice n) args)` by fs[expr_body_pre_def] >>
      drule slice_typed_args >> strip_tac >> gvs[] >>
      gvs[exprCallbackContractsTheory.is_extcode_characterization] >>
      rpt strip_tac >> gvs[]) >>
  PairCases_on `x` >> gvs[code_slice_source_SOME] >>
  rename1 `Builtin ct (Acc Code) [a]` >>
  `well_typed_expr env (Builtin ann (Slice n) [Builtin ct (Acc Code) [a];start;len])` by
    fs[expr_body_pre_def] >>
  drule slice_typed_args >> strip_tac >> gvs[] >>
  `well_typed_expr env (Builtin ct (Acc Code) [a])` by
    (qpat_x_assum `well_typed_expr env (Builtin _ (Slice _) _)` mp_tac >>
     simp[well_typed_expr_def]) >>
  `expr_body_pre cenv cx env start es /\ expr_body_pre cenv cx env len es` by
    (conj_tac >> irule expr_body_pre_builtin_typed_arg >>
     qpat_assum `expr_body_pre _ _ _ (Builtin _ (Slice _) _) _` (irule_at Any) >>
     simp[] >> fs[expr_body_pre_def]) >>
  `expr_body_pre cenv cx env a es` by
    (irule slice_code_address_body_pre >>
     qpat_assum `expr_body_pre _ _ _ (Builtin _ (Slice _) _) _` (irule_at Any) >>
     fs[expr_body_pre_def]) >>
  fs[Once well_typed_expr_def, well_typed_builtin_app_def,
     account_item_type_def, expr_type_def] >>
  irule slice_extcode_typed_entry_mem >> simp[] >>
  metis_tac[]
QED

Theorem slice_nonself_sim_mem:
  expr_body_pre cenv cx env (Builtin ann (Slice n) args) es /\
  ~is_self_code (HD args) /\
  expr_vv_sim_mem ctx func cenv cx ty (Builtin ann (Slice n) args) es ==>
  expr_sim_mem ctx func cenv cx ty (Builtin ann (Slice n) args) es
Proof
  strip_tac >> irule body_expr_sim_mem_of_vv_sim_mem >> simp[] >>
  reverse conj_tac >- metis_tac[] >>
  rpt gen_tac >> strip_tac >>
  `well_typed_expr env (Builtin ann (Slice n) args)` by fs[expr_body_pre_def] >>
  drule slice_typed_args >> strip_tac >> gvs[] >>
  `~names_builtin (Slice n) [src;start;len]` by
    simp[exprSimSliceOrdinaryTheory.names_builtin_slice] >>
  qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
  simp[compile_expr_builtin_dispatch, compile_builtin_dispatch_component_eq,
       lower_value_child_call] >>
  Cases_on `is_extcode src` >>
  Cases_on `is_bytestring_type (expr_type src)` >> fs[] >>
  rpt (pairarg_tac >> simp[]) >> gvs[] >>
  qmatch_goalsub_abbrev_tac `as_ptr_val _ _ result` >>
  Cases_on `result` >> simp[as_ptr_val_def] >> gvs[]
QED
