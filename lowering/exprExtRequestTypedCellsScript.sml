(* Convert delayed-read runtime typing into the fixed-root tuple interface. *)
Theory exprExtRequestTypedCells
Ancestors
  exprExtRequestDelayedTyping exprExtRequestTupleFold exprExtRequestTyping
  exprExtRequestDefaultProbe exprSimHyps exprSimHypsDefs
  memoryLocalRhsProps valueEncodingTyping abiValueEncoding allocLimits
  vyperTypeSystem vyperValue compileEnv words list vyperState
  exprExtRequestStrongCapture exprExtRequestKwargs exprExtRequestUnreadCps
  exprExtRequestHistory exprExtRequestReadProbe exprExtRequestStagesSource
  vyperMisc vyperTyping valueEncodingProps pair exprExtRequestShape
  vyperTypeInvariants supportedExprTraverse exprSimSource rich_list

Theorem extrequest_typed_cell:
  expr_body_pre cenv cx env e es /\ ~expr_has_effect e /\
  extrequest_strong_capture ctx func cenv cx e r vv ee sb t /\
  read_result cx r ee = (INL v,ee) /\
  value_runtime_typed env (expr_type e) v /\
  value_runtime_typed env (lowered_value_type cenv e) v ==>
  ?tv. extrequest_tuple_cell ctx func cenv cx ee sb t ee
    (e,r,vv,lowered_value_type cenv e,tv,v)
Proof
  strip_tac >>
  `expr_sim_inv cenv cx env es /\ well_typed_expr env e /\
   alloc_limits_expr cenv e` by fs[expr_body_pre_def] >>
  drule_all memory_rhs_runtime_layout >> strip_tac >>
  rename1 `evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME tv` >>
  `IS_SOME (evaluate_type (get_tenv cx) (expr_type e))` by
    metis_tac[memory_rhs_runtime_layout, optionTheory.IS_SOME_DEF] >>
  `!stv. evaluate_type (get_tenv cx) (expr_type e) = SOME stv /\
     ~is_word_type (expr_type e) ==>
     type_memory_bytes cenv (expr_type e) = type_memory_size stv /\
     type_memory_size stv < 2**64` by
    (rpt strip_tac >>
     drule_all expr_sim_inv_memory_size >> strip_tac >>
     drule alloc_limits_expr_type_alloc_ok >>
     simp[type_alloc_ok_def]) >>
  `type_memory_size tv < dimword (:256)` by
    (Cases_on `is_word_type (lowered_value_type cenv e)`
     >- (drule_all abi_word_type_size >> simp[dimword_def]) >>
     drule_all extrequest_default_copy_capacity >> simp[]) >>
  qexists_tac `tv` >> simp[extrequest_tuple_cell_def] >>
  metis_tac[extrequest_lowered_type_compatible, value_has_type_val_wf]
QED

Theorem extrequest_typed_cells:
  !xs rs vvs vs.
  EVERY (\e. expr_body_pre cenv cx env e es /\ ~expr_has_effect e) xs /\
  extrequest_strong_captures ctx func cenv cx xs rs vvs ee sb t /\
  read_results cx rs ee = (INL vs,ee) /\
  LIST_REL (\e v. value_runtime_typed env (expr_type e) v /\
    value_runtime_typed env (lowered_value_type cenv e) v) xs vs ==>
  ?cells.
    EVERY (extrequest_tuple_cell ctx func cenv cx ee sb t ee) cells /\
    MAP (\(e,r,vv,ty,tv,v). (vv,ty)) cells =
      ZIP (vvs, MAP (lowered_value_type cenv) xs) /\
    MAP (\(e,r,vv,ty,tv,v). v) cells = vs /\
    MAP (\(e,r,vv,ty,tv,v). ty) cells = MAP (lowered_value_type cenv) xs /\
    MAP (\(e,r,vv,ty,tv,v). expr_type e) cells = MAP expr_type xs
Proof
  Induct
  >- (simp[extrequest_strong_captures_def] >> rpt strip_tac >>
      gvs[] >> simp[ZIP_def]) >>
  rpt gen_tac >> Cases_on `rs` >> Cases_on `vvs` >> Cases_on `vs` >>
  simp[extrequest_strong_captures_def] >> strip_tac >>
  gvs[read_results_def, vyperStateTheory.bind_def,
      vyperStateTheory.return_def, AllCaseEqs()] >>
  drule read_result_state >> disch_then SUBST_ALL_TAC >>
  `?tv. extrequest_tuple_cell ctx func cenv cx ee sb t ee
      (h,h',h'',lowered_value_type cenv h,tv,h''')` by
    (irule extrequest_typed_cell >> metis_tac[]) >>
  first_x_assum (qspecl_then [`t'`, `t''`, `t'''`] mp_tac) >>
  impl_tac >- simp[extrequest_strong_captures_def] >> strip_tac >>
  qexists_tac `(h,h',h'',lowered_value_type cenv h,tv,h''')::cells` >> simp[]
QED

Theorem extrequest_kwargs_typed_cells:
  EVERY (\e. !mid. expr_sim_inv cenv cx env mid ==>
    expr_body_pre cenv cx env e mid) xs /\
  EVERY (\e. ~expr_has_effect e) xs /\
  expr_sim_inv cenv cx env start /\
  extrequest_results_success cx xs start rs pos_end /\
  extrequest_kwargs_post ctx func cenv cx rt opts kwargs pos_end s2 t2 s3
    value_op gas_op default_op xs rs arg_vvs kwvs ee t /\
  read_results cx rs ee = (INL vs,ee) ==>
  ?cells.
    EVERY (extrequest_tuple_cell ctx func cenv cx ee s3 t ee) cells /\
    MAP (\(e,r,vv,ty,tv,v). (vv,ty)) cells =
      ZIP (arg_vvs, MAP (lowered_value_type cenv) xs) /\
    MAP (\(e,r,vv,ty,tv,v). v) cells = vs /\
    MAP (\(e,r,vv,ty,tv,v). ty) cells = MAP (lowered_value_type cenv) xs /\
    MAP (\(e,r,vv,ty,tv,v). expr_type e) cells = MAP expr_type xs
Proof
  strip_tac >>
  `extrequest_strong_captures ctx func cenv cx xs rs arg_vvs ee s3 t /\
   extrequest_read_frame cx (pos_end with gas_obs := []) ee` by
    fs[extrequest_kwargs_post_def, extrequest_history_frame_def] >>
  qpat_x_assum `extrequest_results_success _ _ _ _ _` mp_tac >>
  simp[extrequest_results_success_def] >> strip_tac >>
  `extrequest_read_frame cx mid ee` by
    fs[extrequest_read_frame_def] >>
  `LIST_REL (\e v. value_runtime_typed env (expr_type e) v /\
      value_runtime_typed env (lowered_value_type cenv e) v) xs vs` by
    (irule extrequest_delayed_results_typed >>
     first_assum (irule_at (Pat `eval_expr_results _ _ _ = _`)) >>
     simp[] >> metis_tac[]) >>
  irule extrequest_typed_cells >>
  reverse conj_tac >- metis_tac[] >>
  qexistsl_tac [`env`, `start`] >> simp[] >>
  fs[EVERY_MEM] >> metis_tac[]
QED

Theorem extrequest_cells_layout:
  !cells. EVERY (extrequest_tuple_cell ctx func cenv cx eb cb tb ee) cells ==>
    OPT_MMAP (evaluate_type (get_tenv cx))
      (MAP (\(e,r,vv,ty,tv,v). ty) cells) =
      SOME (MAP (\(e,r,vv,ty,tv,v). tv) cells) /\
    values_have_types (MAP (\(e,r,vv,ty,tv,v). tv) cells)
      (MAP (\(e,r,vv,ty,tv,v). v) cells) /\
    SUM (MAP (type_memory_bytes cenv)
      (MAP (\(e,r,vv,ty,tv,v). ty) cells)) =
      type_memory_size_list (MAP (\(e,r,vv,ty,tv,v). tv) cells)
Proof
  Induct >> simp[OPT_MMAP_def, value_has_type_def,
    valueEncodingTheory.type_memory_size_def] >>
  qx_gen_tac `cell` >> PairCases_on `cell` >>
  simp[extrequest_tuple_cell_def] >> rpt strip_tac >>
  simp[OPT_MMAP_def, value_has_type_def,
    valueEncodingTheory.type_memory_size_def]
QED

Theorem extrequest_cells_tuple:
  EVERY (extrequest_tuple_cell ctx func cenv cx eb cb tb ee) cells /\
  SUM (MAP (type_memory_bytes cenv)
    (MAP (\(e,r,vv,ty,tv,v). ty) cells)) < 2**64 ==>
  evaluate_type (get_tenv cx)
    (TupleT (MAP (\(e,r,vv,ty,tv,v). ty) cells)) =
    SOME (TupleTV (MAP (\(e,r,vv,ty,tv,v). tv) cells)) /\
  value_has_type (TupleTV (MAP (\(e,r,vv,ty,tv,v). tv) cells))
    (ArrayV (TupleV (MAP (\(e,r,vv,ty,tv,v). v) cells))) /\
  type_memory_bytes cenv (TupleT (MAP (\(e,r,vv,ty,tv,v). ty) cells)) =
    type_memory_size (TupleTV (MAP (\(e,r,vv,ty,tv,v). tv) cells))
Proof
  strip_tac >> drule extrequest_cells_layout >> strip_tac >>
  `type_slot_size_list (MAP (\(e,r,vv,ty,tv,v). tv) cells) <= dimword (:256)` by
    (fs[type_memory_size_slots, dimword_def] >> decide_tac) >>
  simp[Once evaluate_type_def, evaluate_types_OPT_MMAP, type_slot_size_def,
    value_has_type_def, type_memory_bytes_def,
    valueEncodingTheory.type_memory_size_def] >> metis_tac[]
QED

Theorem extrequest_fits_assignable:
  (!t u. arg_type_fits t u ==> !tenv.
    assignable_type tenv u /\ well_formed_type tenv t ==>
    assignable_type tenv t) /\
  (!ts us. arg_types_fit ts us ==> !tenv.
    EVERY (assignable_type tenv) us /\ EVERY (well_formed_type tenv) ts ==>
    EVERY (assignable_type tenv) ts)
Proof
  ho_match_mp_tac arg_type_fits_ind >> rw[arg_type_fits_def] >>
  gvs[assignable_type_def] >>
  fs[well_formed_type_def, optionTheory.IS_SOME_EXISTS,
     Once evaluate_type_def, AllCaseEqs()] >>
  imp_res_tac vyperTypeABITheory.evaluate_types_LIST_REL >>
  fs[LIST_REL_EL_EQN, EVERY_EL, well_formed_type_def] >>
  metis_tac[vyperTypeArgFitsTheory.arg_types_fit_LENGTH, LENGTH_NIL,
    optionTheory.IS_SOME_DEF]
QED

Theorem extrequest_cells_assignable:
  EVERY (extrequest_tuple_cell ctx func cenv cx eb cb tb ee) cells /\
  arg_types_fit (MAP (\(e,r,vv,ty,tv,v). expr_type e) cells) ats /\
  EVERY (assignable_type (get_tenv cx)) ats ==>
  EVERY (assignable_type (get_tenv cx))
    (MAP (\(e,r,vv,ty,tv,v). ty) cells)
Proof
  strip_tac >>
  `EVERY (well_formed_type (get_tenv cx))
     (MAP (\(e,r,vv,ty,tv,v). expr_type e) cells)` by
    (simp[EVERY_MAP, EVERY_MEM, FORALL_PROD, well_formed_type_def] >>
     fs[EVERY_MEM, FORALL_PROD, extrequest_tuple_cell_def] >> metis_tac[]) >>
  drule_all (cj 2 extrequest_fits_assignable) >>
  simp[EVERY_MEM, MEM_MAP, FORALL_PROD] >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  PairCases_on `y` >> gvs[] >>
  `extrequest_tuple_cell ctx func cenv cx eb cb tb ee
     (y0,y1,y2,e,y4,y5)` by fs[EVERY_MEM] >>
  fs[extrequest_tuple_cell_def] >>
  Cases_on `e = expr_type y0`
  >- (first_x_assum irule >>
      qexists_tac `(y0,y1,y2,e,y4,y5)` >> simp[]) >>
  Cases_on `e` >>
  gvs[is_bytestring_type_def, assignable_type_def, well_formed_type_def]
QED

Theorem extrequest_call_cells_bound:
  expr_body_pre cenv cx env
    (Call ann (ExtCall stat skip (fname,ats,rt) opts) (a::rest) dflt) es ==>
  SUM (MAP (type_memory_bytes cenv)
    (MAP (lowered_value_type cenv) (TAKE (LENGTH ats) rest))) < 2**64
Proof
  simp[expr_body_pre_def, Once alloc_limits_expr_def,
    ext_call_alloc_ok_def]
QED

Theorem extrequest_call_typed_cells:
  expr_body_pre cenv cx env
    (Call ann (ExtCall stat skip (fname,ats,rt) opts) (a::rest) dflt) es /\
  (?used. !tail. vyperState$bind (eval_expr cx a) (read_result cx)
    (es with gas_obs := used ++ tail) =
      (INL target,start with gas_obs := tail)) /\
  extrequest_results_success cx (TAKE (LENGTH ats) rest) start rs pos_end /\
  extrequest_kwargs_post ctx func cenv cx rt opts (DROP (LENGTH ats) rest)
    pos_end s2 t2 s3 value_op gas_op default_op
    (TAKE (LENGTH ats) rest) rs arg_vvs kwvs ee t /\
  read_results cx rs ee = (INL vs,ee) ==>
  ?cells tvs.
    EVERY (extrequest_tuple_cell ctx func cenv cx ee s3 t ee) cells /\
    MAP (\(e,r,vv,ty,tv,v). (vv,ty)) cells =
      ZIP (arg_vvs, MAP (lowered_value_type cenv) (TAKE (LENGTH ats) rest)) /\
    MAP (\(e,r,vv,ty,tv,v). v) cells = vs /\
    MAP (\(e,r,vv,ty,tv,v). tv) cells = tvs /\
    MAP (\(e,r,vv,ty,tv,v). ty) cells =
      MAP (lowered_value_type cenv) (TAKE (LENGTH ats) rest) /\
    evaluate_type (get_tenv cx)
      (TupleT (MAP (lowered_value_type cenv) (TAKE (LENGTH ats) rest))) =
        SOME (TupleTV tvs) /\
    value_has_type (TupleTV tvs) (ArrayV (TupleV vs)) /\
    type_memory_bytes cenv
      (TupleT (MAP (lowered_value_type cenv) (TAKE (LENGTH ats) rest))) =
        type_memory_size (TupleTV tvs) /\
    (TAKE (LENGTH ats) rest <> [] ==>
      assignable_type (get_tenv cx)
        (TupleT (MAP (lowered_value_type cenv) (TAKE (LENGTH ats) rest))))
Proof
  strip_tac >>
  `expr_body_pre cenv cx env a es` by
    (irule extrequest_body_pre_arg >>
     first_assum (irule_at (Pat `expr_body_pre _ _ _ (Call _ _ _ _) _`)) >>
     gvs[expr_body_pre_def]) >>
  `expr_sim_inv cenv cx env start` by
    (qpat_x_assum `!tail. vyperState$bind (eval_expr cx a) _ _ = _`
       (qspec_then `[]` mp_tac) >>
     `expr_body_pre cenv cx env a (es with gas_obs := used)` by simp[] >>
     simp[vyperStateTheory.bind_def] >> strip_tac >>
     drule_all (SRULE [vyperStateTheory.bind_def]
       exprSimSourceTheory.expr_body_pre_eval) >> simp[]) >>
  `EVERY (\e. !mid. expr_sim_inv cenv cx env mid ==>
     expr_body_pre cenv cx env e mid) (TAKE (LENGTH ats) rest)` by
    (drule extrequest_operand_body_pre >>
     simp[] >> metis_tac[EVERY_TAKE]) >>
  `EVERY (\e. ~expr_has_effect e) (TAKE (LENGTH ats) rest)` by
    (drule extrequest_body_typed >> simp[] >> metis_tac[EVERY_TAKE]) >>
  drule_all extrequest_kwargs_typed_cells >> strip_tac >>
  `SUM (MAP (type_memory_bytes cenv)
     (MAP (\(e,r,vv,ty,tv,v). ty) cells)) < 2**64` by
    metis_tac[extrequest_call_cells_bound] >>
  drule_all extrequest_cells_tuple >> strip_tac >>
  `env.type_defs = get_tenv cx` by
    fs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  `arg_types_fit (MAP (\(e,r,vv,ty,tv,v). expr_type e) cells) ats /\
   EVERY (assignable_type (get_tenv cx)) ats` by
    (drule extrequest_body_typed >>
     simp[Once well_typed_expr_def]) >>
  drule_all extrequest_cells_assignable >> strip_tac >>
  qexistsl_tac [`cells`, `MAP (\(e,r,vv,ty,tv,v). tv) cells`] >>
  gvs[] >>
  simp[assignable_type_def, well_formed_type_def] >> metis_tac[]
QED
