(* Runtime typing at the physical tuple layout of a widened call. *)
Theory tupleWidenedReadiness
Ancestors
  tupleWidenedLayout exprSimSource exprSimHyps valueEncodingTyping
  exprOpenMain exprOpenTerminals exprOpenPrimitives stmtLowering compileEnv context venomInst
  bodySimStmtCases tupleTargetStoreProps vyperTypeValues vyperTypeArgFits
  vyperTypeExprResult vyperTypeInvariants list exprSimProps typedMemoryCopy
  vyperTyping vyperTypeDefaults
Libs
  monadsyntax

Theorem tuple_widened_read_typed:
  !ce cx env e es obs tys stys stvs v ee.
    expr_body_pre ce cx env e es /\ expr_type e = TupleT tys /\
    lowered_value_type ce e <> expr_type e /\
    post_value_type ce e = TupleT stys /\
    evaluate_type (get_tenv cx) (TupleT stys) = SOME (TupleTV stvs) /\
    (do r <- eval_expr cx e; read_result cx r od)
      (es with gas_obs := obs) = (INL v,ee) ==>
    value_has_type (TupleTV stvs) v /\ val_wf (TupleTV stvs) v /\
    expr_sim_inv ce cx env ee
Proof
  rpt gen_tac >> strip_tac >>
  `expr_body_pre ce cx env e (es with gas_obs := obs)` by simp[] >>
  drule_all tuple_widened_source_ready >> strip_tac >> gvs[] >>
  drule_at (Pos last) ifexp_intcall_read_physical_typed >>
  simp[] >> disch_then drule >> strip_tac >> gvs[] >>
  drule_at (Pos last) expr_body_pre_eval >> simp[] >>
  disch_then drule >> strip_tac >>
  metis_tac[value_has_type_val_wf]
QED

Theorem compile_tuple_load_all_open:
  !tys ce op off sa elems sb.
    compile_tuple_load_all ce op tys off sa = (elems,sb) /\
    ~block_is_terminated sa ==> ~block_is_terminated sb
Proof
  Induct >- simp[compile_tuple_load_all_def, comp_return_def] >>
  rpt gen_tac >>
  simp[compile_tuple_load_all_def, comp_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >> gvs[] >>
  rename1 `compile_load_memory src_elem (is_word_type h) load_start = (elem_op,load_end)` >>
  `~block_is_terminated load_start` by
    (drule emit_op_nonterminator_open >> simp[is_terminator_def]) >>
  `~block_is_terminated load_end` by
    (qpat_x_assum `compile_load_memory _ _ _ = _` mp_tac >>
     simp[compile_load_memory_def] >> Cases_on `is_word_type h` >>
     simp[comp_return_def] >> strip_tac >> gvs[] >>
     drule emit_op_nonterminator_open >> simp[is_terminator_def]) >>
  first_x_assum irule >> metis_tac[]
QED

Theorem tuple_targets_destination_ready:
  !tops ctx ce cx env es gs dtys dtvs.
    body_inv tops ctx ce cx /\ expr_sim_inv ce cx env es /\
    storage_vars_rel ce cx /\ transient_vars_rel ce cx /\
    locals_alloc_ok ce env /\
    LIST_REL (\g ty. well_typed_atarget env g ty) gs dtys /\
    LIST_REL (\ty tv. evaluate_type (get_tenv cx) ty = SOME tv) dtys dtvs /\
    EVERY (\g. (?id ty. g = BaseTarget (NameTarget id) /\
                         FLOOKUP env.var_types id = SOME ty /\
                         0 < type_memory_bytes ce ty) \/
                (?nsid. g = BaseTarget (TopLevelNameTarget nsid) /\
                        supported_scalar_target tops nsid) \/
                (?nsid fld fty.
                   g = BaseTarget (AttributeTarget (TopLevelNameTarget nsid) fld) /\
                   supported_storage_field_write tops nsid fld /\
                   type_place_target env
                     (AttributeTarget (TopLevelNameTarget nsid) fld) =
                     SOME (Type fty) /\ is_word_type fty)) gs ==>
    !i. i < LENGTH gs ==>
      tuple_target_aligned ce cx (EL i gs) (EL i dtys) (EL i dtvs) /\
      (~is_word_type (EL i dtys) ==>
        type_memory_size (EL i dtvs) + 64 < dimword (:256)) /\
      (!ee v. expr_sim_inv ce cx env ee /\ value_has_type (EL i dtvs) v ==>
        tuple_target_layout ee.scopes (EL i gs) (EL i dtys) (EL i dtvs) v)
Proof
  rpt gen_tac >> strip_tac >> qx_gen_tac `i` >> disch_tac >>
  irule body_tuple_target_ready >>
  fs[EVERY_EL, LIST_REL_EL_EQN] >> metis_tac[]
QED

Theorem tuple_widened_runtime_ready:
  !ce cx env ee gs stys stvs dtys dtvs vs.
    expr_sim_inv ce cx env ee /\
    evaluate_type (get_tenv cx) (TupleT stys) = SOME (TupleTV stvs) /\
    evaluate_type (get_tenv cx) (TupleT dtys) = SOME (TupleTV dtvs) /\
    value_has_type (TupleTV stvs) (ArrayV (TupleV vs)) /\
    LENGTH gs = LENGTH stys /\ LENGTH dtys = LENGTH gs /\
    (!i. i < LENGTH gs ==>
      type_widens_to (get_tenv cx) (EL i stys) (EL i dtys)) /\
    (!i. i < LENGTH gs ==>
      tuple_target_aligned ce cx (EL i gs) (EL i dtys) (EL i dtvs) /\
      (~is_word_type (EL i dtys) ==>
        type_memory_size (EL i dtvs) + 64 < dimword (:256)) /\
      (!ee v. expr_sim_inv ce cx env ee /\ value_has_type (EL i dtvs) v ==>
        tuple_target_layout ee.scopes (EL i gs) (EL i dtys) (EL i dtvs) v)) ==>
    !i. i < LENGTH gs ==>
      tuple_target_aligned ce cx (EL i gs) (EL i dtys) (EL i dtvs) /\
      tuple_target_layout ee.scopes (EL i gs) (EL i dtys) (EL i dtvs) (EL i vs) /\
      (is_word_type (EL i stys) = is_word_type (EL i dtys)) /\
      type_widens_to (get_tenv cx) (EL i stys) (EL i dtys) /\
      evaluate_type (get_tenv cx) (EL i stys) = SOME (EL i stvs) /\
      value_has_type (EL i stvs) (EL i vs) /\ val_wf (EL i stvs) (EL i vs) /\
      value_has_type (EL i dtvs) (EL i vs) /\ val_wf (EL i dtvs) (EL i vs) /\
      (is_word_type (EL i dtys) ==> type_memory_size (EL i dtvs) = 32) /\
      (~is_word_type (EL i stys) ==> type_memory_size (EL i dtvs) + 64 < dimword (:256))
Proof
  rpt gen_tac >> strip_tac >>
  qpat_assum `evaluate_type _ (TupleT stys) = _`
    (mp_tac o MATCH_MP evaluate_type_TupleT_cases) >> strip_tac >> gvs[] >>
  qpat_assum `evaluate_type _ (TupleT dtys) = _`
    (mp_tac o MATCH_MP evaluate_type_TupleT_cases) >> strip_tac >> gvs[] >>
  gvs[value_has_type_def, values_have_types_LIST_REL, LIST_REL_EL_EQN] >>
  qx_gen_tac `i` >> disch_tac >>
  `type_widens_to (get_tenv cx) (EL i stys) (EL i dtys)` by simp[] >>
  `evaluate_type (get_tenv cx) (EL i stys) = SOME (EL i stvs) /\
   evaluate_type (get_tenv cx) (EL i dtys) = SOME (EL i dtvs) /\
   value_has_type (EL i stvs) (EL i vs)` by simp[] >>
  `value_has_type (EL i dtvs) (EL i vs)` by
    (drule_all type_widens_to_value_has_type >> strip_tac >> gvs[]) >>
  `is_word_type (EL i stys) = is_word_type (EL i dtys)` by
    metis_tac[type_widens_to_word, return_source_word_widens_eq] >>
  simp[] >> metis_tac[value_has_type_val_wf, word_tv_memory_size]
QED
