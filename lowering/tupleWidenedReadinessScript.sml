(* Runtime typing at the physical tuple layout of a widened call. *)
Theory tupleWidenedReadiness
Ancestors
  tupleWidenedLayout exprSimSource exprSimHyps valueEncodingTyping
  exprOpenMain exprOpenTerminals exprOpenPrimitives stmtLowering compileEnv context venomInst
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
