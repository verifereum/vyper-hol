(* Typed capacity transport keeps the operand execution endpoint fixed. *)
Theory bodyPtrMakeArrayLayoutTransport
Ancestors
  bodyPtrDefs exprSimProps compileEnv vyperTypeSystem vyperTyping
  valueEncoding valueEncodingDefs loweringPosts vyperValue exprLowering vyperAST vyperTypeCallGraph
  exprSimIfExp exprSimHypsDefs vyperTypeInvariants

Theorem bytestring_ptr_mem_ok_transport:
  !cx src dst tv v op G tn s.
    ((?m n. src = BaseT (StringT m) /\ dst = BaseT (StringT n)) \/
     (?m n. src = BaseT (BytesT (Dynamic m)) /\
            dst = BaseT (BytesT (Dynamic n)))) /\
    evaluate_type (get_tenv cx) src = SOME tv /\
    value_has_type tv v /\ ptr_mem_ok cx src v op G tn s ==>
    ptr_mem_ok cx dst v op G tn s
Proof
  rpt gen_tac >> rpt strip_tac >> gvs[] >>
  gvs[evaluate_type_def, AllCaseEqs()] >>
  Cases_on `v` >> gvs[value_has_type_def] >>
  gvs[ptr_mem_ok_def, evaluate_type_def, val_in_memory_def,
      val_footprint_def, val_store_size_def] >> metis_tac[]
QED

Theorem call_free_lowered_bytestring_family:
  !ce e env.
    well_typed_expr env e /\ int_calls_expr e = [] ==>
    lowered_value_type ce e = expr_type e \/
    (?m n. expr_type e = BaseT (StringT m) /\
           lowered_value_type ce e = BaseT (StringT n)) \/
    (?m n. expr_type e = BaseT (BytesT (Dynamic m)) /\
           lowered_value_type ce e = BaseT (BytesT (Dynamic n)))
Proof
  ho_match_mp_tac lowered_value_type_ind >>
  simp[lowered_value_type_def, expr_type_def, well_typed_expr_def,
       type_builtin_result_ok_def, vyperTypeCallGraphTheory.int_calls_expr_def] >>
  rpt strip_tac >> gvs[well_typed_builtin_app_def, concat_buffer_type_def]
QED

Theorem make_array_child_ptr_mem_lowered:
  expr_body_pre ce cx env e es /\
  (do r <- eval_expr cx e; read_result cx r od) es = (INL v, es') /\
  (int_calls_expr e = [] \/ lowered_value_type ce e = expr_type e) /\
  ptr_mem_ok cx (expr_type e) v op G tn s ==>
  ptr_mem_ok cx (lowered_value_type ce e) v op G tn s
Proof
  strip_tac >> Cases_on `lowered_value_type ce e = expr_type e` >> gvs[] >>
  `well_typed_expr env e` by gvs[expr_body_pre_def] >>
  drule_all ifexp_body_pre_read_typed >> strip_tac >>
  drule_all call_free_lowered_bytestring_family >> strip_tac >> gvs[] >>
  irule bytestring_ptr_mem_ok_transport >> simp[] >> metis_tac[]
QED
