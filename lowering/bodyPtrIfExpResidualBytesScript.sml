Theory bodyPtrIfExpResidualBytes
Ancestors
  bodyPtrIfExpZeroLayout bodyPtrIfExpResidual bodyPtrIfExpBytesInputs
  bodySim exprSimHypsDefs vyperTypeSystem exprLowering compileEnv context vyperAST
  bodyPtrIfExpAllocCaller

Theorem ifexp_allocating_arm_noncall:
  body_inv tops ctx ce cx /\
  expr_body_pre ce cx env (IfExp ty cond a b) es /\
  (arm = a \/ arm = b) /\ expr_body_pre ce cx env_arm arm es_arm /\
  (int_calls_expr arm = [] \/
   same_memory_layout ce (lowered_value_type ce arm) (expr_type arm)) /\
  post_value_type ce arm = expr_type arm /\
  compile_expr ce ret_ty arm sa = (vv,sb) /\
  vv_post ctx fn ce cx arm es_arm sa sb s0 ee raw vv t /\
  ~same_memory_layout ce (lowered_value_type ce arm) ty ==>
  ~(?ann fid args dret. arm = Call ann (IntCall fid) args dret)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `expr_type arm = ty` by gvs[expr_body_pre_def, well_typed_expr_def] >>
  `int_calls_expr arm = []` by metis_tac[] >>
  strip_tac >> gvs[vyperTypeCallGraphTheory.int_calls_expr_def]
QED

Theorem ifexp_allocating_arm_bytes_inputs:
  body_inv tops ctx ce cx /\
  expr_body_pre ce cx env (IfExp ty cond a b) es /\
  (arm = a \/ arm = b) /\ expr_body_pre ce cx env_arm arm es_arm /\
  (int_calls_expr arm = [] \/
   same_memory_layout ce (lowered_value_type ce arm) (expr_type arm)) /\
  post_value_type ce arm = expr_type arm /\
  compile_expr ce ret_ty arm sa = (vv,sb) /\
  vv_post ctx fn ce cx arm es_arm sa sb s0 ee raw vv t /\
  ~same_memory_layout ce (lowered_value_type ce arm) ty /\
  eval_expr cx arm es_arm = (INL raw,ee) /\ read_result cx raw ee = (INL v,er) ==>
  is_bytestring_type ty /\
  ?tv len. evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv v /\
    ((?bs. v = BytesV bs /\ len = LENGTH bs) \/
     (?str. v = StringV str /\ len = LENGTH str)) /\
    val_store_size tv v = 32 + 32 * ((len+31) DIV 32) /\
    32 + 32 * ((len+31) DIV 32) <= type_memory_bytes ce ty /\
    len+31 < dimword(:256) /\ 32 + 32 * ((len+31) DIV 32) < dimword(:256)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `~(?ann fid args dret. arm = Call ann (IntCall fid) args dret)` by
    (drule_all ifexp_allocating_arm_noncall >> simp[]) >>
  drule_all ifexp_selected_bytes_inputs >> simp[]
QED

Theorem ifexp_allocating_arm_bytes_code:
  body_inv tops ctx ce cx /\
  expr_body_pre ce cx env (IfExp ty cond a b) es /\
  (arm = a \/ arm = b) /\ expr_body_pre ce cx env_arm arm es_arm /\
  (int_calls_expr arm = [] \/
   same_memory_layout ce (lowered_value_type ce arm) (expr_type arm)) /\
  post_value_type ce arm = expr_type arm /\
  compile_expr ce (expr_type arm) arm sa = (vv,sb) /\
  vv_post ctx fn ce cx arm es_arm sa sb s0 ee raw vv t /\
  local_ptrs_reserved ce sa /\ eval_expr cx arm es_arm = (INL raw,ee) /\
  ~is_word_type ty /\ ~same_memory_layout ce (lowered_value_type ce arm) ty /\
  compile_ifexp_arm ce ty (lowered_value_type ce arm) vv sb = (op,sd) /\
  fn_has_code sb sd fn ==>
  is_bytestring_type ty /\
  ?buf sc.
    compile_alloc_buffer (type_memory_bytes ce ty) sb = (buf,sc) /\
    compile_store_bytestring (vv_operand vv) buf.buf_operand sc = ((),sd) /\
    op = buf.buf_operand /\ fn_has_code sb sc fn
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `~(?ann fid args dret. arm = Call ann (IntCall fid) args dret)` by
    (drule_all ifexp_allocating_arm_noncall >> simp[]) >>
  `is_bytestring_type ty` by
    (drule_all ifexp_residual_noncall_bytes >> simp[]) >>
  drule_all ifexp_selected_arm_allocation_premises >> strip_tac >>
  drule_all ifexp_allocating_unwrap_noop >> strip_tac >> gvs[] >>
  gvs[compile_store_memory_def]
QED
