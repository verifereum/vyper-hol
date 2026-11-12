Theory bodyPtrIfExpNoopPost
Ancestors
  bodyPtrIfExpUnwrapNoop bodyPtrDefs exprSimUnwrap exprSimUnwrapProps
  exprLowering loweringPosts vyperState compileEnv context

Theorem unwrap_value_noop_post:
  ~is_word_type (expr_type e) /\
  vv_post ctx fn ce cx e es sa sc s0 ee tv vv u /\
  ptr_vv_ok cx (expr_type e) tv vv ee G tn u /\
  read_result cx tv ee = (INL v,ee) /\
  (!ty op. vv = StackValue ty op /\ ~is_word_type (expr_type e) ==>
     ptr_buf_ok ce e op G u) /\
  (!ty p. vv = LocatedValue ty p /\ p.ptr_location = LocMemory ==>
     ptr_buf_ok ce e p.ptr_operand G u) /\
  ((?ty op. vv = StackValue ty op) \/
   (?ty p. vv = LocatedValue ty p /\ ~is_word_type ty /\ p.ptr_location = LocMemory)) /\
  unwrap_value ce vv sc = (op,sn) ==>
  sn = sc /\ expr_post ctx fn ce cx e es sa sn s0 ee v op u /\
  ptr_val_ok cx (expr_type e) v op G tn u /\ ptr_buf_ok ce e op G u
Proof
  strip_tac >>
  `vv_post ctx fn ce cx e es sa sc s0 ee (Value v) vv u` by
    (drule vv_post_read_result >> disch_then (fn th => fs[th])) >>
  `sn = sc /\ op = vv_operand vv` by metis_tac[unwrap_value_noop_endpoint] >>
  gvs[vv_operand_def]
  >- (conj_tac >- metis_tac[expr_post_of_vv_post_stack] >>
      gvs[ptr_vv_ok_def] >> metis_tac[]) >>
  conj_tac >- metis_tac[expr_post_of_vv_post_memory] >>
  gvs[ptr_vv_ok_def, ptr_val_ok_def] >> metis_tac[]
QED
