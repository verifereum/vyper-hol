(* Physical no-op unwrap retains an arbitrary destination frame R unchanged.
   Active (storage/code) unwrap branches will use the same physical post. *)
Theory abiEncTuplePtrMaterializePrefix
Ancestors
  abiEncTuplePtrMaterializeAlloc bodyPtrIfExpUnwrapNoop exprPtrUnwrapIdentity
  exprSimAggregateChildren exprSimUnwrap exprSimUnwrapProps exprSimMemorySource
  exprPtrUnwrapMarked
  bodyPtrDefs loweringPosts fragGasPathPtr compileEnv context

Theorem materialize_noop_physical_post:
  ((?ty op. vv = StackValue ty op) \/
   (?ty p. vv = LocatedValue ty p /\ ~is_word_type ty /\
           p.ptr_location = LocMemory)) /\
  unwrap_value ce vv sm = (src,su) /\
  vv_post ctx fn ce cx e es sa sm s0 ee raw vv s /\
  read_result cx raw ee = (INL v,ee) ==>
  expr_post ctx fn ce cx e ee (sa with cs_next_var := sm.cs_next_var)
    su s ee v src s
Proof
  rpt gen_tac >> disch_tac >>
  `su = sm /\ src = vv_operand vv` by metis_tac[unwrap_value_noop_endpoint] >>
  gvs[] >>
  drule vv_post_rebase >> strip_tac >>
  all_tac
  >~ [`StackValue ty op`]
  >- (gvs[vv_post_def, vv_holds_def, vv_at_def, vv_own_def,
          expr_post_def, vv_operand_def, expr_val_own_def, expr_val_at_def]) >>
  rename1 `LocatedValue ty p` >>
  `p.ptr_location = LocMemory /\ ~is_word_type ty` by metis_tac[] >>
  simp[vv_operand_def] >> irule expr_post_of_vv_post_memory >>
  simp[] >> qexists `ty` >> simp[] >> metis_tac[vv_post_read_result]
QED

Theorem materialize_noop_physical_ptr_frame:
  ((?ty op. vv = StackValue ty op) \/
   (?ty p. vv = LocatedValue ty p /\ ~is_word_type ty /\
           p.ptr_location = LocMemory)) /\
  unwrap_value ce vv sm = (src,su) /\
  vv_post ctx fn ce cx e es sa sm s0 ee raw vv s /\
  read_result cx raw ee = (INL v,ee) /\
  ptr_vv_ok cx (post_value_type ce e) raw vv ee G tn s /\
  (!ty op. vv = StackValue ty op /\ ~is_word_type (post_value_type ce e) ==>
    ptr_buf_ok ce e op G s) /\
  (!ty p. vv = LocatedValue ty p /\ p.ptr_location = LocMemory ==>
    ptr_buf_ok ce e p.ptr_operand G s) /\
  ~s.vs_halted /\ R sm G tn s ==>
  su = sm /\ src = vv_operand vv /\
  gas_path_ptr D 0 ctx fn PG G tn s 0 G tn (OK s) /\
  expr_post ctx fn ce cx e ee (sa with cs_next_var := sm.cs_next_var)
    su s ee v src s /\
  ptr_val_ok cx (post_value_type ce e) v src G tn s /\
  (~is_word_type (post_value_type ce e) ==> ptr_buf_ok ce e src G s) /\
  R su G tn s
Proof
  rpt gen_tac >> disch_tac >>
  `expr_post ctx fn ce cx e ee (sa with cs_next_var := sm.cs_next_var)
    su s ee v src s` by metis_tac[materialize_noop_physical_post] >>
  `su = sm /\ src = vv_operand vv` by metis_tac[unwrap_value_noop_endpoint] >>
  gvs[] >>
  gvs[ptr_vv_ok_def, vv_operand_def, ptr_val_ok_def] >>
  simp[cj 1 gas_path_ptr_rules] >>
  drule vv_post_located_type >>
  strip_tac >> gvs[] >>
  Cases_on `post_value_type ce e` >>
  gvs[is_bytestring_type_def, is_word_type_def] >>
  Cases_on `b` >> gvs[is_bytestring_type_def, is_word_type_def] >>
  Cases_on `b'` >> gvs[is_bytestring_type_def, is_word_type_def]
QED
