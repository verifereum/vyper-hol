Theory stmtSimLogDataRun
Ancestors
  exprSimDefs exprSimProps exprSimStack loweringPosts
  stmtSimLogData stmtSimLogDataFrame  valueEncoding compileEnv
  context stmtLowering words list arithmetic emitHelper emitHelperProps
  exprSimBufferStore exprLoweringProps

Definition log_data_layout_def:
  (log_data_layout cx [] [] p mem = T) /\
  (log_data_layout cx [] (v::vs) p mem = F) /\
  (log_data_layout cx (ty::tys) [] p mem = F) /\
  (log_data_layout cx (ty::tys) (v::vs) p mem =
    ?tv. evaluate_type (get_tenv cx) ty = SOME tv /\ val_wf tv v /\
         val_in_memory tv v p mem /\
         log_data_layout cx tys vs (p + type_memory_size tv) mem)
End

Theorem log_data_layout_lengths:
  !tys vs p mem. log_data_layout cx tys vs p mem ==> LENGTH tys = LENGTH vs
Proof
  cheat
QED

Theorem log_data_layout_tuple:
  !tys vs p mem. log_data_layout cx tys vs p mem ==>
  ?tvs. LIST_REL (\ty tv. evaluate_type (get_tenv cx) ty = SOME tv) tys tvs /\
    tuple_in_memory vs tvs p mem /\ EVERY2 val_wf tvs vs
Proof
  cheat
QED

Theorem log_data_layout_suffix_frame:
  !tys vs p mem. log_data_layout cx tys vs p mem /\
    EVERY supported_scalar_type tys /\
    log_write_frame st (p + SUM (MAP (type_memory_bytes cenv) tys)) n s t /\
    s.vs_memory = mem ==>
    log_data_layout cx tys vs p t.vs_memory
Proof
  cheat
QED

Theorem compile_log_store_data_shape:
  !xs buf off sa sb. EVERY (supported_scalar_type o SND) xs /\
    compile_log_store_data cenv xs buf off sa = ((),sb) ==>
    same_blocks sa sb /\
    sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb /\
    sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id
Proof
  cheat
QED

Definition log_data_source_def:
  log_data_source cx b cap s (op,ty) v <=>
    supported_scalar_type ty /\
    (?tv. evaluate_type (get_tenv cx) ty = SOME tv /\
      value_has_type tv v /\ val_wf tv v) /\
    expr_val_rel cx ty v op s /\ log_source_apart cx b cap (op,ty) v s
End

Theorem log_data_sources_kept:
  !xs vs. LIST_REL (log_data_source cx b cap s) xs vs /\
    EVERY (\(op,ty). !x. op = Var x ==> not_fresh_at st x) xs /\
    log_write_frame st b cap s t ==>
    LIST_REL (log_data_source cx b cap t) xs vs
Proof
  cheat
QED

Theorem log_data_sources_types:
  !xs vs. LIST_REL (log_data_source cx b cap s) xs vs ==>
    EVERY (supported_scalar_type o SND) xs
Proof
  cheat
QED

Theorem log_data_fresh_mono:
  EVERY (\(op,ty). !x. op = Var x ==> not_fresh_at sa x) xs /\
  sa.cs_next_var <= sb.cs_next_var ==>
  EVERY (\(op,ty). !x. op = Var x ==> not_fresh_at sb x) xs
Proof
  cheat
QED

Theorem compile_log_store_data_split:
  supported_scalar_type ty /\
  compile_log_store_data cenv ((src,ty)::xs) buf off sa = ((),sb) ==>
  ?dst sm sn. emit_op ADD [buf; Lit (n2w off)] sa = (dst,sm) /\
    compile_store_memory cenv src dst ty ty sm = ((),sn) /\
    compile_log_store_data cenv xs buf (off + type_memory_bytes cenv ty) sn = ((),sb) /\
    inst_extends sa sn /\ sa.cs_next_var <= sn.cs_next_var
Proof
  cheat
QED

Theorem log_write_frame_frontier:
  log_write_frame sb b n s t /\ sa.cs_next_var <= sb.cs_next_var ==>
  log_write_frame sa b n s t
Proof
  cheat
QED

Theorem log_data_layout_cons_suffix:
  supported_scalar_type ty /\ evaluate_type (get_tenv cx) ty = SOME tv /\
  val_wf tv v /\ val_in_memory tv v p s.vs_memory /\
  log_data_layout cx tys vs (p + type_memory_bytes cenv ty) t.vs_memory /\
  log_write_frame st (p + type_memory_bytes cenv ty) n s t ==>
  log_data_layout cx (ty::tys) (v::vs) p t.vs_memory
Proof
  cheat
QED

Theorem log_write_frame_join:
  log_write_frame sa p a s q /\ log_write_frame sb (p+a) n q t /\
  sa.cs_next_var <= sb.cs_next_var ==>
  log_write_frame sa p (a+n) s t
Proof
  cheat
QED

Theorem compile_log_store_data_run_core[local]:
  !xs vs off sa sb s.
    compile_log_store_data cenv xs buf off sa = ((),sb) /\
    LIST_REL (log_data_source cx b cap s) xs vs /\
    EVERY (\(op,ty). !x. op = Var x ==> not_fresh_at sa x) xs /\
    (!x. buf = Var x ==> not_fresh_at sa x) /\
    eval_operand buf s = SOME (n2w b) /\
    off + SUM (MAP (type_memory_bytes cenv) (MAP SND xs)) <= cap /\
    b + cap < dimword (:256) ==>
    ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
      log_data_layout cx (MAP SND xs) vs (b + off) t.vs_memory /\
      log_write_frame sa (b + off)
        (SUM (MAP (type_memory_bytes cenv) (MAP SND xs))) s t
Proof
  cheat
QED

Theorem compile_log_store_data_run:
  compile_log_store_data cenv xs buf off sa = ((),sb) /\
  LIST_REL (log_data_source cx b cap s) xs vs /\
  EVERY (\(op,ty). !x. op = Var x ==> not_fresh_at sa x) xs /\
  (!x. buf = Var x ==> not_fresh_at sa x) /\
  eval_operand buf s = SOME (n2w b) /\
  off + SUM (MAP (type_memory_bytes cenv) (MAP SND xs)) <= cap /\
  b + cap < dimword (:256) ==>
  inst_extends sa sb /\ sa.cs_next_var <= sb.cs_next_var /\
  ?t. run_inst_seq (emitted_insts sa sb) s = OK t /\
    log_data_layout cx (MAP SND xs) vs (b + off) t.vs_memory /\
    log_write_frame sa (b + off)
      (SUM (MAP (type_memory_bytes cenv) (MAP SND xs))) s t /\
    LIST_REL (log_data_source cx b cap t) xs vs /\
    eval_operand buf t = SOME (n2w b) /\
    (!op ty. MEM (op,ty) xs ==> eval_operand op t = eval_operand op s)
Proof
  cheat
QED
