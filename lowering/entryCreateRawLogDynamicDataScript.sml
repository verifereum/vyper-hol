(* Scoped dynamic RawLog data continuation, anchored at the topics exit. *)
Theory entryCreateRawLogDynamicData
Ancestors
  entryCreateScopedBind entryCreateReplayBind entryCreateFocusSpec
  bodyFullRawLogDynamic bodyFullRawLogDynamicTail entryCreateRawLogCase
  gasOutcomeFull gasSummaryCompose vyperStorageTrace vyperState
  exprSimDefs exprSimFullBundleProps loweringPosts bodyPtrDefs
  compileEnv venomInst list rich_list arithmetic

Theorem create_raw_log_dynamic_data_scoped_cut:
  expr_type data = BaseT (BytesT (Dynamic cap)) /\
  gas_shadow_context ctx shctx /\
  scoped_operand_outcome (DF,lo,gas_explicit_sites ctx shctx,ctx,func,PG) tops cx st0 a m
    source (es,s,G,tn) Q1
    (\H res ee gt r. (?exc. res = INR exc) /\ R H res ee gt r) /\
  (!marks res mid G1 tn1 t.
     (!tail. source (es with gas_obs :=
       gas_explicit marks s.vs_gas_readings ++ tail) =
       (res,mid with gas_obs := tail)) /\
     storage_trace_domain cx st0 mid.storage_trace /\
     create_operand_at m t /\
     create_operand_full_scope a m (gas_explicit_sites ctx shctx) ctx func s marks (OK t) /\
     (!H. valid_horizon cx st0 H mid.storage_trace ==>
       Q1 H res mid G1 tn1 t /\
       gas_origin_ptr_path (DF H,lo,gas_explicit_sites ctx shctx,ctx,func,PG)
         (s,G,tn) marks (OK t,G1,tn1)) ==>
     ?v. res = INL v /\
       scoped_operand_outcome (DF,lo,gas_explicit_sites ctx shctx,ctx,func,PG) tops cx st0 m b
         (next v) (mid,t,G1,tn1) Q R) /\
  storage_trace_frame source /\ (!v. storage_trace_frame (next v)) /\
  (!marks err ee leaf finish.
     gas_exempt_cert T tops (ctx,func) (ignore_bind source (return ()))
       (es,s) marks (err,ee) (leaf,finish) ==>
     gas_exempt_cert T tops (ctx,func)
       (ignore_bind (bind source next) (return ()))
       (es,s) marks (err,ee) (leaf,finish)) /\
  (!left v mid t right err ee leaf finish.
     gas_marked_exec T (ctx,func) source (es,s) left (INL v) mid (OK t) /\
     gas_exempt_cert T tops (ctx,func)
       (ignore_bind (next v) (return ())) (mid with gas_obs := [],t)
       right (err,ee) (leaf,finish) ==>
     gas_exempt_cert T tops (ctx,func)
       (ignore_bind (bind source next) (return ()))
       (es,s) (left ++ right) (err,ee) (leaf,finish)) /\
  (!marks. create_operand_focus_scope a m (gas_explicit_sites ctx shctx) ctx func s marks ==>
     create_operand_focus_scope a b (gas_explicit_sites ctx shctx) ctx func s marks) /\
  (!marks r. exit_result r /\
     create_operand_full_scope a m (gas_explicit_sites ctx shctx) ctx func s marks r ==>
     create_operand_full_scope a b (gas_explicit_sites ctx shctx) ctx func s marks r) /\
  (!left t right.
     create_operand_full_scope a m (gas_explicit_sites ctx shctx) ctx func s left (OK t) /\
     create_operand_focus_scope m b (gas_explicit_sites ctx shctx) ctx func t right ==>
     create_operand_focus_scope a b (gas_explicit_sites ctx shctx) ctx func s (left ++ right)) /\
  (!left t right r.
     create_operand_full_scope a m (gas_explicit_sites ctx shctx) ctx func s left (OK t) /\
     create_operand_full_scope m b (gas_explicit_sites ctx shctx) ctx func t right r ==>
     create_operand_full_scope a b (gas_explicit_sites ctx shctx) ctx func s (left ++ right) r) ==>
  scoped_operand_outcome (DF,lo,gas_explicit_sites ctx shctx,ctx,func,PG) tops cx st0 a b
    (bind source next) (es,s,G,tn) Q R
Proof
  strip_tac >> irule scoped_operand_bind_all >>
  rpt conj_tac >> TRY (qexistsl_tac [`Q1`,`m`]) >>
  rpt (conj_tac ORELSE first_assum ACCEPT_TAC)
QED
