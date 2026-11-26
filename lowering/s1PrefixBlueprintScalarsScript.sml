(* Scalar request cuts after blueprint target and constructor evaluation. *)
Theory s1PrefixBlueprintScalars
Ancestors
  s1PrefixPreds blueprintLiteralOffsetProps exprSimWordArgs vyperStorageTrace
  exprLowering builtinCreate vyperState bodyFullExprsListFacts bodyFullExprsSingleton

(* The ready predicates carry the operand-cut posts, including all-tail
   replay and the frame for target and constructor operands.  Keep these
   posts at the reached machine states when entering the next source cut. *)
Theorem blueprint_scalar_cuts_prefix:
  (if salted then ?e. salts = [e] /\ expr_type e = BaseT (BytesT (Fixed 32))
   else salts = []) /\
  body_exprs_full_ok cx (amount::(salts ++ [offset])) /\
  body_exprs_prefix_ok cx (amount::(salts ++ [offset])) /\
  (!av sv ov. storage_trace_frame (kfinal av sv ov : evaluation_state -> value evaluation_result)) /\
  (!next.
    body_expr_full_ok cx amount /\ body_expr_prefix_ok cx amount /\
    (!v. storage_trace_frame (next v : evaluation_state -> value evaluation_result)) /\
    (!v em Gm tm m. Amount v em Gm tm m ==>
      gas_prefix_full settings cx st0 (next v) (em,m,Gm,tm)) ==>
    gas_prefix_full settings cx st0
      (bind (bind (eval_expr cx amount) (read_result cx)) next) (es,s,G,tn)) /\
  (!v em Gm tm m. Amount v em Gm tm m ==>
    ?a r b a' w b'. eval_expr cx amount a = (INL r,b) /\
                     read_result cx r a' = (INL w,b')) /\
  (!av em Gm tm m next.
    salted /\ Amount av em Gm tm m /\
    body_expr_full_ok cx (HD salts) /\ body_expr_prefix_ok cx (HD salts) /\
    (!v. storage_trace_frame (next v : evaluation_state -> value evaluation_result)) /\
    (!v en Gn tnn n. Salt av v em Gm tm m en Gn tnn n ==>
      gas_prefix_full settings cx st0 (next v) (en,n,Gn,tnn)) ==>
    gas_prefix_full settings cx st0
      (bind (bind (eval_expr cx (HD salts)) (read_result cx)) next) (em,m,Gm,tm)) /\
  (!av v em Gm tm m en Gn tnn n.
    Salt av v em Gm tm m en Gn tnn n ==>
    ?a r b a' w b'. eval_expr cx (HD salts) a = (INL r,b) /\
                     read_result cx r a' = (INL w,b')) /\
  (!av em Gm tm m. ~salted /\ Amount av em Gm tm m ==>
    BeforeOffset av NONE em Gm tm m) /\
  (!av v em Gm tm m en Gn tnn n.
    Amount av em Gm tm m /\ Salt av v em Gm tm m en Gn tnn n ==>
    BeforeOffset av (SOME v) en Gn tnn n) /\
  (!av sv en Gn tnn n.
    expr_int_literal (origin_fold_value offset) = NONE /\
    BeforeOffset av sv en Gn tnn n /\
    body_expr_full_ok cx offset /\ body_expr_prefix_ok cx offset /\
    (!v. storage_trace_frame (kfinal av sv v)) /\
    (!v ee Ge te t. Offset av sv v en Gn tnn n ee Ge te t ==>
      gas_prefix_full settings cx st0 (kfinal av sv v) (ee,t,Ge,te)) ==>
    gas_prefix_full settings cx st0
      (bind (bind (eval_expr cx offset) (read_result cx)) (kfinal av sv)) (en,n,Gn,tnn)) /\
  (!av sv v en Gn tnn n ee Ge te t.
    BeforeOffset av sv en Gn tnn n /\ Offset av sv v en Gn tnn n ee Ge te t ==>
    gas_prefix_full settings cx st0 (kfinal av sv v) (ee,t,Ge,te)) /\
  (!av sv en Gn tnn n i.
    expr_int_literal (origin_fold_value offset) = SOME i /\
    BeforeOffset av sv en Gn tnn n ==>
    gas_prefix_full settings cx st0 (kfinal av sv (IntV i)) (en,n,Gn,tnn)) ==>
  gas_prefix_full settings cx st0
    (bind (eval_exprs cx (amount::(salts ++ [offset])))
      (\vs. kfinal (HD vs) (if salted then SOME (EL 1 vs) else NONE) (LAST vs)))
    (es,s,G,tn)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!av sv en Gn tnn n. BeforeOffset av sv en Gn tnn n /\
    body_exprs_full_ok cx [offset] /\ body_exprs_prefix_ok cx [offset] ==>
    gas_prefix_full settings cx st0
      (bind (bind (eval_expr cx offset) (read_result cx)) (kfinal av sv))
      (en,n,Gn,tnn)` by
    (rpt gen_tac >>
     rewrite_tac[body_exprs_full_ok_singleton, Once body_exprs_prefix_ok_def] >>
     simp[Once body_exprs_prefix_ok_def] >> strip_tac >>
     Cases_on `expr_int_literal (origin_fold_value offset)`
     >- (fs[] >> metis_tac[]) >>
     rename1 `expr_int_literal (origin_fold_value offset) = SOME i` >>
     `bind (eval_expr cx offset) (read_result cx) = return (IntV i)` by
       (simp[FUN_EQ_THM,return_def] >> metis_tac[blueprint_literal_offset_read]) >>
     simp[bind_return] >> metis_tac[]) >>
  qpat_x_assum `body_exprs_full_ok cx (amount::_)`
    (strip_assume_tac o ONCE_REWRITE_RULE [body_exprs_full_ok_cons]) >>
  qpat_x_assum `body_exprs_prefix_ok cx (amount::_)`
    (strip_assume_tac o ONCE_REWRITE_RULE [body_exprs_prefix_ok_def]) >>
  once_rewrite_tac[exprSimWordArgsTheory.eval_exprs_cons_action] >>
  simp[NoAsms,bind_assoc,bind_return] >> once_rewrite_tac[GSYM bind_assoc] >>
  first_assum irule >>
  simp[storage_trace_frame_bind_all,evaluate_storage_trace_frame] >>
  rpt gen_tac >> disch_tac >>
  `body_exprs_full_ok cx (salts ++ [offset]) /\ body_exprs_prefix_ok cx (salts ++ [offset])`
    by metis_tac[] >>
  Cases_on `salted`
  >- suspend "salt_present" >>
  suspend "salt_absent"
QED

Resume blueprint_scalar_cuts_prefix[salt_present]:
  gvs[] >>
  qpat_x_assum `body_exprs_full_ok cx (_::[offset])`
    (strip_assume_tac o ONCE_REWRITE_RULE [body_exprs_full_ok_cons]) >>
  qpat_x_assum `body_exprs_prefix_ok cx (_::[offset])`
    (strip_assume_tac o ONCE_REWRITE_RULE [body_exprs_prefix_ok_def]) >>
  once_rewrite_tac[exprSimWordArgsTheory.eval_exprs_cons_action] >>
  simp[NoAsms,bind_assoc,bind_return] >> once_rewrite_tac[GSYM bind_assoc] >>
  qpat_assum `!av em Gm tm m next. _ ==> gas_prefix_full _ _ _ _ _` irule >>
  simp[storage_trace_frame_bind_all,evaluate_storage_trace_frame] >>
  qexists `v` >> simp[] >> rpt gen_tac >> disch_tac >>
  `eval_exprs cx [] = return []` by
    simp[FUN_EQ_THM,exprSimWordArgsTheory.eval_exprs_nil,return_def] >>
  once_rewrite_tac[exprSimWordArgsTheory.eval_exprs_cons_action] >>
  simp[bind_assoc,bind_return] >> once_rewrite_tac[GSYM bind_assoc] >>
  metis_tac[]
QED

Resume blueprint_scalar_cuts_prefix[salt_absent]:
  gvs[] >>
  `eval_exprs cx [] = return []` by
    simp[FUN_EQ_THM,exprSimWordArgsTheory.eval_exprs_nil,return_def] >>
  once_rewrite_tac[exprSimWordArgsTheory.eval_exprs_cons_action] >>
  simp[bind_assoc,bind_return] >> once_rewrite_tac[GSYM bind_assoc] >>
  metis_tac[]
QED

Finalise blueprint_scalar_cuts_prefix
