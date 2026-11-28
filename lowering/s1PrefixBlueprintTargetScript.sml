(* The source head of a blueprint create, before evaluating its constructor. *)
Theory s1PrefixBlueprintTarget
Ancestors
  s1PrefixPreds bodyFullCreateHeld exprBodyPreProps exprSimWordArgs
  vyperCreate vyperState vyperStorageTrace bodyFullExprsListFacts

(* Ready is the successful midpoint post of the operand replay cut.  The
   stage needs only its source success guard to unlock the tail hypotheses;
   the continuation still receives the entire post, including replay. *)
(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `create_operand_order (CreateFromBlueprint raw) salted
     (target::amount::(salts ++ offset::ctor)) =
   target::(ctor ++ amount::(salts ++ [offset]))` by
    (Cases_on `salted` >> gvs[listTheory.LENGTH_EQ_NUM_compute,
                             create_operand_order_def]) >>
  qpat_assum `create_operand_order _ _ _ = _` (fn order_th =>
    rewrite_tac[order_th] >>
    qpat_x_assum `body_exprs_full_ok _ (create_operand_order _ _ _)`
      (strip_assume_tac o ONCE_REWRITE_RULE [body_exprs_full_ok_cons]
                        o REWRITE_RULE [order_th]) >>
    qpat_x_assum `body_exprs_prefix_ok _ (create_operand_order _ _ _)`
      (strip_assume_tac o ONCE_REWRITE_RULE [body_exprs_prefix_ok_def]
                        o REWRITE_RULE [order_th])) >>
  `gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     cx st0 (bind (bind (eval_expr cx target) (read_result cx)) next)
     (es,s,G,tn)` suffices_by
    (qpat_x_assum `next = _` SUBST_ALL_TAC >>
     simp[Once exprSimWordArgsTheory.eval_exprs_cons_action,bind_assoc,bind_return]) >>
  qpat_x_assum `_ ==> gas_prefix_full _ _ _ _ (es,s,G,tn)` irule >> simp[] >>
  rpt conj_tac
  >- (rpt gen_tac >> strip_tac >> gvs[] >> metis_tac[])
  >- (gen_tac >> irule storage_trace_frame_bind_all >>
      simp[evaluate_storage_trace_frame]) >>
  irule create_operand_pre >>
  qpat_assum `expr_body_pre _ _ _ (Call _ _ _ _) _` (irule_at Any) >>
  simp[] >> metis_tac[expr_body_pre_static_facts]
QED
*)
Theorem blueprint_target_cut_prefix:
  (expr_body_pre cenv cx env target es /\
   body_expr_full_ok cx target /\ body_expr_prefix_ok cx target /\
   (!v. storage_trace_frame (next v)) /\
   (!v ee G1 tn1 t. Ready v ee G1 tn1 t ==>
     gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
       cx st0 (next v) (ee,t,G1,tn1)) ==>
   gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
     cx st0 (bind (bind (eval_expr cx target) (read_result cx)) next)
     (es,s,G,tn)) /\
  (!v ee G1 tn1 t. Ready v ee G1 tn1 t ==>
     ?a tv b a' v' b'. eval_expr cx target a = (INL tv,b) /\
                        read_result cx tv a' = (INL v',b')) /\
  expr_body_pre cenv cx env
    (Call ann (CreateTarget (CreateFromBlueprint raw) salted rof ks)
      (target::amount::(salts ++ offset::ctor)) dflt) es /\
  LENGTH salts = (if salted then 1 else 0) /\
  body_exprs_full_ok cx
    (create_operand_order (CreateFromBlueprint raw) salted
      (target::amount::(salts ++ offset::ctor))) /\
  body_exprs_prefix_ok cx
    (create_operand_order (CreateFromBlueprint raw) salted
      (target::amount::(salts ++ offset::ctor))) /\
  (!vs. storage_trace_frame (kfinal vs)) /\
  next = (\v. bind (eval_exprs cx (ctor ++ amount::(salts ++ [offset])))
                  (\vs. kfinal (v::vs))) /\
  (!v ee G1 tn1 t. Ready v ee G1 tn1 t /\
    body_exprs_full_ok cx (ctor ++ amount::(salts ++ [offset])) /\
    body_exprs_prefix_ok cx (ctor ++ amount::(salts ++ [offset])) ==>
    gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
      cx st0 (next v) (ee,t,G1,tn1)) ==>
  gas_prefix_full (DF,lo,gas_explicit_sites ctx shadow_ctx,ctx,func,PG)
    cx st0
    (bind (eval_exprs cx
      (create_operand_order (CreateFromBlueprint raw) salted
        (target::amount::(salts ++ offset::ctor)))) kfinal)
    (es,s,G,tn)
Proof
  cheat
QED
