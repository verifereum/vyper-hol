Theory forConsBodyGas
Ancestors
  gasContext stmtSimDefs stmtSimForParts exprSimMemorySource loweringPosts
  vyperInterpreter vyperState finite_map

(* Admissibility of a remaining loop implies admissibility of its first
   body, in the scope created by reading the first iterator element. *)
Theorem captured_storage_body_admissible:
  gas_admissible (eval_for cx tyv id stmts (a::rs)) ok es /\
  (!res. ok res ==> stmt_res_ok lctx res) /\
  lookup_scopes id es.scopes = NONE /\ read_result cx a es = (INL v,es) ==>
  gas_admissible (eval_stmts cx stmts) (stmt_res_ok (InLoop exit incr))
    (es with <| scopes :=
      (FEMPTY |+ (id, <|assignable := F; type := tyv; value := v; popped := []|>)) :: es.scopes;
      gas_obs := [] |>)
Proof
  strip_tac >> simp[gas_admissible_def] >> rpt gen_tac >> strip_tac >>
  rename1 `eval_stmts cx stmts _ = (raw,ef)` >>
  `read_result cx a (es with gas_obs := gs) = (INL v,es with gas_obs := gs)` by
    (drule exprSimMemorySourceTheory.read_result_gas_obs >> simp[]) >>
  `eval_for cx tyv id stmts (a::rs) (es with gas_obs := gs) =
   eval_for cx tyv id stmts (Value v::rs) (es with gas_obs := gs)` by
    (qpat_assum `read_result cx a (es with gas_obs := gs) = _`
       (mp_then Any (rewrite_tac o single) vyperInterpreterTheory.eval_for_cons_read) >>
     `read_result cx (Value v) (es with gas_obs := gs) = (INL v,es with gas_obs := gs)` by
       simp[read_result_def,return_def] >>
     qpat_assum `read_result cx (Value v) _ = _`
       (mp_then Any (rewrite_tac o single) vyperInterpreterTheory.eval_for_cons_read)) >>
  Cases_on `eval_for cx tyv id stmts (Value v::rs) (es with gas_obs := gs)` >>
  rename1 `eval_for cx tyv id stmts (Value v::rs) _ = (lr,le)` >>
  `stmt_res_ok lctx lr` by
    (first_x_assum irule >>
     qpat_assum `gas_admissible _ _ _`
       (qspecl_then [`gs`,`lr`,`le`] mp_tac o REWRITE_RULE[gas_admissible_def]) >> simp[]) >>
  qpat_assum `eval_for cx tyv id stmts (Value v::rs) _ = (lr,le)`
    (mp_then Any mp_tac stmtSimForPartsTheory.eval_for_cons_cases) >>
  simp[] >> strip_tac >> gvs[] >>
  qpat_x_assum `stmt_res_ok lctx _` mp_tac >> simp[stmt_res_ok_def]
QED
