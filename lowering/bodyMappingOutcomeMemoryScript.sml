(* Counted semantic sequencing for mapping subscripts. *)
Theory bodyMappingOutcomeMemory
Ancestors
  mappingSubscriptCode mappingSubscriptSemantics exprSimSubscriptMap
  bodyMemMapBase bodyMemoryPreds
  exprSimMemDefs exprSimMapMemDefs

Theorem mapping_index_sim_mem[local]:
  (!s res t. eval_expr cx obj s = (INL res,t) ==>
     body_expr_mem_ok cx idx) /\
  body_inv tops ctx cenv cx /\
  (expr_body_pre cenv cx env (Subscript ann obj idx) es \/
   expr_map_pre cenv cx env (Subscript ann obj idx) es) /\
  place_type cenv obj = MapPT kt vt /\
  gas_marked_exec T (ctx,func) (eval_expr cx obj)
    (es,s0) marks (INL tv) mid (OK t) ==>
  expr_sim_mem ctx func cenv cx (expr_type idx) idx (mid with gas_obs := [])
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac
      (CONJUNCTS_THEN2 assume_tac strip_assume_tac))) >>
  drule_all mapping_subscript_marked_index_pre >> strip_tac >>
  `body_expr_mem_ok cx idx` by metis_tac[] >>
  qpat_x_assum `body_expr_mem_ok cx idx`
    (mp_tac o CONJUNCT1 o REWRITE_RULE [body_expr_mem_ok_def]) >>
  disch_then (qspecl_then
    [`tops`, `ctx`, `func`, `cenv`, `env`, `expr_type idx`,
     `mid with gas_obs := []`] mp_tac) >> simp[]
QED
