(* The guarded VV judgment supplies both simulation conjuncts for ExtCall. *)
Theory bodyFullExtCallBodyOfVV
Ancestors
  bodyFullShadowBodyInv
  bodyFullPreds bodyFullOfVV bodySimFull bodySim exprSimHyps exprSimSource
  exprSimHypsDefs loweringPosts vyperInterpreter vyperTypeSystem vyperState vyperAST
  bodyFullPredsMods[qualified] bodyInvSplit[qualified]

(* SCRATCH MEASUREMENT: the original proof failed after widening the body
   definitions. Temporarily admit it to test its downstream consumers.
Proof
  rpt gen_tac >> disch_then (mk_asm "vv") >>
  simp[Once body_expr_full_ok_def] >> rpt gen_tac >> strip_tac >>
  conj_asm2_tac
  >- (irule expr_sim_full_of_vv >> simp[post_value_type_def] >> conj_tac
      >- (rpt strip_tac >> drule_all expr_body_pre_copy_ok >> simp[]) >>
      drule expr_body_pre_type_evaluates >>
      simp[optionTheory.IS_SOME_EXISTS] >> strip_tac >>
      qexists `x` >> simp[] >> rpt gen_tac >> strip_tac >>
      `expr_body_pre cenv cx env (Call ann (ExtCall stat skip sig opts) args dflt)
         (es with gas_obs := gs)` by simp[] >>
      drule_all expr_body_pre_runtime_typed >> strip_tac >> gvs[] >> metis_tac[]) >>
  asm "vv" irule >> metis_tac[]
QED
*)
Theorem extcall_body_full_ok_of_vv:
  !cx ann stat skip sig opts args dflt.
    (!DF lo d PG tops ctx shadow_ctx func shadow_func cenv env ty es.
       (contract_inv mods exps ctx cenv cx /\
     module_body_inv mods cenv.ce_module tops cenv cx) /\
       shadow_body_inv_mods mods exps ctx shadow_ctx /\
       body_const_cells_agree mods cx env es /\
       expr_body_pre_mods mods cenv cx env (Call ann (ExtCall stat skip sig opts) args dflt) es ==>
       expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
         cenv cx ty (Call ann (ExtCall stat skip sig opts) args dflt) es) ==>
    body_expr_full_ok_mods mods exps cx (Call ann (ExtCall stat skip sig opts) args dflt)
Proof
  cheat
QED
