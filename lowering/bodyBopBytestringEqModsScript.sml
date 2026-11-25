(* Linked bytestring equality/inequality route. *)
Theory bodyBopBytestringEqMods
Ancestors
  bodyFullPredsMods bodyFullPostsMods bodyFullShadowBodyInv bodyInvSplit
  bodyFullBopBytestringCuts bodyFullBopBytestringChild bodyFullBopBytestringIntervals
  bodyFullBopBytestringPost bodyFullBopBytestringFinalPost
  bodyFullBopBytestringHash bodyFullBopBytestringDigest bodyFullBopBytestringFinish
  bodyFullBopBytestringChild bodyFullExprCore
  gasOutcomeFullBindMods gasOutcomeFullPostMods gasOutcomeFullPostPathMods
  gasExemptCertMods bodyMemoryDefs exprSimFullBundleProps exprBodyPreProps
  exprSimHypsDefs exprLoweringProps loweringPosts bodyPtrDefs
  gasStorage gasShadow gasShadowState vyperStorageTrace vyperStorageFootprint
  vyperState compileEnv exprBopSimProps exprBopSimDefs exprSimSource
  vyperTypeSystem vyperTypeInvariants vyperAST vyperInterpreter contextRawReachable
Libs monadsyntax

Theorem bop_bytestring_eq_value_sim_mods:
  !DF lo d PG src tops ctx shadow_ctx func shadow_func cenv cx env ty ann bop e1 e2 es.
    (bop = Eq \/ bop = NotEq) /\ is_bytestring_type (expr_type e1) /\
    body_exprs_full_ok_mods mods exps cx [e1; e2] /\
    contract_inv mods exps ctx cenv cx /\ module_body_inv mods src tops cenv cx /\
    shadow_body_inv_mods mods exps ctx shadow_ctx /\
    body_const_cells_agree_mods mods cx env es /\
    expr_body_pre_mods mods cenv cx env (Builtin ann (Bop bop) [e1; e2]) es ==>
    expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (Builtin ann (Bop bop) [e1; e2]) es
Proof
  cheat
QED
