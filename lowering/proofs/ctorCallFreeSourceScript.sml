(* Source-side boundary for the constructor's call-free lowering proof. *)
Theory ctorCallFreeSource
Ancestors
  list option e2eDeployDefs ctorDeployInitcode ctorDeployShape loweringShapeSource
  vyperTypeContractContext vyperTypeContract supportedStmtTraverse compileVyper

Theorem classified_constructor_call_free_source:
  !tops rpolicy runtime_bc dunit am tx exts ints fb
   mut nr rr fname args defaults ret ctor_body.
    lower_vyper_deploy_unit tops rpolicy runtime_bc = SOME dunit /\
    constructor_call_free tops /\ deploy_typing_ok tops am tx /\
    classify_functions tops =
      (exts, ints, fb, SOME (mut,nr,rr,fname,args,defaults,ret,ctor_body)) ==>
    ~supported_stmts_expr_exists constructor_call_root ctor_body /\
    ~supported_stmts_expr_exists expr_shape_root ctor_body
Proof
  rpt gen_tac >> strip_tac >>
  drule_all lower_vyper_deploy_unit_ctor_named_init >>
  simp[ctor_named_init_def] >> strip_tac >>
  qspecl_then [`tops`, `NONE`, `"__init__"`] mp_tac
    classify_functions_ctor_lookup >>
  simp[] >> strip_tac >>
  `~supported_stmts_expr_exists constructor_call_root ctor_body` by
    metis_tac[constructor_call_free_def] >>
  simp[] >>
  `~supported_stmts_expr_exists expr_raw_shape_root ctor_body` by
    (strip_tac >>
     qpat_x_assum `~supported_stmts_expr_exists constructor_call_root _` mp_tac >>
     simp[] >> irule (cj 2 supported_stmt_expr_exists_mono) >>
     first_assum (irule_at Any) >>
     rpt strip_tac >> gvs[expr_raw_shape_root_def, constructor_call_root_def]) >>
  `MEM (FunctionDecl Deploy mut nr rr fname args defaults ret ctor_body) tops` by
    (irule classify_functions_ctor_mem >> simp[]) >>
  gvs[deploy_typing_ok_def] >>
  drule check_contract_deploy_function_body_MEM >> simp[] >>
  disch_then drule_all >>
  simp[check_function_body_def, IS_SOME_EXISTS] >> strip_tac >>
  metis_tac[type_stmt_raw_shape]
QED
