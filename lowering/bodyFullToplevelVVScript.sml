Theory bodyFullToplevelVV
Ancestors
  bodyFullToplevelVVStorage bodyFullToplevelVVImmutable bodyFullToplevelCtorSource
  exprSimTopLevelProps vyperTypeGlobalLookupSoundness bodySimFull
  exprSimHypsDefs exprSimSource exprSimHyps exprSimDefs bodyFullToplevelVVNil

Theorem toplevel_name_vv_nil:
  !DF lo d tops ctx func cenv cx env ty ann nsid es.
    body_inv tops ctx cenv cx /\
    expr_body_pre cenv cx env (TopLevelName ann nsid) es ==>
    toplevel_vv_nil (DF,lo,d,ctx,func) cenv cx ty (TopLevelName ann nsid) es
Proof
  rpt gen_tac >> PairCases_on `nsid` >> strip_tac >>
  Cases_on `get_module_code cx nsid0`
  >- (fs[toplevel_vv_nil_def] >>
      metis_tac[missing_module_not_gas_admissible]) >>
  rename1 `get_module_code cx nsid0 = SOME ts` >>
  Cases_on `find_var_decl_by_name nsid1 ts`
  >- (irule toplevel_immutable_vv_nil_from_contract >>
      conj_tac
      >- (rpt gen_tac >> strip_tac >>
          gvs[] >> metis_tac[INST_TYPE [alpha |-> ``:256``] toplevel_ctor_source_contract]) >>
      metis_tac[]) >>
  PairCases_on `x` >> Cases_on `x0` >>
  all_tac >~ [`find_var_decl_by_name _ _ = SOME (StorageVarDecl _ _,_)`]
  >- (irule toplevel_storage_vv_nil >> fs[expr_body_pre_def] >> metis_tac[]) >>
  fs[expr_body_pre_def, expr_sim_pre_def, expr_sim_inv_def] >>
  metis_tac[TopLevelName_Type_HashMapVarDecl_impossible]
QED

Theorem toplevel_name_vv_full:
  !DF lo d PG tops ctx shadow_ctx func shadow_func cenv cx env ty ann nsid es.
    body_inv tops ctx cenv cx /\
    expr_body_pre cenv cx env (TopLevelName ann nsid) es ==>
    expr_vv_sim_full (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
      cenv cx ty (TopLevelName ann nsid) es
Proof
  metis_tac[toplevel_vv_nil_full, toplevel_name_vv_nil]
QED
