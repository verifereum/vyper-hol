Theory bodyPtrPopRuntimeListsBoundary
Ancestors bodyPtrPopRuntimeBoundary bodyPtrPopExternalBodyBoundary
  bodyPtrPopEntryChecksBoundary bodyPtrPopLinearBoundary bodyPtrPopCompilerBoundary
  bodyPtrPopMaterialization moduleLowering compileEnv list

Theorem pop_external_fn_bodies_boundary:
  !fns sa r sb.
    EVERY (\(lbl,ce,args,mincds,pay,nr,key,tr,view,stmts,ret).
      supported_stmts tops bindings stmts) fns /\ pop_comp_boundary sa /\
    compile_external_fn_bodies fns sa = (r,sb) ==> pop_comp_boundary sb
Proof
  Induct >> simp[compile_external_fn_bodies_def, comp_return_def] >>
  rpt gen_tac >> PairCases_on `h` >>
  simp[compile_external_fn_bodies_def, comp_ignore_bind_def] >> strip_tac >>
  rpt (dxrule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
       disch_then irule >> simp[] >> conj_tac >> rpt gen_tac >> strip_tac) >>
  FIRST_PROVE
    [first_x_assum drule_all >> simp[],
     drule_all pop_comp_boundary_new_block >> simp[],
     drule_all pop_compile_entry_checks_boundary >> simp[],
     drule_all pop_external_function_body_boundary >> simp[]]
QED

Theorem pop_internal_fn_bodies_boundary:
  !fns sa r sb.
    EVERY (\(lbl,ce,params,buf,nr,key,tr,view,ctor,imm,stmts,ret).
      supported_stmts tops bindings stmts) fns /\ pop_comp_boundary sa /\
    compile_internal_fn_bodies fns sa = (r,sb) ==> pop_comp_boundary sb
Proof
  Induct >> simp[compile_internal_fn_bodies_def, comp_return_def] >>
  rpt gen_tac >> PairCases_on `h` >>
  simp[compile_internal_fn_bodies_def, comp_ignore_bind_def] >> strip_tac >>
  rpt (dxrule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
       disch_then irule >> simp[] >> conj_tac >> rpt gen_tac >> strip_tac) >>
  FIRST_PROVE
    [first_x_assum drule_all >> simp[],
     drule_all pop_comp_boundary_new_block >> simp[],
     drule_all pop_internal_function_boundary >> simp[]]
QED

Theorem pop_generate_runtime_linear_boundary:
  EVERY (\(lbl,ce,args,mincds,pay,nr,key,tr,view,stmts,ret).
    supported_stmts tops bindings stmts) exts /\
  EVERY (\(lbl,ce,params,buf,nr,key,tr,view,ctor,imm,stmts,ret).
    supported_stmts tops bindings stmts) ints /\
  (case fb of NONE => T | SOME (ce,pay,nr,key,tr,view,stmts,ret) =>
    supported_stmts tops bindings stmts) /\ pop_comp_boundary sa /\
  compile_generate_runtime sels exts ints fb Linear buckets meta dense info sa = (r,sb) ==>
  pop_comp_boundary sb
Proof
  Cases_on `fb` >> TRY (rename1 `SOME f` >> PairCases_on `f`) >>
  simp[compile_generate_runtime_def, comp_ignore_bind_def] >> rpt strip_tac >>
  rpt (dxrule_at (Pat `comp_bind _ _ _ = _`) pop_comp_boundary_bind >>
       disch_then irule >> simp[] >> conj_tac >> rpt gen_tac >> strip_tac) >>
  FIRST_PROVE
    [drule_all pop_fresh_label_boundary >> simp[],
     drule_all pop_selector_dispatch_linear_boundary >> simp[],
     drule_all pop_external_fn_bodies_boundary >> simp[],
     drule_all pop_internal_fn_bodies_boundary >> simp[],
     drule_all pop_fallback_body_boundary >> simp[],
     drule_all pop_comp_boundary_new_block >> simp[],
     drule_at (Pat `emit_inst _ _ _ _ = _`) pop_emit_inst_boundary >> simp[],
     gvs[comp_return_def]]
QED
