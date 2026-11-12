Theory bodyPtrStructLitOwnershipSelectedPackages
Ancestors bodyPtrStructLitOwnershipPackages loweringShapeProps
  compileVyper list pair

Theorem structlit_selected_internal_packages:
  !tops exts ints fb ctor tr nk mode ilen target.
  supported_program tops /\ classify_functions tops = (exts,ints,fb,ctor) ==>
  EVERY (\(lbl,ce,params,rb,nr,key,t,view,c,sz,body,rt).
    internal_fn_shape_ok (lbl,ce,params,rb,nr,key,t,view,c,sz,body,rt) /\
    internal_label_ok lbl)
    (MAP (set_internal_package_target target o
      package_internal_fn tops tr nk mode ilen) ints)
Proof
  rpt gen_tac >> strip_tac >> simp[EVERY_MAP, EVERY_MEM] >>
  gen_tac >> strip_tac >>
  `internal_fn_shape_ok (set_internal_package_target target
     (package_internal_fn tops tr nk mode ilen x))` by
    (irule structlit_internal_package_shape >> gvs[]) >>
  `internal_label_ok (FST (set_internal_package_target target
     (package_internal_fn tops tr nk mode ilen x)))` by
    simp[structlit_internal_package_label] >>
  Cases_on `set_internal_package_target target
    (package_internal_fn tops tr nk mode ilen x)` >> PairCases_on `r` >> gvs[]
QED

Theorem structlit_selected_external_packages:
  !tops exts ints fb ctor tr nk target.
  supported_program tops /\ classify_functions tops = (exts,ints,fb,ctor) ==>
  EVERY (\(lbl,ce,args,cds,pay,nr,key,t,view,body,rt).
    external_fn_shape_ok (lbl,ce,args,cds,pay,nr,key,t,view,body,rt) /\
    ce.ce_alloca_locals)
    (MAP (set_external_package_target target o
      package_external_fn tops tr nk) exts)
Proof
  rpt gen_tac >> strip_tac >> simp[EVERY_MAP, EVERY_MEM] >>
  gen_tac >> strip_tac >>
  `external_fn_shape_ok (set_external_package_target target
    (package_external_fn tops tr nk x))` by
    (irule package_external_fn_shape_ok >>
     simp[] >> metis_tac[supported_program_runtime_bodies_shape_ok]) >>
  `(\(lbl,ce,args,cds,pay,nr,key,t,view,body,rt). ce.ce_alloca_locals)
     (set_external_package_target target (package_external_fn tops tr nk x))`
    by (irule structlit_external_package_alloca_mode) >>
  Cases_on `set_external_package_target target
    (package_external_fn tops tr nk x)` >> PairCases_on `r` >> gvs[]
QED

Theorem structlit_selected_fallback_package:
  !tops tr nk target.
  supported_program tops ==>
  fallback_shape_ok (set_fallback_package_target target
    (package_fallback_fn tops tr nk (FST (SND (SND (classify_functions tops)))))) /\
  (case set_fallback_package_target target
    (package_fallback_fn tops tr nk (FST (SND (SND (classify_functions tops))))) of
    NONE => T | SOME (ce,pay,nr,key,trans,view,stmts,rt) => ce.ce_alloca_locals)
Proof
  rpt gen_tac >> disch_tac >> conj_tac
  >- (irule package_fallback_fn_shape_ok >>
      metis_tac[supported_program_runtime_bodies_shape_ok]) >>
  irule structlit_fallback_package_alloca_mode
QED

Theorem structlit_selected_constructor_package:
  !tops tr nk target mut nr rr name args defaults ret fbody.
  supported_program tops /\
  SND (SND (SND (classify_functions tops))) =
    SOME (mut,nr,rr,name,args,defaults,ret,fbody) ==>
  (\(ce,a,p,n,k,t,stmts,r).
    cenv_static_ok ce /\ ce.ce_return_pc = NONE /\ ce.ce_alloca_locals /\
    ~supported_stmts_expr_exists expr_shape_root stmts)
    (set_constructor_package_target target
      (package_constructor tops tr nk (mut,nr,rr,name,args,defaults,ret,fbody)))
Proof
  rpt gen_tac >> strip_tac >>
  `(\(ce,a,p,n,k,t,stmts,r).
    cenv_static_ok ce /\ ce.ce_return_pc = NONE /\ ce.ce_alloca_locals)
    (set_constructor_package_target target
      (package_constructor tops tr nk (mut,nr,rr,name,args,defaults,ret,fbody)))`
    by (irule structlit_constructor_package_environment) >>
  drule_all structlit_constructor_package_body >>
  disch_then (qspecl_then [`tr`, `nk`, `target`] mp_tac) >>
  Cases_on `set_constructor_package_target target
    (package_constructor tops tr nk (mut,nr,rr,name,args,defaults,ret,fbody))` >>
  PairCases_on `r` >> gvs[]
QED

Theorem structlit_selected_deploy_packages:
  !tops exts ints fb ctor tr nk target ilen.
  supported_program tops /\ classify_functions tops = (exts,ints,fb,ctor) ==>
  (case ctor of NONE => T
   | SOME cf =>
     (\(ce,args,pay,nr,key,t,stmts,rt).
       cenv_static_ok ce /\ ce.ce_return_pc = NONE /\ ce.ce_alloca_locals /\
       ~supported_stmts_expr_exists expr_shape_root stmts)
       (set_constructor_package_target target (package_constructor tops tr nk cf)) /\
     EVERY (\(lbl,env,params,rb,n,k,t,view,c,sz,b,r).
       internal_fn_shape_ok (lbl,env,params,rb,n,k,t,view,c,sz,b,r) /\
       internal_label_ok lbl)
       (MAP (set_internal_package_target target o
         package_internal_fn tops tr nk T ilen) ints))
Proof
  rpt gen_tac >> strip_tac >> Cases_on `ctor` >> simp[] >>
  conj_tac
  >- (PairCases_on `x` >> irule structlit_selected_constructor_package >> gvs[]) >>
  irule structlit_selected_internal_packages >> gvs[]
QED

Theorem structlit_selected_runtime_packages:
  !tops exts ints fb ctor tr nk target.
  supported_program tops /\ classify_functions tops = (exts,ints,fb,ctor) ==>
  EVERY (\(sel,lbl,z). isPREFIX "fn_" lbl) (build_selectors (type_env tops) exts) /\
  EVERY (\(lbl,ce,args,cds,pay,nr,key,t,view,body,rt).
    external_fn_shape_ok (lbl,ce,args,cds,pay,nr,key,t,view,body,rt) /\ ce.ce_alloca_locals)
    (MAP (set_external_package_target target o package_external_fn tops tr nk) exts) /\
  EVERY (\(lbl,ce,params,rb,nr,key,t,view,c,sz,body,rt).
    internal_fn_shape_ok (lbl,ce,params,rb,nr,key,t,view,c,sz,body,rt) /\ internal_label_ok lbl)
    (MAP (set_internal_package_target target o package_internal_fn tops tr nk F 0) ints) /\
  fallback_shape_ok (set_fallback_package_target target (package_fallback_fn tops tr nk fb)) /\
  (case set_fallback_package_target target (package_fallback_fn tops tr nk fb) of
    NONE => T | SOME (ce,pay,nr,key,trans,view,stmts,rt) => ce.ce_alloca_locals)
Proof
  rpt gen_tac >> strip_tac >>
  conj_tac >- simp[build_selectors_fn_labels] >>
  conj_tac >- (irule structlit_selected_external_packages >> gvs[]) >>
  conj_tac >- (irule structlit_selected_internal_packages >> gvs[]) >>
  `fb = FST (SND (SND (classify_functions tops)))` by simp[] >>
  pop_assum SUBST_ALL_TAC >> irule structlit_selected_fallback_package >> simp[]
QED
