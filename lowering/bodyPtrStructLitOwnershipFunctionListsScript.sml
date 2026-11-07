Theory bodyPtrStructLitOwnershipFunctionLists
Ancestors
  bodyPtrStructLitOwnershipInternalFunction bodyPtrStructLitOwnershipDispatch
  bodyPtrStructLitOwnershipShape bodyPtrStructLitOwnershipSteps
  bodyPtrStructLitOwnershipFreshness bodyPtrStructLitOwnershipGuarded
  bodyPtrStructLitOwnershipFrame loweringShapeProps loweringShapeDefs
  moduleLowering compileEnv context

Theorem alloc_run_new_block_exact:
  alloc_run shape_state (new_block lbl)
    (\u s. shape_state s /\ s.cs_current_bb = lbl /\ fresh_outputs s)
Proof
  rw[alloc_run_def] >>
  drule_all shape_state_new_block >> strip_tac >>
  `fresh_outputs st` by metis_tac[shape_base_fresh_outputs, shape_state_def] >>
  mp_tac (Q.INST [`lbl` |-> `lbl`] alloc_run_new_block_fresh) >>
  simp[alloc_run_def] >> disch_then drule_all >>
  gvs[new_block_def]
QED

Theorem alloc_run_external_function_shape_fresh:
  !ce args nr key tr view stmts rt.
  cenv_static_ok ce /\ ce.ce_return_pc = NONE /\ ce.ce_alloca_locals /\
  ~supported_stmts_expr_exists expr_shape_root stmts ==>
  alloc_run shape_state
    (compile_external_function_body ce args nr key tr view stmts rt)
    (\u s. shape_state s /\ fresh_outputs s)
Proof
  rpt strip_tac >> irule alloc_run_conseq >>
  irule_at Any alloc_run_shape_join >>
  irule_at Any compile_external_function_body_shape >> simp[] >>
  irule_at Any alloc_run_compile_external_function_body >> simp[] >>
  simp[cenv_static_ok_shape_ok]
QED

Theorem alloc_run_internal_function_shape_fresh:
  !ce params rb nr key tr view ctor ilen stmts rt.
  cenv_static_ok ce /\ ~supported_stmts_expr_exists expr_shape_root stmts ==>
  alloc_run (\s. shape_state s /\ internal_label_ok s.cs_current_bb)
    (compile_internal_function ce params rb nr key tr view ctor ilen stmts rt)
    (\u s. shape_state s /\ fresh_outputs s)
Proof
  rpt strip_tac >> irule alloc_run_conseq >>
  irule_at Any alloc_run_shape_join >>
  irule_at Any compile_internal_function_shape >> simp[] >>
  irule_at Any alloc_run_compile_internal_function >> simp[]
QED

Theorem alloc_run_compile_external_fn_bodies:
  !exts.
  EVERY (\(lbl,ce,args,min_cds,pay,nr,key,tr,view,stmts,rt).
    external_fn_shape_ok (lbl,ce,args,min_cds,pay,nr,key,tr,view,stmts,rt) /\
    ce.ce_alloca_locals) exts ==>
  alloc_run shape_state (compile_external_fn_bodies exts)
    (\u s. shape_state s /\ fresh_outputs s)
Proof
  Induct >> simp[listTheory.EVERY_DEF]
  >- simp[compile_external_fn_bodies_def, comp_return_def, alloc_run_def,
          alloc_frame_refl, shape_state_def, shape_base_fresh_outputs] >>
  gen_tac >> PairCases_on `h` >>
  simp[external_fn_shape_ok_def] >> strip_tac >>
  simp[Once compile_external_fn_bodies_def, comp_ignore_bind_def] >>
  irule alloc_run_bind >> qexists `\u s. shape_state s` >> conj_tac
  >- (gen_tac >> simp[] >> irule alloc_run_bind >>
      qexists `\u s. shape_state s` >> conj_tac
      >- (gen_tac >> simp[] >> irule alloc_run_bind >>
          qexists `\u s. shape_state s /\ fresh_outputs s` >> conj_tac
          >- (gen_tac >> simp[SF ETA_ss] >> irule alloc_run_conseq >>
              first_x_assum (irule_at Any) >> simp[external_fn_shape_ok_def, internal_fn_shape_ok_def]) >>
          simp[SF ETA_ss] >> irule alloc_run_external_function_shape_fresh >> simp[]) >>
      irule alloc_run_conseq >> irule_at Any alloc_run_compile_entry_checks_frame >>
      qexists `\s. T` >> simp[shape_stable_def]) >>
  irule alloc_run_conseq >> irule_at Any alloc_run_new_block_exact >> simp[]
QED

Theorem alloc_run_compile_internal_fn_bodies:
  !ints.
  EVERY (\(lbl,ce,params,rb,nr,key,tr,view,ctor,ilen,stmts,rt).
    internal_fn_shape_ok (lbl,ce,params,rb,nr,key,tr,view,ctor,ilen,stmts,rt) /\
    internal_label_ok lbl) ints ==>
  alloc_run shape_state (compile_internal_fn_bodies ints)
    (\u s. shape_state s /\ fresh_outputs s)
Proof
  Induct >> simp[listTheory.EVERY_DEF]
  >- simp[compile_internal_fn_bodies_def, comp_return_def, alloc_run_def,
          alloc_frame_refl, shape_state_def, shape_base_fresh_outputs] >>
  gen_tac >> PairCases_on `h` >>
  simp[internal_fn_shape_ok_def] >> strip_tac >>
  simp[Once compile_internal_fn_bodies_def, comp_ignore_bind_def] >>
  irule alloc_run_bind >>
  qexists `\u s. shape_state s /\ internal_label_ok s.cs_current_bb` >> conj_tac
  >- (gen_tac >> simp[] >> irule alloc_run_bind >>
      qexists `\u s. shape_state s /\ fresh_outputs s` >> conj_tac
      >- (gen_tac >> simp[SF ETA_ss] >> irule alloc_run_conseq >>
          first_x_assum (irule_at Any) >> simp[external_fn_shape_ok_def, internal_fn_shape_ok_def]) >>
      irule alloc_run_internal_function_shape_fresh >> simp[]) >>
  irule alloc_run_conseq >> irule_at Any alloc_run_new_block_exact >> simp[]
QED
