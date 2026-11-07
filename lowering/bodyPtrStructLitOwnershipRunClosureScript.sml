Theory bodyPtrStructLitOwnershipRunClosure
Ancestors bodyPtrStructLitOwnershipInitial bodyPtrStructLitOwnershipExtraction
  bodyPtrStructLitOwnershipRuntime bodyPtrStructLitOwnershipDeploy
  bodyPtrStructLitOwnershipSteps loweringShapeProps vyperCompiler
  loweringShapeDefs venomInst

Theorem structlit_alloc_run_initial:
  alloc_run shape_state f Q /\ f (initial_compile_state entry) = (v,st') ==>
  alloc_writers_unique st'
Proof
  strip_tac >> fs[alloc_run_def] >>
  `shape_state (initial_compile_state entry)` by
    simp[shape_state_initial_compile_state] >>
  `alloc_writers_unique (initial_compile_state entry)` by
    simp[initial_compile_state_alloc_writers_unique] >>
  metis_tac[]
QED

Theorem structlit_run_lowering_ownership:
  EVERY (\(sel,lbl,z). isPREFIX "fn_" lbl) sels /\
  EVERY (\(lbl,ce,args,cds,pay,nr,key,t,view,stmts,rt).
    external_fn_shape_ok (lbl,ce,args,cds,pay,nr,key,t,view,stmts,rt) /\ ce.ce_alloca_locals) exts /\
  EVERY (\(lbl,ce,params,rb,nr,key,t,view,c,sz,stmts,rt).
    internal_fn_shape_ok (lbl,ce,params,rb,nr,key,t,view,c,sz,stmts,rt) /\ internal_label_ok lbl) ints /\
  fallback_shape_ok fb /\
  (case fb of NONE => T | SOME (ce,pay,nr,key,trans,view,stmts,rt) => ce.ce_alloca_locals) /\
  run_lowering sels exts ints fb rp buckets metadata dense info entry = SOME u /\
  lookup_function name u.cu_context.ctx_functions = SOME func ==>
  !i j x. MEM i (fn_insts func) /\ MEM j (fn_insts func) /\
    i.inst_opcode = ALLOCA /\ MEM x i.inst_outputs /\ MEM x j.inst_outputs ==> i = j
Proof
  strip_tac >>
  `alloc_run shape_state
    (compile_generate_runtime sels exts ints fb Linear buckets metadata dense info)
    (\u s. shape_state s /\ fresh_outputs s)` by
    (irule alloc_run_generate_runtime_linear >> simp[]) >>
  qpat_x_assum `run_lowering _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[run_lowering_def, lowering_policy_ok_def, AllCaseEqs()] >>
  strip_tac >> gvs[] >>
  Cases_on `compile_generate_runtime sels exts ints fb Linear buckets metadata dense info
    (initial_compile_state entry)` >>
  rename1 `_ = (v,st1)` >> Cases_on `v` >>
  gvs[AllCaseEqs()] >>
  `alloc_writers_unique st1` by
    (drule structlit_alloc_run_initial >> disch_then irule >>
     qexists `entry` >> simp[]) >>
  metis_tac[extract_context_with_internals_alloc_writers_unique]
QED

Theorem structlit_run_deploy_lowering_ownership:
  (has_ctor ==> cenv_static_ok ce /\ ce.ce_return_pc = NONE /\ ce.ce_alloca_locals /\
    ~supported_stmts_expr_exists expr_shape_root stmts /\
    EVERY (\(lbl,env,params,rb,n,k,t,view,c,sz,b,r).
      internal_fn_shape_ok (lbl,env,params,rb,n,k,t,view,c,sz,b,r) /\ internal_label_ok lbl) ints) /\
  run_deploy_lowering has_ctor rp bytes ilen args data_size ints ce stmts pay nr key tr entry = SOME u /\
  lookup_function name u.cu_context.ctx_functions = SOME func ==>
  !i j x. MEM i (fn_insts func) /\ MEM j (fn_insts func) /\
    i.inst_opcode = ALLOCA /\ MEM x i.inst_outputs /\ MEM x j.inst_outputs ==> i = j
Proof
  strip_tac >>
  `alloc_run shape_state
    (compile_generate_deploy has_ctor (LENGTH bytes) ilen args data_size ints ce stmts pay nr key tr)
    (\u s. shape_state s /\ fresh_outputs s)` by
    (irule alloc_run_generate_deploy >> simp[]) >>
  qpat_x_assum `run_deploy_lowering _ _ _ _ _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  simp[run_deploy_lowering_def, AllCaseEqs()] >> strip_tac >>
  Cases_on `compile_generate_deploy has_ctor (LENGTH bytes) ilen args data_size ints ce stmts pay nr key tr
    (initial_compile_state entry)` >>
  rename1 `_ = (v,st1)` >> Cases_on `v` >>
  gvs[AllCaseEqs(), install_immutable_reservation_functions] >>
  `alloc_writers_unique st1` by
    (drule structlit_alloc_run_initial >> disch_then irule >>
     qexists `entry` >> simp[]) >>
  metis_tac[extract_context_with_internals_alloc_writers_unique]
QED
