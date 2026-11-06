Theory bodyPtrIfExpBytesCallerFrame
Ancestors
  bodyPtrIfExpAllocSeparation bodyPtrIfExpAllocCompiler
  compileEnv loweringPosts venomState venomInst finite_map loweringHalt words
  exprLoweringProps

Theorem ifexp_alloca_live_local_write_bounds:
  stmt_state_rel ctx fn ce cx es s /\ fn_inst_ids_distinct fn /\
  MEM (mk_inst id ALLOCA [Lit (n2w capacity)] [out]) (fn_insts fn) /\
  not_local_ptr ce es.scopes out /\ capacity < dimword(:256) /\ n <= capacity /\
  lookup_scopes name es.scopes = SOME entry /\
  FLOOKUP ce.ce_vars name = SOME (PtrVar (Var p) sz) /\ lookup_var p s = SOME w ==>
  val_wf entry.type entry.value /\
  (w2n w + type_memory_size entry.type <= buffer_allocation_base s id \/
   buffer_allocation_base s id+n <= w2n w)
Proof
  strip_tac >>
  `local_ptrs_rel fn ce es.scopes s` by gvs[stmt_state_rel_def, state_rel_def] >>
  `type_memory_size entry.type <= sz /\ val_wf entry.type entry.value` by
    (qpat_x_assum `local_ptrs_rel _ _ _ _` mp_tac >>
     simp[local_ptrs_rel_def] >> strip_tac >>
     first_x_assum (qspecl_then [`name`, `entry`, `p`, `sz`] mp_tac) >>
     simp[] >> strip_tac >> gvs[]) >>
  `local_region ce es.scopes s name (w2n w) sz` by
    (simp[local_region_def] >> metis_tac[]) >>
  drule_all ifexp_alloca_local_separate >> strip_tac >> simp[] >> decide_tac
QED

Theorem ifexp_allocated_address_write_bounds:
  lookup_var out t = SOME (n2w addr) /\ addr+capacity < dimword(:256) /\ n <= capacity ==>
  lookup_var out t = SOME (n2w addr) /\
  w2n (n2w addr : bytes32) = addr /\ addr+n < dimword(:256)
Proof
  strip_tac >> `addr < dimword(:256)` by decide_tac >> simp[]
QED
