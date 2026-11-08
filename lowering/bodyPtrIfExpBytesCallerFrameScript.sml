Theory bodyPtrIfExpBytesCallerFrame
Ancestors
  bodyPtrIfExpAllocSeparation bodyPtrIfExpAllocCompiler
  compileEnv loweringPosts venomState venomInst finite_map loweringHalt words
  exprLoweringProps exprSimProps exprSimDefs bodyPtrIfExpBytesFrame
  stmtFragPtr

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

Theorem ifexp_bytes_live_local_frame_bounds:
  stmt_state_rel ctx fn ce cx es s0 /\
  vv_post ctx fn ce cx e es sa sc s0 ee raw vv t /\
  local_ptrs_reserved ce sa /\ MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  n <= capacity /\
  (!name p sz. local_region ce es.scopes s0 name p sz ==>
    p+sz <= b \/ b+capacity <= p) ==>
  !name entry p sz w.
    lookup_scopes name ee.scopes = SOME entry /\
    FLOOKUP ce.ce_vars name = SOME (PtrVar (Var p) sz) /\
    lookup_var p t = SOME w ==>
    val_wf entry.type entry.value /\
    (w2n w + type_memory_size entry.type <= b \/ b+n <= w2n w)
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  `local_ptrs_rel fn ce ee.scopes t /\ local_ptrs_rel fn ce es.scopes s0` by
    gvs[vv_post_def, stmt_state_rel_def, state_rel_def] >>
  `type_memory_size entry.type <= sz /\ val_wf entry.type entry.value` by
    (qpat_x_assum `local_ptrs_rel _ _ ee.scopes t` mp_tac >>
     simp[local_ptrs_rel_def] >> strip_tac >>
     first_x_assum (qspecl_then [`name`, `entry`, `p`, `sz`] mp_tac) >>
     simp[] >> strip_tac >> gvs[]) >>
  `local_region ce ee.scopes t name (w2n w) sz` by
    (simp[local_region_def] >> metis_tac[]) >>
  `local_region ce es.scopes s0 name (w2n w) sz` by
    (irule local_region_frame >> conj_tac
     >- (qexists_tac `fn` >> simp[]) >>
     qexistsl_tac [`sa`, `ee.scopes`, `t`] >> simp[] >>
     gvs[vv_post_def]) >>
  first_x_assum drule >> strip_tac >> simp[] >> decide_tac
QED

Theorem ifexp_bytes_caller_ghost_inv:
  stmt_state_rel ctx fn ce cx es s0 /\
  vv_post ctx fn ce cx e es sa sc s0 ee raw vv t /\
  local_ptrs_reserved ce sa /\ MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sc.cs_next_var /\ n <= capacity /\
  (!name p sz. local_region ce es.scopes s0 name p sz ==>
    p+sz <= b \/ b+capacity <= p) /\
  ghost_inv d ce cx ee G tn t /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x. not_fresh_at sc x ==>
    FLOOKUP Gf x = FLOOKUP G x /\ op_taint tnf (Var x) = op_taint tn (Var x) /\
    lookup_var x sf = lookup_var x t) /\
  (!ft fv p. val_wf ft fv /\ (p+type_memory_size ft <= b \/ b+n <= p) /\
    (!m. mem_agree_outside tn.t_mem t.vs_memory m ==> val_in_memory ft fv p m) ==>
    !m. mem_agree_outside tnf.t_mem sf.vs_memory m ==> val_in_memory ft fv p m) /\
  stor_taint_ok cx tnf sf ==>
  ghost_inv d ce cx ee Gf tnf sf
Proof
  strip_tac >>
  drule ifexp_bytes_live_local_frame_bounds >>
  disch_then drule >> simp[] >>
  disch_then (qspecl_then [`n`, `capacity`, `b`] mp_tac) >>
  simp[] >> strip_tac >>
  `local_ptrs_reserved ce sc` by metis_tac[local_ptrs_reserved_next_var] >>
  `(!name entry p sz. lookup_scopes name ee.scopes = SOME entry /\
    FLOOKUP ce.ce_vars name = SOME (PtrVar (Var p) sz) ==> not_fresh_at sc p)` by
    (gvs[local_ptrs_reserved_def] >> metis_tac[]) >>
  `(!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sc x) /\
   (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sc x)` by
    metis_tac[not_fresh_at_mono] >>
  irule bytes_writer_ghost_inv >> conj_tac >- simp[] >>
  goal_assum (drule_at (Pat `ghost_inv _ _ _ _ _ _ _`)) >>
  qexistsl_tac [`b`, `n`, `sc`] >> simp[] >> metis_tac[]
QED

Theorem ifexp_bytes_caller_ghost_kept:
  ghost_kept ce es sa G0 tn0 s0 G tn /\ sa.cs_next_var <= sc.cs_next_var /\
  n <= capacity /\
  (!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id ==>
    off+sz <= b \/ b+capacity <= off) /\
  (!name p sz. local_region ce es.scopes s0 name p sz ==>
    p+sz <= b \/ b+capacity <= p) /\
  (!x. not_fresh_at sc x ==>
    FLOOKUP Gf x = FLOOKUP G x /\ op_taint tnf (Var x) = op_taint tn (Var x)) /\
  (!i. ~(b <= i /\ i < b+n) ==> (i IN tnf.t_mem <=> i IN tn.t_mem)) ==>
  ghost_kept ce es sa G0 tn0 s0 Gf tnf
Proof
  strip_tac >>
  `!x. not_fresh_at sa x ==>
    FLOOKUP Gf x = FLOOKUP G x /\ op_taint tnf (Var x) = op_taint tn (Var x)` by
    metis_tac[not_fresh_at_mono] >>
  `!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id ==>
    off+sz <= b \/ b+n <= off` by
    (rpt strip_tac >> first_x_assum drule >> simp[] >> decide_tac) >>
  `!name p sz. local_region ce es.scopes s0 name p sz ==>
    p+sz <= b \/ b+n <= p` by
    (rpt strip_tac >> first_x_assum drule >> strip_tac >> decide_tac) >>
  irule bytes_writer_ghost_kept >>
  goal_assum (drule_at (Pat `ghost_kept _ _ _ _ _ _ _ _`)) >>
  qexistsl_tac [`b`, `n`] >> simp[] >> conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!name p sz. local_region _ _ _ _ _ _ ==> p+sz <= b \/ b+n <= p`
        drule >> decide_tac) >>
  rpt strip_tac >>
  qpat_x_assum `!aid off sz. _ /\ _ ==> off+sz <= b \/ b+n <= off` drule_all >>
  simp[]
QED
