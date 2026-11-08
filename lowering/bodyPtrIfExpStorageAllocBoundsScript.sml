Theory bodyPtrIfExpStorageAllocBounds
Ancestors
  bodyPtrIfExpAllocCompiler bodyPtrIfExpMaterializeFrame
  bodyPtrIfExpStorageFrame bodyPtrIfExpAllocGhost bodyPtrIfExpAllocSeparation
  exprSimDefs loweringPosts compileEnv venomState words finite_map

Theorem ifexp_copy_allocation_bounds:
  stmt_state_rel ctx fn ce cx es s0 /\
  vv_post ctx fn ce cx e es sa sb s0 ee tv vv sArm /\
  local_ptrs_reserved ce sa /\ MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  fn_inst_ids_distinct fn /\ sa.cs_next_var <= sb.cs_next_var /\
  sa.cs_next_id <= sb.cs_next_id /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  compile_alloc_buffer capacity sb = (buf,cs) /\ fn_has_code sb cs fn /\
  capacity < dimword(:256) /\ b = buffer_allocation_base sArm sb.cs_next_id ==>
  b+capacity < dimword(:256) /\
  (!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\
    aid < sa.cs_next_id ==> off+sz <= b \/ b+capacity <= off) /\
  (!name p sz. local_region ce es.scopes s0 name p sz ==>
    p+sz <= b \/ b+capacity <= p) /\
  (!name entry p sz w. lookup_scopes name ee.scopes = SOME entry /\
    FLOOKUP ce.ce_vars name = SOME (PtrVar (Var p) sz) /\
    lookup_var p sArm = SOME w ==>
    val_wf entry.type entry.value /\
    (w2n w+type_memory_size entry.type <= b \/ b+capacity <= w2n w))
Proof
  strip_tac >>
  `stmt_state_rel ctx fn ce cx ee sArm` by gvs[vv_post_def] >>
  drule_all compile_alloc_buffer_raw_step >> strip_tac >>
  drule_all compile_alloc_buffer_frame_separation >>
  disch_then (qspec_then `ee.scopes` strip_assume_tac) >>
  conj_tac >- metis_tac[ifexp_alloca_base_bound] >>
  conj_tac >- (rpt strip_tac >> metis_tac[ifexp_alloca_original_site_separate]) >>
  conj_asm1_tac
  >- (rpt strip_tac >> metis_tac[ifexp_alloca_original_local_separate]) >>
  metis_tac[REWRITE_RULE [arithmeticTheory.ADD_CLAUSES,
    arithmeticTheory.LESS_EQ_REFL] (Q.INST [`j` |-> `0`, `n` |-> `capacity`]
    ifexp_interior_live_local_bounds)]
QED

(* Only reservation and the compiler cutoff are needed for local lookups;
   the generic alloca lookup theorem owns the runtime update reasoning. *)
Theorem ifexp_copy_allocation_local_lookups:
  local_ptrs_reserved ce sa /\ sa.cs_next_var <= sb.cs_next_var /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  compile_alloc_buffer capacity sb = (buf,cs) /\ buf.buf_operand = Var out /\
  step_inst_base (mk_inst sb.cs_next_id ALLOCA [Lit (n2w capacity)] [out]) sArm = OK u ==>
  !name p sz idx. FLOOKUP ce.ce_vars name = SOME (PtrVar (Var p) sz) ==>
    lookup_var p u = lookup_var p sArm /\
    lookup_var p (u with vs_inst_idx := idx) = lookup_var p sArm
Proof
  strip_tac >>
  drule_all compile_alloc_buffer_frame_separation >>
  disch_then (qspec_then `[]` strip_assume_tac) >>
  rpt gen_tac >> strip_tac >>
  `not_fresh_at sa p` by
    (gvs[local_ptrs_reserved_def] >> metis_tac[]) >>
  `p <> out` by metis_tac[] >>
  drule_all alloca_step_lookup_preserved >> simp[lookup_var_def]
QED
