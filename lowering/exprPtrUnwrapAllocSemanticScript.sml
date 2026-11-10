(* Semantic reconstruction uses the concrete allocation endpoint, not a new run. *)
Theory exprPtrUnwrapAllocSemantic
Ancestors
  exprPtrUnwrapAllocEntry exprPtrUnwrapAllocation exprSimAlloc loweringSlice exprLoweringProps arithmetic
  bufferAllocationExecution loweringPosts compileEnv loweringStateRelDefs context venomState venomInst
  venomExecSemantics words finite_map

Theorem unwrap_alloc_semantic_state:
  compile_alloc_buffer nb sa = (buf,sm) /\ fn_has_code sa sm func /\
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ nb < dimword (:256) /\
  buf.buf_operand = Var root /\
  step_inst_base (mk_inst sa.cs_next_id ALLOCA [Lit (n2w nb)] [root]) s = OK u ==>
  stmt_state_rel ctx func cenv cx es (u with vs_inst_idx := k) /\
  ?w. lookup_var root u = SOME w /\
    FLOOKUP u.vs_allocas sa.cs_next_id = SOME (w2n w,nb)
Proof
  strip_tac >> drule unwrap_alloc_generated_code >> strip_tac >>
  `root = STRING #"%" (toString sa.cs_next_var)` by fs[] >>
  `MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w nb)] [root]) (fn_insts func)` by
    metis_tac[buffer_alloc_code] >>
  `not_local_ptr cenv es.scopes root` by
    (simp[] >> irule local_ptrs_reserved_fresh >> qexists_tac `sa` >> simp[]) >>
  `exec_alloca (mk_inst sa.cs_next_id ALLOCA [Lit (n2w nb)] [root]) s (n2w nb : bytes32) = OK u` by
    (qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
     simp[step_inst_base_opcode_eqs, mk_inst_def]) >>
  drule_at (Pat `exec_alloca _ _ _ = _`) stmt_state_rel_exec_alloca >>
  gvs[mk_inst_def] >> disch_then drule_all >>
  simp[stmt_state_rel_inst_idx, w2n_n2w, LESS_MOD]
QED

Theorem unwrap_alloc_fields_old:
  u = update_var root d (buffer_allocation_fields s aid nb) ==>
  u.vs_memory = s.vs_memory /\
  (!x. x <> root ==> lookup_var x u = lookup_var x s) /\
  (!id entry. FLOOKUP s.vs_allocas id = SOME entry ==>
     FLOOKUP u.vs_allocas id = SOME entry)
Proof
  strip_tac >> Cases_on `FLOOKUP s.vs_allocas aid` >>
  gvs[buffer_allocation_fields_def, update_var_def, lookup_var_def,
      FLOOKUP_UPDATE] >> rpt strip_tac >> Cases_on `id = aid` >> gvs[]
QED

Theorem unwrap_alloc_old_disjoint:
  alloca_inv u /\
  FLOOKUP u.vs_allocas aid = SOME (dst,nb) /\
  (!id entry. FLOOKUP s.vs_allocas id = SOME entry ==>
     FLOOKUP u.vs_allocas id = SOME entry) ==>
  !id b len. id < aid /\ FLOOKUP s.vs_allocas id = SOME (b,len) ==>
    regions_disjoint dst nb b len
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  `FLOOKUP u.vs_allocas id = SOME (b,len)` by metis_tac[] >>
  fs[venomMemDefsTheory.alloca_inv_def,
     venomMemDefsTheory.allocas_non_overlapping_def, regions_disjoint_def] >>
  first_x_assum (qspecl_then [`aid`,`id`,`dst`,`nb`,`b`,`len`] mp_tac) >>
  simp[]
QED

Theorem unwrap_alloc_local_disjoint:
  stmt_state_rel ctx func cenv cx es u /\ fn_inst_ids_distinct func /\
  MEM (mk_inst aid ALLOCA [Lit n] [root]) (fn_insts func) /\
  not_local_ptr cenv es.scopes root /\
  FLOOKUP u.vs_allocas aid = SOME (dst,nb) ==>
  !name b len. local_region cenv es.scopes u name b len ==>
    regions_disjoint dst nb b len
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  `alloca_inv u /\ local_ptrs_rel func cenv es.scopes u` by
    fs[stmt_state_rel_def, state_rel_def] >>
  irule localPtrsPropsTheory.local_ptrs_rel_alloca_disjoint >>
  goal_assum drule >>
  qexistsl_tac [`cenv`, `mk_inst aid ALLOCA [Lit n] [root]`, `name`,
                `root`, `es.scopes`, `u`] >> simp[mk_inst_def]
QED

Theorem unwrap_alloc_semantic_frames:
  compile_alloc_buffer nb sa = (buf,sm) /\ fn_has_code sa sm func /\
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ nb < dimword (:256) /\
  buf.buf_operand = Var root /\
  u = update_var root d (buffer_allocation_fields s sa.cs_next_id nb) /\
  step_inst_base (mk_inst sa.cs_next_id ALLOCA [Lit (n2w nb)] [root]) s = OK u ==>
  stmt_state_rel ctx func cenv cx es u /\
  FLOOKUP u.vs_allocas sa.cs_next_id = SOME (w2n d,nb) /\
  u.vs_memory = s.vs_memory /\
  (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
  (!id entry. FLOOKUP s.vs_allocas id = SOME entry ==>
     FLOOKUP u.vs_allocas id = SOME entry) /\
  (!id b len. id < sa.cs_next_id /\ FLOOKUP s.vs_allocas id = SOME (b,len) ==>
     regions_disjoint (w2n d) nb b len) /\
  (!name b len. local_region cenv es.scopes u name b len ==>
     regions_disjoint (w2n d) nb b len)
Proof
  strip_tac >> drule_all unwrap_alloc_semantic_state >>
  disch_then (qspec_then `u.vs_inst_idx` strip_assume_tac) >>
  `lookup_var root u = SOME d` by
    (qpat_x_assum `u = update_var _ _ _` SUBST1_TAC >>
     simp[update_var_def, lookup_var_def, FLOOKUP_UPDATE]) >>
  `w = d` by fs[] >>
  qpat_x_assum `w = d` SUBST_ALL_TAC >>
  drule unwrap_alloc_fields_old >> strip_tac >>
  drule unwrap_alloc_generated_code >> strip_tac >>
  `root = STRING #"%" (toString sa.cs_next_var)` by fs[] >>
  `MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w nb)] [root]) (fn_insts func)` by
    metis_tac[buffer_alloc_code] >>
  `not_local_ptr cenv es.scopes root` by
    (simp[] >> irule local_ptrs_reserved_fresh >> qexists_tac `sa` >> simp[]) >>
  `alloca_inv u` by fs[stmt_state_rel_def, state_rel_def] >>
  `!x. not_fresh_at sa x ==> x <> root` by
    (rpt strip_tac >> gvs[not_fresh_at_def]) >>
  qpat_x_assum `u = update_var _ _ _` kall_tac >>
  qpat_x_assum `root = STRING _ _` kall_tac >>
  qpat_x_assum `out = STRING _ _` kall_tac >>
  qpat_x_assum `stmt_state_rel _ _ _ _ _ (_ with vs_inst_idx := _)` mp_tac >>
  simp[stmt_state_rel_inst_idx] >> strip_tac >>
  simp[] >> rpt conj_tac
  >- (rpt strip_tac >> irule unwrap_alloc_old_disjoint >>
      goal_assum drule >> qexistsl_tac [`sa.cs_next_id`, `id`] >> simp[])
  >> rpt strip_tac >> drule_all unwrap_alloc_local_disjoint >> simp[]
QED
