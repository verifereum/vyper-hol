(* Consumer premises for a supported local array iterator. *)
Theory forPtrElement
Ancestors bodyPtrDefs stmtSimForArray stmtSimForArrayParts ptrCoverage
  exprLoweringProps compileEnv

(* The statement-boundary invariant's live-local interface, independent of
   For syntax. Consumers need not unfold ghost_inv themselves. *)
Theorem ghost_inv_local_ptr:
  ghost_inv d cenv cx es G tn s /\
  lookup_scopes name es.scopes = SOME entry /\
  FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==>
  ptr_covers G tn p s sz /\
  !w mem. lookup_var p s = SOME w /\
    mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory entry.type entry.value (w2n w) mem
Proof
  simp[ghost_inv_def] >> metis_tac[]
QED

Theorem for_local_array_element_robust:
  ghost_inv d cenv cx es G tn s /\
  lookup_scopes name es.scopes = SOME entry /\
  FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) /\
  entry.type = ArrayTV tv (Fixed n) /\
  entry.value = ArrayV (SArrayV kvs) /\
  lookup_var p s = SOME w /\ k < n ==>
  !mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory tv
      (EL k (array_elements (ArrayTV tv (Fixed n)) (SArrayV kvs)))
      (w2n w + k * type_memory_size tv) mem
Proof
  strip_tac >> drule_all ghost_inv_local_ptr >> strip_tac >>
  rpt strip_tac >> irule fixed_array_element_in_memory >>
  first_x_assum drule >> simp[]
QED

(* Coverage follows the actual element address; the arithmetic/provenance
   instructions must supply the three explicit facts about q in the post. *)
Theorem for_array_element_coverage:
  ptr_covers G tn p s region_sz /\ lookup_var p s = SOME w /\
  n * type_memory_size tv <= region_sz /\
  w2n w + region_sz < dimword (:256) /\ k < n /\
  lookup_var q s' = SOME (w + n2w k * n2w (type_memory_size tv)) /\
  FLOOKUP G' q = FLOOKUP G p /\ op_taint tn' (Var q) = {} ==>
  ptr_covers G' tn' q s' (type_memory_size tv)
Proof
  strip_tac >>
  `w2n (w + n2w k * n2w (type_memory_size tv)) =
    w2n w + k * type_memory_size tv` by
    (qspecl_then [`w2n w`, `n`, `type_memory_size tv`, `k`]
       mp_tac fixed_array_element_address >> simp[] >>
     disch_then irule >> decide_tac) >>
  `w2n w + k * type_memory_size tv + type_memory_size tv <=
    w2n w + region_sz` by
    (irule fixed_array_element_extent >> qexists_tac `n` >> simp[]) >>
  gvs[ptr_covers_def] >> decide_tac
QED

Theorem stmt_state_rel_local_extent:
  stmt_state_rel ctx fn cenv cx es s /\
  lookup_scopes name es.scopes = SOME entry /\
  FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) ==>
  ?w. lookup_var p s = SOME w /\
    type_memory_size entry.type <= sz /\
    w2n w + sz <= s.vs_alloca_next /\
    s.vs_alloca_next < dimword (:256)
Proof
  strip_tac >>
  `alloca_room ctx fn s /\ local_ptrs_rel fn cenv es.scopes s` by
    fs[stmt_state_rel_def, state_rel_def] >>
  drule alloca_room_next_lt >> strip_tac >>
  fs[local_ptrs_rel_def] >> metis_tac[]
QED

Theorem for_local_array_element_coverage:
  stmt_state_rel ctx fn cenv cx es s /\
  ghost_inv d cenv cx es G tn s /\
  lookup_scopes name es.scopes = SOME entry /\
  FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) /\
  entry.type = ArrayTV tv (Fixed n) /\ lookup_var p s = SOME w /\
  k < n /\
  lookup_var q s' = SOME (w + n2w k * n2w (type_memory_size tv)) /\
  FLOOKUP G' q = FLOOKUP G p /\ op_taint tn' (Var q) = {} ==>
  ptr_covers G' tn' q s' (type_memory_size tv)
Proof
  strip_tac >> drule_all stmt_state_rel_local_extent >> strip_tac >>
  drule_all ghost_inv_local_ptr >> strip_tac >>
  `n * type_memory_size tv <= sz /\
   w2n w + sz < dimword (:256)` by
    (gvs[valueEncodingTheory.type_memory_size_def] >> decide_tac) >>
  drule_all for_array_element_coverage >> simp[]
QED

(* A typed fixed-array Name really is a no-code memory-local source; this
   bridges the syntactic dispatch audit to the invariant's robust bytes. *)
Theorem for_array_name_source_ptr:
  expr_sim_inv cenv cx env es /\
  well_typed_expr env (Name (ArrayT ty (Fixed n)) name) /\
  stmt_state_rel ctx fn cenv cx es s /\ ghost_inv d cenv cx es G tn s ==>
  ?entry tv p sz w.
    lookup_scopes name es.scopes = SOME entry /\
    FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) /\
    evaluate_type (get_tenv cx) ty = SOME tv /\
    entry.type = ArrayTV tv (Fixed n) /\
    lookup_var p s = SOME w /\ ptr_covers G tn p s sz /\
    n * type_memory_size tv <= sz /\ w2n w + sz < dimword (:256) /\
    compile_expr cenv (ArrayT ty (Fixed n))
      (Name (ArrayT ty (Fixed n)) name) st =
      (LocatedValue (ArrayT ty (Fixed n)) (mk_ptr (Var p) LocMemory), st) /\
    (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
       val_in_memory entry.type entry.value (w2n w) mem)
Proof
  strip_tac >> drule_all array_name_local_binding >> strip_tac >>
  drule_all stmt_state_rel_local_extent >> strip_tac >>
  drule_all ghost_inv_local_ptr >> strip_tac >>
  goal_assum (drule_at Any) >> simp[] >>
  conj_tac >- gvs[valueEncodingTheory.type_memory_size_def] >>
  irule compile_array_name >> simp[]
QED

(* Consumer checkpoint / remaining administrative premises (not new axioms):

   for_supported_array_element_type supplies the Name syntax; S1's exported
   array_name_local_binding is consumed above (array_for_source_ready is
   local to its wrapper). compile_array_name in stmtSimForArrayParts is the
   actual no-code LocMemory boundary; there is no array_iter_layout theorem.
   The element source extent follows from stmt_state_rel_local_extent, not
   from an assumed allocation bound on arbitrary ghost provenance. This also
   handles zero-sized elements: coverage does not require a positive stride.

   C1.2.1 must supply, at the copy entry, the computed element pointer q's
   lookup value, inherited provenance and empty operand taint -- precisely
   the three post-state premises of for_local_array_element_coverage.
   To cover the destination slot p_dst, ALLOCA must give lookup_var p_dst,
   its (base,size) provenance and empty operand taint with size at least the
   evaluated element type size. No destination value cleanliness is needed
   before the overwrite. None of these facts follows from syntactic dispatch.

   Separation must cover re-executed ALLOCA, not just a fresh-frontier case.
   Reuse local_ptrs_rel_alloca_disjoint (localPtrsProps) with alloca_inv,
   fn_inst_ids_distinct, local_ptrs_rel, the slot instruction's membership
   in fn_insts and singleton output, not_local_ptr for that output in the
   OUTER environment, its recorded vs_allocas entry, and the source's
   local_region. stmt_state_rel gives alloca_inv/local_ptrs_rel, while the
   source scope/compiler lookups and lookup_var above give local_region.
   The administrative/layout owner must establish the instruction/output/
   recorded-allocation facts and not_local_ptr; it cannot assume that a new
   syntactic variable implies a new runtime allocation. The existing theorem
   is reused rather than duplicated here.

   The proposed finite-copy post (robust destination value, exterior memory
   agreement and old-variable ghost frame) suffices only after that slot's
   coverage is retained/re-established and the fresh scope binding is related
   to it. Scope extension/pop belongs to C1.3. Across a body callback the
   source's original local binding must remain live with its snapshot value;
   then ghost_inv_local_ptr recovers robust source bytes from callback
   ghost_inv. The old-variable frame alone does not give this memory fact.
   There is no ghost_kept conclusion in stmt_frag_ptr. No counted element
   copy or full loop ghost_inv establishment is claimed by this theory. *)
