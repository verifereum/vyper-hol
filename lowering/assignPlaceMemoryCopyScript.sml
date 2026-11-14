Theory assignPlaceMemoryCopy
Ancestors
  placeMemoryStateRebuild placeMemoryTypedPrimitive valueCopy
  venomExecSemantics venomState valueEncoding compileEnv exprSimHypsDefs loweringPosts
  stmtSimDefs vyperState vyperInterpreter finite_map list words

Theorem memory_place_mcopy_stmt_state:
  stmt_state_rel ctx func cenv cx ee s /\
  expr_sim_inv cenv cx env ee /\ local_ptrs_reserved cenv sa /\
  place_ptr_rel cenv cx s (PlaceR p) dw (SOME LocMemory) (Type dty) /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  value_has_type dtv v /\ val_wf dtv v /\
  write_place cx p v ee = (INL (),ff) /\
  (!id path entry t0. p = MemoryPlace id path /\
    lookup_scopes id ee.scopes = SOME entry /\ cenv.ce_var_type id = SOME t0 ==>
    evaluate_type (get_tenv cx) t0 = SOME entry.type) /\
  val_in_memory dtv v src s.vs_memory /\
  val_footprint dtv v <= n /\ n <= type_memory_size dtv /\
  (cenv.ce_is_ctor ==> !nm tv iv off.
    FLOOKUP cenv.ce_module_vars (cenv.ce_module,nm) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables cenv.ce_module imms) nm = SOME (tv,iv) ==>
    off + type_memory_size tv <= w2n dw \/ w2n dw + n <= off) ==>
  stmt_state_rel ctx func cenv cx ff (mcopy (w2n dw) src n s)
Proof
  strip_tac >> irule memory_place_write_stmt_state >>
  qexistsl_tac [`dtv`, `dty`, `ee`, `env`, `p`, `s`, `s`, `sa`, `v`, `dw`] >>
  simp[mcopy_val_in_memory, mcopy_memory_length] >>
  conj_tac
  >- (rpt strip_tac >> irule mem_bytes_at_mcopy_disjoint >> decide_tac) >>
  conj_tac
  >- simp[mcopy_def, write_memory_with_expansion_def, lookup_var_def] >>
  conj_tac
  >- simp[mcopy_def, write_memory_with_expansion_def,
          venom_state_component_equality] >>
  rpt strip_tac >> irule mem_bytes_at_mcopy_disjoint >> metis_tac[]
QED
