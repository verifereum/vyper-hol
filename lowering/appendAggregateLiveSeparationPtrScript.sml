(* Physical separation uses value placement, not arbitrary provenance sites. *)
Theory appendAggregateLiveSeparationPtr
Ancestors annAssignPtrDestinationFrame localPtrsProps loweringPosts exprLoweringProps
  loweringStateRelDefs venomMemDefs venomState venomInst finite_map arithmetic

Theorem append_aggregate_live_separation_ptr:
  !ctx func cenv cx es s inst dst b sz eb ty ea v src tv a.
    stmt_state_rel ctx func cenv cx es s /\
    fn_inst_ids_distinct func /\ MEM inst (fn_insts func) /\
    inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [dst] /\
    not_local_ptr cenv es.scopes dst /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) /\
    eb.cs_next_id <= inst.inst_id /\
    expr_val_at cenv cx ty ea eb es v (Var src) s /\
    evaluate_type (get_tenv cx) ty = SOME tv /\ ~is_word_type ty /\
    lookup_var src s = SOME a /\ 0 < val_footprint tv v ==>
    w2n a + val_footprint tv v <= b \/ b+sz <= w2n a
Proof
  rpt gen_tac >> strip_tac >>
  `alloca_inv s /\ local_ptrs_rel func cenv es.scopes s` by
    fs[stmt_state_rel_def, state_rel_def] >>
  qpat_x_assum `expr_val_at _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[expr_val_at_def] >>
  simp[eval_operand_def] >> strip_tac
  >- (`aid <> inst.inst_id` by decide_tac >>
      `b' + sz' <= b \/ b+sz <= b'` by
        (fs[alloca_inv_def, allocas_non_overlapping_def] >> metis_tac[]) >>
      decide_tac)
  >- (drule_all local_ptrs_rel_alloca_disjoint >>
      simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  decide_tac
QED
