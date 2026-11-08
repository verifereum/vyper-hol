Theory placeRelayoutStorageRun
Ancestors
  placeStore placeDestinationBounds placeRelayoutSource allocaSiteResource
  exprSimHypsDefs exprLoweringProps stmtSimDefs loweringPosts allocLimits
  vyperTypeArgFits vyperTypeSystem venomMemDefs

Theorem place_relayout_storage_run:
  !ctx func cenv cx env ee ff s p w loc dst op src_loc dty sty stv v sa sb
   cfn bt e sc sd sw.
    compile_assign_value cenv dst loc op (is_word_type dty) src_loc dty sty
      (case dty of ArrayT et (Dynamic _) =>
         SOME ((type_memory_bytes cenv et + 31) DIV 32, type_memory_bytes cenv et)
       | _ => NONE) (type_memory_bytes cenv dty) sa = ((),sb) /\
    compile_get_target_ptr cfn cenv bt sc = ((dst,SOME loc,SOME (ValPT dty)),sd) /\
    (loc = LocStorage \/ loc = LocTransient) /\
    assign_alloc_ok cenv bt e /\ lowered_value_type cenv e = sty /\
    ~(has_length_word (expr_type e) /\ is_empty_value_expr e) /\
    eval_operand dst s = SOME w /\ eval_operand op s = SOME sw /\
    place_ptr_rel cenv cx s (PlaceR p) w (SOME loc) (Type dty) /\
    (!x. dst = Var x ==> not_fresh_at sa x) /\
    (!x. op = Var x ==> not_fresh_at sa x) /\
    type_widens_to (get_tenv cx) sty dty /\ assignable_type (get_tenv cx) sty /\
    evaluate_type (get_tenv cx) sty = SOME stv /\ value_has_type stv v /\
    ~is_word_type sty /\ expr_val_rel cx sty v op s /\ cenv.ce_target CapMcopy /\
    (?aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) /\ aid < sa.cs_next_id /\
       b <= w2n sw /\ w2n sw + type_memory_size stv <= b + sz) /\
    expr_sim_inv cenv cx env ee /\ acyclic_struct_metadata cenv.ce_struct_fields /\
    local_ptrs_reserved cenv sa /\ storage_place_region cx p /\
    stmt_state_rel ctx func cenv cx ee s /\ write_place cx p v ee = (INL (),ff) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t. gas_marked_path F ctx func s 0 (OK t) /\
        stmt_state_rel ctx func cenv cx ff t /\
        (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
        (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==> FLOOKUP t.vs_allocas aid = SOME b) /\
        ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
        t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `loc <> LocMemory` by (Cases_on `loc` >> gvs[]) >>
  `alloca_inv s` by fs[stmt_state_rel_def] >>
  first_x_assum (qx_choosel_then [`aid0`,`off0`,`len0`] strip_assume_tac) >>
  `!sw. eval_operand op s = SOME sw ==>
    w2n sw + type_memory_size stv <= s.vs_alloca_next /\
    !aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) /\ sa.cs_next_id <= aid ==>
       w2n sw + type_memory_size stv <= b \/ b + sz <= w2n sw` by
    (qx_gen_tac `sw'` >> disch_tac >>
     `sw' = sw` by gvs[] >> pop_assum SUBST_ALL_TAC >>
     conj_tac
     >- (drule_all alloca_site_registered_below >> decide_tac) >>
     map_every qx_gen_tac [`aid1`,`off1`,`len1`] >> strip_tac >>
     `aid0 <> aid1` by decide_tac >>
     `off0 + len0 <= off1 \/ off1 + len1 <= off0` by
       metis_tac[alloca_inv_def, allocas_non_overlapping_def] >> decide_tac) >>
  `!dtv. evaluate_type (get_tenv cx) dty = SOME dtv ==> 0 < type_slot_size dtv` by
    metis_tac[type_widens_to_assignable_type, assignable_type_slot_size_pos] >>
  `loc <> LocMemory /\ dty <> sty /\
    ~(is_bytestring_type dty /\ is_bytestring_type sty) ==> type_alloc_ok cenv dty` by
    (strip_tac >> simp[type_alloc_ok_def] >> strip_tac >>
     drule storage_target_normalization_bound >> simp[] >>
     disch_then drule >> metis_tac[]) >>
  irule place_store_value_run >> simp[] >>
  goal_assum (drule_at (Pat `compile_assign_value _ _ _ _ _ _ _ _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `write_place _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `expr_sim_inv _ _ _ _`)) >> simp[] >>
  reverse (conj_tac)
  >- (reverse conj_tac
      >- (rpt strip_tac >> gvs[place_ptr_rel_def]) >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  metis_tac[arithmeticTheory.ADD_COMM]
QED
