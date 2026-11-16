Theory assignPlaceStoreReady
Ancestors
  assignPlaceMemory assignPlaceStorage
  loweringPosts stmtSimDefs stmtLowering compileEnv vyperStorageFootprint
  vyperStoragePlaceObserved
Libs monadsyntax

(* Store-only continuation: unwrap and target framing belong to the caller. *)
Theorem assign_place_store_from_expr_post:
  compile_assign_value cenv dst loc src (is_word_type dty) src_loc dty
    (lowered_value_type cenv e)
    (type_memory_bytes cenv dty) su = ((),sb) /\
  (?H. valid_horizon cx st0 H ee.storage_trace) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    expr_post H ctx func cenv cx e es sa su s0 ee v src s /\
    storage_place_observed H p /\ regions_consistent (FST H) /\
    storage_locks_separated (FST H) (SND H)) /\
  expr_sim_inv cenv cx env ee /\
  type_widens_to (get_tenv cx) (post_value_type cenv e) dty /\
  evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME stv /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  value_has_type stv v /\
  loc <> LocCode /\ loc <> LocCalldata /\
  (!x. src = Var x ==> not_fresh_at su x) /\
  (!x. dst = Var x ==> not_fresh_at su x) /\
  eval_operand dst s = SOME dw /\
  place_ptr_rel cenv cx s (PlaceR p) dw (SOME loc) (Type dty) /\
  (!id path entry t0. p = MemoryPlace id path /\
    lookup_scopes id ee.scopes = SOME entry /\ cenv.ce_var_type id = SOME t0 ==>
    evaluate_type (get_tenv cx) t0 = SOME entry.type) /\
  write_place cx p v ee = (INL (),ff) /\
  local_ptrs_reserved cenv su /\ cenv.ce_target CapMcopy /\
  acyclic_struct_metadata cenv.ce_struct_fields /\
  fn_has_code su sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = su.cs_current_bb /\
  s.vs_inst_idx = LENGTH su.cs_current_insts /\
  expr_body_pre cenv cx env0 e es0 /\
  (do pv <- eval_expr cx e; read_result cx pv od) es0 = (INL v,er) /\
  type_widens_to env0.type_defs (expr_type e) dty /\
  post_value_type cenv e = expr_type e /\
  (lowered_value_type cenv e = expr_type e \/
   is_bytestring_type (expr_type e) /\
   is_bytestring_type (lowered_value_type cenv e) /\
   arg_type_fits (lowered_value_type cenv e) (expr_type e)) /\
  0 < type_slot_size dtv /\ 0 < type_memory_size dtv /\
  (loc <> LocMemory /\ ~is_word_type dty /\ dty <> lowered_value_type cenv e /\
   ~(is_bytestring_type dty /\ is_bytestring_type (lowered_value_type cenv e)) ==>
   type_alloc_ok cenv dty) ==>
  ?t. gas_marked_path F ctx func s 0 (OK t) /\
    (!H. valid_horizon cx st0 H ee.storage_trace ==>
      stmt_state_rel H ctx func cenv cx ff t) /\
    (!x. not_fresh_at su x ==> lookup_var x t = lookup_var x s) /\
    (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
             FLOOKUP t.vs_allocas aid = SOME b) /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_frame cenv ee su s cenv ff t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!H. valid_horizon cx st0 H ee.storage_trace ==>
    expr_post H ctx func cenv cx e es sa su s0 ee v src s` by metis_tac[] >>
  Cases_on `loc = LocMemory`
  >- (qpat_x_assum `loc = LocMemory` SUBST_ALL_TAC >>
      `storage_place_region cx p` by
        (Cases_on `p` >> fs[place_ptr_rel_def,
          vyperStoragePlaceProvenanceTheory.storage_place_region_def] >>
         Cases_on `b` >> fs[slot_loc_def]) >>
      drule_all assign_place_memory_from_expr_post >> strip_tac >>
      qexists_tac `t` >> simp[]) >>
  Q.SUBGOAL_THEN `loc = LocStorage \/ loc = LocTransient` assume_tac
  >- (Cases_on `loc` >> gvs[]) >>
  `~is_word_type dty /\ dty <> lowered_value_type cenv e /\
   ~(is_bytestring_type dty /\ is_bytestring_type (lowered_value_type cenv e)) ==>
   type_alloc_ok cenv dty` by metis_tac[] >>
  drule_all assign_place_storage_from_expr_post >> strip_tac >>
  qexists_tac `t` >> simp[]
QED
