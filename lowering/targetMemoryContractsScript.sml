(* Counted target continuation interfaces. *)
Theory targetMemoryContracts
Ancestors
  bodyMemoryPreds targetPlaceSimCasesBase exprSimMemDefs targetPlaceSimDefs
  targetPlaceSim exprSimDefs
  targetSubscriptMemory bodyMemAugAssignAttrLocal allocaFootprint bodySimAugPlaceLoad
  exprSimProps exprLoweringProps loweringStateRelDefs loweringPosts valueEncoding
  vyperInterpreter vyperState venomState

(* The successful base evaluation is precisely the reachability guard in
   body_base_target_mem_ok; no global expression induction is required. *)
Theorem target_subscript_index_sim_mem:
  body_base_target_mem_ok cx (SubscriptTarget bt e) /\
  body_inv tops ctx cenv cx /\
  target_pre cenv cx env (SubscriptTarget bt e) es /\
  eval_base_place cx bt es = (INL pv,es1) ==>
  expr_sim_mem ctx func cenv cx ty e es1 /\
  expr_vv_sim_mem ctx func cenv cx ty e es1
Proof
  strip_tac >>
  `target_pre cenv cx env bt es` by metis_tac[target_pre_sub] >>
  `expr_sim_inv cenv cx env es1` by metis_tac[eval_base_place_sim_inv] >>
  `expr_body_pre cenv cx env e es1` by
    fs[target_pre_def, target_indices_pre_def] >>
  `body_expr_mem_ok cx e` by
    (fs[body_base_target_mem_ok_def] >> metis_tac[]) >>
  fs[body_expr_mem_ok_def] >> metis_tac[]
QED

(* Even a zero-capacity dynamic array has a length word.  In particular
   the counted header load does not require a nonempty source array. *)
Theorem target_memory_dynamic_header_frontier:
  expr_sim_inv cenv cx env es /\ stmt_state_rel ctx func cenv cx es s /\
  place_ptr_rel cenv cx s (PlaceR (MemoryPlace id path)) w loc
    (Type (ArrayT ety (Dynamic cap))) /\
  lookup_scopes id es.scopes = SOME entry /\
  evaluate_subscripts entry.type entry.value path = INL (ArrayV av) /\
  evaluate_type (get_tenv cx) (ArrayT ety (Dynamic cap)) =
    SOME (ArrayTV etv (Dynamic cap)) ==>
  w2n w + 32 <= s.vs_alloca_next
Proof
  strip_tac >>
  drule_all place_ptr_rel_memory_current >> strip_tac >>
  gvs[place_ptr_rel_def] >>
  `evaluate_type (get_tenv cx) t0 = SOME entry.type` by
    (irule aug_place_entry_type_agrees >> metis_tac[]) >> gvs[] >>
  `local_ptrs_rel func cenv es.scopes s` by
    fs[stmt_state_rel_def, state_rel_def] >>
  `w2n b + sz <= s.vs_alloca_next /\ type_memory_size entry.type <= sz` by
    (qpat_x_assum `local_ptrs_rel _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [local_ptrs_rel_def]) >>
     first_x_assum drule_all >> strip_tac >> gvs[]) >>
  drule mem_path_offset_sound >> strip_tac >>
  `k + 32 <= sz` by (fs[type_memory_size_def] >> decide_tac) >>
  irule local_ptr_field_below_frontier >> qexists `sz` >> simp[]
QED

(* Representative memory-touching subscript suffix: the dynamic local
   length load, with both allocation outputs retained. *)
Theorem target_memory_dynamic_header_path_mem:
  expr_sim_inv cenv cx env es /\ stmt_state_rel ctx func cenv cx es s /\
  place_ptr_rel cenv cx s (PlaceR (MemoryPlace id path)) w loc
    (Type (ArrayT ety (Dynamic cap))) /\
  lookup_scopes id es.scopes = SOME entry /\
  evaluate_subscripts entry.type entry.value path = INL (ArrayV av) /\
  evaluate_type (get_tenv cx) (ArrayT ety (Dynamic cap)) =
    SOME (ArrayTV etv (Dynamic cap)) /\
  emit_op MLOAD [bop] sa = (len,sb) /\ eval_operand bop s = SOME w /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ alloca_history func s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u. gas_marked_path T ctx func s 0 (OK u) /\
    eval_operand len u = SOME (n2w (array_length (ArrayTV etv (Dynamic cap)) av)) /\
    stmt_state_rel ctx func cenv cx es u /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    local_ptrs_reserved cenv sb /\ alloca_history func u /\
    (!rp. not_fresh_at sa rp ==> lookup_var rp u = lookup_var rp s) /\
    u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next /\
    u.vs_memory = s.vs_memory
Proof
  strip_tac >>
  drule_all target_memory_dynamic_header_frontier >> strip_tac >>
  drule_all place_ptr_rel_memory_current >> strip_tac >>
  drule_all target_memory_array_header >> strip_tac >>
  drule_all augassign_field_read_path_mem >> strip_tac >>
  qexists `t` >> simp[]
QED
