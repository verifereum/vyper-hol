(* Allocation bounds at a word-valued local place. *)
Theory augAssignPlaceMemoryTarget
Ancestors
  targetPlaceSimMem stmtSimAugAssignPlaceMemory allocaFootprint
  abiValueEncoding loweringPosts bodySimAugPlaceLoad exprSimDefs
  compileEnv exprSimProps exprLoweringProps bodyMemAugAssignAttrLocal
  fragGasMode stmtSimAugAssignPlace bodyAugPlaceTarget bodySimAugPlaceLive

Theorem aug_place_memory_word_frontier:
  stmt_state_rel ctx func cenv cx es s /\
  expr_sim_inv cenv cx env es /\
  lookup_scopes id es.scopes = SOME entry /\
  place_ptr_rel cenv cx s (PlaceR (MemoryPlace id path)) w loc (Type ty) /\
  is_word_type ty ==>
  w2n w + 32 <= s.vs_alloca_next
Proof
  rpt strip_tac >> gvs[place_ptr_rel_def] >>
  `evaluate_type (get_tenv cx) t0 = SOME entry.type` by
    (irule aug_place_entry_type_agrees >> metis_tac[]) >>
  gvs[] >>
  `local_ptrs_rel func cenv es.scopes s` by
    fs[stmt_state_rel_def, state_rel_def] >>
  `w2n b + sz <= s.vs_alloca_next /\ type_memory_size entry.type <= sz` by
    (qpat_x_assum `local_ptrs_rel _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [local_ptrs_rel_def]) >>
     first_x_assum drule_all >> strip_tac >> gvs[]) >>
  `type_memory_size tv = 32` by metis_tac[abi_word_type_size] >>
  drule mem_path_offset_sound >> strip_tac >>
  irule local_ptr_field_below_frontier >>
  qexists_tac `sz` >> simp[]
QED

(* A successfully read local place admits the counted old-value load. *)
Theorem aug_place_memory_access_path:
  expr_sim_inv cenv cx env es /\ body_inv tops ctx cenv cx /\
  supported_stmt tops bindings (AugAssign ty bt bop e) /\
  ((?b fld. bt = AttributeTarget b fld) \/ (?b k. bt = SubscriptTarget b k)) /\
  type_stmt env ret_ty (AugAssign ty bt bop e) = SOME env' /\
  eval_target_place cx bt es = (INL (MemoryPlace id path),st) /\
  read_place cx (MemoryPlace id path) st = (INL old,stc) /\
  place_type_value cx (MemoryPlace id path) stc = (INL ptv,stt) /\
  stmt_state_rel ctx func cenv cx st s /\
  expr_sim_inv cenv cx env st /\
  place_ptr_rel cenv cx s (PlaceR (MemoryPlace id path)) w loc (Type ty) /\
  emit_op MLOAD [dst] sa = (cur,sb) /\ eval_operand dst s = SOME w /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ alloca_history func s /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  stc = st /\ stt = st /\ type_bits ty MOD 8 = 0 /\
  w2n w + 32 <= s.vs_alloca_next /\
  ?tv u. evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv old /\
    gas_marked_path T ctx func s 0 (OK u) /\
    eval_operand cur u = SOME (typed_val_to_w256 tv old) /\
    stmt_state_rel ctx func cenv cx st u /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    local_ptrs_reserved cenv sb /\ alloca_history func u /\
    (!rp. not_fresh_at sa rp ==> lookup_var rp u = lookup_var rp s) /\
    u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next /\
    u.vs_memory = s.vs_memory /\ sa.cs_next_var <= sb.cs_next_var /\
    (?out. cur = Var out /\ not_fresh_at sb out)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all aug_place_supported_stmt_target_info >> strip_tac >>
  drule_all aug_place_target_memory_live >> strip_tac >>
  drule_all aug_place_memory_access_ready >> strip_tac >>
  `is_word_type ty` by
    (drule aug_place_typing >> metis_tac[exprSimSourceTheory.word_value_type_word]) >>
  `w2n w + 32 <= s.vs_alloca_next` by
    (irule aug_place_memory_word_frontier >> metis_tac[]) >>
  simp[] >> drule_all augassign_field_read_path_mem >> strip_tac >>
  metis_tac[]
QED
