(* Allocation bounds at a word-valued local place. *)
Theory augAssignPlaceMemoryTarget
Ancestors
  targetPlaceSimMem stmtSimAugAssignPlaceMemory allocaFootprint
  abiValueEncoding loweringPosts bodySimAugPlaceLoad exprSimDefs
  compileEnv exprSimProps exprLoweringProps bodyMemAugAssignAttrLocal
  fragGasMode stmtSimAugAssignPlace bodyAugPlaceTarget bodySimAugPlaceLive
  bodyMemEmitOpFrame venomExecSemantics venomInst venomState
  stmtSimAugAssignPlaceStorage gasContext targetPlaceSimCases stmtSimDefs
  vyperExprNoControl vyperInterpreter vyperState

Theorem aug_place_memory_word_frontier[local]:
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

(* Storage and transient loads have no linear-memory footprint. *)
Theorem aug_place_storage_access_path[local]:
  emit_op (if tr then TLOAD else SLOAD) [arg] sa = (op,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  local_ptrs_reserved cenv sa /\ stmt_state_rel ctx func cenv cx st s /\
  alloca_history func s /\ eval_operand arg s = SOME slot /\
  (!x. arg = Var x ==> not_fresh_at sa x) /\
  (if tr then tload slot s else sload slot s) = typed_val_to_w256 tv cur ==>
  ?u. gas_marked_path T ctx func s 0 (OK u) /\
    eval_operand op u = SOME (typed_val_to_w256 tv cur) /\
    stmt_state_rel ctx func cenv cx st u /\ eval_operand arg u = SOME slot /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    local_ptrs_reserved cenv sb /\ alloca_history func u /\
    (!rp. not_fresh_at sa rp ==> lookup_var rp u = lookup_var rp s) /\
    u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next /\
    sa.cs_next_var <= sb.cs_next_var /\
    (?out. op = Var out /\ not_fresh_at sb out)
Proof
  rpt strip_tac >>
  `step_inst_base
     (mk_inst sa.cs_next_id (if tr then TLOAD else SLOAD) [arg]
       [STRING #"%" (toString sa.cs_next_var)]) s =
   OK (update_var (STRING #"%" (toString sa.cs_next_var))
       (typed_val_to_w256 tv cur) s)` by
    (Cases_on `tr` >>
     qpat_x_assum `(if _ then _ else _) = _` mp_tac >>
     simp[mk_inst_def, step_inst_base_def, exec_read1_def]) >>
  drule_at (Pat `step_inst_base _ _ = _`) emit_op_word_path_frame_mem >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
  disch_then drule >>
  (impl_tac >- (Cases_on `tr` >> simp[])) >> strip_tac >>
  qexists_tac `t` >> simp[] >>
  Cases_on `arg` >> gvs[eval_operand_def, lookup_var_def] >> metis_tac[]
QED

(* Source decoding and machine access agree after a pure storage target. *)
Theorem aug_place_storage_read_path:
  contract_storage_well_formed cx es /\
  EVERY (supported_pure_expr tops) (target_indices bt) /\
  eval_target_place cx bt es = (INL (StoragePlace tr slot tv),st) /\
  target_post ctx func cenv cx es sa sp s0 st
    (PlaceR (StoragePlace tr slot tv)) (Type ty) r s /\
  is_word_type ty /\
  emit_op (if tr then TLOAD else SLOAD) [FST r] sp = (op,sb) /\
  fn_has_code sp sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sp /\ alloca_history func s /\
  ~s.vs_halted /\ s.vs_current_bb = sp.cs_current_bb /\
  s.vs_inst_idx = LENGTH sp.cs_current_insts ==>
  ?cur u.
    read_place cx (StoragePlace tr slot tv) st = (INL cur,st) /\
    place_type_value cx (StoragePlace tr slot tv) st = (INL tv,st) /\
    evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv cur /\
    gas_marked_path T ctx func s 0 (OK u) /\
    eval_operand op u = SOME (typed_val_to_w256 tv cur) /\
    stmt_state_rel ctx func cenv cx st u /\ eval_operand (FST r) u = SOME slot /\
    ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    local_ptrs_reserved cenv sb /\ alloca_history func u /\
    (!rp. not_fresh_at sp rp ==> lookup_var rp u = lookup_var rp s) /\
    u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next /\
    sp.cs_next_var <= sb.cs_next_var /\
    (?out. op = Var out /\ not_fresh_at sb out)
Proof
  rpt strip_tac >>
  drule_all aug_place_pure_target_storage_range >> strip_tac >>
  drule_all aug_place_pure_target_storage_live >> strip_tac >>
  `evaluate_type (get_tenv cx) ty = SOME tv /\
   stmt_state_rel ctx func cenv cx st s /\
   eval_operand (FST r) s = SOME slot /\
   (!x. FST r = Var x ==> not_fresh_at sp x)` by
    gvs[target_post_def, place_ptr_rel_def] >>
  drule_all aug_place_storage_read_ready >> strip_tac >>
  drule_all aug_place_storage_load_ready >> strip_tac >>
  drule_all aug_place_storage_access_path >> strip_tac >>
  metis_tac[]
QED

Theorem aug_place_target_admissible_mem:
  gas_admissible (eval_stmt cx (AugAssign ty bt bop e)) (stmt_res_ok lctx) es ==>
  gas_admissible (eval_target_place cx bt) target_place_res_ok es
Proof
  rw[gas_admissible_def] >> Cases_on `res`
  >- simp[target_place_res_ok_def] >>
  rename1 `eval_target_place cx bt _ = (INR ex,ee)` >>
  `no_control_exc ex` by metis_tac[eval_target_place_no_control] >>
  `eval_stmt cx (AugAssign ty bt bop e) (es with gas_obs := gs) =
   (INR ex,ee)` by (simp[Once evaluate_def, bind_def]) >>
  `stmt_res_ok lctx (INR ex)` by metis_tac[] >>
  gvs[stmt_res_ok_def, target_place_res_ok_def, no_control_exc_def]
QED

Theorem aug_place_memory_source_ready:
  expr_sim_inv cenv cx env es /\ body_inv tops ctx cenv cx /\
  supported_stmt tops bindings (AugAssign ty bt bop e) /\
  ((?b fld. bt = AttributeTarget b fld) \/ (?b k. bt = SubscriptTarget b k)) /\
  type_stmt env ret_ty (AugAssign ty bt bop e) = SOME env' /\
  eval_target_place cx bt es = (INL (MemoryPlace id path),st) /\
  expr_sim_inv cenv cx env st /\
  target_post ctx func cenv cx es sa sp s0 st
    (PlaceR (MemoryPlace id path)) (Type ty) r s ==>
  ?cur tv.
    read_place cx (MemoryPlace id path) st = (INL cur,st) /\
    place_type_value cx (MemoryPlace id path) st = (INL tv,st) /\
    evaluate_type (get_tenv cx) ty = SOME tv /\ value_has_type tv cur
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all aug_place_supported_stmt_target_info >> strip_tac >>
  drule_all aug_place_target_memory_live >> strip_tac >>
  `st.scopes = es.scopes` by metis_tac[aug_place_target_scopes] >>
  qpat_x_assum `target_post _ _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[target_post_def, place_readable_def] >> strip_tac >>
  drule_all aug_place_memory_type_read >> strip_tac >>
  `is_word_type ty` by
    (drule aug_place_typing >> metis_tac[exprSimSourceTheory.word_value_type_word]) >>
  drule_all aug_place_memory_read_typed >> simp[]
QED
