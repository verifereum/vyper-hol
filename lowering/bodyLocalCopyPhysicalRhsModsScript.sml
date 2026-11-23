(* Physical resources of a successful RHS at the actual copy cursor. *)
Theory bodyLocalCopyPhysicalRhsMods
Ancestors
  bodyFullPostsMods exprSimCopy assignBasePtrBoundary
  exprBodyPreProps exprBodyPreTypingProps typedMemoryCopy
  exprPtrUnwrapStorageShape exprSimIfExpCompat bodySimStmtFacts
  valueCopyBytes words bodyInvSplit loweringPosts loweringStateRelDefs bodyPtrDefs
  exprLowering stmtSimDefs exprSimMemDefs exprOperandVar valueTypingMemoryProps
  fragGasOriginPtr vyperInterpreter vyperState gasContext vyperStorageFootprint
  compileEnv gasExplicitSites finite_map exprLoweringProps fragGasOriginPtrExec
  exprSimHypsDefs fragExec exprSimUnwrapProps exprSimUnwrap exprSimMemorySource
  context

(* Immutable references select the owner in ce_modules, not the active
   module. At runtime their bytes come out of the data section. *)
Theorem local_copy_runtime_code_source_mods[local]:
  immutable_frame_mods func ce cx ee s /\ ~ce.ce_is_ctor /\
  ALOOKUP ce.ce_modules src = SOME tops /\
  immutable_holds (ce with ce_module := src) cx ty tv w ee s /\
  read_result cx tv ee = (INL v,ee) /\
  evaluate_type (get_tenv cx) ty = SOME rt ==>
  val_in_memory rt v (w2n w) s.vs_data_section /\
  w2n w + type_memory_size rt <= LENGTH s.vs_data_section
Proof
  strip_tac >>
  `immutables_rel ce cx.txn.target src F ee s` by
    fs[immutable_frame_mods_def, immutables_rel_mods_def] >>
  qpat_x_assum `immutable_holds _ _ _ _ _ _ _` mp_tac >>
  simp[immutable_holds_def] >> strip_tac >> gvs[] >>
  qpat_x_assum `immutables_rel _ _ _ _ _ _` mp_tac >>
  simp[immutables_rel_def] >> strip_tac >> first_x_assum drule_all >>
  strip_tac >>
  qpat_x_assum `sub_layout _ _ _ _ _` mp_tac >>
  simp[sub_layout_def] >> strip_tac >>
  `off + k < dimword (:256)` by decide_tac >>
  simp[arithmeticTheory.ADD_COMM] >>
  first_x_assum (qspecl_then [`off`, `s.vs_data_section`] mp_tac) >>
  simp[arithmeticTheory.ADD_COMM]
QED

Theorem local_copy_raw_code_source_mods:
  vv_post_mods H ctx func ce cx e es a sm entry ee tv
    (LocatedValue ty p) s /\
  p.ptr_location = LocCode /\
  ptr_vv_ok cx (post_value_type ce e) tv (LocatedValue ty p) ee G tn s /\
  read_result cx tv ee = (INL v,ee) /\
  evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
  (ce.ce_is_ctor ==>
   ?val. read_result cx tv ee = (INL val,ee) /\
     !rt w. evaluate_type (get_tenv cx) (post_value_type ce e) = SOME rt /\
            eval_operand p.ptr_operand s = SOME w ==>
            w2n w + type_memory_size rt <= lo /\
            (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
                   val_in_memory rt val (w2n w) mem)) ==>
  ty = post_value_type ce e /\
  op_taint tn p.ptr_operand = {} /\
  op_prov G p.ptr_operand = NONE /\
  ?src tops w. ALOOKUP ce.ce_modules src = SOME tops /\
    eval_operand p.ptr_operand s = SOME w /\
    immutable_holds (ce with ce_module := src) cx ty tv w ee s /\
    (ce.ce_is_ctor ==>
      w2n w + type_memory_size rt <= lo /\
      (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
             val_in_memory rt v (w2n w) mem)) /\
    (~ce.ce_is_ctor ==>
      val_in_memory rt v (w2n w) s.vs_data_section /\
      w2n w + type_memory_size rt <= LENGTH s.vs_data_section)
Proof
  strip_tac >>
  qpat_x_assum `vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [vv_post_mods_def]) >>
  qpat_x_assum `vv_holds_mods _ _ _ _ _ _ _` mp_tac >>
  simp[vv_holds_mods_def, immutable_holds_mods_def] >> strip_tac >>
  gvs[ptr_vv_ok_def] >>
  qexistsl_tac [`src`, `tops`] >> simp[arithmeticTheory.ADD_COMM] >>
  strip_tac >> drule_all local_copy_runtime_code_source_mods >>
  simp[arithmeticTheory.ADD_COMM]
QED

Theorem copy_rhs_operand_mods[local]:
  expr_post_mods H ctx func ce cx e es a b entry ee v op s /\
  ptr_val_ok cx (post_value_type ce e) v op G tn s /\
  ptr_buf_ok ce e op G s /\
  expr_store_bound cx (post_value_type ce e) v op s /\
  evaluate_type (get_tenv cx) (post_value_type ce e) = SOME pt /\
  evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME rt /\
  value_has_type rt v /\ value_has_type pt v /\
  ~is_word_type (post_value_type ce e) /\
  (post_value_type ce e = lowered_value_type ce e \/
   is_bytestring_type (post_value_type ce e) /\
   is_bytestring_type (lowered_value_type ce e)) /\
  type_memory_bytes ce (lowered_value_type ce e) = type_memory_size rt ==>
  ?w. eval_operand op s = SOME w /\ op_taint tn op = {} /\
    (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
           val_in_memory rt v (w2n w) mem) /\
    (val_store_size rt v = 0 \/ w2n w + val_store_size rt v <= s.vs_alloca_next) /\
    (0 < type_memory_size rt ==>
       ?src. op = Var src /\ ptr_covers G tn src s (type_memory_size rt))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `?w. eval_operand op s = SOME w` by
    fs[expr_post_mods_def, expr_post_def, expr_val_rel_def] >>
  `op_taint tn op = {} /\
    (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
           val_in_memory pt v (w2n w) mem)` by
    fs[ptr_val_ok_def, ptr_mem_ok_def] >>
  `val_store_size rt v = val_store_size pt v` by
    metis_tac[bytestring_val_store_size_eq, optionTheory.SOME_11] >>
  qexists_tac `w` >> simp[] >> rpt conj_tac
  >- metis_tac[bytestring_val_in_memory_transfer, optionTheory.SOME_11]
  >- fs[expr_store_bound_def] >>
  strip_tac >> irule ptr_buf_ok_read_covers >> simp[] >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem copy_rhs_destination_frame_mods[local]:
  expr_post_mods H ctx func ce cx e es a b entry ee v op s /\
  ghost_kept_at lo ce es a Gi ti entry G tn /\
  not_fresh_at a dst /\ lookup_var dst entry = SOME dw /\
  ptr_covers Gi ti dst entry cap /\
  FLOOKUP entry.vs_allocas aid = SOME chunk ==>
  lookup_var dst s = SOME dw /\ ptr_covers G tn dst s cap /\
  FLOOKUP s.vs_allocas aid = SOME chunk
Proof
  simp[expr_post_mods_def, expr_post_def, ghost_kept_at_def] >>
  strip_tac >> simp[] >>
  qpat_x_assum `ptr_covers _ _ _ _ _` mp_tac >>
  simp[ptr_covers_def] >> metis_tac[]
QED

(* The value branch uses the locations from the actual compile equation,
   and the path, post and frame from one already selected successful run. *)
Theorem local_copy_physical_rhs_mods:
  compile_expr ce (expr_type e) e a = (vv,sm) /\
  unwrap_value ce vv sm = (op,b) /\ local_ptrs_reserved ce a /\
  (!tail. bind (eval_expr cx e) (read_result cx)
     (es with gas_obs := gas_explicit marks entry.vs_gas_readings ++ tail) =
     (INL v,ee with gas_obs := tail)) /\
  storage_trace_domain cx st0 ee.storage_trace /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
     gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (entry,Gi,ti) marks (OK s,G,tn) /\
     expr_post_mods H ctx func ce cx e es a b entry ee v op s /\
     ghost_inv_at_mods (DF H) lo d ce cx ee G tn s) /\
  expr_store_bound cx (post_value_type ce e) v op s /\
  ptr_val_ok cx (post_value_type ce e) v op G tn s /\ ptr_buf_ok ce e op G s /\
  ghost_kept_at lo ce es a Gi ti entry G tn /\
  s.vs_current_bb = b.cs_current_bb /\ s.vs_inst_idx = LENGTH b.cs_current_insts /\
  expr_body_pre_mods mods ce cx env e es /\
  evaluate_type (get_tenv cx) (post_value_type ce e) = SOME pt /\
  evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME rt /\
  value_has_type rt v /\ value_has_type pt v /\
  ~is_word_type (post_value_type ce e) /\
  (post_value_type ce e = lowered_value_type ce e \/
   is_bytestring_type (post_value_type ce e) /\
   is_bytestring_type (lowered_value_type ce e)) ==>
  lower_value compile_expr ce (expr_type e) e a = (op,b) /\
  type_memory_bytes ce (lowered_value_type ce e) = type_memory_size rt /\ val_wf rt v /\
  bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := gas_explicit marks entry.vs_gas_readings) =
    (INL v,ee with gas_obs := []) /\
  ~s.vs_halted /\ s.vs_current_bb = b.cs_current_bb /\
  s.vs_inst_idx = LENGTH b.cs_current_insts /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
     gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (entry,Gi,ti) marks (OK s,G,tn) /\
     expr_post_mods H ctx func ce cx e es a b entry ee v op s /\
     ghost_inv_at_mods (DF H) lo d ce cx ee G tn s) /\
  (!dst cap dw aid chunk. not_fresh_at a dst /\ lookup_var dst entry = SOME dw /\
     ptr_covers Gi ti dst entry cap /\ FLOOKUP entry.vs_allocas aid = SOME chunk ==>
     lookup_var dst s = SOME dw /\ ptr_covers G tn dst s cap /\
     FLOOKUP s.vs_allocas aid = SOME chunk) /\
  ?w. eval_operand op s = SOME w /\ op_taint tn op = {} /\
    (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
           val_in_memory rt v (w2n w) mem) /\
    (val_store_size rt v = 0 \/ w2n w + val_store_size rt v <= s.vs_alloca_next) /\
    (0 < type_memory_size rt ==>
       ?src. op = Var src /\ not_fresh_at b src /\ ptr_covers G tn src s (type_memory_size rt))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `lower_value compile_expr ce (expr_type e) e a = (op,b)` by
    simp[lower_value_def, comp_bind_def] >>
  `type_memory_bytes ce (lowered_value_type ce e) = type_memory_size rt` by
    (irule typed_copy_memory_size >> qexists_tac `get_tenv cx` >>
     fs[expr_body_pre_mods_def, expr_sim_inv_mods_def] >> metis_tac[]) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qpat_assum `!H. valid_horizon _ _ _ _ ==> _`
    (drule_then strip_assume_tac) >>
  simp[value_has_type_memory_wf] >> rpt conj_tac
  >- (first_x_assum (qspec_then `[]` mp_tac) >> simp[])
  >- (drule gas_origin_ptr_path_exec >> simp[exit_result_def] >> metis_tac[])
  >- (rpt strip_tac >> drule_all copy_rhs_destination_frame_mods >> simp[]) >>
  `!x. op = Var x ==> not_fresh_at b x` by
    metis_tac[compile_lower_value_var] >>
  drule_all copy_rhs_operand_mods >>
  disch_then (qx_choose_then `w` (map_every assume_tac o CONJUNCTS)) >>
  qexists_tac `w` >> simp[] >> strip_tac >>
  qpat_assum `0 < type_memory_size rt ==> ?src. _` (drule_then strip_assume_tac) >>
  qexists_tac `src` >> simp[]
QED

Theorem copy_rhs_noncode_post_mods[local]:
  vv_post_mods H ctx func ce cx e es a sm entry ee tv vv s /\
  vv_location vv <> SOME LocCode ==>
  vv_post H ctx func ce cx e es a sm entry ee tv vv s /\
  immutable_frame_mods func ce cx ee s
Proof
  strip_tac >>
  `vv_holds ce cx (post_value_type ce e) tv vv ee s /\ vv_place_ptr ce cx ee s tv vv` by
    (Cases_on `vv` >> gvs[vv_location_def, vv_post_mods_def, vv_holds_mods_def,
       vv_place_ptr_mods_def, vv_place_ptr_def] >>
     Cases_on `tv` >> gvs[vv_place_ptr_def] >>
     CASE_TAC >> gvs[vv_place_ptr_def]) >>
  fs[vv_post_mods_def] >> rewrite_tac[vv_post_def] >> asm_rewrite_tac[]
QED

(* In the memory/stack branches unwrap emits no code. Keep the same VV
   witness (and the full staging width), without rerunning lower_value. *)
Theorem local_copy_rhs_identity_unwrap_mods:
  ((?ty. vv = StackValue ty op) \/
   (?ty p. vv = LocatedValue ty p /\ p.ptr_location = LocMemory /\
           ~is_word_type ty /\ p.ptr_operand = op)) /\
  unwrap_value ce vv sm = (op,b) /\ ~s.vs_halted /\
  read_result cx tv ee = (INL v,ee) /\
  vv_post_mods H ctx func ce cx e es a sm entry ee tv vv s /\
  vv_store_bound cx (post_value_type ce e) (lowered_value_type ce e) ee tv vv s /\
  ptr_vv_ok cx (post_value_type ce e) tv vv ee G tn s /\
  ~is_word_type (post_value_type ce e) ==>
  b = sm /\ gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK s,G,tn) /\
  expr_post_mods H ctx func ce cx e es a b entry ee v op s /\
  ptr_val_ok cx (post_value_type ce e) v op G tn s /\
  expr_store_bound cx (post_value_type ce e) v op s /\
  (!rt w. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME rt /\
          eval_operand op s = SOME w ==>
     type_memory_size rt = 0 \/ w2n w + type_memory_size rt <= s.vs_alloca_next)
Proof
  strip_tac >>
  `vv_location vv <> SOME LocCode` by simp[vv_location_def] >>
  drule_all copy_rhs_noncode_post_mods >> strip_tac >>
  drule_all vv_post_read_result >> strip_tac >>
  gvs[unwrap_value_def, comp_return_def, cj 1 gas_origin_ptr_path_rules,
      expr_post_mods_def, ptr_vv_ok_def, ptr_val_ok_def] >>
  qpat_x_assum `vv_store_bound _ _ _ _ _ _ _` mp_tac >>
  simp[expr_store_bound_def, vv_store_bound_def] >>
  metis_tac[expr_post_of_vv_post_stack, expr_post_of_vv_post_memory]
QED

(* For an emitted unwrap, attach the actual zero-GAS suffix to the raw
   run. The suffix and its post must describe the same selected state. *)
Theorem local_copy_rhs_unwrap_cut_mods:
  compile_expr ce (expr_type e) e a = (vv,sm) /\
  unwrap_value ce vv sm = (op,b) /\
  (!tail. eval_expr cx e
     (es with gas_obs := gas_explicit marks entry.vs_gas_readings ++ tail) =
     (INL tv,ee with gas_obs := tail)) /\
  read_result cx tv ee = (INL v,ee) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
     gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (entry,Gi,ti) marks (OK u,Gu,tu) /\
     vv_post_mods H ctx func ce cx e es a sm entry ee tv vv u) /\
  u.vs_current_bb = sm.cs_current_bb /\ u.vs_inst_idx = LENGTH sm.cs_current_insts /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
     gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (u,Gu,tu) [] (OK s,G,tn) /\
     expr_post_mods H ctx func ce cx e es a b entry ee v op s /\
     ghost_inv_at_mods (DF H) lo d ce cx ee G tn s) ==>
  lower_value compile_expr ce (expr_type e) e a = (op,b) /\
  (!tail. bind (eval_expr cx e) (read_result cx)
     (es with gas_obs := gas_explicit marks entry.vs_gas_readings ++ tail) =
     (INL v,ee with gas_obs := tail)) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
     gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (entry,Gi,ti) marks (OK s,G,tn) /\
     expr_post_mods H ctx func ce cx e es a b entry ee v op s /\
     ghost_inv_at_mods (DF H) lo d ce cx ee G tn s)
Proof
  strip_tac >> simp[lower_value_def, comp_bind_def] >> conj_tac
  >- (drule read_result_gas_obs >> simp[bind_def]) >>
  rpt strip_tac >> res_tac >> simp[] >>
  qpat_x_assum `gas_origin_ptr_path _ (entry,Gi,ti) marks _`
    (mp_then (Pos hd) mp_tac gas_origin_ptr_path_append) >>
  simp[] >> disch_then (qspec_then `[]` mp_tac) >> simp[]
QED
