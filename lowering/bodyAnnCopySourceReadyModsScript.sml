(* Operand and copy-width facts at the selected forced-read endpoint. *)
Theory bodyAnnCopySourceReadyMods
Ancestors
  bodyCopyReadPhysicalTypeMods bodyFullPostsMods internalReturnMemoryInputs
  bodyDeclMemoryCore stmtSimDeclSourceSeparation annassignRelayoutSource
  valueCopyBytes valueTypingMemoryProps typedMemoryCopy reasonCopySourcePtr
  exprOperandVar exprLoweringProps stateRelProj loweringPosts venomMemDefs
  exprSimHypsDefs exprSimProps exprLowering compileEnv venomState words vyperAST vyperTyping
Libs monadsyntax

Theorem ann_read_physical_tags[local]:
  expr_body_pre_mods mods ce cx env e es /\
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := prefix) = (INL v,mid) /\
  ~is_word_type (expr_type e) ==>
  post_value_type ce e = lowered_value_type ce e \/
  is_bytestring_type (post_value_type ce e) /\ is_bytestring_type (lowered_value_type ce e)
Proof
  strip_tac >>
  `(expr_body_pre_mods mods ce cx env e (es with gas_obs := prefix) <=>
    expr_body_pre_mods mods ce cx env e es)` by
    simp_tac (srw_ss()) [expr_body_pre_mods_def,expr_sim_inv_mods_def] >>
  `expr_body_pre_mods mods ce cx env e (es with gas_obs := prefix)` by simp[] >>
  drule_all copy_read_physical_type_mods >> simp[]
QED

Theorem ann_copy_physical_origin[local]:
  (pty = sty \/ is_bytestring_type pty /\ is_bytestring_type sty) /\
  evaluate_type (get_tenv cx) pty = SOME pt /\
  evaluate_type (get_tenv cx) sty = SOME rt /\
  value_has_type pt v /\ value_has_type rt v /\
  expr_val_at ce cx pty a b mid v op s ==>
  expr_val_at ce cx sty a b mid v op s
Proof
  strip_tac >- gvs[] >>
  `?bt1 bt2. pt = BaseTV bt1 /\ rt = BaseTV bt2` by
    metis_tac[bytestring_type_value] >>
  `val_footprint rt v = val_footprint pt v` by
    metis_tac[bytestring_val_footprint_eq] >>
  `val_wf rt v` by simp[value_has_type_memory_wf] >>
  gvs[expr_val_at_def,is_bytestring_word_type] >>
  metis_tac[local_val_at_base,arithmeticTheory.LESS_EQ_REFL]
QED

Theorem ann_copy_live_bytes[local]:
  is_bytestring_type typ /\ type_widens_to tenv sty typ /\
  evaluate_type tenv sty = SOME rt /\ value_has_type rt v /\
  type_memory_size rt <= sz /\
  ptr_covers G tn xs s (type_memory_size rt) /\ ptr_covers G tn p s sz ==>
  is_bytestring_type sty /\
  ?len. ((?bs. v = BytesV bs /\ len = LENGTH bs) \/
         (?str. v = StringV str /\ len = LENGTH str)) /\
    val_store_size rt v = 32 + 32 * word_size len /\
    val_store_size rt v <= type_memory_size rt /\ val_store_size rt v <= sz /\
    ptr_covers G tn xs s (val_store_size rt v) /\
    ptr_covers G tn p s (val_store_size rt v)
Proof
  strip_tac >> drule_all_then assume_tac typed_copy_bytestring_source >>
  `val_store_size rt v <= type_memory_size rt` by
    simp[value_has_type_memory_wf,val_store_size_le] >>
  `val_store_size rt v <= sz` by decide_tac >>
  `ptr_covers G tn xs s (val_store_size rt v)` by
    (irule ptr_covers_mono >> qexists_tac `type_memory_size rt` >> simp[]) >>
  `ptr_covers G tn p s (val_store_size rt v)` by
    (irule ptr_covers_mono >> qexists_tac `sz` >> simp[]) >>
  asm_rewrite_tac[] >> drule_all bytestring_type_value >> strip_tac >>
  Cases_on `v` >> gvs[value_has_type_def,val_store_size_def]
QED

Theorem ann_copy_nonmemory_separate[local]:
  ~is_bytestring_type typ /\ type_widens_to (get_tenv cx) sty typ /\
  ~is_word_type sty /\ evaluate_type (get_tenv cx) sty = SOME rt /\
  0 < type_memory_size rt /\ type_memory_size dtv <= sz /\
  expr_val_at ce cx sty a b mid v op s /\ eval_operand op s = SOME sw /\
  stmt_state_rel H ctx func ce cx mid s /\ fn_inst_ids_distinct func /\
  MEM inst (fn_insts func) /\ inst.inst_outputs = [p] /\
  not_local_ptr ce mid.scopes p /\ inst.inst_id < a.cs_next_id /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n dw,sz) ==>
  w2n sw + type_memory_size rt <= w2n dw \/ w2n dw + type_memory_size dtv <= w2n sw
Proof
  strip_tac >>
  `~is_bytestring_type sty` by
    (strip_tac >> drule_all type_widens_from_bytestring >> simp[]) >>
  drule_all nonbytes_evaluated_val_footprint >> disch_then (qspec_then `v` assume_tac) >>
  `0 < val_footprint rt v` by simp[] >>
  `w2n sw + val_footprint rt v <= w2n dw \/ w2n dw + sz <= w2n sw` by
    (irule expr_val_at_alloca_outside_interval_separate >>
     conj_tac >- first_assum ACCEPT_TAC >>
     goal_assum (drule_at (Pat `expr_val_at _ _ _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `stmt_state_rel _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `FLOOKUP _ _ = SOME (w2n dw,sz)`)) >> simp[]) >>
  decide_tac
QED

Theorem ann_copy_source_ready_mods:
  expr_body_pre_mods mods ce cx env e es /\
  bind (eval_expr cx e) (read_result cx) (es with gas_obs := prefix) = (INL v,mid) /\
  ~is_word_type (expr_type e) /\ ~is_word_type (lowered_value_type ce e) /\
  ~is_word_type (post_value_type ce e) /\
  type_widens_to (get_tenv cx) (lowered_value_type ce e) typ /\
  evaluate_type (get_tenv cx) (post_value_type ce e) = SOME pt /\
  evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME rt /\
  value_has_type pt v /\ value_has_type rt v /\
  type_memory_bytes ce (lowered_value_type ce e) = type_memory_size rt /\
  0 < type_memory_size rt /\ type_memory_size rt <= type_memory_size dtv /\
  type_memory_size dtv <= sz /\
  expr_post_mods H ctx func ce cx e es a b s0 mid v op s /\
  expr_store_bound cx (post_value_type ce e) v op s /\
  ptr_val_ok cx (post_value_type ce e) v op G tn s /\
  (~is_word_type (post_value_type ce e) ==> ptr_buf_ok ce e op G s) /\
  compile_expr ce (expr_type e) e a = (vv,sv) /\
  unwrap_value ce vv sv = (op,b) /\ local_ptrs_reserved ce a /\
  lookup_var p s = SOME dw /\ ptr_covers G tn p s sz /\
  fn_inst_ids_distinct func /\ MEM inst (fn_insts func) /\ inst.inst_outputs = [p] /\
  not_local_ptr ce mid.scopes p /\ inst.inst_id < a.cs_next_id /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n dw,sz) /\
  (is_bytestring_type typ /\ vv_location vv = SOME LocMemory ==>
    !tv w. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME tv /\
           eval_operand op s = SOME w ==>
           type_memory_size tv = 0 \/ w2n w + type_memory_size tv <= s.vs_alloca_next) ==>
  ?xs sw. op = Var xs /\ not_fresh_at b xs /\ lookup_var xs s = SOME sw /\
    ptr_covers G tn xs s (type_memory_size rt) /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==> val_in_memory rt v (w2n sw) m) /\
    w2n sw + val_store_size rt v <= s.vs_alloca_next /\
    s.vs_alloca_next < dimword (:256) /\ w2n dw + sz <= s.vs_alloca_next /\
    (is_bytestring_type typ /\ vv_location vv <> SOME LocMemory ==>
      is_bytestring_type (lowered_value_type ce e) /\
      ?len. ((?bs. v = BytesV bs /\ len = LENGTH bs) \/
             (?str. v = StringV str /\ len = LENGTH str)) /\
        val_store_size rt v = 32 + 32 * word_size len /\
        val_store_size rt v <= type_memory_size rt /\ val_store_size rt v <= sz /\
        ptr_covers G tn xs s (val_store_size rt v) /\
        ptr_covers G tn p s (val_store_size rt v)) /\
    ((~is_bytestring_type typ \/ vv_location vv = SOME LocMemory) ==>
      w2n sw + type_memory_size rt <= s.vs_alloca_next /\
      w2n sw + type_memory_size rt < dimword (:256) /\
      (vv_location vv = SOME LocMemory ==>
        expr_val_at ce cx (lowered_value_type ce e) a b mid v (Var xs) s /\
        FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n dw,sz) /\ inst.inst_id < b.cs_next_id) /\
      (vv_location vv <> SOME LocMemory ==>
        w2n sw + type_memory_size rt <= w2n dw \/ w2n dw + type_memory_size dtv <= w2n sw))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then assume_tac ann_read_physical_tags >>
  `expr_post H ctx func ce cx e es a b s0 mid v op s` by fs[expr_post_mods_def] >>
  `?xs sw. op = Var xs /\ lookup_var xs s = SOME sw /\
    ptr_covers G tn xs s (type_memory_size rt) /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==> val_in_memory rt v (w2n sw) m) /\
    w2n sw + val_store_size rt v <= s.vs_alloca_next` by
    (irule internal_return_memory_value_inputs_lowered >> simp[] >>
     goal_assum (drule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `ptr_val_ok _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `evaluate_type _ _ = SOME pt`)) >> simp[]) >>
  `lower_value compile_expr ce (expr_type e) e a = (op,b)` by
    simp[lower_value_def,comp_bind_def] >>
  `not_fresh_at b xs` by (drule_all compile_lower_value_var >> simp[]) >>
  `stmt_state_rel H ctx func ce cx mid s` by fs[expr_post_def] >>
  `s.vs_alloca_next < dimword (:256)` by
    (drule stmt_state_rel_alloca_room >> MATCH_ACCEPT_TAC alloca_room_next_lt) >>
  `w2n dw + sz <= s.vs_alloca_next` by
    (drule stmt_state_rel_local_ptrs_alloca >>
     pure_rewrite_tac[alloca_inv_def,alloca_next_valid_def] >> strip_tac >>
     first_x_assum drule >> simp[]) >>
  qexistsl_tac [`xs`,`sw`] >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >> conj_tac
  >- (strip_tac >> irule ann_copy_live_bytes >>
      `type_memory_size rt <= sz` by decide_tac >> simp[] >>
      qexistsl_tac [`get_tenv cx`,`typ`] >> simp[]) >>
  suspend "typed"
QED

Resume ann_copy_source_ready_mods[typed]:
  disch_tac >>
  `eval_operand op s = SOME sw` by simp[eval_operand_def] >>
  `w2n sw + type_memory_size rt <= s.vs_alloca_next` by
    (Cases_on `is_bytestring_type typ`
     >- (qpat_assum `_ /\ _ ==> !tv w. _` mp_tac >>
         impl_tac >- fs[] >> disch_then drule_all >> simp[] >> decide_tac) >>
     `~is_bytestring_type (lowered_value_type ce e)` by
       (strip_tac >> drule_all type_widens_from_bytestring >> simp[]) >>
     drule_all val_store_size_non_bytestring >> disch_then (qspec_then `v` assume_tac) >>
     gvs[]) >>
  `w2n sw + type_memory_size rt < dimword (:256)` by decide_tac >>
  `expr_val_at ce cx (lowered_value_type ce e) a b mid v op s` by
    (`expr_val_at ce cx (post_value_type ce e) a b mid v op s` by
       (qpat_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`
          (strip_assume_tac o PURE_REWRITE_RULE [expr_post_def]) >>
        first_assum ACCEPT_TAC) >>
     irule ann_copy_physical_origin >>
     conj_tac >- (qexists_tac `rt` >> simp[]) >>
     qexistsl_tac [`pt`,`post_value_type ce e`] >> asm_rewrite_tac[]) >>
  `inst.inst_id < b.cs_next_id` by
    (drule (cj 2 compile_expr_grows) >> strip_tac >> decide_tac) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >> conj_tac
  >- (disch_tac >>
      qpat_assum `op = Var xs` SUBST_ALL_TAC >> asm_rewrite_tac[]) >>
  disch_tac >>
  `~is_bytestring_type typ` by fs[] >>
  irule ann_copy_nonmemory_separate >>
  conj_tac >- first_assum ACCEPT_TAC >>
  goal_assum (drule_at (Pat `expr_val_at _ _ _ _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `stmt_state_rel _ _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `FLOOKUP _ _ = SOME (w2n dw,sz)`)) >> simp[] >>
  qexists_tac `typ` >> simp[]
QED

Finalise ann_copy_source_ready_mods
