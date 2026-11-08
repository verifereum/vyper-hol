(* Physical RHS reading for immutable stores.  Rebase at the read suffix:
   this also handles internal calls whose physical and annotated types differ. *)
Theory immutableAssignReadiness
Ancestors
  exprSimAggregateBodyCounted exprSimAggregateSource exprSimUnwrapProps
  exprSimHypsDefs loweringPosts compileEnv fragGasMode fragGasPath
  vyperInterpreter vyperState immutableDeployPhysicalSource immutableDeploySourceAge
  immutableDeployAssignRanges valueTypingMemoryProps exprSimOperands
  annassignRelayoutSource exprSimTypedAlloc placeMemoryTypeInterfaces
  vyperTypeSystem vyperTypeArgFits vyperTypeInvariants
  placeStoreStorage valueEncodingProps exprSimProps exprSimHyps
Libs monadsyntax

Theorem immutable_assign_rhs_read:
  compile_expr ce ty e si = (vv,sj) /\
  expr_body_pre ce cx env e es /\
  unwrap_value ce vv sm = (op,su) /\ local_ptrs_reserved ce sm /\
  sa.cs_next_id <= sm.cs_next_id /\
  vv_post ctx func ce cx e es sa sm s0 ee tv vv r /\
  fn_has_code sm su func /\ fn_inst_ids_distinct func /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  ~r.vs_halted /\ r.vs_current_bb = sm.cs_current_bb /\
  r.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?v u. read_result cx tv ee = (INL v,ee) /\
    gas_marked_path F ctx func r 0 (OK u) /\
    expr_post ctx func ce cx e ee
      (sa with cs_next_var := sm.cs_next_var) su r ee v op u /\
    ~u.vs_halted /\ u.vs_current_bb = su.cs_current_bb /\
    u.vs_inst_idx = LENGTH su.cs_current_insts
Proof
  strip_tac >> drule vv_post_materialises >> strip_tac >>
  drule_all unwrap_value_body_rebased_path >> strip_tac >>
  qexistsl_tac [`v`, `u`] >> simp[]
QED

(* Normalization uses the physical RHS type, not the annotation.  Its source
   predates the allocation emitted at sa, including when unwrap allocated. *)
Theorem immutable_assign_normalization_ready:
  expr_body_pre ce cx env e es /\
  (do pv <- eval_expr cx e; read_result cx pv od) es = (INL v,ee) /\
  expr_post ctx func ce cx e ers si sa s0 ee v op s /\
  type_widens_to env.type_defs (expr_type e) dty /\
  supported_value_type tops dty /\
  lowered_value_type ce e <> dty /\
  ~is_word_type (lowered_value_type ce e) /\
  ~is_bytestring_type (lowered_value_type ce e) /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  compile_alloc_buffer cap sa = (buf,mid) /\ fn_has_code sa mid func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved ce sa ==>
  ?stv sw. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME stv /\
    value_has_type stv v /\ val_wf stv v /\
    type_memory_bytes ce (lowered_value_type ce e) = type_memory_size stv /\
    type_widens_to (get_tenv cx) (lowered_value_type ce e) dty /\
    eval_operand op s = SOME sw /\
    val_in_memory stv v (w2n sw) s.vs_memory /\
    0 < type_memory_size stv /\ 0 < type_memory_size dtv /\
    w2n sw + type_memory_size stv < dimword (:256) /\
    w2n sw + type_memory_size stv <= s.vs_alloca_next /\
    (!b sz. FLOOKUP s.vs_allocas sa.cs_next_id = SOME (b,sz) ==>
      w2n sw + type_memory_size stv <= b \/ b + sz <= w2n sw)
Proof
  strip_tac >> drule_all immutable_rhs_physical_typed >> strip_tac >>
  drule_all immutable_rhs_physical_widens >> strip_tac >>
  `post_value_type ce e = lowered_value_type ce e` by
    metis_tac[immutable_rhs_post_physical_classify] >>
  `0 < type_memory_size stv /\ 0 < type_memory_size dtv` by
    metis_tac[immutable_supported_normalization_positive] >>
  `stmt_state_rel ctx func ce cx ee s /\
   expr_val_at ce cx (lowered_value_type ce e) si sa ee v op s /\
   expr_val_rel cx (lowered_value_type ce e) v op s` by fs[expr_post_def] >>
  `?sw. eval_operand op s = SOME sw /\
    val_in_memory stv v (w2n sw) s.vs_memory` by
    (fs[expr_val_rel_def] >> metis_tac[]) >>
  drule_all immutable_rhs_normalization_source_range >> strip_tac >>
  `val_footprint stv v = type_memory_size stv` by
    metis_tac[nonbytes_evaluated_val_footprint] >>
  `w2n sw + type_memory_size stv < dimword (:256)` by
    metis_tac[expr_val_at_bound] >>
  qexistsl_tac [`stv`, `sw`] >> simp[]
QED

(* The direct copier rounds its destination writes to whole words.  The
   rounded span stays within the declared destination, not merely its value. *)
Theorem immutable_assign_direct_window:
  type_widens_to tenv sty dty /\
  evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
  (sty = dty \/ is_bytestring_type sty /\ is_bytestring_type dty) /\
  0 < type_memory_size stv /\ value_has_type stv v /\ val_wf stv v /\
  val_in_memory stv v a mem /\
  copy_size = (if is_bytestring_type dty then type_memory_size stv
               else type_memory_size dtv) /\
  n = (if copy_size <= 32 then 1 else (copy_size+31) DIV 32) ==>
  val_footprint stv v <= 32*n /\ 32*n <= type_memory_size dtv
Proof
  strip_tac >>
  `type_memory_size stv <= type_memory_size dtv` by
    (Cases_on `sty = dty` >- gvs[] >> gvs[] >>
     drule_all place_store_bytestring_representation >> strip_tac >>
     `word_size src_cap <= word_size dst_cap` by
       metis_tac[word_size_monotone] >>
     gvs[valueEncodingTheory.type_memory_size_def]) >>
  `val_footprint stv v <= type_memory_size stv` by metis_tac[val_footprint_le] >>
  Cases_on `is_bytestring_type dty` >> gvs[] >>
  gvs[type_memory_size_slots, arithmeticTheory.MULT_DIV] >>
  rpt IF_CASES_TAC >> gvs[] >> decide_tac
QED

(* assignable_type is needed even on the equal-type path: supported_value_type
   alone admits an empty struct.  Transfer positivity backwards from annotation. *)
Theorem immutable_assign_physical_positive:
  expr_body_pre ce cx env e es /\ assignable_type env.type_defs (expr_type e) /\
  evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME stv ==>
  0 < type_memory_size stv
Proof
  strip_tac >>
  `env.type_defs = get_tenv cx` by
    fs[expr_body_pre_def, expr_sim_inv_def, env_consistent_def,
       env_context_consistent_def] >>
  `type_widens_to (get_tenv cx) (lowered_value_type ce e) (expr_type e)` by
    (irule immutable_rhs_physical_widens >> qexistsl_tac [`env`,`es`] >> simp[]) >>
  `?atv. evaluate_type (get_tenv cx) (expr_type e) = SOME atv` by
    (drule assignable_type_well_formed >>
     simp[well_formed_type_def, optionTheory.IS_SOME_EXISTS]) >>
  `0 < type_slot_size atv` by metis_tac[assignable_type_slot_size_pos] >>
  drule_all type_widens_to_zero_memory_size >>
  simp[type_memory_size_slots]
QED
