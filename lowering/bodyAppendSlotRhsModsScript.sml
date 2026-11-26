(* Inputs to the emitted Append scratch copy, after reaching the target
   and then lowering and reading its RHS. *)
Theory bodyAppendSlotRhsMods
Ancestors
  bodyWriteTargetStageMods bodyAnnNonwordReadTypesMods bodyAppendStorageFacts
  vyperTypeValues vyperTypeEvalCaseProofs vyperTyping exprBodyPreProps
  exprOperandVar assignBasePtrBoundary valueCopyBytes valueTypingMemoryProps
  bodyDeclCopyMemory bodyFullPostsMods exprSimMemDefs bodyPtrDefs
  bodyFullShadowBodyInv exprLoweringProps stateRelProj allocLimits
  loweringPosts freshWrites ptrDiscipline venomState words arithmetic
  exprSimProps valueEncodingProps bodySim exprLowering vyperValue vyperAST
  stmtSimAugAssignPlace compileEnv context targetPlaceSim

Theorem append_rhs_local_base_transport[local]:
  local_val_at cenv cx n k (BaseTV b1) v /\ val_wf (BaseTV b1) v /\
  val_footprint (BaseTV b1) v = val_footprint (BaseTV b2) v ==>
  local_val_at cenv cx n k (BaseTV b2) v
Proof
  simp[local_val_at_def] >> rpt strip_tac >> disj2_tac
  >- (qexists_tac `b1` >> simp[] >> metis_tac[val_footprint_le]) >>
  qexists_tac `bt0` >> simp[]
QED

Theorem append_rhs_physical_at[local]:
  evaluate_type (get_tenv cx) pt = SOME ptv /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  value_has_type ptv v /\ value_has_type stv v /\
  (pt = sty \/ is_bytestring_type pt /\ is_bytestring_type sty) /\
  expr_val_at cenv cx pt sp sm fin v op u ==>
  expr_val_at cenv cx sty sp sm fin v op u
Proof
  strip_tac >> Cases_on `pt = sty` >- fs[] >> fs[] >>
  `val_footprint ptv v = val_footprint stv v` by
    metis_tac[bytestring_val_footprint_eq] >>
  `!n k. local_val_at cenv cx n k ptv v ==> local_val_at cenv cx n k stv v` by
    (`?b1. ptv = BaseTV b1` by metis_tac[bytestring_type_value] >>
     `?b2. stv = BaseTV b2` by metis_tac[bytestring_type_value] >>
     gvs[] >> metis_tac[append_rhs_local_base_transport,value_has_type_memory_wf]) >>
  qpat_x_assum `expr_val_at _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[expr_val_at_def,value_has_type_memory_wf,is_bytestring_word_type] >>
  disch_then (qx_choose_then `w` strip_assume_tac) >> qexists_tac `w` >> simp[]
  >- (disj1_tac >> qexistsl_tac [`aid`,`b`,`sz`] >> simp[] >> first_assum ACCEPT_TAC) >>
  disj2_tac >> disj1_tac >> qexistsl_tac [`n`,`b`,`sz`] >> simp[]
QED

Theorem append_rhs_operand[local]:
  evaluate_type (get_tenv cx) pt = SOME ptv /\
  evaluate_type (get_tenv cx) sty = SOME stv /\
  value_has_type ptv v /\ value_has_type stv v /\
  ~is_word_type pt /\
  (pt = sty \/ is_bytestring_type pt /\ is_bytestring_type sty) /\
  expr_val_rel cx pt v op u /\ ptr_val_ok cx pt v op G tn u /\
  expr_store_bound cx pt v op u /\ u.vs_alloca_next < dimword (:256) /\
  0 < type_memory_size stv ==>
  ?w. eval_operand op u = SOME w /\ op_taint tn op = {} /\
    (!mem. mem_agree_outside tn.t_mem u.vs_memory mem ==>
       val_in_memory stv v (w2n w) mem) /\
    w2n w + val_store_size stv v <= u.vs_alloca_next /\
    w2n w + val_store_size stv v < dimword (:256)
Proof
  strip_tac >>
  `?w. eval_operand op u = SOME w` by fs[expr_val_rel_def] >>
  `op_taint tn op = {} /\ (!mem. mem_agree_outside tn.t_mem u.vs_memory mem ==>
      val_in_memory ptv v (w2n w) mem)` by fs[ptr_val_ok_def,ptr_mem_ok_def] >>
  `val_store_size ptv v = val_store_size stv v` by
    (Cases_on `pt = sty` >- gvs[] >> fs[] >> metis_tac[bytestring_val_store_size_eq]) >>
  `0 < val_store_size stv v` by simp[val_store_size_pos] >>
  `w2n w + val_store_size stv v <= u.vs_alloca_next` by
    (qpat_assum `expr_store_bound _ _ _ _ _`
       (mp_tac o REWRITE_RULE [expr_store_bound_def]) >>
     disch_then (qspecl_then [`ptv`,`w`] mp_tac) >> simp[]) >>
  `w2n w + val_store_size stv v < dimword (:256)` by decide_tac >>
  qexists_tac `w` >> simp[] >>
  (Cases_on `pt = sty` >- gvs[] >> fs[] >> metis_tac[bytestring_val_in_memory_transfer])
QED

Theorem append_slot_target_not_label[local]:
  compile_get_target_ptr cfn cenv bt sa = (r,sp) /\
  FST (SND r) = SOME (slot_loc tr) ==> !l. FST r <> Label l
Proof
  Cases_on `bt`
  >~ [`NameTarget id`]
  >- (simp[compile_get_target_ptr_def] >>
      Cases_on `FLOOKUP cenv.ce_vars id` >> simp[comp_return_def, slot_loc_def] >>
      rename1 `FLOOKUP cenv.ce_vars id = SOME entry` >>
      Cases_on `entry` >> Cases_on `tr` >> simp[comp_return_def, slot_loc_def] >>
      rpt strip_tac >> gvs[])
  >~ [`TopLevelNameTarget key`]
  >- (simp[compile_get_target_ptr_def] >>
      Cases_on `FLOOKUP cenv.ce_module_vars key` >> simp[comp_return_def] >>
      rename1 `FLOOKUP cenv.ce_module_vars key = SOME entry` >>
      Cases_on `entry` >> simp[comp_return_def] >> rpt strip_tac >> gvs[]) >>
  strip_tac >> drule aug_place_target_ptr_not_label >> simp[]
QED

(* Both identity and materializing RHS runs supply expr_post_mods at sm.
   A raw qualified LocCode result is not an input to this rule: the
   read/lowering post already refers to the actual unwrapped operand. *)
Theorem append_slot_rhs_input_mods:
  write_target_post_mods Ht Dt lo d ctx func cenv cx bt es sa sp s0 reached
    (PlaceR (StoragePlace tr slot (ArrayTV tv (Dynamic cap))))
    (Type (ArrayT elem (Dynamic cap))) r G0 tn0 Gp tp s /\
  compile_get_target_ptr compile_expr cenv bt sa = (r,sp) /\
  expr_body_pre_mods mods cenv cx env e reached /\
  bind (eval_expr cx e) (read_result cx) (reached with gas_obs := gs) = (INL v,fin) /\
  type_widens_to env.type_defs (expr_type e) elem /\ ~is_word_type elem /\
  stmt_exprs_ok cenv (Append bt e) /\
  target_place_type cenv bt = SOME (ValPT (ArrayT elem (Dynamic cap))) /\
  lower_value compile_expr cenv elem e sp = (op,sm) /\ local_ptrs_reserved cenv sp /\
  expr_post_mods H ctx func cenv cx e reached sp sm s fin v op u /\
  ghost_inv_at_mods D lo d cenv cx fin G tn u /\
  ghost_kept_at lo cenv reached sp Gp tp s G tn /\
  expr_store_bound cx (post_value_type cenv e) v op u /\
  ptr_val_ok cx (post_value_type cenv e) v op G tn u /\
  (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e op G u) /\
  ~u.vs_halted /\ u.vs_current_bb = sm.cs_current_bb /\
  u.vs_inst_idx = LENGTH sm.cs_current_insts /\ alloca_history func u ==>
  eval_operand (FST r) u = SOME slot /\ op_taint tn (FST r) = {} /\
  op_prov G (FST r) = NONE /\ (!x. FST r = Var x ==> not_fresh_at sm x) /\
  FST (SND r) = SOME (slot_loc tr) /\ SND (SND r) = SOME (ValPT (ArrayT elem (Dynamic cap))) /\
  stmt_state_rel H ctx func cenv cx fin u /\ storage_well_formed_on cx fin (FST H) /\
  immutable_frame_mods func cenv cx fin u /\ allocas_from lo u /\ lo <= u.vs_alloca_next /\
  ~u.vs_halted /\ u.vs_current_bb = sm.cs_current_bb /\
  u.vs_inst_idx = LENGTH sm.cs_current_insts /\ alloca_history func u /\
  local_ptrs_reserved cenv sm /\
  evaluate_type (get_tenv cx) elem = SOME tv /\ well_formed_type_value tv /\
  0 < type_slot_size tv /\ cap < dimword (:256) /\
  type_memory_bytes cenv elem = type_memory_size tv /\
  type_memory_size tv + 64 < dimword (:256) /\ value_has_type tv v /\ val_wf tv v /\
  ?stv xs sw writes.
    encode_value tv v = SOME writes /\
    ~is_word_type (lowered_value_type cenv e) /\
    type_widens_to (get_tenv cx) (lowered_value_type cenv e) elem /\
    evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME stv /\
    type_memory_bytes cenv (lowered_value_type cenv e) = type_memory_size stv /\
    0 < type_memory_size stv /\ type_memory_size stv <= type_memory_size tv /\
    value_has_type stv v /\ val_wf stv v /\
    expr_val_at cenv cx (lowered_value_type cenv e) sp sm fin v op u /\
    op = Var xs /\ not_fresh_at sm xs /\ lookup_var xs u = SOME sw /\
    op_taint tn op = {} /\ ptr_covers G tn xs u (type_memory_size stv) /\
    w2n sw + val_store_size stv v <= u.vs_alloca_next /\
    w2n sw + val_store_size stv v < dimword (:256) /\
    (!mem. mem_agree_outside tn.t_mem u.vs_memory mem ==>
      val_in_memory stv v (w2n sw) mem)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_then strip_assume_tac write_target_storage_view_mods >>
  drule_then strip_assume_tac write_target_post_view_mods >>
  `evaluate_type (get_tenv cx) elem = SOME tv /\ 0 < type_slot_size tv /\
   cap < dimword (:256)` by suspend "array" >>
  `well_formed_type_value tv` by metis_tac[evaluate_type_well_formed_type_value] >>
  drule_then assume_tac expr_body_pre_mods_inv >>
  drule_then assume_tac expr_sim_inv_mods_env >>
  drule_then assume_tac env_consistent_type_defs_get_tenv >>
  `type_widens_to (get_tenv cx) (expr_type e) elem` by fs[] >>
  drule_all_then (map_every assume_tac o CONJUNCTS) ann_copy_nonword_layout_mods >>
  `0 < type_memory_size tv` by simp[type_memory_size_slots] >>
  drule_all_then strip_assume_tac ann_copy_nonword_read_types_mods >>
  `type_memory_size tv + 64 < dimword (:256)` by suspend "alloc" >>
  `?writes. encode_value tv v = SOME writes` by
    (rewrite_tac[GSYM optionTheory.IS_SOME_EXISTS] >>
     irule (cj 1 value_has_type_equiv) >> first_assum ACCEPT_TAC) >>
  `sp.cs_next_var <= sm.cs_next_var` by
    metis_tac[ci_mono_lower_value_compile_expr,ci_mono_def,pairTheory.SND] >>
  `local_ptrs_reserved cenv sm` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sp` >> simp[]) >>
  `!x. FST r = Var x ==> not_fresh_at sm x` by metis_tac[not_fresh_at_mono] >>
  qhdtm_x_assum `expr_post_mods`
    (map_every assume_tac o CONJUNCTS o REWRITE_RULE [expr_post_mods_def,expr_post_def]) >>
  `eval_operand (FST r) u = SOME slot /\ op_taint tn (FST r) = {} /\
   op_prov G (FST r) = NONE` by suspend "saved" >>
  `allocas_from lo u /\ lo <= u.vs_alloca_next` by fs[ghost_inv_at_mods_def] >>
  asm_rewrite_tac[value_type_place_def] >> suspend "operand"
QED

Resume append_slot_rhs_input_mods[array]:
  qpat_x_assum `evaluate_type _ (ArrayT elem _) = _` mp_tac >>
  pure_once_rewrite_tac[evaluate_type_def] >>
  simp[AllCaseEqs(),LET_THM,bound_length_def] >> strip_tac >> gvs[] >>
  `cap <= cap * type_slot_size tv` by
    (Cases_on `type_slot_size tv` >> fs[arithmeticTheory.MULT_CLAUSES]) >>
  qpat_x_assum `type_slot_size (ArrayTV tv (Dynamic cap)) < _` mp_tac >>
  pure_rewrite_tac[type_slot_size_def,bound_length_def] >> decide_tac
QED

Resume append_slot_rhs_input_mods[alloc]:
  markerLib.RESUME_TAC >>
  qpat_x_assum `stmt_exprs_ok _ (Append _ _)` mp_tac >>
  simp[stmt_exprs_ok_def,alloc_limits_stmt_def,wordsTheory.dimword_def] >> decide_tac
QED

Resume append_slot_rhs_input_mods[saved]:
  drule_all_then assume_tac append_slot_target_not_label >>
  qpat_assum `!x w. not_fresh_at sp x /\ _ ==> _` mp_tac >>
  qpat_assum `!x. FST r = Var x ==> not_fresh_at sp x` mp_tac >>
  qpat_assum `ghost_kept_at lo cenv reached sp Gp tp s G tn` mp_tac >>
  qpat_assum `eval_operand (FST r) s = SOME slot` mp_tac >>
  qpat_assum `op_prov Gp (FST r) = NONE` mp_tac >>
  qpat_assum `op_taint tp (FST r) = {}` mp_tac >>
  Cases_on `FST r` >>
  pure_rewrite_tac[eval_operand_def,op_taint_def,op_prov_def,ghost_kept_at_def] >>
  rpt strip_tac >> gvs[] >>
  qpat_assum `!x. not_fresh_at sp x ==> FLOOKUP G x = _ /\ _`
    (drule_then strip_assume_tac) >> simp[]
QED

Resume append_slot_rhs_input_mods[operand]:
  `u.vs_alloca_next < dimword (:256)` by
    (drule stmt_state_rel_alloca_room >> disch_then (ACCEPT_TAC o MATCH_MP alloca_room_next_lt)) >>
  `expr_val_at cenv cx (lowered_value_type cenv e) sp sm fin v op u` by
    (irule append_rhs_physical_at >>
     qpat_assum `expr_val_at cenv cx (post_value_type cenv e) _ _ _ _ _ _` (irule_at Any) >>
     qpat_assum `evaluate_type _ (post_value_type cenv e) = SOME pt` (irule_at Any) >>
     qpat_assum `evaluate_type _ (lowered_value_type cenv e) = SOME rt` (irule_at Any) >> simp[]) >>
  drule_all_then (qx_choose_then `sw` strip_assume_tac) append_rhs_operand >>
  `?xs. op = Var xs /\ ptr_covers G tn xs u (type_memory_size rt)` by
    (irule ptr_buf_ok_read_covers >> simp[] >> qexistsl_tac [`cenv`,`e`] >> simp[]) >>
  `not_fresh_at sm xs` by
    (drule compile_lower_value_var >> disch_then (qspec_then `xs` mp_tac) >> simp[]) >>
  `lookup_var xs u = SOME sw` by fs[eval_operand_def] >>
  qexistsl_tac [`rt`,`xs`,`sw`,`writes`] >> simp[]
QED

Finalise append_slot_rhs_input_mods
