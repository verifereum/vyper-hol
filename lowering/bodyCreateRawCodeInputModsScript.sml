(* Select the qualified immutable backing a reached RawCreate byte string. *)
Theory bodyCreateRawCodeInputMods
Ancestors
  bodyLocalCopyPhysicalRhsMods bodyFullPostsMods bodyFullShadowBodyInv
  exprSimCopy exprOperandVar exprPtrUnwrapStorageShape exprLoweringProps
  reasonEndpointResourcesPtr exprSimConvertFromBytes representationCleanPtr
  bodyImmutableCopyMemory typeLayoutProps stateRelProj loweringStateRelDefs
  loweringPosts exprSimMemDefs valueCopyBytes valueEncodingProps memoryReadProps
  compileEnv finite_map words arithmetic venomState venomInst ptrDiscipline
  context bodyPtrDefs

Theorem raw_create_ctor_base[local]:
  stmt_state_rel H ctx func cenv cx ee t /\
  local_ptrs_reserved cenv a /\ ghost_inv_at_mods D lo d cenv cx ee G tn t /\
  lo <> 0 /\ cenv.ce_imm_alloca = SOME region ==>
  eval_operand region t = SOME 0w /\ copy_old_operand a region /\
  op_taint tn region = {} /\ op_prov G region = NONE
Proof
  strip_tac >>
  conj_tac
  >- (drule stmt_state_rel_immutable_base_zero >> simp[immutable_base_zero_def]) >>
  Cases_on `region` >> simp[copy_old_operand_def,op_taint_def,op_prov_def] >>
  conj_tac >- (drule_all local_ptrs_reserved_imm_base >> simp[]) >>
  fs[ghost_inv_at_mods_def,op_taint_def]
QED

Theorem raw_create_ctor_bytes[local]:
  (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
    val_in_memory (BaseTV (BytesT (Dynamic k))) (BytesV bs) q mem) ==>
  mload q t = n2w (LENGTH bs) /\ read_memory (q+32) (LENGTH bs) t = bs /\
  (!i. q <= i /\ i < q+32+LENGTH bs ==> i NOTIN tn.t_mem)
Proof
  strip_tac >>
  `val_in_memory (BaseTV (BytesT (Dynamic k))) (BytesV bs) q t.vs_memory` by
    (first_x_assum irule >> simp[mem_agree_outside_def]) >>
  qpat_x_assum `val_in_memory _ _ _ t.vs_memory`
    (strip_assume_tac o REWRITE_RULE [dynamic_bytes_memory_boundary]) >>
  simp[GSYM mem_word_at_eq_mload,read_memory_eq_mem_bytes_at] >>
  drule robust_val_in_memory_bytes_clean >> simp[] >> strip_tac >>
  gen_tac >> disch_tac >> Cases_on `i < q+32`
  >- (qpat_assum `!j. q <= j /\ j < q+32 ==> _` (qspec_then `i` irule) >> fs[]) >>
  qpat_assum `!j. q+32 <= j /\ _ ==> _` (qspec_then `i` irule) >> decide_tac
QED

Theorem raw_create_code_input_mods:
  compile_expr cenv (expr_type code) code sa = (vv,a) /\
  vv_post_mods H ctx func cenv cx code es sa a s ee raw vv t /\
  vv_location vv = SOME LocCode /\
  ptr_vv_ok cx (post_value_type cenv code) raw vv ee G tn t /\
  read_result cx raw ee = (INL (BytesV bs),ee) /\
  lowered_value_type cenv code = BaseT (BytesT (Dynamic k)) /\
  evaluate_type (get_tenv cx) (lowered_value_type cenv code) =
    SOME (BaseTV (BytesT (Dynamic k))) /\
  cap = type_memory_bytes cenv (lowered_value_type cenv code) /\
  32 + LENGTH bs <= cap /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv a /\
  ghost_inv_at_mods D lo d cenv cx ee G tn t /\
  (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
    ?val. read_result cx raw ee = (INL val,ee) /\
      !rt w. evaluate_type (get_tenv cx) (post_value_type cenv code) = SOME rt /\
        eval_operand (vv_operand vv) t = SOME w ==>
        w2n w + type_memory_size rt <= lo /\
        (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
          val_in_memory rt val (w2n w) mem)) ==>
  ?ownerSrc tops p tag w.
    ALOOKUP cenv.ce_modules ownerSrc = SOME tops /\
    vv = LocatedValue tag p /\ p.ptr_location = LocCode /\
    eval_operand p.ptr_operand t = SOME w /\
    copy_old_operand a p.ptr_operand /\
    op_taint tn p.ptr_operand = {} /\ op_prov G p.ptr_operand = NONE /\
    tag = BaseT (BytesT (Dynamic k)) /\
    cap = type_memory_size (BaseTV (BytesT (Dynamic k))) /\
    32 * ((type_memory_bytes cenv tag+31) DIV 32) = cap /\
    immutable_holds (cenv with ce_module := ownerSrc) cx tag (Value (BytesV bs)) w ee t /\
    (~cenv.ce_is_ctor ==>
      w2n w + cap <= LENGTH t.vs_data_section /\ w2n w + cap < dimword (:256) /\
      val_in_memory (BaseTV (BytesT (Dynamic k))) (BytesV bs) (w2n w) t.vs_data_section /\
      mem_word_at (w2n w) t.vs_data_section = n2w (LENGTH bs) /\
      mem_bytes_at (w2n w+32) (LENGTH bs) t.vs_data_section = bs) /\
    (cenv.ce_is_ctor ==>
      w2n w + cap <= lo /\
      (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
        val_in_memory (BaseTV (BytesT (Dynamic k))) (BytesV bs) (w2n w) mem) /\
      mload (w2n w) t = n2w (LENGTH bs) /\ read_memory (w2n w+32) (LENGTH bs) t = bs /\
      (!i. w2n w <= i /\ i < w2n w+32+LENGTH bs ==> i NOTIN tn.t_mem) /\
      (!region. cenv.ce_imm_alloca = SOME region ==>
        eval_operand region t = SOME 0w /\ copy_old_operand a region /\
        op_taint tn region = {} /\ op_prov G region = NONE))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `vv` >> gvs[vv_location_def,vv_operand_def] >>
  `lowered_value_type cenv code = expr_type code` by
    (irule compile_nonmemory_lowered_value_type >> simp[] >>
     goal_assum (drule_at Any) >> simp[]) >>
  `expr_type code = BaseT (BytesT (Dynamic k))` by fs[] >>
  `post_value_type cenv code = BaseT (BytesT (Dynamic k))` by
    simp[post_value_type_bytestring,is_bytestring_type_def] >>
  `evaluate_type (get_tenv cx) (post_value_type cenv code) =
     SOME (BaseTV (BytesT (Dynamic k)))` by simp[] >>
  `cenv.ce_is_ctor ==> ?val. read_result cx raw ee = (INL val,ee) /\
      !rt w. evaluate_type (get_tenv cx) (post_value_type cenv code) = SOME rt /\
        eval_operand p.ptr_operand t = SOME w ==>
        w2n w + type_memory_size rt <= lo /\
        (!mem. mem_agree_outside tn.t_mem t.vs_memory mem ==>
          val_in_memory rt val (w2n w) mem)` by simp[] >>
  drule_all_then strip_assume_tac local_copy_raw_code_source_mods >>
  drule_all_then assume_tac immutable_holds_read_value >>
  `copy_old_operand a p.ptr_operand` by
    (drule (cj 1 compiler_compile_var) >> simp[copy_old_operand_def,vv_operand_def]) >>
  `type_memory_bytes cenv (BaseT (BytesT (Dynamic k))) =
    type_memory_size (BaseTV (BytesT (Dynamic k)))` by
    (drule type_memory_bytes_base_evaluated >> simp[]) >>
  qpat_x_assum `_ = post_value_type cenv code` SUBST_ALL_TAC >>
  `immutable_holds (cenv with ce_module := src) cx (BaseT (BytesT (Dynamic k)))
     (Value (BytesV bs)) w ee t` by
    (qpat_assum `post_value_type cenv code = BaseT _` (fn eq =>
       qpat_assum `immutable_holds _ _ (post_value_type cenv code) (Value _) _ _ _`
         (ACCEPT_TAC o REWRITE_RULE [eq]))) >>
  qexistsl [`src`,`tops`,`w`] >>
  simp[body_immutable_copy_aligned_size] >>
  conj_tac
  >- (strip_tac >> fs[] >> drule_all immutable_holds_bounds >>
      fs[dynamic_bytes_memory_boundary]) >>
  strip_tac >> fs[] >>
  drule raw_create_ctor_bytes >> simp[] >> strip_tac >> simp[] >>
  `lo <> 0` by decide_tac >>
  `stmt_state_rel H ctx func cenv cx ee t` by fs[vv_post_mods_def] >>
  gen_tac >> disch_tac >> drule_all raw_create_ctor_base >> simp[]
QED
