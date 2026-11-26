(* Windows for the reached operand of a linked, buffered Return. *)
Theory bodySelectedBufferReturnInputsMods
Ancestors
  bodyFullPostsMods bodyFullShared bodyInvCodeProps bodyFullIntCallBufferedCopy
  internalReturnMemoryInputs externalReturnCopyRecursive externalNormalizePremises
  exprOperandVar stmtSimReturn stateRelProj aggregateEvaluatedLayout
  placeMemoryTypeInterfaces typedMemoryCopy valueTypingMemoryProps valueCopyBytes
  exprSimHypsDefs vyperTypeSystem loweringPosts bodyFullShadowBodyInv bodyPtrDefs
  exprLoweringProps loweringStateRelDefs venomState

Theorem selected_return_copy_layout_mods[local]:
  expr_sim_inv_mods mods cenv cx env es ==>
  sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
  (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(nm,ty,sz). !tv. evaluate_type (get_tenv cx) ty = SOME tv ==>
      sz = type_memory_size tv) fields) /\
  (!ty tv. evaluate_type (get_tenv cx) ty = SOME tv ==>
    type_memory_bytes cenv ty = type_memory_size tv)
Proof
  simp[expr_sim_inv_mods_def] >> strip_tac >>
  conj_tac >- first_assum ACCEPT_TAC >>
  rpt gen_tac >> strip_tac >>
  irule return_copy_memory_size >>
  goal_assum (drule_at Any) >> simp[] >>
  rpt gen_tac >> disch_tac >>
  qpat_assum `!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==> _`
    (drule_then (ACCEPT_TAC o cj 2))
QED

Theorem selected_return_source_size[local]:
  type_widens_to tenv sty ty /\ evaluate_type tenv sty = SOME stv /\
  evaluate_type tenv ty = SOME tv /\ 0 < type_memory_size tv ==>
  0 < type_memory_size stv /\ type_memory_size stv <= type_memory_size tv
Proof
  strip_tac >> conj_tac
  >- (drule_all type_widens_to_zero_memory_size >> simp[]) >>
  gvs[type_widens_to_def] >>
  drule (cj 1 arg_fits_evaluated_memory_size) >>
  disch_then (qspecl_then [`tenv`,`stv`,`tv`] mp_tac) >> simp[]
QED

(* Only the non-bytestring convention uses a full source-capacity bound
   and disjoint source/destination windows. *)
Theorem selected_return_disjoint_windows[local]:
  type_widens_to (get_tenv cx) sty ty /\ ~is_word_type sty /\
  evaluate_type (get_tenv cx) sty = SOME stv /\ value_has_type stv v /\
  0 < type_memory_size stv /\
  (post_value_type cenv e = sty \/
   is_bytestring_type (post_value_type cenv e) /\ is_bytestring_type sty) /\
  expr_post H ctx func cenv cx e es sa sm s0 ee v op t /\
  stmt_state_rel H ctx func cenv cx es s0 /\ local_ptrs_reserved cenv sa /\
  return_buf_sep (SOME (bw,cap)) cenv es s0 /\
  allocas_from (w2n bw + cap) t /\ eval_operand op t = SOME sw /\
  ~is_bytestring_type ty ==>
  w2n sw + type_memory_size stv <= t.vs_alloca_next /\
  (w2n sw + type_memory_size stv <= w2n bw \/
   w2n bw + cap <= w2n sw)
Proof
  strip_tac >>
  `~is_bytestring_type sty` by metis_tac[type_widens_from_bytestring] >>
  `stmt_state_rel H ctx func cenv cx ee t /\
   expr_val_at cenv cx sty sa sm ee v op t /\
   MAP FDOM ee.scopes = MAP FDOM es.scopes /\
   (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
          lookup_var x t = SOME w)` by
    (qpat_assum `post_value_type _ _ = sty` (SUBST1_TAC o SYM) >>
     fs[expr_post_def, locals_kept_def]) >>
  conj_tac
  >- (drule_all normalize_source_window >> simp[]) >>
  `return_buf_sep (SOME (bw,cap)) cenv ee t` by
    (irule return_buf_sep_locals_kept >>
     simp[SimpLHS] >> conj_tac >- fs[arithmeticTheory.ADD_COMM] >>
     qexistsl [`H`,`ctx`,`cx`,`es`,`func`,`s0`,`sa`] >> simp[]) >>
  drule_all intcall_widened_return_source_disjoint >> simp[]
QED

Theorem selected_buffer_return_inputs_mods:
  contract_inv mods exps ctx cenv cx /\ expr_sim_inv_mods mods cenv cx env es /\
  lower_value compile_expr cenv ty e sa = (op,sm) /\
  compile_return_unlock cenv sm = ((),su) /\
  cenv.ce_return_pc = SOME (PtrVar (Var rpc) rsz) /\
  local_ptrs_reserved cenv sa /\ ret_pc_ok cenv sa s0 /\
  return_buf_frame (SOME (bw,type_memory_size tv)) cenv sa s0 /\
  return_buf_sep (SOME (bw,type_memory_size tv)) cenv es s0 /\
  allocas_from (w2n bw + type_memory_size tv) t /\
  s0.vs_alloca_next <= t.vs_alloca_next /\
  stmt_state_rel H ctx func cenv cx es s0 /\
  expr_post_mods H ctx func cenv cx e es sa sm s0 ee v op t /\
  ghost_inv_at_mods D lo (SOME (bw,type_memory_size tv)) cenv cx ee G tn t /\
  ptr_val_ok cx (post_value_type cenv e) v op G tn t /\
  (~is_word_type (post_value_type cenv e) ==> ptr_buf_ok cenv e op G t) /\
  expr_store_bound cx (post_value_type cenv e) v op t /\
  evaluate_type (get_tenv cx) (lowered_value_type cenv e) = SOME stv /\
  evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME ptv /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  value_has_type stv v /\ value_has_type ptv v /\ value_has_type tv v /\
  type_widens_to (get_tenv cx) (lowered_value_type cenv e) ty /\
  (post_value_type cenv e = lowered_value_type cenv e \/
   is_bytestring_type (post_value_type cenv e) /\
   is_bytestring_type (lowered_value_type cenv e)) /\
  ~is_word_type ty /\ 0 < type_memory_size tv /\
  type_memory_size tv + 64 < dimword (:256) /\
  ((FST cenv.ce_nonreentrant /\ ~SND (SND (SND cenv.ce_nonreentrant))) ==>
    ~cx.txn.is_static) ==>
  ?src bp bsz sw pc.
    op = Var src /\ cenv.ce_return_buf = SOME (PtrVar (Var bp) bsz) /\
    lookup_var src t = SOME sw /\ lookup_var bp t = SOME bw /\
    lookup_var rpc t = SOME pc /\
    not_fresh_at su src /\ not_fresh_at su bp /\ not_fresh_at su rpc /\
    ptr_covers G tn src t (type_memory_size stv) /\
    ptr_covers G tn bp t (type_memory_size tv) /\ op_taint tn (Var rpc) = {} /\
    (FST cenv.ce_nonreentrant /\ ~SND (SND (SND cenv.ce_nonreentrant)) ==>
     ~t.vs_call_ctx.cc_static) /\
    (!m. mem_agree_outside tn.t_mem t.vs_memory m ==>
         val_in_memory stv v (w2n sw) m) /\
    w2n sw + val_store_size stv v <= t.vs_alloca_next /\
    w2n bw + type_memory_size tv <= t.vs_alloca_next /\
    t.vs_alloca_next < dimword (:256) /\
    w2n sw + val_store_size stv v < dimword (:256) /\
    w2n bw + type_memory_size tv < dimword (:256) /\
    (~is_bytestring_type ty ==>
      w2n sw + type_memory_size stv <= t.vs_alloca_next /\
      (w2n sw + type_memory_size stv <= w2n bw \/
       w2n bw + type_memory_size tv <= w2n sw)) /\
    (is_bytestring_type ty ==> is_bytestring_type (lowered_value_type cenv e)) /\
    0 < type_memory_size stv /\ type_memory_size stv <= type_memory_size tv /\
    type_memory_size stv + 64 < dimword (:256) /\
    type_memory_bytes cenv (lowered_value_type cenv e) = type_memory_size stv /\
    type_memory_bytes cenv ty = type_memory_size tv /\
    val_wf stv v /\ val_wf tv v /\ allocas_from lo t /\ lo <= t.vs_alloca_next /\
    immutable_frame_mods func cenv cx ee t /\
    acyclic_struct_metadata cenv.ce_struct_fields /\
    sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
    (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
      ALL_DISTINCT (MAP FST fields) /\
      EVERY (\(nm,fty,sz). !ftv. evaluate_type (get_tenv cx) fty = SOME ftv ==>
        sz = type_memory_size ftv) fields)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_then strip_assume_tac selected_return_copy_layout_mods >>
  drule_then assume_tac contract_inv_acyclic_struct_metadata >>
  `0 < type_memory_size stv /\ type_memory_size stv <= type_memory_size tv` by
    (drule_all selected_return_source_size >> simp[]) >>
  `~is_word_type (lowered_value_type cenv e)` by
    metis_tac[return_source_word_widens_eq] >>
  `~is_word_type (post_value_type cenv e)` by
    metis_tac[is_bytestring_word_type] >>
  qpat_assum `expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [expr_post_mods_def]) >>
  `?src sw. op = Var src /\ lookup_var src t = SOME sw /\
    ptr_covers G tn src t (type_memory_size stv) /\
    (!m. mem_agree_outside tn.t_mem t.vs_memory m ==>
         val_in_memory stv v (w2n sw) m) /\
    w2n sw + val_store_size stv v <= t.vs_alloca_next` by
    (qpat_assum `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`
      (mp_then Any mp_tac internal_return_memory_value_inputs_lowered) >>
     disch_then (qspecl_then [`G`,`tn`,`lowered_value_type cenv e`,
                             `post_value_type cenv e`,`stv`,`ptv`] mp_tac) >>
     simp[]) >>
  qpat_assum `return_buf_frame _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [return_buf_frame_def]) >>
  rename1 `cenv.ce_return_buf = SOME (PtrVar (Var bp) bsz)` >>
  `not_fresh_at sa rpc /\ ?pc. lookup_var rpc t = SOME pc` by
    (fs[ret_pc_ok_def, expr_post_def] >> metis_tac[]) >>
  `lookup_var bp t = SOME bw` by fs[expr_post_def] >>
  `ptr_covers G tn bp t (type_memory_size tv) /\ op_taint tn (Var rpc) = {} /\
   allocas_from lo t /\ lo <= t.vs_alloca_next` by
    fs[ghost_inv_at_mods_def, return_buf_ptr_def] >>
  `stmt_state_rel H ctx func cenv cx ee t` by fs[expr_post_def] >>
  `t.vs_alloca_next < dimword (:256)` by
    (drule stmt_state_rel_alloca_room >> metis_tac[alloca_room_next_lt]) >>
  `(FST cenv.ce_nonreentrant /\ ~SND (SND (SND cenv.ce_nonreentrant)) ==>
    ~t.vs_call_ctx.cc_static)` by
    (qpat_assum `stmt_state_rel _ _ _ _ _ ee t`
       (mp_then Any assume_tac stmt_state_rel_state_rel) >>
     drule state_rel_call_ctx_rel >> simp[call_ctx_rel_def]) >>
  `sa.cs_next_var <= sm.cs_next_var /\ su.cs_next_var = sm.cs_next_var` by
    metis_tac[compile_expr_grows, compile_return_unlock_shape] >>
  `not_fresh_at sm src` by
    (drule_all compile_lower_value_var >> simp[]) >>
  `not_fresh_at su src /\ not_fresh_at su bp /\ not_fresh_at su rpc` by
    fs[not_fresh_at_def, GSYM arithmeticTheory.LESS_EQ_TRANS] >>
  `~is_bytestring_type ty ==>
   w2n sw + type_memory_size stv <= t.vs_alloca_next /\
   (w2n sw + type_memory_size stv <= w2n bw \/
    w2n bw + type_memory_size tv <= w2n sw)` by
    (strip_tac >>
     `eval_operand op t = SOME sw` by simp[eval_operand_def] >>
     drule_all selected_return_disjoint_windows >> simp[]) >>
  qexistsl [`src`,`bp`,`bsz`,`sw`,`pc`] >>
  simp[value_has_type_memory_wf] >>
  rpt conj_tac
  >~ [`is_bytestring_type ty ==> _`]
  >- (drule typed_copy_bytestring_source >> simp[]) >>
  first_assum ACCEPT_TAC
QED
