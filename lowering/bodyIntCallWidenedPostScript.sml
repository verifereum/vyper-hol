Theory bodyIntCallWidenedPost
Ancestors
  bodyIntCallRestoreResults valueCopyBytes vyperTypeArgFits
  loweringPosts exprLowering compileEnv vyperInterpreter vyperState
  valueTypingMemoryProps

Theorem widened_allocated_buffer_post:
  ce.ce_func_return_type (nsid_to_string (NONE,name)) = cty /\
  type_widens_to (get_tenv cx) cty ann /\ ~is_word_type ann /\
  (is_bytestring_type ann ==> is_bytestring_type cty) /\
  evaluate_type (get_tenv cx) cty = SOME tv /\ value_has_type tv v /\
  stmt_state_rel ctx func ce cx es' s /\ wb_frame ce es es' sa s0 s /\
  eval_operand buf.buf_operand s = SOME w /\
  val_in_memory tv v (w2n w) s.vs_memory /\
  FLOOKUP s.vs_allocas aid = SOME (b,sz) /\
  sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\
  b <= w2n w /\ w2n w + val_footprint tv v <= b + sz /\
  (!n lb lsz. local_region ce es'.scopes s n lb lsz ==>
    b + sz <= lb \/ lb + lsz <= b) ==>
  vv_post ctx func ce cx (Call ann (IntCall (NONE,name)) args dflt)
    es sa sb s0 es' (Value v) (LocatedValue cty (base_ptr buf)) s
Proof
  strip_tac >>
  `?ptv. evaluate_type (get_tenv cx)
      (post_value_type ce (Call ann (IntCall (NONE,name)) args dflt)) = SOME ptv /\
    value_has_type ptv v /\
    val_in_memory ptv v (w2n w) s.vs_memory /\
    val_footprint ptv v = val_footprint tv v` by
    (Cases_on `is_bytestring_type ann`
     >- (drule_all type_widens_to_value_has_type >> strip_tac >>
         simp[post_value_type_def] >> conj_tac
         >- (irule bytestring_val_in_memory_transfer >>
             goal_assum (drule_at Any) >> metis_tac[]) >>
         metis_tac[bytestring_val_footprint_eq]) >>
     simp[post_value_type_def, lowered_value_type_def] >> metis_tac[]) >>
  `~is_word_type (post_value_type ce
    (Call ann (IntCall (NONE,name)) args dflt))` by
    (Cases_on `is_bytestring_type ann` >>
     simp[post_value_type_def, lowered_value_type_def] >>
     fs[vyperTypeSystemTheory.type_widens_to_def] >>
     Cases_on `cty` >> Cases_on `ann` >>
     gvs[vyperTypeSystemTheory.arg_type_fits_def, is_word_type_def] >>
     rename1 `BaseT bt` >> Cases_on `bt` >>
     gvs[vyperTypeSystemTheory.arg_type_fits_def, is_word_type_def] >>
     Cases_on `b''` >>
     gvs[vyperTypeSystemTheory.arg_type_fits_def, is_word_type_def] >>
     rename1 `arg_type_fits (BaseT (BytesT k)) (BaseT (BytesT l))` >>
     Cases_on `k` >> Cases_on `l` >>
     gvs[vyperTypeSystemTheory.arg_type_fits_def, is_word_type_def]) >>
  simp[vv_post_def, wb_frame_def] >>
  rpt conj_tac
  >~ [`vv_holds`]
    >- (simp[vv_holds_def, contextTheory.base_ptr_def,
             read_result_def, return_def] >>
        conj_tac
        >- (Cases_on `is_bytestring_type ann` >>
            simp[post_value_type_def, lowered_value_type_def]) >>
        gvs[post_value_type_def] >> metis_tac[]) 
  >~ [`vv_at`]
    >- (simp[vv_at_def, contextTheory.base_ptr_def,
             read_result_def, return_def] >> rpt strip_tac >> gvs[] >>
        TRY (metis_tac[value_has_type_memory_wf]) >>
        disj1_tac >> goal_assum (drule_at Any) >> metis_tac[])
  >~ [`vv_own`]
    >- (simp[vv_own_def, contextTheory.base_ptr_def,
             read_result_def, return_def] >> rpt strip_tac >> gvs[] >>
        disj1_tac >> goal_assum (drule_at Any) >> metis_tac[]) >>
  fs[wb_frame_def]
QED
