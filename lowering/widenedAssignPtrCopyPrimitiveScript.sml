(* Primitive counted typed-copy paths for widened local assignment. *)
Theory widenedAssignPtrCopyPrimitive
Ancestors
  context valueEncodingDefs typedCopyPtr typedMemoryCopy bodyPtrBytestringBuiltinsConcatSuffix reasonMemoryEncoderPtr
  assignTuplePtrLoadStep calldataReconstruction representationCleanPtr
  assignBasePtrBytesPost assignBasePtrTypedBytesField annAssignPtrStage
  compileEnv emitHelper emitHelperProps bodyPtrDefs ptrDiscipline
  venomState venomExecSemantics valueEncoding valueEncodingProps
  fragGasPathPtr fragExec typedCopyAgreement finite_map pred_set words list arithmetic

Theorem widened_assign_typed_word_counted:
  !ctx PG D fn cenv dst src dty sty sa sb G tn s dw sw tenv tv v.
    compile_store_memory_typed cenv (Var dst) dty (Var src) sty sa = ((),sb) /\
    is_word_type dty /\ evaluate_type tenv dty = SOME tv /\
    value_has_type tv v /\ not_fresh_at sa dst /\
    ptr_covers G tn src s 32 /\ ptr_covers G tn dst s 32 /\
    lookup_var src s = SOME sw /\ lookup_var dst s = SOME dw /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
      val_in_memory tv v (w2n sw) m) /\
    fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?Gf tf t.
      gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tf (OK t) /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~t.vs_halted /\
      typed_copy_state_frame sa (w2n dw) 32 s t /\
      (!m. mem_agree_outside tf.t_mem t.vs_memory m ==>
        val_in_memory tv v (w2n dw) m) /\
      (!p. not_fresh_at sa p ==>
        lookup_var p t = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
        op_taint tf (Var p) = op_taint tn (Var p)) /\
      tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
      (!i. ~(w2n dw <= i /\ i < w2n dw+32) ==>
        (i IN tf.t_mem <=> i IN tn.t_mem))
Proof
  rpt gen_tac >> strip_tac >>
  `(!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
      mem_word_at (w2n sw) m = typed_val_to_w256 tv v) /\
   (!i. w2n sw <= i /\ i < w2n sw+32 ==> i NOTIN tn.t_mem)` by
    (drule_all robust_typed_word_clean >> simp[]) >>
  `?fo sm. emit_op MLOAD [Var src] sa = (fo,sm) /\
    emit_void MSTORE [Var dst;fo] sm = ((),sb)` by
    (qpat_x_assum `compile_store_memory_typed _ _ _ _ _ _ = _` mp_tac >>
     simp[compile_store_memory_typed_word, comp_bind_def] >>
     Cases_on `emit_op MLOAD [Var src] sa` >> simp[]) >>
  `cs_extends sa sm /\ cs_extends sm sb` by
    metis_tac[reason_emit_op_cs_extends, reason_emit_void_cs_extends] >>
  `fn_has_code sa sm fn /\ fn_has_code sm sb fn` by
    metis_tac[fn_has_code_split] >>
  `32 <= (32:num)` by simp[] >>
  drule_all concat_suffix_path_ptr >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  qexistsl_tac [`H`,`un`,`t`] >> simp[] >>
  conj_tac
  >- (simp[typed_copy_state_frame_def] >> conj_tac
      >- (qpat_x_assum `u with <|vs_vars := _; vs_inst_idx := _|> = s` mp_tac >>
          simp[mstore_def, venom_state_component_equality]) >>
      conj_tac
      >- metis_tac[] >>
      simp[typed_copy_frame_def] >> conj_tac
      >- (rpt strip_tac >> simp[mstore_mem_bytes_at_disjoint]) >>
      simp[immutableMemoryFrameTheory.immutable_mstore_capacity, MAX_DEF]) >>
  rpt strip_tac >> irule calldata_word_representation >>
  reverse conj_tac >- metis_tac[] >>
  `mem_word_at (w2n dw) (mstore (w2n dw) (mload (w2n sw) s) u).vs_memory =
    mem_word_at (w2n dw) m` by
    (irule bodyPtrPrecompileBuiltinsArithmeticValueTheory.clean_word_mem_agree >>
     goal_assum (drule_at Any) >> simp[]) >>
  gvs[mstore_mem_word_at_same, GSYM mem_word_at_eq_mload,
      mem_agree_outside_def]
QED

Theorem widened_assign_typed_bytes_counted:
  !ctx PG D fn cenv dst src dty sty sa sb G tn s dw sw tenv dtv stv v.
    compile_store_memory_typed cenv (Var dst) dty (Var src) sty sa = ((),sb) /\
    is_bytestring_type sty /\ is_bytestring_type dty /\
    evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
    value_has_type stv v /\ value_has_type dtv v /\
    not_fresh_at sa src /\ not_fresh_at sa dst /\
    ptr_covers G tn src s (type_memory_size stv) /\
    ptr_covers G tn dst s (type_memory_size dtv) /\
    lookup_var src s = SOME sw /\ lookup_var dst s = SOME dw /\
    type_memory_size dtv < dimword (:256) /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
      val_in_memory stv v (w2n sw) m) /\
    fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?Gf tf t.
      gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tf (OK t) /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~t.vs_halted /\
      typed_copy_state_frame sa (w2n dw) (type_memory_size dtv) s t /\
      (!m. mem_agree_outside tf.t_mem t.vs_memory m ==>
        val_in_memory dtv v (w2n dw) m) /\
      (!p. not_fresh_at sa p ==>
        lookup_var p t = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
        op_taint tf (Var p) = op_taint tn (Var p)) /\
      tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
      (!i. ~(w2n dw <= i /\ i < w2n dw+type_memory_size dtv) ==>
        (i IN tf.t_mem <=> i IN tn.t_mem))
Proof
  rpt gen_tac >> strip_tac >>
  `compile_store_bytestring (Var src) (Var dst) sa = ((),sb)` by
    metis_tac[compile_store_memory_typed_bytes] >>
  `!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
       val_in_memory dtv v (w2n sw) m` by
    metis_tac[valueCopyBytesTheory.bytestring_val_in_memory_transfer] >>
  qspecl_then [`tenv`,`sty`,`dty`,`stv`,`dtv`,`v`,`w2n sw`,`s`,`tn`]
    mp_tac annAssignPtrMemorySourceTheory.annassign_bytestring_window_ptr >>
  simp[] >> strip_tac >>
  `val_wf dtv v` by metis_tac[valueTypingMemoryPropsTheory.value_has_type_memory_wf] >>
  `32 + 32 * word_size len <= type_memory_size stv /\
   32 + 32 * word_size len <= type_memory_size dtv /\
   val_footprint dtv v <= 32 + 32 * word_size len /\
   32 + 32 * word_size len < dimword (:256)` by
    gvs[vfmConstantsTheory.word_size_def] >>
  `ptr_covers G tn src s 32 /\
   ptr_covers G tn src s (32 + 32 * word_size len) /\
   ptr_covers G tn dst s (32 + 32 * word_size len)` by
    (gvs[ptr_covers_def] >> metis_tac[LESS_EQ_TRANS]) >>
  drule_all assign_base_store_bytestring_robust_counted >>
  disch_then (qspecl_then [`D`,`PG`] strip_assume_tac) >>
  qexistsl_tac [`Gf`,`tf`,`u`] >> simp[] >>
  conj_tac
  >- (irule typed_copy_state_frame_subinterval >> goal_assum (drule_at Any) >> simp[]) >>
  rpt strip_tac >> first_x_assum irule >> decide_tac
QED

Theorem widened_assign_typed_none_counted:
  !ctx PG D fn cenv dst src sa sb G tn s dw.
    compile_store_memory_typed cenv dst NoneT src NoneT sa = ((),sb) /\
    acyclic_struct_metadata cenv.ce_struct_fields /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    gas_path_ptr D 0 ctx fn PG G tn s 0 G tn (OK s) /\
    s.vs_current_bb = sb.cs_current_bb /\
    s.vs_inst_idx = LENGTH sb.cs_current_insts /\
    typed_copy_state_frame sa (w2n dw) (type_memory_size NoneTV) s s /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
      val_in_memory NoneTV NoneV (w2n dw) m) /\
    (!p. not_fresh_at sa p ==>
      lookup_var p s = lookup_var p s /\ FLOOKUP G p = FLOOKUP G p /\
      op_taint tn (Var p) = op_taint tn (Var p)) /\
    tn.t_stor = tn.t_stor /\ tn.t_trans = tn.t_trans /\ tn.t_imm = tn.t_imm /\
    (!i. ~(w2n dw <= i /\ i < w2n dw+type_memory_size NoneTV) ==>
      (i IN tn.t_mem <=> i IN tn.t_mem))
Proof
  rpt gen_tac >> strip_tac >>
  `sb = sa` by
    gvs[Once compile_store_memory_typed_def, is_word_type_def,
        is_bytestring_type_def, type_memory_bytes_def,
        contextPropsTheory.compile_copy_memory_zero] >>
  simp[val_in_memory_def] >> irule (cj 1 gas_path_ptr_rules) >> simp[]
QED
