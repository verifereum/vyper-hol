(* Counted copy primitives for physical-to-annotated aggregate stores.
   Source coverage is an allocation fact, separate from robust semantics:
   tainted padding is allowed and its taint is transported by MCOPY. *)
Theory bodyPtrTypedCopyBoundary
Ancestors
  annAssignPtrCopy annAssignPtrBytestring robustCopyTransportPtr
  typedCopyRobustTransportPtr typedMemoryCopy
  bodyPtrBytestringBuiltinsConcatSuffix typedCopyAgreement
  assignBasePtrBytesField assignBasePtrTypedBytesField assignBasePtrBoundary
  bodyPtrPhysicalChildUnwrap assignTuplePtrLoadStep assignTuplePtrStoreWord
  context emitHelper emitHelperProps compileEnv fragGasPathPtr fragExec
  annAssignPtrScratch exprSimAccounts
  bodyPtrDefs ptrDiscipline venomState venomMemProofs pred_set
  valueEncodingProps valueEncodingDefs arithmetic words finite_map

(* Raw optimized copies use annassign_counted_copy_robust_ptr directly.
   Runtime bytes use assign_base_bytestring_field_robust_counted, whose
   typed_copy_state_frame is retained, and bytestring_val_in_memory_transfer.
   Neither needs clean source padding. *)

Theorem store_memory_typed_word_counted_robust:
  is_word_type dty /\
  compile_store_memory_typed ce (Var dst) dty (Var src) sty sa = ((),sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  not_fresh_at sa dst /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  ptr_covers G tn src s 32 /\ ptr_covers G tn dst s 32 /\
  evaluate_type tenv dty = SOME tv /\ value_has_type tv v /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    val_in_memory tv v (w2n a) m) ==>
  cs_extends sa sb /\
  ?H tf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 H tf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    (sf with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
      vs_inst_idx := s.vs_inst_idx|>) = s /\
    sf.vs_memory = (mstore (w2n b) (mload (w2n a) s) s).vs_memory /\
    tf.t_stor = tn.t_stor /\ tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    tf.t_mem = tn.t_mem DIFF {i | w2n b <= i /\ i < w2n b+32} /\
    (!p. not_fresh_at sa p ==> lookup_var p sf = lookup_var p s /\
      FLOOKUP H p = FLOOKUP G p /\ op_taint tf (Var p) = op_taint tn (Var p)) /\
    mem_agree_outside {i | w2n b <= i /\ i < w2n b+32}
      sf.vs_memory s.vs_memory /\
    (!m. mem_agree_outside tf.t_mem sf.vs_memory m ==>
      val_in_memory tv v (w2n b) m)
Proof
  strip_tac >>
  drule_all robust_typed_word_clean >> strip_tac >>
  `mload (w2n a) s = typed_val_to_w256 tv v` by
    metis_tac[mem_word_at_eq_mload, mem_agree_outside_def] >>
  `!m. mem_agree_outside
      (tn.t_mem DIFF {i | w2n b <= i /\ i < w2n b+32})
      (mstore (w2n b) (typed_val_to_w256 tv v) s).vs_memory m ==>
      val_in_memory tv v (w2n b) m` by
    (metis_tac[typed_word_store_robust_ptr]) >>
  `?tmp sm. emit_op MLOAD [Var src] sa = (tmp,sm) /\
    emit_void MSTORE [Var dst;tmp] sm = ((),sb)` by
    (gvs[Once compile_store_memory_typed_def, comp_bind_def] >>
     pairarg_tac >> gvs[] >> metis_tac[]) >>
  `cs_extends sa sm /\ cs_extends sm sb` by
    (conj_tac >- metis_tac[emit_op_extends_next_var] >>
     irule cs_extends_emit_inst >>
     qexistsl_tac [`MSTORE`, `[Var dst;tmp]`, `[]`] >>
     gvs[emit_void_def, emit_inst_def]) >>
  `cs_extends sa sb` by metis_tac[cs_extends_trans] >> simp[] >>
  `fn_has_code sa sm fn /\ fn_has_code sm sb fn` by
    metis_tac[fn_has_code_split] >>
  `32 <= (32:num)` by simp[] >>
  drule_all concat_suffix_path_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`H`, `un`, `t`] >> simp[] >>
  qpat_x_assum `t = _` SUBST_ALL_TAC >>
  qpat_x_assum `(u with <|vs_vars := _; vs_inst_idx := _|>) = s` mp_tac >>
  simp[mstore_def, write_memory_with_expansion_def, venom_state_component_equality]
QED

(* Optimized-read audit (context.compile_copy_sarray_typed and
   context.compile_copy_dynarray_typed):
   - Fixed arrays read count * dst_stride only when dst_stride = src_stride.
     This is exactly type_memory_bytes ce (ArrayT src_elem (Fixed count));
     no val_footprint-based cleanliness assertion is needed.
   - Dynamic arrays load the header, then copy LENGTH vs * src_stride only
     when the element types (and strides) agree. The following bound uses
     the physical source capacity, independently of destination capacity.
     value_has_type at the destination separately supplies its ASSERT bound.
   - ptr_buf_ok_read_covers supplies source provenance from the child's
     physical ptr_buf_ok post. Offset coverage uses
     assign_base_ptr_covers_offset_address, with nonwrap from alloca bounds.
   - Raw paths retain arbitrary padding taint through
     annassign_counted_copy_robust_ptr. Bytes paths retain the complete
     runtime frame via assign_base_bytestring_field_robust_counted, and
     bytestring_val_in_memory_transfer changes the semantic capacity.
   - Robust source memory and value_has_type come from the child post;
     fn_has_code/position/no-dalloca and old-register freshness come from
     the literal frame. Fresh literal allocation supplies destination
     capacity, nonwrap and disjointness. None of these are semantic
     full-buffer-cleanliness premises. *)
Theorem dynamic_array_copy_read_extent:
  value_has_type (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) ==>
  32 + LENGTH vs * type_memory_bytes ce et <=
    type_memory_bytes ce (ArrayT et (Dynamic cap))
Proof
  simp[vyperTypingTheory.value_has_type_def, type_memory_bytes_def] >>
  rpt strip_tac >> simp[]
QED
