Theory bodyPtrBopInRepresentation
Ancestors bodyPtrDefs loweringPosts exprLoweringProps accountsRelProps
  ptrCoverage compileEnv loweringStateRelDefs words typedCopyPtr

(* A located post rules out calldata without restricting the compiler. *)
Theorem membership_located_not_calldata:
  vv_holds cenv cx ty tv (LocatedValue ann p) es s ==>
  p.ptr_location <> LocCalldata
Proof
  Cases_on `p.ptr_location` >> simp[vv_holds_def]
QED

(* The bound comes from agreement, not slots_in_range (which only says
   that encodings and dynamic lengths are canonical). *)
Theorem membership_storage_extent:
  storage_holds cx tr ty tv w es s /\
  evaluate_type (get_tenv cx) ty = SOME aty ==>
  w2n w + type_slot_size aty <= dimword (:256)
Proof
  strip_tac >> gvs[storage_holds_def, storage_range_agree_def]
QED

Theorem membership_immutable_base_value:
  stmt_state_rel ctx fn cenv cx es s /\
  cenv.ce_imm_alloca = SOME region_op ==>
  eval_operand region_op s = SOME 0w
Proof
  simp[stmt_state_rel_def, immutable_base_zero_def] >> metis_tac[]
QED

(* Located memory posts carry the same footprint placement boundary as
   unwrapped aggregate values; no full-capacity no-wrap guess is needed. *)
Theorem membership_memory_value_at:
  vv_at cenv cx ty sa sb es tv (LocatedValue ann p) s /\
  p.ptr_location = LocMemory /\
  read_result cx tv es = (INL v,es) ==>
  expr_val_at cenv cx ty sa sb es v p.ptr_operand s
Proof
  simp[vv_at_def, expr_val_at_def] >> metis_tac[]
QED

Theorem membership_memory_offset_covers:
  stmt_state_rel ctx fn cenv cx es s /\
  vv_at cenv cx ty sa sb es tv (LocatedValue ann p) s /\
  ptr_vv_ok cx ty tv (LocatedValue ann p) es G tn s /\
  p.ptr_location = LocMemory /\
  read_result cx tv es = (INL v,es) /\
  evaluate_type (get_tenv cx) ty = SOME aty /\ ~is_word_type ty /\
  p.ptr_operand = Var src /\ lookup_var src s = SOME w /\
  0 < n /\ off + n <= val_footprint aty v /\
  lookup_var dst t = SOME (w + n2w off) /\
  FLOOKUP G' dst = FLOOKUP G src /\ op_taint tn' (Var dst) = {} ==>
  ptr_covers G' tn' dst t n
Proof
  strip_tac >>
  `expr_val_at cenv cx ty sa sb es v (Var src) s` by
    (drule_all membership_memory_value_at >> simp[]) >>
  `ptr_val_ok cx ty v (Var src) G tn s` by
    (gvs[ptr_vv_ok_def, ptr_val_ok_def] >>
     metis_tac[]) >>
  drule_all expr_val_at_ptr_offset_read_covers >> simp[]
QED

(* Runtime producer ledger (not extra hypotheses for the body theorem):

   Memory: membership_memory_offset_covers consumes exactly the located
   post's vv_at/ptr_vv_ok plus its read_result. For a header use off=0,n=32;
   dynarray_length_footprint_contained supplies containment. For a word child
   use off=32+32*i (dynamic) or 32*i (fixed), n=32. word_type_sizes
   (stmtSimReturn) gives element size 32, and val_footprint_def makes an
   array's footprint its full type_memory_size, including sparse defaults.
   Thus ptr_buf_ok alone is NOT used to infer a no-wrap bound on arbitrary
   ghost regions. The existing expr_val_at_ptr_offset_read_covers uses the
   real allocation frontier from stmt_state_rel to prove address no-wrap.
   The prefix must still establish dst's evaluated offset, inherited
   provenance and clean taint; membership_loop_frame transports the posts.

   Types: expr_body_pre_runtime_typed (exprSimSource) supplies evaluated
   array type and value_has_type after eval_expr/read_result. Dynamic
   child typing is all_have_type_EVERY + EVERY_EL. For fixed sparse arrays
   sparse_val_has_type (entryDecodeStaticProps) includes missing/default
   entries, given sparse_has_type and evaluated element type. The type
   compiler link is expr_sim_inv_memory_size (exprSimHyps). It must be
   applied at the operand's source state, not assumed at the final state.
   memory_dynamic_typed_element_clean consumes the resulting child typing;
   the existing scalar-case fixed cleanliness theorem needs either typed
   scalar inversion or the analogous robust typed-word derivation.

   Slots: membership_storage_extent gives the full natural slot extent
   <= dimword, enough for a positive live child's address < dimword.
   evaluated_word_deadless + located_{fixed_deadless,dynamic_element}_clean
   (LiveStorage) give clean key taint. storage_holds also retains decoding
   and canonicality, so numerical contents are not inferred from taint.

   Runtime code: ~ce_is_ctor is an entry assumption of both pointer
   judgments; compile_imm_load_word therefore uses DLOAD regardless of
   ce_imm_alloca. immutable_holds provides off+type_memory_size itv <
   dimword and sub_layout (the constructor disjunct is false). Its source
   immutable value and stmt_state_rel.state_rel.immutables_rel provide
   the data-section contents. No staging base ghost property is needed.

   Outstanding producer mathematics, not validated by these projections:
   ws = MAP (typed_val_to_w256 etv) vs for dynamic arrays, and the GENLIST
   of typed sparse_val encodings for fixed arrays; prove that MEM of the
   encoded needle is exactly evaluate_binop's value membership. This needs
   equality reflection at the common evaluated element type, not merely
   is_word_type of the needle. Prove/obtain that compatibility from the
   builtin typing premise before constructing ws. None of the projections
   here certify this semantic list identity or the counted load prefix.
*)
