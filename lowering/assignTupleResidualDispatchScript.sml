(* Diagnostic of the unstaged, equal-layout RHS ownership interface. *)
Theory assignTupleResidualDispatch
Ancestors
  assignTupleResidualBoundary stmtLowering loweringPosts exprLowering
  vyperAST vyperTypeSystem finite_map compileEnv
  tuplePlaceSnapshot tuplePlacePrefixCert tupleStageProps
Libs
  monadsyntax

(* expr_post supplies expr_val_at, rather than unconditional ownership, for
   this equal-layout internal-call case.  Its local-region alternative is
   not excluded by the interface.  No runtime counterexample is asserted. *)
Triviality equal_layout_unstaged_ownership_diagnostic:
  lowered_value_type cenv (Call (TupleT tys) (IntCall fid) args drv) = TupleT tys /\
  evaluate_type (get_tenv cx) (TupleT tys) = SOME tv /\
  0 < val_footprint tv v /\
  (!aid b sz. FLOOKUP sv.vs_allocas aid = SOME (b,sz) /\
     sa.cs_next_id <= aid /\ aid < su.cs_next_id ==> F) ==>
  ~is_memory_view (Call (TupleT tys) (IntCall fid) args drv) /\
  post_value_type cenv (Call (TupleT tys) (IntCall fid) args drv) = TupleT tys /\
  ~expr_val_own cenv cx (TupleT tys) sa su ee v op sv
Proof
  simp[is_memory_view_def, post_value_type_def, is_word_type_def,
       is_bytestring_type_def] >>
  rpt strip_tac >> fs[expr_val_own_def, is_word_type_def] >>
  first_x_assum (qspec_then `tv` mp_tac) >> simp[] >> metis_tac[]
QED

(* The call-site post selects the actual layout; only equal layouts may
   retain the borrowed alternative of the snapshot certificate. *)
Theorem tuple_rhs_snapshot_certificate:
  well_typed_expr env e /\ expr_type e = TupleT tys /\
  lowered_value_type cenv e = TupleT ltys /\
  evaluate_type (get_tenv cx) (TupleT ltys) = SOME (TupleTV ltvs) /\
  expr_post ctx func cenv cx e es sa su s0 ee (ArrayV (TupleV vs)) op sv /\
  eval_operand op sv = SOME w ==>
  tuple_place_snapshot cenv cx ee sa.cs_next_id su.cs_next_id
    tys ltys ltvs w sv
Proof
  strip_tac >> drule_all tuple_rhs_lowered_resources >> strip_tac >>
  Cases_on `ltys = tys`
  >- (gvs[] >> drule_all tuple_place_expr_snapshot_cases >>
      simp[tuple_place_snapshot_def, local_val_at_def] >>
      metis_tac[]) >>
  `expr_val_own cenv cx (TupleT ltys) sa su ee
    (ArrayV (TupleV vs)) op sv` by gvs[] >>
  drule_all tuple_place_expr_owned_snapshot >>
  simp[tuple_place_snapshot_def] >> metis_tac[]
QED

(* A cut for every compiler dispatch, including rejection. The caller
   supplies the actual element list, not the annotation's element list. *)
Theorem tuple_unpack_dispatch_cut:
  elem_types = (case ty of
      TupleT tys => tys
    | StructT nsid => MAP (FST o SND)
        (get_struct_fields cenv.ce_struct_fields (nsid_to_string nsid))
    | _ => REPLICATE (LENGTH gs) (BaseT (UintT 256))) /\
  stage = ((may_stage /\ EXISTS (\t. ~is_word_type t) elem_types) /\
           0 < SUM (MAP (type_memory_bytes cenv) elem_types)) /\
  compile_tuple_unpack cenv ty may_stage gs op su = ((),sf) ==>
  (stage /\ ~cenv.ce_target CapMcopy /\ emit_inst INVALID [] [] su = ((),sf)) \/
  (~(stage /\ ~cenv.ce_target CapMcopy) /\
   ?staged sl elems ss.
     (if stage then
        do buf <- compile_alloc_buffer (SUM (MAP (type_memory_bytes cenv) elem_types));
           emit_void MCOPY [buf.buf_operand; op;
             Lit (n2w (SUM (MAP (type_memory_bytes cenv) elem_types)))];
           comp_return buf.buf_operand od
      else comp_return op) su = (staged,sl) /\
     compile_tuple_load_all cenv staged elem_types 0 sl = (elems,ss) /\
     compile_tuple_store_all cenv elem_types gs elems ss = ((),sf))
Proof
  strip_tac >>
  qpat_x_assum `compile_tuple_unpack _ _ _ _ _ _ = _` mp_tac >>
  simp_tac bool_ss [compile_tuple_unpack_def, LET_THM] >>
  qpat_x_assum `elem_types = _` (fn th => rewrite_tac[GSYM th]) >>
  rewrite_tac[arithmeticTheory.GREATER_DEF, CONJ_ASSOC] >>
  qpat_x_assum `stage = _` (fn th => rewrite_tac[GSYM th]) >>
  Cases_on `stage /\ ~cenv.ce_target CapMcopy`
  >- simp[] >>
  simp[] >> strip_tac >> conj_tac >- metis_tac[] >>
  qpat_x_assum `_ su = ((),sf)` mp_tac >>
  rewrite_tac[optional_tuple_stage_code] >>
  simp_tac bool_ss [type_memory_bytes_def] >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> gvs[]) >> rpt strip_tac >> gvs[] >>
  metis_tac[]
QED
