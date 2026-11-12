(* Numeric premise provenance for tuple-place stores. *)
Theory tuplePlaceBounds
Ancestors
  tuplePlaceSource exprSimHyps exprSimHypsDefs abiEncoderInput
  allocLimits compileEnv placeMemoryLiveRegion exprSimProps loweringPosts

Theorem tuple_place_element_alloc_ok:
  !cenv tys i.
    type_alloc_ok cenv (TupleT tys) /\ i < LENGTH tys ==>
    type_alloc_ok cenv (EL i tys)
Proof
  rpt gen_tac >>
  simp[type_alloc_ok_def, is_word_type_def, type_memory_bytes_def] >>
  strip_tac >>
  qspecl_then [`type_memory_bytes cenv`, `tys`, `i`] mp_tac
    abi_encoder_prefix_sum_bound >>
  fs[SF ETA_ss] >> decide_tac
QED

Theorem tuple_place_rhs_element_alloc_ok:
  expr_body_pre cenv cx env e es /\ expr_type e = TupleT tys /\
  i < LENGTH tys ==> type_alloc_ok cenv (EL i tys)
Proof
  strip_tac >>
  `type_alloc_ok cenv (TupleT tys)` by
    (gvs[expr_body_pre_def] >>
     drule alloc_limits_expr_type_alloc_ok >> simp[]) >>
  metis_tac[tuple_place_element_alloc_ok]
QED

(* Actual local containment yields the allocation end bound. The generic
   place_store_value_run additionally asks for 64 bytes after that end;
   this stronger margin is not supplied by local_ptrs_rel. *)
Theorem tuple_place_memory_end_bound:
  place_ptr_rel cenv cx s (PlaceR p) w (SOME LocMemory) (Type dty) /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  stmt_state_rel ctx func cenv cx ee s /\
  write_place cx p v ee = (INL (),ff) /\
  (!id path entry t0.
    p = MemoryPlace id path /\ lookup_scopes id ee.scopes = SOME entry /\
    cenv.ce_var_type id = SOME t0 ==>
    evaluate_type (get_tenv cx) t0 = SOME entry.type) ==>
  w2n w + type_memory_size dtv < dimword (:256)
Proof
  strip_tac >> drule_all memory_place_live_region >> strip_tac >>
  drule stmt_state_rel_region_lt >> strip_tac >>
  first_x_assum drule >> decide_tac
QED
