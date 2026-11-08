(* Borrowed tuple bytes: pointer evaluation is distinct from writes. *)
Theory tuplePlaceBorrow
Ancestors
  tuplePlaceSnapshot tuplePlaceSource supportedTargets bodySimAugPlaceScopes
  vyperPlaceFrames vyperInterpreter vyperState vyperMisc vyperValue
  vyperScopePreservation vyperPlaceStatePreservation exprSimSource loweringPosts

Theorem tuple_place_pure_target_scopes:
  !bt tops cx es res ee.
    supported_target_pure tops bt /\
    eval_base_place cx bt es = (res,ee) ==> ee.scopes = es.scopes
Proof
  measureInduct_on `base_assignment_target_size bt` >> Cases_on `bt` >> rpt gen_tac
  >- (simp[Once evaluate_def, get_scopes_def, bind_def, ignore_bind_def,
           type_check_def, assert_def, return_def, raise_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[])
  >- (PairCases_on `p` >> simp[Once evaluate_def] >>
      metis_tac[lookup_global_scopes])
  >- (qpat_x_assum `!y. _` (qspec_then `b` mp_tac) >>
      simp[vyperASTTheory.expr_size_def] >> strip_tac >> rpt strip_tac >>
      qpat_x_assum `eval_base_place _ (SubscriptTarget _ _) _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
      strip_tac >> gvs[supported_target_pure_def] >>
      imp_res_tac read_result_state >> imp_res_tac extend_place_state >>
      imp_res_tac aug_place_pure_expr_scopes >> gvs[] >> metis_tac[])
  >> (qpat_x_assum `!y. _` (qspec_then `b` mp_tac) >>
      simp[vyperASTTheory.expr_size_def] >> strip_tac >> rpt strip_tac >>
      qpat_x_assum `eval_base_place _ (AttributeTarget _ _) _ = _` mp_tac >>
      simp[Once evaluate_def, bind_def, AllCaseEqs(), return_def, raise_def] >>
      strip_tac >> gvs[supported_target_pure_def] >>
      imp_res_tac extend_place_state >> gvs[] >> metis_tac[])
QED

Theorem tuple_place_pure_target_borrow_bytes:
  supported_target_pure tops bt /\
  eval_base_place cx bt es = (res,ee) /\
  target_post ctx func cenv cx es sa sb s0 ee pv vt r s /\
  local_region cenv es.scopes s0 n b sz ==>
  mem_bytes_at b sz s.vs_memory = mem_bytes_at b sz s0.vs_memory
Proof
  rpt strip_tac >>
  drule_all tuple_place_pure_target_scopes >> strip_tac >>
  irule tuple_place_target_unchanged_local >> goal_assum (drule_at Any) >>
  simp[] >> metis_tac[]
QED

Theorem tuple_place_borrowed_tuple_path:
  local_val_at cenv cx n k (TupleTV tvs) (ArrayV (TupleV vs)) ==>
  local_path_at cenv cx n k (TupleTV tvs)
Proof
  simp[local_val_at_def]
QED

(* A tuple borrowed inside an array has a whole-tuple sibling window.
   This checks layout arithmetic, not arbitrary typed target separation. *)
Theorem tuple_place_nested_borrow_layout_probe:
  let etv = ArrayTV (BaseTV (UintT 256)) (Fixed 1) in
  let tv = TupleTV [etv; etv] in
    mem_path_offset (ArrayTV tv (Fixed 2))
      [ValueSubscript (IntV 0)] = SOME (0,tv) /\
    mem_path_offset (ArrayTV tv (Fixed 2))
      [ValueSubscript (IntV 1)] = SOME (64,tv) /\
    type_memory_size tv = 64 /\
    0 + type_memory_size tv <= 64
Proof
  EVAL_TAC >> simp[]
QED

(* C1.3.4.5: borrowed-store applicability audit (not an asserted theorem).

   Candidate separation boundary, at the state s AFTER pointer evaluation:
     expr_sim_inv cenv cx env ee /\ stmt_state_rel ctx func cenv cx ee s /\
     local_region cenv ee.scopes s n b sz /\
     local_path_at cenv cx n k (TupleTV tvs) /\
     k + type_memory_size (TupleTV tvs) <= sz /\
     evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
     i < LENGTH tys /\ well_typed_target env bt (EL i tys) /\
     supported_target_pure tops bt /\
     eval_base_place cx bt ee = (INL (PlaceR p),ee) /\
     place_ptr_rel cenv cx s (PlaceR p) dw (SOME LocMemory) (Type (EL i tys))
       ==> b+k+type_memory_size (TupleTV tvs) <= w2n dw \/
           w2n dw+type_memory_size (EL i tvs) <= b+k.

   This is a PROPOSED boundary needing proof, not something supplied by
   place_ptr_rel. The eval_base_place equation is essential: mem_path_offset
   itself permits tuple subscripts, while type_place_target does not. An
   arbitrary path in place_ptr_rel can therefore point inside the borrow.
   Actual source target reachability must be retained from target simulation.

   Premise ledger:
   - LIST_REL and the root EVERY give typed BaseTargets and supported purity.
     EL specialization needs the equal lengths obtained from LIST_REL and
     evaluate_type. Success decomposition supplies the actual target equation.
   - expr_post supplies stmt_state_rel and expr_val_at at the RHS endpoint;
     tuple_place_borrowed_tuple_path extracts the structural path in the local
     alternative. Full TYPE extent containment is NOT mere val_footprint
     containment: derive it from mem_path_offset_sound plus the local declared
     type/entry alignment and local_ptrs_rel's type_memory_size <= sz.
   - lowered_value_type differs from expr_type for tuples only at IntCall.
     post_value_type then is lowered_value_type. If layouts differ, expr_post's
     conditional expr_val_own supplies the OWNED alternative; do not claim
     borrowed witnesses are impossible. If equal, borrowed reasoning uses
     ltys=tys and consequently ltvs=tvs by evaluation uniqueness.
   - Pure pointer evaluation preserves scopes and borrowed bytes by the two
     boundaries above; target_post preserves old operands/allocations. These
     results do not apply to the following store.

   Remaining structural gap:
   For SAME root, align the two evaluated root types, then compare borrow path
   and actual target path. Strict target descendants cannot cross TupleT:
   subscript_vtype (Type (TupleT ts)) idx_ty = NONE and attribute_type on
   TupleT is NONE. A target ancestor would require the tuple to occur inside
   its own member type; rule this out by strict structural type-value descent,
   NOT strict byte-size descent (capacity one and zero-sized layouts exist).
   Divergent paths need a general prefix-incomparable-path disjointness lemma.
   exprSimProps has local mem_step_offset_apart and exported path bounds, but
   exported dynarray_apart/dead_apart concern LENGTH WORDS only, not arbitrary
   destination envelopes. The checked example above tests nested array layout
   only. For DISTINCT locals local_ptrs_rel gives whole-region disjointness;
   combine containment and no-wrap bounds. Structs require field offsets, and
   Dynamic arrays include their 32-byte header and full capacity, not live len.

   Common-endpoint store contract still needed:
   Under the exact premises of place_store_word_run/place_store_value_run and
   the derived separation, obtain ONE t with their gas_marked_path, ff state
   relation, old variable/alloca frames and sb program counter, AND
     mem_bytes_at (b+k) (type_memory_size (TupleTV tvs)) t.vs_memory =
     mem_bytes_at (b+k) (type_memory_size (TupleTV tvs)) s.vs_memory.
   Preserve the borrow operand and local region witness at that SAME t for
   the next pointer evaluation; preserve fresh-allocation age/extent as well.
   local_path_at is independent of runtime scopes and values, so its witness
   survives writes with cenv,cx unchanged; local_region needs the source
   write's lookup/type preservation and old pointer frame, not unchanged
   whole entries. The generic store theorems return no snapshot-byte frame;
   a separate existential copy-effect run cannot be joined to their endpoint.
   Seek a strengthened task-local store boundary with a common execution.
   Existing tuple_place_copy_snapshot consumes typed_copy_effect once this
   common-endpoint obligation is solved. No universal separation or store
   contract is certified by this diagnostic, and no root premise is changed.
*)
