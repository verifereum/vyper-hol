(* Borrowed tuple bytes are protected by the mutable-place tuple barrier. *)
Theory assignTupleResidualSnapshot
Ancestors
  tuplePlaceReachable assignTuplePtrUnread assignTuplePtrBoundary
  bodyPtrDefs loweringStateRelDefs arithmetic targetPlaceSim
  bodyPtrPopTargetSimIndexSource supportedStmts supportedTargets vyperInterpreter vyperState

Theorem tuple_borrowed_value_store_frame_ptr:
  expr_sim_inv cenv cx env ee /\ stmt_state_rel ctx func cenv cx ee s /\
  local_region cenv ee.scopes s n b sz /\
  local_path_at cenv cx n k (TupleTV tvs) /\
  k + type_memory_size (TupleTV tvs) <= sz /\
  evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
  i < LENGTH tys /\ well_typed_target env bt (EL i tys) /\
  supported_target_pure tops bt /\ call_evaluation_safe cx [] /\
  eval_base_place cx bt ee = (INL (PlaceR p),ee) /\
  place_ptr_rel cenv cx s (PlaceR p) dw (SOME LocMemory) (Type (EL i tys)) /\
  ptr_val_ok cx ty v op G tn s /\
  eval_operand op t = eval_operand op s /\
  op_taint tn' op = op_taint tn op /\ op_prov G' op = op_prov G op /\
  (!q. op = Var q ==> FLOOKUP G' q = FLOOKUP G q) /\
  (!tv. evaluate_type (get_tenv cx) ty = SOME tv ==> val_wf tv v) /\
  (!tv w. evaluate_type (get_tenv cx) ty = SOME tv /\
     eval_operand op s = SOME w ==>
     b + k <= w2n w /\
     w2n w + val_footprint tv v <= b + k + type_memory_size (TupleTV tvs)) /\
  written <= type_memory_size (EL i tvs) /\
  (!a. ~(w2n dw <= a /\ a < w2n dw + written) ==>
     mem_bytes_at a 1 t.vs_memory = mem_bytes_at a 1 s.vs_memory /\
     (a IN tn'.t_mem <=> a IN tn.t_mem)) ==>
  ptr_val_ok cx ty v op G' tn' t
Proof
  strip_tac >> drule_all tuple_place_borrow_destination_apart >> strip_tac >>
  irule assignTuplePtrBoundaryTheory.ptr_val_ok_exterior_frame >>
  (conj_tac >- simp[]) >>
  qexistsl [`G`, `s`, `tn`, `{a | w2n dw <= a /\ a < w2n dw + written}`] >>
  simp[] >> rpt strip_tac >>
  first_x_assum (qspecl_then [`tv`, `w`] mp_tac) >> simp[] >> decide_tac
QED

(* Supported memory destinations have no index evaluation at all. *)
Theorem supported_memory_target_identity:
  supported_target tops bindings bt /\
  eval_base_place cx bt es = (INL (PlaceR (MemoryPlace id path)),ee) ==>
  bt = NameTarget id /\ path = [] /\ ee = es /\ supported_target_pure tops bt
Proof
  strip_tac >> drule target_base_memory_root_ptr >> strip_tac >>
  Cases_on `bt` >>
  gvs[supported_target_def, target_root_def, supported_target_pure_def]
  >- (gvs[Once evaluate_def, get_scopes_def, bind_def, ignore_bind_def,
          type_check_def, assert_def, return_def, raise_def, AllCaseEqs()]) >>
  Cases_on `b` >> gvs[supported_target_def, target_root_def]
QED
