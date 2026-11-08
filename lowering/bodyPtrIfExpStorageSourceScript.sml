Theory bodyPtrIfExpStorageSource
Ancestors bodyPtrIfExpStorageExit bodyPtrIfExpBytesInputs
  bodyPtrIfExpMaterializeCapacity loweringPosts bodyPtrDefs
  vyperStorageBackend vyperState vyperTyping vyperTypeValues venomState

Theorem ifexp_storage_holds_decode:
  storage_holds cx tr ty raw p ee s /\
  evaluate_type (get_tenv cx) ty = SOME tvt /\
  read_result cx raw ee = (INL v,ee) ==>
  well_formed_type_value tvt /\
  slots_in_range (get_storage cx ee tr) (w2n p) tvt /\
  decode_value (get_storage cx ee tr) (w2n p) tvt = SOME v /\
  storage_range_agree (get_storage cx ee tr)
    (if tr then contract_transient s else contract_storage s) p tvt
Proof
  strip_tac >> fs[storage_holds_def] >>
  drule evaluate_type_well_formed_type_value >> strip_tac >>
  gvs[read_storage_slot_def, bind_def, get_storage_backend_eq,
      lift_option_def, return_def, AllCaseEqs()] >>
  Cases_on `decode_value (get_storage cx ee tr) (w2n p) tvt` >>
  gvs[return_def, raise_def]
QED

Theorem ifexp_storage_source_dead:
  ptr_vv_ok cx ty raw (LocatedValue tag pp) ee G tn s /\
  (pp.ptr_location = LocStorage \/ pp.ptr_location = LocTransient) /\
  eval_operand pp.ptr_operand s = SOME p /\
  evaluate_type (get_tenv cx) ty = SOME tvt ==>
  op_taint tn pp.ptr_operand = {} /\
  (!k b. w2n p <= w2n k /\ w2n k < w2n p+type_slot_size tvt /\
    b < 32 /\ (k,b) IN
      (if pp.ptr_location = LocStorage then tn.t_stor else tn.t_trans) ==>
    dead_bytes
      (if pp.ptr_location = LocStorage then contract_storage s else contract_transient s)
      (w2n p) tvt (w2n k) b)
Proof
  strip_tac >> fs[ptr_vv_ok_def] >> rpt strip_tac >>
  first_x_assum drule_all >>
  gvs[contract_storage_def, contract_transient_def, vfmStateTheory.lookup_account_def]
QED

Theorem ifexp_storage_arm_source:
  post_value_type ce e = expr_type e /\
  expr_body_pre ce cx env e es /\ eval_expr cx e es = (INL raw,ee) /\
  read_result cx raw ee = (INL v,ee) /\
  vv_post ctx fn ce cx e es sa sb s0 ee raw (LocatedValue tag pp) s /\
  ptr_vv_ok cx (expr_type e) raw (LocatedValue tag pp) ee G tn s /\
  (pp.ptr_location = LocStorage \/ pp.ptr_location = LocTransient) ==>
  ?p tvt.
    eval_operand pp.ptr_operand s = SOME p /\
    evaluate_type (get_tenv cx) (expr_type e) = SOME tvt /\
    well_formed_type_value tvt /\
    type_slot_size tvt = (type_memory_bytes ce (expr_type e)+31) DIV 32 /\
    32*((type_memory_bytes ce (expr_type e)+31) DIV 32) = type_memory_bytes ce (expr_type e) /\
    op_taint tn pp.ptr_operand = {} /\
    slots_in_range (get_storage cx ee (pp.ptr_location = LocTransient)) (w2n p) tvt /\
    decode_value (get_storage cx ee (pp.ptr_location = LocTransient)) (w2n p) tvt = SOME v /\
    storage_range_agree (get_storage cx ee (pp.ptr_location = LocTransient))
      (if pp.ptr_location = LocStorage then contract_storage s else contract_transient s) p tvt /\
    (!k b. w2n p <= w2n k /\ w2n k < w2n p+type_slot_size tvt /\ b < 32 /\
      (k,b) IN (if pp.ptr_location = LocStorage then tn.t_stor else tn.t_trans) ==>
      dead_bytes (if pp.ptr_location = LocStorage then contract_storage s else contract_transient s)
        (w2n p) tvt (w2n k) b)
Proof
  strip_tac >> drule_all ifexp_arm_annotation_typed >> strip_tac >>
  drule_all ifexp_materialize_annotation_aligned >> strip_tac >>
  `?p. eval_operand pp.ptr_operand s = SOME p /\
    storage_holds cx (pp.ptr_location = LocTransient) (expr_type e) raw p ee s` by
    (fs[vv_post_def, vv_holds_def] >> metis_tac[]) >>
  drule_all ifexp_storage_holds_decode >> strip_tac >>
  drule ifexp_storage_source_dead >> simp[] >> strip_tac >>
  gvs[] >> simp[valueEncodingPropsTheory.type_memory_size_slots, arithmeticTheory.MULT_DIV]
QED
