(* Decoding projection at storage forcing entry; no copy execution is chosen. *)
Theory exprPtrUnwrapStorageSource
Ancestors
  exprPtrUnwrapStorage loweringPosts exprSimUnwrap vyperStorageBackend
  vyperState vyperStorage vyperTypeValues accountsRelProps exprSimProps

Theorem storage_holds_decode:
  storage_holds cx tr t tv w es s /\
  evaluate_type (get_tenv cx) t = SOME ty ==>
  ?v. read_result cx tv es = (INL v,es) /\
    well_formed_type_value ty /\
    slots_in_range (get_storage cx es tr) (w2n w) ty /\
    decode_value (get_storage cx es tr) (w2n w) ty = SOME v /\
    storage_range_agree (get_storage cx es tr)
      (if tr then contract_transient s else contract_storage s) w ty
Proof
  strip_tac >> gvs[storage_holds_def] >>
  `well_formed_type_value ty` by metis_tac[evaluate_type_well_formed_type_value] >>
  simp[] >>
  qpat_x_assum `read_storage_slot _ _ _ _ _ = _` mp_tac >>
  simp[read_storage_slot_def, get_storage_backend_eq, bind_def,
       lift_option_def, return_def] >>
  Cases_on `decode_value (get_storage cx es tr) (w2n w) ty` >>
  simp[return_def, raise_def]
QED

Theorem ptr_vv_ok_storage_frame:
  ptr_vv_ok cx t tv (LocatedValue t' p) es G tn s /\
  p.ptr_location = slot_loc tr /\
  eval_operand p.ptr_operand u = eval_operand p.ptr_operand s /\
  op_taint tm p.ptr_operand = op_taint tn p.ptr_operand /\
  u.vs_accounts = s.vs_accounts /\ u.vs_transient = s.vs_transient /\
  u.vs_call_ctx = s.vs_call_ctx /\ tm.t_stor = tn.t_stor /\
  tm.t_trans = tn.t_trans ==>
  ptr_vv_ok cx t tv (LocatedValue t' p) es H tm u
Proof
  Cases_on `tr` >> simp[slot_loc_def, bodyPtrDefsTheory.ptr_vv_ok_def]
QED
