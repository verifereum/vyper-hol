(* Storage/transient expression endpoints use the common checked encoder.
   Keys are arbitrary operands, not necessarily variables. *)
Theory reasonStorageConsumerPtr
Ancestors
  reasonEndpointResourcesPtr reasonCopySourcePtr revertReasonEntryPtr
  loweringPosts bodyPtrDefs compileEnv context exprLoweringProps
  valueEncoding valueEncodingProps vyperValue vyperState venomState
  ptrDiscipline words arithmetic finite_map list contractABI vfmConstants

Theorem compile_revert_storage_string_endpoint_ptr:
  compile_revert_with_reason cenv (LocatedValue (BaseT (StringT max)) p) mt
    (type_memory_bytes cenv (BaseT (StringT max))) sa = ((),sb) /\
  evaluate_type (get_tenv cx) (BaseT (StringT max)) = SOME (BaseTV (StringT max)) /\
  type_alloc_ok cenv (BaseT (StringT max)) /\
  val_wf (BaseTV (StringT max)) (StringV str) /\
  vv_holds cenv cx (BaseT (StringT max)) tv
    (LocatedValue (BaseT (StringT max)) p) es s /\
  ptr_vv_ok cx (BaseT (StringT max)) tv
    (LocatedValue (BaseT (StringT max)) p) es G tn s /\
  read_result cx tv es = (INL (StringV str),es) /\
  p.ptr_location = (if tr then LocTransient else LocStorage) /\
  copy_old_operand sa p.ptr_operand /\
  fn_has_code sa sb fn /\ stmt_state_rel ctx fn cenv cx es s /\
  fn_inst_ids_distinct fn /\
  (!k. k < 3 ==> not_local_ptr cenv es.scopes
    (STRING #"%" (toString (sa.cs_next_var+k)))) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?z Gf tnf. gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (Abort Revert_abort z)
Proof
  strip_tac >>
  `?a. eval_operand p.ptr_operand s = SOME a /\
    storage_holds cx tr (BaseT (StringT max)) tv a es s` by
    (Cases_on `tr` >> gvs[vv_holds_def]) >>
  `op_taint tn p.ptr_operand = {}` by fs[ptr_vv_ok_def] >>
  drule_all ptr_vv_ok_string_storage_key_clean >> strip_tac >>
  drule_all string_encoder_size_bounds >> strip_tac >>
  irule compile_revert_reason_storage_path_ptr >> simp[] >>
  goal_assum (drule_at (Pat `compile_revert_with_reason _ _ _ _ _ = _`)) >>
  qexistsl [`a`,`cx`,`es`,`str`,`tr`,`tv`] >>
  simp[] >> metis_tac[ADD_COMM]
QED
