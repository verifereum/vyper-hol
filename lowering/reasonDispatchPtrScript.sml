(* Representation dispatch for a typed string reason at an expression endpoint. *)
Theory reasonDispatchPtr
Ancestors
  reasonFragmentPtr reasonMemoryConsumerPtr reasonStorageConsumerPtr
  reasonCodeConsumerPtr reasonLiteralConsumerPtr reasonEndpointResourcesPtr
  loweringPosts exprLoweringProps exprSimProps compileEnv context
  bodyPtrDefs ptrDiscipline arithmetic list

Theorem compile_revert_string_endpoint_ptr:
  compile_expr cenv (expr_type r) r sa = (vv,sm) /\
  expr_type r = BaseT (StringT max) /\
  evaluate_type (get_tenv cx) (BaseT (StringT max)) = SOME (BaseTV (StringT max)) /\
  type_alloc_ok cenv (BaseT (StringT max)) /\
  val_wf (BaseTV (StringT max)) (StringV str) /\
  compile_revert_with_reason cenv vv (expr_type r)
    (type_memory_bytes cenv (expr_type r)) sm = ((),sb) /\
  fn_has_code sm sb fn /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved cenv sa /\ ~ctx_has_dalloca ctx /\ ~cenv.ce_is_ctor /\
  vv_post ctx fn cenv cx r es sa sm s0 ee tv vv t /\
  ptr_vv_ok cx (expr_type r) tv vv ee G tn t /\
  ~t.vs_halted /\ t.vs_current_bb = sm.cs_current_bb /\
  t.vs_inst_idx = LENGTH sm.cs_current_insts /\
  read_result cx tv ee = (INL (StringV str),ee) ==>
  ?z Gf tnf. gas_path_ptr D 0 ctx fn PG G tn t 0 Gf tnf (Abort Revert_abort z)
Proof
  strip_tac >>
  `copy_old_operand sm (vv_operand vv)` by metis_tac[compile_expr_old_operand] >>
  `sa.cs_next_var <= sm.cs_next_var` by metis_tac[cj 1 compile_expr_grows] >>
  `!k. k < 3 ==> not_local_ptr cenv ee.scopes
    (STRING #"%" (toString (sm.cs_next_var+k)))` by
    (rpt strip_tac >> irule local_ptrs_reserved_fresh >>
     goal_assum (drule_at Any) >> decide_tac) >>
  fs[vv_post_def] >> gvs[] >> Cases_on `vv`
  >- (irule (INST_TYPE [alpha |-> ``:type``] compile_revert_memory_string_endpoint_ptr) >> simp[] >>
      goal_assum (drule_at (Pat `vv_at _ _ _ _ _ _ _ _ _`)) >>
      simp[vv_operand_def, ADD_COMM] >>
      qexistsl [`BaseT (StringT max) : type`,`sb`] >> fs[vv_operand_def]) >>
  rename1 `LocatedValue vty p` >>
  `vty = BaseT (StringT max)` by fs[vv_holds_def] >> gvs[] >>
  Cases_on `p.ptr_location`
  >- suspend "memory"
  >- suspend "storage"
  >- suspend "transient"
  >- suspend "code"
  >> fs[vv_holds_def]
QED

Resume compile_revert_string_endpoint_ptr[memory]:
  irule (INST_TYPE [alpha |-> ``:type``] compile_revert_memory_string_endpoint_ptr) >>
  simp[] >> goal_assum (drule_at (Pat `vv_at _ _ _ _ _ _ _ _ _`)) >>
  simp[is_word_type_def, ADD_COMM] >>
  qexistsl [`BaseT (StringT max) : type`,`sb`] >> fs[vv_operand_def]
QED

Resume compile_revert_string_endpoint_ptr[storage]:
  irule (INST_TYPE [alpha |-> ``:type``] compile_revert_storage_string_endpoint_ptr) >>
  simp[] >> goal_assum (drule_at (Pat `vv_holds _ _ _ _ _ _ _`)) >>
  qexists `BaseT (StringT max) : type` >> qexists `sm` >>
  qexistsl [`sb`,`str`,`F`] >>
  fs[vv_operand_def, ADD_COMM]
QED

Resume compile_revert_string_endpoint_ptr[transient]:
  irule (INST_TYPE [alpha |-> ``:type``] compile_revert_storage_string_endpoint_ptr) >>
  simp[] >> goal_assum (drule_at (Pat `vv_holds _ _ _ _ _ _ _`)) >>
  qexists `BaseT (StringT max) : type` >> qexists `sm` >>
  qexistsl [`sb`,`str`,`T`] >>
  fs[vv_operand_def, ADD_COMM]
QED

Resume compile_revert_string_endpoint_ptr[code]:
  irule (INST_TYPE [alpha |-> ``:type``] compile_revert_code_string_endpoint_ptr) >>
  simp[] >> goal_assum (drule_at (Pat `vv_holds _ _ _ _ _ _ _`)) >>
  qexists `BaseT (StringT max) : type` >> qexists `sm` >>
  qexistsl [`sb`,`str`] >>
  fs[vv_operand_def, ADD_COMM]
QED

Finalise compile_revert_string_endpoint_ptr
