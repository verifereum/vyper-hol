Theory bodyPtrBopInNormalizedRuntime
Ancestors bodyPtrBopInRuntimeRepresentation bodyPtrBopInMemoryRuntime
  bodyPtrBopInCodeRuntime bodyPtrBopInSlotRuntime bodyPtrBopInLoopContract
  compileEnv context vyperValue vyperTyping vyperState venomState ptrDiscipline vyperAST

Theorem membership_normalized_array_runtime:
  post_value_type cenv e = expr_type e /\
  membership_vv_post d ctx fn cenv cx e es sc sa vv s0 G0 tn0 tvv ee s G tn /\
  compile_expr cenv ty e sc = (vv,sa) /\ local_ptrs_reserved cenv sc /\
  compile_var_array_membership cenv needle vv (ArrayT et bd) is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\ ~cenv.ce_is_ctor /\
  expr_type e = ArrayT et bd /\
  evaluate_type (get_tenv cx) (ArrayT et bd) = SOME (ArrayTV tv bd) /\
  evaluate_type (get_tenv cx) et = SOME tv /\ is_word_type et /\
  read_result cx tvv ee = (INL (ArrayV av),ee) /\
  value_has_type (ArrayTV tv bd) (ArrayV av) /\
  ws = (case av of DynArrayV vs => MAP (typed_val_to_w256 tv) vs
        | SArrayV kvs => GENLIST (\j. typed_val_to_w256 tv (sparse_val tv kvs j))
                           (bound_length bd)) /\
  (!x. needle = Var x ==> not_fresh_at sa x) /\
  eval_operand needle s = SOME w /\ op_prov G needle = NONE /\ op_taint tn needle = {} /\
  ~s.vs_halted ==>
  ?G' tn' t. gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    membership_loop_frame sa G tn s G' tn' t /\
    eval_operand op t = SOME (bool_to_word (if is_in then MEM w ws else ~MEM w ws)) /\
    op_prov G' op = NONE /\ op_taint tn' op = {} /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  drule_all membership_vv_post_runtime_representation >> strip_tac >>
  `compile_var_array_membership cenv needle (LocatedValue ann p)
     (ArrayT et bd) is_in sa = (op,sb)` by metis_tac[] >>
  `s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts` by
    fs[bodyPtrBopInVvContractTheory.membership_vv_post_def] >>
  Cases_on `bd` >> Cases_on `av` >>
  fs[Once value_has_type_def, bound_length_def] >>
  Cases_on `p.ptr_location` >> gvs[]
  >- suspend "fixed_memory"
  >- suspend "fixed_storage"
  >- suspend "fixed_transient"
  >- suspend "fixed_code"
  >- suspend "dynamic_memory"
  >- suspend "dynamic_storage"
  >- suspend "dynamic_transient"
  >> suspend "dynamic_code"
QED

Resume membership_normalized_array_runtime[fixed_memory]:
  irule membership_fixed_memory_runtime >> simp[] >>
  goal_assum (drule_at (Pat `compile_var_array_membership _ _ _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `vv_at _ _ _ _ _ _ _ _ _`)) >>
  simp[is_word_type_def, value_has_type_def, read_result_def, return_def] >> metis_tac[]
QED
Resume membership_normalized_array_runtime[fixed_storage]:
  irule (Q.INST [`tr` |-> `F`] membership_fixed_slot_runtime) >> simp[] >>
  goal_assum (drule_at (Pat `compile_var_array_membership _ _ _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `vv_holds _ _ _ _ _ _ _`)) >>
  simp[value_has_type_def, read_result_def, return_def] >> metis_tac[]
QED
Resume membership_normalized_array_runtime[fixed_transient]:
  irule (Q.INST [`tr` |-> `T`] membership_fixed_slot_runtime) >> simp[] >>
  goal_assum (drule_at (Pat `compile_var_array_membership _ _ _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `vv_holds _ _ _ _ _ _ _`)) >>
  simp[value_has_type_def, read_result_def, return_def] >> metis_tac[]
QED
Resume membership_normalized_array_runtime[fixed_code]:
  irule membership_fixed_code_runtime >> simp[] >>
  goal_assum (drule_at (Pat `compile_var_array_membership _ _ _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `vv_holds _ _ _ _ _ _ _`)) >>
  simp[value_has_type_def] >> metis_tac[]
QED
Resume membership_normalized_array_runtime[dynamic_memory]:
  irule membership_dynamic_memory_runtime >> simp[] >>
  goal_assum (drule_at (Pat `compile_var_array_membership _ _ _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `vv_at _ _ _ _ _ _ _ _ _`)) >>
  simp[is_word_type_def, value_has_type_def, read_result_def, return_def] >> metis_tac[]
QED
Resume membership_normalized_array_runtime[dynamic_storage]:
  irule (Q.INST [`tr` |-> `F`] membership_dynamic_slot_runtime) >> simp[] >>
  goal_assum (drule_at (Pat `compile_var_array_membership _ _ _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `vv_holds _ _ _ _ _ _ _`)) >>
  simp[value_has_type_def, read_result_def, return_def] >> metis_tac[]
QED
Resume membership_normalized_array_runtime[dynamic_transient]:
  irule (Q.INST [`tr` |-> `T`] membership_dynamic_slot_runtime) >> simp[] >>
  goal_assum (drule_at (Pat `compile_var_array_membership _ _ _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `vv_holds _ _ _ _ _ _ _`)) >>
  simp[value_has_type_def, read_result_def, return_def] >> metis_tac[]
QED
Resume membership_normalized_array_runtime[dynamic_code]:
  irule membership_dynamic_code_runtime >> simp[] >>
  goal_assum (drule_at (Pat `compile_var_array_membership _ _ _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `vv_holds _ _ _ _ _ _ _`)) >>
  simp[value_has_type_def] >> metis_tac[]
QED
Finalise membership_normalized_array_runtime
