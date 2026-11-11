Theory bodyPtrBopInMemoryRuntime
Ancestors bodyPtrBopInRuntimeEntry bodyPtrBopInLoopSearch
  bodyPtrBopInRuntimeContracts exprSimBopRestWordTail context
  exprLowering compileEnv vyperValue vyperState venomState ptrDiscipline
  bodyPtrBopInRuntimeCompiler bodyPtrBopInMemoryHeaderRuntime fragExec
  bodyPtrBopInHeaderCode

Theorem membership_fixed_memory_runtime:
  compile_var_array_membership cenv needle (LocatedValue ann p)
    (ArrayT ety (Fixed cap)) is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\ ~cenv.ce_is_ctor /\
  p.ptr_location = LocMemory /\ p.ptr_operand = Var basesrc /\
  not_fresh_at sa basesrc /\
  stmt_state_rel ctx fn cenv cx es s /\
  vv_at cenv cx (ArrayT ety (Fixed cap)) sc sd es tvv (LocatedValue ann p) s /\
  ptr_vv_ok cx (ArrayT ety (Fixed cap)) tvv (LocatedValue ann p) es G tn s /\
  read_result cx tvv es = (INL (ArrayV (SArrayV kvs)),es) /\
  evaluate_type (get_tenv cx) (ArrayT ety (Fixed cap)) = SOME (ArrayTV tv (Fixed cap)) /\
  evaluate_type (get_tenv cx) ety = SOME tv /\ is_word_type ety /\
  value_has_type (ArrayTV tv (Fixed cap)) (ArrayV (SArrayV kvs)) /\
  ws = GENLIST (\j. typed_val_to_w256 tv (sparse_val tv kvs j)) cap /\
  lookup_var basesrc s = SOME bw /\ cap < dimword (:256) /\
  (!x. needle = Var x ==> not_fresh_at sa x) /\
  eval_operand needle s = SOME w /\ op_prov G needle = NONE /\ op_taint tn needle = {} /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?G' tn' t. gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    membership_loop_frame sa G tn s G' tn' t /\
    eval_operand op t = SOME (bool_to_word (if is_in then MEM w ws else ~MEM w ws)) /\
    op_prov G' op = NONE /\ op_taint tn' op = {} /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `elem_size_in_location cenv LocMemory ety = 32` by
    (drule rest_word_word_stride >> simp[word_scale_def]) >>
  `compile_array_membership_loop needle (Var basesrc) (Lit (n2w cap)) 32 0
     (compile_ptr_load F cenv.ce_imm_alloca LocMemory) NONE is_in sa = (op,sb)` by
    gvs[compile_var_array_membership_def, vv_operand_def, vv_location_def,
        comp_bind_def, comp_return_def, comp_ignore_bind_def] >>
  `membership_load_contract D ctx fn PG sa 0 F cenv.ce_imm_alloca LocMemory ws G tn s` by
    (irule membership_memory_load_contract >> simp[] >>
     goal_assum (drule_at (Pat `vv_at _ _ _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `compile_array_membership_loop _ _ _ _ _ _ _ _ _ = _`)) >>
     simp[is_word_type_def] >> metis_tac[]) >>
  irule membership_loop_conditional >> simp[] >>
  goal_assum (drule_at (Pat `compile_array_membership_loop _ _ _ _ _ _ _ _ _ = _`)) >>
  simp[eval_operand_def, op_prov_def, op_taint_def] >> gvs[]
QED

Theorem membership_dynamic_memory_runtime:
  compile_var_array_membership cenv needle (LocatedValue ann p)
    (ArrayT ety (Dynamic cap)) is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\ ~cenv.ce_is_ctor /\
  p.ptr_location = LocMemory /\ p.ptr_operand = Var basesrc /\
  not_fresh_at sa basesrc /\
  stmt_state_rel ctx fn cenv cx es s /\
  vv_at cenv cx (ArrayT ety (Dynamic cap)) sc sd es tvv (LocatedValue ann p) s /\
  ptr_vv_ok cx (ArrayT ety (Dynamic cap)) tvv (LocatedValue ann p) es G tn s /\
  read_result cx tvv es = (INL (ArrayV (DynArrayV vs)),es) /\
  evaluate_type (get_tenv cx) (ArrayT ety (Dynamic cap)) = SOME (ArrayTV tv (Dynamic cap)) /\
  evaluate_type (get_tenv cx) ety = SOME tv /\ is_word_type ety /\
  value_has_type (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) /\
  lookup_var basesrc s = SOME bw /\ cap < dimword (:256) /\
  (!x. needle = Var x ==> not_fresh_at sa x) /\
  eval_operand needle s = SOME w /\ op_prov G needle = NONE /\ op_taint tn needle = {} /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?G' tn' t. gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    membership_loop_frame sa G tn s G' tn' t /\
    eval_operand op t = SOME (bool_to_word
      (if is_in then MEM w (MAP (typed_val_to_w256 tv) vs)
       else ~MEM w (MAP (typed_val_to_w256 tv) vs))) /\
    op_prov G' op = NONE /\ op_taint tn' op = {} /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `elem_size_in_location cenv LocMemory ety = 32` by
    (drule rest_word_word_stride >> simp[word_scale_def]) >>
  qpat_x_assum `compile_var_array_membership _ _ _ _ _ _ = _` mp_tac >>
  simp[membership_dynamic_compile_split, vv_location_def, vv_operand_def,
       word_scale_def] >>
  pure_once_rewrite_tac[comp_bind_def] >> simp[LET_THM] >>
  pairarg_tac >> simp[] >> strip_tac >>
  rename1 `compile_array_membership_loop _ _ _ _ _ _ _ _ mid = _` >>
  `cs_extends sa mid /\ cs_extends mid sb` by
    metis_tac[membership_runtime_header_extends, membership_runtime_loop_extends] >>
  `fn_has_code sa mid fn /\ fn_has_code mid sb fn` by
    metis_tac[fn_has_code_mid, cs_extends_refl] >>
  irule membership_dynamic_memory_header_runtime >> simp[] >>
  goal_assum (drule_at (Pat `vv_at _ _ _ _ _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `compile_array_membership_loop _ _ _ _ _ _ _ _ _ = _`)) >>
  simp[] >> metis_tac[]
QED
