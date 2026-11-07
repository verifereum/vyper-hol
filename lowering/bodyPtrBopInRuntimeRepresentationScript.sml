Theory bodyPtrBopInRuntimeRepresentation
Ancestors bodyPtrBopInBaseBoundary bodyPtrBopInStackMemory
  bodyPtrBopInVvContract exprOperandVar loweringPosts bodyPtrDefs
  compileEnv exprLowering vyperValue venomState context vyperAST exprSimUnwrapProps

(* Normalize representation certificates, not the generated computation.
   In particular stack arrays keep the compiler's real default-memory path. *)
Theorem membership_array_vv_located:
  vv_holds cenv cx (ArrayT et bd) tvv vv es s /\
  vv_at cenv cx (ArrayT et bd) sc sd es tvv vv s /\
  ptr_vv_ok cx (ArrayT et bd) tvv vv es G tn s ==>
  ?ann p bw.
    (!needle is_in.
      compile_var_array_membership cenv needle vv (ArrayT et bd) is_in =
      compile_var_array_membership cenv needle (LocatedValue ann p)
        (ArrayT et bd) is_in) /\
    vv_operand vv = p.ptr_operand /\ p.ptr_location <> LocCalldata /\
    eval_operand p.ptr_operand s = SOME bw /\
    vv_holds cenv cx (ArrayT et bd) tvv (LocatedValue ann p) es s /\
    vv_at cenv cx (ArrayT et bd) sc sd es tvv (LocatedValue ann p) s /\
    ptr_vv_ok cx (ArrayT et bd) tvv (LocatedValue ann p) es G tn s
Proof
  strip_tac >> Cases_on `vv`
  >- (rename1 `StackValue ann arr_op` >>
      `~is_word_type (ArrayT et bd)` by simp[is_word_type_def] >>
      drule_all membership_stack_memory_holds >> disch_tac >>
      drule_all membership_stack_memory_at >> disch_tac >>
      drule_all membership_stack_memory_ptr >> disch_tac >>
      qexistsl_tac [`ArrayT et bd`, `mk_ptr arr_op LocMemory`] >>
      simp[membership_stack_memory_compile, vv_operand_def, mk_ptr_def] >>
      fs[vv_holds_def, mk_ptr_def] >> metis_tac[]) >>
  rename1 `LocatedValue ann p` >> qexistsl_tac [`ann`, `p`] >>
  simp[vv_operand_def] >>
  Cases_on `p.ptr_location` >> fs[vv_holds_def] >> metis_tac[]
QED

Theorem membership_evaluated_array_capacity:
  evaluate_type tenv (ArrayT et bd) = SOME (ArrayTV tv bd) ==>
  bound_length bd < dimword(:256)
Proof
  Cases_on `bd` >>
  simp[Once evaluate_type_def, AllCaseEqs(), bound_length_def, type_slot_size_def] >>
  rpt strip_tac >>
  `n * 1 <= n * type_slot_size tv` by simp[arithmeticTheory.LE_MULT_LCANCEL] >>
  decide_tac
QED

Theorem membership_ptr_vv_read_result:
  read_result cx tvv es = (INL v,es) ==>
  (ptr_vv_ok cx ty tvv vv es G tn s <=>
   ptr_vv_ok cx ty (Value v) vv es G tn s)
Proof
  strip_tac >> Cases_on `vv` >>
  simp[ptr_vv_ok_def, vyperStateTheory.read_result_def,
       vyperStateTheory.return_def]
QED

Theorem membership_vv_post_runtime_representation:
  membership_vv_post d ctx fn cenv cx e es sc sd vv s0 G0 tn0 tvv ee s G tn /\
  compile_expr cenv ty e sc = (vv,sd) /\ local_ptrs_reserved cenv sc /\
  expr_type e = ArrayT et bd /\
  evaluate_type (get_tenv cx) (ArrayT et bd) = SOME (ArrayTV tv bd) /\
  read_result cx tvv ee = (INL (ArrayV av),ee) ==>
  bound_length bd < dimword(:256) /\
  ?ann p bw.
    (!needle is_in.
      compile_var_array_membership cenv needle vv (ArrayT et bd) is_in =
      compile_var_array_membership cenv needle (LocatedValue ann p)
        (ArrayT et bd) is_in) /\
    (!x. p.ptr_operand = Var x ==> not_fresh_at sd x) /\
    p.ptr_location <> LocCalldata /\ eval_operand p.ptr_operand s = SOME bw /\
    stmt_state_rel ctx fn cenv cx ee s /\
    vv_holds cenv cx (ArrayT et bd) (Value (ArrayV av)) (LocatedValue ann p) ee s /\
    vv_at cenv cx (ArrayT et bd) sc sd ee (Value (ArrayV av)) (LocatedValue ann p) s /\
    ptr_vv_ok cx (ArrayT et bd) (Value (ArrayV av)) (LocatedValue ann p) ee G tn s /\
    (p.ptr_location = LocMemory ==> ?x. p.ptr_operand = Var x /\ lookup_var x s = SOME bw)
Proof
  strip_tac >>
  `!x. vv_operand vv = Var x ==> not_fresh_at sd x` by
    metis_tac[cj 1 compiler_compile_var] >>
  qpat_x_assum `membership_vv_post _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    mp_tac >>
  simp[membership_vv_post_def] >> strip_tac >>
  `vv_post ctx fn cenv cx e es sc sd s0 ee (Value (ArrayV av)) vv s` by
    metis_tac[vv_post_read_result] >>
  `ptr_vv_ok cx (ArrayT et bd) (Value (ArrayV av)) vv ee G tn s` by
    metis_tac[membership_ptr_vv_read_result] >>
  qpat_x_assum `vv_post _ _ _ _ _ _ _ _ _ _ tvv _ _` kall_tac >>
  qpat_x_assum `ptr_vv_ok _ _ tvv _ _ _ _ _` kall_tac >>
  gvs[vv_post_def] >>
  conj_tac >- metis_tac[membership_evaluated_array_capacity] >>
  drule_all membership_array_vv_located >> strip_tac >>
  qexistsl_tac [`ann`, `p`, `bw`] >> simp[] >>
  strip_tac >>
  irule membership_located_memory_base_var >> simp[] >>
  goal_assum (drule_at (Pat `ptr_vv_ok _ _ _ _ _ _ _ _`)) >>
  simp[vyperStateTheory.read_result_def, vyperStateTheory.return_def]
QED
