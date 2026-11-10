Theory bodyPtrBopInMemoryHeaderRuntime
Ancestors bodyPtrBopInRuntimeEntry bodyPtrBopInLoopSearch
  bodyPtrBopInRuntimeContracts venomState ptrDiscipline compileEnv loweringStateRelDefs
  vyperValue vyperTyping context bodyPtrBopInHeaderCode bodyPtrBopInLoopContract
  fragGasPathPtr

(* Both anchors are essential: the base is old before the header, whereas
   its freshly generated length becomes old only at the loop frontier. *)
Theorem membership_dynamic_memory_header_runtime:
  (do len <- compile_ptr_load F imm LocMemory (Var basesrc);
      flag <- emit_op GT [len;Lit (n2w cap)];
      valid <- emit_op ISZERO [flag];
      emit_inst ASSERT [valid] [];
      comp_return len od) early = (len,sa) /\
  compile_array_membership_loop needle (Var basesrc) len 32 32
    (compile_ptr_load F imm LocMemory) is_in sa = (op,sb) /\
  fn_has_code early sa fn /\ fn_has_code sa sb fn /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = early.cs_current_bb /\ s.vs_inst_idx = LENGTH early.cs_current_insts /\
  stmt_state_rel ctx fn cenv cx es s /\
  vv_at cenv cx (ArrayT ety (Dynamic cap)) sc sd es tvv (LocatedValue ann p) s /\
  ptr_vv_ok cx (ArrayT ety (Dynamic cap)) tvv (LocatedValue ann p) es G tn s /\
  p.ptr_location = LocMemory /\ p.ptr_operand = Var basesrc /\
  read_result cx tvv es = (INL (ArrayV (DynArrayV vs)),es) /\
  evaluate_type (get_tenv cx) (ArrayT ety (Dynamic cap)) = SOME (ArrayTV tv (Dynamic cap)) /\
  evaluate_type (get_tenv cx) ety = SOME tv /\ is_word_type ety /\
  value_has_type (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) /\
  lookup_var basesrc s = SOME bw /\ not_fresh_at early basesrc /\
  cap < dimword (:256) /\
  (!x. needle = Var x ==> not_fresh_at early x) /\
  eval_operand needle s = SOME w /\ op_prov G needle = NONE /\ op_taint tn needle = {} ==>
  ?G' tn' t. gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    membership_loop_frame early G tn s G' tn' t /\
    eval_operand op t = SOME (bool_to_word
      (if is_in then MEM w (MAP (typed_val_to_w256 tv) vs)
       else ~MEM w (MAP (typed_val_to_w256 tv) vs))) /\
    op_prov G' op = NONE /\ op_taint tn' op = {} /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `~is_word_type (ArrayT ety (Dynamic cap))` by simp[is_word_type_def] >>
  drule_all membership_memory_header_entry >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `!x. len = Var x ==> not_fresh_at sa x` by
    (drule (SRULE [] (GEN_ALL membership_runtime_header_layout)) >>
     simp[not_fresh_at_def]) >>
  `eval_operand needle sh = SOME w /\ op_prov Gh needle = NONE /\
   op_taint tnh needle = {}` by
    (drule_all membership_loop_frame_operand >> simp[]) >>
  `membership_load_contract D ctx fn PG sa 32 F imm LocMemory
     (MAP (typed_val_to_w256 tv) vs) Gh tnh sh` by
    (irule membership_memory_load_contract_source >> simp[] >>
     goal_assum (drule_at (Pat `vv_at _ _ _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `compile_array_membership_loop _ _ _ _ _ _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `membership_loop_frame _ _ _ _ _ _ _`)) >>
     simp[] >> metis_tac[]) >>
  `LENGTH vs < dimword (:256)` by
    (fs[value_has_type_def] >> decide_tac) >>
  `!x. needle = Var x ==> not_fresh_at sa x` by metis_tac[] >>
  drule_at (Pat `membership_load_contract _ _ _ _ _ _ _ _ _ _ _ _ _`)
    membership_loop_conditional >> simp[] >>
  disch_then drule_all >> strip_tac >>
  `membership_loop_frame early G tn s G' tn' t` by
    metis_tac[membership_loop_frame_source] >>
  qpat_x_assum `gas_path_ptr _ _ _ _ _ G tn s _ Gh tnh _`
    (mp_then Any mp_tac gas_path_ptr_then) >>
  disch_then drule >> simp[] >> strip_tac >>
  goal_assum (drule_at (Pat `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ _`)) >> simp[]
QED
