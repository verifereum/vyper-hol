Theory bodyPtrBopInSlotHeaderRuntime
Ancestors bodyPtrBopInRuntimeEntry bodyPtrBopInLoopSearch
  bodyPtrBopInRuntimeContracts bodyPtrBopInSlotFrame bodyPtrBopInSlotLoad
  venomState ptrDiscipline compileEnv loweringStateRelDefs vyperValue vyperTyping context
  bodyPtrBopInHeaderCode bodyPtrBopInLoopContract fragGasPathPtr vyperValueOperation

Theorem membership_dynamic_slot_header_runtime:
  (do len <- compile_ptr_load F imm (if tr then LocTransient else LocStorage) arr_op;
      flag <- emit_op GT [len;Lit (n2w cap)];
      valid <- emit_op ISZERO [flag];
      emit_inst ASSERT [valid] [];
      comp_return len od) early = (len,sa) /\
  compile_array_membership_loop needle arr_op len 1 1
    (compile_ptr_load F imm (if tr then LocTransient else LocStorage)) NONE is_in sa = (op,sb) /\
  fn_has_code early sa fn /\ fn_has_code sa sb fn /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = early.cs_current_bb /\ s.vs_inst_idx = LENGTH early.cs_current_insts /\
  vv_holds cenv cx (ArrayT ety (Dynamic cap)) tvv (LocatedValue ann p) es s /\
  ptr_vv_ok cx (ArrayT ety (Dynamic cap)) tvv (LocatedValue ann p) es G tn s /\
  p.ptr_location = (if tr then LocTransient else LocStorage) /\ p.ptr_operand = arr_op /\
  read_result cx tvv es = (INL (ArrayV (DynArrayV vs)),es) /\
  evaluate_type (get_tenv cx) ety = SOME tv /\ is_word_type ety /\
  value_has_type (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) /\
  eval_operand arr_op s = SOME bw /\
  (!x. arr_op = Var x ==> not_fresh_at early x) /\
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
  drule_all membership_located_slot_holds >> disch_tac >>
  drule_all membership_slot_header_entry >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `!x. len = Var x ==> not_fresh_at sa x` by
    (drule (SRULE [] (GEN_ALL membership_runtime_header_layout)) >>
     simp[not_fresh_at_def]) >>
  `eval_operand needle sh = SOME w /\ op_prov Gh needle = NONE /\
   op_taint tnh needle = {}` by
    (drule_all membership_loop_frame_operand >> simp[]) >>
  `vv_holds cenv cx (ArrayT ety (Dynamic cap)) tvv (LocatedValue ann p) es sh` by
    (qpat_assum `membership_loop_frame early G tn s Gh tnh sh`
       (mp_then Any mp_tac membership_frame_slot_holds) >>
     disch_then (drule_at (Pat `vv_holds _ _ _ _ _ _ _`)) >>
     simp[] >> disch_then (qspec_then `tr` mp_tac) >> simp[]) >>
  `ptr_vv_ok cx (ArrayT ety (Dynamic cap)) tvv (LocatedValue ann p) es Gh tnh sh` by
    (irule membership_frame_located_slot_ptr_ok >> simp[] >>
     conj_tac >- metis_tac[] >>
     goal_assum (drule_at (Pat `membership_loop_frame _ _ _ _ _ _ _`)) >> simp[] >> metis_tac[]) >>
  `eval_operand arr_op sh = SOME bw` by
    (qpat_assum `membership_loop_frame early G tn s Gh tnh sh`
       (mp_then Any mp_tac membership_loop_frame_operand) >>
     disch_then (qspec_then `arr_op` mp_tac) >> simp[]) >>
  `membership_load_contract D ctx fn PG sa 1 F imm
     (if tr then LocTransient else LocStorage) (MAP (typed_val_to_w256 tv) vs) Gh tnh sh` by
    (irule membership_slot_load_contract >> simp[] >>
     goal_assum (drule_at (Pat `vv_holds _ _ _ _ _ _ _`)) >> gvs[] >>
     goal_assum (drule_at (Pat `compile_array_membership_loop _ _ _ _ _ _ _ _ _ = _`)) >>
     simp[] >> metis_tac[]) >>
  `LENGTH vs < dimword (:256)` by (fs[value_has_type_def] >> decide_tac) >>
  `!x. needle = Var x ==> not_fresh_at sa x` by metis_tac[] >>
  `eval_operand len sh = SOME (n2w (LENGTH vs))` by fs[array_length_def] >>
  drule_at (Pat `membership_load_contract _ _ _ _ _ _ _ _ _ _ _ _ _`)
    membership_loop_conditional >> simp[] >> disch_then drule_all >> strip_tac >>
  `membership_loop_frame early G tn s G' tn' t` by
    metis_tac[membership_loop_frame_source] >>
  qpat_x_assum `gas_path_ptr _ _ _ _ _ G tn s _ Gh tnh _`
    (mp_then Any mp_tac gas_path_ptr_then) >>
  disch_then drule >> simp[] >> strip_tac >>
  goal_assum (drule_at (Pat `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ _`)) >> simp[]
QED
