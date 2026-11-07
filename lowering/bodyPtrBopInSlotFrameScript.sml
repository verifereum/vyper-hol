Theory bodyPtrBopInSlotFrame
Ancestors bodyPtrBopInSlotLoad bodyPtrBopInRuntimeContracts
  bodyPtrBopInLoopContract loweringPosts venomState

Theorem membership_frame_storage_holds:
  membership_loop_frame early G0 tn0 s0 G tn s /\
  storage_holds cx tr ty tvv bw es s0 ==>
  storage_holds cx tr ty tvv bw es s
Proof
  strip_tac >> drule membership_frame_slot_state >> strip_tac >>
  fs[storage_holds_def, contract_storage_def, contract_transient_def]
QED

Theorem membership_frame_slot_holds:
  membership_loop_frame early G0 tn0 s0 G tn s /\
  (!x. arr_op = Var x ==> not_fresh_at early x) /\
  vv_holds cenv cx ty tvv (LocatedValue ann p) es s0 /\
  p.ptr_location = (if tr then LocTransient else LocStorage) /\
  p.ptr_operand = arr_op /\ eval_operand arr_op s0 = SOME bw ==>
  vv_holds cenv cx ty tvv (LocatedValue ann p) es s
Proof
  strip_tac >> drule_all membership_located_slot_holds >> disch_tac >>
  drule_all membership_frame_storage_holds >> disch_tac >>
  `s.vs_labels = s0.vs_labels` by
    (fs[membership_loop_frame_def] >>
     qpat_x_assum `s = _` (fn th => once_rewrite_tac[th]) >> simp[]) >>
  `eval_operand arr_op s = eval_operand arr_op s0` by
    (Cases_on `arr_op` >> fs[membership_loop_frame_def, eval_operand_def]) >>
  Cases_on `tr` >> gvs[vv_holds_def]
QED
