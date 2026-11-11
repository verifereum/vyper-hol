Theory bodyPtrBopInRuntimeEntry
Ancestors bodyPtrBopInRuntimeContracts bodyPtrBopInContractTransport
  bodyPtrBopInHeaderControl bodyPtrBopInElementLoad bodyPtrBopInLoopContract
  bodyPtrDefs loweringPosts exprSimVVFrame exprLowering venomState ptrDiscipline finite_map
  fragGasPathPtr bodyPtrBopInHeaderCode bodyPtrBopInHeaderLoad

(* Narrow post transport uses a frontier at which the base is old. This
   need not be the later loop frontier at which header outputs are old. *)
Theorem membership_frame_located_ptr_ok:
  membership_loop_frame sa G0 tn0 s0 G tn s /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sa x) /\
  ptr_vv_ok cx ty tvv (LocatedValue ann p) es G0 tn0 s0 ==>
  ptr_vv_ok cx ty tvv (LocatedValue ann p) es G tn s
Proof
  strip_tac >> drule_all membership_loop_frame_operand >> strip_tac >>
  simp[ptr_vv_ok_def] >>
  conj_tac >- fs[ptr_vv_ok_def] >>
  conj_tac >- fs[ptr_vv_ok_def] >>
  conj_tac
  >- (strip_tac >>
      `?v. read_result cx tvv es = (INL v,es) /\
           ptr_mem_ok cx ty v p.ptr_operand G0 tn0 s0` by fs[ptr_vv_ok_def] >>
      goal_assum (drule_at Any) >>
      metis_tac[membership_frame_ptr_mem_ok]) >>
  fs[ptr_vv_ok_def, membership_loop_frame_def] >>
  qpat_x_assum `s = _` (fn th => once_rewrite_tac[th]) >> simp[]
QED

Theorem membership_frame_located_holds:
  membership_loop_frame sa (G0:string |-> num # num) tn0 s0 G tn s /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sa x) /\
  vv_holds cenv cx ty tvv (LocatedValue ann p) es s0 ==>
  vv_holds cenv cx ty tvv (LocatedValue ann p) es s
Proof
  strip_tac >>
  `eval_operand p.ptr_operand s = eval_operand p.ptr_operand s0` by
    metis_tac[membership_loop_frame_operand] >>
  irule exprSimVVFrameTheory.vv_holds_vars_frame >> qexists_tac `s0` >>
  simp[contextTheory.vv_operand_def] >> fs[membership_loop_frame_def] >>
  qpat_x_assum `s = _` (fn th => once_rewrite_tac[th]) >>
  simp[contract_storage_def, contract_transient_def]
QED

Theorem membership_frame_local_region:
  membership_loop_frame sa G0 tn0 s0 G tn s /\
  local_ptrs_reserved cenv sa ==>
  (local_region cenv scopes s n b sz <=> local_region cenv scopes s0 n b sz)
Proof
  simp[membership_loop_frame_def, loweringStateRelDefsTheory.local_ptrs_reserved_def,
       loweringStateRelDefsTheory.local_region_def] >> rpt strip_tac >>
  eq_tac >> strip_tac >> goal_assum (drule_at Any) >>
  metis_tac[]
QED

Theorem membership_frame_located_at:
  membership_loop_frame sa (G0:string |-> num # num) tn0 s0 G tn s /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sa x) /\
  local_ptrs_reserved cenv sa /\
  vv_at cenv cx ty sc sd es tvv (LocatedValue ann p) s0 ==>
  vv_at cenv cx ty sc sd es tvv (LocatedValue ann p) s
Proof
  strip_tac >> drule_all membership_loop_frame_operand >> strip_tac >>
  `!n b sz. local_region cenv es.scopes s n b sz <=>
            local_region cenv es.scopes s0 n b sz` by
    metis_tac[membership_frame_local_region] >>
  irule exprSimVVFrameTheory.vv_at_vars_frame >>
  qexistsl_tac [`s0`, `sd`] >> simp[contextTheory.vv_operand_def] >>
  fs[membership_loop_frame_def] >>
  qpat_x_assum `s = _` (fn th => once_rewrite_tac[th]) >> simp[]
QED

Theorem membership_header_frame:
  hdr = "%" ++ toString sa.cs_next_var /\
  flag = "%" ++ toString (sa.cs_next_var+1) /\
  valid = "%" ++ toString (sa.cs_next_var+2) /\
  t = (update_var valid 1w (update_var flag 0w (update_var hdr (n2w n) s))
    with vs_inst_idx := pc) /\
  tn' = (tn with t_var := tn.t_var |+ (hdr,{}) |+ (flag,{}) |+ (valid,{})) /\
  (!x. x <> hdr ==> FLOOKUP G1 x = FLOOKUP G x) /\
  (!x. x <> flag /\ x <> valid ==> FLOOKUP G' x = FLOOKUP G1 x) ==>
  membership_loop_frame sa G tn s G' tn' t
Proof
  strip_tac >> simp[membership_loop_frame_def] >> conj_tac
  >- (rpt strip_tac >>
      `x <> hdr /\ x <> flag /\ x <> valid` by
        gvs[loweringStateRelDefsTheory.not_fresh_at_def] >>
      gvs[lookup_var_def, update_var_def, FLOOKUP_UPDATE,
           op_taint_def] >> metis_tac[]) >>
  simp[update_var_def, venom_state_component_equality]
QED

Theorem membership_header_frontier:
  (do len <- compile_ptr_load F imm loc arr;
      flag <- emit_op GT [len;Lit (n2w cap)];
      valid <- emit_op ISZERO [flag];
      emit_inst ASSERT [valid] [];
      comp_return len od) sa = (len,sb) ==>
  !x. not_fresh_at sa x ==> not_fresh_at sb x
Proof
  strip_tac >>
  drule (SRULE [] (GEN_ALL bodyPtrBopInHeaderCodeTheory.membership_runtime_header_layout)) >>
  strip_tac >> simp[loweringStateRelDefsTheory.not_fresh_at_def] >> rpt strip_tac >>
  gvs[]
QED

(* HeaderLoad supplies the concrete checked load; this boundary retains
   both frontiers rather than asserting the header preserves late names. *)
Theorem membership_generated_header_entry:
  (do len <- compile_ptr_load F imm loc arr;
      flag <- emit_op GT [len;Lit (n2w cap)];
      valid <- emit_op ISZERO [flag];
      emit_inst ASSERT [valid] [];
      comp_return len od) sa = (len,sb) /\ fn_has_code sa sb fn /\
  hdr = "%" ++ toString sa.cs_next_var /\
  flag = "%" ++ toString (sa.cs_next_var+1) /\
  valid = "%" ++ toString (sa.cs_next_var+2) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\ n <= cap /\ cap < dimword(:256) /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  gas_path_ptr D 0 ctx fn PG G tn s 0 G1
    (tn with t_var := tn.t_var |+ (hdr,{}))
    (OK (update_var hdr (n2w n) s with vs_inst_idx := SUC s.vs_inst_idx)) /\
  FLOOKUP G1 hdr = NONE /\
  (!x. x <> hdr ==> FLOOKUP G1 x = FLOOKUP G x) ==>
  ?Gh tnh sh.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gh tnh (OK sh) /\
    membership_loop_frame sa G tn s Gh tnh sh /\
    (!x. not_fresh_at sa x ==> not_fresh_at sb x) /\
    sh.vs_current_bb = sb.cs_current_bb /\
    sh.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sh.vs_halted /\
    eval_operand len sh = SOME (n2w n) /\
    op_prov Gh len = NONE /\ op_taint tnh len = {}
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_all membership_generated_header_capacity_path >> strip_tac >>
  `membership_loop_frame sa G tn s G' tn' t` by
    (irule membership_header_frame >> metis_tac[]) >>
  `hdr <> flag /\ hdr <> valid` by gvs[] >>
  `eval_operand (Var hdr) t = SOME (n2w n) /\
   op_prov G' (Var hdr) = NONE /\ op_taint tn' (Var hdr) = {} /\
   ~t.vs_halted` by
    (irule membership_header_result_clean >> metis_tac[]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at sb x` by
    (drule membership_header_frontier >> simp[]) >>
  drule (SRULE [] (GEN_ALL bodyPtrBopInHeaderCodeTheory.membership_runtime_header_layout)) >>
  strip_tac >> qexistsl_tac [`G'`, `tn'`, `t`] >>
  gvs[update_var_def]
QED

Theorem membership_header_loop_init:
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load F imm loc) is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\ ~sh.vs_halted /\
  sh.vs_current_bb = sa.cs_current_bb /\
  sh.vs_inst_idx = LENGTH sa.cs_current_insts /\
  gas_path_ptr D 0 ctx fn PG G0 tn0 s0 0 Gh tnh (OK sh) /\
  membership_loop_frame early G0 tn0 s0 Gh tnh sh /\
  (!x. not_fresh_at early x ==> not_fresh_at sa x) ==>
  ?G' tn' t.
    gas_path_ptr D 0 ctx fn PG G0 tn0 s0 0 G' tn' (OK t) /\
    membership_loop_frame sa Gh tnh sh G' tn' t /\
    membership_loop_frame early G0 tn0 s0 G' tn' t /\
    membership_loop_registers sa 0 0w G' tn' t /\ ~t.vs_halted /\
    t.vs_current_bb = fresh_label_output "in_cond" (sa.cs_next_label+1) /\
    t.vs_inst_idx = 0
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_all membership_loop_contract_init >>
  disch_then (qspecl_then [`tnh`, `PG`, `Gh`, `D`] strip_assume_tac) >>
  qexistsl_tac [`G'`, `tn'`, `t`] >> simp[] >> conj_tac
  >- (qpat_x_assum `gas_path_ptr _ _ _ _ _ G0 tn0 s0 _ Gh tnh _`
        (mp_then Any mp_tac gas_path_ptr_then) >>
      disch_then drule >> simp[]) >>
  metis_tac[membership_loop_frame_source]
QED

Theorem membership_memory_header_entry:
  (do len <- compile_ptr_load F imm LocMemory (Var basesrc);
      flag <- emit_op GT [len;Lit (n2w cap)];
      valid <- emit_op ISZERO [flag];
      emit_inst ASSERT [valid] [];
      comp_return len od) sa = (len,sb) /\ fn_has_code sa sb fn /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\ cap < dimword(:256) /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  stmt_state_rel ctx fn cenv cx es s /\
  vv_at cenv cx aty sc sd es tvv (LocatedValue ann p) s /\
  ptr_vv_ok cx aty tvv (LocatedValue ann p) es G tn s /\
  p.ptr_location = LocMemory /\ p.ptr_operand = Var basesrc /\
  read_result cx tvv es = (INL (ArrayV (DynArrayV vs)),es) /\
  evaluate_type (get_tenv cx) aty = SOME (ArrayTV tv (Dynamic cap)) /\
  value_has_type (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) /\
  ~is_word_type aty /\ lookup_var basesrc s = SOME bw ==>
  ?Gh tnh sh.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gh tnh (OK sh) /\
    membership_loop_frame sa G tn s Gh tnh sh /\
    (!x. not_fresh_at sa x ==> not_fresh_at sb x) /\
    sh.vs_current_bb = sb.cs_current_bb /\
    sh.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sh.vs_halted /\
    eval_operand len sh = SOME (n2w (LENGTH vs)) /\
    op_prov Gh len = NONE /\ op_taint tnh len = {}
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_all membership_runtime_header_code >> strip_tac >>
  gnvs[] >>
  drule_at (Pat `vv_at _ _ _ _ _ _ _ _ _`) (GEN_ALL membership_memory_header_path) >>
  simp[] >> disch_then drule_all >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  irule membership_generated_header_entry >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem membership_code_header_entry:
  (do len <- compile_ptr_load F imm LocCode arr_op;
      flag <- emit_op GT [len;Lit (n2w cap)];
      valid <- emit_op ISZERO [flag];
      emit_inst ASSERT [valid] [];
      comp_return len od) sa = (len,sb) /\ fn_has_code sa sb fn /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\ cap < dimword(:256) /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  stmt_state_rel ctx fn cenv cx es s /\ ~cenv.ce_is_ctor /\
  immutable_holds cenv cx (ArrayT ety (Dynamic cap)) (Value (ArrayV av)) bw es s /\
  evaluate_type (get_tenv cx) ety = SOME tv /\
  value_has_type (ArrayTV tv (Dynamic cap)) (ArrayV av) /\
  eval_operand arr_op s = SOME bw /\ op_taint tn arr_op = {} ==>
  ?Gh tnh sh.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gh tnh (OK sh) /\
    membership_loop_frame sa G tn s Gh tnh sh /\
    (!x. not_fresh_at sa x ==> not_fresh_at sb x) /\
    sh.vs_current_bb = sb.cs_current_bb /\
    sh.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sh.vs_halted /\
    eval_operand len sh = SOME (n2w (array_length (ArrayTV tv (Dynamic cap)) av)) /\
    op_prov Gh len = NONE /\ op_taint tnh len = {}
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_all membership_runtime_header_code >> strip_tac >> gnvs[] >>
  drule_at (Pat `immutable_holds _ _ _ _ _ _ _`) (GEN_ALL membership_code_header_path) >>
  simp[] >> disch_then drule_all >>
  disch_then (qspecl_then [`PG`, `G`, `D`] strip_assume_tac) >>
  irule membership_generated_header_entry >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem membership_slot_header_entry:
  (do len <- compile_ptr_load F imm (if tr then LocTransient else LocStorage) arr_op;
      flag <- emit_op GT [len;Lit (n2w cap)];
      valid <- emit_op ISZERO [flag];
      emit_inst ASSERT [valid] [];
      comp_return len od) sa = (len,sb) /\ fn_has_code sa sb fn /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\ cap < dimword(:256) /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  storage_holds cx tr (ArrayT ety (Dynamic cap)) tvv bw es s /\
  ptr_vv_ok cx (ArrayT ety (Dynamic cap)) tvv (LocatedValue ann p) es G tn s /\
  p.ptr_location = (if tr then LocTransient else LocStorage) /\
  p.ptr_operand = arr_op /\ eval_operand arr_op s = SOME bw /\
  read_result cx tvv es = (INL (ArrayV av),es) /\
  evaluate_type (get_tenv cx) ety = SOME tv ==>
  ?Gh tnh sh.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gh tnh (OK sh) /\
    membership_loop_frame sa G tn s Gh tnh sh /\
    (!x. not_fresh_at sa x ==> not_fresh_at sb x) /\
    sh.vs_current_bb = sb.cs_current_bb /\
    sh.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sh.vs_halted /\
    eval_operand len sh = SOME (n2w (array_length (ArrayTV tv (Dynamic cap)) av)) /\
    op_prov Gh len = NONE /\ op_taint tnh len = {}
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_all membership_runtime_header_code >> strip_tac >>
  Cases_on `tr` >> gnvs[] >>
  drule_at (Pat `storage_holds _ _ _ _ _ _ _`) (GEN_ALL membership_slot_header_path) >>
  simp[] >> disch_then drule_all >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  irule membership_generated_header_entry >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED
