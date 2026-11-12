Theory bodyPtrBopInBoundedSlot
Ancestors bodyPtrBopInBoundedAddress bodyPtrBopInBoundedLayout
  bodyPtrBopInSlotLoad bodyPtrBopInSlotFrame bodyPtrBopInRuntimeContracts
  bodyPtrBopInHeaderLoad bodyPtrBopInEncodedElements bodyPtrBopInLoopContract
  bodyPtrDefs loweringStateRelDefs venomState ptrDiscipline finite_map
  vyperArray vyperTyping vyperValueOperation context compileEnv fragGasPathPtr
  arithmetic venomInst

Theorem membership_slot_length_header_entry:
  compile_ptr_load F imm (if tr then LocTransient else LocStorage) arr_op sa = (len,sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
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
    (!x. len = Var x ==> not_fresh_at sb x) /\
    sh.vs_current_bb = sb.cs_current_bb /\
    sh.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sh.vs_halted /\
    eval_operand len sh = SOME (n2w (array_length (ArrayTV tv (Dynamic cap)) av)) /\
    op_prov Gh len = NONE /\ op_taint tnh len = {}
Proof
  strip_tac >> drule_all membership_length_header_code >> strip_tac >>
  `get_instruction bb s.vs_inst_idx = SOME
    (mk_inst sa.cs_next_id (if tr then TLOAD else SLOAD) [arr_op]
      ["%" ++ toString sa.cs_next_var])` by (Cases_on `tr` >> gvs[]) >>
  gnvs[] >>
  drule_at (Pat `storage_holds _ _ _ _ _ _ _`) (GEN_ALL membership_slot_header_path) >>
  simp[] >> disch_then drule_all >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  drule (SRULE [] (GEN_ALL membership_length_header_layout)) >> strip_tac >>
  goal_assum (drule_at (Pat `gas_path_ptr _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  simp[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE,
    op_prov_def, op_taint_def, not_fresh_at_def] >>
  simp[membership_loop_frame_def] >> conj_tac
  >- (rpt strip_tac >>
      `x <> "%" ++ toString sa.cs_next_var` by fs[not_fresh_at_def] >>
      gvs[not_fresh_at_def, lookup_var_def, FLOOKUP_UPDATE, op_taint_def]) >>
  simp[venom_state_component_equality]
QED

Theorem membership_bounded_slot_load_path:
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load F imm (if tr then LocTransient else LocStorage)) (SOME cap) is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  membership_loop_frame sa G0 tn0 s0 G tn s /\
  membership_loop_registers sa i r G tn s /\
  s.vs_current_bb = fresh_label_output "in_body" (sa.cs_next_label+2) /\
  delta = (if 0 < skip then 1 else 0) /\ s.vs_inst_idx = 2+delta /\
  src = "%" ++ toString (sa.cs_next_var+6+delta) /\
  dst = "%" ++ toString (sa.cs_next_var+7+delta) /\
  lookup_var src s = SOME w /\ op_taint tn (Var src) = {} /\
  key_taint (if tr then tn.t_trans else tn.t_stor) w = {} ==>
  ?G' tn' t.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    membership_loop_frame sa G0 tn0 s0 G' tn' t /\
    membership_loop_registers sa i r G' tn' t /\
    t = (update_var dst (if tr then tload w s else sload w s) s
      with vs_inst_idx := 3+delta) /\
    FLOOKUP G' dst = NONE /\ op_taint tn' (Var dst) = {}
Proof
  strip_tac >> drule_all membership_bounded_compiled_load_lookup >> strip_tac >>
  `get_instruction bb s.vs_inst_idx = SOME
    (mk_inst (sa.cs_next_id+11+delta) (if tr then TLOAD else SLOAD)
      [Var src] [dst])` by (Cases_on `tr` >> gvs[]) >>
  drule_at (Pat `get_instruction _ _ = _`) membership_positioned_slot_load_framed_path >>
  disch_then (drule_at (Pat `membership_loop_frame _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `membership_loop_registers _ _ _ _ _ _`)) >>
  gvs[eval_operand_def] >> disch_then drule_all >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`G'`, `tn'`] >> fs[ADD1]
QED

Theorem membership_bounded_slot_array_element_prefix:
  compile_array_membership_loop needle arr_op len 1 prefix
    (compile_ptr_load F imm (if tr then LocTransient else LocStorage)) (SOME cap) is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  membership_loop_frame sa G0 tn0 s0 G tn s /\
  membership_loop_registers sa i r G tn s /\
  s.vs_current_bb = fresh_label_output "in_body" (sa.cs_next_label+2) /\
  s.vs_inst_idx = 0 /\ (!x. arr_op = Var x ==> not_fresh_at sa x) /\
  storage_holds cx tr (ArrayT ety bd) tvv bw es s0 /\
  ptr_vv_ok cx (ArrayT ety bd) tvv (LocatedValue ann p) es G0 tn0 s0 /\
  p.ptr_location = (if tr then LocTransient else LocStorage) /\
  p.ptr_operand = arr_op /\ eval_operand arr_op s0 = SOME bw /\
  read_result cx tvv es = (INL (ArrayV av),es) /\
  is_word_type ety /\ evaluate_type (get_tenv cx) ety = SOME tv /\
  i < array_length (ArrayTV tv bd) av /\
  array_index (ArrayTV tv bd) av (&i) = SOME v /\
  prefix = (case bd of Fixed _ => 0 | Dynamic _ => 1) /\
  delta = (if 0 < prefix then 1 else 0) /\
  dst = "%" ++ toString (sa.cs_next_var+7+delta) ==>
  ?G' tn' t.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    membership_loop_frame sa G0 tn0 s0 G' tn' t /\
    membership_loop_registers sa i r G' tn' t /\
    t.vs_current_bb = s.vs_current_bb /\ t.vs_inst_idx = 3+delta /\
    ~t.vs_halted /\ lookup_var dst t = SOME (typed_val_to_w256 tv v) /\
    FLOOKUP G' dst = NONE /\ op_taint tn' (Var dst) = {}
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `op_taint tn0 arr_op = {}` by (fs[ptr_vv_ok_def] >> metis_tac[]) >>
  drule (SRULE [] (GEN_ALL membership_bounded_runtime_address_prefix)) >>
  simp[] >> disch_then drule_all >>
  disch_then (qspecl_then [`PG`, `D`]
    (qx_choose_then `G1` (qx_choose_then `tn1` (qx_choose_then `q` strip_assume_tac)))) >>
  drule_at (Pat `membership_loop_frame _ _ _ _ G1 tn1 q`)
    (SIMP_RULE (srw_ss() ++ ARITH_ss) [] (GEN_ALL membership_slot_array_read)) >>
  disch_then (drule_at (Pat `storage_holds _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `ptr_vv_ok _ _ _ _ _ _ _ _`)) >>
  fs[] >> disch_then drule_all >> strip_tac >>
  drule (SRULE [] (GEN_ALL membership_bounded_slot_load_path)) >>
  disch_then (drule_at (Pat `membership_loop_frame _ _ _ _ G1 tn1 q`)) >>
  disch_then (drule_at (Pat `membership_loop_registers _ _ _ G1 tn1 q`)) >>
  gvs[] >> disch_then drule_all >>
  disch_then (qspecl_then [`PG`, `D`]
    (qx_choose_then `G2` (qx_choose_then `tn2` strip_assume_tac))) >>
  qmatch_asmsub_abbrev_tac `membership_loop_frame sa G0 tn0 s0 G2 tn2 t` >>
  qexistsl_tac [`G2`, `tn2`, `t`] >>
  simp[Abbr `t`, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  qpat_x_assum `gas_path_ptr _ _ _ _ _ G tn s _ G1 tn1 _`
    (mp_then Any mp_tac gas_path_ptr_then) >>
  disch_then drule >> simp[update_var_def]
QED

Theorem membership_bounded_slot_load_contract:
  compile_array_membership_loop needle arr_op len 1 1
    (compile_ptr_load F imm (if tr then LocTransient else LocStorage)) (SOME cap) is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\
  (!x. arr_op = Var x ==> not_fresh_at sa x) /\
  vv_holds cenv cx (ArrayT ety (Dynamic cap)) tvv (LocatedValue ann p) es s0 /\
  ptr_vv_ok cx (ArrayT ety (Dynamic cap)) tvv (LocatedValue ann p) es G0 tn0 s0 /\
  p.ptr_location = (if tr then LocTransient else LocStorage) /\
  p.ptr_operand = arr_op /\ eval_operand arr_op s0 = SOME bw /\
  read_result cx tvv es = (INL (ArrayV (DynArrayV vs)),es) /\
  is_word_type ety /\ evaluate_type (get_tenv cx) ety = SOME tv /\
  value_has_type (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) ==>
  membership_element_load_contract D ctx fn PG sa 4
    (Var ("%" ++ toString (sa.cs_next_var+8)))
    (MAP (typed_val_to_w256 tv) vs) G0 tn0 s0
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  pure_rewrite_tac[membership_element_load_contract_def] >>
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `?v. array_index (ArrayTV tv (Dynamic cap)) (DynArrayV vs) (&i) = SOME v /\
       value_has_type tv v /\
       EL i (MAP (typed_val_to_w256 tv) vs) = typed_val_to_w256 tv v` by
    (irule membership_dynamic_encoded_element >> simp[] >> metis_tac[]) >>
  drule_all membership_located_slot_holds >> disch_tac >>
  drule (GEN_ALL membership_bounded_slot_array_element_prefix) >>
  disch_then (drule_at (Pat `storage_holds _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `ptr_vv_ok _ _ _ _ _ _ _ _`)) >>
  gvs[array_length_def] >> disch_then drule_all >>
  disch_then (qspecl_then [`PG`, `D`]
    (qx_choose_then `Go` (qx_choose_then `tno` (qx_choose_then `t` strip_assume_tac)))) >>
  qexistsl_tac [`Go`, `tno`, `t`] >>
  gvs[eval_operand_def, op_prov_def]
QED

Theorem membership_bounded_slot_prepare:
  compile_ptr_load F imm (if tr then LocTransient else LocStorage) arr_op early = (len,sa) /\
  compile_array_membership_loop needle arr_op len 1 1
    (compile_ptr_load F imm (if tr then LocTransient else LocStorage)) (SOME cap) is_in sa = (op,sb) /\
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
  (!x. arr_op = Var x ==> not_fresh_at early x) /\ cap < dimword (:256) /\
  (!x. needle = Var x ==> not_fresh_at early x) /\
  eval_operand needle s = SOME w /\ op_prov G needle = NONE /\ op_taint tn needle = {} ==>
  ?Gh tnh sh.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gh tnh (OK sh) /\
    membership_loop_frame early G tn s Gh tnh sh /\
    (!x. not_fresh_at early x ==> not_fresh_at sa x) /\
    (!x. len = Var x ==> not_fresh_at sa x) /\
    (!x. needle = Var x ==> not_fresh_at sa x) /\
    sh.vs_current_bb = sa.cs_current_bb /\
    sh.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~sh.vs_halted /\
    eval_operand len sh = SOME (n2w (LENGTH (MAP (typed_val_to_w256 tv) vs))) /\
    op_prov Gh len = NONE /\ op_taint tnh len = {} /\
    eval_operand needle sh = SOME w /\ op_prov Gh needle = NONE /\ op_taint tnh needle = {} /\
    LENGTH (MAP (typed_val_to_w256 tv) vs) <= cap /\ cap < dimword (:256) /\
    membership_element_load_contract D ctx fn PG sa 4
      (Var ("%" ++ toString (sa.cs_next_var+8)))
      (MAP (typed_val_to_w256 tv) vs) Gh tnh sh
Proof
  strip_tac >>
  drule_all membership_located_slot_holds >> disch_tac >>
  drule_all membership_slot_length_header_entry >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
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
  `membership_element_load_contract D ctx fn PG sa 4
     (Var ("%" ++ toString (sa.cs_next_var+8)))
     (MAP (typed_val_to_w256 tv) vs) Gh tnh sh` by
    (irule membership_bounded_slot_load_contract >> simp[] >>
     goal_assum (drule_at (Pat `vv_holds _ _ _ _ _ _ _`)) >> gvs[] >>
     goal_assum (drule_at (Pat `compile_array_membership_loop _ _ _ _ _ _ _ _ _ = _`)) >>
     simp[] >> metis_tac[]) >>
  qexistsl_tac [`Gh`, `tnh`, `sh`] >>
  fs[array_length_def, value_has_type_def] >> metis_tac[]
QED
