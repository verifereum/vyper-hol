Theory bodyPtrBopInBoundedMemory
Ancestors bodyPtrBopInBoundedAddress bodyPtrBopInBoundedLayout
  bodyPtrBopInElementLoad bodyPtrBopInRuntimeEntry bodyPtrBopInHeaderLoad
  bodyPtrBopInRuntimeContracts bodyPtrBopInEncodedElements bodyPtrBopInLoopContract
  bodyPtrDefs loweringStateRelDefs venomState ptrDiscipline finite_map vyperArray
  vyperTyping vyperValueOperation context compileEnv fragGasPathPtr arithmetic venomInst
  list rich_list

Theorem membership_memory_length_header_entry:
  compile_ptr_load F imm LocMemory (Var basesrc) sa = (len,sb) /\ fn_has_code sa sb fn /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
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
    (!x. len = Var x ==> not_fresh_at sb x) /\
    sh.vs_current_bb = sb.cs_current_bb /\
    sh.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sh.vs_halted /\
    eval_operand len sh = SOME (n2w (LENGTH vs)) /\
    op_prov Gh len = NONE /\ op_taint tnh len = {} /\ LENGTH vs <= cap
Proof
  strip_tac >> drule_all membership_length_header_code >> strip_tac >> fs[] >>
  drule_at (Pat `vv_at _ _ _ _ _ _ _ _ _`) (GEN_ALL membership_memory_header_path) >>
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

Theorem membership_bounded_memory_load_path:
  compile_array_membership_loop needle arr len stride skip
    (compile_ptr_load F imm LocMemory) (SOME cap) is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  membership_loop_frame sa G0 tn0 s0 G tn s /\
  membership_loop_registers sa i r G tn s /\
  s.vs_current_bb = fresh_label_output "in_body" (sa.cs_next_label+2) /\
  delta = (if 0 < skip then 1 else 0) /\ s.vs_inst_idx = 2+delta /\
  src = "%" ++ toString (sa.cs_next_var+6+delta) /\
  dst = "%" ++ toString (sa.cs_next_var+7+delta) /\
  lookup_var src s = SOME w /\ ptr_covers G tn src s 32 /\
  mem_word_taint tn.t_mem (w2n w) = {} ==>
  ?G' tn' t.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    membership_loop_frame sa G0 tn0 s0 G' tn' t /\
    membership_loop_registers sa i r G' tn' t /\
    t = (update_var dst (mload (w2n w) s) s with vs_inst_idx := 3+delta) /\
    FLOOKUP G' dst = NONE /\ op_taint tn' (Var dst) = {}
Proof
  strip_tac >> drule_all membership_bounded_compiled_load_lookup >> strip_tac >>
  `get_instruction bb s.vs_inst_idx = SOME
    (mk_inst (sa.cs_next_id+11+delta) MLOAD [Var src] [dst])` by gvs[] >>
  drule_at (Pat `get_instruction _ _ = _`) membership_positioned_mload_path >>
  gvs[] >> disch_then drule_all >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  goal_assum (drule_at Any) >>
  qexists_tac `tn with t_var := tn.t_var |+
    ("%" ++ toString (sa.cs_next_var+7+(if 0 < skip then 1 else 0)),{})` >>
  fs[ADD1, op_taint_def, FLOOKUP_UPDATE] >> reverse conj_tac
  >- (irule membership_registers_scalar_update >> simp[] >>
      qexistsl_tac [`G`, `tn`] >> simp[op_taint_def, FLOOKUP_UPDATE]) >>
  irule membership_frame_scalar_update >>
  conj_tac >- simp[not_fresh_at_def] >>
  qexistsl_tac [`G`, `tn`] >> simp[op_taint_def, FLOOKUP_UPDATE]
QED

Theorem membership_bounded_memory_array_element_source:
  compile_array_membership_loop needle (Var basesrc) len 32 prefix
    (compile_ptr_load F imm LocMemory) (SOME bound) is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  membership_loop_frame early G0 tn0 s0 Gh tnh sh /\
  (!x. not_fresh_at early x ==> not_fresh_at sa x) /\
  membership_loop_frame sa Gh tnh sh G tn s /\
  membership_loop_registers sa i r G tn s /\
  s.vs_current_bb = fresh_label_output "in_body" (sa.cs_next_label+2) /\
  s.vs_inst_idx = 0 /\ not_fresh_at early basesrc /\
  stmt_state_rel ctx fn cenv cx es s0 /\
  vv_at cenv cx aty sc sd es tvv (LocatedValue ann p) s0 /\
  ptr_vv_ok cx aty tvv (LocatedValue ann p) es G0 tn0 s0 /\
  p.ptr_location = LocMemory /\ p.ptr_operand = Var basesrc /\
  read_result cx tvv es = (INL (ArrayV av),es) /\
  evaluate_type (get_tenv cx) aty = SOME (ArrayTV tv bd) /\
  ~is_word_type aty /\ is_word_type ety /\
  evaluate_type (get_tenv cx) ety = SOME tv /\ value_has_type tv v /\
  ((?vs. av = DynArrayV vs /\ bd = Dynamic cap /\
      prefix = 32 /\ i < LENGTH vs /\ v = EL i vs) \/
   (?kvs. av = SArrayV kvs /\ bd = Fixed cap /\
      prefix = 0 /\ v = (case ALOOKUP kvs i of SOME x => x | NONE => default_value tv))) /\
  i < cap /\ lookup_var basesrc s0 = SOME bw /\
  delta = (if 0 < prefix then 1 else 0) /\
  dst = "%" ++ toString (sa.cs_next_var+7+delta) ==>
  ?G' tn' t.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    membership_loop_frame sa Gh tnh sh G' tn' t /\
    membership_loop_registers sa i r G' tn' t /\
    t.vs_current_bb = s.vs_current_bb /\ t.vs_inst_idx = 3+delta /\
    ~t.vs_halted /\ lookup_var dst t = SOME (typed_val_to_w256 tv v) /\
    FLOOKUP G' dst = NONE /\ op_taint tn' (Var dst) = {}
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `op_taint tn0 (Var basesrc) = {}` by
    (fs[ptr_vv_ok_def] >> metis_tac[]) >>
  `not_fresh_at sa basesrc` by metis_tac[] >>
  `eval_operand (Var basesrc) s0 = SOME bw` by simp[eval_operand_def] >>
  `eval_operand (Var basesrc) sh = SOME bw /\
   op_prov Gh (Var basesrc) = op_prov G0 (Var basesrc) /\
   op_taint tnh (Var basesrc) = {}` by
    (qpat_assum `membership_loop_frame early G0 tn0 s0 Gh tnh sh`
       (mp_then Any mp_tac membership_loop_frame_operand) >>
     disch_then (qspec_then `Var basesrc` mp_tac) >> simp[]) >>
  drule (SRULE [] (GEN_ALL membership_bounded_runtime_address_prefix)) >>
  simp[] >> disch_then drule_all >>
  disch_then (qspecl_then [`PG`, `D`]
    (qx_choose_then `G1` (qx_choose_then `tn1` (qx_choose_then `q` strip_assume_tac)))) >>
  `membership_loop_frame early G0 tn0 s0 G1 tn1 q` by
    metis_tac[membership_loop_frame_source] >>
  rule_assum_tac (SRULE [op_prov_def]) >>
  `FLOOKUP G1 ("%" ++ toString (sa.cs_next_var+6+delta)) = FLOOKUP G0 basesrc` by
    (gvs[] >> metis_tac[]) >>
  gnvs[] >>
  drule_at (Pat `membership_loop_frame early _ _ _ G1 tn1 q`)
    (SIMP_RULE (srw_ss() ++ ARITH_ss) [] (GEN_ALL membership_memory_array_read)) >>
  disch_then drule_all >> strip_tac >>
  drule (SRULE [] (GEN_ALL membership_bounded_memory_load_path)) >>
  disch_then (drule_at (Pat `membership_loop_frame sa Gh tnh sh G1 tn1 q`)) >>
  disch_then (drule_at (Pat `membership_loop_registers _ _ _ G1 tn1 q`)) >>
  gvs[] >> disch_then drule_all >>
  disch_then (qspecl_then [`PG`, `D`]
    (qx_choose_then `G2` (qx_choose_then `tn2` strip_assume_tac))) >>
  qmatch_asmsub_abbrev_tac `membership_loop_frame sa Gh tnh sh G2 tn2 t` >>
  qexistsl_tac [`G2`, `tn2`, `t`] >>
  simp[Abbr `t`, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  qpat_x_assum `gas_path_ptr _ _ _ _ _ G tn s _ G1 tn1 _`
    (mp_then Any mp_tac gas_path_ptr_then) >>
  disch_then drule >> simp[update_var_def]
QED

Theorem membership_bounded_memory_load_contract_source:
  compile_array_membership_loop needle (Var basesrc) len 32 32
    (compile_ptr_load F imm LocMemory) (SOME cap) is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\ not_fresh_at early basesrc /\
  membership_loop_frame early G0 tn0 s0 Gh tnh sh /\
  (!x. not_fresh_at early x ==> not_fresh_at sa x) /\
  stmt_state_rel ctx fn cenv cx es s0 /\
  vv_at cenv cx (ArrayT ety (Dynamic cap)) sc sd es tvv (LocatedValue ann p) s0 /\
  ptr_vv_ok cx (ArrayT ety (Dynamic cap)) tvv (LocatedValue ann p) es G0 tn0 s0 /\
  p.ptr_location = LocMemory /\ p.ptr_operand = Var basesrc /\
  read_result cx tvv es = (INL (ArrayV (DynArrayV vs)),es) /\
  evaluate_type (get_tenv cx) (ArrayT ety (Dynamic cap)) = SOME (ArrayTV tv (Dynamic cap)) /\
  is_word_type ety /\ evaluate_type (get_tenv cx) ety = SOME tv /\
  value_has_type (ArrayTV tv (Dynamic cap)) (ArrayV (DynArrayV vs)) /\
  lookup_var basesrc s0 = SOME bw ==>
  membership_element_load_contract D ctx fn PG sa 4
    (Var ("%" ++ toString (sa.cs_next_var+8)))
    (MAP (typed_val_to_w256 tv) vs) Gh tnh sh
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  pure_rewrite_tac[membership_element_load_contract_def] >>
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `?v. array_index (ArrayTV tv (Dynamic cap)) (DynArrayV vs) (&i) = SOME v /\
       value_has_type tv v /\
       EL i (MAP (typed_val_to_w256 tv) vs) = typed_val_to_w256 tv v` by
    (irule membership_dynamic_encoded_element >> simp[] >> metis_tac[]) >>
  `i < cap /\ i < LENGTH vs /\ v = EL i vs` by
    (gvs[array_index_dyn, oEL_THM] >> fs[value_has_type_def]) >>
  drule (GEN_ALL membership_bounded_memory_array_element_source) >>
  disch_then (drule_at (Pat `vv_at _ _ _ _ _ _ _ _ _`)) >>
  gvs[is_word_type_def] >> disch_then drule_all >> simp[] >>
  disch_then (qspecl_then [`PG`, `D`]
    (qx_choose_then `Go` (qx_choose_then `tno` (qx_choose_then `t` strip_assume_tac)))) >>
  qexistsl_tac [`Go`, `tno`, `t`] >>
  gvs[eval_operand_def, op_prov_def]
QED

Theorem membership_bounded_memory_prepare:
  compile_ptr_load F imm LocMemory (Var basesrc) early = (len,sa) /\
  compile_array_membership_loop needle (Var basesrc) len 32 32
    (compile_ptr_load F imm LocMemory) (SOME cap) is_in sa = (op,sb) /\
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
  lookup_var basesrc s = SOME bw /\ not_fresh_at early basesrc /\ cap < dimword (:256) /\
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
  `~is_word_type (ArrayT ety (Dynamic cap))` by simp[is_word_type_def] >>
  drule_all membership_memory_length_header_entry >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `eval_operand needle sh = SOME w /\ op_prov Gh needle = NONE /\
   op_taint tnh needle = {}` by
    (drule_all membership_loop_frame_operand >> simp[]) >>
  `membership_element_load_contract D ctx fn PG sa 4
     (Var ("%" ++ toString (sa.cs_next_var+8)))
     (MAP (typed_val_to_w256 tv) vs) Gh tnh sh` by
    (irule membership_bounded_memory_load_contract_source >> simp[] >>
     goal_assum (drule_at (Pat `vv_at _ _ _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `compile_array_membership_loop _ _ _ _ _ _ _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `membership_loop_frame _ _ _ _ _ _ _`)) >>
     simp[] >> metis_tac[]) >>
  qexistsl_tac [`Gh`, `tnh`, `sh`] >> simp[] >> metis_tac[]
QED
