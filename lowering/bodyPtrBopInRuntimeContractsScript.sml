Theory bodyPtrBopInRuntimeContracts
Ancestors bodyPtrBopInEncodedElements bodyPtrBopInElementLoad
  bodyPtrBopInSlotLoad bodyPtrBopInCodeLoad bodyPtrBopInRepresentation
  bodyPtrBopInLoopContract vyperArray vyperTyping vyperValueOperation
  entryDecodeStaticProps list rich_list venomState ptrDiscipline

(* Shared list description: no execution or pointer callback is assumed. *)
Theorem membership_encoded_array_element[local]:
  evaluate_type env et = SOME tv /\
  value_has_type (ArrayTV tv bd) (ArrayV av) /\
  ((?vs cap. av = DynArrayV vs /\ bd = Dynamic cap /\
      ws = MAP (typed_val_to_w256 tv) vs) \/
   (?kvs cap. av = SArrayV kvs /\ bd = Fixed cap /\
      ws = GENLIST (\j. typed_val_to_w256 tv (sparse_val tv kvs j)) cap)) /\
  i < LENGTH ws ==>
  i < array_length (ArrayTV tv bd) av /\
  ?v. array_index (ArrayTV tv bd) av (&i) = SOME v /\
      value_has_type tv v /\ EL i ws = typed_val_to_w256 tv v
Proof
  strip_tac >> gvs[]
  >- (drule_all (SRULE [] o GEN_ALL $ membership_dynamic_encoded_element) >>
      simp[array_length_def])
  >> drule_all (SRULE [] o GEN_ALL $ membership_fixed_encoded_element) >>
  simp[array_length_def]
QED

(* vv_at is vacuous away from memory: contents come from vv_holds,
   while ptr_vv_ok supplies the robust clean pointer post. *)
Theorem membership_located_slot_holds:
  vv_holds cenv cx ty tvv (LocatedValue ann p) es s /\
  p.ptr_location = (if tr then LocTransient else LocStorage) /\
  p.ptr_operand = arr_op /\ eval_operand arr_op s = SOME bw ==>
  storage_holds cx tr ty tvv bw es s
Proof
  Cases_on `tr` >> strip_tac >> gvs[loweringPostsTheory.vv_holds_def, eval_operand_def]
QED

Theorem membership_located_code_holds:
  vv_holds cenv cx ty tvv (LocatedValue ann p) es s /\
  p.ptr_location = LocCode /\ p.ptr_operand = arr_op /\
  eval_operand arr_op s = SOME bw ==>
  immutable_holds cenv cx ty tvv bw es s
Proof
  strip_tac >> gvs[loweringPostsTheory.vv_holds_def, eval_operand_def]
QED

Theorem membership_slot_load_contract:
  compile_array_membership_loop needle arr_op len 1 prefix
    (compile_ptr_load F imm (if tr then LocTransient else LocStorage)) is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\
  (!x. arr_op = Var x ==> not_fresh_at sa x) /\
  vv_holds cenv cx (ArrayT ety bd) tvv (LocatedValue ann p) es s0 /\
  ptr_vv_ok cx (ArrayT ety bd) tvv (LocatedValue ann p) es G0 tn0 s0 /\
  p.ptr_location = (if tr then LocTransient else LocStorage) /\
  p.ptr_operand = arr_op /\ eval_operand arr_op s0 = SOME bw /\
  read_result cx tvv es = (INL (ArrayV av),es) /\
  is_word_type ety /\ evaluate_type (get_tenv cx) ety = SOME tv /\
  value_has_type (ArrayTV tv bd) (ArrayV av) /\
  ((?vs cap. av = DynArrayV vs /\ bd = Dynamic cap /\
      ws = MAP (typed_val_to_w256 tv) vs) \/
   (?kvs cap. av = SArrayV kvs /\ bd = Fixed cap /\
      ws = GENLIST (\j. typed_val_to_w256 tv (sparse_val tv kvs j)) cap)) /\
  prefix = (case bd of Fixed _ => 0 | Dynamic _ => 1) ==>
  membership_load_contract D ctx fn PG sa prefix F imm
    (if tr then LocTransient else LocStorage) ws G0 tn0 s0
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  pure_rewrite_tac[membership_load_contract_def] >>
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_all membership_encoded_array_element >> strip_tac >>
  drule_all membership_located_slot_holds >> disch_tac >>
  drule (GEN_ALL membership_slot_array_element_prefix) >>
  disch_then (drule_at (Pat `storage_holds _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `ptr_vv_ok _ _ _ _ _ _ _ _`)) >>
  gvs[] >> disch_then drule_all >>
  disch_then (qspecl_then [`PG`, `D`]
    (qx_choose_then `Go` (qx_choose_then `tno` (qx_choose_then `t` strip_assume_tac)))) >>
  qexistsl_tac [`Go`, `tno`, `t`] >>
  gvs[eval_operand_def, op_prov_def]
QED

Theorem membership_code_load_contract:
  compile_array_membership_loop needle arr_op len 32 prefix
    (compile_ptr_load F imm LocCode) is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\
  (!x. arr_op = Var x ==> not_fresh_at sa x) /\
  stmt_state_rel ctx fn cenv cx es s0 /\ ~cenv.ce_is_ctor /\
  vv_holds cenv cx (ArrayT ety bd) (Value (ArrayV av)) (LocatedValue ann p) es s0 /\
  ptr_vv_ok cx (ArrayT ety bd) (Value (ArrayV av)) (LocatedValue ann p) es G0 tn0 s0 /\
  p.ptr_location = LocCode /\ p.ptr_operand = arr_op /\
  eval_operand arr_op s0 = SOME bw /\
  is_word_type ety /\ evaluate_type (get_tenv cx) ety = SOME tv /\
  value_has_type (ArrayTV tv bd) (ArrayV av) /\
  ((?vs cap. av = DynArrayV vs /\ bd = Dynamic cap /\
      ws = MAP (typed_val_to_w256 tv) vs) \/
   (?kvs cap. av = SArrayV kvs /\ bd = Fixed cap /\
      ws = GENLIST (\j. typed_val_to_w256 tv (sparse_val tv kvs j)) cap)) /\
  prefix = (case bd of Fixed _ => 0 | Dynamic _ => 32) ==>
  membership_load_contract D ctx fn PG sa prefix F imm LocCode ws G0 tn0 s0
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  pure_rewrite_tac[membership_load_contract_def] >>
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_all membership_encoded_array_element >> strip_tac >>
  drule_all membership_located_code_holds >> disch_tac >>
  `op_taint tn0 arr_op = {}` by
    (fs[bodyPtrDefsTheory.ptr_vv_ok_def] >> metis_tac[]) >>
  drule (GEN_ALL membership_code_array_element_prefix) >>
  disch_then (drule_at (Pat `immutable_holds _ _ _ _ _ _ _`)) >>
  gvs[] >> disch_then drule_all >>
  disch_then (qspecl_then [`PG`, `D`]
    (qx_choose_then `Go` (qx_choose_then `tno` (qx_choose_then `t` strip_assume_tac)))) >>
  qexistsl_tac [`Go`, `tno`, `t`] >>
  gvs[eval_operand_def, op_prov_def]
QED

Theorem membership_memory_load_contract:
  compile_array_membership_loop needle (Var basesrc) len 32 prefix
    (compile_ptr_load F imm LocMemory) is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\ not_fresh_at sa basesrc /\
  stmt_state_rel ctx fn cenv cx es s0 /\
  vv_at cenv cx aty sc sd es tvv (LocatedValue ann p) s0 /\
  ptr_vv_ok cx aty tvv (LocatedValue ann p) es G0 tn0 s0 /\
  p.ptr_location = LocMemory /\ p.ptr_operand = Var basesrc /\
  read_result cx tvv es = (INL (ArrayV av),es) /\
  evaluate_type (get_tenv cx) aty = SOME (ArrayTV tv bd) /\
  ~is_word_type aty /\ is_word_type ety /\
  evaluate_type (get_tenv cx) ety = SOME tv /\
  value_has_type (ArrayTV tv bd) (ArrayV av) /\
  ((?vs. av = DynArrayV vs /\ bd = Dynamic cap /\ prefix = 32 /\
      ws = MAP (typed_val_to_w256 tv) vs) \/
   (?kvs. av = SArrayV kvs /\ bd = Fixed cap /\ prefix = 0 /\
      ws = GENLIST (\j. typed_val_to_w256 tv (sparse_val tv kvs j)) cap)) /\
  lookup_var basesrc s0 = SOME bw ==>
  membership_load_contract D ctx fn PG sa prefix F imm LocMemory ws G0 tn0 s0
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  pure_rewrite_tac[membership_load_contract_def] >>
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `i < array_length (ArrayTV tv bd) av /\
   ?v. array_index (ArrayTV tv bd) av (&i) = SOME v /\
       value_has_type tv v /\ EL i ws = typed_val_to_w256 tv v` by
    (irule membership_encoded_array_element >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `i < cap /\
   ((?vs. av = DynArrayV vs /\ bd = Dynamic cap /\ prefix = 32 /\
       i < LENGTH vs /\ v = EL i vs) \/
    (?kvs. av = SArrayV kvs /\ bd = Fixed cap /\ prefix = 0 /\
       v = (case ALOOKUP kvs i of SOME x => x | NONE => default_value tv)))` by
    (gvs[array_length_def] >>
     gvs[array_index_dyn, oEL_THM, array_index_sarray] >>
     fs[value_has_type_def] >>
     Cases_on `ALOOKUP kvs i` >> gvs[]) >>
  drule (GEN_ALL membership_memory_array_element_prefix) >>
  disch_then (drule_at (Pat `vv_at _ _ _ _ _ _ _ _ _`)) >>
  gvs[] >> disch_then drule_all >>
  disch_then (qspecl_then [`PG`, `D`]
    (qx_choose_then `Go` (qx_choose_then `tno` (qx_choose_then `t` strip_assume_tac)))) >>
  qexistsl_tac [`Go`, `tno`, `t`] >>
  gvs[eval_operand_def, op_prov_def]
QED

Theorem membership_code_load_contract_source:
  compile_array_membership_loop needle arr_op len 32 prefix
    (compile_ptr_load F imm LocCode) is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\
  (!x. arr_op = Var x ==> not_fresh_at early x) /\
  membership_loop_frame early G0 tn0 s0 Gh tnh sh /\
  (!x. not_fresh_at early x ==> not_fresh_at sa x) /\
  stmt_state_rel ctx fn cenv cx es s0 /\ ~cenv.ce_is_ctor /\
  vv_holds cenv cx (ArrayT ety bd) (Value (ArrayV av)) (LocatedValue ann p) es s0 /\
  ptr_vv_ok cx (ArrayT ety bd) (Value (ArrayV av)) (LocatedValue ann p) es G0 tn0 s0 /\
  p.ptr_location = LocCode /\ p.ptr_operand = arr_op /\
  eval_operand arr_op s0 = SOME bw /\
  is_word_type ety /\ evaluate_type (get_tenv cx) ety = SOME tv /\
  value_has_type (ArrayTV tv bd) (ArrayV av) /\
  ((?vs cap. av = DynArrayV vs /\ bd = Dynamic cap /\
      ws = MAP (typed_val_to_w256 tv) vs) \/
   (?kvs cap. av = SArrayV kvs /\ bd = Fixed cap /\
      ws = GENLIST (\j. typed_val_to_w256 tv (sparse_val tv kvs j)) cap)) /\
  prefix = (case bd of Fixed _ => 0 | Dynamic _ => 32) ==>
  membership_load_contract D ctx fn PG sa prefix F imm LocCode ws Gh tnh sh
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  pure_rewrite_tac[membership_load_contract_def] >>
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_all membership_encoded_array_element >> strip_tac >>
  drule_all membership_located_code_holds >> disch_tac >>
  `op_taint tn0 arr_op = {}` by
    (fs[bodyPtrDefsTheory.ptr_vv_ok_def] >> metis_tac[]) >>
  drule (GEN_ALL membership_code_array_element_prefix_source) >>
  disch_then (drule_at (Pat `immutable_holds _ _ _ _ _ _ _`)) >>
  gvs[] >> disch_then drule_all >>
  disch_then (qspecl_then [`PG`, `D`]
    (qx_choose_then `Go` (qx_choose_then `tno` (qx_choose_then `t` strip_assume_tac)))) >>
  qexistsl_tac [`Go`, `tno`, `t`] >>
  gvs[eval_operand_def, op_prov_def]
QED

Theorem membership_memory_load_contract_source:
  compile_array_membership_loop needle (Var basesrc) len 32 prefix
    (compile_ptr_load F imm LocMemory) is_in sa = (op,sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\ not_fresh_at early basesrc /\
  membership_loop_frame early G0 tn0 s0 Gh tnh sh /\
  (!x. not_fresh_at early x ==> not_fresh_at sa x) /\
  stmt_state_rel ctx fn cenv cx es s0 /\
  vv_at cenv cx aty sc sd es tvv (LocatedValue ann p) s0 /\
  ptr_vv_ok cx aty tvv (LocatedValue ann p) es G0 tn0 s0 /\
  p.ptr_location = LocMemory /\ p.ptr_operand = Var basesrc /\
  read_result cx tvv es = (INL (ArrayV av),es) /\
  evaluate_type (get_tenv cx) aty = SOME (ArrayTV tv bd) /\
  ~is_word_type aty /\ is_word_type ety /\
  evaluate_type (get_tenv cx) ety = SOME tv /\
  value_has_type (ArrayTV tv bd) (ArrayV av) /\
  ((?vs. av = DynArrayV vs /\ bd = Dynamic cap /\ prefix = 32 /\
      ws = MAP (typed_val_to_w256 tv) vs) \/
   (?kvs. av = SArrayV kvs /\ bd = Fixed cap /\ prefix = 0 /\
      ws = GENLIST (\j. typed_val_to_w256 tv (sparse_val tv kvs j)) cap)) /\
  lookup_var basesrc s0 = SOME bw ==>
  membership_load_contract D ctx fn PG sa prefix F imm LocMemory ws Gh tnh sh
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  pure_rewrite_tac[membership_load_contract_def] >>
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `i < array_length (ArrayTV tv bd) av /\
   ?v. array_index (ArrayTV tv bd) av (&i) = SOME v /\
       value_has_type tv v /\ EL i ws = typed_val_to_w256 tv v` by
    (irule membership_encoded_array_element >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  `i < cap /\
   ((?vs. av = DynArrayV vs /\ bd = Dynamic cap /\ prefix = 32 /\
       i < LENGTH vs /\ v = EL i vs) \/
    (?kvs. av = SArrayV kvs /\ bd = Fixed cap /\ prefix = 0 /\
       v = (case ALOOKUP kvs i of SOME x => x | NONE => default_value tv)))` by
    (gvs[array_length_def] >>
     gvs[array_index_dyn, oEL_THM, array_index_sarray] >>
     fs[value_has_type_def] >>
     Cases_on `ALOOKUP kvs i` >> gvs[]) >>
  drule (GEN_ALL membership_memory_array_element_prefix_source) >>
  disch_then (drule_at (Pat `vv_at _ _ _ _ _ _ _ _ _`)) >>
  gvs[] >> disch_then drule_all >>
  disch_then (qspecl_then [`PG`, `D`]
    (qx_choose_then `Go` (qx_choose_then `tno` (qx_choose_then `t` strip_assume_tac)))) >>
  qexistsl_tac [`Go`, `tno`, `t`] >>
  gvs[eval_operand_def, op_prov_def]
QED
