(* Stack and borrowed-memory rows keep their original compiler interval. *)
Theory bodyExtSavedValueEndpointMods
Ancestors
  bodyFullPostsMods abiEncodeArgsSim logValueFramePtr exprSimMemDefs
  exprSimProps loweringPosts bodyPtrDefs context venomState ptrDiscipline
  vyperInterpreter vyperState vyperContext vyperValue vyperTypeSystem
  valueEncodingDefs finite_map words pred_set arithmetic

Theorem ext_saved_value_extract[local]:
  ((?tag op. sv = StackValue tag op) \/
   (?p. sv = LocatedValue ty p /\ ~is_word_type ty /\ p.ptr_location = LocMemory)) /\
  read_result cx raw pos = (INL v,pos) /\
  vv_holds_mods cenv cx ty raw sv pos u /\ vv_at cenv cx ty si ss pos raw sv u /\
  ptr_vv_ok cx ty raw sv pos G tn u ==>
  expr_val_at cenv cx ty si ss pos v (vv_operand sv) u /\
  expr_val_rel cx ty v (vv_operand sv) u /\ ptr_val_ok cx ty v (vv_operand sv) G tn u
Proof
  strip_tac >> gvs[vv_operand_def, vv_holds_mods_def, vv_holds_def, ptr_vv_ok_def]
  >- gvs[vv_at_def] >>
  conj_tac >- (irule vv_at_memory_val_at >> metis_tac[]) >>
  gvs[expr_val_rel_def, ptr_val_ok_def]
QED

Theorem ext_saved_value_pack[local]:
  ((?tag op. sv = StackValue tag op) \/
   (?p. sv = LocatedValue ty p /\ ~is_word_type ty /\ p.ptr_location = LocMemory)) /\
  expr_val_at cenv cx ty si ss ee v (vv_operand sv) t /\
  expr_val_rel cx ty v (vv_operand sv) t /\ ptr_val_ok cx ty v (vv_operand sv) G tn t ==>
  vv_holds_mods cenv cx ty (Value v) sv ee t /\
  vv_at cenv cx ty si ss ee (Value v) sv t /\ ptr_vv_ok cx ty (Value v) sv ee G tn t
Proof
  strip_tac >>
  gvs[vv_operand_def, vv_holds_mods_def, vv_holds_def, vv_at_def, ptr_vv_ok_def,
      read_result_def, return_def] >>
  conj_tac >- gvs[expr_val_rel_def] >>
  conj_tac >- gvs[expr_val_at_def, local_place_at_def] >>
  gvs[ptr_val_ok_def]
QED

Theorem ext_saved_value_store_bound[local]:
  vv_store_bound cx ty ty pos raw sv u /\ read_result cx raw pos = (INL v,pos) /\
  eval_operand (vv_operand sv) t = eval_operand (vv_operand sv) u /\
  u.vs_alloca_next <= t.vs_alloca_next ==>
  vv_store_bound cx ty ty ee (Value v) sv t
Proof
  strip_tac >> drule_all_then assume_tac vv_store_bound_frame_mem_src >>
  qpat_x_assum `vv_store_bound _ _ _ _ _ _ u` kall_tac >>
  fs[vv_store_bound_def, read_result_def, return_def] >> metis_tac[]
QED

Theorem ext_saved_value_endpoint_mods:
  ty = lowered_value_type cenv e /\
  ((?tag op. sv = StackValue tag op) \/
   (?p. sv = LocatedValue ty p /\ ~is_word_type ty /\ p.ptr_location = LocMemory)) /\
  (?raw. read_result cx raw pos = (INL v,pos) /\
    vv_holds_mods cenv cx ty raw sv pos u /\ vv_at cenv cx ty si ss pos raw sv u /\
    ptr_vv_ok cx ty raw sv pos G1 tn1 u /\ vv_store_bound cx ty ty pos raw sv u) /\
  (!tag op. sv = StackValue tag op /\ ~is_word_type ty ==> ptr_buf_ok cenv e op G1 u) /\
  (!tag p. sv = LocatedValue tag p /\ p.ptr_location = LocMemory ==>
     ptr_buf_ok cenv e p.ptr_operand G1 u) /\
  (!x. vv_operand sv = Var x ==> not_fresh_at ss x) /\
  stmt_state_rel (H:(bool # bytes32 # type_value) list # num list) ctx func cenv cx pos u /\
  MAP FDOM ee.scopes = MAP FDOM pos.scopes /\ local_ptrs_reserved cenv ss /\
  wb_frame cenv pos ee ss u t /\ ghost_kept_at lo cenv pos ss G1 tn1 u G2 tn2 /\
  (!x w. not_fresh_at ss x /\ lookup_var x u = SOME w ==> lookup_var x t = SOME w) /\
  t.vs_labels = u.vs_labels /\ u.vs_alloca_next <= t.vs_alloca_next /\
  (!tv w. ~is_word_type ty /\ expr_val_at cenv cx ty si ss pos v (vv_operand sv) u /\
    evaluate_type (get_tenv cx) ty = SOME tv /\ eval_operand (vv_operand sv) u = SOME w ==>
    val_wf tv v /\
    mem_bytes_at (w2n w) (val_footprint tv v) t.vs_memory =
      mem_bytes_at (w2n w) (val_footprint tv v) u.vs_memory /\
    (!i. w2n w <= i /\ i < w2n w + val_footprint tv v /\ i IN tn2.t_mem ==> i IN tn1.t_mem)) ==>
  (?raw. read_result cx raw ee = (INL v,ee) /\
    vv_holds_mods cenv cx ty raw sv ee t /\ vv_at cenv cx ty si ss ee raw sv t /\
    ptr_vv_ok cx ty raw sv ee G2 tn2 t /\ vv_store_bound cx ty ty ee raw sv t) /\
  (!tag op. sv = StackValue tag op /\ ~is_word_type ty ==> ptr_buf_ok cenv e op G2 t) /\
  (!tag p. sv = LocatedValue tag p /\ p.ptr_location = LocMemory ==>
     ptr_buf_ok cenv e p.ptr_operand G2 t)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `ty = lowered_value_type _ _` kall_tac >>
  qpat_x_assum `?raw. read_result _ raw _ = _ /\ _` strip_assume_tac >>
  drule_all_then strip_assume_tac ext_saved_value_extract >>
  `?w. eval_operand (vv_operand sv) u = SOME w` by fs[expr_val_rel_def] >>
  `eval_operand (vv_operand sv) t = eval_operand (vv_operand sv) u` by
    (qmatch_asmsub_abbrev_tac `eval_operand op u` >>
     Cases_on `op` >> gvs[eval_operand_def] >> metis_tac[]) >>
  `(!x. vv_operand sv = Var x ==> FLOOKUP G2 x = FLOOKUP G1 x) /\
   op_taint tn2 (vv_operand sv) = op_taint tn1 (vv_operand sv)` by
    (qmatch_goalsub_abbrev_tac `op_taint tn2 op` >> Cases_on `op` >>
     gvs[ghost_kept_at_def, op_taint_def] >> metis_tac[]) >>
  `expr_val_at cenv cx ty si ss ee v (vv_operand sv) t` by
    (qpat_assum `eval_operand _ t = eval_operand _ u` (assume_tac o SYM) >>
     drule_all abi_args_location_kept_eq >> simp[]) >>
  `ptr_val_ok cx ty v (vv_operand sv) G2 tn2 t` by
    (irule ptr_val_ok_footprint_frame >> qexistsl [`G1`, `u`, `tn1`] >> simp[]) >>
  `expr_val_rel cx ty v (vv_operand sv) t` by
    (Cases_on `is_word_type ty` >- gvs[expr_val_rel_def] >>
     Cases_on `evaluate_type (get_tenv cx) ty` >- simp[expr_val_rel_def] >>
     irule expr_val_rel_footprint_agree >> simp[] >> qexists `u` >> simp[]) >>
  conj_tac
  >- (drule_all_then strip_assume_tac ext_saved_value_pack >>
      drule_all_then assume_tac ext_saved_value_store_bound >>
      qexists `Value v` >> simp[read_result_def, return_def]) >>
  `ptr_buf_ok cenv e (vv_operand sv) G1 u ==> ptr_buf_ok cenv e (vv_operand sv) G2 t` by
    (strip_tac >> irule ptr_buf_ok_frame >> qexistsl [`G1`, `u`] >> simp[]) >>
  conj_tac >> rpt strip_tac >> gvs[vv_operand_def]
QED
