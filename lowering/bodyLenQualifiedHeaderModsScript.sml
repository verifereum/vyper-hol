(* Identify the source length and the concrete header at a linked VV landing. *)
Theory bodyLenQualifiedHeaderMods
Ancestors
  bodyFullPostsMods exprSimLen bodyInvSplit loweringPosts loweringStateRelDefs
  bodyPtrDefs builtinProps context vyperTypeSystem vyperTyping vyperValue
  vyperInterpreter vyperState valueEncodingProps valueEncodingDefs compileEnv
  venomState words finite_map alist

Theorem len_sized_layout[local]:
  is_sized_type pt /\ evaluate_type tenv pt = SOME pvt ==>
  ~is_word_type pt /\ 32 <= type_memory_size pvt
Proof
  strip_tac >> drule sized_type_cases >> strip_tac >>
  gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs(),
      valueEncodingTheory.type_memory_size_def, is_word_type_def]
QED

Theorem len_sized_memory_header_widens[local]:
  type_widens_to tenv pt ty /\ is_sized_type ty /\
  evaluate_type tenv pt = SOME pvt /\ evaluate_type tenv ty = SOME tvt /\
  value_has_type tvt v /\ val_in_memory pvt v a mem ==>
  ?n. result_array_length cx (Value v) ee = (INL n,ee) /\
      mem_word_at a mem = n2w n
Proof
  strip_tac >> gvs[type_widens_to_def]
  >- (drule_all sized_memory_header >> simp[]) >>
  drule sized_type_cases >> strip_tac >> Cases_on `pt` >>
  gvs[arg_type_fits_def, vyperValueTheory.evaluate_type_def, AllCaseEqs()]
  >~ [`arg_type_fits (ArrayT _ bd) _`]
  >- (Cases_on `bd` >> gvs[arg_type_fits_def] >> Cases_on `v` >>
      gvs[value_has_type_def, val_in_memory_def, result_array_length_def,
          read_result_def, bind_def, return_def] >>
      rename1 `ArrayV av` >> Cases_on `av` >>
      gvs[value_has_type_def, val_in_memory_def, result_array_length_def,
          read_result_def, bind_def, return_def]) >>
  Cases_on `v` >>
  gvs[value_has_type_def, val_in_memory_def, result_array_length_def,
      read_result_def, bind_def, return_def]
QED

Theorem len_selected_data[local]:
  immutable_frame_mods func cenv cx ee t /\ ~cenv.ce_is_ctor /\
  immutable_holds_mods cenv cx pt tv w ee t /\
  evaluate_type (get_tenv cx) pt = SOME pvt ==>
  ?v. read_result cx tv ee = (INL v,ee) /\
      w2n w + type_memory_size pvt <= LENGTH t.vs_data_section /\
      val_in_memory pvt v (w2n w) t.vs_data_section
Proof
  strip_tac >>
  qpat_x_assum `immutable_holds_mods _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [immutable_holds_mods_def,immutable_holds_def]) >>
  Cases_on `ALOOKUP ee.immutables cx.txn.target` >>
  gvs[compile_env_accfupds,sub_layout_def] >>
  `immutables_rel cenv cx.txn.target src F ee t` by
    fs[immutable_frame_mods_def,immutables_rel_mods_def] >>
  qpat_x_assum `immutables_rel _ _ _ _ _ _` mp_tac >>
  simp[immutables_rel_def] >> disch_then (drule_all_then strip_assume_tac) >>
  conj_tac >- decide_tac >>
  once_rewrite_tac[arithmeticTheory.ADD_COMM] >> first_x_assum irule >> simp[]
QED

Theorem len_memory_read_robust[local]:
  (case vv_location vv of NONE => LocMemory | SOME l => l) = LocMemory /\
  ptr_vv_ok cx pt tv vv ee G tn t /\ ~is_word_type pt /\
  evaluate_type (get_tenv cx) pt = SOME pvt /\ eval_operand (vv_operand vv) t = SOME w ==>
  ?v. read_result cx tv ee = (INL v,ee) /\
      !m. mem_agree_outside tn.t_mem t.vs_memory m ==> val_in_memory pvt v (w2n w) m
Proof
  Cases_on `vv` >>
  simp[vv_location_def,vv_operand_def,ptr_vv_ok_def,ptr_val_ok_def,ptr_mem_ok_def] >>
  metis_tac[]
QED

Theorem len_read_header[local]:
  type_widens_to (get_tenv cx) pt ty /\ is_sized_type ty /\
  evaluate_type (get_tenv cx) pt = SOME pvt /\ evaluate_type (get_tenv cx) ty = SOME tvt /\
  env.type_defs = get_tenv cx /\ eval_result_typed (env,cx,ee) tv (Type ty) /\
  (!v. read_result cx tv ee = (INL v,ee) ==> value_has_type tvt v) /\
  read_result cx tv ee = (INL v,ee) /\ val_in_memory pvt v a mem ==>
  ?n. result_array_length cx tv ee = (INL n,ee) /\ mem_word_at a mem = n2w n
Proof
  strip_tac >> `evaluate_type env.type_defs ty = SOME tvt` by simp[] >>
  `value_has_type tvt v` by simp[] >>
  drule_all sized_read_result_length >> strip_tac >>
  drule_all len_sized_memory_header_widens >>
  disch_then (qspecl_then [`ee`,`cx`] mp_tac) >> simp[]
QED

Theorem len_qualified_header_mods:
  vv_post_mods H ctx func cenv cx e es sa sm s0 ee tv vv t /\
  is_sized_type (expr_type e) /\
  type_widens_to (get_tenv cx) (post_value_type cenv e) (expr_type e) /\
  evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME pvt /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tvt /\
  env.type_defs = get_tenv cx /\ eval_result_typed (env,cx,ee) tv (Type (expr_type e)) /\
  (!v. read_result cx tv ee = (INL v,ee) ==> value_has_type tvt v) /\
  ptr_vv_ok cx (post_value_type cenv e) tv vv ee G tn t /\
  (cenv.ce_is_ctor /\ vv_location vv = SOME LocCode ==>
    ?v. read_result cx tv ee = (INL v,ee) /\
        !rt w. evaluate_type (get_tenv cx) (post_value_type cenv e) = SOME rt /\
          eval_operand (vv_operand vv) t = SOME w ==>
          w2n w + type_memory_size rt <= lo /\
          !m. mem_agree_outside tn.t_mem t.vs_memory m ==> val_in_memory rt v (w2n w) m) ==>
  let L = case vv_location vv of NONE => LocMemory | SOME l => l in
  ?n w. result_array_length cx tv ee = (INL n,ee) /\
        eval_operand (vv_operand vv) t = SOME w /\ L <> LocCalldata /\
        ptr_load_val cenv.ce_is_ctor L w t = n2w n /\
        (L = LocCode /\ ~cenv.ce_is_ctor ==> w2n w <= LENGTH t.vs_data_section) /\
        (L = LocCode /\ cenv.ce_is_ctor ==> w2n w + 32 <= lo) /\
        (L = LocMemory \/ (L = LocCode /\ cenv.ce_is_ctor) ==>
          !m. mem_agree_outside tn.t_mem t.vs_memory m ==> mem_word_at (w2n w) m = n2w n)
Proof
  simp[LET_THM] >> strip_tac >>
  `stmt_state_rel H ctx func cenv cx ee t /\
   immutable_frame_mods func cenv cx ee t /\
   vv_holds_mods cenv cx (post_value_type cenv e) tv vv ee t` by
    fs[vv_post_mods_def] >>
  qpat_x_assum `vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _` kall_tac >>
  `is_sized_type (post_value_type cenv e)` by (drule_all sized_type_widens_source >> simp[]) >>
  drule_all len_sized_layout >> strip_tac >>
  qabbrev_tac `L = case vv_location vv of NONE => LocMemory | SOME l => l` >>
  Cases_on `L = LocCode` >- suspend "code" >>
  `vv_holds cenv cx (post_value_type cenv e) tv vv ee t` by
    (Cases_on `vv` >> gvs[Abbr `L`,vv_location_def,vv_holds_mods_def]) >>
  drule_all vv_holds_sized_length_success_widens >> strip_tac >>
  `type_widens_to env.type_defs (post_value_type cenv e) (expr_type e)` by simp[] >>
  drule_all vv_holds_len_header_widens >> strip_tac >>
  `L <> LocCalldata` by
    (Cases_on `vv` >> gvs[Abbr `L`,vv_location_def,vv_holds_def] >>
     Cases_on `p.ptr_location` >> gvs[]) >>
  qexistsl_tac [`n`,`w`] >> gvs[Abbr `L`] >> rpt strip_tac >>
  drule_all len_memory_read_robust >> strip_tac >>
  `val_in_memory pvt v (w2n w) m` by simp[] >>
  drule_all len_read_header >> simp[]
QED

Resume len_qualified_header_mods[code]:
  `vv_location vv = SOME LocCode` by
    (Cases_on `vv_location vv` >> gvs[Abbr `L`]) >>
  `?w. eval_operand (vv_operand vv) t = SOME w /\
       immutable_holds_mods cenv cx (post_value_type cenv e) tv w ee t` by
    (Cases_on `vv` >> gvs[vv_holds_mods_def,vv_location_def,vv_operand_def]) >>
  Cases_on `cenv.ce_is_ctor`
  >- (qpat_x_assum `_ /\ vv_location vv = SOME LocCode ==> _` mp_tac >>
      simp[] >> strip_tac >>
      `w2n w + type_memory_size pvt <= lo /\
       !m. mem_agree_outside tn.t_mem t.vs_memory m ==> val_in_memory pvt v (w2n w) m` by
        (first_x_assum drule_all >> simp[]) >>
      `val_in_memory pvt v (w2n w) t.vs_memory` by simp[mem_agree_outside_def] >>
      drule_all len_read_header >> strip_tac >>
      qexists_tac `n` >> simp[ptr_load_val_def,GSYM mem_word_at_eq_mload] >>
      rpt strip_tac >>
      `val_in_memory pvt v (w2n w) m` by simp[] >> drule_all len_read_header >> simp[]) >>
  drule_all len_selected_data >> strip_tac >>
  drule_all len_read_header >> strip_tac >>
  qexistsl_tac [`n`,`w`] >> simp[ptr_load_val_def,GSYM mem_word_at_def] >> decide_tac
QED

Finalise len_qualified_header_mods
