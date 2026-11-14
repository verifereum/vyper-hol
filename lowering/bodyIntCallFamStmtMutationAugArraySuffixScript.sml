(* Current-state array suffix dispatch, independent of source evaluation. *)
Theory bodyIntCallFamStmtMutationAugArraySuffix
Ancestors
  bodyIntCallFamStmtMutationAugArraySummary bodyIntCallJointAggCore
  bodyIntCallJointContract
  targetSubscriptContinuation targetPlaceSimDefs exprSimDefs
  exprSimHypsDefs loweringPosts exprLowering vyperTypeSystem
  vyperInterpreter vyperState compileEnv gasSummary vyperValue
  exprSimProps valueEncodingProps exprSimHyps exprSimFieldLayout

Theorem intcall_target_array_suffix_summary:
  intcall_frame_ok fp /\ intcall_expr_res fp ce env es0 sa s0 /\
  intcall_expr_cont fp ce env es0 sa s0 es sn u /\ es.gas_obs = [] /\
  target_post fp.jc_ctx fp.jc_func ce fp.jc_cx es0 sa sn s0 es pv
    (Type (ArrayT ety bd)) rb u /\
  subscript_vtype (Type (ArrayT ety bd)) (expr_type e) = SOME vt /\
  evaluate_type (get_tenv fp.jc_cx) (expr_type e) = SOME itv /\
  value_has_type itv (IntV i) /\ eval_operand ix u = SOME (i2w i) /\
  target_subscript_suffix ce e rb ix sn = (op,sb) /\
  fn_has_code sn sb fp.jc_func /\
  sa.cs_next_var <= sn.cs_next_var /\ sa.cs_next_id <= sn.cs_next_id /\
  MAP FDOM es0.scopes = MAP FDOM es.scopes /\
  (!x. ix = Var x ==> not_fresh_at sn x) /\
  (!l. ix <> Label l) /\ (!l. FST rb <> Label l) /\
  (!x. FST op = Var x ==> not_fresh_at sb x) /\
  (!id path. pv = PlaceR (MemoryPlace id path) ==>
    ?entry av. lookup_scopes id es.scopes = SOME entry /\
      evaluate_subscripts entry.type entry.value path = INL (ArrayV av)) /\
  (!tr slot tv. pv = PlaceR (StoragePlace tr slot tv) ==>
    storage_read_live fp.jc_cx tr (get_storage fp.jc_cx es tr) slot tv /\
    w2n slot + type_slot_size tv <= dimword(:256) /\
    (!etv cnt. tv = ArrayTV etv (Dynamic cnt) ==>
      w2n (lookup_storage slot (get_storage fp.jc_cx es tr)) <= cnt)) ==>
  gas_summary_at F (fp.jc_ctx,fp.jc_func) []
    (extend_place fp.jc_cx pv (ValueSubscript (IntV i))) (es,u)
    (\res ee v. ?pv'. res = INL pv' /\
      target_post fp.jc_ctx fp.jc_func ce fp.jc_cx es0 sa sb s0 ee pv' vt op v /\
      intcall_expr_cont fp ce env es0 sa s0 ee sb v)
    (\res ee r. expr_exit res r)
Proof
  strip_tac >>
  `intcall_expr_res fp ce env es sn u /\ ~u.vs_halted /\
   u.vs_current_bb = sn.cs_current_bb /\
   u.vs_inst_idx = LENGTH sn.cs_current_insts` by fs[intcall_expr_cont_def] >>
  `gas_summary_at F (fp.jc_ctx,fp.jc_func) []
    (extend_place fp.jc_cx pv (ValueSubscript (IntV i))) (es,u)
    (\res ee v. ?pv'. res = INL pv' /\
      target_post fp.jc_ctx fp.jc_func ce fp.jc_cx es0 sa sb s0 ee pv' vt op v /\
      intcall_expr_cont fp ce env es sn u ee sb v)
    (\res ee r. expr_exit res r)` by suspend "dispatch" >>
  pop_assum (strip_assume_tac o REWRITE_RULE [gas_summary_at_def]) >>
  rewrite_tac[gas_summary_at_def] >>
  qexistsl_tac [`res`, `es_end`, `r`] >> simp[] >>
  gvs[] >>
  irule bodyIntCallJointAggCoreTheory.intcall_expr_cont_trans >>
  simp[] >> qexistsl_tac [`es`, `sn`, `u`] >> simp[]
QED

Resume intcall_target_array_suffix_summary[dispatch]:
  `SND (SND rb) = SOME (ValPT (ArrayT ety bd)) /\
   ?w. place_ptr_rel ce fp.jc_cx u pv w (FST (SND rb)) (Type (ArrayT ety bd))` by
    (fs[target_post_def, value_type_place_def] >> metis_tac[]) >>
  Cases_on `pv` >> gvs[place_ptr_rel_def] >>
  Cases_on `p` >> gvs[place_ptr_rel_def]
  >~ [`StoragePlace tr slot tv`]
  >- (`?dyn cnt. bd = if dyn then Dynamic cnt else Fixed cnt` by
        (Cases_on `bd` >> metis_tac[]) >> gvs[] >>
      `?etv. evaluate_type (get_tenv fp.jc_cx) ety = SOME etv /\
         tv = ArrayTV etv (if dyn then Dynamic cnt else Fixed cnt)` by
        (Cases_on `dyn` >> gvs[evaluate_type_def, AllCaseEqs()]) >> gvs[] >>
      `type_memory_bytes ce ety = type_memory_size etv` by
        (irule expr_sim_inv_memory_size >>
         fs[intcall_expr_res_def] >> metis_tac[]) >>
      PairCases_on `rb` >>
      gvs[target_subscript_suffix_array] >>
      `word_scale (slot_loc tr) = 1 /\
       elem_size_in_location ce (slot_loc tr) ety = type_slot_size etv` by
        (Cases_on `tr` >>
         simp[slot_loc_def, word_scale_def, elem_size_in_location_def,
              is_slot_addressed_def, slot_count_of_memory_size]) >>
      `vt = Type ety` by (Cases_on `dyn` >> gvs[subscript_vtype_def]) >> gvs[] >>
      irule intcall_target_storage_array_extend_summary >>
      simp[] >>
      qexistsl_tac [`ix`, `itv`, `expr_type e`,
        `(rb0,SOME (slot_loc tr),SOME (ValPT (ArrayT ety (if dyn then Dynamic cnt else Fixed cnt))))`] >>
      simp[] >> Cases_on `dyn` >>
      gvs[slot_loc_def, compile_array_subscript_def]) >>
  `?dyn cnt. bd = if dyn then Dynamic cnt else Fixed cnt` by
    (Cases_on `bd` >> metis_tac[]) >> gvs[] >>
  `?etv. evaluate_type (get_tenv fp.jc_cx) ety = SOME etv /\
     tv = ArrayTV etv (if dyn then Dynamic cnt else Fixed cnt)` by
    (Cases_on `dyn` >> gvs[evaluate_type_def, AllCaseEqs()]) >> gvs[] >>
  `vt = Type ety` by (Cases_on `dyn` >> gvs[subscript_vtype_def]) >> gvs[] >>
  PairCases_on `rb` >>
  gvs[target_subscript_suffix_array, word_scale_def, elem_size_in_location_def,
      is_slot_addressed_def] >>
  irule intcall_target_memory_array_extend_summary >> simp[] >>
  qexistsl_tac [`cnt`, `dyn`, `etv`, `ix`, `itv`, `expr_type e`,
    `(rb0,SOME LocMemory,SOME (ValPT (ArrayT ety (if dyn then Dynamic cnt else Fixed cnt))))`] >>
  simp[] >> Cases_on `dyn` >> gvs[compile_array_subscript_def]
QED

Finalise intcall_target_array_suffix_summary
