(* Counted tuple selection: source selection and allocation-frontier bounds. *)
Theory bodyMemSubscriptTuple
Ancestors
  exprSimTuple bodyFieldMemoryProps bodyMemoryPreds stmtSimForced
  exprSimMemDefs exprSimHyps exprSimHypsDefs exprSimSource exprSimUnwrap
  exprSimDefs loweringPosts gasOutcome gasSummary gasContext fragGasMode
  exprLowering exprLoweringProps compileEnv context vyperAST vyperInterpreter
  vyperState vyperTypeExprSoundness fragExec exprSimProps valueTypingMemoryProps
  valueEncoding valueEncodingDefs valueEncodingProofs exprSimAttributeProps exprSimAttributeFields exprSimAttribute
  vyperTyping words list rich_list

Theorem tuple_select_mem_source[local]:
  expr_body_pre cenv cx env
    (Subscript (EL k tys) obj (Literal ity (IntL (&k)))) es /\
  expr_body_pre cenv cx env obj es /\ expr_type obj = TupleT tys /\
  post_value_type cenv obj = TupleT tys /\ k < LENGTH tys /\
  vv_post ctx func cenv cx obj es sa sm s0 ee tv bvv t /\
  eval_operand (vv_operand bvv) t = SOME w /\
  eval_expr cx obj (es with gas_obs := gs) = (INL tv, ee) ==>
  ?tvs vs tv'.
    evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
    OPT_MMAP (evaluate_type (get_tenv cx)) tys = SOME tvs /\
    LENGTH tvs = LENGTH tys /\
    read_result cx tv ee = (INL (ArrayV (TupleV vs)), ee) /\
    values_have_types tvs vs /\ read_result cx tv' ee = (INL (EL k vs), ee) /\
    !tail. select_result cx (TupleT tys) tv (ValueSubscript (IntV (&k)))
      (ee with gas_obs := tail) = (INL tv', ee with gas_obs := tail)
Proof
  strip_tac >> drule_at (Pos last) tuple_base_facts >>
  disch_then (qspecl_then [`cenv`, `env`, `ity`, `k`, `tys`] mp_tac) >>
  simp[] >> strip_tac >>
  drule_all tuple_base_read >> strip_tac >>
  Cases_on `select_result cx (TupleT tys) tv (ValueSubscript (IntV (&k))) ee` >>
  rename1 `_ = (sr, ee2)` >>
  `!m. sr <> INR (Error (TypeError m))` by metis_tac[] >>
  `k < LENGTH vs` by simp[] >>
  drule_all select_tuple_read >> strip_tac >> gvs[] >>
  drule tuple_select_gas_obs >> strip_tac >> metis_tac[]
QED

Theorem tuple_element_bound_mem[local]:
  !tvs k (w:bytes32) next.
    k < LENGTH tvs /\
    (type_memory_size_list tvs = 0 \/ w2n w + type_memory_size_list tvs <= next) /\
    next < dimword (:256) ==>
    type_memory_size (EL k tvs) = 0 \/
    w2n (w + n2w (SUM (TAKE k (MAP type_memory_size tvs)))) +
      type_memory_size (EL k tvs) <= next
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`MAP type_memory_size tvs`, `k`] mp_tac sum_take_el_le >>
  simp[EL_MAP, GSYM type_memory_size_list_sum] >> strip_tac >>
  Cases_on `type_memory_size (EL k tvs) = 0` >> simp[] >>
  `w2n (w + n2w (SUM (TAKE k (MAP type_memory_size tvs)))) =
   w2n w + SUM (TAKE k (MAP type_memory_size tvs))` by
    (irule field_ptr_w2n >>
     qexistsl_tac [`type_memory_size (EL k tvs)`, `type_memory_size_list tvs`] >>
     simp[] >> decide_tac) >> simp[] >> decide_tac
QED

Theorem tuple_selected_store_bound_mem[local]:
  vv_post ctx func cenv cx (Subscript (EL k tys) obj idx) es sa sb s0 ee tv'
    (LocatedValue (EL k tys) (mk_ptr dst (vv_loc bvv))) u /\
  vv_store_bound cx (TupleT tys) lt ee tv bvv t /\
  expr_sim_inv cenv cx env es /\
  evaluate_type (get_tenv cx) (TupleT tys) = SOME (TupleTV tvs) /\
  OPT_MMAP (evaluate_type (get_tenv cx)) tys = SOME tvs /\ k < LENGTH tvs /\
  read_result cx tv ee = (INL (ArrayV (TupleV vs)), ee) /\
  eval_operand (vv_operand bvv) t = SOME w /\
  eval_operand dst u = SOME (w + n2w (tuple_offset cenv tys (vv_loc bvv) k)) /\
  u.vs_alloca_next = t.vs_alloca_next ==>
  vv_store_bound cx (EL k tys) (EL k tys) ee tv'
    (LocatedValue (EL k tys) (mk_ptr dst (vv_loc bvv))) u
Proof
  strip_tac >> Cases_on `vv_loc bvv = LocMemory`
  >- (`type_memory_size_list tvs = 0 \/
       w2n w + type_memory_size_list tvs <= t.vs_alloca_next` by
        (qpat_x_assum `vv_store_bound _ _ _ _ _ _ _`
          (mp_tac o CONJUNCT1 o REWRITE_RULE [vv_store_bound_def]) >>
         Cases_on `bvv` >>
         gvs[vv_loc_def, vv_location_def, vv_operand_def, is_word_type_def,
             val_store_size_def, type_memory_size_def] >> metis_tac[]) >>
      `evaluate_type (get_tenv cx) (EL k tys) = SOME (EL k tvs)` by
        (drule opt_mmap_el >> disch_then (qspec_then `k` mp_tac) >>
         impl_tac >- (drule vyperTypeABITheory.OPT_MMAP_LENGTH >> simp[]) >>
         simp[]) >>
      `u.vs_alloca_next < dimword (:256)` by
        metis_tac[vv_post_def, stmt_state_rel_def, alloca_room_next_lt] >>
      drule_all tuple_offset_memory >> disch_then (qspec_then `k` assume_tac) >>
      `type_memory_size (EL k tvs) = 0 \/
       w2n (w + n2w (SUM (TAKE k (MAP type_memory_size tvs)))) +
         type_memory_size (EL k tvs) <= u.vs_alloca_next` by
        (irule tuple_element_bound_mem >> simp[] >> metis_tac[]) >>
      drule vv_store_bound_capacity >>
      simp[expr_type_def, post_value_type_def, mk_ptr_def] >>
      disch_then irule >> simp[] >> metis_tac[]) >>
  irule vv_store_bound_nonmem >> simp[mk_ptr_def]
QED

Theorem tuple_step_mem[local]:
  expr_body_pre cenv cx env
    (Subscript (EL k tys) obj (Literal ity (IntL (&k)))) es /\
  expr_body_pre cenv cx env obj es /\ expr_type obj = TupleT tys /\
  post_value_type cenv obj = TupleT tys /\ k < LENGTH tys /\
  compile_expr cenv ty obj sa = (bvv, sm) /\ local_ptrs_reserved cenv sa /\
  sa.cs_next_var <= sm.cs_next_var /\
  emit_op ADD [vv_operand bvv; Lit (n2w (tuple_offset cenv tys (vv_loc bvv) k))]
    sm = (dst, sb) /\ fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  vv_post ctx func cenv cx obj es sa sm s0 ee tv bvv t /\
  vv_store_bound cx (TupleT tys) (lowered_value_type cenv obj) ee tv bvv t /\
  t.vs_current_bb = sm.cs_current_bb /\
  t.vs_inst_idx = LENGTH sm.cs_current_insts /\ alloca_history func t /\
  s0.vs_alloca_next <= t.vs_alloca_next /\ ~t.vs_halted /\
  eval_expr cx obj (es with gas_obs := gs) = (INL tv, ee) ==>
  ?tv' u.
    (!tail. select_result cx (TupleT tys) tv (ValueSubscript (IntV (&k)))
      (ee with gas_obs := tail) = (INL tv', ee with gas_obs := tail)) /\
    gas_path_mem ctx func t 0 (OK u) /\
    vv_post ctx func cenv cx (Subscript (EL k tys) obj (Literal ity (IntL (&k))))
      es sa sb s0 ee tv' (LocatedValue (EL k tys) (mk_ptr dst (vv_loc bvv))) u /\
    vv_store_bound cx (EL k tys) (EL k tys) ee tv'
      (LocatedValue (EL k tys) (mk_ptr dst (vv_loc bvv))) u /\
    u.vs_current_bb = sb.cs_current_bb /\
    u.vs_inst_idx = LENGTH sb.cs_current_insts /\
    alloca_history func u /\ s0.vs_alloca_next <= u.vs_alloca_next
Proof
  strip_tac >>
  `?w. eval_operand (vv_operand bvv) t = SOME w` by
    (gvs[vv_post_def] >> Cases_on `bvv` >>
     gvs[vv_holds_def, vv_operand_def, expr_val_rel_def]) >>
  drule_all tuple_select_mem_source >> strip_tac >>
  drule_all attr_add_counted_post >> strip_tac >>
  rename1 `gas_path_mem ctx func t 0 (OK u)` >>
  `expr_sim_inv cenv cx env es` by fs[expr_body_pre_def] >>
  `vv_post ctx func cenv cx
    (Subscript (EL k tys) obj (Literal ity (IntL (&k)))) es sa sb s0 ee tv'
    (LocatedValue (EL k tys) (mk_ptr dst (vv_loc bvv))) u` by
    (qpat_assum `!tail. select_result _ _ _ _ _ = _`
      (qspec_then `[]` (assume_tac o MATCH_MP select_result_memory_place)) >>
     irule tuple_vv_post >> simp[] >>
     conj_tac >- metis_tac[] >> qexistsl_tac [`tv`, `vs`] >> simp[]) >>
  qexistsl_tac [`tv'`, `u`] >> simp[] >>
  irule tuple_selected_store_bound_mem >> simp[] >>
  goal_assum (drule_at Any) >> goal_assum (drule_at Any) >> simp[] >>
  metis_tac[]
QED

Theorem compile_subscript_tuple_vv_sim_mem:
  !ctx func cenv cx env ty obj ity k es tys.
    expr_body_pre cenv cx env
      (Subscript (EL k tys) obj (Literal ity (IntL (&k)))) es /\
    expr_body_pre cenv cx env obj es /\ expr_type obj = TupleT tys /\
    post_value_type cenv obj = expr_type obj /\
    place_type cenv obj = ValPT (TupleT tys) /\ k < LENGTH tys /\
    expr_vv_sim_mem ctx func cenv cx ty obj es ==>
    expr_vv_sim_mem ctx func cenv cx ty
      (Subscript (EL k tys) obj (Literal ity (IntL (&k)))) es
Proof
  rpt gen_tac >> strip_tac >>
  simp[expr_vv_sim_mem_def] >> rpt gen_tac >> strip_tac >>
  drule_all compile_expr_tuple_subscript >> strip_tac >>
  gvs[literal_int_index_def] >>
  rename1 `compile_expr cenv ty obj sa = (bvv, sm)` >>
  drule attr_extends >> strip_tac >>
  drule compile_expr_extends >> strip_tac >>
  drule_all fn_has_code_split >> strip_tac >>
  `gas_admissible (eval_expr cx obj) expr_vv_res_ok es` by
    metis_tac[expr_body_pre_vv_gas_admissible] >>
  qpat_x_assum `expr_vv_sim_mem _ _ _ _ _ obj _`
    (mp_tac o REWRITE_RULE [expr_vv_sim_mem_def]) >>
  disch_then (qspecl_then [`sa`, `sm`, `bvv`, `s0`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  simp[tuple_source] >> irule forced_vv_then_outcome >> simp[] >>
  qexists_tac `\tv ee t.
    vv_post ctx func cenv cx obj es sa sm s0 ee tv bvv t /\
    vv_store_bound cx (TupleT tys) (lowered_value_type cenv obj) ee tv bvv t /\
    t.vs_current_bb = sm.cs_current_bb /\
    t.vs_inst_idx = LENGTH sm.cs_current_insts /\
    alloca_history func t /\ s0.vs_alloca_next <= t.vs_alloca_next` >>
  reverse conj_tac >- gvs[] >>
  rpt gen_tac >> BETA_TAC >> strip_tac >>
  `ee with gas_obs := [] = ee` by
    simp[vyperStateTheory.evaluation_state_component_equality] >>
  drule_all tuple_step_mem >> strip_tac >>
  qexistsl_tac [`INL tv'`, `ee`, `OK u`] >>
  fs[gas_marked_path_def, expr_type_def, lowered_value_type_def]
QED

Theorem body_subscript_tuple_vv_mem:
  body_expr_mem_ok cx obj /\ body_inv tops ctx cenv cx /\
  expr_body_pre cenv cx env (Subscript ann obj idx) es /\
  expr_type obj = TupleT tys /\ place_type cenv obj = ValPT (TupleT tys) /\
  post_value_type cenv obj = expr_type obj ==>
  expr_vv_sim_mem ctx func cenv cx ty (Subscript ann obj idx) es
Proof
  strip_tac >> drule_all tuple_pre_base >> strip_tac >> gvs[] >>
  irule compile_subscript_tuple_vv_sim_mem >> simp[] >>
  conj_tac >- (qexists_tac `env` >> simp[]) >>
  gvs[body_expr_mem_ok_def] >> metis_tac[]
QED
