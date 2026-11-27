Theory bodyFullForStorageCapture
Ancestors
  exprBodyPreCallSafetyProps exprBodyPreTypingProps
  exprSimSource exprSimPopStorage stmtSimAugAssignPlaceStorage
  vyperFiniteStoragePreservation vyperStoragePlaceRegion vyperStorageBackend
  vyperStorageFootprint vyperInterpreter vyperState vyperValue vyperAST vyperTypeValues
  exprSimHypsDefs vyperTypeExprSoundness vyperTypeInvariants
  vyperStoragePlaceObserved loweringPosts bodyPtrDefs bodyPtrBopInLiveStorage
  accountsRelProps venomExecSemantics context compileEnv venomState
  fragGasOriginPtr fragGasSeqPtr bodyPtrMakeArrayEmission exprPtrUnwrapCopyEdges
  bodyPtrBopInLoadOutput stmtAppendStorageRunPtr ptrDiscipline fragExec
  emitHelper venomInst venomExecProps unitTransformDefs memSafeRun
  contextCodegenRel codegenRel finite_map words integer list

(* A successful expression can capture a subarray, so the observed root
   need not be the array itself. The iterator saves addresses, not values. *)
Theorem for_storage_iterator_capture_mods:
  expr_body_pre_mods mods c cx env e es /\
  eval_expr cx e es = (INL (PlaceR (StoragePlace tr slot (ArrayTV et bd))),ee) /\
  valid_horizon cx st0 H ee.storage_trace /\
  storage_well_formed_on cx es (FST H) /\
  storage_well_formed_on cx ee (FST H) /\
  len = (case bd of Fixed n => n | Dynamic n =>
           w2n (lookup_storage slot (get_storage cx ee tr))) ==>
  compatible_bound bd len /\ len <= bound_length bd /\
  eval_iterator cx (Array e) es =
    (INL (GENLIST (\i. PlaceR (StoragePlace tr
        ((case bd of Fixed _ => slot | Dynamic _ => slot + 1w) +
         n2w (i * type_slot_size et)) et)) len),ee) /\
  ?off root path delta.
    MEM (StorageRoot tr off root) ee.storage_trace /\
    storage_subregion root path delta (ArrayTV et bd) /\
    slot = n2w off + n2w delta
Proof
  strip_tac >>
  `valid_horizon cx es H ee.storage_trace` by fs[valid_horizon_def] >>
  drule_then strip_assume_tac expr_body_pre_mods_runtime_typing >>
  drule_then assume_tac expr_body_pre_mods_call_evaluation_safe >>
  drule_all eval_expr_observed_region >> strip_tac >>
  `storage_place_observed H (StoragePlace tr slot (ArrayTV et bd))` by
    metis_tac[aug_place_storage_rooted_observed] >>
  `compatible_bound bd len /\ len <= bound_length bd` by
    (Cases_on `bd` >> simp[compatible_bound_def, bound_length_def] >>
     `slots_in_range (get_storage cx ee tr) (w2n slot)
        (ArrayTV et (Dynamic n))` by
       (irule aug_place_observed_slots_in_range >>
        simp[type_slot_size_def] >> qexists_tac `H` >> gvs[valid_horizon_def]) >>
     drule pop_array_length_bound >> simp[]) >>
  simp[Once evaluate_def, bind_def, array_iterator_results_storage] >>
  Cases_on `bd` >>
  gvs[result_array_length_def, get_storage_backend_eq, bind_def,
      ignore_bind_def, check_def, assert_def, return_def, compatible_bound_def] >>
  qexistsl [`offset`, `tv`, `path`, `delta`] >> simp[]
QED

Theorem for_storage_iterator_capture:
  expr_body_pre_mods mods c cx env e es /\
  eval_expr cx e es = (INL (PlaceR (StoragePlace tr slot (ArrayTV et bd))),ee) /\
  valid_horizon cx st0 H ee.storage_trace /\
  storage_well_formed_on cx es (FST H) /\
  storage_well_formed_on cx ee (FST H) /\
  len = (case bd of Fixed n => n | Dynamic n =>
           w2n (lookup_storage slot (get_storage cx ee tr))) ==>
  compatible_bound bd len /\ len <= bound_length bd /\
  eval_iterator cx (Array e) es =
    (INL (GENLIST (\i. PlaceR (StoragePlace tr
        ((case bd of Fixed _ => slot | Dynamic _ => slot + 1w) +
         n2w (i * type_slot_size et)) et)) len),ee) /\
  ?off root path delta.
    MEM (StorageRoot tr off root) ee.storage_trace /\
    storage_subregion root path delta (ArrayTV et bd) /\
    slot = n2w off + n2w delta
Proof
  simp[expr_body_pre_split_def] >> metis_tac[for_storage_iterator_capture_mods]
QED

Theorem for_storage_iterator_child_observed:
  storage_place_observed H (StoragePlace tr slot (ArrayTV et bd)) /\
  i < bound_length bd ==>
  storage_place_observed H (StoragePlace tr
    ((case bd of Fixed _ => slot | Dynamic _ => slot + 1w) +
     n2w (i * type_slot_size et)) et)
Proof
  simp[storage_place_observed_def] >> strip_tac >>
  qabbrev_tac `d = case bd of Fixed _ => 0 | Dynamic _ => 1` >>
  `storage_subregion (ArrayTV et bd) [ValueSubscript (IntV (&i))]
      (d + i * type_slot_size et) et` by
    (Cases_on `bd` >>
     fs[storage_subregion_def, bound_length_def, Abbr `d`]) >>
  `storage_subregion tv (path ++ [ValueSubscript (IntV (&i))])
      (delta + (d + i * type_slot_size et)) et` by
    (irule storage_subregion_append >> qexists_tac `ArrayTV et bd` >> simp[]) >>
  qexistsl [`root`, `tv`, `path ++ [ValueSubscript (IntV (&i))]`,
            `delta + (d + i * type_slot_size et)`] >>
  Cases_on `bd` >> simp[Abbr `d`, word_add_n2w, GSYM WORD_ADD_ASSOC]
QED

Theorem storage_expr_post_value_type[local]:
  eval_expr cx e es = (INL (PlaceR (StoragePlace tr slot tv)),ee) ==>
  post_value_type c e = expr_type e
Proof
  strip_tac >> irule post_value_type_not_int_call >>
  rpt gen_tac >> strip_tac >> gvs[] >> PairCases_on `fid` >>
  gvs[Once evaluate_def, bind_def, ignore_bind_def, return_def,
      vyperMiscTheory.option_CASE_rator, pairTheory.FORALL_PROD, AllCaseEqs()]
QED

(* This is the successful slot branch of the full expression post. Its
   operand may have been computed by a subscript or a field selection. *)
Theorem for_storage_iterator_operand:
  expr_body_pre_mods mods c cx env e es /\
  eval_expr cx e es = (INL (PlaceR (StoragePlace tr slot (ArrayTV et bd))),ee) /\
  vv_post H ctx func c cx e es sa sb s0 ee
    (PlaceR (StoragePlace tr slot (ArrayTV et bd))) vv s /\
  ptr_vv_ok cx (post_value_type c e)
    (PlaceR (StoragePlace tr slot (ArrayTV et bd))) vv ee G tn s ==>
  post_value_type c e = expr_type e /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME (ArrayTV et bd) /\
  well_formed_type_value (ArrayTV et bd) /\
  ?p. vv = LocatedValue (expr_type e) p /\ p.ptr_location = slot_loc tr /\
    eval_operand p.ptr_operand s = SOME slot /\ op_taint tn p.ptr_operand = {} /\
    storage_holds cx tr (expr_type e)
      (PlaceR (StoragePlace tr slot (ArrayTV et bd))) slot ee s /\
    (case bd of Fixed _ => T | Dynamic _ =>
       key_taint (if tr then tn.t_trans else tn.t_stor) slot = {} /\
       (if tr then tload slot s else sload slot s) =
         lookup_storage slot (get_storage cx ee tr))
Proof
  strip_tac >>
  drule_then assume_tac storage_expr_post_value_type >>
  drule_all expr_body_pre_eval_result >> strip_tac >>
  `env.type_defs = get_tenv cx` by
    gvs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def] >>
  `evaluate_type (get_tenv cx) (expr_type e) = SOME (ArrayTV et bd) /\
   well_formed_type_value (ArrayTV et bd)` by
    gvs[eval_result_typed_def, runtime_place_typed_def, place_type_value_def,
        return_def] >>
  `~is_word_type (expr_type e)` by
    (`?ty b. expr_type e = ArrayT ty b` by
       (spose_not_then strip_assume_tac >>
        metis_tac[evaluate_type_not_ArrayT_imp_not_ArrayTV]) >>
     simp[is_word_type_def]) >>
  Cases_on `vv` >> gvs[vv_post_def, vv_at_def, vv_place_ptr_def] >>
  rename1 `ptr_vv_ok _ _ _ (LocatedValue ann p) _ _ _ _` >>
  `ann = expr_type e /\ storage_holds cx tr (expr_type e)
       (PlaceR (StoragePlace tr slot (ArrayTV et bd))) slot ee s` by
    (Cases_on `tr` >> gvs[vv_holds_def, slot_loc_def]) >>
  `op_taint tn p.ptr_operand = {}` by fs[ptr_vv_ok_def] >>
  simp[] >> Cases_on `bd` >> simp[] >> conj_tac
  >- (irule located_dynamic_header_clean >>
      qpat_assum `ptr_vv_ok _ _ _ _ _ _ _ _` (irule_at Any) >>
      simp[GSYM slot_loc_def]) >>
  qpat_x_assum `storage_holds _ _ _ _ _ _ _` mp_tac >>
  simp[storage_holds_def, type_slot_size_def] >> strip_tac >>
  drule storage_range_agree_head >>
  simp[type_slot_size_def] >> Cases_on `tr` >> simp[sload_def, tload_def]
QED

(* The dynamic array's header load can follow any expression operand. The
   instruction has no storage effect and preserves all earlier variables. *)
Theorem for_storage_iterator_dynamic_length_run_uniform:
  compile_ptr_load ctor imm (slot_loc tr) bop sa = (len_op,sb) /\
  fn_has_code sa sb func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  eval_operand bop s = SOME slot /\ op_taint tn bop = {} /\
  key_taint (if tr then tn.t_trans else tn.t_stor) slot = {} /\
  (if tr then tload slot s else sload slot s) = n2w len ==>
  ?out t G1 tn1.
    len_op = Var out /\
    t = (update_var out (n2w len) s with vs_inst_idx := SUC s.vs_inst_idx) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G1,tn1)) /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    ~t.vs_halted /\ eval_operand len_op t = SOME (n2w len) /\
    op_taint tn1 len_op = {} /\ op_prov G1 len_op = NONE /\
    tn1.t_mem = tn.t_mem /\ tn1.t_stor = tn.t_stor /\
    tn1.t_trans = tn.t_trans /\ tn1.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==> x <> out) /\
    (!x. x <> out ==> lookup_var x t = lookup_var x s /\
      FLOOKUP G1 x = FLOOKUP G x /\ op_taint tn1 (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  `emit_op (if tr then TLOAD else SLOAD) [bop] sa = (len_op,sb)` by
    (Cases_on `tr` >> gvs[slot_loc_def, compile_ptr_load_def]) >>
  drule_all emit_op_fetch_boundary >> strip_tac >>
  qpat_x_assum `tmp = STRING _ _` kall_tac >>
  qabbrev_tac `i = mk_inst sa.cs_next_id (if tr then TLOAD else SLOAD) [bop] [tmp]` >>
  qabbrev_tac `u = update_var tmp (n2w len) s` >>
  qabbrev_tac `t = u with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `G1 = step_prov PG G i u` >>
  qabbrev_tac `tn1 = step_taint i s u tn` >>
  `get_instruction bb s.vs_inst_idx = SOME i` by simp[Abbr `i`] >>
  `step_inst_base i s = OK u` by
    (Cases_on `tr` >>
     gvs[Abbr `i`, Abbr `u`, step_inst_base_opcode_eqs, exec_read1_def]) >>
  `!D. ptr_inst_ok D lo 0 ctx func G tn i s` by
    (gen_tac >> simp[Abbr `i`] >> irule ptr_inst_ok_slot_load >> Cases_on `tr` >> fs[]) >>
  `inst_mem_below_frontier i s /\ inst_dload_in_section i s /\
   i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode /\ i.inst_opcode <> GAS` by
    (Cases_on `tr` >>
     simp[Abbr `i`, mk_inst_def, is_terminator_def, inst_mem_below_frontier_def,
          inst_dload_in_section_def, source_memory_read_ranges_def,
          source_memory_write_ranges_def]) >>
  `ctx_has_dalloca ctx ==> dalloca_no_wrap i s` by
    (Cases_on `tr` >> simp[Abbr `i`, mk_inst_def, dalloca_no_wrap_non_dalloca]) >>
  `!D. gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G1,tn1)` by
    (gen_tac >>
     qpat_assum `!D. ptr_inst_ok D _ _ _ _ _ _ _ _` (qspec_then `D` assume_tac) >>
     drule_all straight_line_origin_ptr_edge >>
     simp[Abbr `t`, Abbr `G1`, Abbr `tn1`]) >>
  `~t.vs_halted` by simp[Abbr `t`, Abbr `u`, update_var_def] >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G1,tn1)` by
    (gen_tac >>
     qpat_assum `!D. gas_origin_ptr_edge _ _ _ _` (qspec_then `D` assume_tac) >>
     drule (cj 2 gas_origin_ptr_path_rules) >>
     disch_then (qspecl_then [`[]`, `OK t`, `G1`, `tn1`] mp_tac) >>
     simp[cj 1 gas_origin_ptr_path_rules]) >>
  `tn1 = tn with t_var := tn.t_var |+ (tmp,{})` by
    (simp[Abbr `tn1`, Abbr `i`] >> irule scalar_storage_load_taint >>
     simp[Abbr `u`, update_var_def]) >>
  `FLOOKUP G1 tmp = NONE` by
    (simp[Abbr `G1`, Abbr `i`] >> irule scalar_load_output_prov >>
     Cases_on `tr` >> simp[]) >>
  qexistsl [`tmp`, `t`, `G1`, `tn1`] >>
  simp[Abbr `t`, Abbr `u`, update_var_def, eval_operand_def, lookup_var_def,
       op_taint_def, op_prov_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> simp[Abbr `G1`, Abbr `i`, scalar_step_old_prov] >>
  metis_tac[]
QED
