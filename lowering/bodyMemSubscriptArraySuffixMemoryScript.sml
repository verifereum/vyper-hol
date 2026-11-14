(* Counted represented-array selection with allocation-frontier capacity. *)
Theory bodyMemSubscriptArraySuffixMemory
Ancestors
  bodyMemSubscriptArrayPaths bodyMemSubscriptArrayBounds bodyImmutableUnwrapMemory
  exprSimSubscriptArraySuffix exprSimSubscriptArrayCompose exprSimSubscriptArrayFramed
  exprSimMemDefs exprSimHyps exprSimHypsDefs exprSimProps exprSimAttributeProps
  exprLoweringProps loweringPosts compileEnv context gasSummary gasOutcome
  fragGasMode fragExec venomState vyperArray option vyperState vyperAST vyperValue vyperTyping vyperValueOperation
  valueEncoding valueEncodingDefs valueTypingMemoryProps words integer integer_word
  arithmetic finite_map list

Theorem array_selection_summary_mem[local]:
  (!tr slot vt. r <> PlaceR (StoragePlace tr slot vt)) /\
  select_result cx ty r sub ee = (res,ee) /\
  gas_marked_path T ctx func s 0 outcome /\
  ((?q. outcome = OK q /\ Q res (ee with gas_obs := []) q) \/
   (exit_result outcome /\ expr_exit res outcome)) ==>
  gas_summary_at T (ctx,func) [] (select_result cx ty r sub) (ee,s)
    Q (\res ee out. expr_exit res out)
Proof
  strip_tac >> simp[gas_summary_at_def] >>
  qexistsl_tac [`res`,`ee`,`outcome`] >> simp[] >>
  simp[gas_marked_exec_def] >>
  drule select_result_nonstorage_gas_obs >> gvs[]
QED

Theorem framed_array_element_summary_mem[local]:
  expr_body_pre cenv cx env obj es /\
  eval_expr cx obj es = (INL r,t) /\
  expr_type obj = ArrayT et bd /\ post_value_type cenv obj = expr_type obj /\
  evaluate_type (get_tenv cx) (ArrayT et bd) = SOME (ArrayTV etv bd) /\
  evaluate_type (get_tenv cx) et = SOME etv /\
  ee.scopes = t.scopes /\ ee.immutables = t.immutables /\ ee.gas_obs = [] /\
  (!tr slot vt. r <> PlaceR (StoragePlace tr slot vt)) /\
  (vv_location (FST (compile_expr cenv ty obj sa)) = SOME LocCode \/ (?n. bd = Fixed n)) /\
  read_result cx r ee = (INL (ArrayV av),ee) /\
  array_index (ArrayTV etv bd) av i = SOME v /\
  val_wf (ArrayTV etv bd) (ArrayV av) /\ val_wf etv v /\ value_has_type etv v /\
  vv_post ctx func cenv cx (Subscript (ArrayT et bd) obj idx) es sa sd s0 ee r
    (LocatedValue (ArrayT et bd) p) q /\
  (p.ptr_location = LocMemory \/ p.ptr_location = LocCode) /\
  (p.ptr_location = LocMemory ==> ?n. bd = Fixed n /\ Num i < n) /\
  eval_operand p.ptr_operand q = SOME w /\
  j = (case bd of Fixed _ => 0 | Dynamic _ => 32) + Num i * type_memory_size etv /\
  eval_operand dst q = SOME (w + n2w j) /\
  (p.ptr_location = LocMemory ==> w2n (w + n2w j) = w2n w + j) /\
  gas_marked_path T ctx func s 0 (OK q) /\
  q.vs_current_bb = sd.cs_current_bb /\ q.vs_inst_idx = LENGTH sd.cs_current_insts /\
  alloca_history func q /\ s.vs_alloca_next <= q.vs_alloca_next /\
  vv_store_bound cx (ArrayT et bd) lt eb r (LocatedValue (ArrayT et bd) p) tb /\
  read_result cx r eb = (INL (ArrayV av),eb) /\
  eval_operand p.ptr_operand tb = SOME w /\ tb.vs_alloca_next <= q.vs_alloca_next ==>
  gas_summary_at T (ctx,func) []
    (select_result cx (ArrayT et bd) r (ValueSubscript (IntV i))) (ee,s)
    (\res ee' q. ?child. res = INL child /\
      vv_post ctx func cenv cx (Subscript et obj idx) es sa sd s0 ee' child
        (LocatedValue et (mk_ptr dst p.ptr_location)) q /\
      vv_store_bound cx et et ee' child (LocatedValue et (mk_ptr dst p.ptr_location)) q /\
      q.vs_current_bb = sd.cs_current_bb /\ q.vs_inst_idx = LENGTH sd.cs_current_insts /\
      alloca_history func q /\ s.vs_alloca_next <= q.vs_alloca_next)
    (\res ee' out. expr_exit res out)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all framed_array_select_read >> strip_tac >>
  qpat_assum `select_result _ _ _ _ _ = (INL _,_)`
    (assume_tac o MATCH_MP select_result_memory_place) >>
  `p.ptr_location = LocMemory ==> ?n. bd = Fixed n` by metis_tac[] >>
  drule_all vv_post_array_element >> strip_tac >>
  `q.vs_alloca_next < dimword (:256)` by
    metis_tac[vv_post_def, stmt_state_rel_def, alloca_room_next_lt] >>
  `vv_store_bound cx et et ee child (LocatedValue et (mk_ptr dst p.ptr_location)) q` by
    (drule_at (Pos (el 2)) array_selected_store_bound_mem >>
     simp[exprSimAttributePropsTheory.vv_loc_def, contextTheory.vv_location_def,
          contextTheory.vv_operand_def] >>
     disch_then irule >> goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  irule array_selection_summary_mem >> simp[] >>
  qexists_tac `OK q` >> simp[] >>
  `ee with gas_obs := [] = ee` by
    (Cases_on `ee` >> gvs[evaluation_state_component_equality]) >>
  simp[] >> metis_tac[]
QED

Theorem framed_array_represented_suffix_summary_mem:
  ((?ty. vv_location (FST (compile_expr cenv ty obj sa)) = SOME LocCode) \/
   (?n. bd = Fixed n)) /\
  expr_body_pre cenv cx env (Subscript ann obj idx) es /\
  expr_body_pre cenv cx env obj es /\ expr_type obj = ArrayT et bd /\
  post_value_type cenv obj = expr_type obj /\
  eval_expr cx obj es = (INL r,t) /\
  ee.scopes = t.scopes /\ ee.immutables = t.immutables /\ ee.gas_obs = [] /\
  (!tr slot vt. r <> PlaceR (StoragePlace tr slot vt)) /\
  ((~cenv.ce_is_ctor /\ p.ptr_location = LocCode) \/
   ((?n. bd = Fixed n) /\
    (!tv. evaluate_type (get_tenv cx) et = SOME tv ==> dynarray_free tv) /\
    p.ptr_location = LocMemory)) /\
  local_ptrs_reserved cenv sc /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sc x) /\
  (!l. p.ptr_operand <> Label l) /\
  (!x. iop = Var x ==> not_fresh_at sc x) /\ (!l. iop <> Label l) /\
  compile_array_subscript p.ptr_operand iop
    (case bd of Fixed _ => F | Dynamic _ => T)
    (case bd of Fixed n => n | Dynamic _ => 0)
    (word_scale p.ptr_location) (elem_size_in_location cenv p.ptr_location et)
    (is_signed_type (expr_type idx))
    (compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca p.ptr_location) sc = (dst,sd) /\
  fn_has_code sc sd func /\ ~s.vs_halted /\
  s.vs_current_bb = sc.cs_current_bb /\ s.vs_inst_idx = LENGTH sc.cs_current_insts /\
  stmt_state_rel ctx func cenv cx ee s /\
  vv_post ctx func cenv cx (Subscript (ArrayT et bd) obj idx) es sa sc s0 ee r
    (LocatedValue (ArrayT et bd) p) s /\
  evaluate_type (get_tenv cx) et = SOME etv /\
  evaluate_type (get_tenv cx) (ArrayT et bd) = SOME (ArrayTV etv bd) /\
  read_result cx r ee = (INL (ArrayV av),ee) /\
  val_wf (ArrayTV etv bd) (ArrayV av) /\
  value_has_type (ArrayTV etv bd) (ArrayV av) /\
  eval_operand p.ptr_operand s = SOME w /\ eval_operand iop s = SOME iw /\
  i = (if is_signed_type (expr_type idx) then w2i iw else &(w2n iw)) /\
  array_length (ArrayTV etv bd) av < dimword (:256) /\
  (!al. av = SArrayV al ==> ?n. bd = Fixed n) /\
  (!q. (!x z. not_fresh_at sc x /\ lookup_var x s = SOME z ==> lookup_var x q = SOME z) /\
       (!aid a. FLOOKUP s.vs_allocas aid = SOME a ==> FLOOKUP q.vs_allocas aid = SOME a) /\
       q.vs_memory = s.vs_memory /\ stmt_state_rel ctx func cenv cx ee q ==>
       vv_post ctx func cenv cx (Subscript (ArrayT et bd) obj idx) es sa sd s0 ee r
         (LocatedValue (ArrayT et bd) p) q) /\
  fn_inst_ids_distinct func /\ alloca_history func s /\
  vv_store_bound cx (ArrayT et bd) lt eb r (LocatedValue (ArrayT et bd) p) tb /\
  read_result cx r eb = (INL (ArrayV av),eb) /\
  eval_operand p.ptr_operand tb = SOME w /\ tb.vs_alloca_next <= s.vs_alloca_next ==>
  gas_summary_at T (ctx,func) []
    (select_result cx (ArrayT et bd) r (ValueSubscript (IntV i))) (ee,s)
    (\res ee' q. ?child. res = INL child /\
      vv_post ctx func cenv cx (Subscript ann obj idx) es sa sd s0 ee' child
        (LocatedValue ann (mk_ptr dst p.ptr_location)) q /\
      vv_store_bound cx ann ann ee' child (LocatedValue ann (mk_ptr dst p.ptr_location)) q /\
      q.vs_current_bb = sd.cs_current_bb /\ q.vs_inst_idx = LENGTH sd.cs_current_insts /\
      alloca_history func q /\ s.vs_alloca_next <= q.vs_alloca_next)
    (\res ee' out. expr_exit res out)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `p.ptr_location = LocCode ==> w2n w <= LENGTH s.vs_data_section` by
    (strip_tac >> `~cenv.ce_is_ctor` by gvs[] >>
     `immutable_holds cenv cx (ArrayT et bd) r w ee s` by
       gvs[vv_post_def, vv_holds_def, expr_type_def] >>
     `immutable_holds cenv cx (ArrayT et bd) (Value (ArrayV av)) w ee s` by
       (gvs[immutable_holds_def, read_result_def, return_def] >> metis_tac[]) >>
     drule_all runtime_immutable_data_section >> simp[]) >>
  drule_all_then assume_tac array_index_word_bounds >>
  Cases_on `valid_index (ArrayTV etv bd) av i`
  >- suspend "valid" >>
  drule_all_then assume_tac framed_array_select_error >>
  Cases_on `bd`
  >- suspend "fixed_oob" >>
  suspend "dynamic_oob"
QED

Resume framed_array_represented_suffix_summary_mem[fixed_oob]:
  `array_length (ArrayTV etv (Fixed n)) av = n` by
    (Cases_on `av` >> gvs[value_has_type_def, array_length_def]) >>
  fs[Excl "valid_index_def"] >>
  drule_all fixed_array_subscript_counted_mem_oob >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  irule array_selection_summary_mem >> simp[] >>
  goal_assum (drule_at Any) >>
  qexists_tac `INR (Error (RuntimeError "evaluate_subscripts array_index"))` >>
  metis_tac[exprSimDefsTheory.expr_exit_def, exit_result_def]
QED

Resume framed_array_represented_suffix_summary_mem[dynamic_oob]:
  fs[Excl "valid_index_def"] >>
  `immutable_holds cenv cx (ArrayT et (Dynamic n)) r w ee s` by
    gvs[vv_post_def, vv_holds_def, expr_type_def] >>
  drule_all_then assume_tac framed_array_code_length_view >>
  `compile_ptr_load F cenv.ce_imm_alloca LocCode = compile_imm_load_word F cenv.ce_imm_alloca` by
    simp[FUN_EQ_THM, compile_ptr_load_def] >>
  gvs[Excl "valid_index_def"] >>
  `~idx_in_range (is_signed_type (expr_type idx)) iw
     (word_of_bytes T (0w:bytes32)
       (TAKE 32 (DROP (w2n w) s.vs_data_section ++ REPLICATE 32 0w)))` by simp[] >>
  drule_all runtime_array_subscript_counted_mem_oob >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  irule array_selection_summary_mem >> simp[] >>
  goal_assum (drule_at Any) >> simp[exprSimDefsTheory.expr_exit_def, exit_result_def]
QED

Resume framed_array_represented_suffix_summary_mem[valid]:
  `ann = et` by
    (qpat_x_assum `expr_body_pre _ _ _ (Subscript _ _ _) _` mp_tac >>
     simp[exprSimHypsDefsTheory.expr_body_pre_def,
          Once vyperTypeSystemTheory.well_typed_expr_def] >>
     strip_tac >> gvs[vyperTypeSystemTheory.subscript_type_ok_def] >>
     drule vyperTypeSystemTheory.type_place_expr_vtype_annotation >>
     strip_tac >> Cases_on `vt` >>
     gvs[vyperTypeSystemTheory.vtype_annotation_ok_def] >>
     gvs[vyperTypeSystemTheory.subscript_vtype_def, AllCaseEqs()]) >>
  drule array_index_valid >> pure_rewrite_tac[IS_SOME_EXISTS] >> strip_tac >>
  rename1 `array_index (ArrayTV etv bd) av i = SOME v` >>
  `well_formed_type_value etv` by metis_tac[evaluate_type_well_formed] >>
  `value_has_type etv v` by metis_tac[vyperAssignPreservesTypeTheory.array_index_has_type] >>
  `val_wf etv v` by metis_tac[value_has_type_memory_wf] >>
  `type_memory_bytes cenv et = type_memory_size etv` by
    (irule expr_sim_inv_memory_size >> goal_assum (drule_at Any) >>
     qexistsl_tac [`env`,`es`] >> fs[expr_body_pre_def]) >>
  `iw = n2w (Num i)` by
    (qpat_x_assum `valid_index _ _ _` mp_tac >> qpat_x_assum `i = _` mp_tac >>
     rpt (pop_assum kall_tac) >> Cases_on `is_signed_type (expr_type idx)` >>
     simp[w2i_def] >> Cases_on `word_msb iw` >> simp[] >> rw[] >> gvs[]) >>
  qpat_x_assum `i = _` kall_tac >>
  Cases_on `bd`
  >- suspend "fixed_valid" >>
  suspend "dynamic_valid"
QED

Resume framed_array_represented_suffix_summary_mem[fixed_valid]:
  `array_length (ArrayTV etv (Fixed n)) av = n` by
    (Cases_on `av` >> gvs[value_has_type_def, array_length_def]) >>
  fs[Excl "valid_index_def"] >>
  `Num i < n` by (gvs[valid_index_def] >> intLib.COOPER_TAC) >>
  drule_all fixed_array_subscript_counted_mem_ok >> strip_tac >>
  `vv_post ctx func cenv cx (Subscript (ArrayT et (Fixed n)) obj idx) es sa sd s0 ee r
     (LocatedValue (ArrayT et (Fixed n)) p) t'` by
    (first_x_assum irule >> simp[]) >>
  `eval_operand p.ptr_operand t' = SOME w` by
    (Cases_on `p.ptr_operand` >> gvs[eval_operand_def] >>
     first_x_assum irule >> metis_tac[]) >>
  `eval_operand dst t' = SOME (w + n2w (Num i * type_memory_size etv))` by
    gvs[elem_size_in_location_def, is_slot_addressed_def, GSYM word_mul_n2w] >>
  `p.ptr_location = LocMemory ==> w2n (w + n2w (Num i * type_memory_size etv)) =
      w2n w + Num i * type_memory_size etv` by
    (strip_tac >> irule fixed_array_element_nonwrapping >>
     goal_assum (drule_at Any) >> simp[] >>
     irule (SIMP_RULE (srw_ss()) [] vv_post_memory_footprint_bound) >>
     goal_assum (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
     simp[expr_type_def]) >>
  qpat_assum `p.ptr_location = _` (fn th => pure_rewrite_tac[GSYM th]) >>
  irule framed_array_element_summary_mem >> simp[] >>
  (conj_tac >- (qexists_tac `env` >> simp[])) >>
  qexistsl_tac [`eb`,`lt`,`t'`,`tb`,`w`] >> simp[] >>
  metis_tac[]
QED

Resume framed_array_represented_suffix_summary_mem[dynamic_valid]:
  fs[Excl "valid_index_def"] >>
  `immutable_holds cenv cx (ArrayT et (Dynamic n)) r w ee s` by
    gvs[vv_post_def, vv_holds_def, expr_type_def] >>
  drule_all_then assume_tac framed_array_code_length_view >>
  `compile_ptr_load F cenv.ce_imm_alloca LocCode = compile_imm_load_word F cenv.ce_imm_alloca` by
    simp[FUN_EQ_THM, compile_ptr_load_def] >>
  gvs[Excl "valid_index_def"] >>
  `idx_in_range (is_signed_type (expr_type idx)) (n2w (Num i))
     (word_of_bytes T (0w:bytes32)
       (TAKE 32 (DROP (w2n w) s.vs_data_section ++ REPLICATE 32 0w)))` by simp[] >>
  drule_all runtime_array_subscript_counted_mem_ok >> strip_tac >>
  `vv_post ctx func cenv cx (Subscript (ArrayT ann (Dynamic n)) obj idx) es sa sd s0 ee r
     (LocatedValue (ArrayT ann (Dynamic n)) p) t'` by
    (first_x_assum irule >> simp[]) >>
  `eval_operand p.ptr_operand t' = SOME w` by
    (Cases_on `p.ptr_operand` >> gvs[eval_operand_def] >>
     first_x_assum irule >> metis_tac[]) >>
  `eval_operand dst t' = SOME (w + n2w (32 + Num i * type_memory_size etv))` by
    (gvs[elem_size_in_location_def, is_slot_addressed_def,
         word_scale_def, word_mul_n2w, word_add_n2w, WORD_ADD_ASSOC] >>
     simp[GSYM word_add_n2w, WORD_ADD_ASSOC] >>
     simp[AC WORD_ADD_ASSOC WORD_ADD_COMM]) >>
  qpat_assum `p.ptr_location = _` (fn th => pure_rewrite_tac[GSYM th]) >>
  irule framed_array_element_summary_mem >> simp[] >>
  (conj_tac >- (qexists_tac `ty` >> simp[])) >>
  (conj_tac >- (qexists_tac `env` >> simp[])) >>
  qexistsl_tac [`eb`,`lt`,`t'`,`tb`,`w`] >> simp[ADD_COMM]
QED

Finalise framed_array_represented_suffix_summary_mem
