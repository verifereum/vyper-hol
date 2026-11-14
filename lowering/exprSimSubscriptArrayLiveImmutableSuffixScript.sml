(* Immutable array selection on current contents, independent of the base evaluation. *)
Theory exprSimSubscriptArrayLiveImmutableSuffix
Ancestors
  exprSimSubscriptArraySuffix exprSimSubscriptArraySource exprSimSubscriptArrayFramed
  exprSimProps exprSimCopy exprSimHypsDefs loweringPosts context vyperState
  vyperPlaceStatePreservation vyperPlaceResultTyping vyperPlaceTyping vyperValueOperation vyperValue
  valueEncodingDefs finite_map words exprSimSubscriptArrayLiveImmutableView loweringStateRelDefs
  exprSimArrayIndex compileEnv emitHelperProps exprSimUnwrap fragGasMode fragGasSeq
  freshWrites fragGasFresh fragExec venomState exprLoweringProps rich_list
  exprSimUnopProps fragGasPath exprSimAbiEncodeArgsCountedLabels

Theorem live_immutable_select:
  FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of
       NONE => FEMPTY | SOME imms => get_source_immutables src imms) id =
    SOME (itv,iv) /\
  mem_path_offset itv path = SOME (k,ptv) /\
  evaluate_subscripts itv iv path = INL a /\
  evaluate_subscripts ptv a [sb] = INL v ==>
  select_result cx ty (PlaceR (ImmutablePlace src id path)) sb ee =
    (INL (PlaceR (ImmutablePlace src id (path ++ [sb]))),ee) /\
  read_result cx (PlaceR (ImmutablePlace src id (path ++ [sb]))) ee = (INL v,ee)
Proof
  rpt gen_tac >> strip_tac >>
  `subscripts_type itv path = SOME ptv` by metis_tac[mem_path_offset_sound] >>
  `evaluate_subscripts itv iv (path ++ [sb]) = INL v` by
    (drule_all evaluate_subscripts_append >> simp[]) >>
  `get_immutables cx src ee =
    (INL (get_source_immutables src (THE (ALOOKUP ee.immutables cx.txn.target))),ee)` by
    (Cases_on `ALOOKUP ee.immutables cx.txn.target` >>
     gvs[get_immutables_def, get_address_immutables_def, bind_def,
         lift_option_type_def, return_def]) >>
  conj_tac
  >- (Cases_on `ALOOKUP ee.immutables cx.txn.target` >> gvs[] >>
      drule_all select_immutable_result >>
      simp[bind_def, lift_sum_def, return_def]) >>
  Cases_on `ALOOKUP ee.immutables cx.txn.target` >> gvs[] >>
  simp[read_result_def, read_place_def, get_immutables_def,
       get_address_immutables_def, bind_def, lift_option_type_def,
       lift_sum_def, return_def]
QED

Theorem live_immutable_element_place_ptr:
  FLOOKUP cenv.ce_module_vars (cenv.ce_module,id) = SOME (ImmutableLoc off) /\
  src = cenv.ce_module /\
  FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
    | SOME imms => get_source_immutables src imms) id = SOME (itv,iv) /\
  mem_path_offset itv path = SOME (k,ArrayTV etv bd) /\
  array_index (ArrayTV etv bd) av i = SOME v /\
  val_wf (ArrayTV etv bd) (ArrayV av) /\
  p.ptr_location = LocCode /\ w = n2w (off+k) /\
  j = (case bd of Fixed _ => 0 | Dynamic _ => 32) + Num i * type_memory_size etv /\
  eval_operand dst q = SOME (w+n2w j) ==>
  vv_place_ptr cenv cx ee q
    (PlaceR (ImmutablePlace src id (path ++ [ValueSubscript (IntV i)])))
    (LocatedValue et (mk_ptr dst p.ptr_location))
Proof
  strip_tac >> drule_all array_element_step_offset >> strip_tac >>
  drule_all mem_path_offset_snoc >> strip_tac >>
  gvs[vv_place_ptr_def, mk_ptr_def] >>
  pure_rewrite_tac[GSYM wordsTheory.word_add_n2w, arithmeticTheory.ADD_ASSOC,
                   wordsTheory.WORD_ADD_ASSOC] >> REFL_TAC
QED

Theorem live_immutable_element_summary_family:
  FLOOKUP cenv.ce_module_vars (cenv.ce_module,id) = SOME (ImmutableLoc off) /\
  src = cenv.ce_module /\
  FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
    | SOME imms => get_source_immutables src imms) id = SOME (itv,iv) /\
  mem_path_offset itv path = SOME (k,ArrayTV etv bd) /\
  evaluate_subscripts itv iv path = INL (ArrayV av) /\
  expr_type obj = ArrayT et bd /\ ee.gas_obs = [] /\
  evaluate_type (get_tenv cx) (ArrayT et bd) = SOME (ArrayTV etv bd) /\
  evaluate_type (get_tenv cx) et = SOME etv /\
  read_result cx (PlaceR (ImmutablePlace src id path)) ee = (INL (ArrayV av),ee) /\
  array_index (ArrayTV etv bd) av i = SOME v /\
  val_wf (ArrayTV etv bd) (ArrayV av) /\ val_wf etv v /\ value_has_type etv v /\
  (!H. P H ==> vv_post H ctx func cenv cx (Subscript (ArrayT et bd) obj idx) es sa sd s0 ee
    (PlaceR (ImmutablePlace src id path)) (LocatedValue ann p) q) /\
  p.ptr_location = LocCode /\ w = n2w (off+k) /\
  eval_operand p.ptr_operand q = SOME w /\
  j = (case bd of Fixed _ => 0 | Dynamic _ => 32) + Num i * type_memory_size etv /\
  eval_operand dst q = SOME (w+n2w j) /\
  gas_marked_path F ctx func s 0 (OK q) /\
  q.vs_current_bb = sd.cs_current_bb /\ q.vs_inst_idx = LENGTH sd.cs_current_insts ==>
  gas_summary_at F (ctx,func) []
    (select_result cx (ArrayT et bd) (PlaceR (ImmutablePlace src id path))
      (ValueSubscript (IntV i))) (ee,s)
    (\res ee' q. ?child. res = INL child /\ ee' = ee /\
      (!H. P H ==> vv_post H ctx func cenv cx (Subscript et obj idx) es sa sd s0 ee' child
        (LocatedValue et (mk_ptr dst p.ptr_location)) q) /\
      q.vs_current_bb = sd.cs_current_bb /\ q.vs_inst_idx = LENGTH sd.cs_current_insts)
    (\res ee' outcome. expr_exit res outcome)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `evaluate_subscripts (ArrayTV etv bd) (ArrayV av) [ValueSubscript (IntV i)] = INL v` by
    simp[evaluate_subscripts_def] >>
  drule_all live_immutable_select >> strip_tac >>
  drule_all live_immutable_element_place_ptr >> strip_tac >>
  `!H. P H ==> vv_post H ctx func cenv cx (Subscript et obj idx) es sa sd s0 ee
     (PlaceR (ImmutablePlace src id (path ++ [ValueSubscript (IntV i)])))
     (LocatedValue et (mk_ptr dst p.ptr_location)) q` by
    (rpt strip_tac >>
     qpat_assum `!H. P H ==> _` (qspec_then `H` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
     irule vv_post_array_element >> simp[] >>
     qexistsl_tac [`ann`,`av`,`i`,`PlaceR (ImmutablePlace src id path)`] >> simp[]) >>
  irule select_result_counted_summary >> simp[] >>
  qexists_tac `OK q` >> simp[] >>
  `ee with gas_obs := [] = ee` by
    (Cases_on `ee` >> gvs[evaluation_state_component_equality]) >>
  simp[] >> metis_tac[]
QED

Theorem live_immutable_select_error:
  FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
    | SOME imms => get_source_immutables src imms) id = SOME (itv,iv) /\
  mem_path_offset itv path = SOME (k,ArrayTV etv bd) /\
  evaluate_subscripts itv iv path = INL (ArrayV av) /\
  ~valid_index (ArrayTV etv bd) av i /\
  (!al. av = SArrayV al ==> ?n. bd = Fixed n) ==>
  select_result cx ty (PlaceR (ImmutablePlace src id path)) (ValueSubscript (IntV i)) ee =
    (INR (Error (RuntimeError "evaluate_subscripts array_index")),ee)
Proof
  strip_tac >>
  `subscripts_type itv path = SOME (ArrayTV etv bd)` by
    metis_tac[mem_path_offset_sound] >>
  `evaluate_subscripts (ArrayTV etv bd) (ArrayV av) [ValueSubscript (IntV i)] =
     INR (RuntimeError "evaluate_subscripts array_index")` by
    metis_tac[evaluate_array_subscript_oob] >>
  Cases_on `ALOOKUP ee.immutables cx.txn.target` >> gvs[] >>
  `get_immutables cx src ee = (INL (get_source_immutables src x),ee)` by
    simp[get_immutables_def, get_address_immutables_def, bind_def,
         lift_option_type_def, return_def] >>
  drule_all select_immutable_result >>
  simp[bind_def, lift_sum_def, raise_def]
QED

Theorem live_immutable_ctor_length_view:
  cenv.ce_is_ctor /\ src = cenv.ce_module /\
  expr_sim_inv cenv cx env ee /\ stmt_state_rel H ctx func cenv cx ee s /\
  FLOOKUP cenv.ce_module_vars (src,id) = SOME (ImmutableLoc off) /\
  FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
    | SOME imms => get_source_immutables src imms) id = SOME (itv,iv) /\
  mem_path_offset itv path = SOME (k,ArrayTV etv (Dynamic cap)) /\
  evaluate_subscripts itv iv path = INL (ArrayV av) /\
  value_has_type (ArrayTV etv (Dynamic cap)) (ArrayV av) /\
  off + type_memory_size itv < dimword (:256) ==>
  mload (w2n (n2w (off+k):bytes32)) s =
    n2w (array_length (ArrayTV etv (Dynamic cap)) av)
Proof
  strip_tac >>
  `k + type_memory_size (ArrayTV etv (Dynamic cap)) <= type_memory_size itv` by
    metis_tac[mem_path_offset_sound] >>
  `off+k < dimword (:256)` by
    (gvs[valueEncodingTheory.type_memory_size_def] >> decide_tac) >>
  Cases_on `av` >> gvs[vyperTypingTheory.value_has_type_def] >>
  `mem_word_at (off+k) s.vs_memory = n2w (LENGTH l)` by
    (`val_in_memory itv iv off s.vs_memory` by
       (gvs[exprLoweringPropsTheory.stmt_state_rel_def, state_rel_def, immutables_rel_def] >>
        first_x_assum drule_all >> simp[]) >>
     `value_has_type itv iv /\ well_formed_type_value itv` by
       (irule imm_place_at_value_type >> goal_assum (drule_at Any) >>
        qexistsl_tac [`cenv`, `env`, `0`, `[]`] >>
        simp[mem_path_offset_def, evaluate_subscripts_def]) >>
     drule_all targetSubscriptMemoryTheory.mem_path_offset_current_value >>
     simp[valueEncodingPropsTheory.val_in_memory_dynarray]) >>
  gvs[venomStateTheory.mload_def, mem_word_at_def, array_length_def,
      arithmeticTheory.ADD_COMM]
QED

Theorem imm_array_ctor_counted_optional[local]:
  compile_array_subscript base_op iop T cnt ws esz sgn
    (compile_ptr_load T cenv.ce_imm_alloca LocCode) sc = (dst,sd) /\
  fn_has_code sc sd func /\ local_ptrs_reserved cenv sc /\
  stmt_state_rel H ctx func cenv cx ee s /\
  ~s.vs_halted /\ s.vs_current_bb = sc.cs_current_bb /\
  s.vs_inst_idx = LENGTH sc.cs_current_insts /\
  (!x. base_op = Var x ==> not_fresh_at sc x) /\
  (!x. iop = Var x ==> not_fresh_at sc x) /\
  eval_operand base_op s = SOME w /\ eval_operand iop s = SOME iw ==>
  if idx_in_range sgn iw (mload (w2n w) s) then
    ?q. gas_marked_path F ctx func s 0 (OK q) /\
      stmt_state_rel H ctx func cenv cx ee q /\
      eval_operand dst q = SOME ((w+n2w ws)+iw*n2w esz) /\
      (!x z. not_fresh_at sc x /\ lookup_var x s = SOME z ==> lookup_var x q = SOME z) /\
      (!aid a. FLOOKUP s.vs_allocas aid = SOME a ==> FLOOKUP q.vs_allocas aid = SOME a) /\
      q.vs_memory = s.vs_memory /\
      q.vs_accounts = s.vs_accounts /\ q.vs_transient = s.vs_transient /\
      q.vs_requests = s.vs_requests /\ q.vs_call_ctx = s.vs_call_ctx /\ ~q.vs_halted /\
      q.vs_current_bb = sd.cs_current_bb /\ q.vs_inst_idx = LENGTH sd.cs_current_insts
  else ?q. gas_marked_path F ctx func s 0 (Abort Revert_abort q)
Proof
  simp[compile_array_subscript_split, comp_bind_def, compile_ptr_load_def] >>
  pairarg_tac >> simp[] >> strip_tac >>
  rename1 `compile_imm_load_word T cenv.ce_imm_alloca base_op sc = (lop,sm)` >>
  `straight_fresh (comp_ignore_bind (array_bounds_check iop lop sgn)
      (array_elem_ptr base_op iop T ws esz))` by
    simp[straight_fresh_array_check_ptr] >>
  `cs_extends sc sm /\ sc.cs_next_var <= sm.cs_next_var /\
   (!x. lop = Var x ==> not_fresh_at sm x)` by
    (qpat_x_assum `compile_imm_load_word _ _ _ _ = _` mp_tac >>
     Cases_on `cenv.ce_imm_alloca` >>
     simp[compile_imm_load_word_def, emitHelperTheory.emit_op_def,
          comp_bind_def, fresh_var_def, fresh_id_def, comp_ignore_bind_def,
          comp_return_def, emit_def] >> strip_tac >> gvs[] >>
     simp[not_fresh_at_def] >>
     irule cs_extends_same_block >>
     simp[same_blocks_def, GSYM APPEND_ASSOC, rich_listTheory.IS_PREFIX_APPEND]) >>
  `cs_extends sm sd` by metis_tac[straight_fresh_cs_extends] >>
  drule_all fn_has_code_split >> strip_tac >>
  drule_all compile_imm_load_word_ctor_path_fields >> strip_tac >>
  rename1 `gas_path ctx func s 0 (OK u)` >>
  `~u.vs_halted` by metis_tac[gas_path_normal] >>
  `gas_marked_path F ctx func s 0 (OK u)` by
    fs[gas_marked_path_def] >>
  `u.vs_labels = s.vs_labels` by metis_tac[abi_args_marked_path_labels] >>
  `eval_operand base_op u = SOME w /\ eval_operand iop u = SOME iw` by
    (conj_tac >> Cases_on `base_op` >> Cases_on `iop` >>
     gvs[eval_operand_def] >> metis_tac[]) >>
  `(!x. base_op = Var x ==> not_fresh_at sm x) /\
   (!x. iop = Var x ==> not_fresh_at sm x)` by
    metis_tac[not_fresh_at_mono] >>
  `eval_operand base_op (drop_fresh sm u) = SOME w /\
   eval_operand iop (drop_fresh sm u) = SOME iw /\
   eval_operand lop (drop_fresh sm u) = SOME (mload (w2n w) s) /\
   fresh_vars_wrt sm (drop_fresh sm u)` by
    simp[varsExtTheory.fresh_vars_wrt_drop_fresh, eval_operand_drop_fresh] >>
  IF_CASES_TAC
  >- suspend "success" >>
  drule_all array_check_ptr_oob >> strip_tac >>
  drule_all straight_fresh_clean_abort_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule_all gas_marked_path_then >> simp[] >> metis_tac[]
QED

Resume imm_array_ctor_counted_optional[success]:
  drule_all array_check_ptr_run >> strip_tac >>
  drule_all straight_fresh_clean_success_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `local_ptrs_reserved cenv sm` by metis_tac[local_ptrs_reserved_next_var] >>
  drule_all straight_fresh_run_post >> strip_tac >>
  `gas_marked_path F ctx func s 0
     (OK (t' with vs_inst_idx := LENGTH sd.cs_current_insts))` by
    (drule_all gas_marked_path_then >> simp[]) >>
  `writes_fresh sm (emitted_insts sm sd)` by metis_tac[straight_fresh_def] >>
  `t'.vs_accounts = u.vs_accounts /\ t'.vs_transient = u.vs_transient /\
   t'.vs_requests = u.vs_requests /\ t'.vs_call_ctx = u.vs_call_ctx` by
    (qspecl_then [`emitted_insts sm sd`,`sm`,`u`,`t'`] mp_tac run_inst_seq_writes_fresh >>
     (impl_tac >- simp[]) >>
     disch_then (fn th => once_rewrite_tac[CONJUNCT1 th]) >> simp[]) >>
  qexists_tac `t' with vs_inst_idx := LENGTH sd.cs_current_insts` >>
  simp[] >> rpt strip_tac >>
  qpat_x_assum `!z v. not_fresh_at sm z /\ _ ==> _` irule >>
  simp[] >> metis_tac[not_fresh_at_mono]
QED

Finalise imm_array_ctor_counted_optional


Theorem live_immutable_array_counted_fields:
  compile_array_subscript base_op iop
    (case bd of Fixed _ => F | Dynamic _ => T)
    (case bd of Fixed n => n | Dynamic _ => 0) ws esz sgn
    (compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca LocCode) sc = (dst,sd) /\
  fn_has_code sc sd func /\ local_ptrs_reserved cenv sc /\
  expr_sim_inv cenv cx env ee /\ stmt_state_rel H ctx func cenv cx ee s /\
  ~s.vs_halted /\ s.vs_current_bb = sc.cs_current_bb /\
  s.vs_inst_idx = LENGTH sc.cs_current_insts /\
  (!x. base_op = Var x ==> not_fresh_at sc x) /\
  (!x. iop = Var x ==> not_fresh_at sc x) /\
  (!region x. cenv.ce_imm_alloca = SOME region /\ region = Var x ==> not_fresh_at sc x) /\
  eval_operand base_op s = SOME w /\ eval_operand iop s = SOME iw /\
  src = cenv.ce_module /\ w = n2w (off+k) /\
  FLOOKUP cenv.ce_module_vars (src,id) = SOME (ImmutableLoc off) /\
  FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
    | SOME imms => get_source_immutables src imms) id = SOME (itv,iv) /\
  mem_path_offset itv path = SOME (k,ArrayTV etv bd) /\
  evaluate_subscripts itv iv path = INL (ArrayV av) /\
  off + type_memory_size itv < dimword (:256) /\
  immutable_holds cenv cx (ArrayT et bd) (PlaceR (ImmutablePlace src id path)) w ee s /\
  evaluate_type (get_tenv cx) et = SOME etv /\
  read_result cx (PlaceR (ImmutablePlace src id path)) ee = (INL (ArrayV av),ee) /\
  value_has_type (ArrayTV etv bd) (ArrayV av) ==>
  if idx_in_range sgn iw (n2w (array_length (ArrayTV etv bd) av)) then
    ?q. gas_marked_path F ctx func s 0 (OK q) /\
      stmt_state_rel H ctx func cenv cx ee q /\
      eval_operand dst q = SOME ((case bd of Fixed _ => w | Dynamic _ => w+n2w ws) + iw*n2w esz) /\
      (!x z. not_fresh_at sc x /\ lookup_var x s = SOME z ==> lookup_var x q = SOME z) /\
      (!aid a. FLOOKUP s.vs_allocas aid = SOME a ==> FLOOKUP q.vs_allocas aid = SOME a) /\
      q.vs_memory = s.vs_memory /\
      q.vs_accounts = s.vs_accounts /\ q.vs_transient = s.vs_transient /\
      q.vs_requests = s.vs_requests /\ q.vs_call_ctx = s.vs_call_ctx /\ ~q.vs_halted /\
      q.vs_current_bb = sd.cs_current_bb /\ q.vs_inst_idx = LENGTH sd.cs_current_insts
  else ?q. gas_marked_path F ctx func s 0 (Abort Revert_abort q)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> Cases_on `bd`
  >- suspend "fixed" >>
  Cases_on `cenv.ce_is_ctor`
  >- suspend "ctor" >>
  drule_all framed_array_code_length_view >> strip_tac >>
  `compile_ptr_load F cenv.ce_imm_alloca LocCode = compile_imm_load_word F cenv.ce_imm_alloca` by
    simp[FUN_EQ_THM, compile_ptr_load_def] >>
  gvs[] >> IF_CASES_TAC
  >- (drule runtime_array_subscript_counted_fields >> simp[] >>
      disch_then (drule_at (Pat `stmt_state_rel H _ _ _ _ _ _`)) >> simp[] >>
      strip_tac >> qexists_tac `t` >> simp[]) >>
  drule runtime_array_subscript_counted_oob >> simp[] >>
  disch_then (drule_at (Pat `eval_operand base_op _ = _`)) >> simp[] >> metis_tac[]
QED

Resume live_immutable_array_counted_fields[fixed]:
  `array_length (ArrayTV etv (Fixed n)) av = n` by
    (Cases_on `av` >> gvs[vyperTypingTheory.value_has_type_def, array_length_def]) >>
  gvs[] >> IF_CASES_TAC
  >- (drule_all fixed_array_subscript_counted_fields >>
      strip_tac >> qexists_tac `t` >> simp[]) >>
  drule_all fixed_array_subscript_counted_oob >> simp[]
QED

Resume live_immutable_array_counted_fields[ctor]:
  `mload (w2n w) s = n2w (array_length (ArrayTV etv (Dynamic n)) av)` by
    (qpat_assum `w = _` SUBST_ALL_TAC >>
     irule live_immutable_ctor_length_view >> rpt (goal_assum (drule_at Any)) >> simp[]) >>
  `!region. cenv.ce_imm_alloca = SOME region ==> eval_operand region s = SOME 0w` by
    fs[exprLoweringPropsTheory.stmt_state_rel_def, state_rel_def, immutable_base_zero_def] >>
  gvs[] >> drule imm_array_ctor_counted_optional >>
  disch_then (drule_at (Pat `stmt_state_rel H _ _ _ _ _ _`)) >> simp[] >>
  IF_CASES_TAC >> simp[] >> strip_tac >>
  qexists_tac `t` >> simp[]
QED

Finalise live_immutable_array_counted_fields

Theorem live_immutable_array_counted:
  compile_array_subscript base_op iop
    (case bd of Fixed _ => F | Dynamic _ => T)
    (case bd of Fixed n => n | Dynamic _ => 0) ws esz sgn
    (compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca LocCode) sc = (dst,sd) /\
  fn_has_code sc sd func /\ local_ptrs_reserved cenv sc /\
  expr_sim_inv cenv cx env ee /\ stmt_state_rel H ctx func cenv cx ee s /\
  ~s.vs_halted /\ s.vs_current_bb = sc.cs_current_bb /\
  s.vs_inst_idx = LENGTH sc.cs_current_insts /\
  (!x. base_op = Var x ==> not_fresh_at sc x) /\
  (!x. iop = Var x ==> not_fresh_at sc x) /\
  (!region x. cenv.ce_imm_alloca = SOME region /\ region = Var x ==> not_fresh_at sc x) /\
  eval_operand base_op s = SOME w /\ eval_operand iop s = SOME iw /\
  src = cenv.ce_module /\ w = n2w (off+k) /\
  FLOOKUP cenv.ce_module_vars (src,id) = SOME (ImmutableLoc off) /\
  FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
    | SOME imms => get_source_immutables src imms) id = SOME (itv,iv) /\
  mem_path_offset itv path = SOME (k,ArrayTV etv bd) /\
  evaluate_subscripts itv iv path = INL (ArrayV av) /\
  off + type_memory_size itv < dimword (:256) /\
  immutable_holds cenv cx (ArrayT et bd) (PlaceR (ImmutablePlace src id path)) w ee s /\
  evaluate_type (get_tenv cx) et = SOME etv /\
  read_result cx (PlaceR (ImmutablePlace src id path)) ee = (INL (ArrayV av),ee) /\
  value_has_type (ArrayTV etv bd) (ArrayV av) ==>
  if idx_in_range sgn iw (n2w (array_length (ArrayTV etv bd) av)) then
    ?q. gas_marked_path F ctx func s 0 (OK q) /\
      stmt_state_rel H ctx func cenv cx ee q /\
      eval_operand dst q = SOME ((case bd of Fixed _ => w | Dynamic _ => w+n2w ws) + iw*n2w esz) /\
      (!x z. not_fresh_at sc x /\ lookup_var x s = SOME z ==> lookup_var x q = SOME z) /\
      (!aid a. FLOOKUP s.vs_allocas aid = SOME a ==> FLOOKUP q.vs_allocas aid = SOME a) /\
      q.vs_memory = s.vs_memory /\
      q.vs_current_bb = sd.cs_current_bb /\ q.vs_inst_idx = LENGTH sd.cs_current_insts
  else ?q. gas_marked_path F ctx func s 0 (Abort Revert_abort q)
Proof
  strip_tac >> drule_all live_immutable_array_counted_fields >>
  IF_CASES_TAC >> simp[] >> strip_tac >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem live_immutable_represented_suffix_summary_family:
  src = cenv.ce_module /\ p.ptr_location = LocCode /\
  FLOOKUP cenv.ce_module_vars (src,id) = SOME (ImmutableLoc off) /\
  FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
    | SOME imms => get_source_immutables src imms) id = SOME (itv,iv) /\
  mem_path_offset itv path = SOME (k,ArrayTV etv bd) /\
  evaluate_subscripts itv iv path = INL (ArrayV av) /\
  off + type_memory_size itv < dimword (:256) /\
  expr_type obj = ArrayT et bd /\ ee.gas_obs = [] /\
  expr_sim_inv cenv cx env ee /\ P Hw /\
  (!H. P H ==> stmt_state_rel H ctx func cenv cx ee s) /\
  immutable_holds cenv cx (ArrayT et bd) (PlaceR (ImmutablePlace src id path)) w ee s /\
  evaluate_type (get_tenv cx) et = SOME etv /\
  evaluate_type (get_tenv cx) (ArrayT et bd) = SOME (ArrayTV etv bd) /\
  read_result cx (PlaceR (ImmutablePlace src id path)) ee = (INL (ArrayV av),ee) /\
  val_wf (ArrayTV etv bd) (ArrayV av) /\ value_has_type (ArrayTV etv bd) (ArrayV av) /\
  array_length (ArrayTV etv bd) av < dimword (:256) /\
  (!al. av = SArrayV al ==> ?n. bd = Fixed n) /\
  w = n2w (off+k) /\ eval_operand p.ptr_operand s = SOME w /\
  eval_operand iop s = SOME iw /\
  i = (if is_signed_type (expr_type idx) then w2i iw else &(w2n iw)) /\
  type_memory_bytes cenv et = type_memory_size etv /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sc x) /\
  (!l. p.ptr_operand <> Label l) /\
  (!x. iop = Var x ==> not_fresh_at sc x) /\
  (!region x. cenv.ce_imm_alloca = SOME region /\ region = Var x ==> not_fresh_at sc x) /\
  local_ptrs_reserved cenv sc /\
  compile_array_subscript p.ptr_operand iop
    (case bd of Fixed _ => F | Dynamic _ => T)
    (case bd of Fixed n => n | Dynamic _ => 0)
    (word_scale p.ptr_location) (elem_size_in_location cenv p.ptr_location et)
    (is_signed_type (expr_type idx))
    (compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca p.ptr_location) sc = (dst,sd) /\
  fn_has_code sc sd func /\ ~s.vs_halted /\
  s.vs_current_bb = sc.cs_current_bb /\ s.vs_inst_idx = LENGTH sc.cs_current_insts /\
  (!H q. P H /\ (!x z. not_fresh_at sc x /\ lookup_var x s = SOME z ==> lookup_var x q = SOME z) /\
       (!aid a. FLOOKUP s.vs_allocas aid = SOME a ==> FLOOKUP q.vs_allocas aid = SOME a) /\
       q.vs_memory = s.vs_memory /\ stmt_state_rel H ctx func cenv cx ee q ==>
       vv_post H ctx func cenv cx (Subscript (ArrayT et bd) obj idx) es sa sd s0 ee
         (PlaceR (ImmutablePlace src id path)) (LocatedValue (ArrayT et bd) p) q) ==>
  gas_summary_at F (ctx,func) []
    (select_result cx (ArrayT et bd) (PlaceR (ImmutablePlace src id path))
      (ValueSubscript (IntV i))) (ee,s)
    (\res ee' q. ?child. res = INL child /\ ee' = ee /\
      (!H. P H ==> vv_post H ctx func cenv cx (Subscript et obj idx) es sa sd s0 ee' child
        (LocatedValue et (mk_ptr dst p.ptr_location)) q) /\
      q.vs_current_bb = sd.cs_current_bb /\ q.vs_inst_idx = LENGTH sd.cs_current_insts)
    (\res ee' outcome. expr_exit res outcome)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `stmt_state_rel Hw ctx func cenv cx ee s` by metis_tac[] >>
  drule_all_then assume_tac array_index_word_bounds >>
  `compile_array_subscript p.ptr_operand iop
    (case bd of Fixed _ => F | Dynamic _ => T)
    (case bd of Fixed n => n | Dynamic _ => 0)
    (word_scale LocCode) (elem_size_in_location cenv LocCode et)
    (is_signed_type (expr_type idx))
    (compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca LocCode) sc = (dst,sd)` by gvs[] >>
  drule_all live_immutable_array_counted_fields >>
  Cases_on `valid_index (ArrayTV etv bd) av i`
  >- suspend "valid" >>
  qpat_x_assum `valid_index _ _ _ <=> _` (fn th => pure_asm_rewrite_tac[GSYM th, boolTheory.COND_CLAUSES]) >> strip_tac >>
  drule_all live_immutable_select_error >> strip_tac >>
  irule select_result_counted_summary >> simp[] >>
  goal_assum (drule_at Any) >>
  gvs[exprSimDefsTheory.expr_exit_def, fragExecTheory.exit_result_def]
QED

Resume live_immutable_represented_suffix_summary_family[valid]:
  qpat_x_assum `valid_index _ _ _ <=> _`
    (fn eq => qpat_assum `valid_index _ _ _`
      (fn v => pure_rewrite_tac[GSYM eq, v, boolTheory.COND_CLAUSES])) >> strip_tac >>
  `?v. array_index (ArrayTV etv bd) av i = SOME v` by
    metis_tac[vyperArrayTheory.array_index_valid, optionTheory.IS_SOME_EXISTS] >>
  `value_has_type etv v` by
    metis_tac[vyperAssignPreservesTypeTheory.array_index_has_type,
              vyperTypingTheory.evaluate_type_well_formed] >>
  `val_wf etv v` by
    metis_tac[valueTypingMemoryPropsTheory.value_has_type_memory_wf] >>
  `iw = n2w (Num i)` by
    (qpat_x_assum `valid_index _ _ _` mp_tac >>
     qpat_x_assum `i = _` mp_tac >> rpt (pop_assum kall_tac) >>
     Cases_on `is_signed_type (expr_type idx)` >>
     simp[integer_wordTheory.w2i_def] >>
     Cases_on `word_msb iw` >> simp[] >> rw[] >> gvs[]) >>
  `!H. P H ==> vv_post H ctx func cenv cx (Subscript (ArrayT et bd) obj idx) es sa sd s0 ee
     (PlaceR (ImmutablePlace src id path)) (LocatedValue (ArrayT et bd) p) q` by
    (rpt strip_tac >>
     `stmt_state_rel H ctx func cenv cx ee s` by metis_tac[] >>
     `stmt_state_rel H ctx func cenv cx ee q` by
       (irule stmt_state_rel_fields_transport >> metis_tac[]) >>
     first_x_assum irule >> simp[]) >>
  `eval_operand p.ptr_operand q = SOME w` by
    (qpat_x_assum `eval_operand p.ptr_operand s = SOME w` mp_tac >>
     qpat_x_assum `!x. p.ptr_operand = Var x ==> _` mp_tac >>
     qpat_x_assum `!x z. not_fresh_at sc x /\ lookup_var x s = SOME z ==> _` mp_tac >>
     qpat_x_assum `!l. p.ptr_operand <> Label l` mp_tac >>
     rpt (pop_assum kall_tac) >>
     Cases_on `p.ptr_operand` >> simp[venomStateTheory.eval_operand_def] >> metis_tac[]) >>
  `eval_operand dst q = SOME (w + n2w
      ((case bd of Fixed _ => 0 | Dynamic _ => 32) + Num i * type_memory_size etv))` by
    (qpat_x_assum `eval_operand dst q = _` mp_tac >>
     qpat_x_assum `w = n2w _` mp_tac >>
     qpat_x_assum `iw = n2w _` mp_tac >>
     qpat_x_assum `type_memory_bytes cenv et = _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     Cases_on `bd` >> simp[compileEnvTheory.word_scale_def,
       compileEnvTheory.elem_size_in_location_def, compileEnvTheory.is_slot_addressed_def,
       GSYM wordsTheory.word_mul_n2w] >>
     rpt strip_tac >>
     simp[wordsTheory.word_mul_n2w, GSYM wordsTheory.word_add_n2w,
          AC wordsTheory.WORD_ADD_ASSOC wordsTheory.WORD_ADD_COMM]) >>
  irule live_immutable_element_summary_family >>
  rpt (goal_assum (drule_at Any)) >> simp[] >>
  qpat_x_assum `FLOOKUP cenv.ce_module_vars (src,id) = _` mp_tac >> simp[]
QED

Finalise live_immutable_represented_suffix_summary_family

Theorem live_immutable_element_summary:
  FLOOKUP cenv.ce_module_vars (cenv.ce_module,id) = SOME (ImmutableLoc off) /\
  src = cenv.ce_module /\
  FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
    | SOME imms => get_source_immutables src imms) id = SOME (itv,iv) /\
  mem_path_offset itv path = SOME (k,ArrayTV etv bd) /\
  evaluate_subscripts itv iv path = INL (ArrayV av) /\
  expr_type obj = ArrayT et bd /\ ee.gas_obs = [] /\
  evaluate_type (get_tenv cx) (ArrayT et bd) = SOME (ArrayTV etv bd) /\
  evaluate_type (get_tenv cx) et = SOME etv /\
  read_result cx (PlaceR (ImmutablePlace src id path)) ee = (INL (ArrayV av),ee) /\
  array_index (ArrayTV etv bd) av i = SOME v /\
  val_wf (ArrayTV etv bd) (ArrayV av) /\ val_wf etv v /\ value_has_type etv v /\
  vv_post H ctx func cenv cx (Subscript (ArrayT et bd) obj idx) es sa sd s0 ee
    (PlaceR (ImmutablePlace src id path)) (LocatedValue ann p) q /\
  p.ptr_location = LocCode /\ w = n2w (off+k) /\
  eval_operand p.ptr_operand q = SOME w /\
  j = (case bd of Fixed _ => 0 | Dynamic _ => 32) + Num i * type_memory_size etv /\
  eval_operand dst q = SOME (w+n2w j) /\
  gas_marked_path F ctx func s 0 (OK q) /\
  q.vs_current_bb = sd.cs_current_bb /\ q.vs_inst_idx = LENGTH sd.cs_current_insts ==>
  gas_summary_at F (ctx,func) []
    (select_result cx (ArrayT et bd) (PlaceR (ImmutablePlace src id path))
      (ValueSubscript (IntV i))) (ee,s)
    (\res ee' q. ?child. res = INL child /\
      vv_post H ctx func cenv cx (Subscript et obj idx) es sa sd s0 ee' child
        (LocatedValue et (mk_ptr dst p.ptr_location)) q /\
      q.vs_current_bb = sd.cs_current_bb /\ q.vs_inst_idx = LENGTH sd.cs_current_insts)
    (\res ee' outcome. expr_exit res outcome)
Proof
  strip_tac >>
  mp_tac (live_immutable_element_summary_family |> Q.INST [`P` |-> `(\h. h = H)`]) >>
  (impl_tac >- (simp[] >> gvs[])) >>
  simp[gasSummaryTheory.gas_summary_at_def] >> metis_tac[]
QED

Theorem live_immutable_represented_suffix_summary:
  src = cenv.ce_module /\ p.ptr_location = LocCode /\
  FLOOKUP cenv.ce_module_vars (src,id) = SOME (ImmutableLoc off) /\
  FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of NONE => FEMPTY
    | SOME imms => get_source_immutables src imms) id = SOME (itv,iv) /\
  mem_path_offset itv path = SOME (k,ArrayTV etv bd) /\
  evaluate_subscripts itv iv path = INL (ArrayV av) /\
  off + type_memory_size itv < dimword (:256) /\
  expr_type obj = ArrayT et bd /\ ee.gas_obs = [] /\
  expr_sim_inv cenv cx env ee /\ stmt_state_rel H ctx func cenv cx ee s /\
  immutable_holds cenv cx (ArrayT et bd) (PlaceR (ImmutablePlace src id path)) w ee s /\
  evaluate_type (get_tenv cx) et = SOME etv /\
  evaluate_type (get_tenv cx) (ArrayT et bd) = SOME (ArrayTV etv bd) /\
  read_result cx (PlaceR (ImmutablePlace src id path)) ee = (INL (ArrayV av),ee) /\
  val_wf (ArrayTV etv bd) (ArrayV av) /\ value_has_type (ArrayTV etv bd) (ArrayV av) /\
  array_length (ArrayTV etv bd) av < dimword (:256) /\
  (!al. av = SArrayV al ==> ?n. bd = Fixed n) /\
  w = n2w (off+k) /\ eval_operand p.ptr_operand s = SOME w /\
  eval_operand iop s = SOME iw /\
  i = (if is_signed_type (expr_type idx) then w2i iw else &(w2n iw)) /\
  type_memory_bytes cenv et = type_memory_size etv /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sc x) /\
  (!l. p.ptr_operand <> Label l) /\
  (!x. iop = Var x ==> not_fresh_at sc x) /\
  (!region x. cenv.ce_imm_alloca = SOME region /\ region = Var x ==> not_fresh_at sc x) /\
  local_ptrs_reserved cenv sc /\
  compile_array_subscript p.ptr_operand iop
    (case bd of Fixed _ => F | Dynamic _ => T)
    (case bd of Fixed n => n | Dynamic _ => 0)
    (word_scale p.ptr_location) (elem_size_in_location cenv p.ptr_location et)
    (is_signed_type (expr_type idx))
    (compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca p.ptr_location) sc = (dst,sd) /\
  fn_has_code sc sd func /\ ~s.vs_halted /\
  s.vs_current_bb = sc.cs_current_bb /\ s.vs_inst_idx = LENGTH sc.cs_current_insts /\
  (!q. (!x z. not_fresh_at sc x /\ lookup_var x s = SOME z ==> lookup_var x q = SOME z) /\
       (!aid a. FLOOKUP s.vs_allocas aid = SOME a ==> FLOOKUP q.vs_allocas aid = SOME a) /\
       q.vs_memory = s.vs_memory /\ stmt_state_rel H ctx func cenv cx ee q ==>
       vv_post H ctx func cenv cx (Subscript (ArrayT et bd) obj idx) es sa sd s0 ee
         (PlaceR (ImmutablePlace src id path)) (LocatedValue (ArrayT et bd) p) q) ==>
  gas_summary_at F (ctx,func) []
    (select_result cx (ArrayT et bd) (PlaceR (ImmutablePlace src id path))
      (ValueSubscript (IntV i))) (ee,s)
    (\res ee' q. ?child. res = INL child /\
      vv_post H ctx func cenv cx (Subscript et obj idx) es sa sd s0 ee' child
        (LocatedValue et (mk_ptr dst p.ptr_location)) q /\
      q.vs_current_bb = sd.cs_current_bb /\ q.vs_inst_idx = LENGTH sd.cs_current_insts)
    (\res ee' outcome. expr_exit res outcome)
Proof
  strip_tac >>
  mp_tac (live_immutable_represented_suffix_summary_family |>
    Q.INST [`P` |-> `(\h. h = H)`, `Hw` |-> `H`]) >>
  (impl_tac >- (simp[] >> gvs[])) >>
  simp[gasSummaryTheory.gas_summary_at_def] >> metis_tac[]
QED
