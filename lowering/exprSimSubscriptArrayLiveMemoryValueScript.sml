(* Captured memory Values through an index fragment. *)
Theory exprSimSubscriptArrayLiveMemoryValue
Ancestors
  exprSimSubscriptArrayFrame exprSimSubscriptArraySuffix exprSimSubscriptArrayFramed
  exprSimSubscriptArrayLiveMemory exprSimSubscriptArrayEndpoint
  exprSimProps exprSimWordArgs exprSimHypsDefs exprLoweringProps vyperValue loweringPosts vyperState valueEncodingProofs
  valueEncoding valueEncodingDefs exprBopSimProps freshWrites

Theorem value_memory_bytes_frame:
  vv_at cenv cx ty sa sb es (Value v) (LocatedValue ty p) s /\
  p.ptr_location = LocMemory /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  eval_operand p.ptr_operand s = SOME w /\
  expr_sim_inv cenv cx env es /\
  (ee.scopes = es.scopes \/ dynarray_free tv) /\
  wb_frame cenv es ee sb s s' ==>
  mem_bytes_at (w2n w) (val_footprint tv v) s'.vs_memory =
    mem_bytes_at (w2n w) (val_footprint tv v) s.vs_memory
Proof
  strip_tac >>
  qpat_x_assum `vv_at _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[vv_at_def, read_result_def, return_def] >> strip_tac >> gvs[]
  >- (gvs[wb_frame_def] >>
      `mem_bytes_at b sz s'.vs_memory = mem_bytes_at b sz s.vs_memory` by
        (first_x_assum irule >> simp[] >> metis_tac[]) >>
      drule mem_bytes_at_agree_window >> simp[])
  >- (gvs[wb_frame_def] >>
      `mem_bytes_at b sz s'.vs_memory = mem_bytes_at b sz s.vs_memory` by
        (fs[locals_kept_def] >> metis_tac[]) >>
      drule mem_bytes_at_agree_window >> simp[])
  >- simp[mem_bytes_at_def]
  >- (gvs[wb_frame_def] >>
      `mem_bytes_at b sz s'.vs_memory = mem_bytes_at b sz s.vs_memory` by
        (first_x_assum irule >> simp[] >> metis_tac[]) >>
      drule mem_bytes_at_agree_window >> simp[])
  >- (gvs[wb_frame_def] >> drule_all locals_kept_dynarray_free_value >> simp[]) >>
  simp[mem_bytes_at_def]
QED

Theorem value_memory_at_frame:
  vv_at cenv cx ty sa sb es (Value v) (LocatedValue ty p) s /\
  p.ptr_location = LocMemory /\
  (!w. eval_operand p.ptr_operand s = SOME w ==> eval_operand p.ptr_operand s' = SOME w) /\
  wb_frame cenv es ee sb s s' /\ local_ptrs_reserved cenv sb /\
  local_ptrs_rel func cenv es.scopes s /\
  sb.cs_next_id <= sc.cs_next_id ==>
  vv_at cenv cx ty sa sc ee (Value v) (LocatedValue ty p) s'
Proof
  strip_tac >>
  `!n b sz. local_region cenv es.scopes s n b sz ==>
             local_region cenv ee.scopes s' n b sz` by
    (rpt strip_tac >> irule local_region_frame_fwd >>
     qexistsl_tac [`s`,`sb`,`es.scopes`] >> fs[wb_frame_def, locals_kept_def]) >>
  `!n b sz. local_region cenv ee.scopes s' n b sz ==>
             local_region cenv es.scopes s n b sz` by
    (rpt strip_tac >> irule local_region_frame >>
     conj_tac >- metis_tac[] >>
     qexistsl_tac [`sb`,`ee.scopes`,`s'`] >> fs[wb_frame_def, locals_kept_def]) >>
  gvs[vv_at_def, read_result_def, return_def] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >> gvs[] >> fs[wb_frame_def]
  >- (disj1_tac >> qexistsl_tac [`aid`,`b`,`sz`] >> simp[] >> metis_tac[]) >>
  disj2_tac >> disj1_tac >> qexistsl_tac [`n`,`b`,`sz`] >> simp[] >>
  fs[local_place_at_def]
QED

Theorem value_memory_holds_frame:
  vv_holds cenv cx ty (Value v) (LocatedValue ty p) es s /\
  vv_at cenv cx ty sa sb es (Value v) (LocatedValue ty p) s /\
  p.ptr_location = LocMemory /\ ~is_word_type ty /\
  (!tv. evaluate_type (get_tenv cx) ty = SOME tv ==>
        ee.scopes = es.scopes \/ dynarray_free tv) /\
  (!w. eval_operand p.ptr_operand s = SOME w ==> eval_operand p.ptr_operand s' = SOME w) /\
  expr_sim_inv cenv cx env es /\ wb_frame cenv es ee sb s s' ==>
  vv_holds cenv cx ty (Value v) (LocatedValue ty p) ee s'
Proof
  strip_tac >>
  qpat_x_assum `vv_holds _ _ _ _ _ _ _` mp_tac >>
  simp[vv_holds_def, read_result_def, return_def] >> strip_tac >>
  qexists_tac `w` >> simp[] >> rpt strip_tac >>
  `mem_bytes_at (w2n w) (val_footprint tvt v) s'.vs_memory =
   mem_bytes_at (w2n w) (val_footprint tvt v) s.vs_memory` by
    (irule value_memory_bytes_frame >> simp[] >>
     goal_assum (drule_at Any) >> metis_tac[]) >>
  irule val_in_memory_footprint_agree >> simp[] >>
  conj_tac >- fs[vv_at_def, read_result_def, return_def] >>
  qexists_tac `s.vs_memory` >> simp[]
QED

Theorem memory_array_value_element_at:
  vv_at cenv cx (ArrayT et bd) sa sb ee (Value (ArrayV av)) (LocatedValue ann p) q /\
  p.ptr_location = LocMemory /\ eval_operand p.ptr_operand q = SOME w /\
  evaluate_type (get_tenv cx) (ArrayT et bd) = SOME (ArrayTV etv bd) /\
  evaluate_type (get_tenv cx) et = SOME etv /\
  val_wf (ArrayTV etv bd) (ArrayV av) /\ val_wf etv v /\
  array_index (ArrayTV etv bd) av i = SOME v /\
  j = (case bd of Fixed _ => 0 | Dynamic _ => 32) + Num i * type_memory_size etv /\
  eval_operand dst q = SOME dw /\ w2n dw = w2n w + j ==>
  vv_at cenv cx et sa sb ee (Value v) (LocatedValue et (mk_ptr dst LocMemory)) q
Proof
  strip_tac >>
  `sub_layout (ArrayTV etv bd) (ArrayV av) 0 (ArrayTV etv bd) (ArrayV av)` by
    simp[sub_layout_def] >>
  drule_all sub_layout_array_element >> strip_tac >>
  `j + val_footprint etv v <= val_footprint (ArrayTV etv bd) (ArrayV av)` by
    (drule val_footprint_le >> fs[sub_layout_def, val_footprint_def] >> decide_tac) >>
  drule_all array_element_step_offset >> strip_tac >>
  qpat_x_assum `vv_at _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[vv_at_def, read_result_def, return_def, contextTheory.mk_ptr_def] >>
  strip_tac >> gvs[]
  >- (disj1_tac >> qexistsl_tac [`aid`,`b`,`sz`] >> simp[] >> metis_tac[]) >>
  disj2_tac >> disj1_tac >> qexistsl_tac [`n`,`b`,`sz`] >> simp[local_place_at_def] >>
  `j + w2n w - b = (w2n w - b) + j` by decide_tac >>
  simp[] >> drule_all local_val_at_array_element >> simp[]
QED

Theorem live_memory_value_base_endpoint:
  vv_post ctx func cenv cx obj es sa sb s0 t (Value a) (LocatedValue (ArrayT et bd) p) u /\
  expr_post ctx func cenv cx idx t sb sc u ee iv iop s /\
  expr_type obj = ArrayT et bd /\ post_value_type cenv obj = expr_type obj /\
  p.ptr_location = LocMemory /\
  (ee.scopes = t.scopes \/ (?n. bd = Fixed n /\
    !tv. evaluate_type (get_tenv cx) et = SOME tv ==> dynarray_free tv)) /\
  is_word_type (expr_type idx) /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sb x) /\ (!l. p.ptr_operand <> Label l) /\
  (!x. iop = Var x ==> not_fresh_at sc x) /\ (!l. iop <> Label l) /\
  expr_sim_inv cenv cx env t /\ stmt_state_rel ctx func cenv cx es s0 /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sb /\
  MAP FDOM es.scopes = MAP FDOM t.scopes /\
  sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id /\
  sb.cs_next_var <= sc.cs_next_var /\ sb.cs_next_id <= sd.cs_next_id /\
  (!x w. not_fresh_at sc x /\ lookup_var x s = SOME w ==> lookup_var x q = SOME w) /\
  (!aid a. FLOOKUP s.vs_allocas aid = SOME a ==> FLOOKUP q.vs_allocas aid = SOME a) /\
  q.vs_memory = s.vs_memory /\ stmt_state_rel ctx func cenv cx ee q ==>
  vv_post ctx func cenv cx (Subscript (ArrayT et bd) obj idx) es sa sd s0 ee (Value a)
    (LocatedValue (ArrayT et bd) p) q
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `expr_post ctx func cenv cx idx t sb sd u ee iv iop q` by
    (irule word_expr_post_readonly_tail >> simp[] >> qexistsl_tac [`s`,`sc`] >> simp[]) >>
  `wb_frame cenv t ee sb u q` by metis_tac[exprSimWordArgsTheory.expr_post_frame] >>
  `wb_frame cenv es t sa s0 u` by
    (fs[vv_post_def] >> simp[wb_frame_def] >> first_assum ACCEPT_TAC) >>
  `wb_frame cenv es ee sa s0 q` by (drule_all wb_frame_trans >> simp[]) >>
  `!w. eval_operand p.ptr_operand u = SOME w ==> eval_operand p.ptr_operand q = SOME w` by
    (rpt strip_tac >> irule eval_operand_frame >> simp[] >>
     qexistsl_tac [`sb`,`u`] >> fs[wb_frame_def]) >>
  `local_ptrs_rel func cenv t.scopes u` by
    fs[vv_post_def, exprLoweringPropsTheory.stmt_state_rel_def,
       loweringStateRelDefsTheory.state_rel_def] >>
  `!tv. evaluate_type (get_tenv cx) (ArrayT et bd) = SOME tv ==>
     ee.scopes = t.scopes \/ dynarray_free tv` by
    (rpt strip_tac >> fs[evaluate_type_def, AllCaseEqs()] >>
     metis_tac[dynarray_free_fixed]) >>
  `vv_holds cenv cx (ArrayT et bd) (Value a) (LocatedValue (ArrayT et bd) p) ee q` by
    (irule value_memory_holds_frame >> simp[compileEnvTheory.is_word_type_def] >>
     qexistsl_tac [`env`,`t`,`u`,`sa`,`sb`] >> fs[vv_post_def]) >>
  `vv_at cenv cx (ArrayT et bd) sa sd ee (Value a) (LocatedValue (ArrayT et bd) p) q` by
    (irule value_memory_at_frame >> simp[] >>
     qexistsl_tac [`t`,`func`,`u`,`sb`] >> fs[vv_post_def]) >>
  `~expr_has_effect obj /\ ~expr_has_effect idx ==> pure_frame cenv func es sa s0 q` by
    (strip_tac >> irule pure_frame_trans >> simp[] >> qexistsl_tac [`t`,`sb`,`u`] >>
     fs[vv_post_def, wb_frame_def] >> drule_all exprSimWordArgsTheory.expr_post_pure_frame >> simp[]) >>
  irule exprSimHashTheory.vv_post_frame_intro >>
  simp[vyperASTTheory.expr_type_def, expr_has_effect_thm,
       vv_place_ptr_def, vv_storage_live_def]
QED

Theorem memory_value_array_element_post:
  vv_post ctx func cenv cx (Subscript (ArrayT et bd) obj idx) es sa sb s0 ee
    (Value (ArrayV av)) (LocatedValue (ArrayT et bd) p) q /\
  p.ptr_location = LocMemory /\ eval_operand p.ptr_operand q = SOME w /\
  evaluate_type (get_tenv cx) (ArrayT et bd) = SOME (ArrayTV etv bd) /\
  evaluate_type (get_tenv cx) et = SOME etv /\
  val_wf (ArrayTV etv bd) (ArrayV av) /\ val_wf etv v /\ value_has_type etv v /\
  array_index (ArrayTV etv bd) av i = SOME v /\
  j = (case bd of Fixed _ => 0 | Dynamic _ => 32) + Num i * type_memory_size etv /\
  eval_operand dst q = SOME (w + n2w j) /\ w2n (w + n2w j) = w2n w + j ==>
  vv_post ctx func cenv cx (Subscript et obj idx) es sa sb s0 ee (Value v)
    (LocatedValue et (mk_ptr dst LocMemory)) q
Proof
  strip_tac >>
  `vv_holds cenv cx (ArrayT et bd) (Value (ArrayV av)) (LocatedValue (ArrayT et bd) p) ee q /\
   vv_at cenv cx (ArrayT et bd) sa sb ee (Value (ArrayV av)) (LocatedValue (ArrayT et bd) p) q` by
    fs[vv_post_def, vyperASTTheory.expr_type_def] >>
  `read_result cx (Value (ArrayV av)) ee = (INL (ArrayV av),ee) /\
   read_result cx (Value v) ee = (INL v,ee)` by simp[read_result_def, return_def] >>
  `vv_holds cenv cx et (Value v) (LocatedValue et (mk_ptr dst LocMemory)) ee q` by
    metis_tac[vv_holds_array_element] >>
  `vv_at cenv cx et sa sb ee (Value v) (LocatedValue et (mk_ptr dst LocMemory)) q` by
    (irule memory_array_value_element_at >> simp[] >> goal_assum (drule_at Any) >>
     qexistsl_tac [`i`,`w`] >> gvs[]) >>
  fs[vv_post_def, vyperASTTheory.expr_type_def, vv_place_ptr_def, vv_storage_live_def,
     contextTheory.mk_ptr_def] >> first_assum ACCEPT_TAC
QED

Theorem live_memory_value_array_suffix_summary:
  expr_body_pre cenv cx env (Subscript ann obj idx) es /\
  expr_type obj = ArrayT et bd /\ post_value_type cenv obj = expr_type obj /\
  eval_expr cx obj es = (INL (Value a),t) /\
  eval_expr cx idx t = (INL ir,ee) /\ read_result cx ir ee = (INL iv,ee) /\
  ee.gas_obs = [] /\ p.ptr_location = LocMemory /\
  (ee.scopes = t.scopes \/ (?n. bd = Fixed n /\
    !tv. evaluate_type (get_tenv cx) et = SOME tv ==> dynarray_free tv)) /\
  vv_post ctx func cenv cx obj es sa sb s0 t (Value a)
    (LocatedValue (ArrayT et bd) p) u /\
  expr_post ctx func cenv cx idx t sb sc u ee iv iop s /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sb x) /\ (!l. p.ptr_operand <> Label l) /\
  (!x. iop = Var x ==> not_fresh_at sc x) /\ (!l. iop <> Label l) /\
  expr_sim_inv cenv cx env t /\ stmt_state_rel ctx func cenv cx es s0 /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sb /\ local_ptrs_reserved cenv sc /\
  MAP FDOM es.scopes = MAP FDOM t.scopes /\
  sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id /\
  sb.cs_next_var <= sc.cs_next_var /\ sb.cs_next_id <= sc.cs_next_id /\
  compile_array_subscript p.ptr_operand iop
    (case bd of Fixed _ => F | Dynamic _ => T)
    (case bd of Fixed n => n | Dynamic _ => 0)
    (word_scale p.ptr_location) (elem_size_in_location cenv p.ptr_location et)
    (is_signed_type (expr_type idx))
    (compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca p.ptr_location) sc = (dst,sd) /\
  fn_has_code sc sd func /\ ~s.vs_halted /\
  s.vs_current_bb = sc.cs_current_bb /\ s.vs_inst_idx = LENGTH sc.cs_current_insts ==>
  gas_summary_at F (ctx,func) []
    (select_result cx (ArrayT et bd) (Value a) (ValueSubscript iv)) (ee,s)
    (\res ee' q. ?child. res = INL child /\
      vv_post ctx func cenv cx (Subscript ann obj idx) es sa sd s0 ee' child
        (LocatedValue ann (mk_ptr dst p.ptr_location)) q /\
      q.vs_current_bb = sd.cs_current_bb /\ q.vs_inst_idx = LENGTH sd.cs_current_insts)
    (\res ee' outcome. expr_exit res outcome)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then assume_tac exprSimSubscriptArraySourceTheory.expr_body_pre_array_subscript_base >>
  drule_all_then assume_tac exprSimSubscriptArraySourceTheory.expr_body_pre_array_subscript_index_after_base >>
  drule_all_then strip_assume_tac exprSimSourceTheory.expr_body_pre_runtime_typed >>
  `value_has_type tvt iv` by metis_tac[] >>
  drule_all framed_array_index_post_view >> strip_tac >>
  `is_word_type (expr_type idx)` by
    (qpat_x_assum `value_has_type tvt iv` mp_tac >>
     qpat_x_assum `evaluate_type _ (expr_type idx) = _` mp_tac >>
     qpat_assum `iv = IntV i` SUBST1_TAC >> rpt (pop_assum kall_tac) >>
     Cases_on `expr_type idx` >>
     simp[vyperValueTheory.evaluate_type_def, AllCaseEqs(),
          vyperTypingTheory.value_has_type_def, compileEnvTheory.is_word_type_def] >>
     rpt strip_tac >> gvs[vyperTypingTheory.value_has_type_def, compileEnvTheory.is_word_type_def]) >>
  `stmt_state_rel ctx func cenv cx ee s` by fs[expr_post_def] >>
  `!x. p.ptr_operand = Var x ==> not_fresh_at sc x` by
    (rpt strip_tac >> qpat_x_assum `!x. p.ptr_operand = Var x ==> _` drule >>
     metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  `cs_extends sc sd /\ sc.cs_next_var <= sd.cs_next_var /\ sc.cs_next_id <= sd.cs_next_id` by
    (qpat_x_assum `compile_array_subscript _ _ _ _ _ _ _ _ sc = _`
       (mp_tac o Q.AP_TERM `SND`) >> simp[] >> disch_then (SUBST1_TAC o SYM) >>
     rewrite_tac[GSYM ci_mono_def] >> irule ci_mono_compile_array_subscript >>
     simp[ci_mono_compile_ptr_load]) >>
  suspend "represented"
QED

Resume live_memory_value_array_suffix_summary[represented]:
  `!q sd. (!x z. not_fresh_at sc x /\ lookup_var x s = SOME z ==> lookup_var x q = SOME z) /\
       (!aid a. FLOOKUP s.vs_allocas aid = SOME a ==> FLOOKUP q.vs_allocas aid = SOME a) /\
       q.vs_memory = s.vs_memory /\ stmt_state_rel ctx func cenv cx ee q /\
       sb.cs_next_id <= sd.cs_next_id ==>
       vv_post ctx func cenv cx (Subscript (ArrayT et bd) obj idx) es sa sd s0 ee (Value a)
         (LocatedValue (ArrayT et bd) p) q` by
    (rpt strip_tac >> irule live_memory_value_base_endpoint >> simp[] >>
     goal_assum (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >> simp[] >>
     metis_tac[]) >>
  `vv_post ctx func cenv cx (Subscript (ArrayT et bd) obj idx) es sa sc s0 ee (Value a)
     (LocatedValue (ArrayT et bd) p) s` by simp[] >>
  `?etv av b. a = ArrayV av /\
     evaluate_type (get_tenv cx) et = SOME etv /\
     evaluate_type (get_tenv cx) (ArrayT et bd) = SOME (ArrayTV etv bd) /\
     value_has_type (ArrayTV etv bd) (ArrayV av) /\
     val_wf (ArrayTV etv bd) (ArrayV av) /\
     eval_operand p.ptr_operand s = SOME b /\
     val_in_memory (ArrayTV etv bd) (ArrayV av) (w2n b) s.vs_memory` by
    (`vv_holds cenv cx (ArrayT et bd) (Value a) (LocatedValue (ArrayT et bd) p) ee s` by
       (qpat_x_assum `vv_post _ _ _ _ (Subscript _ _ _) _ _ sc _ _ _ _ s` mp_tac >>
        pure_rewrite_tac[vv_post_def, post_value_type_def, vyperASTTheory.expr_type_def] >>
        strip_tac >> first_assum ACCEPT_TAC) >>
     qpat_x_assum `ee.scopes = _ \/ _` kall_tac >>
     mp_tac (Q.SPECL [`cenv`,`cx`,`env`,`obj`,`es`,`Value a`,`t`] exprSimSourceTheory.expr_body_pre_runtime_typed) >>
     (impl_tac >- simp[]) >> disch_then (qx_choose_then `base_tv` strip_assume_tac) >>
     `?etv. evaluate_type (get_tenv cx) et = SOME etv /\
       base_tv = ArrayTV etv bd` by gvs[vyperValueTheory.evaluate_type_def, AllCaseEqs()] >>
     gvs[read_result_def, return_def] >>
     Cases_on `a` >> fs[vyperTypingTheory.value_has_type_def] >>
     `val_wf (ArrayTV etv bd) (ArrayV a')` by
       metis_tac[valueTypingMemoryPropsTheory.value_has_type_memory_wf] >>
     qpat_x_assum `vv_holds _ _ _ _ _ ee s` mp_tac >>
     simp[vv_holds_def, read_result_def, return_def] >> metis_tac[]) >>
  qpat_x_assum `a = ArrayV av` SUBST_ALL_TAC >>
  `array_length (ArrayTV etv bd) av < dimword (:256)` by
    metis_tac[targetSubscriptMemoryTheory.target_memory_array_length_bound] >>
  `ann = et` by
    (qpat_x_assum `expr_body_pre _ _ _ (Subscript _ _ _) _` mp_tac >>
     simp[expr_body_pre_def, Once vyperTypeSystemTheory.well_typed_expr_def] >>
     strip_tac >> gvs[vyperTypeSystemTheory.subscript_type_ok_def] >>
     drule placeTypingPropsTheory.type_place_expr_vtype_annotation >>
     strip_tac >> Cases_on `vt` >> gvs[vyperTypeSystemTheory.vtype_annotation_ok_def] >>
     gvs[vyperTypeSystemTheory.subscript_vtype_def, AllCaseEqs()]) >>
  `type_memory_bytes cenv et = type_memory_size etv` by
    (irule exprSimHypsTheory.expr_sim_inv_memory_size >> goal_assum (drule_at Any) >>
     qexistsl_tac [`env`,`t`] >> simp[]) >>
  qpat_x_assum `ann = et` SUBST_ALL_TAC >>
  qpat_x_assum `iv = IntV i` SUBST_ALL_TAC >>
  suspend "selection"
QED

Resume live_memory_value_array_suffix_summary[selection]:
  `((case bd of Fixed _ => F | Dynamic _ => T) ==>
     mload (w2n b) s = n2w (array_length (ArrayTV etv bd) av)) /\
   ((case bd of Fixed _ => F | Dynamic _ => T) = F ==>
     (case bd of Fixed n => n | Dynamic _ => 0) = array_length (ArrayTV etv bd) av)` by
    (Cases_on `bd` >> simp[]
     >- (Cases_on `av` >> gvs[vyperTypingTheory.value_has_type_def,
                            vyperValueOperationTheory.array_length_def]) >>
     drule_all targetSubscriptMemoryTheory.target_memory_array_header >> simp[]) >>
  `!al. av = SArrayV al ==> ?n. bd = Fixed n` by
    (rpt strip_tac >> Cases_on `bd` >> gvs[vyperTypingTheory.value_has_type_def]) >>
  drule_all_then assume_tac array_index_word_bounds >>
  Cases_on `valid_index (ArrayTV etv bd) av i`
  >- suspend "valid" >>
  `~idx_in_range (is_signed_type (expr_type idx)) iw
      (if (case bd of Fixed _ => F | Dynamic _ => T) then mload (w2n b) s
       else n2w (case bd of Fixed n => n | Dynamic _ => 0))` by
    (Cases_on `bd` >> fs[] >> metis_tac[]) >>
  `?q. gas_marked_path F ctx func s 0 (Abort Revert_abort q)` by
    (qpat_x_assum `p.ptr_location = LocMemory` SUBST_ALL_TAC >>
     drule_all targetSubscriptMemoryTheory.target_memory_array_abort_path >> simp[]) >>
  `select_result cx (ArrayT et bd) (Value (ArrayV av)) (ValueSubscript (IntV i)) ee =
    (INR (Error (RuntimeError "evaluate_subscripts array_index")),ee)` by
    (drule_all exprSimSubscriptArraySourceTheory.evaluate_array_subscript_oob >>
     simp[select_result_def, bind_def, lift_option_type_def, lift_sum_def,
          return_def, raise_def, vyperStateTheory.evaluate_subscripts_def]) >>
  irule select_result_counted_summary >> simp[] >> goal_assum (drule_at Any) >>
  fs[exprSimDefsTheory.expr_exit_def, fragExecTheory.exit_result_def]
QED

Resume live_memory_value_array_suffix_summary[valid]:
  `idx_in_range (is_signed_type (expr_type idx)) iw
      (if (case bd of Fixed _ => F | Dynamic _ => T) then mload (w2n b) s
       else n2w (case bd of Fixed n => n | Dynamic _ => 0))` by
    (Cases_on `bd` >> fs[] >> metis_tac[]) >>
  qpat_assum `p.ptr_location = LocMemory` (fn th => SUBST_ALL_TAC th >> assume_tac th) >>
  drule_all targetSubscriptMemoryTheory.target_memory_array_path >> strip_tac >>
  rename1 `gas_marked_path F ctx func s 0 (OK q)` >>
  suspend "child"
QED

Resume live_memory_value_array_suffix_summary[child]:
  `?v. array_index (ArrayTV etv bd) av i = SOME v /\
       val_wf etv v /\ value_has_type etv v` by
    (drule_all exprSimSubscriptArraySourceTheory.evaluate_array_subscript_in_bounds >>
     rewrite_tac[exprSimSubscriptArraySourceTheory.evaluate_array_subscript_result] >>
     Cases_on `array_index (ArrayTV etv bd) av i` >> simp[] >> strip_tac >>
     `well_formed_type_value etv` by metis_tac[vyperTypeValuesTheory.evaluate_type_well_formed_type_value] >>
     `value_has_type etv x` by metis_tac[vyperAssignPreservesTypeTheory.array_index_has_type] >>
     metis_tac[valueTypingMemoryPropsTheory.value_has_type_memory_wf]) >>

  `eval_operand p.ptr_operand q = SOME b` by
    (irule eval_operand_frame >> simp[] >> qexistsl_tac [`sc`,`s`] >> simp[]) >>
  `vv_post ctx func cenv cx (Subscript (ArrayT et bd) obj idx) es sa sd s0 ee
     (Value (ArrayV av)) (LocatedValue (ArrayT et bd) p) q` by simp[] >>
  `w2n b + val_footprint (ArrayTV etv bd) (ArrayV av) < dimword (:256)` by
    (`read_result cx (Value (ArrayV av)) ee = (INL (ArrayV av),ee)` by
       simp[read_result_def, return_def] >>
     drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`) vv_post_memory_footprint_bound >>
     simp[vyperASTTheory.expr_type_def] >> disch_then drule >> simp[]) >>
  qabbrev_tac `j = (case bd of Fixed _ => 0 | Dynamic _ => 32) + Num i * type_memory_size etv` >>
  `sub_layout (ArrayTV etv bd) (ArrayV av) 0 (ArrayTV etv bd) (ArrayV av)` by
    simp[sub_layout_def] >>
  `j + type_memory_size etv <= val_footprint (ArrayTV etv bd) (ArrayV av)` by
    (drule_all sub_layout_array_element >> simp[Abbr `j`, sub_layout_def, val_footprint_def]) >>
  `w2n (b + n2w j) = w2n b + j` by
    (irule exprSimAttributePropsTheory.field_ptr_w2n >> metis_tac[]) >>
  `iw = n2w (Num i)` by
    (qpat_x_assum `valid_index _ _ _` mp_tac >>
     qpat_x_assum `i = _` mp_tac >> rpt (pop_assum kall_tac) >>
     Cases_on `is_signed_type (expr_type idx)` >>
     simp[integer_wordTheory.w2i_def] >>
     Cases_on `word_msb iw` >> simp[] >> rw[] >> gvs[]) >>
  `eval_operand dst q = SOME (b + n2w j)` by
    (qpat_x_assum `eval_operand dst q = _` mp_tac >>
     qpat_x_assum `type_memory_bytes cenv et = _` mp_tac >>
     qpat_x_assum `iw = n2w _` mp_tac >>
     pure_rewrite_tac[markerTheory.Abbrev_def] >>
     unabbrev_all_tac >> rpt (pop_assum kall_tac) >>
     Cases_on `bd` >> rpt strip_tac >>
     gvs[compileEnvTheory.elem_size_in_location_def,
         compileEnvTheory.is_slot_addressed_def, compileEnvTheory.word_scale_def,
         wordsTheory.word_mul_n2w, wordsTheory.word_add_n2w,
         wordsTheory.WORD_ADD_ASSOC] >>
     simp[GSYM wordsTheory.word_add_n2w, wordsTheory.WORD_ADD_ASSOC] >>
     simp[AC wordsTheory.WORD_ADD_ASSOC wordsTheory.WORD_ADD_COMM]) >>
  `vv_post ctx func cenv cx (Subscript et obj idx) es sa sd s0 ee (Value v)
     (LocatedValue et (mk_ptr dst LocMemory)) q` by
    (irule memory_value_array_element_post >> simp[] >>
     goal_assum (drule_at Any) >>
     goal_assum (drule_at (Pat `array_index _ _ _ = _`)) >>
     goal_assum (drule_at (Pat `eval_operand dst q = _`)) >>
     qpat_x_assum `i = _` kall_tac >>
     qpat_x_assum `iw = _` kall_tac >>
     qpat_x_assum `w2n (b + n2w j) = _` mp_tac >>
     simp[Abbr `j`]) >>
  qpat_x_assum `i = _` kall_tac >> qpat_x_assum `iw = _` kall_tac >>
  `select_result cx (ArrayT et bd) (Value (ArrayV av)) (ValueSubscript (IntV i)) ee =
    (INL (Value v),ee)` by
    simp[select_result_def, bind_def, lift_option_type_def, lift_sum_def,
         return_def, raise_def, vyperStateTheory.evaluate_subscripts_def] >>
  `ee with gas_obs := [] = ee` by simp[vyperStateTheory.evaluation_state_component_equality] >>
  irule select_result_counted_summary >> simp[] >>
  goal_assum (drule_at (Pat `gas_marked_path _ _ _ _ _ _`)) >> simp[]
QED

Finalise live_memory_value_array_suffix_summary
