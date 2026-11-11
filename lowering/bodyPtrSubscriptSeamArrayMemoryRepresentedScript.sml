Theory bodyPtrSubscriptSeamArrayMemoryRepresented
Ancestors
  bodyPtrSubscriptSeamArrayMemoryCompose exprSimVVFrame exprSimWordArgs
  exprSimHash exprSimProps exprSimSubscriptArrayFrame loweringPosts
  compileEnv venomState context finite_map
  exprSimSubscriptArraySuffix exprSimSubscriptArrayFramed
  bodyPtrSubscriptSeamArrayMemoryTyping bodyPtrSubscriptSeamArrayMemorySuffix
  bodyPtrDefs bodyPtrSubscriptSeamArrayMemoryEndpoint vyperArray
  assignBasePtrBoundary bodyPtrEnvBuiltinsEdges appendStorageGhostPtr
  exprSimCopy exprLoweringProps exprSimSubscriptArrayEndpoint

Theorem memory_vv_post_readonly_tail:
  vv_post ctx func cenv cx e es sa sc s0 ee r (LocatedValue ann p) s /\
  post_value_type cenv e = expr_type e /\ p.ptr_location = LocMemory /\
  local_ptrs_reserved cenv sa /\ sa.cs_next_var <= sc.cs_next_var /\
  sc.cs_next_id <= sd.cs_next_id /\
  eval_operand p.ptr_operand z = eval_operand p.ptr_operand s /\
  (!x w. not_fresh_at sc x /\ lookup_var x s = SOME w ==> lookup_var x z = SOME w) /\
  (!name b sz. local_region cenv ee.scopes s name b sz <=>
               local_region cenv ee.scopes z name b sz) /\
  z.vs_allocas = s.vs_allocas /\ z.vs_memory = s.vs_memory /\
  contract_storage z = contract_storage s /\ contract_transient z = contract_transient s /\
  stmt_state_rel ctx func cenv cx ee z ==>
  vv_post ctx func cenv cx e es sa sd s0 ee r (LocatedValue ann p) z
Proof
  strip_tac >>
  `wb_frame cenv es ee sa s0 s` by
    (gvs[vv_post_def, wb_frame_def] >> metis_tac[]) >>
  `wb_frame cenv es ee sa s0 z` by
    (irule wb_frame_readonly_tail >> goal_assum (drule_at Any) >> metis_tac[]) >>
  `vv_holds cenv cx (expr_type e) r (LocatedValue ann p) ee z` by
    (irule vv_holds_vars_frame >> qexists_tac `s` >>
     gvs[vv_post_def, vv_operand_def]) >>
  `vv_at cenv cx (expr_type e) sa sd ee r (LocatedValue ann p) z` by
    (irule vv_at_vars_frame >> qexistsl_tac [`s`,`sc`] >>
     gvs[vv_post_def, vv_operand_def]) >>
  irule vv_post_frame_intro >> simp[vv_storage_live_def]
QED

Theorem nonnegative_index_word:
  !sgn (w:bytes32) i.
    i = (if sgn then w2i w else &(w2n w)) /\ 0 <= i ==>
    w = n2w (Num i)
Proof
  Cases >> simp[] >> rpt strip_tac >> gvs[] >>
  gvs[integer_wordTheory.w2i_def] >>
  Cases_on `word_msb w` >> gvs[]
QED
Theorem array_lowered_value_type:
  expr_body_pre cenv cx env e es /\ expr_type e = ArrayT et bd /\
  post_value_type cenv e = expr_type e ==>
  lowered_value_type cenv e = expr_type e
Proof
  Cases_on `e` >>
  gvs[vyperASTTheory.expr_type_def, exprLoweringTheory.lowered_value_type_def]
  >~ [`Builtin t b l`] >- (Cases_on `b` >>
    gvs[exprLoweringTheory.lowered_value_type_def,
        exprLoweringTheory.concat_buffer_type_def, vyperASTTheory.expr_type_def] >>
    gvs[exprSimHypsDefsTheory.expr_body_pre_def,
        Once vyperTypeSystemTheory.well_typed_expr_def,
        vyperTypeSystemTheory.well_typed_builtin_app_def])
  >~ [`TypeBuiltin t t0 t1 l`] >- (Cases_on `t0` >>
    gvs[exprLoweringTheory.lowered_value_type_def, vyperASTTheory.expr_type_def] >>
    gvs[exprSimHypsDefsTheory.expr_body_pre_def,
        Once vyperTypeSystemTheory.well_typed_expr_def,
        vyperTypeSystemTheory.type_builtin_result_ok_def]) >>
  Cases_on `c` >> gvs[exprLoweringTheory.lowered_value_type_def,
    post_value_type_def, is_word_type_def, is_bytestring_type_def,
    vyperASTTheory.expr_type_def] >> rpt strip_tac >>
  gvs[is_word_type_def, is_bytestring_type_def]
QED


Theorem fixed_array_represented_summary_ptr:
  expr_body_pre cenv cx env (Subscript et obj idx) es /\
  expr_type obj = ArrayT et (Fixed n) /\ post_value_type cenv obj = expr_type obj /\
  eval_expr cx obj es = (INL r,t) /\
  (!tr slot vt. r <> PlaceR (StoragePlace tr slot vt)) /\
  ee.scopes = t.scopes /\ ee.immutables = t.immutables /\ ee.gas_obs = [] /\
  vv_post ctx func cenv cx obj es sa sc s0 ee r
    (LocatedValue (ArrayT et (Fixed n)) p) q /\
  ptr_vv_ok cx (ArrayT et (Fixed n)) r (LocatedValue (ArrayT et (Fixed n)) p) ee G tn q /\
  ptr_buf_ok cenv obj p.ptr_operand G q /\ p.ptr_location = LocMemory /\
  eval_operand iop q = SOME iw /\
  i = (if is_signed_type (expr_type idx) then w2i iw else &(w2n iw)) /\
  op_taint tn iop = {} /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sc x) /\ (!l. p.ptr_operand <> Label l) /\
  (!x. iop = Var x ==> not_fresh_at sc x) /\ (!l. iop <> Label l) /\
  compile_array_subscript p.ptr_operand iop F n ws (elem_size_in_location cenv LocMemory et)
    (is_signed_type (expr_type idx)) loader sc = (dst,sd) /\
  fn_has_code sc sd func /\ ~ctx_has_dalloca ctx /\ ~q.vs_halted /\
  q.vs_current_bb = sc.cs_current_bb /\ q.vs_inst_idx = LENGTH sc.cs_current_insts /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sc /\ ci_mono sa sc /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sc x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sc x) /\
  ghost_inv d cenv cx ee G tn q /\ ghost_kept cenv es sa G0 tn0 s0 G tn ==>
  gas_summary_ptr_at (cx_dead cx) (ctx,func) PG []
    (select_result cx (ArrayT et (Fixed n)) r (ValueSubscript (IntV i))) (ee,q,G,tn)
    (\res ee' H tm z. ?child. res = INL child /\
      vv_post ctx func cenv cx (Subscript et obj idx) es sa sd s0 ee' child
        (LocatedValue et (mk_ptr dst LocMemory)) z /\
      z.vs_current_bb = sd.cs_current_bb /\ z.vs_inst_idx = LENGTH sd.cs_current_insts /\
      ghost_inv d cenv cx ee' H tm z /\
      ptr_vv_ok cx et child (LocatedValue et (mk_ptr dst LocMemory)) ee' H tm z /\
      ptr_buf_ok cenv (Subscript et obj idx) dst H z /\
      ghost_kept cenv es sa G0 tn0 s0 H tm)
    (\res ee' gt outcome. expr_exit res outcome)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `expr_body_pre cenv cx env obj es` by
    metis_tac[exprSimSubscriptArraySourceTheory.expr_body_pre_array_subscript_base] >>
  drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`) framed_array_post_view >>
  disch_then (qspecl_then [`t`,`env`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `array_length (ArrayTV etv (Fixed n)) av = n` by
    (Cases_on `av` >> gvs[vyperTypingTheory.value_has_type_def,
                        vyperValueOperationTheory.array_length_def]) >>
  Cases_on `valid_index (ArrayTV etv (Fixed n)) av i`
  >- suspend "valid" >>
  `~((is_signed_type (expr_type idx) ==> 0 <= w2i iw) /\
      w2n iw < w2n (n2w n:bytes32))` by
    (drule_all array_index_word_bounds >>
     Cases_on `is_signed_type (expr_type idx)` >>
     simp[exprSimArrayIndexTheory.idx_in_range_def, integer_wordTheory.WORD_LTi,
          integer_wordTheory.word_0_w2i] >> intLib.COOPER_TAC) >>
  drule_all fixed_array_rejected_summary_ptr >> simp[]
QED

Resume fixed_array_represented_summary_ptr[valid]:
  drule_all array_subscript_memory_layout >> strip_tac >>
  `0 <= i` by gvs[vyperArrayTheory.valid_index_def] >>
  `iw = n2w (Num i)` by metis_tac[nonnegative_index_word] >>
  drule array_index_valid >>
  pure_rewrite_tac[optionTheory.IS_SOME_EXISTS] >> strip_tac >>
  rename1 `array_index (ArrayTV etv (Fixed n)) av i = SOME v` >>
  `well_formed_type_value etv` by
    metis_tac[vyperTypingTheory.evaluate_type_well_formed] >>
  `value_has_type etv v` by
    metis_tac[vyperAssignPreservesTypeTheory.array_index_has_type] >>
  `val_wf etv v` by
    metis_tac[valueTypingMemoryPropsTheory.value_has_type_memory_wf] >>
  `w2n w + val_footprint (ArrayTV etv (Fixed n)) (ArrayV av) < dimword (:256)` by
    (irule vv_post_memory_footprint_bound >>
     goal_assum (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`)) >> simp[]) >>
  drule_all fixed_array_child_bounds >> strip_tac >>
  `0 < type_memory_size (ArrayTV etv (Fixed n))` by
    (irule (cj 1 valueEncodingPropsTheory.type_memory_size_pos) >>
     qpat_x_assum `evaluate_type _ (ArrayT _ _) = _` mp_tac >>
     simp[Once vyperValueTheory.evaluate_type_def, AllCaseEqs()] >>
     rpt strip_tac >> simp[vyperValueTheory.type_slot_size_def]) >>
  `type_memory_bytes cenv (lowered_value_type cenv obj) =
     type_memory_size (ArrayTV etv (Fixed n))` by
    (`lowered_value_type cenv obj = expr_type obj` by
       (irule array_lowered_value_type >> metis_tac[]) >> simp[]) >>
  `op_taint tn p.ptr_operand = {}` by gvs[ptr_vv_ok_def] >>
  `?base. p.ptr_operand = Var base /\
     ptr_covers G tn base q (type_memory_size (ArrayTV etv (Fixed n)))` by
    (irule assignBasePtrBoundaryTheory.ptr_buf_ok_read_covers >> simp[] >>
     qexistsl_tac [`cenv`,`obj`] >> simp[]) >>
  `((is_signed_type (expr_type idx) ==> 0 <= w2i (n2w (Num i):bytes32)) /\
     w2n (n2w (Num i):bytes32) < w2n (n2w n:bytes32))` by
    (drule_all array_index_word_bounds >>
     qpat_x_assum `iw = _` SUBST_ALL_TAC >>
     qpat_x_assum `array_length _ _ = n` SUBST_ALL_TAC >>
     qpat_x_assum `valid_index _ _ _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     Cases_on `is_signed_type (expr_type idx)` >>
     simp[exprSimArrayIndexTheory.idx_in_range_def, integer_wordTheory.WORD_LTi,
          integer_wordTheory.word_0_w2i] >> intLib.COOPER_TAC) >>
  suspend "run"

QED

Resume fixed_array_represented_summary_ptr[run]:
  `compile_array_subscript (Var base') iop F n ws (type_memory_size etv)
     (is_signed_type (expr_type idx)) loader sc = (dst,sd)` by metis_tac[] >>
  `not_fresh_at sc base' /\ lookup_var base' q = SOME w` by
    metis_tac[venomStateTheory.eval_operand_def] >>
  `eval_operand iop q = SOME (n2w (Num i))` by metis_tac[] >>
  drule_all static_selector_counted >>
  disch_then (qspecl_then [`PG`,`cx_dead cx`] strip_assume_tac) >>
  `stmt_state_rel ctx func cenv cx ee q` by metis_tac[vv_post_def] >>
  `stmt_state_rel ctx func cenv cx ee sf` by metis_tac[] >>
  `ghost_inv d cenv cx ee Gf tnf sf` by
    (irule ghost_inv_register_transport >> goal_assum (drule_at Any) >> simp[] >>
     qexists_tac `sc` >> simp[] >> metis_tac[]) >>
  `ghost_kept cenv es sa G0 tn0 s0 Gf tnf` by
    (irule ghost_kept_suffix_compose >> goal_assum (drule_at Any) >>
     qexists_tac `sc` >> simp[] >> metis_tac[ci_mono_def]) >>
  suspend "endpoint"
QED

Resume fixed_array_represented_summary_ptr[endpoint]:
  `compile_array_subscript p.ptr_operand iop F n ws
     (elem_size_in_location cenv LocMemory et) (is_signed_type (expr_type idx))
     (compile_ptr_load cenv.ce_is_ctor cenv.ce_imm_alloca LocMemory) sc = (dst,sd)` by
    (qpat_x_assum `compile_array_subscript p.ptr_operand _ _ _ _ _ _ _ _ = _` mp_tac >>
     simp[exprLoweringTheory.compile_array_subscript_def]) >>
  `sc.cs_next_id <= sd.cs_next_id` by
    (`ci_mono sc sd` suffices_by simp[exprLoweringPropsTheory.ci_mono_def] >>
     qpat_x_assum `compile_array_subscript _ _ _ _ _ _ _ _ sc = _`
       (SUBST1_TAC o SYM o PURE_REWRITE_RULE [pairTheory.SND] o Q.AP_TERM `SND`) >>
     irule exprLoweringPropsTheory.ci_mono_compile_array_subscript >>
     simp[exprLoweringPropsTheory.ci_mono_compile_ptr_load]) >>
  `eval_operand p.ptr_operand sf = SOME w` by
    metis_tac[venomStateTheory.eval_operand_def] >>
  `!name b sz. local_region cenv ee.scopes q name b sz <=>
               local_region cenv ee.scopes sf name b sz` by
    (rpt gen_tac >> irule (GSYM copy_buffer_local_region_frame) >>
     qexists_tac `sc` >> simp[] >> metis_tac[]) >>
  `vv_post ctx func cenv cx obj es sa sd s0 ee r
     (LocatedValue (ArrayT et (Fixed n)) p) sf` by
    (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _`) memory_vv_post_readonly_tail >>
     disch_then (qspecl_then [`sf`,`sd`] mp_tac) >>
     simp[] >> metis_tac[ci_mono_def, venomStateTheory.contract_storage_def,
                         venomStateTheory.contract_transient_def]) >>
  `eval_operand (Var out) sf = SOME (w + n2w (Num i * type_memory_size etv))` by
    metis_tac[venomStateTheory.eval_operand_def] >>
  qpat_x_assum `vv_post _ _ _ _ _ _ sa sc _ _ _ _ _` kall_tac >>
  `type_memory_bytes cenv (lowered_value_type cenv (Subscript et obj idx)) <=
     type_memory_size etv` by simp[] >>
  drule_all fixed_array_element_summary_ptr >>
  qpat_x_assum `dst = Var out` SUBST_ALL_TAC >>
  rpt (pop_assum kall_tac) >> simp[]
QED

Finalise fixed_array_represented_summary_ptr
