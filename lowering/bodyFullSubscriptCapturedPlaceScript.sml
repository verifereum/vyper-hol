Theory bodyFullSubscriptCapturedPlace
Ancestors exprLowering[qualified,ignore_grammar]
  exprSimHypsDefs allocLimits targetOverlapAccess vyperLocalAccessFrame
  vyperSubscriptOverlap loweringPosts valueEncodingProps
  loweringStateRelDefs exprSimProps vyperInterpreter vyperState context
  venomExecSemantics words exprBopSimProps vyperMisc exprSimExtract32Post
  exprSimSubscriptArraySource exprSimSource vyperPlaceTyping
  bodyPtrDefs logValueFramePtr typedCopyLayoutPtr vyperArray valueEncoding
  bodyFullTargetArraySuffix exprSimSubscriptArraySuffix exprOperandVar
  exprLoweringProps exprSimArrayIndex freshWrites fragExec emitHelperProps
  emitHelper fragGasOriginPtr compileEnv list venomState
  exprSimSubscriptArrayFramed stateRelProj vyperEvalExprPreservesScopesDom
  bodyPtrSignedConvertSourceFrame exprSimHash exprSimWordArgs
  bodyFullTargetAttribute[qualified,ignore_grammar]
  bodyFullHashKeccakFixed[qualified,ignore_grammar]
  bodyFullUnwrapRun[qualified,ignore_grammar] wordArgsPtr[qualified,ignore_grammar]
  gasOutcomeFullCompose vyperStorageFootprint exprSimDefs

(* The allocation check rejects writes to the root of a popped array
   before the index is evaluated.  Preserve the entry, including its
   popped history, rather than requiring the captured path to be live. *)
Theorem subscript_pop_local_frame[local]:
  expr_body_pre cenv cx env (Subscript ty obj idx) es /\
  eval_expr cx obj es = (INL (PlaceR (MemoryPlace id path)),mid) /\
  is_ArrayT (expr_type obj) /\ base_from_pop obj /\
  eval_expr cx idx (mid with gas_obs := gs) = (res,fin) ==>
  lookup_scopes id fin.scopes = lookup_scopes id mid.scopes
Proof
  strip_tac >>
  `!mods accs. MEM (ReadAcc (LocalRef id)) accs ==>
     MEM (LocalRef id) (nonconstant_reads mods accs)` by
    (recInduct nonconstant_reads_ind >> rw[nonconstant_reads_def] >>
     rpt (CASE_TAC >> gvs[]) >> metis_tac[]) >>
  `MEM (LocalRef id)
     (nonconstant_reads cenv.ce_modules (expr_accesses cenv.ce_modules obj))` by
    (first_x_assum irule >> simp[expr_accesses_def] >>
     metis_tac[eval_expr_memory_access]) >>
  `~MEM (WriteAcc (LocalRef id)) (accesses_expr idx)` suffices_by
    (strip_tac >>
     qpat_assum `eval_expr _ idx _ = _`
       (mp_then Any mp_tac eval_expr_unwritten_local) >>
     simp[]) >>
  strip_tac >>
  `pop_subscript_overlap cenv.ce_modules obj idx` by
    (simp[pop_subscript_overlap_def, any_written_MEM] >>
     conj_tac >- (strip_tac >> gvs[]) >>
     disj1_tac >> qexists `LocalRef id` >> simp[expr_accesses_def]) >>
  gvs[expr_body_pre_def, alloc_limits_expr_def]
QED

Theorem captured_place_window[local]:
  vv_at ce cx ty sa sm mid (PlaceR (MemoryPlace id path)) (LocatedValue t p) s /\
  p.ptr_location = LocMemory /\ eval_operand p.ptr_operand s = SOME w /\
  read_result cx (PlaceR (MemoryPlace id path)) mid = (INL v,mid) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  expr_post H ctx fn ce cx idx mid sm sn s fin key op u /\
  lookup_scopes id fin.scopes = lookup_scopes id mid.scopes ==>
  val_wf tv v /\
  mem_bytes_at (w2n w) (val_footprint tv v) u.vs_memory =
  mem_bytes_at (w2n w) (val_footprint tv v) s.vs_memory
Proof
  strip_tac >>
  qpat_x_assum `vv_at _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [vv_at_def]) >> simp[] >>
  strip_tac >> simp[]
  >- (`mem_bytes_at b sz u.vs_memory = mem_bytes_at b sz s.vs_memory` by
        (fs[expr_post_def] >> metis_tac[]) >>
      drule mem_bytes_at_translated_window >>
      disch_then (qspecl_then [`w2n w - b`, `val_footprint tv v`] mp_tac) >>
      `b + (w2n w - b) = w2n w` by decide_tac >>
      simp[] >> decide_tac)
  >- (gvs[local_place_at_def] >>
      `mem_bytes_at b sz u.vs_memory = mem_bytes_at b sz s.vs_memory` by
        (fs[expr_post_def, locals_kept_def] >> metis_tac[]) >>
      drule mem_bytes_at_translated_window >>
      disch_then (qspecl_then [`w2n w - b`, `val_footprint tv v`] mp_tac) >>
      `b + (w2n w - b) = w2n w` by decide_tac >>
      simp[] >> decide_tac) >>
  simp[valueEncodingDefsTheory.mem_bytes_at_def]
QED

Theorem subscript_array_window_taint[local]:
  vv_at ce cx ty sa sm mid raw (LocatedValue t p) s /\
  p.ptr_location = LocMemory /\ eval_operand p.ptr_operand s = SOME w /\
  read_result cx raw mid = (INL v,mid) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  ghost_kept_at lo ce (mid with gas_obs := gs) sm G tn s G' tn' /\
  w2n w <= i /\ i < w2n w + val_footprint tv v /\ i IN tn'.t_mem ==>
  i IN tn.t_mem
Proof
  strip_tac >>
  qpat_x_assum `vv_at _ _ _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [vv_at_def]) >> simp[] >> strip_tac >>
  fs[ghost_kept_at_def]
  >- (`b <= i /\ i < b + sz` by decide_tac >> metis_tac[])
  >- (`b <= i /\ i < b + sz` by decide_tac >> metis_tac[]) >>
  decide_tac
QED

Theorem captured_ptr_vv_footprint_frame[local]:
  ptr_vv_ok cx ty raw (LocatedValue t p) mid G tn s /\
  p.ptr_location = LocMemory /\
  read_result cx raw mid = (INL v,mid) /\
  read_result cx raw fin = (INL v,fin) /\
  eval_operand p.ptr_operand s = SOME w /\
  eval_operand p.ptr_operand u = SOME w /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  val_wf tv v /\
  mem_bytes_at (w2n w) (val_footprint tv v) u.vs_memory =
  mem_bytes_at (w2n w) (val_footprint tv v) s.vs_memory /\
  (!i. w2n w <= i /\ i < w2n w + val_footprint tv v /\ i IN tn'.t_mem ==>
       i IN tn.t_mem) /\
  ghost_kept_at lo ce (mid with gas_obs := gs) sm G tn s G' tn' /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sm x) ==>
  ptr_vv_ok cx ty raw (LocatedValue t p) fin G' tn' u
Proof
  strip_tac >> fs[ptr_vv_ok_def,ptr_mem_ok_def] >>
  conj_tac
  >- (Cases_on `p.ptr_operand` >> gvs[ptrDisciplineTheory.op_taint_def,ghost_kept_at_def] >>
      metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >> irule robust_val_in_memory_footprint_frame >>
      conj_tac >- simp[] >>
      qexistsl [`s.vs_memory`, `u.vs_memory`, `tn.t_mem`, `tn'.t_mem`] >> simp[]) >>
  strip_tac >>
  gvs[ghost_kept_at_def] >> metis_tac[]
QED

(* The two child posts suffice to carry a captured memory place across
   the index. No lookup in the live array value is required. *)
Theorem subscript_captured_pop_transport:
  expr_body_pre ce cx env (Subscript ty obj idx) es /\
  eval_expr cx obj es = (INL (PlaceR (MemoryPlace id path)),mid) /\
  expr_type obj = ArrayT et bd /\ base_from_pop obj /\
  post_value_type ce obj = expr_type obj /\
  bind (eval_expr cx idx) (read_result cx) (mid with gas_obs := gs) = (INL key,fin) /\
  vv_post H ctx fn ce cx obj es sa sm s0 mid
    (PlaceR (MemoryPlace id path)) (LocatedValue t p) s /\
  expr_post H ctx fn ce cx idx (mid with gas_obs := gs) sm sn s fin key op u /\
  local_ptrs_reserved ce sm /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sm x) /\
  (!l. p.ptr_operand <> Label l) /\
  evaluate_type (get_tenv cx) (post_value_type ce obj) = SOME tv /\
  ptr_vv_ok cx (post_value_type ce obj) (PlaceR (MemoryPlace id path))
    (LocatedValue t p) mid G tn s /\
  ghost_kept_at lo ce (mid with gas_obs := gs) sm G tn s G' tn' ==>
  ptr_vv_ok cx (post_value_type ce obj) (PlaceR (MemoryPlace id path))
    (LocatedValue t p) fin G' tn' u /\
  runtime_place_typed cx fin (MemoryPlace id path) tv /\
  popped_keys_indexed fin.scopes /\
  p.ptr_location = LocMemory /\
  vv_place_ptr ce cx fin u (PlaceR (MemoryPlace id path)) (LocatedValue t p) /\
  ?w v. eval_operand p.ptr_operand s = SOME w /\
        eval_operand p.ptr_operand u = SOME w /\
        place_ptr_rel ce cx u (PlaceR (MemoryPlace id path)) w
          (SOME LocMemory) (Type (expr_type obj)) /\
        read_result cx (PlaceR (MemoryPlace id path)) mid = (INL v,mid) /\
        read_result cx (PlaceR (MemoryPlace id path)) fin = (INL v,fin) /\
        val_wf tv v /\
        val_in_memory tv v (w2n w) u.vs_memory /\
        mem_bytes_at (w2n w) (val_footprint tv v) u.vs_memory =
        mem_bytes_at (w2n w) (val_footprint tv v) s.vs_memory
Proof
  strip_tac >>
  fs[extract32_expr_post_start_gas_obs] >>
  `expr_body_pre ce cx env obj es` by
    metis_tac[expr_body_pre_array_subscript_base, base_from_pop_not_array_slot_base] >>
  drule_all_then assume_tac expr_body_pre_array_subscript_index_after_base >>
  drule_all_then strip_assume_tac expr_body_pre_place_metadata >>
  `?ir. eval_expr cx idx (mid with gas_obs := gs) = (INL ir,fin)` by
    (qpat_x_assum `bind _ _ _ = _` mp_tac >>
     Cases_on `eval_expr cx idx (mid with gas_obs := gs)` >> Cases_on `q` >>
     simp[bind_def] >> metis_tac[read_result_state]) >>
  `lookup_scopes id fin.scopes = lookup_scopes id mid.scopes` by
    (`is_ArrayT (expr_type obj)` by simp[] >>
     drule_all subscript_pop_local_frame >> simp[]) >>
  `runtime_place_typed cx fin (MemoryPlace id path) tv` by
    gvs[runtime_place_typed_memory] >>
  `popped_keys_indexed fin.scopes` by
    (irule expr_body_pre_popped_keys_indexed >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  fs[vv_post_def] >>
  `p.ptr_location = LocMemory` by fs[vv_place_ptr_def] >>
  fs[vv_holds_def] >>
  `eval_operand p.ptr_operand u = SOME w` by
    (irule eval_operand_frame >> conj_tac >- simp[] >> qexistsl [`sm`,`s`] >>
     fs[expr_post_def]) >>
  `vv_place_ptr ce cx fin u (PlaceR (MemoryPlace id path)) (LocatedValue t p)` by
    (fs[vv_place_ptr_def, local_ptrs_reserved_def, expr_post_def] >>
     qexists `b` >> gvs[] >>
     `not_fresh_at sm q` by
       (qpat_assum `!n1 n2 q sz1 sz2. _` (qspecl_then
         [`id`,`id`,`q`,`sz`,`sz`] mp_tac) >> simp[]) >>
     first_x_assum irule >> simp[]) >>
  `place_ptr_rel ce cx u (PlaceR (MemoryPlace id path)) w
     (SOME LocMemory) (Type (expr_type obj))` by
    (`expr_sim_inv ce cx env mid` by fs[expr_body_pre_def] >>
     qpat_assum `vv_place_ptr _ _ fin _ _ _`
       (mp_tac o REWRITE_RULE [vv_place_ptr_def]) >> simp[] >> strip_tac >>
     fs[runtime_place_typed_memory] >>
     `tv0 = entry.type` by
       (fs[expr_sim_inv_def, vyperTypeInvariantsTheory.env_consistent_def,
           vyperTypeInvariantsTheory.env_scopes_consistent_def] >>
        qpat_x_assum `!id entry. lookup_scopes id mid.scopes = SOME entry ==> _` drule >>
        disch_then (strip_assume_tac o REWRITE_RULE [optionTheory.IS_SOME_EXISTS]) >>
        qpat_x_assum `!id ty. FLOOKUP env.var_types id = SOME ty ==> ce.ce_var_type id = SOME ty` drule >>
        strip_tac >> gvs[] >>
        qpat_x_assum `!id ty entry. _ /\ lookup_scopes id mid.scopes = SOME entry ==> _` drule_all >>
        simp[]) >>
     `tvk = tv` by metis_tac[mem_path_offset_sound, optionTheory.SOME_11] >>
     simp[place_ptr_rel_def] >> metis_tac[]) >>
  `read_result cx (PlaceR (MemoryPlace id path)) fin = (INL v,fin)` by
    (qpat_x_assum `read_result _ _ mid = _` mp_tac >>
     Cases_on `lookup_scopes id mid.scopes` >>
     simp[read_result_def, read_place_def, get_scopes_def, bind_def,
          lift_option_type_def, lift_sum_def, return_def, raise_def] >>
     Cases_on `read_memory_path x path` >> simp[return_def, raise_def]) >>
  drule_all captured_place_window >> strip_tac >>
  `!i. w2n w <= i /\ i < w2n w + val_footprint tv v /\ i IN tn'.t_mem ==>
       i IN tn.t_mem` by
    (rpt strip_tac >> drule_all subscript_array_window_taint >> simp[]) >>
  drule_all_then assume_tac captured_ptr_vv_footprint_frame >>
  `val_in_memory tv v (w2n w) u.vs_memory` by
    (irule val_in_memory_footprint_agree >> conj_tac >- simp[] >>
     qexists `s.vs_memory` >> simp[]) >>
  gvs[]
QED

(* A fixed array's selected element inherits its memory representation and
   capacity from the captured base pointer, not from the root's live value. *)
Theorem subscript_captured_fixed_child:
  runtime_place_typed cx es (MemoryPlace id path) (ArrayTV etv (Fixed n)) /\
  popped_keys_indexed es.scopes /\
  read_result cx (PlaceR (MemoryPlace id path)) es =
    (INL (ArrayV (SArrayV kvs)),es) /\
  array_index (ArrayTV etv (Fixed n)) (SArrayV kvs) i = SOME v /\
  evaluate_type (get_tenv cx) (ArrayT et (Fixed n)) = SOME (ArrayTV etv (Fixed n)) /\
  evaluate_type (get_tenv cx) et = SOME etv /\ val_wf etv v /\
  p.ptr_location = LocMemory /\ eval_operand p.ptr_operand s = SOME w /\
  ptr_vv_ok cx (ArrayT et (Fixed n)) (PlaceR (MemoryPlace id path))
    (LocatedValue t p) es G tn s /\
  j = Num i * type_memory_size etv /\ eval_operand dst u = SOME (w + n2w j) /\
  w2n (w + n2w j) = w2n w + j /\
  op_taint tn' dst = {} /\ op_prov G' dst = op_prov G p.ptr_operand /\
  tn'.t_mem = tn.t_mem /\ u.vs_memory = s.vs_memory /\
  place_ptr_rel ce cx s (PlaceR (MemoryPlace id path)) w
    (SOME LocMemory) (Type (ArrayT et (Fixed n))) /\
  (!q sz b. FLOOKUP ce.ce_vars id = SOME (PtrVar (Var q) sz) /\
     lookup_var q s = SOME b ==> lookup_var q u = SOME b) ==>
  select_result cx ty (PlaceR (MemoryPlace id path)) (ValueSubscript (IntV i)) es =
    (INL (PlaceR (MemoryPlace id (path ++ [ValueSubscript (IntV i)]))),es) /\
  vv_place_ptr ce cx es u (PlaceR (MemoryPlace id (path ++ [ValueSubscript (IntV i)])))
    (LocatedValue et (mk_ptr dst LocMemory)) /\
  ptr_vv_ok cx et (PlaceR (MemoryPlace id (path ++ [ValueSubscript (IntV i)])))
    (LocatedValue et (mk_ptr dst LocMemory)) es G' tn' u
Proof
  strip_tac >>
  `evaluate_subscripts (ArrayTV etv (Fixed n)) (ArrayV (SArrayV kvs))
     [ValueSubscript (IntV i)] = INL v` by simp[evaluate_array_subscript_result] >>
  drule_all select_fixed_memory_read >> strip_tac >>
  `0 <= i /\ Num i < n /\
    v = (case ALOOKUP kvs (Num i) of NONE => default_value etv | SOME x => x)` by
    (Cases_on `0 <= i /\ Num i < n` >> fs[array_index_sarray] >>
     Cases_on `ALOOKUP kvs (Num i)` >> gvs[]) >>
  conj_tac >- simp[] >>
  conj_tac
  >- (fs[place_ptr_rel_def] >>
      `mem_step_offset (ArrayTV etv (Fixed n)) (ValueSubscript (IntV i)) =
         SOME (j,etv)` by simp[mem_step_offset_def] >>
      `tv = ArrayTV etv (Fixed n)` by metis_tac[optionTheory.SOME_11] >>
      `mem_path_offset tv0 (path ++ [ValueSubscript (IntV i)]) = SOME (k+j,etv)` by
        metis_tac[mem_path_offset_snoc] >>
      rename1 `FLOOKUP ce.ce_vars id = SOME (PtrVar (Var root) sz)` >>
      `lookup_var root u = SOME b` by metis_tac[] >>
      simp[vv_place_ptr_def,contextTheory.mk_ptr_def] >>
      simp[GSYM word_add_n2w, WORD_ADD_ASSOC]) >>
  `ptr_mem_ok cx (ArrayT et (Fixed n)) (ArrayV (SArrayV kvs)) p.ptr_operand G tn s` by
    (qpat_assum `ptr_vv_ok _ _ _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE [ptr_vv_ok_def]) >> simp[]) >>
  qpat_x_assum `ptr_vv_ok _ _ _ _ _ _ _ _` kall_tac >>
  gvs[ptr_vv_ok_def,ptr_mem_ok_def,contextTheory.mk_ptr_def] >>
  conj_tac
  >- (rpt strip_tac >> irule sarray_in_memory_robust_element >> simp[] >>
      qexistsl [`n`,`kvs`,`s.vs_memory`,`tn`] >> simp[]) >>
  qmatch_goalsub_abbrev_tac `val_footprint etv child` >>
  rename1 `val_wf etv v` >> strip_tac >>
  `val_store_size etv v <= type_memory_size etv` by simp[val_store_size_le] >>
  `0 < type_memory_size etv` by metis_tac[val_footprint_le, arithmeticTheory.NOT_ZERO_LT_ZERO, arithmeticTheory.LESS_EQ_0] >>
  `Num i * type_memory_size etv + type_memory_size etv <= n * type_memory_size etv` by
    (`SUC (Num i) * type_memory_size etv <= n * type_memory_size etv` by
       simp[arithmeticTheory.LE_MULT_RCANCEL] >>
     pop_assum mp_tac >> pure_rewrite_tac[arithmeticTheory.MULT_CLAUSES] >> decide_tac) >>
  `n <> 0` by decide_tac >>
  qpat_x_assum `val_footprint (ArrayTV _ _) _ <> 0 ==> _`
    (mp_tac o SIMP_RULE (srw_ss()) [val_footprint_def,val_store_size_def,type_memory_size_def]) >>
  simp[] >> strip_tac >>
  Cases_on `dst` >> fs[ptrDisciplineTheory.op_prov_def] >> decide_tac
QED

Theorem captured_fixed_emission_cut[local]:
  compile_array_subscript bop iop F n ws esz sgn loader sn = (dst,sb) /\
  fn_has_code sn sb fn ==>
  ?sc. array_bounds_check iop (Lit (n2w n)) sgn sn = ((),sc) /\
    array_elem_ptr bop iop F ws esz sc = (dst,sb) /\
    same_blocks sn sc /\ same_blocks sc sb /\
    sc.cs_current_insts = sn.cs_current_insts ++ emitted_insts sn sc /\
    sb.cs_current_insts = sc.cs_current_insts ++ emitted_insts sc sb /\
    fn_has_code sn sc fn /\ fn_has_code sc sb fn /\
    EVERY (\ins. ins.inst_opcode <> INVOKE /\ ins.inst_opcode <> GAS /\
                 ~is_terminator ins.inst_opcode) (emitted_insts sn sc) /\
    EVERY (\ins. ins.inst_opcode <> INVOKE /\ ins.inst_opcode <> GAS /\
                 ~is_terminator ins.inst_opcode) (emitted_insts sc sb) /\
    EVERY (\ins. ins.inst_opcode <> ALLOCA) (emitted_insts sn sc) /\
    EVERY (\ins. ins.inst_opcode <> ALLOCA) (emitted_insts sc sb)
Proof
  simp[compile_array_subscript_split, comp_bind_def, comp_ignore_bind_def,
       comp_return_def] >> pairarg_tac >> simp[] >> strip_tac >>
  rename1 `array_bounds_check _ _ _ sn = (unit,sc)` >>
  Cases_on `unit` >> gvs[] >>
  `same_blocks sn sc /\
   sc.cs_current_insts = sn.cs_current_insts ++ emitted_insts sn sc /\
   EVERY (\ins. ins.inst_opcode <> INVOKE /\ ins.inst_opcode <> GAS /\
                 ~is_terminator ins.inst_opcode) (emitted_insts sn sc) /\
   EVERY (\ins. ins.inst_opcode <> ALLOCA) (emitted_insts sn sc)` by
    (qpat_x_assum `array_bounds_check _ _ _ _ = _` mp_tac >>
     simp[array_bounds_check_def, comp_bind_def] >> pairarg_tac >> simp[] >> strip_tac >>
     qpat_x_assum `array_bounds_valid _ _ _ _ = _` mp_tac >>
     simp[array_bounds_valid_def, comp_bind_def] >>
     Cases_on `sgn` >> simp[comp_return_def] >>
     rpt (pairarg_tac >> simp[]) >> strip_tac >>
     imp_res_tac emitted_insts_emit_op >> imp_res_tac emitted_insts_emit_void >>
     imp_res_tac emit_op_extends >> imp_res_tac emit_void_extends >>
     rpt (qpat_x_assum `_.cs_current_insts = _.cs_current_insts ++ emitted_insts _ _` kall_tac) >>
     gvs[same_blocks_def] >>
     simp[emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND, APPEND_ASSOC,
          venomInstTheory.mk_inst_def, venomInstTheory.is_terminator_def]) >>
  `same_blocks sc sb /\
   sb.cs_current_insts = sc.cs_current_insts ++ emitted_insts sc sb /\
   EVERY (\ins. ins.inst_opcode <> INVOKE /\ ins.inst_opcode <> GAS /\
                 ~is_terminator ins.inst_opcode) (emitted_insts sc sb) /\
   EVERY (\ins. ins.inst_opcode <> ALLOCA) (emitted_insts sc sb)` by
    (qpat_x_assum `sc.cs_current_insts = sn.cs_current_insts ++ _` kall_tac >>
     qpat_x_assum `array_elem_ptr _ _ _ _ _ _ = _` mp_tac >>
     simp[array_elem_ptr_def, comp_bind_def, comp_return_def] >>
     rpt (pairarg_tac >> simp[]) >> strip_tac >>
     imp_res_tac emit_op_extends >> imp_res_tac emitted_insts_emit_op >>
     rpt (qpat_x_assum `_.cs_current_insts = _.cs_current_insts ++ emitted_insts _ _` kall_tac) >>
     gvs[same_blocks_def] >>
     simp[emitted_insts_def, rich_listTheory.DROP_LENGTH_APPEND, APPEND_ASSOC,
          venomInstTheory.mk_inst_def, venomInstTheory.is_terminator_def]) >>
  `cs_extends sn sc /\ cs_extends sc sb` by
     fs[cs_extends_def, same_blocks_def, rich_listTheory.IS_PREFIX_APPEND] >>
  drule_all_then strip_assume_tac fn_has_code_split >>
  simp[]
QED


(* Keep the base ownership witness, changing the source endpoint only
   through the retained read and scope-domain frame. *)

Theorem captured_memory_vv_at_frame[local]:
  vv_at ce cx ty sa sm mid raw (LocatedValue t p) s /\
  p.ptr_location = LocMemory /\
  read_result cx raw mid = (INL v,mid) /\
  read_result cx raw fin = (INL v,fin) /\
  eval_operand p.ptr_operand q = eval_operand p.ptr_operand s /\
  (!aid a. FLOOKUP s.vs_allocas aid = SOME a ==> FLOOKUP q.vs_allocas aid = SOME a) /\
  (!n b sz. local_region ce fin.scopes q n b sz <=> local_region ce mid.scopes s n b sz) /\
  sm.cs_next_id <= sb.cs_next_id ==>
  vv_at ce cx ty sa sb fin raw (LocatedValue t p) q
Proof
  simp[vv_at_def] >> strip_tac >> rpt strip_tac >>
  qpat_x_assum `p.ptr_location = LocMemory ==> _` mp_tac >>
  simp[] >> strip_tac >>
  qexists `w` >> simp[]
  >- (disj1_tac >> qexistsl [`aid`,`b`,`sz`] >> simp[] >> first_assum ACCEPT_TAC) >>
  disj2_tac >> disj1_tac >> qexistsl [`n`,`b`,`sz`] >> simp[]
QED
(* Enter the fixed-array tail with the actual base and index child posts.
   The source place retained here is the one captured by the Pop. *)

(* The index and the address computation form a writeback frame from the
   captured base endpoint.  The selected place facts are already about q. *)
Theorem captured_fixed_post_join[local]:
  vv_post H ctx fn ce cx obj es sa sm s0 mid raw basevv s /\
  expr_post H ctx fn ce cx idx (mid with gas_obs := gs) sm sn s fin key iop u /\
  stmt_state_rel H ctx fn ce cx es s0 /\ local_ptrs_reserved ce sa /\
  MAP FDOM es.scopes = MAP FDOM mid.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  sm.cs_next_var <= sn.cs_next_var /\
  (q with <|vs_vars := u.vs_vars; vs_inst_idx := u.vs_inst_idx|>) = u /\
  (!x. not_fresh_at sn x ==> FLOOKUP q.vs_vars x = FLOOKUP u.vs_vars x) /\
  vv_holds ce cx et result (LocatedValue et (mk_ptr dst LocMemory)) fin q /\
  vv_at ce cx et sa sb fin result (LocatedValue et (mk_ptr dst LocMemory)) q /\
  vv_place_ptr ce cx fin q result (LocatedValue et (mk_ptr dst LocMemory)) ==>
  vv_post H ctx fn ce cx (Subscript et obj idx) es sa sb s0 fin
    result (LocatedValue et (mk_ptr dst LocMemory)) q
Proof
  strip_tac >>
  `q = u with <|vs_vars := q.vs_vars; vs_inst_idx := q.vs_inst_idx|>` by
    (qpat_assum `q with <|vs_vars := _; vs_inst_idx := _|> = u`
       (fn th => CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [GSYM th]))) >> simp[]) >>
  `!x w. not_fresh_at sn x /\ lookup_var x u = SOME w ==> lookup_var x q = SOME w` by
    simp[lookup_var_def] >>
  `local_ptrs_reserved ce sn` by
    (irule local_ptrs_reserved_next_var >> qexists `sa` >> simp[]) >>
  `stmt_state_rel H ctx fn ce cx fin q` by
    (irule stmt_state_rel_readonly_vars_pc >> qexistsl [`u`,`sn`] >> simp[] >>
     drule expr_post_state >> simp[]) >>
  `q.vs_memory = u.vs_memory /\ q.vs_allocas = u.vs_allocas` by
    (qpat_assum `q = u with <|vs_vars := _; vs_inst_idx := _|>`
       (fn th => once_rewrite_tac [th]) >> simp[]) >>
  `expr_post H ctx fn ce cx idx mid sm sn s fin key iop u` by
    (qpat_x_assum `expr_post H _ _ _ _ idx (mid with gas_obs := _) _ _ _ _ _ _ _` mp_tac >>
     rewrite_tac[extract32_expr_post_start_gas_obs]) >>
  `wb_frame ce es mid sa s0 s` by
    (fs[vv_post_def, wb_frame_def] >> first_assum ACCEPT_TAC) >>
  `wb_frame ce mid fin sm s q` by
    (irule wb_frame_readonly_tail >> qexistsl [`sn`,`u`] >> simp[] >>
     metis_tac[expr_post_frame]) >>
  `wb_frame ce es fin sa s0 q` by (drule_all wb_frame_trans >> simp[]) >>
  `~expr_has_effect obj /\ ~expr_has_effect idx ==> pure_frame ce fn es sa s0 q` by
    (strip_tac >>
     `pure_frame ce fn es sa s0 s` by fs[vv_post_def] >>
     `pure_frame ce fn mid sm s u` by (drule_all expr_post_pure_frame >> simp[]) >>
     `pure_frame ce fn mid sm s q` by
       (irule pure_frame_mem_tail >> qexists `u` >> simp[]) >>
     irule pure_frame_trans >> simp[] >> qexistsl [`mid`,`sm`,`s`] >>
     fs[wb_frame_def] >> metis_tac[]) >>
  `storage_well_formed_on cx fin (FST H)` by fs[expr_post_def] >>
  irule vv_post_frame_intro >>
  simp[vyperASTTheory.expr_type_def, expr_has_effect_thm, vv_storage_live_def] >>
  gvs[contextTheory.mk_ptr_def]
QED

Theorem captured_fixed_ghost_join[local]:
  stmt_state_rel (H:(bool # 256 word # type_value) list # num list)
    ctx fn ce cx es s0 /\ local_ptrs_reserved ce sa /\
  MAP FDOM es.scopes = MAP FDOM mid.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sm.cs_next_var <= sn.cs_next_var /\
  sa.cs_next_id <= sm.cs_next_id /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  ghost_kept_at lo ce es sa G0 tn0 s0 G tn /\
  ghost_kept_at lo ce (mid with gas_obs := gs) sm G tn s G' tn' /\
  ghost_inv_at D lo d ce cx fin G' tn' u /\
  wb_frame ce es mid sa s0 s /\
  (q with <|vs_vars := u.vs_vars; vs_inst_idx := u.vs_inst_idx|>) = u /\
  tnq.t_mem = tn'.t_mem /\ tnq.t_stor = tn'.t_stor /\
  tnq.t_trans = tn'.t_trans /\ tnq.t_imm = tn'.t_imm /\
  (!x. not_fresh_at sn x ==>
       FLOOKUP Gq x = FLOOKUP G' x /\ FLOOKUP tnq.t_var x = FLOOKUP tn'.t_var x /\
       FLOOKUP q.vs_vars x = FLOOKUP u.vs_vars x) ==>
  ghost_inv_at D lo d ce cx fin Gq tnq q /\
  ghost_kept_at lo ce es sa G0 tn0 s0 Gq tnq
Proof
  strip_tac >>
  `!x. not_fresh_at sa x ==> not_fresh_at sn x` by
    ((metis_tac[not_fresh_at_mono])) >>
  `q = u with <|vs_vars := q.vs_vars; vs_inst_idx := q.vs_inst_idx|>` by
    (qpat_assum `q with <|vs_vars := _; vs_inst_idx := _|> = u`
       (fn th => CONV_TAC (RAND_CONV (ONCE_REWRITE_CONV [GSYM th]))) >> simp[]) >>
  conj_tac
  >- (irule bodyFullTargetAttributeTheory.ghost_inv_at_fresh_write >>
      qexistsl [`G'`,`u`,`sa`,`tn'`] >>
      simp[ptrDisciplineTheory.op_taint_def, lookup_var_def] >>
      qpat_assum `q = u with <|vs_vars := _; vs_inst_idx := _|>`
        (fn th => once_rewrite_tac [th]) >> simp[]) >>
  `ghost_kept_at lo ce es sa G0 tn0 s0 G' tn'` by
    (irule (INST_TYPE [``:'b`` |-> ``:256``] wordArgsPtrTheory.ghost_kept_at_wb_trans) >>
     simp[] >> conj_tac >- (qexistsl [`H`,`ctx`,`cx`,`fn`] >> simp[]) >>
     qexistsl [`G`,`mid`,`mid with gas_obs := gs`,`s`,`sm`,`tn`] >> simp[]) >>
  irule bodyFullUnwrapRunTheory.ghost_kept_at_clean_suffix >>
  qexistsl [`G'`,`tn'`] >> simp[ptrDisciplineTheory.op_taint_def]
QED

Theorem captured_fixed_capacity[local]:
  base_from_pop obj /\ expr_type obj = ArrayT et (Fixed n) /\
  post_value_type ce obj = expr_type obj /\
  vv_store_bound cx (post_value_type ce obj) (lowered_value_type ce obj)
    mid raw (LocatedValue t p) s /\
  ptr_buf_ok ce obj p.ptr_operand G s /\ p.ptr_location = LocMemory /\
  expr_sim_inv ce cx env es /\
  evaluate_type (get_tenv cx) (ArrayT et (Fixed n)) = SOME (ArrayTV etv (Fixed n)) /\
  evaluate_type (get_tenv cx) et = SOME etv /\
  eval_operand p.ptr_operand s = SOME w /\
  eval_operand dst q = SOME (w + n2w (i * type_memory_size etv)) /\
  w2n (w + n2w (i * type_memory_size etv)) = w2n w + i * type_memory_size etv /\
  op_prov Gq dst = op_prov G p.ptr_operand /\
  i < n /\ s.vs_alloca_next <= q.vs_alloca_next /\
  vv_post H ctx fn ce cx (Subscript et obj idx) es sa sb s0 fin result
    (LocatedValue et (mk_ptr dst LocMemory)) q ==>
  vv_store_bound cx (post_value_type ce (Subscript et obj idx))
    (lowered_value_type ce (Subscript et obj idx)) fin result
    (LocatedValue et (mk_ptr dst LocMemory)) q /\
  ptr_buf_ok ce (Subscript et obj idx) dst Gq q
Proof
  strip_tac >>
  `lowered_value_type ce obj = expr_type obj` by
    ((qpat_assum `base_from_pop obj` mp_tac >> Cases_on `obj` >>
     simp[base_from_pop_def, exprLoweringTheory.lowered_value_type_def] >> (gvs[base_from_pop_def, exprLoweringTheory.lowered_value_type_def]))) >>
  `i * type_memory_size etv + type_memory_size etv <=
     type_memory_size (ArrayTV etv (Fixed n))` by
    (pure_rewrite_tac[type_memory_size_def] >>
     irule vyperLookupStorageTheory.array_index_element_end_bound >> simp[]) >>
  conj_tac
  >- (simp[exprLoweringTheory.lowered_value_type_def, vyperASTTheory.expr_type_def] >>
      drule exprSimMemDefsTheory.vv_store_bound_capacity >>
      simp[contextTheory.mk_ptr_def, vyperASTTheory.expr_type_def] >>
      disch_then irule >> simp[] >>
      Cases_on `type_memory_size etv = 0` >> simp[] >>
      `n <> 0` by decide_tac >>
      `w2n w + type_memory_size (ArrayTV etv (Fixed n)) <= s.vs_alloca_next` by
        (qpat_assum `vv_store_bound _ _ _ _ _ _ _`
           (mp_tac o CONJUNCT2 o REWRITE_RULE [exprSimMemDefsTheory.vv_store_bound_def]) >>
         disch_then (qspecl_then [`t`,`p.ptr_operand`,`ArrayTV etv (Fixed n)`,`w`] mp_tac) >>
         simp[type_memory_size_def]) >>
      decide_tac) >>
  irule bodyPtrAttributeFieldsTheory.ptr_buf_ok_offset >>
  goal_assum (drule_at (Pat `ptr_buf_ok _ _ _ _ _`)) >>
  qexistsl [`i * type_memory_size etv`,`w`] >>
  `type_memory_bytes ce et = type_memory_size etv /\
   type_memory_bytes ce (ArrayT et (Fixed n)) = type_memory_size (ArrayTV etv (Fixed n))` by
    metis_tac[exprSimHypsTheory.expr_sim_inv_memory_size] >>
  simp[exprLoweringTheory.lowered_value_type_def, vyperASTTheory.expr_type_def] >>
  rpt strip_tac >> Cases_on `p.ptr_operand` >> Cases_on `dst` >>
  gvs[ptrDisciplineTheory.op_prov_def]
QED

Theorem subscript_captured_fixed_execution:
  expr_body_pre ce cx env (Subscript ann obj idx) es /\
  eval_expr cx obj es = (INL (PlaceR (MemoryPlace id path)),mid) /\
  expr_type obj = ArrayT et (Fixed n) /\ base_from_pop obj /\
  post_value_type ce obj = expr_type obj /\
  esz = type_memory_bytes ce et /\
  bind (eval_expr cx idx) (read_result cx) (mid with gas_obs := gs) = (INL key,fin) /\
  vv_post H ctx fn ce cx obj es sa sm s0 mid
    (PlaceR (MemoryPlace id path)) (LocatedValue t p) s /\
  expr_post H ctx fn ce cx idx (mid with gas_obs := gs) sm sn s fin key iop u /\
  local_ptrs_reserved ce sm /\
  stmt_state_rel H ctx fn ce cx es s0 /\ local_ptrs_reserved ce sa /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  ghost_kept_at lo ce es sa G0 tn0 s0 G tn /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sm x) /\
  (!l. p.ptr_operand <> Label l) /\
  evaluate_type (get_tenv cx) (expr_type obj) = SOME (ArrayTV etv (Fixed n)) /\
  ptr_vv_ok cx (post_value_type ce obj) (PlaceR (MemoryPlace id path))
    (LocatedValue t p) mid G tn s /\
  ghost_kept_at lo ce (mid with gas_obs := gs) sm G tn s G' tn' /\
  ghost_inv_at D0 lo d ce cx fin G' tn' u /\
  ptr_val_ok cx (post_value_type ce idx) key iop G' tn' u /\
  vv_store_bound cx (post_value_type ce obj) (lowered_value_type ce obj)
    mid (PlaceR (MemoryPlace id path)) (LocatedValue t p) s /\
  ptr_buf_ok ce obj p.ptr_operand G s /\ s.vs_alloca_next <= u.vs_alloca_next /\
  lower_value compile_expr ce ty idx sm = (iop,sn) /\
  compile_array_subscript p.ptr_operand iop F n ws esz
    (is_signed_type (expr_type idx)) loader sn = (dst,sb) /\
  fn_has_code sn sb fn /\ alloca_history fn u /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\ ~u.vs_halted /\
  u.vs_current_bb = sn.cs_current_bb /\ u.vs_inst_idx = LENGTH sn.cs_current_insts ==>
  ?w i iw v q Gq tnq.
    p.ptr_location = LocMemory /\ key = IntV i /\
    i = (if is_signed_type (expr_type idx) then w2i iw else &(w2n iw)) /\
    eval_operand p.ptr_operand u = SOME w /\
    runtime_place_typed cx fin (MemoryPlace id path) (ArrayTV etv (Fixed n)) /\
    popped_keys_indexed fin.scopes /\
    read_result cx (PlaceR (MemoryPlace id path)) fin = (INL v,fin) /\
    val_wf (ArrayTV etv (Fixed n)) v /\
    ptr_vv_ok cx (ArrayT et (Fixed n)) (PlaceR (MemoryPlace id path))
      (LocatedValue t p) fin G' tn' u /\
    place_ptr_rel ce cx u (PlaceR (MemoryPlace id path)) w
      (SOME LocMemory) (Type (ArrayT et (Fixed n))) /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (u,G',tn') []
      (if idx_in_range (is_signed_type (expr_type idx)) iw (n2w n)
       then OK q else Abort Revert_abort q,Gq,tnq)) /\
    tnq.t_mem = tn'.t_mem /\ tnq.t_stor = tn'.t_stor /\
    tnq.t_trans = tn'.t_trans /\ tnq.t_imm = tn'.t_imm /\
    (!x. not_fresh_at sn x ==>
      FLOOKUP Gq x = FLOOKUP G' x /\ FLOOKUP tnq.t_var x = FLOOKUP tn'.t_var x /\
      FLOOKUP q.vs_vars x = FLOOKUP u.vs_vars x) /\
    (q with <|vs_vars := u.vs_vars; vs_inst_idx := u.vs_inst_idx|>) =
      (if idx_in_range (is_signed_type (expr_type idx)) iw (n2w n)
       then u else revert_state (set_returndata [] u)) /\
    (~idx_in_range (is_signed_type (expr_type idx)) iw (n2w n) ==>
      select_result cx (ArrayT et (Fixed n)) (PlaceR (MemoryPlace id path))
        (ValueSubscript (IntV i)) fin =
        (INR (Error (RuntimeError "evaluate_subscripts array_index")),fin)) /\
    (idx_in_range (is_signed_type (expr_type idx)) iw (n2w n) ==>
      ~q.vs_halted /\ q.vs_current_bb = sb.cs_current_bb /\
      q.vs_inst_idx = LENGTH sb.cs_current_insts /\ alloca_history fn q /\
      0 <= i /\ Num i < n /\ esz = type_memory_size etv /\
      evaluate_type (get_tenv cx) et = SOME etv /\
      w2n (w + iw * n2w esz) = w2n w + Num i * esz /\
      eval_operand p.ptr_operand s = SOME w /\
      eval_operand dst q = SOME (w + iw * n2w esz) /\
      op_prov Gq dst = op_prov G' p.ptr_operand /\ op_taint tnq dst = {} /\
      select_result cx (ArrayT et (Fixed n)) (PlaceR (MemoryPlace id path))
        (ValueSubscript (IntV i)) fin =
        (INL (PlaceR (MemoryPlace id (path ++ [ValueSubscript (IntV i)]))),fin) /\
      vv_place_ptr ce cx fin q (PlaceR (MemoryPlace id (path ++ [ValueSubscript (IntV i)])))
        (LocatedValue et (mk_ptr dst LocMemory)) /\
      ptr_vv_ok cx et (PlaceR (MemoryPlace id (path ++ [ValueSubscript (IntV i)])))
        (LocatedValue et (mk_ptr dst LocMemory)) fin Gq tnq q /\
      vv_at ce cx et sa sb fin (PlaceR (MemoryPlace id (path ++ [ValueSubscript (IntV i)])))
        (LocatedValue et (mk_ptr dst LocMemory)) q /\
      vv_holds ce cx et (PlaceR (MemoryPlace id (path ++ [ValueSubscript (IntV i)])))
        (LocatedValue et (mk_ptr dst LocMemory)) fin q /\
      vv_post H ctx fn ce cx (Subscript et obj idx) es sa sb s0 fin
        (PlaceR (MemoryPlace id (path ++ [ValueSubscript (IntV i)])))
        (LocatedValue et (mk_ptr dst LocMemory)) q /\
      vv_store_bound cx (post_value_type ce (Subscript et obj idx))
        (lowered_value_type ce (Subscript et obj idx)) fin
        (PlaceR (MemoryPlace id (path ++ [ValueSubscript (IntV i)])))
        (LocatedValue et (mk_ptr dst LocMemory)) q /\
      ptr_buf_ok ce (Subscript et obj idx) dst Gq q /\
      (! (H':(bool # 256 word # type_value) list # num list) D'.
          stmt_state_rel H' ctx fn ce cx es s0 /\
          vv_post H' ctx fn ce cx obj es sa sm s0 mid
            (PlaceR (MemoryPlace id path)) (LocatedValue t p) s /\
          expr_post H' ctx fn ce cx idx (mid with gas_obs := gs) sm sn s fin key iop u /\
          ghost_inv_at D' lo d ce cx fin G' tn' u ==>
          vv_post H' ctx fn ce cx (Subscript et obj idx) es sa sb s0 fin
            (PlaceR (MemoryPlace id (path ++ [ValueSubscript (IntV i)])))
            (LocatedValue et (mk_ptr dst LocMemory)) q /\
          ghost_inv_at D' lo d ce cx fin Gq tnq q /\
          ghost_kept_at lo ce es sa G0 tn0 s0 Gq tnq))
Proof
  strip_tac >>
  `evaluate_type (get_tenv cx) (post_value_type ce obj) = SOME (ArrayTV etv (Fixed n))` by
    metis_tac[] >>
  drule_all_then strip_assume_tac subscript_captured_pop_transport >>
  drule_all_then assume_tac expr_body_pre_array_subscript_index_after_base >>
  `?ir. eval_expr cx idx (mid with gas_obs := gs) = (INL ir,fin) /\
        read_result cx ir fin = (INL key,fin)` by
    (drule_then strip_assume_tac vyperStatePreservationTheory.bind_split
     >- (rename1 `read_result cx ir _ = (INL key,fin)` >>
         qpat_assum `read_result cx ir _ = _`
           (SUBST_ALL_TAC o MATCH_MP read_result_state) >>
         qexists `ir` >> simp[])
     >> gvs[]) >>
  `expr_body_pre ce cx env idx (mid with gas_obs := gs)` by simp[] >>
  drule_all_then strip_assume_tac expr_body_pre_runtime_typed >>
  `?tvi. evaluate_type (get_tenv cx) (expr_type idx) = SOME tvi /\
         value_has_type tvi key` by metis_tac[] >>
  drule_all_then strip_assume_tac framed_array_index_post_view >>
  `is_word_type (expr_type idx)` by
    (qpat_assum `evaluate_type _ (expr_type idx) = _` mp_tac >>
     qpat_assum `value_has_type tvi key` mp_tac >>
     qpat_assum `key = IntV i` SUBST1_TAC >> rpt (pop_assum kall_tac) >>
     Cases_on `expr_type idx` >>
     simp[vyperValueTheory.evaluate_type_def, AllCaseEqs(),
          vyperTypingTheory.value_has_type_def, compileEnvTheory.is_word_type_def] >>
     rpt strip_tac >> gvs[vyperTypingTheory.value_has_type_def, compileEnvTheory.is_word_type_def]) >>
  `op_taint tn' p.ptr_operand = {} /\ op_taint tn' iop = {} /\ op_prov G' iop = NONE /\
   allocas_from lo u` by fs[ptr_vv_ok_def, ptr_val_ok_def, ghost_inv_at_def] >>
  `sm.cs_next_var <= sn.cs_next_var` by
    (qspecl_then [`ce`,`ty`,`idx`,`sm`] mp_tac ci_mono_lower_value_compile_expr >>
     simp[ci_mono_def]) >>
  `!x. p.ptr_operand = Var x ==> not_fresh_at sn x` by
    metis_tac[not_fresh_at_mono] >>
  `!x. iop = Var x ==> not_fresh_at sn x` by
    (rpt strip_tac >> irule compile_lower_value_var >>
     qexistsl [`ce`,`idx`,`iop`,`sm`,`ty`] >> simp[]) >>
  drule_all_then strip_assume_tac captured_fixed_emission_cut >>
  `eval_operand (Lit (n2w n)) u = SOME (n2w n) /\
   (!x. Lit (n2w n) = Var x ==> not_fresh_at sn x) /\
   op_prov G' (Lit (n2w n)) = NONE /\ op_taint tn' (Lit (n2w n)) = {}` by
    simp[eval_operand_def, ptrDisciplineTheory.op_prov_def, ptrDisciplineTheory.op_taint_def] >>
  drule_all array_tail_scalar_uniform >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choose_then `q` (qx_choose_then `Gq` (qx_choose_then `tnq` strip_assume_tac)))) >>
  `ptr_vv_ok cx (ArrayT et (Fixed n)) (PlaceR (MemoryPlace id path))
     (LocatedValue t p) fin G' tn' u /\
   place_ptr_rel ce cx u (PlaceR (MemoryPlace id path)) w
     (SOME LocMemory) (Type (ArrayT et (Fixed n)))` by metis_tac[] >>
  `n < dimword (:256)` by metis_tac[placeStoreSlotsTheory.store_slots_fixed_count_bound] >>
  `idx_in_range (is_signed_type (expr_type idx)) iw (n2w n) <=> 0 <= i /\ i < &n` by
    (drule idx_in_range_integer >>
     disch_then (qspecl_then [`iw`,`is_signed_type (expr_type idx)`] mp_tac) >> simp[]) >>
  `value_has_type (ArrayTV etv (Fixed n)) v` by
    (`expr_body_pre ce cx env obj es` by
       metis_tac[expr_body_pre_array_subscript_base, base_from_pop_not_array_slot_base] >>
     qpat_assum `expr_body_pre _ _ _ obj _`
       (mp_then Any mp_tac expr_body_pre_runtime_typed) >>
     simp[] >> metis_tac[]) >>
  `?kvs. v = ArrayV (SArrayV kvs)` by
    (qpat_assum `value_has_type (ArrayTV _ _) v` mp_tac >>
     rpt (pop_assum kall_tac) >> Cases_on `v` >>
     simp[vyperTypingTheory.value_has_type_def] >>
     rename1 `ArrayV av` >> Cases_on `av` >>
     simp[vyperTypingTheory.value_has_type_def]) >>
  `~idx_in_range (is_signed_type (expr_type idx)) iw (n2w n) ==>
     select_result cx (ArrayT et (Fixed n)) (PlaceR (MemoryPlace id path))
       (ValueSubscript (IntV i)) fin =
       (INR (Error (RuntimeError "evaluate_subscripts array_index")),fin)` by
    (disch_tac >>
     `~valid_index (ArrayTV etv (Fixed n)) (SArrayV kvs) i` by
       (simp[vyperValueOperationTheory.array_length_def, IgnAsm `i = if _ then _ else _`] >>
        metis_tac[]) >>
     `evaluate_subscripts (ArrayTV etv (Fixed n)) (ArrayV (SArrayV kvs))
        [ValueSubscript (IntV i)] = INR (RuntimeError "evaluate_subscripts array_index")` by
       (irule evaluate_array_subscript_oob >> simp[]) >>
     `!tr slot vt. MemoryPlace id path <> StoragePlace tr slot vt` by simp[] >>
     `read_result cx (PlaceR (MemoryPlace id path)) fin =
        (INL (ArrayV (SArrayV kvs)),fin)` by simp[] >>
     drule_all select_nonstorage_place_error >> simp[]) >>
  qexistsl [`w`,`i`,`iw`,`v`,`q`,`Gq`,`tnq`] >>
  simp[IgnAsm `idx_in_range _ _ _ <=> _`] >> disch_tac >>
  qpat_assum `idx_in_range _ _ _ ==> _` (drule_then strip_assume_tac) >>
  `evaluate_type (get_tenv cx) (ArrayT et (Fixed n)) = SOME (ArrayTV etv (Fixed n))` by
    metis_tac[] >>
  `evaluate_type (get_tenv cx) et = SOME etv` by
    (qpat_assum `evaluate_type _ (ArrayT _ _) = SOME _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[vyperValueTheory.evaluate_type_def, AllCaseEqs()]) >>
  `esz = type_memory_size etv` by
    (qpat_assum `esz = type_memory_bytes ce et` SUBST1_TAC >>
     irule exprSimHypsTheory.expr_sim_inv_memory_size >>
     qexistsl [`cx`,`env`,`es`] >> fs[expr_body_pre_def]) >>
  `0 <= i /\ i < &n` by metis_tac[] >>
  `iw = n2w (Num i)` by
    (qpat_assum `0 <= i` mp_tac >> qpat_assum `i = _` mp_tac >>
     rpt (pop_assum kall_tac) >> Cases_on `is_signed_type (expr_type idx)` >>
     simp[integer_wordTheory.w2i_def] >> Cases_on `word_msb iw` >>
     simp[] >> rw[] >> gvs[]) >>
  qpat_x_assum `i = if _ then _ else _` (SUBST1_TAC o SYM) >>
  `?vchild. array_index (ArrayTV etv (Fixed n)) (SArrayV kvs) i = SOME vchild` by
    (irule (REWRITE_RULE [optionTheory.IS_SOME_EXISTS] array_index_valid) >>
     simp[vyperArrayTheory.valid_index_def,
          vyperValueOperationTheory.array_length_def]) >>
  `val_wf etv vchild` by
    metis_tac[vyperAssignPreservesTypeTheory.array_index_has_type,
      valueTypingMemoryPropsTheory.value_has_type_memory_wf,
      vyperTypingTheory.evaluate_type_well_formed] >>
  `w2n w + val_footprint (ArrayTV etv (Fixed n)) (ArrayV (SArrayV kvs)) < dimword (:256)` by
    (drule_all vv_post_memory_footprint_bound >> simp[]) >>
  `w2n (w + n2w (Num i * type_memory_size etv)) = w2n w + Num i * type_memory_size etv` by
    (irule fixed_array_element_nonwrapping >> qexistsl [`SArrayV kvs`,`n`,`vchild`] >>
     metis_tac[]) >>
  `eval_operand dst q = SOME (w + n2w (Num i * type_memory_size etv))` by
    simp[word_mul_n2w] >>
  `q.vs_memory = u.vs_memory` by
    (qpat_assum `q with <|vs_vars := _; vs_inst_idx := _|> = _`
       (mp_tac o Q.AP_TERM `\z. z.vs_memory`) >> simp[]) >>
  `!r sz b. FLOOKUP ce.ce_vars id = SOME (PtrVar (Var r) sz) /\
      lookup_var r u = SOME b ==> lookup_var r q = SOME b` by
    ((rpt strip_tac >>
     `not_fresh_at sm r` by
       (qpat_assum `local_ptrs_reserved ce sm`
          (qspecl_then [`id`,`id`,`r`,`sz`,`sz`] mp_tac o
           CONJUNCT1 o CONJUNCT2 o REWRITE_RULE [local_ptrs_reserved_def]) >>
        simp[]) >>
     `not_fresh_at sn r` by metis_tac[not_fresh_at_mono] >>
     qpat_assum `!x. not_fresh_at sn x ==> _`
       (qspec_then `r` mp_tac) >> simp[lookup_var_def] >> (gvs[not_fresh_at_mono, lookup_var_def]))) >>
  `read_result cx (PlaceR (MemoryPlace id path)) fin =
     (INL (ArrayV (SArrayV kvs)),fin)` by simp[] >>
  drule_all_then strip_assume_tac (SIMP_RULE (srw_ss()) []
    (Q.INST [`j` |-> `Num i * type_memory_size etv`] subscript_captured_fixed_child)) >>
  simp[] >>
  `q.vs_allocas = u.vs_allocas` by
    (qpat_assum `q with <|vs_vars := _; vs_inst_idx := _|> = _`
       (mp_tac o Q.AP_TERM `\z. z.vs_allocas`) >> simp[]) >>
  `alloca_history fn q` by
    (`sb.cs_current_bb = sn.cs_current_bb /\
      sb.cs_current_insts = sn.cs_current_insts ++
        (emitted_insts sn sc ++ emitted_insts sc sb)` by
       fs[same_blocks_def, APPEND_ASSOC] >>
     drule_all_then strip_assume_tac
       stmtReasonLitFragMemoryTheory.fn_has_code_code >>
     fs[rich_listTheory.IS_PREFIX_APPEND] >>
     `q.vs_inst_idx = u.vs_inst_idx +
       LENGTH (emitted_insts sn sc ++ emitted_insts sc sb)` by simp[] >>
     `q.vs_current_bb = u.vs_current_bb` by simp[] >>
     `EVERY (\ins. ins.inst_opcode <> ALLOCA)
        (emitted_insts sn sc ++ emitted_insts sc sb)` by simp[] >>
     `DROP u.vs_inst_idx bb.bb_instructions =
        (emitted_insts sn sc ++ emitted_insts sc sb) ++ l` by
       simp[APPEND_ASSOC] >>
     `lookup_block u.vs_current_bb fn.fn_blocks = SOME bb` by simp[] >>
     `alloca_history fn (q with vs_inst_idx := q.vs_inst_idx)`
       suffices_by simp[] >>
     qpat_assum `q.vs_inst_idx = u.vs_inst_idx + _` SUBST1_TAC >>
     irule bodyBinopFragMemoryTheory.alloca_history_no_alloca_slice >>
     simp[] >> qexistsl [`bb`,`l`] >> simp[]) >>
  `!z a. FLOOKUP s.vs_allocas z = SOME a ==> FLOOKUP q.vs_allocas z = SOME a` by
    fs[expr_post_def] >>
  `!z a. not_fresh_at sm z /\ lookup_var z s = SOME a ==> lookup_var z q = SOME a` by
    (rpt strip_tac >>
     `lookup_var z u = SOME a` by (fs[expr_post_def] >> metis_tac[]) >>
     `not_fresh_at sn z` by metis_tac[not_fresh_at_mono] >>
     qpat_assum `!x. not_fresh_at sn x ==> _` (qspec_then `z` mp_tac) >>
     fs[lookup_var_def]) >>
  `eval_operand p.ptr_operand q = eval_operand p.ptr_operand s` by
    (irule EQ_TRANS >> qexists `SOME w` >> simp[] >>
     irule eval_operand_frame >> conj_tac >- simp[] >>
     qexistsl [`sm`,`s`] >> simp[]) >>
  `MAP FDOM mid.scopes = MAP FDOM fin.scopes` by
    (qpat_assum `eval_expr cx idx _ = (INL ir,fin)`
       (mp_then Any mp_tac eval_expr_preserves_scopes_dom) >> simp[]) >>
  `local_ptrs_rel fn ce mid.scopes s` by
    (qpat_assum `vv_post _ _ _ _ _ obj _ _ _ _ mid _ _ s`
       (mp_tac o CONJUNCT1 o REWRITE_RULE [vv_post_def]) >>
     metis_tac[stmt_state_rel_local_ptrs_alloca]) >>
  `!name b sz. local_region ce fin.scopes q name b sz <=>
                local_region ce mid.scopes s name b sz` by
    (rpt gen_tac >> eq_tac >> strip_tac
     >- (irule local_region_frame >> metis_tac[])
     >> irule local_region_frame_fwd >> metis_tac[]) >>
  `sm.cs_next_id <= sb.cs_next_id` by
    (`ci_mono sm sn` by
       (qspecl_then [`ce`,`ty`,`idx`,`sm`] mp_tac ci_mono_lower_value_compile_expr >> simp[]) >>
     `compile_array_subscript p.ptr_operand iop F n ws esz
         (is_signed_type (expr_type idx)) (\a. comp_return a) sn = (dst,sb)` by
       ((qpat_assum `compile_array_subscript _ _ F _ _ _ _ loader _ = _` mp_tac >>
        simp[compile_array_subscript_split, comp_bind_def, comp_ignore_bind_def,
             comp_return_def] >> (gvs[compile_array_subscript_split, comp_bind_def, comp_ignore_bind_def, comp_return_def]))) >>
     `ci_mono sn (SND (compile_array_subscript p.ptr_operand iop F n ws esz
         (is_signed_type (expr_type idx)) (\a. comp_return a) sn))` by
       (irule ci_mono_compile_array_subscript >> simp[ci_mono_comp_return]) >>
     gvs[ci_mono_def] >> decide_tac) >>
  `vv_at ce cx (ArrayT et (Fixed n)) sa sm mid
     (PlaceR (MemoryPlace id path)) (LocatedValue t p) s` by
    gvs[vv_post_def] >>
  `read_result cx (PlaceR (MemoryPlace id path)) mid =
      (INL (ArrayV (SArrayV kvs)),mid)` by simp[] >>
  drule_all_then assume_tac captured_memory_vv_at_frame >>
  `evaluate_subscripts (ArrayTV etv (Fixed n)) (ArrayV (SArrayV kvs))
     [ValueSubscript (IntV i)] = INL vchild` by simp[evaluate_array_subscript_result] >>
  drule_all_then strip_assume_tac select_fixed_memory_read >>
  `Num i < n` by
    (qpat_assum `i < &n` mp_tac >> qpat_assum `0 <= i` mp_tac >>
     intLib.COOPER_TAC) >>
  `type_memory_bytes ce et = type_memory_size etv` by metis_tac[] >>
  simp[word_mul_n2w] >>
  conj_asm1_tac
  >- (irule vv_at_fixed_array_element >>
      ntac 5 (goal_assum (drule_at Any)) >>
      simp[mem_step_offset_def] >> qexists `i` >> simp[] >>
      rpt gen_tac >> eq_tac >> strip_tac >> simp[]) >>
  qpat_assum `!ty. _ /\ read_result cx _ fin = (INL vchild,fin)`
    (qspec_then `et` strip_assume_tac) >>
  `ptr_mem_ok cx et vchild dst Gq tnq q` by
    (qpat_assum `!ty. _ /\ _ /\ ptr_vv_ok cx et _ _ _ Gq tnq q`
       (qspec_then `et` mp_tac) >>
     gvs[ptr_vv_ok_def, contextTheory.mk_ptr_def]) >>
  `val_in_memory etv vchild (w2n (w + n2w (Num i * type_memory_size etv))) q.vs_memory` by
    (qpat_assum `ptr_mem_ok cx et vchild dst Gq tnq q`
       (mp_then Any mp_tac bodyPtrBopHashFootprintTheory.ptr_mem_ok_representation) >>
     simp[]) >>
  `value_has_type etv vchild` by
    metis_tac[vyperAssignPreservesTypeTheory.array_index_has_type,
              vyperTypingTheory.evaluate_type_well_formed] >>
  conj_asm1_tac
  >- (gvs[vv_holds_def, contextTheory.mk_ptr_def] >>
      strip_tac >> metis_tac[val_in_memory_word_type]) >>
  `MAP FDOM es.scopes = MAP FDOM mid.scopes` by
    (qpat_assum `eval_expr cx obj _ = _`
       (mp_then Any mp_tac eval_expr_preserves_scopes_dom) >> simp[]) >>
  conj_asm1_tac
  >- (irule captured_fixed_post_join >>
      simp[] >>
      goal_assum (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
      goal_assum (drule_at (Pat `expr_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
      simp[] >>
      qpat_assum `!x. not_fresh_at sn x ==> _` mp_tac >> simp[]) >>
  `s.vs_alloca_next <= q.vs_alloca_next` by
    (qpat_assum `q with <|vs_vars := _; vs_inst_idx := _|> = _`
       (mp_tac o Q.AP_TERM `\z. z.vs_alloca_next`) >> simp[]) >>
  `op_prov G' p.ptr_operand = op_prov G p.ptr_operand` by
    (Cases_on `p.ptr_operand` >> gvs[ptrDisciplineTheory.op_prov_def, ghost_kept_at_def]) >>
  `op_prov Gq dst = op_prov G p.ptr_operand` by metis_tac[] >>
  `expr_sim_inv ce cx env es` by fs[expr_body_pre_def] >>
  drule_all_then strip_assume_tac captured_fixed_capacity >>
  fs[post_value_type_def] >>
  qx_gen_tac `HH` >> qx_gen_tac `DD` >> strip_tac >>
  conj_tac
  >- (irule captured_fixed_post_join >>
      simp[] >>
      goal_assum (drule_at (Pat `vv_post HH _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
      goal_assum (drule_at (Pat `expr_post HH _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
      simp[] >>
      qpat_assum `!x. not_fresh_at sn x ==> _` mp_tac >> simp[]) >>
  `wb_frame ce es mid sa s0 s` by
    (fs[vv_post_def, wb_frame_def] >> first_assum ACCEPT_TAC) >>
  irule captured_fixed_ghost_join >>
  simp[] >> conj_tac >- (qexistsl [`HH`,`ctx`,`fn`] >> simp[]) >>
  qexistsl [`G`,`G'`,`gs`,`mid`,`s`,`sm`,`sn`,`tn`,`tn'`,`u`] >> simp[]
QED

(* Package the bounds-and-address tail at the successful index endpoint.
   The canonical horizon chooses one endpoint; the two child posts at each
   horizon then establish its joint post without running the tail again. *)
Theorem subscript_captured_fixed_outcome:
  expr_body_pre ce cx env (Subscript et obj idx) es /\
  eval_expr cx obj es = (INL (PlaceR (MemoryPlace id path)),mid) /\
  expr_type obj = ArrayT et (Fixed n) /\ base_from_pop obj /\
  post_value_type ce obj = expr_type obj /\
  esz = type_memory_bytes ce et /\
  bind (eval_expr cx idx) (read_result cx) (mid with gas_obs := gs) = (INL key,fin) /\
  storage_trace_domain cx st0 fin.storage_trace /\ fin.gas_obs = [] /\
  local_ptrs_reserved ce sm /\ local_ptrs_reserved ce sa /\
  sa.cs_next_var <= sm.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  ghost_kept_at lo ce es sa G0 tn0 s0 G tn /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sm x) /\
  (!l. p.ptr_operand <> Label l) /\
  evaluate_type (get_tenv cx) (expr_type obj) = SOME (ArrayTV etv (Fixed n)) /\
  ptr_vv_ok cx (post_value_type ce obj) (PlaceR (MemoryPlace id path))
    (LocatedValue t p) mid G tn s /\
  ghost_kept_at lo ce (mid with gas_obs := gs) sm G tn s G' tn' /\
  ptr_val_ok cx (post_value_type ce idx) key iop G' tn' u /\
  vv_store_bound cx (post_value_type ce obj) (lowered_value_type ce obj)
    mid (PlaceR (MemoryPlace id path)) (LocatedValue t p) s /\
  ptr_buf_ok ce obj p.ptr_operand G s /\
  s0.vs_alloca_next <= s.vs_alloca_next /\ s.vs_alloca_next <= u.vs_alloca_next /\
  lower_value compile_expr ce ty idx sm = (iop,sn) /\
  compile_array_subscript p.ptr_operand iop F n ws esz
    (is_signed_type (expr_type idx)) loader sn = (dst,sb) /\
  fn_has_code sn sb fn /\ alloca_history fn u /\
  ~u.vs_halted /\
  u.vs_current_bb = sn.cs_current_bb /\ u.vs_inst_idx = LENGTH sn.cs_current_insts /\
  (!H. valid_horizon cx st0 H fin.storage_trace ==>
    stmt_state_rel H ctx fn ce cx es s0 /\
    vv_post H ctx fn ce cx obj es sa sm s0 mid
      (PlaceR (MemoryPlace id path)) (LocatedValue t p) s /\
    expr_post H ctx fn ce cx idx (mid with gas_obs := gs) sm sn s fin key iop u /\
    ghost_inv_at (DF H) lo d ce cx fin G' tn' u) ==>
  gas_outcome_full (DF,lo,explicit,ctx,fn,PG) (cx_tops cx) cx st0
    (select_result cx (ArrayT et (Fixed n)) (PlaceR (MemoryPlace id path))
      (ValueSubscript key)) (fin,u,G',tn')
    (\H res ee Gz tnz z. ?r. res = INL r /\
       vv_post H ctx fn ce cx (Subscript et obj idx) es sa sb s0 ee
         r (LocatedValue et (mk_ptr dst LocMemory)) z /\
       vv_store_bound cx (post_value_type ce (Subscript et obj idx))
         (lowered_value_type ce (Subscript et obj idx)) ee
         r (LocatedValue et (mk_ptr dst LocMemory)) z /\
       z.vs_current_bb = sb.cs_current_bb /\
       z.vs_inst_idx = LENGTH sb.cs_current_insts /\ alloca_history fn z /\
       (ctx_has_dalloca ctx ==> allocas_below_fmp z) /\
       s0.vs_alloca_next <= z.vs_alloca_next /\
       ghost_inv_at (DF H) lo d ce cx ee Gz tnz z /\
       ptr_vv_ok cx (post_value_type ce (Subscript et obj idx))
         r (LocatedValue et (mk_ptr dst LocMemory)) ee Gz tnz z /\
       (!v. r = Value v /\ ~is_word_type (post_value_type ce (Subscript et obj idx)) /\
          ~is_bytestring_type (post_value_type ce (Subscript et obj idx)) ==>
          vv_own ce cx (post_value_type ce (Subscript et obj idx)) sa sb ee
            r (LocatedValue et (mk_ptr dst LocMemory)) z /\
          (!t' p'. LocatedValue et (mk_ptr dst LocMemory) = LocatedValue t' p' ==>
                   p'.ptr_location = LocMemory)) /\
       (ce.ce_is_ctor /\ vv_location (LocatedValue et (mk_ptr dst LocMemory)) = SOME LocCode ==>
        ?v. read_result cx r ee = (INL v,ee) /\
            !rt w. evaluate_type (get_tenv cx) (post_value_type ce (Subscript et obj idx)) = SOME rt /\
              eval_operand (vv_operand (LocatedValue et (mk_ptr dst LocMemory))) z = SOME w ==>
              w2n w + type_memory_size rt <= lo /\
              (!mem. mem_agree_outside tnz.t_mem z.vs_memory mem ==>
                val_in_memory rt v (w2n w) mem)) /\
       (!t' op. LocatedValue et (mk_ptr dst LocMemory) = StackValue t' op /\
          ~is_word_type (post_value_type ce (Subscript et obj idx)) ==>
          ptr_buf_ok ce (Subscript et obj idx) op Gz z) /\
       (!t' p'. LocatedValue et (mk_ptr dst LocMemory) = LocatedValue t' p' /\
          p'.ptr_location = LocMemory ==>
          ptr_buf_ok ce (Subscript et obj idx) p'.ptr_operand Gz z) /\
       ghost_kept_at lo ce es sa G0 tn0 s0 Gz tnz)
    (\H res ee gt r. expr_exit res r /\ halt_exit H cx ee res r /\
      (ctx_has_dalloca ctx ==> !z. r = Halt z ==> allocas_below_fmp z))
Proof
  strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (qspec_then `storage_trace_horizon fin.storage_trace` mp_tac) >>
  impl_tac >- simp[GSYM storage_trace_domain_def] >> strip_tac >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp u` by
    (qpat_assum `expr_post _ ctx fn ce cx idx _ _ _ _ _ _ _ u`
       (ACCEPT_TAC o MATCH_MP bodyFullHashKeccakFixedTheory.stmt_state_rel_allocas_below_fmp o
        MATCH_MP expr_post_state)) >>
  drule_all subscript_captured_fixed_execution >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  qpat_x_assum `i = if _ then _ else _` kall_tac >>
  qpat_x_assum `key = IntV i` SUBST_ALL_TAC >>
  irule gas_outcome_full_intro >>
  qexistsl [`Gq`,`fin`,`[]`,
    `if idx_in_range (is_signed_type (expr_type idx)) iw (n2w n)
     then OK q else Abort Revert_abort q`,
    `FST (select_result cx (ArrayT et (Fixed n)) (PlaceR (MemoryPlace id path))
      (ValueSubscript (IntV i)) fin)`,`tnq`] >>
  simp[gasSummaryTheory.gas_explicit_def] >>
  `fin with gas_obs := [] = fin` by simp[evaluation_state_component_equality] >>
  conj_tac
  >- (gen_tac >>
      `!tr slot vt. PlaceR (MemoryPlace id path) <> PlaceR (StoragePlace tr slot vt)` by simp[] >>
      `SND (select_result cx (ArrayT et (Fixed n)) (PlaceR (MemoryPlace id path))
        (ValueSubscript (IntV i)) fin) = fin` by
        (Cases_on `idx_in_range (is_signed_type (expr_type idx)) iw (n2w n)` >> gvs[]) >>
      drule_all select_result_nonstorage_gas_obs >> simp[]) >>
  Cases_on `idx_in_range (is_signed_type (expr_type idx)) iw (n2w n)` >>
  gvs[fragExecTheory.exit_result_def, expr_exit_def, halt_exit_def,
      contextTheory.mk_ptr_def, contextTheory.vv_location_def,
      vyperASTTheory.expr_type_def, post_value_type_def] >>
  qx_gen_tac `H` >> disch_tac >>
  `ctx_has_dalloca ctx ==> allocas_below_fmp q` by
    (qpat_assum `q with <|vs_vars := _; vs_inst_idx := _|> = u`
       (mp_tac o Q.AP_TERM `\z. allocas_below_fmp z`) >>
     qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp u` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[ptrDisciplineTheory.allocas_below_fmp_def] >>
     metis_tac[]) >>
  `q.vs_alloca_next = u.vs_alloca_next` by
    (qpat_assum `_ with <|vs_vars := _; vs_inst_idx := _|> = u`
       (mp_tac o Q.AP_TERM `\z. z.vs_alloca_next`) >> simp[]) >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _` (drule_then strip_assume_tac) >>
  qpat_assum `!H' D'. _ ==> vv_post H' _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
    (qspecl_then [`H`,`DF H`] mp_tac) >>
  simp[] >> decide_tac
QED

(* An owned Value uses a fresh nonlocal allocation, so index effects do
   not need to preserve the contents of any local variable. *)
Theorem subscript_owned_value_transport:
  vv_post H ctx fn ce cx obj es sa sm s0 mid (Value v) (LocatedValue t p) s /\
  vv_own ce cx (post_value_type ce obj) sa sm mid (Value v) (LocatedValue t p) s /\
  ptr_vv_ok cx (post_value_type ce obj) (Value v) (LocatedValue t p) mid G tn s /\
  p.ptr_location = LocMemory /\
  evaluate_type (get_tenv cx) (post_value_type ce obj) = SOME tv /\
  bind (eval_expr cx idx) (read_result cx) (mid with gas_obs := gs) = (INL key,fin) /\
  expr_post H ctx fn ce cx idx (mid with gas_obs := gs) sm sn s fin key op u /\
  ghost_kept_at lo ce (mid with gas_obs := gs) sm G tn s G' tn' /\
  local_ptrs_reserved ce sm /\
  (!x. p.ptr_operand = Var x ==> not_fresh_at sm x) /\
  (!l. p.ptr_operand <> Label l) ==>
  vv_own ce cx (post_value_type ce obj) sa sm fin (Value v) (LocatedValue t p) u /\
  ptr_vv_ok cx (post_value_type ce obj) (Value v) (LocatedValue t p) fin G' tn' u /\
  ?w. eval_operand p.ptr_operand s = SOME w /\
      eval_operand p.ptr_operand u = SOME w /\
      val_wf tv v /\
      mem_bytes_at (w2n w) (val_footprint tv v) u.vs_memory =
      mem_bytes_at (w2n w) (val_footprint tv v) s.vs_memory /\
      (!i. w2n w <= i /\ i < w2n w + val_footprint tv v /\ i IN tn'.t_mem ==>
           i IN tn.t_mem)
Proof
  strip_tac >>
  `MAP FDOM mid.scopes = MAP FDOM fin.scopes` by
    (drule (REWRITE_RULE [ETA_AX] forced_eval_expr_preserves_scopes_dom) >> simp[]) >>
  `local_ptrs_rel fn ce mid.scopes s` by
    (irule (cj 1 stmt_state_rel_local_ptrs_alloca) >> fs[vv_post_def] >>
     metis_tac[]) >>
  `val_wf tv v` by
    (fs[vv_post_def, vv_at_def, read_result_def, return_def] >> metis_tac[]) >>
  `!x a. not_fresh_at sm x /\ lookup_var x s = SOME a ==> lookup_var x u = SOME a` by
    fs[expr_post_def] >>
  qpat_x_assum `vv_own _ _ _ _ _ mid _ _ _` mp_tac >>
  simp[vv_own_def, read_result_def, return_def] >>
  disch_then (qx_choose_then `w` (CONJUNCTS_THEN2 assume_tac assume_tac)) >>
  `eval_operand p.ptr_operand u = SOME w` by
    (irule eval_operand_frame >> conj_tac >- simp[] >>
     qexistsl [`sm`,`s`] >> simp[]) >>
  `mem_bytes_at (w2n w) (val_footprint tv v) u.vs_memory =
   mem_bytes_at (w2n w) (val_footprint tv v) s.vs_memory /\
   (!i. w2n w <= i /\ i < w2n w + val_footprint tv v /\ i IN tn'.t_mem ==>
        i IN tn.t_mem) /\
   vv_own ce cx (post_value_type ce obj) sa sm fin (Value v) (LocatedValue t p) u` by
    (Cases_on `val_footprint tv v = 0`
     >- (simp[valueEncodingDefsTheory.mem_bytes_at_def, vv_own_def,
              read_result_def, return_def] >> decide_tac) >>
     gvs[] >>
     `!n b' sz'. local_region ce (mid with gas_obs := gs).scopes s n b' sz' ==>
                  b + sz <= b' \/ b' + sz' <= b` by
       (simp[] >> first_assum ACCEPT_TAC) >>
     drule_all_then strip_assume_tac bodyFullBuiltinConcatScratchTheory.concat_scratch_child_frame >>
     conj_tac
     >- (drule mem_bytes_at_translated_window >>
         disch_then (qspecl_then [`w2n w - b`, `val_footprint tv v`] mp_tac) >>
         `b + (w2n w - b) = w2n w` by decide_tac >> simp[] >> decide_tac) >>
     conj_tac
     >- (rpt strip_tac >> `b <= i /\ i < b + sz` by decide_tac >> metis_tac[]) >>
     simp[vv_own_def, read_result_def, return_def] >>
     qexistsl [`aid`,`b`,`sz`] >> simp[] >>
     rpt strip_tac >>
     `local_region ce mid.scopes s n lb lsz` by
       (irule local_region_frame >> metis_tac[]) >> metis_tac[]) >>
  `read_result cx (Value v) mid = (INL v,mid) /\
   read_result cx (Value v) fin = (INL v,fin)` by simp[read_result_def, return_def] >>
  drule_all_then assume_tac captured_ptr_vv_footprint_frame >>
  conj_tac
  >- (qpat_assum `vv_own _ _ _ _ _ fin _ _ _`
        (mp_tac o REWRITE_RULE [vv_own_def]) >> simp[]) >>
  simp[]
QED
