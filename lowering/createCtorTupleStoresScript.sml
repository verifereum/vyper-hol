Theory createCtorTupleStores
Ancestors
  createCtorTupleSlotUnwrap createCtorTupleWriteResources createCtorTupleStoreFold
  createCtorTupleCaptureFrame exprOperandVar exprSafeOperand exprSimProps
  exprSimSubscriptArrayFrame exprBopSimProps exprSimMemoryPath
  exprLoweringProps loweringPosts loweringStateRelDefs exprLowering context
  compileEnv emitHelper emitHelperProps fragGasMode fragGasPath freshWrites
  externalEntryShape
  valueEncodingProps venomState venomMemDefs words finite_map arithmetic list

(* Join the multiblock delayed read to the physical write.  The capture
   endpoint stays fixed, independently of the moving execution cursor. *)
Theorem ctor_delayed_slot_path:
  emit_op ADD [src; Lit (n2w off)] a = (dst,a1) /\
  unwrap_value ce vv a1 = (op,a2) /\
  (if is_word_type ty then emit_void MSTORE [dst; op]
   else if is_bytestring_type ty then compile_store_bytestring op dst
   else emit_void MCOPY [dst; op; Lit (n2w (type_memory_bytes ce ty))])
    a2 = ((),a3) /\
  fn_has_code a a3 func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce origin /\ local_ptrs_reserved ce c_vvs /\
  origin.cs_next_var <= c_vvs.cs_next_var /\
  origin.cs_next_id <= c_vvs.cs_next_id /\
  c_vvs.cs_next_var <= a.cs_next_var /\ c_vvs.cs_next_id <= a.cs_next_id /\
  (!x. vv_operand vv = Var x ==> not_fresh_at c_vvs x) /\
  (!l. vv_operand vv <> Label l) /\
  (!x. src = Var x ==> not_fresh_at a x) /\ (!l. src <> Label l) /\
  eval_operand src s = SOME (n2w source_base) /\
  source_base + off < dimword (:256) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\
  type_memory_bytes ce ty = type_memory_size tv /\
  type_memory_size tv < 2 ** 64 /\
  type_memory_size tv + 64 < dimword (:256) /\
  stmt_state_rel H ctx func ce cx es s /\
  storage_well_formed_on cx es (FST H) /\
  vv_holds ce cx ty raw vv es s /\
  vv_at ce cx ty origin c_vvs es raw vv s /\
  read_result cx raw es = (INL v,es) /\
  FLOOKUP s.vs_allocas tuple_aid = SOME (source_base,source_cap) /\
  c_vvs.cs_next_id <= tuple_aid /\ tuple_aid < a.cs_next_id /\
  off + type_memory_size tv <= source_cap /\
  (?inst. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
     inst.inst_id = tuple_aid) /\
  (!n b k. local_region ce es.scopes s n b k ==>
     source_base + source_cap <= b \/ b + k <= source_base) /\
  ~s.vs_halted /\ s.vs_current_bb = a.cs_current_bb /\
  s.vs_inst_idx = LENGTH a.cs_current_insts ==>
  ?q. gas_marked_path F ctx func s 0 (OK q) /\
    val_in_memory tv v (source_base + off) q.vs_memory /\
    eval_operand src q = SOME (n2w source_base) /\
    stmt_state_rel H ctx func ce cx es q /\
    alloca_inv q /\ alloca_room ctx func q /\ fmp_room ctx func q /\
    ~q.vs_halted /\ q.vs_current_bb = a3.cs_current_bb /\
    q.vs_inst_idx = LENGTH a3.cs_current_insts /\
    q.vs_accounts = s.vs_accounts /\ q.vs_transient = s.vs_transient /\
    q.vs_requests = s.vs_requests /\ q.vs_call_ctx = s.vs_call_ctx /\
    wb_frame ce es es c_vvs s q /\
    (!x w. not_fresh_at a x /\ lookup_var x s = SOME w ==>
       lookup_var x q = SOME w) /\
    FLOOKUP q.vs_allocas tuple_aid = SOME (source_base,source_cap) /\
    source_base + source_cap <= q.vs_alloca_next /\
    mem_bytes_at source_base off q.vs_memory =
      mem_bytes_at source_base off s.vs_memory /\
    (!n b k. local_region ce es.scopes q n b k <=>
       local_region ce es.scopes s n b k) /\
    (!aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) /\
       aid < a.cs_next_id /\
       (b + sz <= source_base \/ source_base + source_cap <= b) /\
       (!n p k. local_region ce es.scopes s n p k ==>
          b + sz <= p \/ p + k <= b) ==>
       mem_bytes_at b sz q.vs_memory = mem_bytes_at b sz s.vs_memory) /\
    (!ty' raw' vv' value'.
       vv_holds ce cx ty' raw' vv' es s /\
       vv_at ce cx ty' origin c_vvs es raw' vv' s /\
       read_result cx raw' es = (INL value',es) /\
       (!x. vv_operand vv' = Var x ==> not_fresh_at c_vvs x) /\
       (!l. vv_operand vv' <> Label l) ==>
       vv_holds ce cx ty' raw' vv' es q /\
       vv_at ce cx ty' origin c_vvs es raw' vv' q /\
       read_result cx raw' es = (INL value',es))
Proof
  strip_tac >>
  `ci_mono a a1 /\ ci_mono a1 a2 /\ ci_mono a2 a3` by
    (conj_tac >- metis_tac[ci_mono_emit_op, pairTheory.SND] >>
     conj_tac >- metis_tac[ci_mono_unwrap_value, pairTheory.SND] >>
     Cases_on `is_word_type ty` >> gvs[]
     >- metis_tac[ci_mono_emit_void, pairTheory.SND] >>
     Cases_on `is_bytestring_type ty` >> gvs[] >>
     metis_tac[ci_mono_emit_void, ci_mono_compile_store_bytestring, pairTheory.SND]) >>
  `fn_has_code a a2 func /\ fn_has_code a2 a3 func` by
    (irule fragExecTheory.fn_has_code_split >>
     simp[] >>
     gvs[ci_mono_def] >> metis_tac[cs_extends_trans]) >>
  `!tvt. evaluate_type (get_tenv cx) ty = SOME tvt /\ ~is_word_type ty ==>
     type_memory_bytes ce ty = type_memory_size tvt /\
     type_memory_size tvt < 2 ** 64` by (rpt strip_tac >> gvs[]) >>
  drule_all ctor_slot_unwrap_path >>
  disch_then (qx_choose_then `u` strip_assume_tac) >>
  `(!x. op = Var x \/ dst = Var x ==> not_fresh_at a2 x)` by
    (`!x. op = Var x ==> not_fresh_at a2 x` by
       (`case vv of
           StackValue t vo => (!x. vo = Var x ==> not_fresh_at a1 x)
         | LocatedValue t p => (!x. p.ptr_operand = Var x ==> not_fresh_at a1 x)` by
          (Cases_on `vv` >> gvs[vv_operand_def, ci_mono_def] >>
           metis_tac[not_fresh_at_mono, LESS_EQ_TRANS]) >>
        qpat_x_assum `case vv of _ => _ | _ => _` mp_tac >>
        qpat_x_assum `unwrap_value ce vv a1 = _` mp_tac >>
        POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[compiler_unwrap_value_var]) >>
     `safe_operand a1 dst` by metis_tac[emit_op_safe_operand] >>
     rpt strip_tac >- metis_tac[] >>
     irule not_fresh_at_mono >> qexists `a1` >>
     gvs[ci_mono_def, safe_operand_def]) >>
  `?sw. eval_operand op u = SOME sw /\
     (if is_word_type ty then sw = typed_val_to_w256 tv v
      else val_in_memory tv v (w2n sw) u.vs_memory)` by
    gvs[expr_val_rel_def] >>
  `w2n (n2w (source_base + off):bytes32) = source_base + off` by
    simp[] >>
  `ce.ce_is_ctor ==> !name tv' v' io.
     FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc io) /\
     FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
       | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (tv',v') ==>
     regions_disjoint io (type_memory_size tv') source_base source_cap` by
    (fs[stmt_state_rel_def, immutable_alloca_sep_def] >> metis_tac[]) >>
  `c_vvs.cs_next_var <= a2.cs_next_var` by
    gvs[ci_mono_def] >>
  drule_at (Pat `(if _ then _ else _) _ = _`) ctor_physical_write_resources >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `evaluate_type _ _ = _`)) >>
  disch_then (drule_at (Pat `value_has_type _ _`)) >>
  disch_then (drule_at (Pat `eval_operand op _ = _`)) >>
  disch_then (drule_at (Pat `eval_operand dst _ = _`)) >>
  disch_then (drule_at (Pat `FLOOKUP _ _ = _`)) >>
  disch_then (qspecl_then [`tuple_aid`,`c_vvs`] mp_tac) >>
  simp[] >>
  impl_tac >- (rpt conj_tac >> metis_tac[]) >>
  disch_then (qx_choose_then `q` strip_assume_tac) >>
  `local_ptrs_reserved ce a` by metis_tac[local_ptrs_reserved_next_var] >>
  `!n b k. local_region ce es.scopes u n b k <=>
             local_region ce es.scopes s n b k` by
    (rpt gen_tac >> irule local_region_wb_frame >> simp[] >>
     conj_tac >- (qexists `func` >> gvs[stmt_state_rel_def, state_rel_def]) >>
     metis_tac[]) >>
  `wb_frame ce es es c_vvs s u` by
    (gvs[wb_frame_def] >> conj_tac
     >- (rpt strip_tac >>
         qpat_x_assum `!x w. not_fresh_at a x /\ _ ==> _` irule >>
         simp[] >> metis_tac[not_fresh_at_mono]) >>
     rpt strip_tac >>
     qpat_x_assum `!aid b sz. _ /\ aid < a.cs_next_id /\ _ ==> _` irule >>
     conj_tac >- metis_tac[] >> qexists `aid` >> simp[] >> decide_tac) >>
  `wb_frame ce es es c_vvs s q` by
    (irule exprSimWordArgsTheory.wb_frame_trans >> simp[] >>
     conj_tac >- (qexistsl [`es`,`c_vvs`,`u`] >> simp[]) >> metis_tac[]) >>
  `!n b k. local_region ce es.scopes q n b k <=>
             local_region ce es.scopes s n b k` by
    (rpt gen_tac >> irule local_region_wb_frame >> simp[] >>
     conj_tac >- (qexists `func` >> gvs[stmt_state_rel_def, state_rel_def]) >>
     metis_tac[]) >>
  qexists `q` >> simp[] >>
  conj_tac >- metis_tac[gas_marked_path_then, ADD_CLAUSES] >>
  conj_tac
  >- (irule eval_operand_frame >> conj_tac >- simp[] >>
      qexistsl [`a2`,`u`] >> simp[] >> gvs[ci_mono_def] >>
      metis_tac[not_fresh_at_mono]) >>
  conj_tac
  >- (gvs[wb_frame_def, ci_mono_def] >> metis_tac[not_fresh_at_mono]) >>
  conj_tac
  >- (`mem_bytes_at source_base off u.vs_memory =
         mem_bytes_at source_base off s.vs_memory` by
        (drule valueEncodingPropsTheory.mem_bytes_at_translated_window >>
         disch_then (qspecl_then [`0`,`off`] mp_tac) >> simp[]) >>
      metis_tac[LESS_EQ_REFL]) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `mem_bytes_at b sz u.vs_memory = mem_bytes_at b sz s.vs_memory` by
        (qpat_assum `wb_frame ce es es a s u` mp_tac >>
         pure_rewrite_tac[wb_frame_def] >> strip_tac >>
         qpat_x_assum `!aid b sz. _ /\ aid < a.cs_next_id /\ _ ==> _` irule >>
         simp[] >> conj_tac
         >- (rpt strip_tac >>
             qpat_x_assum `!n p k. local_region ce es.scopes s n p k ==> _` drule >>
             decide_tac) >>
         qexists `aid` >> simp[]) >>
      `mem_bytes_at b sz q.vs_memory = mem_bytes_at b sz u.vs_memory` by
        (qpat_assum `!a n. _ ==> mem_bytes_at a n q.vs_memory = _` irule >> decide_tac) >>
      simp[]) >>
  rpt gen_tac >> strip_tac >>
  `vv_holds ce cx ty' raw' vv' es u /\
   vv_at ce cx ty' origin c_vvs es raw' vv' u` by metis_tac[] >>
  drule_at (Pat `vv_at _ _ _ _ _ _ _ _ _`)
    (INST_TYPE [beta |-> alpha] ctor_capture_frame) >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _ _`)) >>
  simp[contract_storage_def, contract_transient_def] >>
  disch_then (qspecl_then [`c_vvs`,`c_vvs`] mp_tac) >> simp[] >>
  `(!t op. vv' = StackValue t op ==>
      (!x. op = Var x ==> not_fresh_at c_vvs x) /\ (!l. op <> Label l)) /\
   (!t p. vv' = LocatedValue t p ==>
      (!x. p.ptr_operand = Var x ==> not_fresh_at c_vvs x) /\
      (!l. p.ptr_operand <> Label l))` by
    (Cases_on `vv'` >> gvs[vv_operand_def]) >> simp[]
QED

(* Remaining arguments recurse at the physical byte cursor.  The recursive
   prefix frame retains the head representation, including zero-width slots. *)
Theorem ctor_delayed_stores_from_boundaries:
  compile_extcall_store_values ce (ZIP (vvs,tys)) src off ca = ((),cb) /\
  LENGTH vvs = LENGTH tys /\ LENGTH raws = LENGTH tys /\
  LENGTH values = LENGTH tys /\ LENGTH tvs = LENGTH tys /\
  fn_has_code ca cb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce origin /\ local_ptrs_reserved ce c_vvs /\
  origin.cs_next_var <= c_vvs.cs_next_var /\
  origin.cs_next_id <= c_vvs.cs_next_id /\
  c_vvs.cs_next_var <= ca.cs_next_var /\
  c_vvs.cs_next_id <= ca.cs_next_id /\
  (!x. src = Var x ==> not_fresh_at ca x) /\ (!l. src <> Label l) /\
  eval_operand src s = SOME (n2w source_base) /\
  (!i. i < LENGTH tys ==>
    evaluate_type (get_tenv cx) (EL i tys) = SOME (EL i tvs) /\
    value_has_type (EL i tvs) (EL i values) /\
    val_wf (EL i tvs) (EL i values) /\
    type_memory_bytes ce (EL i tys) = type_memory_size (EL i tvs) /\
    type_memory_size (EL i tvs) < 2 ** 64 /\
    type_memory_size (EL i tvs) + 64 < dimword (:256) /\
    source_base + off + SUM (MAP (type_memory_bytes ce) (TAKE i tys))
      < dimword (:256) /\
    (!x. vv_operand (EL i vvs) = Var x ==> not_fresh_at c_vvs x) /\
    (!l. vv_operand (EL i vvs) <> Label l) /\
    vv_holds ce cx (EL i tys) (EL i raws) (EL i vvs) es s /\
    vv_at ce cx (EL i tys) origin c_vvs es (EL i raws) (EL i vvs) s /\
    read_result cx (EL i raws) es = (INL (EL i values),es)) /\
  stmt_state_rel H ctx func ce cx es s /\
  storage_well_formed_on cx es (FST H) /\
  alloca_inv s /\ alloca_room ctx func s /\ fmp_room ctx func s /\
  FLOOKUP s.vs_allocas tuple_aid = SOME (source_base,source_cap) /\
  c_vvs.cs_next_id <= tuple_aid /\ tuple_aid < ca.cs_next_id /\
  off + SUM (MAP (type_memory_bytes ce) tys) <= source_cap /\
  source_base + source_cap <= s.vs_alloca_next /\
  (?inst. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
     inst.inst_id = tuple_aid) /\
  (!n b k. local_region ce es.scopes s n b k ==>
     source_base + source_cap <= b \/ b + k <= source_base) /\
  ~s.vs_halted /\ s.vs_current_bb = ca.cs_current_bb /\
  s.vs_inst_idx = LENGTH ca.cs_current_insts ==>
  ?q. gas_marked_path F ctx func s 0 (OK q) /\
    val_in_memory (TupleTV tvs) (ArrayV (TupleV values))
      (source_base + off) q.vs_memory /\
    eval_operand src q = SOME (n2w source_base) /\
    stmt_state_rel H ctx func ce cx es q /\
    alloca_inv q /\ alloca_room ctx func q /\ fmp_room ctx func q /\
    ~q.vs_halted /\ q.vs_current_bb = cb.cs_current_bb /\
    q.vs_inst_idx = LENGTH cb.cs_current_insts /\
    q.vs_accounts = s.vs_accounts /\ q.vs_transient = s.vs_transient /\
    q.vs_requests = s.vs_requests /\ q.vs_call_ctx = s.vs_call_ctx /\
    wb_frame ce es es c_vvs s q /\
    (!x w. not_fresh_at ca x /\ lookup_var x s = SOME w ==>
       lookup_var x q = SOME w) /\
    FLOOKUP q.vs_allocas tuple_aid = SOME (source_base,source_cap) /\
    source_base + source_cap <= q.vs_alloca_next /\
    mem_bytes_at source_base off q.vs_memory =
      mem_bytes_at source_base off s.vs_memory /\
    (!n b k. local_region ce es.scopes q n b k <=>
       local_region ce es.scopes s n b k) /\
    (!aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) /\
       aid < ca.cs_next_id /\
       (b + sz <= source_base \/ source_base + source_cap <= b) /\
       (!n p k. local_region ce es.scopes s n p k ==>
          b + sz <= p \/ p + k <= b) ==>
       mem_bytes_at b sz q.vs_memory = mem_bytes_at b sz s.vs_memory) /\
    (!ty' raw' vv' value'.
       vv_holds ce cx ty' raw' vv' es s /\
       vv_at ce cx ty' origin c_vvs es raw' vv' s /\
       read_result cx raw' es = (INL value',es) /\
       (!x. vv_operand vv' = Var x ==> not_fresh_at c_vvs x) /\
       (!l. vv_operand vv' <> Label l) ==>
       vv_holds ce cx ty' raw' vv' es q /\
       vv_at ce cx ty' origin c_vvs es raw' vv' q /\
       read_result cx raw' es = (INL value',es))
Proof
  map_every qid_spec_tac [`cb`,`s`,`ca`,`off`,`tys`,`raws`,`tvs`,`values`] >>
  Induct_on `vvs`
  >- (rpt gen_tac >> strip_tac >>
      gvs[compile_extcall_store_values_def, comp_return_def] >>
      qexists `s` >> simp[gas_marked_path_def, gas_path_rules,
        val_in_memory_tuple, valueEncodingDefsTheory.val_in_memory_def,
        wb_frame_def, locals_kept_refl]) >>
  rpt gen_tac >>
  namedCases_on `tys` ["", "ty remaining_tys"] >>
  namedCases_on `raws` ["", "raw remaining_raws"] >>
  namedCases_on `tvs` ["", "tv remaining_tvs"] >>
  namedCases_on `values` ["", "v remaining_values"] >>
  simp[] >> strip_tac >>
  qpat_x_assum `!values tvs raws tys off ca s cb. _` (mk_asm "ih") >>
  qpat_assum `!i. i < SUC (LENGTH remaining_tys) ==> _`
    (qspec_then `0` (strip_assume_tac o SIMP_RULE (srw_ss()) [])) >>
  qpat_x_assum `compile_extcall_store_values _ _ _ _ _ = _` mp_tac >>
  simp[Once compile_extcall_store_values_def, comp_bind_def, comp_ignore_bind_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  rename1 `emit_op ADD [src; Lit (n2w off)] ca = (dst,a1)` >>
  rename1 `unwrap_value ce h a1 = (op,a2)` >>
  rename1 `(if _ then _ else _) a2 = (r,a3)` >> Cases_on `r` >>
  `ci_mono ca a1 /\ ci_mono a1 a2 /\ ci_mono a2 a3` by
    (conj_tac >- metis_tac[ci_mono_emit_op, pairTheory.SND] >>
     conj_tac >- metis_tac[ci_mono_unwrap_value, pairTheory.SND] >>
     Cases_on `is_word_type ty` >> gvs[]
     >- metis_tac[ci_mono_emit_void, pairTheory.SND] >>
     Cases_on `is_bytestring_type ty` >> gvs[] >>
     metis_tac[ci_mono_emit_void, ci_mono_compile_store_bytestring, pairTheory.SND]) >>
  `cs_extends a3 cb` by
    (qpat_x_assum `compile_extcall_store_values _ _ _ _ a3 = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     metis_tac[externalEntryShapeTheory.compile_extcall_store_values_labels, pairTheory.SND]) >>
  `fn_has_code ca a3 func /\ fn_has_code a3 cb func` by
    (irule fragExecTheory.fn_has_code_split >> simp[] >>
     gvs[ci_mono_def] >> metis_tac[cs_extends_trans]) >>
  `off + type_memory_size tv <= source_cap` by gvs[] >>
  drule_at (Pat `emit_op _ _ _ = _`) ctor_delayed_slot_path >>
  disch_then (drule_at (Pat `unwrap_value _ _ _ = _`)) >>
  disch_then (drule_at (Pat `evaluate_type _ _ = _`)) >>
  disch_then (drule_at (Pat `vv_at _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `fn_has_code ca a3 _`)) >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `FLOOKUP _ _ = _`)) >>
  simp[] >>
  impl_tac >- (conj_tac >- metis_tac[] >> metis_tac[]) >>
  disch_then (qx_choose_then `u` strip_assume_tac) >>
  `c_vvs.cs_next_var <= a3.cs_next_var /\ c_vvs.cs_next_id <= a3.cs_next_id /\
   ca.cs_next_var <= a3.cs_next_var /\ ca.cs_next_id <= a3.cs_next_id` by
    gvs[ci_mono_def] >>
  `!x. src = Var x ==> not_fresh_at a3 x` by
    metis_tac[not_fresh_at_mono] >>
  asm_x "ih" (drule_at (Pat `compile_extcall_store_values _ _ _ _ a3 = _`)) >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _ u`)) >>
  disch_then (drule_at (Pat `fn_has_code a3 cb _`)) >>
  simp[] >>
  disch_then (qspecl_then [`remaining_values`,`remaining_tvs`,`remaining_raws`] mp_tac) >>
  impl_tac
  >- (simp[] >> conj_tac
      >- (qx_gen_tac `i` >> strip_tac >>
          qpat_x_assum `!i. i < SUC (LENGTH remaining_tys) ==> _`
            (qspec_then `SUC i` mp_tac) >>
          simp[TAKE_def] >> strip_tac >>
          gvs[] >> metis_tac[]) >>
      conj_tac >- metis_tac[] >> metis_tac[]) >>
  disch_then (qx_choose_then `q` strip_assume_tac) >>
  `mem_bytes_at (source_base + off) (type_memory_size tv) q.vs_memory =
   mem_bytes_at (source_base + off) (type_memory_size tv) u.vs_memory` by
    (qpat_assum `mem_bytes_at source_base (off + _) q.vs_memory = _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> strip_tac >>
     drule valueEncodingPropsTheory.mem_bytes_at_translated_window >>
     disch_then (qspecl_then [`off`,`type_memory_size tv`] mp_tac) >> simp[]) >>
  `val_in_memory tv v (source_base + off) q.vs_memory` by
    (irule val_in_memory_mem_agree >> simp[] >>
     qexistsl [`type_memory_size tv`,`u.vs_memory`] >> gvs[]) >>
  `wb_frame ce es es c_vvs s q` by
    (irule exprSimWordArgsTheory.wb_frame_trans >> simp[] >>
     conj_tac >- (qexistsl [`es`,`c_vvs`,`u`] >> simp[]) >> metis_tac[]) >>
  qexists `q` >> simp[] >>
  conj_tac >- metis_tac[gas_marked_path_then, ADD_CLAUSES] >>
  conj_tac
  >- (gvs[val_in_memory_tuple, valueEncodingDefsTheory.val_in_memory_def]) >>
  conj_tac >- metis_tac[not_fresh_at_mono] >>
  conj_tac
  >- (`mem_bytes_at source_base off q.vs_memory =
         mem_bytes_at source_base off u.vs_memory` by
        (qpat_assum `mem_bytes_at source_base (off + _) q.vs_memory = _` mp_tac >>
         POP_ASSUM_LIST (K ALL_TAC) >> strip_tac >>
         drule valueEncodingPropsTheory.mem_bytes_at_translated_window >>
         disch_then (qspecl_then [`0`,`off`] mp_tac) >> simp[]) >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  `FLOOKUP u.vs_allocas aid = SOME (b,sz)` by
    (qpat_assum `wb_frame ce es es c_vvs s u` mp_tac >>
     pure_rewrite_tac[wb_frame_def] >> strip_tac >> metis_tac[]) >>
  `mem_bytes_at b sz q.vs_memory = mem_bytes_at b sz u.vs_memory` by
    (qpat_x_assum `!aid b sz. FLOOKUP u.vs_allocas aid = _ /\ _ ==> _` irule >>
     metis_tac[LESS_LESS_EQ_TRANS]) >>
  `mem_bytes_at b sz u.vs_memory = mem_bytes_at b sz s.vs_memory` by
    (qpat_x_assum `!aid b sz. FLOOKUP s.vs_allocas aid = _ /\ _ ==> _` irule >>
     metis_tac[]) >> simp[]
QED
