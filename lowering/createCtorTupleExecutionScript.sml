(* Actual constructor argument capture and delayed physical tuple staging.
   The representative window includes the source-typed fixed Bytes[0] boundary. *)
Theory createCtorTupleExecution
Ancestors
  createCtorTupleStaging createCtorTupleCaptureAssembly
  vyperEvalExprPreservesScopesDom
  exprLowering context exprLoweringProps exprSimProps loweringPosts
  loweringStateRelDefs fragGasMode fragGasPath fragExec freshWrites
  vyperState vyperTyping vyperValue vyperMisc vyperTypeDefaults
  valueEncoding valueEncodingProps compileEnv
  venomState venomExecSemantics
  list rich_list arithmetic words finite_map

(* The common indexed interface for the two supported argument domains. *)
Theorem ctor_tuple_capture_domain[local]:
  (LENGTH args = 1 \/ EVERY (\e. ~expr_has_effect e) args) /\
  expr_sim_inv ce cx env es /\
  (!e ea. MEM e args /\ expr_sim_inv ce cx env ea ==>
    expr_body_pre ce cx env e ea /\
    expr_vv_sim ctx func ce cx (expr_type e) e ea /\
    gas_admissible (eval_expr cx e) expr_vv_res_ok ea) /\
  compile_multi_vvs compile_expr ce args c1 = (vvs,c_vvs) /\
  fn_has_code c1 c_vvs func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce c1 /\ ci_mono c1 c_vvs /\
  (!e ca cb vv. MEM e args /\
    compile_expr ce (expr_type e) e ca = (vv,cb) ==>
    (!x. vv_operand vv = Var x ==> not_fresh_at cb x) /\
    (!l. vv_operand vv <> Label l)) /\
  (!ty tv. evaluate_type (get_tenv cx) ty = SOME tv ==>
    type_memory_bytes ce ty = type_memory_size tv) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func ce cx es s_buf /\
    storage_well_formed_on cx es (FST H)) /\
  ~s_buf.vs_halted /\
  s_buf.vs_current_bb = c1.cs_current_bb /\
  s_buf.vs_inst_idx = LENGTH c1.cs_current_insts ==>
  ?marks. !tail raws values ee H.
    eval_expr_results cx args
      (es with gas_obs := gas_explicit marks s_buf.vs_gas_readings ++ tail) =
        (INL raws,ee) /\
    read_results cx raws ee = (INL values,ee) /\
    valid_horizon cx st0 H ee.storage_trace ==>
    ?t. gas_marked_path F ctx func s_buf (LENGTH marks) (OK t) /\
      gas_marked_exec F (ctx,func)
        (bind (eval_expr_results cx args)
          (\raws. bind (read_results cx raws) (\values. return (raws,values))))
        (es,s_buf) marks (INL (raws,values)) (ee with gas_obs := []) (OK t) /\
      ee.gas_obs = tail /\
      LENGTH vvs = LENGTH args /\
      LENGTH raws = LENGTH args /\ LENGTH values = LENGTH args /\
      (!i. i < LENGTH args ==>
        vv_holds ce cx (lowered_value_type ce (EL i args))
          (EL i raws) (EL i vvs) (ee with gas_obs := []) t /\
        vv_at ce cx (lowered_value_type ce (EL i args)) c1 c_vvs
          (ee with gas_obs := []) (EL i raws) (EL i vvs) t /\
        read_result cx (EL i raws) (ee with gas_obs := []) =
          (INL (EL i values),ee with gas_obs := []) /\
        (?tv. evaluate_type (get_tenv cx) (lowered_value_type ce (EL i args)) = SOME tv /\
          value_has_type tv (EL i values) /\ val_wf tv (EL i values) /\
          type_memory_bytes ce (lowered_value_type ce (EL i args)) = type_memory_size tv) /\
        (!x. vv_operand (EL i vvs) = Var x ==> not_fresh_at c_vvs x) /\
        (!l. vv_operand (EL i vvs) <> Label l)) /\
      stmt_state_rel H ctx func ce cx (ee with gas_obs := []) t /\
      storage_well_formed_on cx (ee with gas_obs := []) (FST H) /\
      alloca_inv t /\ alloca_room ctx func t /\ local_ptrs_reserved ce c_vvs /\
      t.vs_current_bb = c_vvs.cs_current_bb /\
      t.vs_inst_idx = LENGTH c_vvs.cs_current_insts /\
      (!x w. not_fresh_at c1 x /\ lookup_var x s_buf = SOME w ==>
        lookup_var x t = SOME w) /\
      (!aid b. FLOOKUP s_buf.vs_allocas aid = SOME b ==>
        FLOOKUP t.vs_allocas aid = SOME b) /\
      (!aid off sz. FLOOKUP s_buf.vs_allocas aid = SOME (off,sz) /\
        aid < c1.cs_next_id /\
        (!n b sz'. local_region ce es.scopes s_buf n b sz' ==>
          off + sz <= b \/ b + sz' <= off) ==>
        mem_bytes_at off sz t.vs_memory = mem_bytes_at off sz s_buf.vs_memory)
Proof
  disch_tac >> Cases_on `EVERY (\e. ~expr_has_effect e) args`
  >- (irule compile_multi_vvs_pure_capture >> gvs[] >> metis_tac[]) >>
  gvs[] >>
  Cases_on `args` >> gvs[] >>
  rename1 `compile_multi_vvs compile_expr ce [e] c1 = (vvs,c_vvs)` >>
  `?vv. vvs = [vv] /\ compile_expr ce (expr_type e) e c1 = (vv,c_vvs)` by
    (Cases_on `compile_expr ce (expr_type e) e c1` >>
     gvs[compile_multi_vvs_def, comp_bind_def, comp_return_def]) >>
  gvs[] >>
  `expr_body_pre ce cx env e es /\
   expr_vv_sim ctx func ce cx (expr_type e) e es /\
   gas_admissible (eval_expr cx e) expr_vv_res_ok es` by metis_tac[] >>
  `(!x. vv_operand vv = Var x ==> not_fresh_at c_vvs x) /\
   (!l. vv_operand vv <> Label l)` by metis_tac[] >>
  drule_all compile_multi_vvs_singleton_capture >> strip_tac >>
  qexists `marks` >> rpt strip_tac >>
  qpat_x_assum `!tail raws values ee H. _`
    (qspecl_then [`tail`,`raws`,`values`,`ee`,`H`] mp_tac) >>
  simp[] >> strip_tac >> gvs[] >> qexists `t` >> simp[] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

(* Whole-helper producer.  The two compiler cut equations merely name the
   capture and allocation cursors; the delayed-store equation follows from
   the actual compile_create_ctor_tuple equation.  All target paths are
   conclusions, never premises. *)
Theorem compile_create_ctor_tuple_correct:
  compile_create_ctor_tuple compile_expr ce args c1 = (src,c2) /\
  compile_multi_vvs compile_expr ce args c1 = (vvs,c_vvs) /\
  compile_alloc_buffer
    (type_memory_bytes ce (TupleT (MAP (lowered_value_type ce) args)))
    c_vvs = (buf,c_alloc) /\
  (LENGTH args = 1 \/ EVERY (\e. ~expr_has_effect e) args) /\
  expr_sim_inv ce cx env es /\
  (!e ea. MEM e args /\ expr_sim_inv ce cx env ea ==>
    expr_body_pre ce cx env e ea /\
    expr_vv_sim ctx func ce cx (expr_type e) e ea /\
    gas_admissible (eval_expr cx e) expr_vv_res_ok ea) /\
  fn_has_code c1 c_vvs func /\ fn_has_code c_vvs c_alloc func /\
  fn_has_code c_alloc c2 func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce c1 /\ ci_mono c1 c_vvs /\
  local_ptrs_rel func ce es.scopes s_buf /\
  (!e ca cb vv. MEM e args /\
    compile_expr ce (expr_type e) e ca = (vv,cb) ==>
    (!x. vv_operand vv = Var x ==> not_fresh_at cb x) /\
    (!l. vv_operand vv <> Label l)) /\
  sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
  (!ty tv. evaluate_type (get_tenv cx) ty = SOME tv ==>
    type_memory_bytes ce ty = type_memory_size tv) /\
  type_memory_bytes ce (TupleT (MAP (lowered_value_type ce) args)) < dimword (:256) /\
  LENGTH tvs = LENGTH args /\
  (!i. i < LENGTH args ==>
    evaluate_type (get_tenv cx) (lowered_value_type ce (EL i args)) = SOME (EL i tvs) /\
    type_memory_size (EL i tvs) < 2 ** 64 /\
    type_memory_size (EL i tvs) + 64 < dimword (:256)) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func ce cx es s_buf /\
    storage_well_formed_on cx es (FST H)) /\
  ~s_buf.vs_halted /\ s_buf.vs_current_bb = c1.cs_current_bb /\
  s_buf.vs_inst_idx = LENGTH c1.cs_current_insts ==>
  ?marks. !tail raws values ee H av.
    eval_expr_results cx args
      (es with gas_obs := gas_explicit marks s_buf.vs_gas_readings ++ tail) =
        (INL raws,ee) /\
    read_results cx raws ee = (INL values,ee) /\
    valid_horizon cx st0 H ee.storage_trace /\
    vyper_to_abi (get_tenv cx) (TupleT (MAP (lowered_value_type ce) args))
      (ArrayV (TupleV values)) = SOME av ==>
    ?s_vvs s_tup source_base source_cap ct rv.
      gas_marked_path F ctx func s_buf (LENGTH marks) (OK s_vvs) /\
      gas_marked_path F ctx func s_vvs 0 (OK s_tup) /\
      gas_marked_path F ctx func s_buf (LENGTH marks) (OK s_tup) /\
      gas_marked_exec F (ctx,func)
        (bind (eval_expr_results cx args)
          (\raws. bind (read_results cx raws) (\values. return (raws,values))))
        (es,s_buf) marks (INL (raws,values)) (ee with gas_obs := []) (OK s_vvs) /\
      ee.gas_obs = tail /\
      LENGTH vvs = LENGTH args /\ LENGTH raws = LENGTH args /\ LENGTH values = LENGTH args /\
      (!i. i < LENGTH args ==>
        vv_holds ce cx (lowered_value_type ce (EL i args))
          (EL i raws) (EL i vvs) (ee with gas_obs := []) s_vvs /\
        vv_at ce cx (lowered_value_type ce (EL i args)) c1 c_vvs
          (ee with gas_obs := []) (EL i raws) (EL i vvs) s_vvs /\
        read_result cx (EL i raws) (ee with gas_obs := []) =
          (INL (EL i values),ee with gas_obs := [])) /\
      stmt_state_rel H ctx func ce cx (ee with gas_obs := []) s_vvs /\
      storage_well_formed_on cx (ee with gas_obs := []) (FST H) /\
      ~s_vvs.vs_halted /\ s_vvs.vs_current_bb = c_vvs.cs_current_bb /\
      s_vvs.vs_inst_idx = LENGTH c_vvs.cs_current_insts /\
      eval_operand src s_tup = SOME (n2w source_base) /\
      source_cap = type_memory_bytes ce (TupleT (MAP (lowered_value_type ce) args)) /\
      evaluate_type (get_tenv cx) (TupleT (MAP (lowered_value_type ce) args)) =
        SOME (TupleTV tvs) /\
      value_has_type (TupleTV tvs) (ArrayV (TupleV values)) /\
      val_in_memory (TupleTV tvs) (ArrayV (TupleV values)) source_base s_tup.vs_memory /\
      abi_encoder_window_input
        (type_to_abi_enc_info ce.ce_struct_fields ce (TupleT (MAP (lowered_value_type ce) args)))
        ct rv source_base source_cap s_tup.vs_memory /\
      enc ct rv = enc (vyper_to_abi_type (get_tenv cx)
        (TupleT (MAP (lowered_value_type ce) args))) av /\
      source_rep (get_tenv cx) (TupleT (MAP (lowered_value_type ce) args))
        (type_to_abi_enc_info ce.ce_struct_fields ce (TupleT (MAP (lowered_value_type ce) args))) ct /\
      stmt_state_rel H ctx func ce cx (ee with gas_obs := []) s_tup /\
      alloca_inv s_tup /\ alloca_room ctx func s_tup /\ fmp_room ctx func s_tup /\
      ~s_tup.vs_halted /\ s_tup.vs_current_bb = c2.cs_current_bb /\
      s_tup.vs_inst_idx = LENGTH c2.cs_current_insts /\
      FLOOKUP s_tup.vs_allocas c_vvs.cs_next_id = SOME (source_base,source_cap) /\
      source_base + source_cap <= s_tup.vs_alloca_next /\
      wb_frame ce (ee with gas_obs := []) (ee with gas_obs := []) c_vvs s_vvs s_tup /\
      s_tup.vs_accounts = s_vvs.vs_accounts /\
      s_tup.vs_transient = s_vvs.vs_transient /\
      s_tup.vs_requests = s_vvs.vs_requests /\ s_tup.vs_call_ctx = s_vvs.vs_call_ctx /\
      (!n b k. local_region ce ee.scopes s_tup n b k <=>
        local_region ce es.scopes s_buf n b k) /\
      (!aid row. FLOOKUP s_buf.vs_allocas aid = SOME row ==>
        FLOOKUP s_tup.vs_allocas aid = SOME row) /\
      (!aid b k. aid < c1.cs_next_id /\ FLOOKUP s_buf.vs_allocas aid = SOME (b,k) ==>
        source_base + source_cap <= b \/ b + k <= source_base) /\
      (!n b k. local_region ce ee.scopes s_tup n b k ==>
        source_base + source_cap <= b \/ b + k <= source_base) /\
      (!aid b k. aid < c1.cs_next_id /\ FLOOKUP s_buf.vs_allocas aid = SOME (b,k) /\
        (!n p len. local_region ce es.scopes s_buf n p len ==>
          b + k <= p \/ p + len <= b) ==>
        mem_bytes_at b k s_tup.vs_memory = mem_bytes_at b k s_buf.vs_memory) /\
      (!x w. not_fresh_at c1 x /\ lookup_var x s_buf = SOME w ==>
        lookup_var x s_tup = SOME w)
Proof
  disch_tac >>
  rpt (qpat_x_assum `_ /\ _` (CONJUNCTS_THEN assume_tac)) >>
  drule_all ctor_tuple_capture_domain >> strip_tac >>
  qexists `marks` >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `!tail raws values ee H. _`
    (qspecl_then [`tail`,`raws`,`values`,`ee`,`H`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  `src = buf.buf_operand /\
   compile_extcall_store_values ce
     (ZIP (vvs,MAP (lowered_value_type ce) args)) src 0 c_alloc = ((),c2)` by
    (Cases_on `compile_extcall_store_values ce
       (ZIP (vvs,MAP (lowered_value_type ce) args)) buf.buf_operand 0 c_alloc` >>
     gvs[compile_create_ctor_tuple_def, comp_bind_def, comp_ignore_bind_def, comp_return_def]) >>
  `~t.vs_halted` by metis_tac[gas_marked_path_exec, gas_path_normal] >>
  `c1.cs_next_var <= c_vvs.cs_next_var /\ c1.cs_next_id <= c_vvs.cs_next_id` by
    gvs[ci_mono_def] >>
  `!i. i < LENGTH (MAP (lowered_value_type ce) args) ==>
    evaluate_type (get_tenv cx) (EL i (MAP (lowered_value_type ce) args)) = SOME (EL i tvs) /\
    value_has_type (EL i tvs) (EL i values) /\ val_wf (EL i tvs) (EL i values) /\
    type_memory_bytes ce (EL i (MAP (lowered_value_type ce) args)) = type_memory_size (EL i tvs) /\
    type_memory_size (EL i tvs) < 2 ** 64 /\ type_memory_size (EL i tvs) + 64 < dimword (:256) /\
    (!x. vv_operand (EL i vvs) = Var x ==> not_fresh_at c_vvs x) /\
    (!l. vv_operand (EL i vvs) <> Label l) /\
    vv_holds ce cx (EL i (MAP (lowered_value_type ce) args)) (EL i raws) (EL i vvs)
      (ee with gas_obs := []) t /\
    vv_at ce cx (EL i (MAP (lowered_value_type ce) args)) c1 c_vvs (ee with gas_obs := [])
      (EL i raws) (EL i vvs) t /\
    read_result cx (EL i raws) (ee with gas_obs := []) = (INL (EL i values),ee with gas_obs := [])` by
    (simp[EL_MAP] >> metis_tac[optionTheory.SOME_11]) >>
  `LENGTH vvs = LENGTH (MAP (lowered_value_type ce) args) /\
   LENGTH raws = LENGTH (MAP (lowered_value_type ce) args) /\
   LENGTH values = LENGTH (MAP (lowered_value_type ce) args) /\
   LENGTH tvs = LENGTH (MAP (lowered_value_type ce) args)` by simp[] >>
  drule_all ctor_tuple_stage2_correct >> strip_tac >>
  `gas_marked_path F ctx func s_buf (LENGTH marks) (OK s_tup)` by
    metis_tac[gas_marked_path_then, ADD_0] >>
  `MAP FDOM es.scopes = MAP FDOM ee.scopes` by
    (drule eval_expr_results_preserves_scopes_dom >> simp[]) >>
  `!n b k. local_region ce ee.scopes t n b k <=>
    local_region ce es.scopes s_buf n b k` by
    (rpt gen_tac >> eq_tac >> strip_tac
     >- (drule_all local_region_frame >> simp[])
     >> drule_all local_region_frame_fwd >> simp[]) >>
  `evaluate_type (get_tenv cx) (TupleT (MAP (lowered_value_type ce) args)) =
     SOME (TupleTV tvs) /\
   value_has_type (TupleTV tvs) (ArrayV (TupleV values))` by
    suspend "tuple_typing" >>
  qexistsl [`t`,`s_tup`,`source_base`,`source_cap`,`ct`,`rv`] >>
  suspend "endpoint_frames"
QED

Resume compile_create_ctor_tuple_correct[tuple_typing]:
  `OPT_MMAP (evaluate_type (get_tenv cx)) (MAP (lowered_value_type ce) args) = SOME tvs` by
    (simp[OPT_MMAP_SOME_IFF, EVERY_EL, EL_MAP, LIST_EQ_REWRITE] >>
     metis_tac[]) >>
  `MAP (type_memory_bytes ce) (MAP (lowered_value_type ce) args) = MAP type_memory_size tvs` by
    (irule LIST_EQ >> simp[EL_MAP] >> metis_tac[]) >>
  `type_memory_bytes ce (TupleT (MAP (lowered_value_type ce) args)) = type_memory_size (TupleTV tvs)` by
    simp[type_memory_bytes_def, type_memory_size_def,
         valueEncodingProofsTheory.type_memory_size_list_sum] >>
  `type_slot_size (TupleTV tvs) <= dimword (:256)` by
    (qpat_x_assum `type_memory_bytes ce (TupleT _) < _` mp_tac >>
     simp[type_memory_size_slots] >> decide_tac) >>
  conj_tac >- simp[Once evaluate_type_def, evaluate_types_OPT_MMAP] >>
  simp[value_has_type_def, values_have_types_LIST_REL, LIST_REL_EL_EQN] >>
  metis_tac[]
QED

Resume compile_create_ctor_tuple_correct[endpoint_frames]:
  qpat_x_assum `!n b k. local_region _ _ s_tup n b k <=> _`
    (assume_tac o SRULE []) >>
  simp[] >>
  conj_tac >- (rpt strip_tac >>
    `aid < c_vvs.cs_next_id` by decide_tac >>
    `FLOOKUP t.vs_allocas aid = SOME (b,k)` by metis_tac[] >>
    qpat_x_assum `!aid b k. _ ==> _ \/ _`
      (qspecl_then [`aid`,`b`,`k`] mp_tac) >> simp[]) >>
  conj_tac >- (rpt strip_tac >>
    qpat_x_assum `!n b k. _ ==> _ \/ _`
      (qspecl_then [`n`,`b`,`k`] mp_tac) >> simp[]) >>
  conj_tac >- (rpt strip_tac >>
    `aid < c_vvs.cs_next_id` by decide_tac >>
    `mem_bytes_at b k s_tup.vs_memory = mem_bytes_at b k t.vs_memory` by
      (qpat_x_assum `!aid b k. _ ==> mem_bytes_at b k s_tup.vs_memory = _` irule >>
       conj_tac >- (simp[] >> metis_tac[]) >>
       qexists `aid` >> simp[] >> metis_tac[]) >>
    simp[] >>
    qpat_x_assum `!aid off sz. _ ==> mem_bytes_at off sz t.vs_memory = _` irule >>
    conj_tac >- metis_tac[ADD_COMM] >> qexists `aid` >> simp[]) >>
  metis_tac[not_fresh_at_mono]
QED

Finalise compile_create_ctor_tuple_correct

(* Consumer audit: instantiate dallocaBlueprintArgsTheory.
   create_blueprint_encoded_args_representative_prefix with
   tenv = get_tenv cx and v = ArrayV (TupleV values).  The whole-helper
   export supplies evaluated tuple typing, conversion, encoding equality,
   source window, cursor, allocation extent and all older register values.
   In particular the captured blueprint code register and outer encoder
   buffer survive whenever they are not_fresh_at c1.

   createCtorTupleWindowTheory.ctor_tuple_encoder_pre_resources combines
   those source facts with the consumer's separate ordinary resources:
   destination operand/extent, source-destination disjointness, encoder
   code/distinctness/operand age, and every registered 32-byte encoder
   scratch slot disjoint from both windows.  These destination and scratch
   obligations are not inferred from abi_encoder_window_input.  The
   consumer also retains its ABI-size bound and compiler monotonicity
   premises; neither is silently inferred here.  The canonical encoder
   theorem is unchanged, and the representative type ct is not forced to
   the literal source ABI type (so fixed Bytes[0] remains included). *)
