(* The completed StructLit's result stays in the original allocation. *)
Theory bodyStructResultMemoryMods
Ancestors
  bodyStructFieldCutsMods bodyFullPostsMods bodyPtrDefs exprSimProps
  exprSimAggregateLayout exprSimAggregateSource
  exprSimHyps exprSimUnwrapProps exprSimMemorySource
  bodyFullHashKeccakFixed stateRelProj allocaSiteResource
  vyperTypeEvalCaseProofs valueEncodingTyping valueEncoding vyperTyping
  gasShadowCompile gasShadowState gasOutcomeFullBindMods gasOutcomeFullPostMods
  gasExemptCertMods haltExitProj stmtSimProps
  vyperStorageTrace vyperStorageFootprint exprSimMemDefs exprSimDefs
  ptrDiscipline loweringPosts loweringStateRelDefs exprLoweringProps
  exprLowering compileEnv context vyperInterpreter vyperState vyperAST
  venomState words list fragGasOriginPtr
Libs monadsyntax

Triviality struct_value_layout:
  LENGTH kes = LENGTH tvs /\ LIST_REL value_has_type tvs vs ==>
  val_wf (StructTV (ZIP (MAP FST kes,tvs))) (StructV (ZIP (MAP FST kes,vs))) /\
  type_memory_size (StructTV (ZIP (MAP FST kes,tvs))) = type_memory_size_list tvs
Proof
  strip_tac >> conj_tac
  >- (irule (cj 1 value_has_type_val_wf) >> simp[value_has_type_def] >>
      irule struct_has_type_zip_same_names_stmt >> simp[] >>
      metis_tac[LIST_REL_LENGTH]) >>
  simp[type_memory_size_def, struct_layout_size_zip]
QED

Theorem struct_result_vv_post_mods:
  ba.buf_operand = Var root /\
  evaluate_type (get_tenv cx) (StructT nsid) = SOME (StructTV (ZIP (MAP FST kes,tvs))) /\
  LENGTH kes = LENGTH tvs /\ LIST_REL value_has_type tvs vs /\
  type_memory_bytes ce (StructT nsid) = type_memory_size_list tvs /\
  struct_prefix_mods (ctx,func,ce,cx,lo,d,~expr_has_effect (StructLit (StructT nsid) nsid kes))
    (es,sa,s0,G0,tn0) (root,addr,type_memory_size_list tvs,aid)
    (H,D,ee,sb,G,tn,s) cells (type_memory_size_list tvs) /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    fields_in_memory (ZIP (MAP FST kes,vs)) (ZIP (MAP FST kes,tvs)) addr m) ==>
  vv_post_mods H ctx func ce cx (StructLit (StructT nsid) nsid kes) es sa sb s0 ee
    (Value (StructV (ZIP (MAP FST kes,vs)))) (LocatedValue (StructT nsid) (base_ptr ba)) s /\
  vv_store_bound cx (StructT nsid) (StructT nsid) ee
    (Value (StructV (ZIP (MAP FST kes,vs)))) (LocatedValue (StructT nsid) (base_ptr ba)) s /\
  ptr_vv_ok cx (StructT nsid) (Value (StructV (ZIP (MAP FST kes,vs))))
    (LocatedValue (StructT nsid) (base_ptr ba)) ee G tn s /\
  vv_own ce cx (StructT nsid) sa sb ee (Value (StructV (ZIP (MAP FST kes,vs))))
    (LocatedValue (StructT nsid) (base_ptr ba)) s /\
  ptr_buf_ok ce (StructLit (StructT nsid) nsid kes) ba.buf_operand G s
Proof
  strip_tac >> drule_all_then strip_assume_tac struct_value_layout >>
  qpat_x_assum `struct_prefix_mods _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [struct_prefix_mods_def]) >>
  qabbrev_tac `v = StructV (ZIP (MAP FST kes,vs))` >>
  qabbrev_tac `tv = StructTV (ZIP (MAP FST kes,tvs))` >>
  `!m. mem_agree_outside tn.t_mem s.vs_memory m ==> val_in_memory tv v addr m` by
    simp[Abbr `v`, Abbr `tv`, valueEncodingDefsTheory.val_in_memory_def] >>
  `val_in_memory tv v addr s.vs_memory` by
    (first_x_assum irule >> simp[mem_agree_outside_def]) >>
  `val_footprint tv v <= type_memory_size_list tvs` by
    metis_tac[val_footprint_le] >>
  `w2n ((n2w addr):bytes32) = addr` by
    (simp[w2n_n2w] >> decide_tac) >>
  `addr + type_memory_size_list tvs <= s.vs_alloca_next` by
    (drule_then strip_assume_tac stmt_state_rel_local_ptrs_alloca >>
     drule_all_then assume_tac alloca_site_registered_below >> simp[]) >>
  conj_tac
  >- (simp[vv_post_mods_def, vv_holds_mods_def, vv_holds_def, vv_at_def,
            vv_place_ptr_mods_def, vv_place_ptr_def, post_value_type_def, expr_type_def,
            base_ptr_def, is_word_type_def, read_result_def, return_def, eval_operand_def] >>
      fs[wb_frame_def] >> reverse conj_tac >- first_assum ACCEPT_TAC >>
      disj1_tac >> qexistsl_tac [`aid`,`addr`,`type_memory_size_list tvs`] >>
      simp[] >> rpt strip_tac >>
      qpat_assum `!n p k. local_region ce ee.scopes s n p k ==> _`
        (drule_then mp_tac) >> decide_tac) >>
  `val_store_size tv v = type_memory_size_list tvs` by
    simp[Abbr `v`, val_store_size_def] >>
  conj_tac
  >- (simp[vv_store_bound_def, base_ptr_def, is_word_type_def,
           read_result_def, return_def, eval_operand_def] >>
      rpt strip_tac >> gvs[]) >>
  conj_tac
  >- (simp[ptr_vv_ok_def, ptr_mem_ok_def, base_ptr_def, is_word_type_def,
           read_result_def, return_def, eval_operand_def] >>
      gvs[ptr_covers_def]) >>
  conj_tac
  >- (simp[vv_own_def, base_ptr_def, read_result_def, return_def, eval_operand_def] >>
      disj1_tac >> qexistsl_tac [`aid`,`addr`,`type_memory_size_list tvs`] >>
      simp[] >> rpt strip_tac >>
      qpat_assum `!n p k. local_region ce ee.scopes s n p k ==> _`
        (drule_then mp_tac) >> decide_tac) >>
  gvs[ptr_buf_ok_def, ptr_covers_def, lowered_value_type_def, expr_type_def,
      eval_operand_def] >> decide_tac
QED

Triviality struct_literal_unwrap:
  compile_expr ce ty (StructLit (StructT nsid) nsid kes) sa = (vv,sm) /\
  lower_value compile_expr ce ty (StructLit (StructT nsid) nsid kes) sa = (op,sb) ==>
  ?p. vv = LocatedValue (StructT nsid) p /\ p.ptr_operand = op /\
      p.ptr_location = LocMemory /\ sm = sb
Proof
  strip_tac >> drule_then strip_assume_tac compile_struct_literal_inv >>
  qexists_tac `base_ptr ba` >> simp[expr_type_def, base_ptr_def] >>
  `lower_value compile_expr ce ty (StructLit (StructT nsid) nsid kes) sa =
     (ba.buf_operand,sm)` by
    (gvs[expr_type_def] >> drule lower_value_nonword_memory >>
     simp[base_ptr_def, is_word_type_def]) >>
  gvs[]
QED

Triviality struct_literal_compiled_value:
  lower_value compile_expr ce ty (StructLit (StructT nsid) nsid kes) sa = (op,sb) /\
  lower_value compile_expr (gas_shadow_env T ce) ty
    (gas_shadow_expr (StructLit (StructT nsid) nsid kes)) shadow_sa = (op,shadow_sb) /\
  gas_shadow_state sa shadow_sa ==>
  ?p. compile_expr ce ty (StructLit (StructT nsid) nsid kes) sa =
        (LocatedValue (StructT nsid) p,sb) /\
      compile_expr (gas_shadow_env T ce) ty
        (gas_shadow_expr (StructLit (StructT nsid) nsid kes)) shadow_sa =
        (LocatedValue (StructT nsid) p,shadow_sb) /\
      p.ptr_operand = op /\ p.ptr_location = LocMemory
Proof
  strip_tac >> Cases_on `compile_expr ce ty (StructLit (StructT nsid) nsid kes) sa` >>
  drule_all_then strip_assume_tac struct_literal_unwrap >> gvs[] >>
  `gas_shadow_compiles (compile_expr ce ty (StructLit (StructT nsid) nsid kes))
    (compile_expr (gas_shadow_env T ce) ty (gas_shadow_expr (StructLit (StructT nsid) nsid kes)))` by
    irule (cj 1 gas_shadow_compile_expr_env |> SPEC_ALL |>
           Q.INST [`shadow` |-> `T`] |> REWRITE_RULE [COND_CLAUSES]) >>
  qpat_x_assum `gas_shadow_compiles _ _`
    (qspecl_then [`sa`,`shadow_sa`] mp_tac o REWRITE_RULE [gas_shadow_compiles_def]) >>
  Cases_on `compile_expr (gas_shadow_env T ce) ty
    (gas_shadow_expr (StructLit (StructT nsid) nsid kes)) shadow_sa` >>
  simp[] >> strip_tac >> gvs[] >>
  qpat_assum `compile_expr _ _ (gas_shadow_expr _) _ = _`
    (fn th => mp_tac (MATCH_MP (ONCE_REWRITE_RULE [GSYM AND_IMP_INTRO]
      lower_value_nonword_memory) th)) >> simp[is_word_type_def]
QED

Triviality struct_literal_eval_value:
  eval_expr cx (StructLit ann nsid kes) es = (INL tv,ee) ==>
  ?v. tv = Value v
Proof
  Cases_on `eval_exprs cx (MAP SND kes) es` >>
  drule_then assume_tac aggregate_eval_struct >>
  Cases_on `q` >> gvs[] >> strip_tac >> gvs[]
QED

Triviality struct_literal_read_post:
  p.ptr_location = LocMemory /\
  vv_post_mods H ctx func ce cx (StructLit (StructT nsid) nsid kes) es sa sb s0 ee
    (Value v) (LocatedValue (StructT nsid) p) u /\
  vv_store_bound cx (StructT nsid) (StructT nsid) ee
    (Value v) (LocatedValue (StructT nsid) p) u /\
  ptr_vv_ok cx (StructT nsid) (Value v) (LocatedValue (StructT nsid) p) ee G tn u ==>
  expr_post_mods H ctx func ce cx (StructLit (StructT nsid) nsid kes) es sa sb s0 ee
    v p.ptr_operand u /\
  expr_store_bound cx (StructT nsid) v p.ptr_operand u /\
  ptr_val_ok cx (StructT nsid) v p.ptr_operand G tn u
Proof
  simp[ptr_val_ok_def, ptr_vv_ok_def, vv_store_bound_def, expr_store_bound_def,
       is_word_type_def, read_result_def, return_def] >> strip_tac >>
  qpat_x_assum `vv_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o PURE_REWRITE_RULE [vv_post_mods_def]) >>
  simp[expr_post_mods_def] >>
  irule expr_post_of_vv_post_memory >> simp[] >> qexists_tac `StructT nsid` >>
  simp[is_word_type_def, vv_post_def] >>
  gvs[vv_place_ptr_mods_def, vv_place_ptr_def, vv_holds_mods_def] >>
  first_assum ACCEPT_TAC
QED

(* The source read is return on the literal's successful Value. Its
   compiled counterpart keeps the buffer operand and emits no instructions. *)
Theorem struct_literal_value_of_memory_vv_mods:
  expr_vv_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    ce cx ty (StructLit (StructT nsid) nsid kes) es ==>
  expr_sim_full_mods (DF,lo,d,ctx,shadow_ctx,PG,func,shadow_func)
    ce cx ty (StructLit (StructT nsid) nsid kes) es
Proof
  strip_tac >> rewrite_tac[expr_sim_full_mods_def] >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all_then (qx_choose_then `p` strip_assume_tac) struct_literal_compiled_value >>
  drule_then assume_tac forced_expr_admissible_raw >>
  qpat_x_assum `expr_vv_sim_full_mods _ _ _ _ _ _`
    (qspecl_then [`st0`,`sa`,`sb`,`shadow_sa`,`shadow_sb`,
                  `LocatedValue (StructT nsid) p`,`s0`,`G0`,`tn0`] mp_tac o
     REWRITE_RULE [expr_vv_sim_full_mods_def]) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> strip_tac >>
  qmatch_asmsub_abbrev_tac `gas_outcome_full_mods _ _ _ _ _ _ childQ childR` >>
  irule gas_outcome_full_mods_bind_all >> BETA_TAC >> rpt conj_tac
  >~ [`gas_marked_exec _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >>
      rename1 `gas_marked_exec _ _ _ _ _ (INL reached) mid (OK mid_state)` >>
      irule gas_exempt_cert_mods_bind_result >>
      qexistsl_tac [`mid`,`mid_state`,`reached`] >> simp[])
  >~ [`gas_exempt_cert_mods _ _ _ _ _ _ _ _`]
  >- (rpt strip_tac >> irule gas_exempt_cert_mods_error_result >> simp[])
  >~ [`storage_trace_frame (eval_expr _ _)`]
  >- simp[evaluate_storage_trace_frame]
  >~ [`!v. storage_trace_frame (read_result _ v)`]
  >- simp[storage_trace_frame_read_result] >>
  qexists_tac `\H res ee G tn u. childQ H res ee G tn u /\ ee.gas_obs = [] /\ ~u.vs_halted` >>
  reverse conj_tac
  >- (irule gas_outcome_full_mods_post_source >>
      qpat_assum `gas_outcome_full_mods _ _ _ _ _ _ childQ childR` (irule_at Any) >>
      conj_tac >- simp[] >>
      rpt gen_tac >> Cases_on `res` >> simp[Abbr `childR`, expr_exit_def] >>
      ONCE_REWRITE_TAC [INST_TYPE [beta |-> ``:value``] expr_exit_INR_type,
        INST_TYPE [beta |-> ``:value``] halt_exit_INR_type] >> simp[]) >>
  suspend "read"
QED

Resume struct_literal_value_of_memory_vv_mods[read]:
  qx_genl_tac [`marks`,`res`,`ee`,`G`,`tn`,`u`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `valid_horizon cx st0 (storage_trace_horizon ee.storage_trace) ee.storage_trace` by
    fs[storage_trace_domain_def] >>
  qunabbrev_tac `childQ` >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> _`
    (drule_then (strip_assume_tac o BETA_RULE)) >>
  `eval_expr cx (StructLit (StructT nsid) nsid kes)
      (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
      (INL tv,ee with gas_obs := [])` by
    (qpat_x_assum `!tail. eval_expr _ _ _ = _` (qspec_then `[]` mp_tac) >> simp[]) >>
  drule_then (qx_choose_then `v` strip_assume_tac) struct_literal_eval_value >>
  disj1_tac >> qexists_tac `Value v` >> simp[] >>
  irule gas_outcome_full_mods_pure >> simp[read_result_def, return_def] >>
  qexistsl_tac [`G`,`ee`,`INL v`,`u`,`tn`] >> simp[] >>
  qx_gen_tac `H` >> strip_tac >>
  conj_tac >- simp[cj 1 gas_origin_ptr_path_rules] >>
  qpat_x_assum `!h. valid_horizon _ _ h ee.storage_trace ==> _`
    (qspec_then `H` (mp_tac o BETA_RULE)) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  `ee with gas_obs := [] = ee` by simp[evaluation_state_component_equality] >>
  gvs[expr_type_def, lowered_value_type_def] >>
  drule_all_then strip_assume_tac struct_literal_read_post >> simp[] >>
  qpat_assum `!t' p'. LocatedValue _ _ = LocatedValue t' p' /\ _ ==> ptr_buf_ok _ _ _ _ _`
    (qspecl_then [`StructT nsid`,`p`] mp_tac) >> simp[]
QED

Finalise struct_literal_value_of_memory_vv_mods
