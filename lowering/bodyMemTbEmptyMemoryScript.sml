(* Memory case of the body induction for empty(T) of a non-word type:
   a fresh zeroed buffer with a counted memory-safe initialization path. *)
Theory bodyMemTbEmptyMemory
Ancestors
  bodyMemoryPreds compileEnv bodyEmptyBufferMemory exprSimAggregates
  exprSimMemDefs exprSimMemoryValues exprSimBuffer exprSimAggregateLayout
  exprSimBufferEmptyExec gasSummary loweringPosts exprLoweringProps
  exprLowering exprSimHypsDefs exprSimDefs exprSimProps valueEncoding
  vyperTypeSystem vyperContext vyperValue vyperInterpreter vyperState
  vyperAST venomState gasContext exprSimHyps allocLimits words
  context valueEncodingProofs arithmetic exprSimVVFrame venomMemDefs
  gasOutcome venomInstProofs venomExecSemantics list fragGasMode exprSimMemUnwrap

Theorem memory_value_post_gas_obs[local]:
  p.ptr_location = LocMemory /\
  vv_post ctx func cenv cx e es sa sb s0 ee (Value v) (LocatedValue ty p) t /\
  stmt_state_rel ctx func cenv cx (ee with gas_obs := gs) t ==>
  vv_post ctx func cenv cx e es sa sb s0 (ee with gas_obs := gs)
    (Value v) (LocatedValue ty p) t
Proof
  strip_tac >>
  gvs[vv_post_def, vv_holds_def, vv_at_def, read_result_def, return_def] >>
  first_assum ACCEPT_TAC
QED

Theorem value_store_bound_gas_obs[local]:
  vv_store_bound cx ty lt (ee with gas_obs := gs) (Value v) vv t <=>
  vv_store_bound cx ty lt ee (Value v) vv t
Proof
  simp[vv_store_bound_def, read_result_def, return_def]
QED

Theorem empty_memory_vv_sim[local]:
  ~is_word_type typ /\
  expr_body_pre cenv cx env (TypeBuiltin ann Empty typ args) es ==>
  expr_vv_sim_mem ctx func cenv cx ty (TypeBuiltin ann Empty typ args) es
Proof
  strip_tac >>
  `args = [] /\ ann = typ` by
    gvs[expr_body_pre_def, well_typed_expr_def, type_builtin_result_ok_def,
        well_typed_type_builtin_args_def] >>
  gvs[] >> rename1 `~is_word_type typ` >> rw[expr_vv_sim_mem_def] >>
  Cases_on `evaluate_type (get_tenv cx) typ`
  >- (qpat_x_assum `gas_admissible _ _ _` mp_tac >>
      simp[gas_admissible_def, Once evaluate_def, bind_def, ignore_bind_def,
           type_check_def, assert_def, return_def, lift_sum_def, raise_def,
           type_builtin_args_length_ok_def, evaluate_type_builtin_def,
           expr_vv_res_ok_def] >>
      simp[Once evaluate_def, return_def, raise_def, bind_def]) >>
  rename1 `evaluate_type (get_tenv cx) typ = SOME tv` >>
  `!s. eval_expr cx (TypeBuiltin typ Empty typ []) s =
       (INL (Value (default_value tv)), s)` by
    (gen_tac >> simp[Once evaluate_def, bind_def, ignore_bind_def,
      type_check_def, assert_def, return_def, lift_sum_def,
      type_builtin_args_length_ok_def, evaluate_type_builtin_def] >>
     simp[Once evaluate_def, return_def]) >>
  gvs[compile_expr_type_builtin_dispatch, Once compile_expr_def,
      comp_bind_def, comp_return_def] >>
  pairarg_tac >> gvs[] >>
  `expr_sim_inv cenv cx env es` by gvs[expr_body_pre_def] >>
  `type_memory_bytes cenv typ < dimword (:256)` by
    (gvs[expr_body_pre_def, alloc_limits_expr_def] >>
     simp[dimword_def] >> decide_tac) >>
  drule_all empty_type_buffer_size >> strip_tac >>
  drule_all compile_builtin_empty_complex_run >> strip_tac >>
  drule_all compile_empty_buffer_mem_path >> strip_tac >>
  drule_all empty_type_default_memory >> strip_tac >>
  `vv_post ctx func cenv cx (TypeBuiltin typ Empty typ []) es sa sb s0 es
     (Value (default_value tv)) (LocatedValue typ (base_ptr buf)) t` by
    (irule (SRULE [expr_type_def]
      (Q.INST [`e` |-> `TypeBuiltin typ Empty typ []`] (SPEC_ALL buffer_memory_vv_post))) >>
     simp[expr_type_def, base_ptr_def, val_wf_default_value_proof] >>
     conj_tac
     >- (rpt strip_tac >>
         qpat_x_assum `!name b len. local_region _ _ _ _ _ _ ==> _ \/ _` drule >>
         strip_tac >> first_x_assum irule >> decide_tac) >>
     conj_tac
     >- (rpt strip_tac >>
         qpat_x_assum `!aid b len. _ ==> regions_disjoint _ _ b len` drule >>
         simp[compileEnvTheory.regions_disjoint_def] >> strip_tac >>
         first_x_assum irule >> decide_tac) >>
     reverse conj_tac
     >- (drule_all expr_sim_inv_memory_size >> strip_tac >>
         simp[val_footprint_le, val_wf_default_value_proof]) >>
     rpt strip_tac >>
     `local_region cenv es.scopes s0 n lb lsz` by
       (irule local_region_frame >> conj_tac
        >- (qexists_tac `func` >> gvs[stmt_state_rel_def, state_rel_def]) >>
        qexistsl [`sa`, `es.scopes`, `t`] >> simp[]) >>
     qpat_x_assum `!name b len. local_region _ _ s0 _ _ _ ==> _` drule >>
     simp[ADD_COMM]) >>
  `w2n w + type_memory_bytes cenv typ <= t.vs_alloca_next` by
    (`alloca_inv t` by fs[stmt_state_rel_def] >>
     fs[alloca_inv_def, alloca_next_valid_def] >>
     first_x_assum drule >> simp[]) >>
  `type_memory_bytes cenv typ = type_memory_size tv` by
    metis_tac[expr_sim_inv_memory_size] >>
  `vv_store_bound cx typ typ es (Value (default_value tv))
      (LocatedValue typ (base_ptr buf))
      (t with vs_inst_idx := LENGTH sb.cs_current_insts)` by
    (irule (SRULE [expr_type_def]
      (Q.INST [`e` |-> `TypeBuiltin typ Empty typ []`]
        (SPEC_ALL vv_store_bound_capacity))) >>
     simp[] >> reverse conj_tac
     >- (goal_assum (drule_at Any)) >>
     qexists_tac `w` >> simp[base_ptr_def, ADD_COMM]) >>
  drule compile_builtin_empty_complex_shape >> strip_tac >>
  `t.vs_current_bb = s0.vs_current_bb` by
    (irule (SRULE [] (Q.ISPEC `\s:venom_state. s.vs_current_bb`
      run_inst_seq_preserves_field)) >>
     qexists_tac `emitted_insts sa sb` >> simp[] >> rpt strip_tac >>
     fs[EVERY_MEM] >>
     metis_tac[step_preserves_control_flow, step_inst_non_invoke]) >>
  simp[gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
  simp[gas_summary_at_def] >>
  qexistsl_tac [`INL (Value (default_value tv))`, `es`,
    `OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)`] >>
  conj_tac >- simp[gas_marked_exec_def, gas_marked_path_def] >>
  simp[expr_type_def, lowered_value_type_def] >>
  conj_tac
  >- (`stmt_state_rel ctx func cenv cx (es with gas_obs := []) t` by
        (drule msg_gas_state_frame >>
         disch_then (qspecl_then [`t.vs_gas_readings`, `t.vs_inst_idx`, `[]`] mp_tac) >>
         simp[NoAsms]) >>
      irule memory_value_post_gas_obs >>
      simp[base_ptr_def] >> goal_assum (drule_at Any) >> simp[]) >>
  simp[value_store_bound_gas_obs]
QED

Theorem body_type_builtin_empty_memory_mem_case:
  !cx v11 typ es.
    ~is_word_type typ ==>
    body_expr_mem_ok cx (TypeBuiltin v11 Empty typ es)
Proof
  rpt gen_tac >> strip_tac >> simp[body_expr_mem_ok_def] >>
  rpt gen_tac >> strip_tac >>
  `expr_vv_sim_mem ctx func cenv cx ty (TypeBuiltin v11 Empty typ es) es'` by
    (irule empty_memory_vv_sim >> metis_tac[]) >>
  simp[] >> irule expr_sim_mem_of_vv_sim_mem >> simp[] >>
  `v11 = typ /\ es = []` by
    gvs[expr_body_pre_def, well_typed_expr_def, type_builtin_result_ok_def,
        well_typed_type_builtin_args_def] >>
  gvs[expr_type_def] >> conj_tac
  >- (rpt gen_tac >>
      simp[compile_expr_type_builtin_dispatch, Once compile_expr_def,
           comp_bind_def, comp_return_def] >>
      pairarg_tac >> simp[]) >>
  rpt strip_tac >>
  `expr_sim_inv cenv cx env es'` by fs[expr_body_pre_def] >>
  drule_all expr_sim_inv_memory_size >> strip_tac >> simp[] >>
  fs[expr_body_pre_def, alloc_limits_expr_def]
QED
