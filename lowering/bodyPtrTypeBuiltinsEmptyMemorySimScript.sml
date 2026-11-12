Theory bodyPtrTypeBuiltinsEmptyMemorySim
Ancestors
  bodyPtrTypeBuiltinsEmptyMemoryRun bodyPtrTypeBuiltinsEmptyMemoryPost
  bodyPtrTypeBuiltinsEmptyWord bodyPtrTypeBuiltinsWordCases
  exprSimAggregates exprSimBuffer exprSimBufferEmptyExec exprSimAggregateLayout
  exprSimHypsDefs exprSimHyps exprSimProps exprSimDefs bodyPtrDefs
  exprLowering exprLoweringProps loweringPosts compileEnv loweringStateRelDefs context
  vyperTypeSystem vyperInterpreter vyperState vyperValue vyperAST vyperContext
  gasContext fragGasPathPtr valueEncoding valueEncodingProofs words allocLimits
  venomState gasSummary exprSimVVFrame list venomInstProofs venomExecSemantics stmtFragPtr
  bodyPtrHashBuiltinsGhostFrame exprSimSubscriptArrayCompose

Theorem empty_memory_vv_sim_ptr:
  !d ctx PG func cenv cx env ty ann typ args es.
    ~is_word_type typ /\
    expr_body_pre cenv cx env (TypeBuiltin ann Empty typ args) es ==>
    expr_vv_sim_ptr d ctx PG func cenv cx ty (TypeBuiltin ann Empty typ args) es
Proof
  rpt gen_tac >> strip_tac >>
  `args = [] /\ ann = typ` by
    gvs[expr_body_pre_def, well_typed_expr_def, type_builtin_result_ok_def,
        well_typed_type_builtin_args_def] >>
  gvs[] >> rename1 `~is_word_type typ` >> simp[expr_vv_sim_ptr_def] >> rpt gen_tac >> strip_tac >>
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
      comp_bind_def, comp_return_def] >> pairarg_tac >> gvs[] >>
  `expr_sim_inv cenv cx env es` by gvs[expr_body_pre_def] >>
  `type_memory_bytes cenv typ < dimword (:256)` by
    (gvs[expr_body_pre_def, alloc_limits_expr_def] >>
     simp[dimword_def] >> decide_tac) >>
  suspend "run"
QED
Resume empty_memory_vv_sim_ptr[run]:
  drule_all empty_type_buffer_size >> strip_tac >>
  drule_all compile_builtin_empty_complex_run >> strip_tac >>
  `?p w H th. buf.buf_operand = Var p /\ lookup_var p t = SOME w /\
    gas_path_ptr (cx_dead cx) 0 ctx func PG G0 tn0 s0 0 H th
      (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)) /\
    ptr_covers H th p t (type_memory_bytes cenv typ) /\
    (!a. w2n w <= a /\ a < w2n w +
      (if is_bytestring_type typ \/
        (case typ of ArrayT _ (Dynamic _) => T | _ => F)
       then 32 else type_memory_bytes cenv typ) ==> a NOTIN th.t_mem) /\
    ghost_inv d cenv cx es H th t /\ ghost_kept cenv es sa G0 tn0 s0 H th` by
    (irule empty_buffer_framed_path >> simp[] >>
     goal_assum (drule_at Any) >> simp[]) >>
  suspend "post"
QED
Resume empty_memory_vv_sim_ptr[post]:
  `w' = w` by gvs[eval_operand_def] >> gvs[] >>
  drule_all empty_type_default_memory >> strip_tac >>
  `vv_post ctx func cenv cx (TypeBuiltin typ Empty typ []) es sa sb s0 es
     (Value (default_value tv)) (LocatedValue typ (base_ptr buf)) t` by
    suspend "semantic" >>
  `ptr_vv_ok cx typ (Value (default_value tv))
      (LocatedValue typ (base_ptr buf)) es H th t /\
    ptr_buf_ok cenv (TypeBuiltin typ Empty typ []) buf.buf_operand H t` by
    suspend "pointer" >>
  `t.vs_current_bb = sb.cs_current_bb` by suspend "bb" >>
  simp[gas_outcome_ptr_def] >> qexists_tac `[]` >> disj1_tac >>
  simp[gas_summary_ptr_at_def] >>
  qexistsl_tac [`INL (Value (default_value tv))`, `es`, `H`, `th`,
    `OK (t with vs_inst_idx := LENGTH sb.cs_current_insts)`] >>
  simp[expr_type_def, base_ptr_def] >>
  suspend "transport"
QED
Resume empty_memory_vv_sim_ptr[semantic]:
  irule (SRULE [expr_type_def]
    (Q.INST [`e` |-> `TypeBuiltin typ Empty typ []`, `p` |-> `base_ptr buf`]
      (SPEC_ALL buffer_memory_vv_post))) >>
  goal_assum (drule_at Any) >>
  simp[base_ptr_def, val_wf_default_value_proof] >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!name b len. local_region _ _ _ _ _ _ ==> _ \/ _` drule >>
      strip_tac >> first_x_assum irule >> decide_tac) >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!aid b len. _ ==> regions_disjoint _ _ b len` drule >>
      simp[regions_disjoint_def] >> strip_tac >>
      first_x_assum irule >> decide_tac) >>
  drule_all expr_sim_inv_memory_size >> strip_tac >>
  simp[val_footprint_le, val_wf_default_value_proof] >>
  rpt strip_tac >>
  `local_region cenv es.scopes s0 n lb lsz` by
    (irule local_region_frame >> conj_tac
     >- (qexists_tac `func` >> gvs[stmt_state_rel_def, state_rel_def]) >>
     qexistsl_tac [`sa`, `es.scopes`, `t`] >> simp[]) >>
  qpat_x_assum `!name b len. local_region _ _ s0 _ _ _ ==> _` drule >>
  simp[arithmeticTheory.ADD_COMM]
QED
Resume empty_memory_vv_sim_ptr[pointer]:
  `ptr_vv_ok cx typ (Value (default_value tv))
    (LocatedValue typ (base_ptr <|buf_operand := Var p;
      buf_size := type_memory_bytes cenv typ|>)) es H th t /\
    ptr_buf_ok cenv (TypeBuiltin typ Empty typ []) (Var p) H t` by
    (irule empty_memory_pointer_post >> simp[] >> metis_tac[]) >>
  gvs[base_ptr_def, ptr_vv_ok_def]
QED
Resume empty_memory_vv_sim_ptr[bb]:
  drule compile_builtin_empty_complex_shape >> strip_tac >>
  `t.vs_current_bb = s0.vs_current_bb` by
    (irule (SRULE [] (Q.ISPEC `\s:venom_state. s.vs_current_bb`
      run_inst_seq_preserves_field)) >>
     qexists_tac `emitted_insts sa sb` >> simp[] >> rpt strip_tac >>
     fs[EVERY_MEM] >>
     metis_tac[step_preserves_control_flow, step_inst_non_invoke]) >>
  gvs[]
QED
Resume empty_memory_vv_sim_ptr[transport]:
  simp[ghost_inv_gas_obs, hash_ghost_inv_inst_idx, vv_post_final_gas] >>
  gvs[ptr_vv_ok_def, ptr_mem_ok_def, ptr_buf_ok_def, base_ptr_def,
      read_result_def, return_def, eval_operand_def, lookup_var_def]
QED
Finalise empty_memory_vv_sim_ptr
