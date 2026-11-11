(* Force the counted in-memory slice result without a target suffix. *)
Theory bodyMemBiCalldataSliceRead
Ancestors
  bodyMemBiCalldataSliceCompose bodyMemBiCalldataSliceFacts
  exprSimMemorySource exprSimMemDefs exprSimDefs exprSimProps
  exprSimUnwrapProps loweringPosts exprLowering exprLoweringProps
  gasOutcome gasSummary gasSummaryCompose gasExemptCert gasContext
  vyperInterpreter vyperState vyperAST vyperTypeSystem
  loweringSlice compileEnv venomState context exprSimMemoryPath exprSimCalldataSlice

Theorem compile_calldata_slice_sim_mem:
  expr_body_pre cenv cx env
    (Builtin (BaseT (BytesT (Dynamic n))) (CalldataSlice n) [e]) es /\
  expr_type e = BaseT (UintT 256) /\
  expr_sim_mem ctx func cenv cx (expr_type e) e es ==>
  expr_sim_mem ctx func cenv cx ty
    (Builtin (BaseT (BytesT (Dynamic n))) (CalldataSlice n) [e]) es
Proof
  strip_tac >>
  `expr_vv_sim_mem ctx func cenv cx ty
    (Builtin (BaseT (BytesT (Dynamic n))) (CalldataSlice n) [e]) es` by
    metis_tac[compile_calldata_slice_vv_sim_mem] >>
  simp[expr_sim_mem_def] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `lower_value _ _ _ _ _ = _` mp_tac >>
  simp[lower_value_def, comp_bind_def] >>
  Cases_on `compile_expr cenv ty
    (Builtin (BaseT (BytesT (Dynamic n))) (CalldataSlice n) [e]) sa` >>
  rename1 `_ = (vv,sm)` >> simp[] >>
  `?ptr. vv = LocatedValue (BaseT (BytesT (Dynamic n)))
    (mk_ptr ptr LocMemory)` by
    (qpat_x_assum `compile_expr _ _ _ _ = _` mp_tac >>
     simp[compile_calldata_slice_parts] >>
     Cases_on `lower_value compile_expr cenv (BaseT (UintT 256)) e sa` >>
     simp[] >>
     Cases_on `compile_slice_calldata q (Lit (n2w n))
       (type_memory_bytes cenv (BaseT (BytesT (Dynamic n)))) r` >>
     simp[as_ptr_val_def] >> metis_tac[]) >>
  gvs[] >>
  simp[unwrap_memory_compile, mk_ptr_def, is_word_type_def, comp_return_def] >>
  strip_tac >> gvs[] >>
  `gas_admissible (eval_expr cx
    (Builtin (BaseT (BytesT (Dynamic n))) (CalldataSlice n) [e]))
    expr_vv_res_ok es` by metis_tac[forced_expr_admissible_raw] >>
  qpat_x_assum `expr_vv_sim_mem _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [expr_vv_sim_mem_def]) >>
  disch_then (qspecl_then [`sa`, `sb`,
    `LocatedValue (BaseT (BytesT (Dynamic n))) (mk_ptr op LocMemory)`, `s0`] mp_tac) >>
  (impl_tac >- simp[mk_ptr_def]) >>
  rewrite_tac[gas_outcome_def] >> strip_tac
  >- suspend "normal" >>
  suspend "exempt"
QED

Resume compile_calldata_slice_sim_mem[normal]:
  qexists_tac `marks` >> disj1_tac >>
  qpat_x_assum `gas_summary_at _ _ _ _ _ _ _`
    (mp_tac o REWRITE_RULE [gas_summary_at_def]) >>
  strip_tac
  >- suspend "success" >>
  suspend "exception"
QED

Resume compile_calldata_slice_sim_mem[exempt]:
  qexists_tac `marks` >> disj2_tac >> metis_tac[force_exempt_cert]
QED

Resume compile_calldata_slice_sim_mem[success]:
  gvs[] >>
  drule_at (Pat `vv_post`) buffer_memory_marked_read >>
  simp[mk_ptr_def, is_word_type_def] >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  `read_result cx tv (es_end with gas_obs := []) =
     (INL v,es_end with gas_obs := [])` by
    (qpat_x_assum `gas_marked_exec _ _ (bind _ _) _ _ _ _ _`
       (mp_tac o REWRITE_RULE [gas_marked_exec_def]) >>
     qpat_x_assum `gas_marked_exec _ _ (eval_expr _ _) _ _ _ _ _`
       (mp_tac o REWRITE_RULE [gas_marked_exec_def]) >>
     simp[] >> rpt strip_tac >>
     first_x_assum (qspec_then `[]` mp_tac) >>
     first_x_assum (qspec_then `[]` mp_tac) >>
     simp[bind_def]) >>
  `expr_store_bound cx
     (expr_type (Builtin (BaseT (BytesT (Dynamic n))) (CalldataSlice n) [e]))
     v op t` by
    (fs[vv_store_bound_def, expr_store_bound_def, mk_ptr_def] >> metis_tac[]) >>
  simp[gas_summary_at_def] >>
  qexistsl_tac [`INL v`, `es_end with gas_obs := []`, `OK t`] >> simp[]
QED

Resume compile_calldata_slice_sim_mem[exception]:
  Cases_on `res` >- gvs[expr_exit_def] >>
  simp[gas_summary_at_def] >>
  qexistsl_tac [`INR y`, `es_end`, `r`] >> simp[] >>
  conj_tac
  >- (irule gas_marked_exec_bind_exception >> simp[]) >>
  Cases_on `r` >> Cases_on `y` >> gvs[expr_exit_def] >>
  rename1 `expr_exit (INR (Error err)) _` >>
  Cases_on `err` >> gvs[expr_exit_def]
QED

Finalise compile_calldata_slice_sim_mem
