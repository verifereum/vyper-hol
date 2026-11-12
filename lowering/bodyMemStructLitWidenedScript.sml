(* Memory case for struct literals with widened internal-call fields.
   The body-aware tuple contract owns child execution and typed stores when
   every field is flat against its declared type; a nested widening is held. *)
Theory bodyMemStructLitWidened
Ancestors
  bodyMemoryPreds typedCopyRankPathMem bodyMemStructFieldsBody
  bodyMemAggregateAlloc bodyMemAggregateAssembly bodyExprForceMemory
  exprSimAggregates exprSimAggregateLayout exprSimHyps exprSimMemDefs
  exprSimHypsDefs exprLoweringProps exprSimProps fragExec compileEnv allocLimits
  exprSimAggregateSource exprSimBuffer bodyMemAggregateBounds valueEncoding
  loweringPosts exprSimSource exprSimAggregateChildren vyperAST vyperInterpreter vyperState

Theorem body_struct_lit_widened_flat_mem[local]:
  !cx v7 src_id_opt id kes.
    (!ks. ks = MAP FST kes ==> body_exprs_mem_ok cx (MAP SND kes)) ==>
    !tops ctx func cenv env ty es.
      body_inv tops ctx cenv cx /\
      expr_body_pre cenv cx env (StructLit v7 (src_id_opt,id) kes) es /\
      (?e. MEM e (MAP SND kes) /\ int_calls_expr e <> [] /\
           lowered_value_type cenv e <> expr_type e) /\
      LIST_REL (\t e. t = expr_type e \/
        is_bytestring_type t /\ is_bytestring_type (expr_type e))
        (MAP (FST o SND) (get_struct_fields cenv.ce_struct_fields
           (nsid_to_string (src_id_opt,id)))) (MAP SND kes) ==>
      expr_sim_mem ctx func cenv cx ty (StructLit v7 (src_id_opt,id) kes) es /\
      expr_vv_sim_mem ctx func cenv cx ty (StructLit v7 (src_id_opt,id) kes) es
Proof
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  conj_asm2_tac
  >- (irule body_expr_sim_mem_of_vv_sim_mem >>
      first_assum (irule_at (Pat `expr_body_pre _ _ _ _ _`)) >> simp[] >>
      rpt strip_tac >> drule compile_struct_literal_inv >> simp[]) >>
  rw[expr_vv_sim_mem_def] >>
  drule compile_struct_literal_inv >> strip_tac >> gvs[] >>
  drule struct_literal_lookup_types >> strip_tac >>
  drule struct_literal_evaluated_layout >> strip_tac >>
  `expr_sim_inv cenv cx env es` by gvs[expr_body_pre_def] >>
  `!e st. MEM e (MAP SND kes) /\ expr_sim_inv cenv cx env st ==>
    expr_body_pre cenv cx env e st` by
    metis_tac[expr_body_pre_struct_field] >>
  `ci_mono sa sm` by metis_tac[ci_mono_compile_alloc_buffer, pairTheory.SND] >>
  `ci_mono sm sb` by
    metis_tac[ci_mono_compile_struct_lit_cfn, compile_expr_ci_mono, pairTheory.SND] >>
  `cs_extends sa sm /\ cs_extends sm sb` by gvs[ci_mono_def] >>
  drule_all fn_has_code_split >> strip_tac >>
  `SUM (MAP (SND o SND)
    (get_struct_fields cenv.ce_struct_fields (nsid_to_string (src_id_opt,id)))) <
    dimword (:256)` by
    (gvs[expr_body_pre_def, alloc_limits_expr_def, type_memory_bytes_def] >>
     simp[wordsTheory.dimword_def] >> decide_tac) >>
  drule_all exprSimAllocTheory.buffer_alloc_code >> strip_tac >>
  drule_all aggregate_buffer_alloc_counted_mem_any_block >> strip_tac >>
  suspend "fields"
QED

Resume body_struct_lit_widened_flat_mem[fields]:
  qmatch_asmsub_abbrev_tac `compile_alloc_buffer sz sa` >>
  gvs[] >>
  drule_at (Pat `compile_struct_lit _ _ _ _ _ _ _ = _`)
    aggregate_struct_fields_body_sim_mem >>
  simp[] >> disch_then drule >> disch_then drule >> disch_then drule >>
  disch_then (drule_at (Pat `OPT_MMAP _ _ = _`)) >>
  disch_then (drule_at (Pat `lookup_var _ _ = _`)) >>
  disch_then (drule_at (Pat `MEM _ (fn_insts _)`)) >>
  simp[] >>
  disch_then (qspecl_then [`env`, `es`, `ctx`, `tops`] mp_tac) >>
  (impl_tac >- (simp[] >> rpt strip_tac >>
    irule aggregate_alloca_immutable_sep >>
    goal_assum (drule_at (Pat `stmt_state_rel ctx _ _ _ _ _`)) >>
    qpat_x_assum `MEM inst (fn_insts func)` kall_tac >>
    goal_assum (drule_at (Pat `MEM _ (fn_insts _)`)) >>
    simp[venomInstTheory.mk_inst_def] >>
    goal_assum (drule_at Any) >> simp[])) >> strip_tac >> gvs[] >>
  irule bodyDeclMemoryComposeTheory.gas_outcome_zero_prefix_mem >>
  qexists_tac `t` >>
  conj_tac >- gvs[fragGasModeTheory.gas_marked_path_def] >>
  rewrite_tac[aggregate_struct_action_mem] >>
  drule aggregate_outcome_source_run_mem >> strip_tac >>
  irule aggregate_outcome_map_mem >>
  goal_assum (drule_at Any) >>
  conj_tac >- (rpt strip_tac >> gvs[sumTheory.SUM_MAP]) >>
  rpt strip_tac >> gvs[sumTheory.SUM_MAP] >>
  suspend "value_post"
QED

Resume body_struct_lit_widened_flat_mem[value_post]:
  `eval_expr cx (StructLit v7 (src_id_opt,id) kes) (es with gas_obs := gs) =
    (INL (Value (StructV (ZIP (MAP FST kes,vs)))),ee)` by
    (drule aggregate_eval_struct >> simp[]) >>
  rpt (qpat_x_assum `gas_outcome _ _ _ _ _ _ _` kall_tac) >>
  `expr_body_pre cenv cx env (StructLit v7 (src_id_opt,id) kes) (es with gas_obs := gs)` by simp[] >>
  `v7 = StructT (src_id_opt,id)` by
    gvs[expr_body_pre_def, vyperTypeSystemTheory.well_typed_expr_def] >>
  gvs[] >>
  `val_wf (StructTV (ZIP (MAP FST kes,tvs)))
    (StructV (ZIP (MAP FST kes,vs)))` by
    (irule aggregate_materialised_child_wf >>
     goal_assum (drule_at (Pat `eval_expr _ _ _ = _`)) >>
     simp[expr_type_def, read_result_def, return_def] >>
     goal_assum (drule_at Any) >> simp[]) >>
  `val_footprint (StructTV (ZIP (MAP FST kes,tvs)))
     (StructV (ZIP (MAP FST kes,vs))) <= type_memory_size_list tvs` by
    (drule val_footprint_le >> simp[type_memory_size_def] >>
     `LENGTH (MAP FST kes) = LENGTH tvs` by
       (drule vyperTypeABITheory.OPT_MMAP_LENGTH >> simp[]) >>
     simp[struct_layout_size_zip]) >>
  `MAP FDOM es.scopes = MAP FDOM ee.scopes` by
    (drule vyperEvalExprPreservesScopesDomTheory.eval_expr_preserves_scopes_dom >> simp[]) >>
  `!nm lb len. local_region cenv ee.scopes t' nm lb len ==>
     b + type_memory_size_list tvs <= lb \/ lb + len <= b` by
    (rpt strip_tac >> drule_all aggregate_buffer_clearance >> simp[]) >>
  `~expr_has_effect (StructLit (StructT (src_id_opt,id)) (src_id_opt,id) kes) ==>
     pure_frame cenv func es sa s0 t'` by
    (rewrite_tac[expr_has_effect_thm] >> strip_tac >>
     qpat_x_assum `_ ==> (!n lb lsz. local_region _ _ _ _ _ _ ==> _) /\ _` mp_tac >>
     (impl_tac >- (qpat_x_assum `~EXISTS _ _` mp_tac >>
        simp_tac (srw_ss()) [listTheory.EVERY_MAP, listTheory.NOT_EXISTS,
                             combinTheory.o_DEF])) >>
     strip_tac >>
     qpat_assum `FLOOKUP t.vs_allocas _ = SOME (b,_)` (fn th =>
       qpat_assum `!aid a. FLOOKUP t.vs_allocas aid = SOME a ==> _` (fn th2 =>
         assume_tac (MATCH_MP th2 th))) >>
     irule (Q.SPECL [`cenv`, `func`, `es`, `sa`, `sm`, `s0`, `t`, `t'`]
       aggregate_pure_frame_buffer) >>
     qpat_assum `MEM (mk_inst sa.cs_next_id ALLOCA _ _) _` (irule_at Any) >>
     qpat_assum `FLOOKUP t'.vs_allocas sa.cs_next_id = SOME (b,_)` (irule_at Any) >>
     qexistsl [`t`, `sm`] >> rpt conj_tac
     >- first_assum ACCEPT_TAC
     >- (qpat_assum `!name p n. local_region cenv es.scopes t name p n <=> _`
           (fn th => rewrite_tac [th]) >>
         qpat_assum `t.vs_memory = s0.vs_memory` (fn th => rewrite_tac [th]) >>
         first_assum ACCEPT_TAC)
     >- (qpat_assum `t.vs_memory = s0.vs_memory` (fn th => rewrite_tac [th]) >>
         qx_genl_tac [`pp`, `nn`] >> strip_tac >>
         qpat_assum `!p n. (n + p <= b \/ _) /\ _ ==> _` (qspecl_then [`pp`, `nn`] mp_tac) >>
         (impl_tac >- (conj_tac >- decide_tac >> first_assum ACCEPT_TAC)) >>
         disch_then ACCEPT_TAC)
     >- (irule arithmeticTheory.LESS_IMP_LESS_OR_EQ >> first_assum ACCEPT_TAC) >>
     first_assum ACCEPT_TAC) >>
  suspend "buffer_post"
QED

Resume body_struct_lit_widened_flat_mem[buffer_post]:
  conj_asm1_tac
  >- (irule buffer_loop_memory_vv_post >>
      simp[expr_type_def, is_word_type_def, contextTheory.mk_ptr_def, contextTheory.base_ptr_def,
        venomStateTheory.eval_operand_def, valueEncodingDefsTheory.val_in_memory_def] >>
      qexistsl [`b`,`sm`,`type_memory_size_list tvs`,`t`] >>
      simp[wordsTheory.dimword_def] >>
      conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac >- first_assum ACCEPT_TAC >>
      qpat_x_assum `!aid p n. FLOOKUP t.vs_allocas aid = SOME (p,n) /\ _ ==> _` mp_tac >>
      qpat_x_assum `_ ==> pure_frame _ _ _ _ _ _` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >>
      metis_tac[arithmeticTheory.ADD_COMM]) >>
  irule aggregate_allocated_result_store_bound_mem >>
  simp[expr_type_def, exprLoweringTheory.lowered_value_type_def,
       contextTheory.base_ptr_def] >>
  conj_tac >- fs[stmt_state_rel_def] >>
  reverse conj_tac >-
    (qexistsl [`ctx`, `es`, `func`, `s0`, `sa`, `sb`] >>
     gvs[expr_type_def, contextTheory.base_ptr_def]) >>
  qexistsl [`sa.cs_next_id`, `b`, `type_memory_size_list tvs`] >>
  simp[] >>
  `LENGTH (MAP FST kes) = LENGTH tvs` by
    (drule vyperTypeABITheory.OPT_MMAP_LENGTH >> simp[]) >>
  simp[type_memory_size_def, struct_layout_size_zip,
       venomStateTheory.eval_operand_def] >>
  metis_tac[]
QED
Finalise body_struct_lit_widened_flat_mem

(* PORT_ADMISSION: SEQ-4300, s3-mem-safety, replaces body_struct_lit_widened_call_elem_mem which built at 0de4aa499 *)
(* HELD, the twin of bodyMemAggregateLoops' aggregate_make_tuple_nested_sim_mem:
   a field whose declared type it widens to other than as a bytestring (a
   nested bound change), which needs a typed relayout store. *)
Theorem body_struct_lit_widened_nested_mem[local]:
  !cx v7 src_id_opt id kes.
    (!ks. ks = MAP FST kes ==> body_exprs_mem_ok cx (MAP SND kes)) ==>
    !tops ctx func cenv env ty es.
      body_inv tops ctx cenv cx /\
      expr_body_pre cenv cx env (StructLit v7 (src_id_opt,id) kes) es /\
      (?e. MEM e (MAP SND kes) /\ int_calls_expr e <> [] /\
           lowered_value_type cenv e <> expr_type e) /\
      ~LIST_REL (\t e. t = expr_type e \/
        is_bytestring_type t /\ is_bytestring_type (expr_type e))
        (MAP (FST o SND) (get_struct_fields cenv.ce_struct_fields
           (nsid_to_string (src_id_opt,id)))) (MAP SND kes) ==>
      expr_sim_mem ctx func cenv cx ty (StructLit v7 (src_id_opt,id) kes) es /\
      expr_vv_sim_mem ctx func cenv cx ty (StructLit v7 (src_id_opt,id) kes) es
Proof
  cheat
QED

Theorem body_struct_lit_widened_call_elem_mem:
  !cx v7 src_id_opt id kes.
    (!ks. ks = MAP FST kes ==> body_exprs_mem_ok cx (MAP SND kes)) ==>
    !tops ctx func cenv env ty es.
      body_inv tops ctx cenv cx /\
      expr_body_pre cenv cx env (StructLit v7 (src_id_opt,id) kes) es /\
      (?e. MEM e (MAP SND kes) /\ int_calls_expr e <> [] /\
           lowered_value_type cenv e <> expr_type e) ==>
      expr_sim_mem ctx func cenv cx ty (StructLit v7 (src_id_opt,id) kes) es /\
      expr_vv_sim_mem ctx func cenv cx ty (StructLit v7 (src_id_opt,id) kes) es
Proof
  rpt gen_tac >> disch_tac >> rpt gen_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `LIST_REL (\t e. t = expr_type e \/
        is_bytestring_type t /\ is_bytestring_type (expr_type e))
        (MAP (FST o SND) (get_struct_fields cenv.ce_struct_fields
           (nsid_to_string (src_id_opt,id)))) (MAP SND kes)`
  >- (mp_tac (SPEC_ALL body_struct_lit_widened_flat_mem) >>
      impl_tac >- first_assum ACCEPT_TAC >>
      disch_then (qspecl_then [`tops`, `ctx`, `func`, `cenv`, `env`, `ty`, `es`]
        mp_tac) >>
      impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
      simp[]) >>
  mp_tac (SPEC_ALL body_struct_lit_widened_nested_mem) >>
  impl_tac >- first_assum ACCEPT_TAC >>
  disch_then (qspecl_then [`tops`, `ctx`, `func`, `cenv`, `env`, `ty`, `es`]
    mp_tac) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  simp[]
QED
