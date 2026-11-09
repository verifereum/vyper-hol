(* Stronger suffix interfaces: no condition on the already-emitted block. *)
Theory bodyMemBiMethodIdEndpoint
Ancestors
  bodyMemBiMethodIdSuffix exprOperandVar venomMemProps fragGasSeqMem
  fragGasMode allocaHistoryFragment fragExec bodyAllocMemory allocaFootprint
  allocaSiteResource loweringHalt builtinHashing builtinBytesMemory builtinBytes
  exprSimHash exprLoweringProps emitHelperProps emitHelper context compileEnv
  fragExecMem instMemFrontier venomState venomExecSemantics venomInst venomMemDefs
  list rich_list words arithmetic exprSimMemDefs exprSimProps loweringPosts
  exprLowering vyperAST vyperValue vyperTypeSystem vyperTyping

Theorem method_id_fixed_hash_mem_ok_any_block:
  compile_keccak256_bytesm src m sa = (op,sb) /\ m <= 32 /\
  eval_operand src s = SOME w /\ fn_has_code sa sb func /\
  stmt_state_rel ctx func cenv cx es s ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  strip_tac >>
  `MEM (mk_inst sa.cs_next_id ALLOCA [Lit 32w]
    [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func)` by
    (mp_tac (Q.INST [`sha` |-> `F`, `v` |-> `src`] hash_fixed_alloca_code) >> simp[]) >>
  `32 < dimword (:256)` by simp[dimword_def] >>
  drule_all method_id_alloc_site_bound >> strip_tac >>
  `alloca_next_valid s` by fs[stmt_state_rel_def, alloca_inv_def] >>
  `p + 32 <= (abi_builtin_allocate_state sa.cs_next_id 32 s).vs_alloca_next` by
    (irule alloca_site_frontier >> simp[]) >>
  qpat_x_assum `compile_keccak256_bytesm _ _ _ = _` mp_tac >>
  simp[compile_keccak256_bytesm_def, comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  rpt (pairarg_tac >> simp[]) >> strip_tac >>
  rename1 `compile_alloc_buffer 32 sa = (buf,sm)` >>
  rename1 `emit_void MSTORE _ sm = (unit,sh)` >> Cases_on `unit` >>
  qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
  simp[compile_alloc_buffer_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  qpat_assum `emit_op ALLOCA _ _ = _`
    (strip_assume_tac o MATCH_MP emitted_insts_emit_op) >>
  gvs[] >> rename1 `emit_void MSTORE _ sm = ((),sh)` >>
  qpat_assum `emit_void MSTORE _ sm = _`
    (strip_assume_tac o MATCH_MP emitted_insts_emit_void) >>
  qpat_assum `emit_op SHA3 _ _ = _`
    (strip_assume_tac o MATCH_MP emitted_insts_emit_op) >>
  drule (Q.INST [`n` |-> `32`] step_alloca_site) >> simp[dimword_def] >>
  disch_then (qspec_then `STRING #"%" (toString sa.cs_next_var)` assume_tac) >>
  qmatch_asmsub_abbrev_tac `step_inst_base _ s = OK u` >>
  `?w'. eval_operand src u = SOME w'` by
    (Cases_on `src` >> gvs[Abbr `u`, eval_operand_def, lookup_var_def, update_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
     metis_tac[]) >>
  `p < dimword (:256)` by decide_tac >>
  `!id. step_inst_base (mk_inst id MSTORE [Var (STRING #"%" (toString sa.cs_next_var)); src] []) u =
      OK (mstore p w' u) /\
      inst_mem_below_frontier (mk_inst id MSTORE [Var (STRING #"%" (toString sa.cs_next_var)); src] []) u` by
    (gen_tac >> irule scratch_mstore_mem_ok >> simp[Abbr `u`, eval_operand_update_var]) >>
  `inst_mem_below_frontier
     (mk_inst sa.cs_next_id ALLOCA [Lit 32w] [STRING #"%" (toString sa.cs_next_var)]) s` by
    (irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
  qspecl_then [`sa`, `sm`, `sh`, `sb`] mp_tac emitted_insts_three >>
  simp[run_inst_seq_mem_ok_cons, run_inst_seq_mem_ok_last] >>
  strip_tac >>
  simp[below_frontier_SHA3, eval_operand_lit, Abbr `u`, eval_operand_update_var] >>
  rpt strip_tac >> gvs[] >> simp[w2n_n2w] >>
  `m MOD dimword (:256) <= m` by simp[MOD_LESS_EQ] >> decide_tac
QED

Theorem method_id_typed_hash_mem_ok_any_block:
  expr_post ctx func cenv cx e es sa sm s0 es' v src s /\
  expr_type e = BaseT bty /\ is_bytes_or_string_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV bty) /\
  value_has_type (BaseTV bty) v /\
  expr_store_bound cx (expr_type e) v src s /\
  lower_value compile_expr cenv (expr_type e) e sa = (src,sm) /\
  local_ptrs_reserved cenv sa /\
  compile_method_id_hash (expr_type e) src sm = (op,sb) /\
  fn_has_code sm sb func ==>
  run_inst_seq_mem_ok (emitted_insts sm sb) s
Proof
  strip_tac >>
  `!x. src = Var x ==> not_fresh_at sm x` by
    (metis_tac[compile_lower_value_var]) >>
  Cases_on `bty` >> gvs[is_bytes_or_string_type_def]
  >~ [`BytesT bd`]
  >- (Cases_on `bd` >> gvs[compile_method_id_hash_def]
      >- (Cases_on `v` >> gvs[value_has_type_def] >>
          `LENGTH l <= 32` by gvs[evaluate_type_def, AllCaseEqs()] >>
          drule hash_fixed_post_view >> simp[value_has_type_def] >> strip_tac >>
          irule method_id_fixed_hash_mem_ok_any_block >>
          fs[expr_post_def] >> metis_tac[]) >>
      drule method_id_dynamic_hash_mem_ok >> disch_then irule >>
      simp[is_bytestring_type_def] >> metis_tac[]) >>
  gvs[compile_method_id_hash_def] >>
  drule method_id_dynamic_hash_mem_ok >> disch_then irule >>
  simp[is_bytestring_type_def] >> metis_tac[]
QED

Theorem method_id_runtime_typed_mem_ok_any_block:
  expr_post ctx func cenv cx e es sa sm s0 es' v x s /\
  expr_type e = BaseT bty /\ is_bytes_or_string_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV bty) /\
  value_has_type (BaseTV bty) v /\
  lower_value compile_expr cenv (expr_type e) e sa = (x,sm) /\
  compile_method_id_runtime (expr_type e) x fixed sm = (op,sb) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  MAP FDOM es.scopes = MAP FDOM es'.scopes /\
  expr_store_bound cx (expr_type e) v x s ==>
  run_inst_seq_mem_ok (emitted_insts sm sb) s
Proof
  strip_tac >> drule_all hash_method_id_runtime_cut >> strip_tac >>
  drule_all hash_method_id_hash_cut >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts sm sm') s` by
    (drule method_id_typed_hash_mem_ok_any_block >> disch_then irule >> simp[] >> metis_tac[]) >>
  drule_all method_id_hash_typed_post_run >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sm sm') s = OK hashed` >>
  `sa.cs_next_var <= sm'.cs_next_var` by
    (drule (cj 2 compile_expr_grows) >> strip_tac >>
     drule_all method_id_hash_grows >> strip_tac >> decide_tac) >>
  `local_ptrs_reserved cenv sm'` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `sm'.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sm' /\
   sb.cs_current_insts = sm'.cs_current_insts ++ emitted_insts sm' sb` by
    (drule_all method_id_tail_shape >> strip_tac >>
     drule_all method_id_hash_as_keccak >>
     disch_then (qspecl_then [`x`, `sm`] SUBST_ALL_TAC) >>
     drule_all keccak_typed_suffix_shape >> simp[]) >>
  `emitted_insts sm sb = emitted_insts sm sm' ++ emitted_insts sm' sb` by
    (irule emitted_insts_append >> simp[]) >>
  qpat_x_assum `emitted_insts sm sb = _` (fn th => rewrite_tac[th]) >>
  irule run_inst_seq_mem_ok_append >> simp[] >>
  rpt strip_tac >> gvs[] >>
  `!u. run_inst_seq_mem_ok (emitted_insts sm' sp) u` by
    (qpat_assum `emit_op SHR _ _ = _`
       (strip_assume_tac o MATCH_MP emitted_insts_emit_op) >>
     qpat_assum `emit_op SHL _ _ = _`
       (strip_assume_tac o MATCH_MP emitted_insts_emit_op) >>
     `emitted_insts sm' sp = emitted_insts sm' sn ++ emitted_insts sn sp` by
       (irule emitted_insts_append >> simp[]) >>
     simp[] >> gen_tac >> irule run_inst_seq_mem_ok_every >>
     simp[] >> rpt conj_tac >> gen_tac >>
     irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
  Cases_on `fixed` >> gvs[] >>
  drule_all hash_method_id_mask_cut >> strip_tac >>
  drule_all method_id_mask_frame >> strip_tac >>
  qpat_assum `emit_op SHR _ _ = _`
    (strip_assume_tac o MATCH_MP emitted_insts_emit_op) >>
  qpat_assum `emit_op SHL _ _ = _`
    (strip_assume_tac o MATCH_MP emitted_insts_emit_op) >>
  `emitted_insts sm' sb = emitted_insts sm' sp ++ emitted_insts sp sb` by
    (qpat_x_assum `sm'.cs_current_insts = _` kall_tac >>
     qpat_x_assum `sb.cs_current_insts = _` kall_tac >>
     drule compile_alloc_buffer_insts >> strip_tac >>
     qpat_assum `emit_void MSTORE _ sh = _`
       (strip_assume_tac o MATCH_MP emitted_insts_emit_void) >>
     qpat_assum `emit_op ADD _ _ = _`
       (strip_assume_tac o MATCH_MP emitted_insts_emit_op) >>
     qpat_assum `emit_void MSTORE _ sd = _`
       (strip_assume_tac o MATCH_MP emitted_insts_emit_void) >>
     pure_rewrite_tac[emitted_insts_def] >>
     map_every (fn q => qpat_assum q (fn th => pure_rewrite_tac[th]))
       [`sb.cs_current_insts = _`, `sd.cs_current_insts = _`,
        `st.cs_current_insts = _`, `sh.cs_current_insts = _`,
        `sp.cs_current_insts = _`, `sn.cs_current_insts = _`] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >>
     simp_tac list_ss [LENGTH_APPEND, DROP_APPEND2, GSYM APPEND_ASSOC]) >>
  qpat_x_assum `emitted_insts sm' sb = _` (fn th => rewrite_tac[th]) >>
  irule run_inst_seq_mem_ok_append >> simp[] >> rpt strip_tac >> gvs[] >>
  drule method_id_output_buffer_mem_ok_unrestricted >> disch_then irule >>
  metis_tac[]
QED

Theorem method_id_runtime_typed_post_run_mem_any_block:
  expr_post ctx func cenv cx e es sa sm s0 es' v x s /\
  expr_type e = BaseT bty /\ is_bytes_or_string_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME (BaseTV bty) /\
  value_has_type (BaseTV bty) v /\
  lower_value compile_expr cenv (expr_type e) e sa = (x,sm) /\
  compile_method_id_runtime (expr_type e) x fixed sm = (op,sb) /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  MAP FDOM es.scopes = MAP FDOM es'.scopes /\
  expr_store_bound cx (expr_type e) v x s ==>
  ?t r. run_inst_seq (emitted_insts sm sb) s = OK t /\
    run_inst_seq_mem_ok (emitted_insts sm sb) s /\
    s.vs_alloca_next <= t.vs_alloca_next /\
    builtin_result cx es'.accounts
      (BaseT (BytesT (if fixed then Fixed 4 else Dynamic 4)))
      MethodId [expr_type e] [v] = INL r /\
    vv_post ctx func cenv cx
      (Builtin (BaseT (BytesT (if fixed then Fixed 4 else Dynamic 4))) MethodId [e])
      es sa sb s0 es' (Value r)
      (if fixed then StackValue (BaseT (BytesT (Fixed 4))) op else
       LocatedValue (BaseT (BytesT (Dynamic 4)))
         <|ptr_location := LocMemory; ptr_operand := op|>) t /\
    vv_store_bound cx
      (BaseT (BytesT (if fixed then Fixed 4 else Dynamic 4)))
      (BaseT (BytesT (if fixed then Fixed 4 else Dynamic 4)))
      es' (Value r)
      (if fixed then StackValue (BaseT (BytesT (Fixed 4))) op else
       LocatedValue (BaseT (BytesT (Dynamic 4)))
         <|ptr_location := LocMemory; ptr_operand := op|>) t
Proof
  strip_tac >>
  drule_all method_id_runtime_typed_post_run >> strip_tac >>
  `run_inst_seq_mem_ok (emitted_insts sm sb) s` by
    (drule_all method_id_runtime_typed_mem_ok_any_block >> simp[]) >>
  `s.vs_alloca_next <= t.vs_alloca_next` by
    (irule method_id_sequence_frontier >> goal_assum (drule_at Any) >>
     qpat_x_assum `compile_method_id_runtime _ _ _ _ = _` mp_tac >>
     Cases_on `bty` >> gvs[is_bytes_or_string_type_def] >>
     TRY (rename1 `BytesT bd` >> Cases_on `bd`) >>
     Cases_on `fixed` >>
     simp[compile_method_id_runtime_def, compile_method_id_hash_def,
       compile_keccak256_bytes_def, compile_keccak256_bytesm_def,
       compile_alloc_buffer_def, emit_op_def, emit_void_def,
       fresh_var_def, fresh_id_def, emit_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
     rpt strip_tac >> gvs[] >>
     simp_tac (srw_ss()) [emitted_insts_def] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >>
     simp_tac (srw_ss()) [mk_inst_def, is_terminator_def, is_ext_call_op_def]) >>
  qexistsl_tac [`t`, `r`] >> simp[] >>
  Cases_on `fixed` >> gvs[]
  >- (irule vv_store_bound_stack_word >> simp[is_word_type_def]) >>
  drule_all hash_method_id_runtime_cut >> strip_tac >> gvs[] >>
  drule_all hash_method_id_hash_cut >> strip_tac >>
  drule (Q.INST [`sh` |-> `sm'`, `hash` |-> `hash`]
    method_id_hash_typed_post_run) >> simp[] >> strip_tac >>
  rename1 `run_inst_seq (emitted_insts sm sm') s = OK hashed` >>
  `sa.cs_next_var <= sm'.cs_next_var` by
    (drule (cj 2 compile_expr_grows) >> strip_tac >>
     drule_all method_id_hash_grows >> strip_tac >> decide_tac) >>
  `local_ptrs_reserved cenv sm'` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  drule_all hash_method_id_mask_cut >> strip_tac >>
  drule_all method_id_dynamic_suffix_frame >> strip_tac >>
  `emitted_insts sm sb = emitted_insts sm sm' ++ emitted_insts sm' sb` by
    (irule method_id_runtime_hash_split >> goal_assum (drule_at Any) >> simp[] >>
     metis_tac[]) >>
  `t' = t` by
    (qpat_assum `run_inst_seq (emitted_insts sm sm') s = OK hashed`
       (mp_tac o MATCH_MP run_inst_seq_append) >>
     disch_then (qspec_then `emitted_insts sm' sb` assume_tac) >>
     qpat_x_assum `run_inst_seq (emitted_insts sm sb) s = _` mp_tac >>
     asm_rewrite_tac[] >> simp[]) >>
  gvs[] >>
  `w2n p + 64 <= t.vs_alloca_next` by
    (fs[stmt_state_rel_def] >> drule_all alloca_site_registered_below >> simp[]) >>
  simp[vv_store_bound_def, vyperStateTheory.read_result_def, vyperStateTheory.return_def,
    evaluate_type_def, val_store_size_def, valueEncodingTheory.type_memory_size_def] >>
  `word_size 4 = 1` by EVAL_TAC >> simp[]
QED
