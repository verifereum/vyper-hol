(*
 * The pointer twin of S1's Name case (exprSimName, exprSimNameValue,
 * exprSimNameWord, exprSimMemoryRead): a local is its pointer variable p,
 * with no code; ghost_inv's locals clause covers p for the local's region
 * and has its value in memory whatever the tainted bytes hold.  A word
 * local's value is then loaded by one MLOAD, whose 32 bytes that robustness
 * makes untainted (representationCleanPtr), so the loaded word is too.
 *
 * TOP-LEVEL:
 *   name_expr_sim_ptr
 *
 * Helpers: name_local_facts, name_ptr_mem_ok, name_source,
 *   name_vv_sim_ptr, name_nonword_sim_ptr, name_word_sim_ptr
 *)
Theory exprSimPtrName
Ancestors
  exprSimPtrProps gasSummary bodyPtrDefs fragGasPathPtr fragGasSeqPtr ptrSafeRun
  ptrDiscipline typedCopyPtr representationCleanPtr
  exprSimNameValue exprSimMemoryPath exprSimUnwrapProps exprSimProps
  exprSimHypsDefs exprSimDefs loweringPosts loweringSlice emitHelperProps
  exprLowering exprLoweringProps fragExec compileEnv loweringStateRelDefs context
  exprSimHyps exprSimSource
  vyperAST vyperInterpreter vyperState vyperTypeEnv vyperTypeSystem
  vyperTypeInvariants vyperTyping valueEncoding
  valueEncodingProps venomExecSemantics venomInst venomState
  entryDecodeStaticProps list finite_map

Theorem name_local_facts[local]:
  expr_sim_pre cenv cx env (Name ann id) es ==>
  ?entry p sz.
    lookup_scopes id es.scopes = SOME entry /\
    evaluate_type (get_tenv cx) ann = SOME entry.type /\
    value_has_type entry.type entry.value /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    cenv.ce_var_type id = SOME ann
Proof
  strip_tac >>
  `?entry. lookup_scopes id es.scopes = SOME entry /\
           evaluate_type (get_tenv cx) ann = SOME entry.type /\
           value_has_type entry.type entry.value` by
    (gvs[expr_sim_pre_def, expr_sim_inv_def] >>
     drule_all well_typed_Name_lookup >> strip_tac >>
     gvs[env_consistent_def, env_context_consistent_def]) >>
  `?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)` by
    gvs[expr_sim_pre_def, expr_sim_inv_def, well_typed_expr_def] >>
  `cenv.ce_var_type id = SOME ann` by
    gvs[expr_sim_pre_def, expr_sim_inv_def, well_typed_expr_def] >>
  metis_tac[]
QED

(* The local's pointer, from ghost_inv's locals clause and local_ptrs_rel. *)
Theorem name_ptr_mem_ok[local]:
  ghost_inv d cenv cx es G tn s /\ stmt_state_rel ctx func cenv cx es s /\
  lookup_scopes id es.scopes = SOME entry /\
  evaluate_type (get_tenv cx) ann = SOME entry.type /\
  FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) ==>
  ?w. lookup_var p s = SOME w /\ ptr_covers G tn p s sz /\
      type_memory_size entry.type <= sz /\
      ptr_mem_ok cx ann entry.value (Var p) G tn s /\
      !mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
            val_in_memory entry.type entry.value (w2n w) mem
Proof
  strip_tac >>
  `?w. lookup_var p s = SOME w /\ type_memory_size entry.type <= sz /\
       val_wf entry.type entry.value` by
    (fs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def] >>
     first_x_assum drule_all >> metis_tac[]) >>
  `ptr_covers G tn p s sz /\
   !mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
         val_in_memory entry.type entry.value (w2n w) mem` by
    (fs[ghost_inv_def] >> metis_tac[]) >>
  drule val_store_size_le >> strip_tac >>
  qexists_tac `w` >> simp[ptr_mem_ok_def, eval_operand_def] >>
  rpt strip_tac >> gvs[ptr_covers_def]
QED

Theorem word_type_memory_bytes[local]:
  is_word_type ty ==> type_memory_bytes cenv ty = 32
Proof
  Cases_on `ty` >> simp[is_word_type_def, type_memory_bytes_def] >>
  rename1 `BaseT bt` >> Cases_on `bt` >>
  simp[is_word_type_def, type_memory_bytes_def] >>
  rename1 `BytesT bd` >> Cases_on `bd` >>
  simp[is_word_type_def, type_memory_bytes_def]
QED

(* The buffer of a local's type is its value's footprint. *)
Theorem name_buf_bytes[local]:
  expr_sim_pre cenv cx env (Name ann id) es /\
  evaluate_type (get_tenv cx) ann = SOME tv ==>
  type_memory_bytes cenv ann = type_memory_size tv
Proof
  strip_tac >> Cases_on `is_word_type ann`
  >- metis_tac[word_type_memory_bytes, word_type_memory_size] >>
  drule expr_sim_pre_body_pre >> strip_tac >>
  drule expr_body_pre_copy_ok >>
  disch_then (qspec_then `tv` mp_tac) >>
  gvs[vyperASTTheory.expr_type_def]
QED

(* A local's pointer covers the buffer of its type. *)
Theorem name_ptr_buf_ok[local]:
  expr_sim_pre cenv cx env (Name ann id) es /\
  evaluate_type (get_tenv cx) ann = SOME tv /\
  type_memory_size tv <= sz /\ ptr_covers G tn p s sz ==>
  ptr_buf_ok cenv (Name ann id) (Var p) G s
Proof
  strip_tac >> drule_all name_buf_bytes >> strip_tac >>
  rw[ptr_buf_ok_def, lowered_value_type_def, eval_operand_def] >>
  gvs[ptr_covers_def, vyperASTTheory.expr_type_def]
QED

(* The source: a name reads its local's value, reading no gas. *)
Theorem name_source[local]:
  lookup_scopes id es.scopes = SOME entry ==>
  (!tail. eval_expr cx (Name ann id) (es with gas_obs := tail) =
            (INL (PlaceR (MemoryPlace id [])), es with gas_obs := tail)) /\
  (!tail. bind (eval_expr cx (Name ann id)) (read_result cx)
            (es with gas_obs := tail) =
            (INL entry.value, es with gas_obs := tail)) /\
  read_result cx (PlaceR (MemoryPlace id [])) (es with gas_obs := []) =
    (INL entry.value, es with gas_obs := [])
Proof
  strip_tac >>
  `!tail. eval_expr cx (Name ann id) (es with gas_obs := tail) =
            (INL (PlaceR (MemoryPlace id [])), es with gas_obs := tail)` by
    simp[Once evaluate_def, bind_def, get_scopes_def, return_def,
         type_check_def, assert_def, check_def, ignore_bind_def] >>
  `!tail. bind (eval_expr cx (Name ann id)) (read_result cx)
            (es with gas_obs := tail) =
            (INL entry.value, es with gas_obs := tail)` by
    (gen_tac >>
     qspecl_then [`cx`, `ann`, `id`, `es with gas_obs := tail`, `entry`]
       mp_tac eval_name_word >> simp[] >>
     CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]) >>
  simp[] >>
  first_x_assum (qspec_then `[]` mp_tac) >> simp[vyperStateTheory.bind_def]
QED

Theorem name_vv_sim_ptr[local]:
  expr_sim_pre cenv cx env (Name ann id) es ==>
  expr_vv_sim_ptr d ctx PG func cenv cx ty (Name ann id) es
Proof
  strip_tac >> drule name_local_facts >> strip_tac >>
  rw[expr_vv_sim_ptr_def] >>
  drule compile_name_value_ptr >> strip_tac >> gvs[] >>
  drule_all name_ptr_mem_ok >> strip_tac >>
  drule name_source >> strip_tac >>
  `ptr_buf_ok cenv (Name ann id) (Var p) G0 s0` by
    metis_tac[name_ptr_buf_ok] >>
  rewrite_tac[gas_outcome_ptr_def] >> qexists_tac `[]` >> disj1_tac >>
  rewrite_tac[gas_summary_ptr_at_def] >>
  qexistsl_tac [`INL (PlaceR (MemoryPlace id []))`, `es`, `G0`, `tn0`,
                `OK s0`] >>
  simp[gas_explicit_def, gas_path_ptr_rules] >>
  conj_tac >- (irule name_value_post >> simp[]) >>
  gvs[ghost_inv_def, ptr_vv_ok_def, mk_ptr_def, ghost_kept_def,
      vyperASTTheory.expr_type_def, ptr_covers_def] >>
  metis_tac[]
QED

(* A local of a non-word type: its pointer, no code. *)
Theorem name_nonword_sim_ptr[local]:
  expr_sim_pre cenv cx env (Name ann id) es /\ ~is_word_type ann ==>
  expr_sim_ptr d ctx PG func cenv cx ty (Name ann id) es
Proof
  strip_tac >> drule name_local_facts >> strip_tac >>
  rw[expr_sim_ptr_def] >>
  `op = Var p /\ sb = sa` by
    (drule compile_name_value_ptr >> strip_tac >>
     gvs[lower_value_def, comp_bind_def, unwrap_memory_compile, mk_ptr_def,
         comp_return_def]) >>
  gvs[] >>
  drule_all name_ptr_mem_ok >> strip_tac >>
  drule name_source >> strip_tac >>
  `vv_post ctx func cenv cx (Name ann id) es sa sa s0 (es with gas_obs := [])
     (Value entry.value) (LocatedValue ann (mk_ptr (Var p) LocMemory)) s0` by
    (`read_result cx (PlaceR (MemoryPlace id [])) (es with gas_obs := []) =
       (INL entry.value, es with gas_obs := [])` by simp[] >>
     drule vv_post_read_result >> disch_then (fn th => rewrite_tac[GSYM th]) >>
     irule name_value_post >> simp[]) >>
  `ptr_buf_ok cenv (Name ann id) (Var p) G0 s0` by
    metis_tac[name_ptr_buf_ok] >>
  rewrite_tac[gas_outcome_ptr_def] >> qexists_tac `[]` >> disj1_tac >>
  rewrite_tac[gas_summary_ptr_at_def] >>
  qexistsl_tac [`INL entry.value`, `es`, `G0`, `tn0`, `OK s0`] >>
  simp[gas_explicit_def, gas_path_ptr_rules] >>
  conj_tac
  >- (drule expr_post_of_vv_post_memory >> simp[mk_ptr_def]) >>
  gvs[ghost_inv_def, ptr_val_ok_def, ghost_kept_def,
      vyperASTTheory.expr_type_def, ptr_covers_def] >>
  metis_tac[]
QED

(* A word-typed local: one MLOAD through its pointer. *)
Theorem name_word_sim_ptr[local]:
  expr_sim_pre cenv cx env (Name ann id) es /\ is_word_type ann ==>
  expr_sim_ptr d ctx PG func cenv cx ty (Name ann id) es
Proof
  strip_tac >> drule name_local_facts >> strip_tac >>
  rw[expr_sim_ptr_def] >>
  drule_all lower_value_name_word >> strip_tac >>
  drule_all name_ptr_mem_ok >> strip_tac >>
  `!mem. mem_agree_outside tn0.t_mem s0.vs_memory mem ==>
         mem_word_at (w2n w) mem = typed_val_to_w256 entry.type entry.value` by
    metis_tac[val_in_memory_word_type] >>
  `!i. w2n w <= i /\ i < w2n w + 32 ==> i NOTIN tn0.t_mem` by
    (qspecl_then [`tn0.t_mem`, `s0.vs_memory`, `w2n w`,
                  `typed_val_to_w256 entry.type entry.value`]
       mp_tac robust_mem_word_at_clean >> simp[]) >>
  `mload (w2n w) s0 = typed_val_to_w256 entry.type entry.value` by
    metis_tac[mem_word_at_eq_mload, mem_agree_outside_def] >>
  `ptr_covers G0 tn0 p s0 32` by
    (`type_memory_size entry.type = 32` by metis_tac[word_type_memory_size] >>
     gvs[ptr_covers_def]) >>
  drule_all emit_mload_ptr_path >>
  disch_then (qspecl_then [`cx_dead cx`, `PG`] strip_assume_tac) >> gvs[] >>
  qabbrev_tac `out = STRING #"%" (toString sa.cs_next_var)` >>
  qabbrev_tac `u = update_var out (typed_val_to_w256 entry.type entry.value) s0
                   with vs_inst_idx := SUC s0.vs_inst_idx` >>
  `eval_operand (Var p) s0 = SOME w` by simp[eval_operand_def] >>
  drule_all emit_mload_endpoint >> strip_tac >>
  drule name_source >> strip_tac >>
  `stmt_state_rel ctx func cenv cx (es with gas_obs := []) u` by
    (simp[Abbr `u`] >>
     `not_local_ptr cenv (es with gas_obs := []).scopes out` by
       (simp[Abbr `out`] >> irule local_ptrs_reserved_fresh >>
        qexists_tac `sa` >> simp[]) >>
     `stmt_state_rel ctx func cenv cx (es with gas_obs := [])
        (s0 with vs_inst_idx := SUC s0.vs_inst_idx)` by
       (drule msg_gas_state_frame >>
        disch_then (qspecl_then [`s0.vs_gas_readings`,
                                 `SUC s0.vs_inst_idx`, `[]`] mp_tac) >>
        simp[]) >>
     drule_all stmt_state_rel_update_var >> simp[update_var_def]) >>
  `vv_post ctx func cenv cx (Name ann id) es sa sa s0 (es with gas_obs := [])
     (Value entry.value) (LocatedValue ann (mk_ptr (Var p) LocMemory)) s0` by
    (`read_result cx (PlaceR (MemoryPlace id [])) (es with gas_obs := []) =
       (INL entry.value, es with gas_obs := [])` by simp[] >>
     drule vv_post_read_result >> disch_then (fn th => rewrite_tac[GSYM th]) >>
     irule name_value_post >> simp[]) >>
  `expr_post ctx func cenv cx (Name ann id) es sa sb s0 (es with gas_obs := [])
     entry.value (Var out) u` by
    (`eval_operand (Var out) u =
        SOME (typed_val_to_w256 entry.type entry.value)` by
       simp[Abbr `u`, eval_operand_def, lookup_var_def, update_var_def,
            finite_mapTheory.FLOOKUP_UPDATE] >>
     drule expr_post_of_vv_post_load >> disch_then irule >>
     simp[vyperASTTheory.expr_type_def] >>
     gvs[Abbr `u`, Abbr `out`] >> metis_tac[]) >>
  rewrite_tac[gas_outcome_ptr_def] >> qexists_tac `[]` >> disj1_tac >>
  rewrite_tac[gas_summary_ptr_at_def] >>
  qexistsl_tac [`INL entry.value`, `es`, `G'`, `tn'`, `OK u`] >>
  simp[gas_explicit_def, ptr_val_ok_def, vyperASTTheory.expr_type_def] >>
  gvs[Abbr `u`] >> rpt conj_tac
  >- (irule ghost_inv_fresh_frame >>
      qexistsl_tac [`G0`, `es`, `s0`, `sa`, `tn0`] >>
      simp[update_var_def] >> rpt strip_tac >>
      `x <> out` by metis_tac[] >>
      simp[lookup_var_def, update_var_def, finite_mapTheory.FLOOKUP_UPDATE])
  >- (simp[ghost_kept_def] >> metis_tac[])
QED

Theorem name_expr_sim_ptr:
  !d PG ctx func cenv cx env ty ann id es.
    expr_sim_pre cenv cx env (Name ann id) es ==>
    expr_sim_ptr d ctx PG func cenv cx ty (Name ann id) es /\
    expr_vv_sim_ptr d ctx PG func cenv cx ty (Name ann id) es
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- (Cases_on `is_word_type ann`
      >- (irule name_word_sim_ptr >> metis_tac[]) >>
      irule name_nonword_sim_ptr >> metis_tac[]) >>
  irule name_vv_sim_ptr >> metis_tac[]
QED
