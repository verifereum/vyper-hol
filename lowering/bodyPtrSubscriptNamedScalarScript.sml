(* Typed local preparation for the constructive scalar execution pilot. *)
Theory bodyPtrSubscriptNamedScalar
Ancestors
  bodyPtrSubscriptScalarLoad exprSimNameValue representationCleanPtr
  entryDecodeProps stmtSimReturn exprSimHypsDefs exprLoweringProps
  bodyPtrDefs exprSimDefs loweringPosts vyperTypeEnv vyperTypeInvariants
  vyperTypeSystem vyperValue valueEncoding valueEncodingProps
  codegenRel contextCodegenRel compileEnv ptrDiscipline finite_map
  exprSimProps emitHelper venomState vyperAST localPtrsProps varsExt

Theorem named_word_preparation:
  expr_body_pre cenv cx env (Name ann id) es /\ is_word_type ann /\
  stmt_state_rel ctx func cenv cx es s /\ ghost_inv d cenv cx es G tn s ==>
  ?entry p sz a.
    lookup_scopes id es.scopes = SOME entry /\
    evaluate_type (get_tenv cx) ann = SOME entry.type /\
    value_has_type entry.type entry.value /\
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    cenv.ce_var_type id = SOME ann /\
    lookup_var p s = SOME a /\ ptr_covers G tn p s 32 /\
    mload (w2n a) s = typed_val_to_w256 entry.type entry.value /\
    (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem)
Proof
  rpt strip_tac >>
  `?entry. lookup_scopes id es.scopes = SOME entry /\
           evaluate_type (get_tenv cx) ann = SOME entry.type /\
           value_has_type entry.type entry.value` by
    (gvs[expr_body_pre_def, expr_sim_inv_def] >>
     drule_all well_typed_Name_lookup >> strip_tac >>
     gvs[env_consistent_def, env_context_consistent_def]) >>
  `?p sz. FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz)` by
    gvs[expr_body_pre_def, expr_sim_inv_def, well_typed_expr_def] >>
  `cenv.ce_var_type id = SOME ann` by
    gvs[expr_body_pre_def, expr_sim_inv_def, well_typed_expr_def] >>
  `?a. lookup_var p s = SOME a /\ type_memory_size entry.type <= sz` by
    (fs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def] >>
     first_x_assum drule_all >> metis_tac[]) >>
  `type_memory_size entry.type = 32` by metis_tac[word_type_sizes] >>
  `ptr_covers G tn p s sz /\
   (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
          val_in_memory entry.type entry.value (w2n a) mem)` by
    (fs[ghost_inv_def] >> metis_tac[]) >>
  `!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
         mem_word_at (w2n a) mem = typed_val_to_w256 entry.type entry.value` by
    (rpt strip_tac >> drule_all val_in_memory_word >> metis_tac[]) >>
  `!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem` by
    (drule robust_mem_word_at_clean >> simp[]) >>
  qexistsl_tac [`entry`, `p`, `sz`, `a`] >> simp[] >> conj_tac
  >- (fs[ptr_covers_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS,
        arithmeticTheory.LESS_EQ_ADD]) >>
  rewrite_tac[GSYM mem_word_at_eq_mload] >> first_x_assum irule >>
  simp[mem_agree_outside_def]
QED

(* Unlike the older word_value post, this includes address and bytesN:
   the result word is interpreted using the evaluated annotation. *)
Theorem named_typed_word_post:
  emit_op MLOAD [Var p] sa = (Var out,sb) /\
  local_ptrs_reserved cenv sa /\ stmt_state_rel ctx func cenv cx es s0 /\
  is_word_type ann /\ evaluate_type (get_tenv cx) ann = SOME tv ==>
  expr_post ctx func cenv cx (Name ann id) es sa sb s0
    (es with gas_obs := []) v (Var out)
    (update_var out (typed_val_to_w256 tv v)
      (s0 with vs_inst_idx := LENGTH sb.cs_current_insts))
Proof
  strip_tac >>
  `out = STRCAT "%" (toString sa.cs_next_var)` by
    gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
        fresh_id_def, fresh_var_def, emit_def] >>
  `not_local_ptr cenv (es with gas_obs := []).scopes out` by
    (gvs[] >> irule local_ptrs_reserved_fresh >> qexists_tac `sa` >> simp[]) >>
  `stmt_state_rel ctx func cenv cx (es with gas_obs := [])
    (update_var out (typed_val_to_w256 tv v)
      (s0 with vs_inst_idx := LENGTH sb.cs_current_insts))` by
    (irule stmt_state_rel_update_var >> simp[] >>
     drule msg_gas_state_frame >>
     disch_then (qspecl_then [`s0.vs_gas_readings`,
                            `LENGTH sb.cs_current_insts`, `[]`] mp_tac) >> simp[]) >>
  simp[expr_post_def, expr_val_rel_def, expr_val_at_def,
       expr_type_def, eval_operand_def, update_var_def,
       lookup_var_def, FLOOKUP_UPDATE, locals_kept_mem] >>
  rpt strip_tac >>
  `STRING #"%" (toString sa.cs_next_var) <> x` by
    (strip_tac >> gvs[not_fresh_at_def]) >> simp[]
QED
