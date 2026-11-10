(* The empty assignment shortcut emits only a clean zero header. *)
Theory assignBasePtrLocalEmptyFragment
Ancestors assignBasePtrEmptyStore assignTuplePtrStoreHead stmtSimAssignMem
  stmtSimAssignSource stmtSimDeclMem bodyPtrDefs stmtFragPtr stmtSimProps
  tupleLocalStoreRun loweringPosts
  stmtLowering compileEnv loweringStateRelDefs exprSimDefs exprSimWordArgs exprLoweringProps
  gasSummaryComposePtr fragGasPathPtr gasSummary fragGasMode
  valueEncoding valueEncodingProps venomState venomExecSemantics venomInst
  emitHelper emitHelperProps context finite_map vyperLookup vyperState list rich_list
Libs monadsyntax

Theorem compile_assign_local_empty_stmt_frag_ptr:
  !d ctx PG func cx lctx RetQ cenv ty id e es p sz vtyp tyv.
    FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
    has_length_word (expr_type e) /\ is_empty_value_expr e /\
    has_length_word vtyp /\ evaluate_type (get_tenv cx) vtyp = SOME tyv /\
    (!gs. bind (eval_expr cx e) (read_result cx) (es with gas_obs := gs) =
      (INL (default_value tyv), es with gas_obs := gs)) /\
    (!entry. lookup_scopes id es.scopes = SOME entry ==> entry.type = tyv) ==>
    stmt_frag_ptr d ctx PG func cx lctx RetQ cenv
      (stmt_env cenv lctx ty (Assign (BaseTarget (NameTarget id)) e))
      (eval_stmt cx (Assign (BaseTarget (NameTarget id)) e)) es
Proof
  rpt gen_tac >> strip_tac >>
  simp[stmt_frag_ptr_def] >> rpt gen_tac >> strip_tac >>
  drule_all assign_local_empty_code_parts >> strip_tac >>
  qpat_x_assum `cenv' = cenv` SUBST_ALL_TAC >>
  `!tail. bind (eval_expr cx e) (read_result cx)
    (es with gas_obs := [] ++ tail) =
    (INL (default_value tyv), es with gas_obs := tail)` by simp[] >>
  drule_all assign_local_continuation_all_tails >> strip_tac >>
  `lookup_scopes id es.scopes = SOME entry` by
    metis_tac[find_containing_scope_lookup] >>
  `entry.type = tyv` by metis_tac[] >>
  `?w. lookup_var p s0 = SOME w` by
    (fs[stmt_state_rel_def, state_rel_def, local_ptrs_rel_def] >> metis_tac[]) >>
  drule_all tuple_store_destination_region >> strip_tac >>
  `val_in_memory tyv (default_value tyv) (w2n w)
     (mstore (w2n w) 0w s0).vs_memory /\
   val_wf tyv (default_value tyv) /\ 32 <= type_memory_size tyv` by
    (irule memory_length_word_layout >> simp[mstore_mem_word_at_same] >> metis_tac[]) >>
  `32 <= sz` by metis_tac[arithmeticTheory.LESS_EQ_TRANS] >>
  `local_ptrs_rel func cenv es.scopes s0` by fs[stmt_state_rel_def, state_rel_def] >>
  `!x cap. cenv.ce_return_pc = SOME (PtrVar (Var x) cap) ==> not_fresh_at sa x`
    by metis_tac[ret_pc_ok_def] >>
  `emit_inst MSTORE [Var p; Lit 0w] [] sa = ((),sb)` by fs[emit_void_def, emit_inst_def] >>
  drule_all assign_base_empty_local_store_path >>
  disch_then (qspecl_then [`PG`, `cx_dead cx`] strip_assume_tac) >>
  suspend "post"
QED

Resume compile_assign_local_empty_stmt_frag_ptr[post]:
  `val_wf entry.type (default_value tyv) /\
   32 <= type_memory_size entry.type /\
   val_in_memory entry.type (default_value tyv) (w2n w)
     (mstore (w2n w) 0w s0).vs_memory` by simp[] >>
  drule_all local_header_store_state >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   LENGTH sb.cs_current_insts = SUC (LENGTH sa.cs_current_insts) /\
   ~block_is_terminated sb` by
    (qpat_x_assum `emit_void _ _ _ = _` mp_tac >>
     simp[emit_void_def, comp_bind_def, comp_ignore_bind_def,
          fresh_id_def, emit_def, comp_return_def] >> strip_tac >>
     Cases_on `sa.cs_current_insts` >>
     gvs[block_is_terminated_def, LAST_APPEND, LAST_CONS_cond, mk_inst_def, is_terminator_def]) >>
  `~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
   t.vs_inst_idx = LENGTH sb.cs_current_insts` by
    simp[mstore_def] >>
  simp[gas_outcome_ptr_def] >> qexists_tac `[]` >> disj1_tac >>
  simp[gas_summary_ptr_at_marked] >>
  qexistsl_tac [`INL ()`, `es with scopes := pre ++
    (env |+ (id,entry with <|value := default_value tyv; popped := []|>)) :: rest`,
    `G0`, `tf`, `OK t`] >>
  conj_tac
  >- (simp[gas_marked_exec_ptr_def, gas_explicit_def] >>
      reverse conj_tac >- metis_tac[] >>
      gen_tac >> drule assign_local_admissible_run >>
      disch_then (qspec_then `tail` SUBST1_TAC) >> simp[bind_def]) >>
  `(mstore (w2n w) 0w s0).vs_current_bb = sa.cs_current_bb` by simp[mstore_def] >>
  disj1_tac >> simp[stmt_lands_def, cenv_top_ext_refl] >>
  conj_tac
  >- (qpat_x_assum `stmt_state_rel _ _ _ _ _ (mstore _ _ _)` mp_tac >>
      pure_once_rewrite_tac[GSYM stmt_state_rel_inst_idx] >>
      simp[]) >>
  conj_tac
  >- (qpat_x_assum `ghost_inv _ _ _ (_ with scopes := _) _ _ t` mp_tac >>
      qabbrev_tac `scs = pre ++ (env |+ (id,entry with <|value := default_value tyv; popped := []|>)) :: rest` >>
      `es with <|scopes := scs; gas_obs := []|> =
       (es with scopes := scs) with gas_obs := []` by
        simp[evaluation_state_component_equality] >>
      qpat_x_assum `es with <|scopes := scs; gas_obs := []|> = _`
        (fn th => pure_once_rewrite_tac [th]) >>
      pure_rewrite_tac[ghost_inv_gas_obs] >> simp[]) >>
  metis_tac[]
QED

Finalise compile_assign_local_empty_stmt_frag_ptr
