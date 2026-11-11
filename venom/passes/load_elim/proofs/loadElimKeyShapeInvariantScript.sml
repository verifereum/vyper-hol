Theory loadElimKeyShapeInvariant
Ancestors
  loadElimDefs loadElimTransferProvenance loadElimAbsoluteKey
  loadElimLatticeSoundHelpers loadElimBilateralInvariant loadElimConvergence
  loadElimSolverHelpers venomInst finite_map list pred_set

Definition le_keys_satisfy_def:
  le_keys_satisfy Q ll <=>
    !k vs. FLOOKUP (unwrap_load_lattice ll) k = SOME vs ==> Q k
End

Definition le_configured_context_def:
  le_configured_context ctx <=>
    MEM (ctx.lctx_config,ctx.lctx_addr_space)
      [(memory_config,AddrSp_Memory); (storage_config,AddrSp_Storage);
       (transient_config,AddrSp_Transient); (dload_config,AddrSp_Data);
       (calldataload_config,AddrSp_Calldata)]
End

Theorem le_keys_satisfy_empty[simp]:
  le_keys_satisfy Q NONE /\ le_keys_satisfy Q (SOME FEMPTY)
Proof
  simp[le_keys_satisfy_def, unwrap_load_lattice_def]
QED

Theorem le_keys_satisfy_transfer:
  le_keys_satisfy Q ll /\
  (!k v. le_transfer_generates ctx inst k v ==> Q k) ==>
  le_keys_satisfy Q (load_transfer ctx inst ll)
Proof
  simp[le_keys_satisfy_def] >> rpt strip_tac
  >> drule le_transfer_lookup_origin >> metis_tac[]
QED

Theorem le_keys_satisfy_join:
  le_keys_satisfy Q a /\ le_keys_satisfy Q b ==>
  le_keys_satisfy Q (load_join a b)
Proof
  Cases_on `a` >> Cases_on `b`
  >> simp[le_keys_satisfy_def, load_join_def, unwrap_load_lattice_def]
  >> rpt strip_tac >> drule load_join_raw_lookup >> metis_tac[]
QED

Theorem le_keys_satisfy_fold:
  le_keys_satisfy Q ll /\
  (!inst k v. MEM inst insts /\ le_transfer_generates ctx inst k v ==> Q k) ==>
  le_keys_satisfy Q (FOLDL (\acc inst. load_transfer ctx inst acc) ll insts)
Proof
  qid_spec_tac `ll` >> Induct_on `insts` >> simp[]
  >> rpt strip_tac >> first_x_assum irule
  >> metis_tac[le_keys_satisfy_transfer]
QED

Theorem le_generated_key_absolute:
  le_configured_context ctx /\ (!v. bp_get_ptrs ctx.lctx_bp v = []) /\
  le_transfer_generates ctx inst k v ==>
  le_absolute_key ctx.lctx_addr_space k
Proof
  simp[le_configured_context_def, le_transfer_generates_def]
  >> rpt strip_tac >> gvs[]
  >> gvs[memory_config_def, storage_config_def, transient_config_def,
         dload_config_def, calldataload_config_def]
  >> metis_tac[SRULE [] le_empty_read_key_shape,
               SRULE [] le_empty_write_key_shape, le_dload_key_shape]
QED

Theorem le_absolute_keys_transfer:
  le_configured_context ctx /\ (!v. bp_get_ptrs ctx.lctx_bp v = []) /\
  le_keys_satisfy (le_absolute_key ctx.lctx_addr_space) ll ==>
  le_keys_satisfy (le_absolute_key ctx.lctx_addr_space) (load_transfer ctx inst ll)
Proof
  strip_tac >> irule le_keys_satisfy_transfer
  >> metis_tac[le_generated_key_absolute]
QED

Theorem le_absolute_keys_fold:
  le_configured_context ctx /\ (!v. bp_get_ptrs ctx.lctx_bp v = []) /\
  le_keys_satisfy (le_absolute_key ctx.lctx_addr_space) ll ==>
  le_keys_satisfy (le_absolute_key ctx.lctx_addr_space)
    (FOLDL (\acc inst. load_transfer ctx inst acc) ll insts)
Proof
  strip_tac >> irule le_keys_satisfy_fold
  >> metis_tac[le_generated_key_absolute]
QED

Theorem le_analyze_absolute_keys:
  wf_function fn /\ le_configured_context ctx /\
  (!v. bp_get_ptrs ctx.lctx_bp v = []) ==>
  (!lbl idx. le_keys_satisfy (le_absolute_key ctx.lctx_addr_space)
    (df_at NONE (load_analyze ctx fn) lbl idx)) /\
  (!lbl. le_keys_satisfy (le_absolute_key ctx.lctx_addr_space)
    (df_boundary NONE (load_analyze ctx fn) lbl))
Proof
  strip_tac >> simp[load_analyze_def] >>
  irule le_df_analyze_invariant_bilateral >>
  simp[load_edge_transfer_def, le_keys_satisfy_join, le_absolute_keys_transfer] >>
  conj_tac >- (Cases_on `fn_entry_label fn` >> simp[]) >>
  qexistsl [
    `le_solver_inv (set (fn_labels fn)) (le_generated_keys ctx (fn_insts fn))
       (le_generated_operands (fn_insts fn))`,
    `CARD (set (fn_labels fn)) *
      (1 + CARD (le_generated_keys ctx (fn_insts fn)) *
        (CARD (le_generated_operands (fn_insts fn)) + 1))`,
    `le_solver_leq`,
    `le_solver_rank (set (fn_labels fn)) (le_generated_keys ctx (fn_insts fn))
       (le_generated_operands (fn_insts fn))`] >>
  simp[GSYM le_solver_process_def] >>
  conj_tac
  >- (rpt strip_tac >> drule_all le_solver_process_closed >>
      simp[le_solver_process_def]) >>
  conj_tac >- simp[le_solver_process_inflationary] >>
  conj_tac
  >- (drule le_solver_entry_init >>
      Cases_on `fn_entry_label fn` >> simp[fn_labels_def]) >>
  irule (ONCE_REWRITE_RULE [arithmeticTheory.ADD_COMM] le_solver_bounded_measure) >> simp[]
QED
