(* State bridges for memory-to-storage copy and normalization. *)
Theory stmtSimStoreCopyState
Ancestors
  stmtSimStoreCopy exprSimProps exprLoweringProps accountsRelProps
  compileEnv loweringStateRelDefs loweringPosts vyperStorageBackend
  vfmState venomState venomMemDefs valueEncoding
  list rich_list arithmetic words

Theorem place_store_normalize_state:
  stmt_state_rel ctx func cenv cx es (store_copy_normalize q t) /\
  local_ptrs_reserved cenv sa /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x q) ==>
  stmt_state_rel ctx func cenv cx es t
Proof
  strip_tac >>
  `stmt_state_rel ctx func cenv cx es
    ((store_copy_normalize q t) with vs_vars := t.vs_vars)` by
    (irule stmt_state_rel_vars_frame >>
     conj_tac
     >- (rpt gen_tac >> strip_tac >>
         `not_fresh_at sa p` by
           (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
         first_x_assum drule >> simp[store_copy_normalize_def, lookup_var_def]) >>
     conj_tac
     >- (gen_tac >> strip_tac >>
         `not_fresh_at sa p` by
           (fs[local_ptrs_reserved_def] >> metis_tac[]) >>
         first_x_assum drule >> simp[store_copy_normalize_def, lookup_var_def]) >>
     first_assum ACCEPT_TAC) >>
  qpat_x_assum `stmt_state_rel _ _ _ _ _ (store_copy_normalize _ _)` kall_tac >>
  qpat_x_assum `stmt_state_rel _ _ _ _ _ _` mp_tac >>
  rpt (pop_assum kall_tac) >>
  simp_tac (srw_ss()) [store_copy_normalize_def, stmt_state_rel_def, state_rel_def,
    local_ptrs_rel_def, local_region_def, local_backed_def, storage_rel_def,
    transient_rel_def, accounts_rel_def, immutables_rel_def, logs_rel_def,
    venomMemDefsTheory.alloca_inv_def, alloca_room_def, fmp_room_def,
    immutable_alloca_sep_def, immutable_decl_sep_def, immutable_base_zero_def,
    lookup_var_def, oneline eval_operand_def, contract_storage_def, contract_transient_def,
    venomMemDefsTheory.allocas_non_overlapping_def,
    venomMemDefsTheory.alloca_next_valid_def, pending_alloca_size_def] >>
  strip_tac >> asm_rewrite_tac[]
QED
