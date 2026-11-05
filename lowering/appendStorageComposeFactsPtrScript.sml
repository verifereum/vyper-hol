(* Exported source/machine boundaries for append composition. *)
Theory appendStorageComposeFactsPtr
Ancestors
  appendStorageSourcePtr stmtSimAppendStorageCompose stmtSimDefs
  accountsRelProps appendStorageRel exprLowering emitHelper emitHelperProps
  compileEnv venomState vyperStorage vfmState list rich_list
  exprSimDefs exprLoweringProps vyperState vyperValue vyperStorageBackend venomInst

Theorem append_storage_header_agree:
  stmt_state_rel ctx func cenv cx es s /\
  declared_storage_region cx mid n [] = SOME (tr,slot,ArrayTV tv (Dynamic cap)) ==>
  (if tr then tload slot s else sload slot s) =
    lookup_storage slot (get_storage cx es tr)
Proof
  strip_tac >>
  `accounts_rel cx es s /\ s.vs_call_ctx.cc_address = cx.txn.target` by
    fs[stmt_state_rel_def, state_rel_def, call_ctx_rel_def] >>
  drule accounts_rel_storage_transient >>
  disch_then (drule_at Any) >> strip_tac >>
  `storage_read_live cx tr (get_storage cx es tr) slot
     (ArrayTV tv (Dynamic cap))` by
    metis_tac[declared_storage_region_read_live] >>
  `storage_agree (storage_dead cx tr (get_storage cx es tr))
      (get_storage cx es tr)
      (if tr then contract_transient s else contract_storage s)` by
    (Cases_on `tr` >>
     gvs[storage_rel_def, transient_rel_def, get_storage_def, lookup_account_def]) >>
  `0 < type_slot_size (ArrayTV tv (Dynamic cap))` by
    simp[type_slot_size_def] >>
  drule_all storage_agree_read_head >>
  Cases_on `tr` >> simp[tload_def, sload_def]
QED

Theorem append_storage_word_suffix_open:
  compile_dynarray_append cenv bop vop 1 1 dt vt cap T
    (if tr then TLOAD else SLOAD) (if tr then TSTORE else SSTORE) sb = ((),sf) ==>
  ~block_is_terminated sf
Proof
  Cases_on `tr` >>
  simp[compile_dynarray_append_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_void_def, fresh_id_def, fresh_var_def,
       emit_def] >> strip_tac >> gvs[] >>
  pure_rewrite_tac [GSYM listTheory.APPEND_ASSOC] >>
  Cases_on `sb.cs_current_insts` >>
  simp[block_is_terminated_def, mk_inst_def, is_terminator_def,
       listTheory.LAST_CONS_cond, rich_listTheory.LAST_APPEND_NOT_NIL]
QED
