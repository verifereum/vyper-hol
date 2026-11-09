(* Source actions and the memory-free storage Append suffix. *)
Theory bodyMemAppendFacts
Ancestors
  stmtSimAppendStorageCompose accountsRelProps vyperStorage vyperStorageBackend
  vyperValue vfmState vyperInterpreter vyperState stmtSimDefs
  exprLowering compileEnv loweringStateRelDefs emitHelper emitHelperProps exprLoweringProps
  instMemFrontier fragExecMem memSafeRun venomMemDefs venomInst venomState
  venomExecSemantics list rich_list

Theorem append_storage_word_suffix_footprint_mem:
  compile_dynarray_append cenv bop vop 1 1 dt vt cap T
    (if tr then TLOAD else SLOAD) (if tr then TSTORE else SSTORE) sa = ((),sf) ==>
  same_blocks sa sf /\ inst_extends sa sf /\
  EVERY (\i. MEM i.inst_opcode [SLOAD; TLOAD; LT; ASSERT; ADD; MUL; SSTORE; TSTORE])
    (emitted_insts sa sf)
Proof
  Cases_on `tr` >>
  simp[compile_dynarray_append_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_void_def, fresh_id_def, fresh_var_def,
       emit_def] >> strip_tac >> gvs[] >>
  simp[same_blocks_def, inst_extends_def, emitted_insts_def] >>
  pure_rewrite_tac [GSYM listTheory.APPEND_ASSOC,
                   rich_listTheory.DROP_LENGTH_APPEND] >>
  simp[mk_inst_def]
QED

Theorem append_storage_word_suffix_open_mem:
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

Theorem append_storage_word_suffix_mem_ok:
  compile_dynarray_append cenv bop vop 1 1 dt vt cap T
    (if tr then TLOAD else SLOAD) (if tr then TSTORE else SSTORE) sa = ((),sf) ==>
  run_inst_seq_mem_ok (emitted_insts sa sf) s
Proof
  strip_tac >> drule append_storage_word_suffix_footprint_mem >> strip_tac >>
  irule run_inst_seq_mem_ok_every >>
  fs[EVERY_MEM] >> rpt strip_tac >>
  first_x_assum drule >> simp[] >> strip_tac >>
  simp[below_frontier_no_ranges, inst_dload_in_section_def]
QED

Theorem append_storage_header_agree_mem:
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

Theorem append_storage_place_preserves_gas:
  append_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic cap))) v st =
    (res,st') ==> st'.gas_obs = st.gas_obs
Proof
  simp[append_place_def, get_storage_backend_eq, bind_def, LET_THM,
       ignore_bind_def, check_def, assert_def, return_def, raise_def,
       write_storage_slot_eq] >>
  rpt (BasicProvers.FULL_CASE_TAC >>
       gvs[set_storage_def, return_def, raise_def]) >>
  rpt strip_tac >> gvs[] >> Cases_on `tr` >> simp[set_storage_def]
QED

Theorem append_storage_place_no_return:
  append_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic cap))) v st =
    (res,st') ==> !rv. res <> INR (ReturnException rv)
Proof
  simp[append_place_def, get_storage_backend_eq, bind_def, LET_THM,
       ignore_bind_def, check_def, assert_def, return_def, raise_def,
       write_storage_slot_eq] >>
  rpt (BasicProvers.FULL_CASE_TAC >>
       gvs[set_storage_def, return_def, raise_def]) >>
  rpt strip_tac >> gvs[]
QED

Theorem append_storage_place_exit_transport:
  append_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic cap))) v st =
    (res,st') /\ stmt_exit RetQ st' res r ==>
  !st2. stmt_exit RetQ st2 res r
Proof
  strip_tac >> drule append_storage_place_no_return >>
  Cases_on `res` >> gvs[stmt_exit_def] >>
  Cases_on `y` >> gvs[stmt_exit_def]
QED

Theorem append_storage_word_suffix_grows_mem:
  compile_dynarray_append cenv bop vop 1 1 dt vt cap T
    (if tr then TLOAD else SLOAD) (if tr then TSTORE else SSTORE) sa = ((),sf) ==>
  sa.cs_next_var <= sf.cs_next_var
Proof
  Cases_on `tr` >>
  simp[compile_dynarray_append_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_void_def, fresh_id_def,
       fresh_var_def, emit_def] >> strip_tac >> gvs[]
QED
