(* Frame boundaries for counted memory-to-storage execution. *)
Theory bodyMemAssignTopCopyPaths
Ancestors
  bodyMemAssignTopCopyLoop stmtSimStoreCopy fragGasSeqMem fragGasMode fragGasPathMem
  context compileEnv emitHelper emitHelperProps exprLoweringProps
  fragExec venomExecSemantics venomState venomInst
  words arithmetic list rich_list finite_map

Theorem topcopy_prefix_zero[simp]:
  store_copy_prefix loc b k sbase 0 = sbase
Proof
  simp[store_copy_prefix_def, COUNT_LIST_def]
QED

Theorem topcopy_prefix_suc:
  store_copy_prefix loc b k sbase (SUC i) =
    (if loc = LocStorage then sstore else tstore)
      (k + n2w i) (mload (w2n (b + n2w i * 32w)) sbase)
      (store_copy_prefix loc b k sbase i)
Proof
  simp[store_copy_prefix_def, COUNT_LIST_SNOC, FOLDL_SNOC]
QED

Theorem topcopy_prefix_memory[simp]:
  (store_copy_prefix loc b k sbase i).vs_memory = sbase.vs_memory
Proof
  Induct_on `i` >> simp[topcopy_prefix_suc] >>
  Cases_on `loc = LocStorage` >> gvs[sstore_def, tstore_def]
QED

Theorem topcopy_prefix_labels[simp]:
  (store_copy_prefix loc b k sbase i).vs_labels = sbase.vs_labels
Proof
  Induct_on `i` >> simp[topcopy_prefix_suc] >>
  Cases_on `loc = LocStorage` >> gvs[sstore_def, tstore_def]
QED

Theorem topcopy_prefix_call_ctx[simp]:
  (store_copy_prefix loc b k sbase i).vs_call_ctx = sbase.vs_call_ctx
Proof
  Induct_on `i` >> simp[topcopy_prefix_suc] >>
  Cases_on `loc = LocStorage` >> gvs[sstore_def, tstore_def]
QED

Theorem topcopy_prefix_frontier[simp]:
  (store_copy_prefix loc b k sbase i).vs_alloca_next = sbase.vs_alloca_next
Proof
  Induct_on `i` >> simp[topcopy_prefix_suc] >>
  Cases_on `loc = LocStorage` >> gvs[sstore_def, tstore_def]
QED

Theorem topcopy_normalize_jump[simp]:
  store_copy_normalize sbase (jump_to l s) = store_copy_normalize sbase s
Proof
  simp[store_copy_normalize_def, jump_to_def]
QED

Theorem topcopy_normalize_idx[simp]:
  store_copy_normalize sbase (s with vs_inst_idx := idx) =
    store_copy_normalize sbase s
Proof
  simp[store_copy_normalize_def]
QED

Theorem topcopy_normalize_update[simp]:
  store_copy_normalize sbase (update_var v w s) = store_copy_normalize sbase s
Proof
  simp[store_copy_normalize_def, update_var_def]
QED

Theorem topcopy_normalize_store:
  store_copy_normalize sbase
    ((if loc = LocStorage then sstore else tstore) key value s) =
  (if loc = LocStorage then sstore else tstore) key value
    (store_copy_normalize sbase s)
Proof
  Cases_on `loc = LocStorage` >>
  simp[store_copy_normalize_def, sstore_def, tstore_def]
QED

Theorem topcopy_frame_base[simp]:
  store_copy_frame sa loc b k sbase 0 sbase
Proof
  simp[store_copy_frame_def, store_copy_normalize_def]
QED

Theorem topcopy_frame_jump[simp]:
  store_copy_frame sa loc b k sbase i (jump_to l s) =
    store_copy_frame sa loc b k sbase i s
Proof
  simp[store_copy_frame_def, jump_to_def, store_copy_normalize_def, lookup_var_def]
QED

Theorem topcopy_frame_idx[simp]:
  store_copy_frame sa loc b k sbase i (s with vs_inst_idx := idx) =
    store_copy_frame sa loc b k sbase i s
Proof
  simp[store_copy_frame_def, lookup_var_def]
QED

Theorem topcopy_frame_update:
  store_copy_frame sa loc b k sbase i s /\
  (!x. not_fresh_at sa x ==> x <> v) ==>
  store_copy_frame sa loc b k sbase i (update_var v w s)
Proof
  simp[store_copy_frame_def, lookup_var_update_var] >> metis_tac[]
QED

Theorem topcopy_frame_memory:
  store_copy_frame sa loc b k sbase i s ==> s.vs_memory = sbase.vs_memory
Proof
  strip_tac >> fs[store_copy_frame_def] >>
  qpat_x_assum `store_copy_normalize _ _ = _`
    (mp_tac o Q.AP_TERM `\s. s.vs_memory`) >>
  simp[store_copy_normalize_def]
QED

Theorem topcopy_frame_labels:
  store_copy_frame sa loc b k sbase i s ==> s.vs_labels = sbase.vs_labels
Proof
  strip_tac >> fs[store_copy_frame_def] >>
  qpat_x_assum `store_copy_normalize _ _ = _`
    (mp_tac o Q.AP_TERM `\s. s.vs_labels`) >>
  simp[store_copy_normalize_def]
QED

Theorem topcopy_frame_call_ctx:
  store_copy_frame sa loc b k sbase i s ==> s.vs_call_ctx = sbase.vs_call_ctx
Proof
  strip_tac >> fs[store_copy_frame_def] >>
  qpat_x_assum `store_copy_normalize _ _ = _`
    (mp_tac o Q.AP_TERM `\s. s.vs_call_ctx`) >>
  simp[store_copy_normalize_def]
QED

Theorem topcopy_frame_frontier:
  store_copy_frame sa loc b k sbase i s ==> s.vs_alloca_next = sbase.vs_alloca_next
Proof
  strip_tac >> fs[store_copy_frame_def] >>
  qpat_x_assum `store_copy_normalize _ _ = _`
    (mp_tac o Q.AP_TERM `\s. s.vs_alloca_next`) >>
  simp[store_copy_normalize_def]
QED

Theorem topcopy_frame_operand:
  store_copy_frame sa loc b k sbase i s /\
  (!x. op = Var x ==> not_fresh_at sa x) /\
  eval_operand op sbase = SOME w ==>
  eval_operand op s = SOME w
Proof
  strip_tac >> drule topcopy_frame_labels >> strip_tac >>
  Cases_on `op` >> gvs[eval_operand_def, store_copy_frame_def] >>
  metis_tac[]
QED

Theorem topcopy_frame_load:
  store_copy_frame sa loc b k sbase i s ==> mload addr s = mload addr sbase
Proof
  strip_tac >> drule topcopy_frame_memory >> simp[mload_def]
QED

Theorem topcopy_frame_store:
  store_copy_frame sa loc b k sbase i s ==>
  store_copy_frame sa loc b k sbase (SUC i)
    ((if loc = LocStorage then sstore else tstore)
      (k + n2w i) (mload (w2n (b + n2w i * 32w)) sbase) s)
Proof
  simp[store_copy_frame_def, topcopy_prefix_suc, topcopy_normalize_store] >>
  strip_tac >> Cases_on `loc = LocStorage` >>
  gvs[sstore_def, tstore_def, lookup_var_def]
QED

Theorem topcopy_frame_index_bound:
  store_copy_frame sa loc b k sbase i s /\
  w2n b + 32*n <= sbase.vs_alloca_next /\ i < n ==>
  w2n b + 32*(i+1) <= s.vs_alloca_next
Proof
  strip_tac >> drule topcopy_frame_frontier >> decide_tac
QED
