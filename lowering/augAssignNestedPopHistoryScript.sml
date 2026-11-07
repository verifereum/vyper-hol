(* Relational history for the actual computed-header Pop suffix.
   Prefix target evaluation and modifying calls are outside this boundary. *)
Theory augAssignNestedPopHistory
Ancestors
  exprSimPopNestedBase vyperStorageBackend vyperStorage vyperState
  venomState venomExecSemantics vfmState list

Theorem nested_pop_saved_word_history:
  ALL_DISTINCT [x6;x5;x4;x3;x2;x1;x0] /\
  eval_operand hdr s = SOME slot /\
  (!x. hdr = Var x ==> ~MEM x [x0;x1;x2;x3;x4;x5;x6]) /\
  ~cx.txn.is_static /\ ~s.vs_call_ctx.cc_static /\
  lookup_storage slot (get_storage cx es tr) <> 0w /\
  (if tr then tload slot s else sload slot s) =
    lookup_storage slot (get_storage cx es tr) /\
  (if tr then tload saved s else sload saved s) =
    lookup_storage saved (get_storage cx es tr) ==>
  ?pv es' u.
    pop_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic cap))) es = (INL pv,es') /\
    run_inst_seq (nested_pop_suffix hdr tr id (type_slot_size tv)
      x0 x1 x2 x3 x4 x5 x6) s = OK u /\
    (if tr then tload saved u else sload saved u) =
      lookup_storage saved (get_storage cx es' tr)
Proof
  strip_tac >>
  `(if tr then tload slot s else sload slot s) <> 0w` by metis_tac[] >>
  drule_all nested_pop_suffix_run >>
  disch_then (qspecl_then [`id`, `type_slot_size tv`] strip_assume_tac) >>
  simp[pop_place_def, get_storage_backend_eq, bind_def, ignore_bind_def,
       check_def, assert_def, return_def, write_storage_slot_eq] >>
  `0 < w2n (lookup_storage slot (get_storage cx es tr))` by
    (Cases_on `lookup_storage slot (get_storage cx es tr)` >> gvs[]) >>
  simp[encode_value_def, encode_base_to_slot_def, integer_wordTheory.i2w_pos] >>
  simp[get_storage_after_set, apply_writes_def] >>
  qpat_x_assum `u = _` SUBST1_TAC >>
  Cases_on `tr` >> gvs[] >>
  Cases_on `saved = slot` >> gvs[] >>
  fs[sload_def, tload_def, sstore_def, tstore_def,
     contract_storage_def, contract_transient_def,
     lookup_account_def, lookup_storage_def, update_storage_def,
     combinTheory.APPLY_UPDATE_THM, GSYM wordsTheory.word_add_n2w,
     wordsTheory.WORD_ADD_0] >>
  simp[wordsTheory.n2w_sub]
QED
