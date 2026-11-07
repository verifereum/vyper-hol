(* Saved payload words survive Pop even when shortening makes them dead.
   These facts use the source equation and the emitted instruction run, not
   the masked expression simulation postcondition. *)
Theory augAssignEffectfulHistory
Ancestors
  augAssignEffectfulRead exprSimPopStorage exprLoweringProps
  vyperStorageBackend vyperStorage venomState emitHelperProps vfmState
  emitHelper list venomExecSemantics

Theorem eval_pop_storage_saved_word:
  get_module_code cx src = SOME ts /\
  find_var_decl_by_name id ts = SOME (StorageVarDecl tr (ArrayT et (Dynamic n)), name) /\
  lookup_var_slot_from_layout cx tr src name = SOME slot /\
  evaluate_type (get_tenv cx) (ArrayT et (Dynamic n)) = SOME (ArrayTV tv (Dynamic n)) /\
  ~cx.txn.is_static /\
  lookup_storage (n2w slot) (get_storage cx es tr) <> 0w /\
  saved <> n2w slot ==>
  ?p es'. eval_expr cx (Pop ann (TopLevelNameTarget (src,id))) es = (INL p,es') /\
    lookup_storage saved (get_storage cx es' tr) =
    lookup_storage saved (get_storage cx es tr)
Proof
  strip_tac >> drule_all eval_pop_storage >>
  disch_then (qspecl_then [`es`, `ann`] assume_tac) >>
  fs[wordsTheory.w2n_eq_0] >>
  simp[get_storage_after_set, apply_writes_def, GSYM wordsTheory.word_add_n2w, wordsTheory.WORD_ADD_0,
       lookup_storage_def, update_storage_def, combinTheory.APPLY_UPDATE_THM]
QED

Theorem compile_pop_storage_saved_word:
  compile_dynarray_pop (Lit slot) 1 esz ctor imm
    (if tr then LocTransient else LocStorage) sa = (r,sb) /\
  ~s.vs_call_ctx.cc_static /\
  (if tr then tload slot s else sload slot s) <> 0w /\
  saved <> slot ==>
  ?u. run_inst_seq (emitted_insts sa sb) s = OK u /\
    (if tr then tload saved u else sload saved u) =
    (if tr then tload saved s else sload saved s)
Proof
  strip_tac >> drule dynarray_pop_storage_shape >> strip_tac >>
  `ALL_DISTINCT [x6;x5;x4;x3;x2;x1;x0]` by fs[ALL_DISTINCT] >>
  drule_all dynarray_pop_storage_run >>
  disch_then (qspecl_then [`sa.cs_next_id`, `esz`] strip_assume_tac) >>
  qexists `u` >> conj_tac
  >- fs[emitted_insts_def, DROP_PREFIX] >>
  qpat_x_assum `u = _` SUBST1_TAC >>
  Cases_on `tr` >>
  fs[sload_def, tload_def, sstore_def, tstore_def,
     contract_storage_def, contract_transient_def,
     lookup_account_def, lookup_storage_def, update_storage_def,
     combinTheory.APPLY_UPDATE_THM]
QED

(* In particular w may be the canonical typed encoding of a saved scalar.
   No liveness assumption is made about saved after Pop: it can be the
   last element of the old array. *)
Theorem pop_storage_saved_word_history:
  get_module_code cx src = SOME ts /\
  find_var_decl_by_name id ts = SOME (StorageVarDecl tr (ArrayT et (Dynamic n)), name) /\
  lookup_var_slot_from_layout cx tr src name = SOME slot /\
  evaluate_type (get_tenv cx) (ArrayT et (Dynamic n)) = SOME (ArrayTV tv (Dynamic n)) /\
  ~cx.txn.is_static /\
  lookup_storage (n2w slot) (get_storage cx es tr) <> 0w /\
  compile_dynarray_pop (Lit (n2w slot)) 1 (type_slot_size tv) ctor imm
    (if tr then LocTransient else LocStorage) sa = (r,sb) /\
  ~s.vs_call_ctx.cc_static /\
  (if tr then tload (n2w slot) s else sload (n2w slot) s) <> 0w /\
  saved <> n2w slot /\
  lookup_storage saved (get_storage cx es tr) = w /\
  (if tr then tload saved s else sload saved s) = w ==>
  ?p es' u.
    eval_expr cx (Pop ann (TopLevelNameTarget (src,id))) es = (INL p,es') /\
    run_inst_seq (emitted_insts sa sb) s = OK u /\
    lookup_storage saved (get_storage cx es' tr) = w /\
    (if tr then tload saved u else sload saved u) = w
Proof
  strip_tac >>
  drule_all eval_pop_storage_saved_word >>
  disch_then (qspec_then `ann` strip_assume_tac) >>
  drule_all compile_pop_storage_saved_word >> strip_tac >>
  qexistsl [`p`, `es'`, `u`] >> simp[]
QED
