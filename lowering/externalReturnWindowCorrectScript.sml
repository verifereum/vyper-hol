(* Fixed-function terminal bridge. The source is already normalized, or is
   an actual bytes/string singleton window supplied by externalReturnWindowSource.
   This does not establish S1 or widened-IntCall physical-memory availability. *)
Theory externalReturnWindowCorrect
Ancestors
  externalReturnWindowOwnership externalReturnWindowSource loweringReturnWindow
  loweringHalt vyperLoweringCorrect retAbiPlanProps e2eDefs

Theorem return_window_halt_result:
  ~lookup_raw_return_or_F (NONE : num option) tx.function_name External tops /\
  cx.sources = srcs /\ cx.layouts = layouts /\ cx.txn.target = tx.target /\
  (if nr /\ ~iv then release_nonreentrant_lock cx.txn.target nkey
   else vyperState$return ()) es = (INL (), es') /\
  state_rel func cenv cx es s /\ return_bytes tops ret v ss.vs_returndata /\
  ss.vs_accounts = s.vs_accounts /\
  ss.vs_transient =
    (if nr /\ ~iv then (tstore (n2w nkey) 0w s).vs_transient else s.vs_transient) /\
  ss.vs_logs = s.vs_logs /\ ss.vs_requests = s.vs_requests /\
  ss.vs_pending_deletions = s.vs_pending_deletions ==>
  external_call_result_rel tops ret tx
    (INL v, finalize_pending_deletions
      (abstract_machine_from_state srcs exps layouts es'), es'.requests) (Halt ss)
Proof
  strip_tac >> drule_all external_halt_success_unlock >>
  simp[external_call_result_rel_def, tx_return_bytes_def] >> metis_tac[]
QED

(* The ABI conversion links the window to the safely cast source result.
   Singleton bytes/string adapters retain type_memory_size in metadata but
   supply cap = 32 + LENGTH bs using val_footprint, not declared capacity. *)
Theorem external_return_abi_window_unlock_result_rel:
  ~lookup_raw_return_or_F (NONE : num option) tx.function_name External tops /\
  cx.sources = srcs /\ cx.layouts = layouts /\ cx.txn.target = tx.target /\
  compile_external_return (SOME op) F F ei msz nr nkey ut iv st = (x,sf) /\
  (nr /\ ~iv ==> ut) /\ (!y. op = Var y ==> not_fresh_at st y) /\
  (if nr /\ ~iv then release_nonreentrant_lock cx.txn.target nkey
   else vyperState$return ()) es = (INL (), es') /\
  evaluate_type (type_env tops) ret = SOME tv /\ safe_cast tv v0 = SOME v /\
  abi_enc_plan (type_env tops)
    (if needs_external_call_wrap ret /\
        is_dynamic (vyper_to_abi_type (type_env tops) ret)
     then TupleT [ret] else ret) ei /\
  vyper_abi_size_bound (type_env tops)
    (if needs_external_call_wrap ret /\
        is_dynamic (vyper_to_abi_type (type_env tops) ret)
     then TupleT [ret] else ret) <= msz /\
  fn_has_code st sf func /\ fn_inst_ids_distinct func /\
  state_rel func cenv cx es s /\ alloca_inv s /\ alloca_room ctx func s /\
  msz < dimword (:256) /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  (?sb cap av. eval_operand op s = SOME (n2w sb) /\
    vyper_to_abi (type_env tops)
      (if needs_external_call_wrap ret /\
          is_dynamic (vyper_to_abi_type (type_env tops) ret)
       then TupleT [ret] else ret)
      (if needs_external_call_wrap ret /\
          is_dynamic (vyper_to_abi_type (type_env tops) ret)
       then ArrayV (TupleV [v]) else v) = SOME av /\
    abi_encoder_window_input ei
      (vyper_to_abi_type (type_env tops)
        (if needs_external_call_wrap ret /\
            is_dynamic (vyper_to_abi_type (type_env tops) ret)
         then TupleT [ret] else ret)) av sb cap s.vs_memory /\
    return_window_ownership func op ei msz nkey ut iv st x sf sb cap s) ==>
  ?fuel ss. run_from fuel ctx func s = Halt ss /\
    external_call_result_rel tops ret tx
      (INL v, finalize_pending_deletions
        (abstract_machine_from_state srcs exps layouts es'), es'.requests) (Halt ss)
Proof
  strip_tac >> drule_all return_abi_window_value >> strip_tac >>
  drule_all return_window_ownership_resources >> strip_tac >>
  `av' = av` by
    (qpat_x_assum `vyper_to_abi _ _ _ = SOME av'` mp_tac >>
     asm_rewrite_tac [optionTheory.SOME_11] >> metis_tac[]) >>
  qpat_x_assum `av' = av` SUBST_ALL_TAC >>
  drule_all compile_external_return_window_unlock_run >> strip_tac >>
  qexistsl_tac [`fuel`, `ss`] >> conj_tac >- first_assum ACCEPT_TAC >>
  irule return_window_halt_result >> metis_tac[]
QED

Theorem external_return_abi_window_result_rel:
  ~lookup_raw_return_or_F (NONE : num option) tx.function_name External tops /\
  cx.sources = srcs /\ cx.layouts = layouts /\ cx.txn.target = tx.target /\
  compile_external_return (SOME op) F F ei msz nr nkey ut iv st = (x,sf) /\
  (nr ==> iv) /\ (!y. op = Var y ==> not_fresh_at st y) /\
  evaluate_type (type_env tops) ret = SOME tv /\ safe_cast tv v0 = SOME v /\
  abi_enc_plan (type_env tops)
    (if needs_external_call_wrap ret /\
        is_dynamic (vyper_to_abi_type (type_env tops) ret)
     then TupleT [ret] else ret) ei /\
  vyper_abi_size_bound (type_env tops)
    (if needs_external_call_wrap ret /\
        is_dynamic (vyper_to_abi_type (type_env tops) ret)
     then TupleT [ret] else ret) <= msz /\
  fn_has_code st sf func /\ fn_inst_ids_distinct func /\
  state_rel func cenv cx es s /\ alloca_inv s /\ alloca_room ctx func s /\
  msz < dimword (:256) /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  (?sb cap av. eval_operand op s = SOME (n2w sb) /\
    vyper_to_abi (type_env tops)
      (if needs_external_call_wrap ret /\
          is_dynamic (vyper_to_abi_type (type_env tops) ret)
       then TupleT [ret] else ret)
      (if needs_external_call_wrap ret /\
          is_dynamic (vyper_to_abi_type (type_env tops) ret)
       then ArrayV (TupleV [v]) else v) = SOME av /\
    abi_encoder_window_input ei
      (vyper_to_abi_type (type_env tops)
        (if needs_external_call_wrap ret /\
            is_dynamic (vyper_to_abi_type (type_env tops) ret)
         then TupleT [ret] else ret)) av sb cap s.vs_memory /\
    return_window_ownership func op ei msz nkey ut iv st x sf sb cap s) ==>
  ?fuel ss. run_from fuel ctx func s = Halt ss /\
    external_call_result_rel tops ret tx
      (INL v, finalize_pending_deletions
        (abstract_machine_from_state srcs exps layouts es), es.requests) (Halt ss)
Proof
  strip_tac >>
  `~(nr /\ ~iv)` by metis_tac[] >>
  `((if nr /\ ~iv then release_nonreentrant_lock cx.txn.target nkey
     else vyperState$return ()) es = (INL (),es))` by
    simp[vyperStateTheory.return_def] >>
  `(nr /\ ~iv ==> ut)` by simp[] >>
  drule_all (CONV_RULE (DEPTH_CONV LEFT_IMP_EXISTS_CONV)
    (SIMP_RULE bool_ss [PULL_EXISTS] external_return_abi_window_unlock_result_rel)) >>
  simp[]
QED

Theorem external_return_abi_window_cenv_result_rel:
  ~lookup_raw_return_or_F (NONE : num option) tx.function_name External tops /\
  cx.sources = srcs /\ cx.layouts = layouts /\ cx.txn.target = tx.target /\
  compile_external_return (SOME op) F F cenv.ce_ret_enc_info
    cenv.ce_max_return_size nr nkey ut iv st = (x,sf) /\
  cenv.ce_ret_enc_info = (update_cenv_ret_abi cenv0 ret).ce_ret_enc_info /\
  cenv.ce_max_return_size = (update_cenv_ret_abi cenv0 ret).ce_max_return_size /\
  cenv0.ce_struct_fields = make_struct_fields_map tops /\
  ALL_DISTINCT (FLAT (MAP (type_def_keys_toplevel (NONE:num option)) tops)) /\
  assignable_type (type_env tops) ret /\
  (nr ==> iv) /\ (!y. op = Var y ==> not_fresh_at st y) /\
  evaluate_type (type_env tops) ret = SOME tv /\ safe_cast tv v0 = SOME v /\
  fn_has_code st sf func /\ fn_inst_ids_distinct func /\
  state_rel func cenv cx es s /\ alloca_inv s /\ alloca_room ctx func s /\
  cenv.ce_max_return_size < dimword (:256) /\ ~s.vs_halted /\
  s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts /\
  (?sb cap av. eval_operand op s = SOME (n2w sb) /\
    vyper_to_abi (type_env tops)
      (if needs_external_call_wrap ret /\
          is_dynamic (vyper_to_abi_type (type_env tops) ret)
       then TupleT [ret] else ret)
      (if needs_external_call_wrap ret /\
          is_dynamic (vyper_to_abi_type (type_env tops) ret)
       then ArrayV (TupleV [v]) else v) = SOME av /\
    abi_encoder_window_input cenv.ce_ret_enc_info
      (vyper_to_abi_type (type_env tops)
        (if needs_external_call_wrap ret /\
            is_dynamic (vyper_to_abi_type (type_env tops) ret)
         then TupleT [ret] else ret)) av sb cap s.vs_memory /\
    return_window_ownership func op cenv.ce_ret_enc_info cenv.ce_max_return_size
      nkey ut iv st x sf sb cap s) ==>
  ?fuel ss. run_from fuel ctx func s = Halt ss /\
    external_call_result_rel tops ret tx
      (INL v, finalize_pending_deletions
        (abstract_machine_from_state srcs exps layouts es), es.requests) (Halt ss)
Proof
  strip_tac >> drule_all update_cenv_ret_abi_plan >> strip_tac >>
  `abi_enc_plan (type_env tops)
    (if needs_external_call_wrap ret /\
        is_dynamic (vyper_to_abi_type (type_env tops) ret)
     then TupleT [ret] else ret) cenv.ce_ret_enc_info` by
    asm_rewrite_tac [] >>
  `vyper_abi_size_bound (type_env tops)
    (if needs_external_call_wrap ret /\
        is_dynamic (vyper_to_abi_type (type_env tops) ret)
     then TupleT [ret] else ret) <= cenv.ce_max_return_size` by
    asm_rewrite_tac [arithmeticTheory.LESS_EQ_REFL] >>
  drule_all (CONV_RULE (DEPTH_CONV LEFT_IMP_EXISTS_CONV)
    (SIMP_RULE bool_ss [PULL_EXISTS] external_return_abi_window_result_rel)) >>
  simp[]
QED
