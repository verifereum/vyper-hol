(* A reached noncopy positional suffix preserves a borrowed storage read. *)
Theory bodyLogReachedSlotMods
Ancestors
  bodyExtNoncopySourceMods vyperStorageBackend vyperStatePreservation
  vyperInterpreter exprLowering

Theorem log_reached_slot_read_mods:
  (!ty key actuals fallback.
    (source_body_call_supported cx key /\
      MEM key (linked_live_functions mods exps)) /\
    ~call_can_mutate cenv (IntCall key) /\
    state_rel_frame (\s t. machine_frame (s with logs := t.logs) t)
      (eval_exprs cx actuals) ==>
    state_rel_frame (\s t. machine_frame (s with logs := t.logs) t)
      (eval_expr cx (Call ty (IntCall key) actuals fallback))) /\
  ~exprs_can_mutate cenv ys /\
  EVERY (\k. source_body_call_supported cx k) (int_calls_exprs ys) /\
  EVERY (\k. MEM k (linked_live_functions mods exps)) (int_calls_exprs ys) /\
  eval_exprs cx ys (mid with gas_obs := obs) = (INL vs,ee) /\
  read_storage_slot cx tr w tv mid = (INL v,mid) ==>
  read_storage_slot cx tr w tv ee = (INL v,ee)
Proof
  strip_tac >>
  drule_all ext_noncopy_suffix_frame_mods >> strip_tac >>
  `get_storage cx ee tr = get_storage cx mid tr` by
    (qpat_assum `!tr. get_storage cx ee tr = get_storage cx mid tr`
       (qspec_then `tr` ACCEPT_TAC)) >>
  qpat_x_assum `read_storage_slot cx tr w tv mid = (INL v,mid)`
    (strip_assume_tac o SIMP_RULE bool_ss [read_storage_slot_eq]) >>
  simp[read_storage_slot_eq] >>
  Cases_on `decode_value (get_storage cx mid tr) (w2n w) tv` >> gvs[]
QED
