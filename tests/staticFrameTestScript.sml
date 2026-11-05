(* Static call frames: where the source and Venom semantics fail, and what
   a static frame's outgoing calls look like. *)
Theory staticFrameTest
Ancestors
  vyperState vyperInterpreter venomExecSemantics venomInst venomState

(* ----- Source ----- *)

Theorem static_storage_write_fails:
  cx.txn.is_static ==>
  write_storage_slot cx is_transient slot tv v st =
    (INR (Error (RuntimeError "write in static context")), st)
Proof
  simp[write_storage_slot_def, check_not_static_def, check_def, assert_def,
       bind_def, ignore_bind_def]
QED

Theorem static_call_value_fails:
  cx.txn.is_static /\ amount <> 0 ==>
  frame_call_value cx (SOME amount) st =
    (INR (Error (RuntimeError "write in static context")), st)
Proof
  simp[frame_call_value_def, check_def, assert_def, bind_def, ignore_bind_def]
QED

(* NONE is a static call: call_outcome_request and make_ext_call_state
   both read it so. *)
Theorem static_call_zero_value_is_static:
  cx.txn.is_static ==>
  frame_call_value cx (SOME 0) st = (INL NONE, st) /\
  frame_call_value cx NONE st = (INL NONE, st)
Proof
  simp[frame_call_value_def, check_def, assert_def, bind_def, ignore_bind_def,
       return_def]
QED

Theorem nonstatic_call_value_unchanged:
  ~cx.txn.is_static ==> frame_call_value cx value_opt st = (INL value_opt, st)
Proof
  simp[frame_call_value_def, return_def]
QED

(* A static frame entering a nonreentrant non-view function checks the lock,
   then fails without taking it. *)
Theorem static_nonreentrant_entry_fails_lock_free:
  cx.txn.is_static /\ cx.nonreentrant_slot = SOME slot /\
  vfmState$lookup_storage (n2w slot)
    (vfmExecution$lookup_transient_storage cx.txn.target st.tStorage) <> 1w ==>
  lock_if_nr cx T F st =
    (INR (Error (RuntimeError "write in static context")), st)
Proof
  simp[lock_if_nr_def, acquire_nonreentrant_lock_def, check_not_static_def,
       check_def, assert_def, bind_def, ignore_bind_def, return_def,
       get_transient_storage_def]
QED

Theorem static_nonreentrant_entry_fails_lock_held:
  cx.txn.is_static /\ cx.nonreentrant_slot = SOME slot /\
  vfmState$lookup_storage (n2w slot)
    (vfmExecution$lookup_transient_storage cx.txn.target st.tStorage) = 1w ==>
  lock_if_nr cx T F st =
    (INR (Error (RuntimeError "nonreentrant lock")), st)
Proof
  simp[lock_if_nr_def, acquire_nonreentrant_lock_def, bind_def,
       ignore_bind_def, raise_def, get_transient_storage_def]
QED

Theorem static_nonreentrant_view_entry_succeeds:
  cx.nonreentrant_slot = SOME slot /\
  vfmState$lookup_storage (n2w slot)
    (vfmExecution$lookup_transient_storage cx.txn.target st.tStorage) <> 1w ==>
  lock_if_nr cx T T st = (INL (), st)
Proof
  simp[lock_if_nr_def, acquire_nonreentrant_lock_def, bind_def,
       ignore_bind_def, return_def, get_transient_storage_def]
QED

(* ----- Venom ----- *)

Theorem venom_static_sstore_aborts:
  s.vs_call_ctx.cc_static ==>
  step_inst_base (mk_inst 0 SSTORE [Lit 0w; Lit 1w] []) s =
    Abort ExHalt_abort (halt_state (set_returndata [] s))
Proof
  simp[Once step_inst_base_def, mk_inst_def, eval_operands_def,
       eval_operand_def]
QED

Theorem venom_static_tstore_aborts:
  s.vs_call_ctx.cc_static ==>
  step_inst_base (mk_inst 0 TSTORE [Lit 0w; Lit 1w] []) s =
    Abort ExHalt_abort (halt_state (set_returndata [] s))
Proof
  simp[Once step_inst_base_def, mk_inst_def, eval_operands_def,
       eval_operand_def]
QED

Theorem venom_static_log_aborts:
  s.vs_call_ctx.cc_static ==>
  step_inst_base (mk_inst 0 LOG [Lit 0w; Lit 0w; Lit 0w] []) s =
    Abort ExHalt_abort (halt_state (set_returndata [] s))
Proof
  simp[Once step_inst_base_def, mk_inst_def, eval_operands_def,
       eval_operand_def]
QED

Theorem venom_static_call_with_value_aborts:
  s.vs_call_ctx.cc_static ==>
  step_inst_base
    (mk_inst 0 CALL [Lit 0w; Lit 0w; Lit 1w; Lit 0w; Lit 0w; Lit 0w; Lit 0w]
       ["r"]) s =
    Abort ExHalt_abort (halt_state (set_returndata [] s))
Proof
  simp[Once step_inst_base_def, mk_inst_def, eval_operand_def]
QED

(* A value-0 CALL from a static frame goes out as a static call. *)
Theorem venom_static_call_zero_value_is_static:
  s.vs_call_ctx.cc_static ==>
  step_inst_base
    (mk_inst 0 CALL [Lit 0w; Lit 0w; Lit 0w; Lit 0w; Lit 0w; Lit 0w; Lit 0w]
       ["r"]) s =
    exec_ext_call
      (mk_inst 0 CALL [Lit 0w; Lit 0w; Lit 0w; Lit 0w; Lit 0w; Lit 0w; Lit 0w]
         ["r"]) s 0w 0w 0w 0w 0w 0w 0w T
Proof
  simp[Once step_inst_base_def, mk_inst_def, eval_operand_def]
QED

Theorem venom_nonstatic_sstore_succeeds:
  ~s.vs_call_ctx.cc_static ==>
  ?t. step_inst_base (mk_inst 0 SSTORE [Lit 0w; Lit 1w] []) s = OK t
Proof
  simp[Once step_inst_base_def, mk_inst_def, eval_operands_def,
       eval_operand_def, exec_write2_def]
QED
