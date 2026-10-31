(*
 * Vyper-to-Venom Lowering Correctness (Top-Level)
 *
 * Upstream: vyperlang/vyper@a7f7bf133
 *
 * Connects Vyper big-step semantics (call_external) to Venom IR
 * execution (run_context) on the raw lower_vyper_runtime_unit context.
 *
 * Three-layer decomposition:
 *   Layer 1 - Selector dispatch: calldata method_id routes to correct
 *     entry block (selectorDispatch, per compile_selector_dispatch)
 *   Layer 2 - Argument decoding: ABI-encoded calldata decoded to values
 *     matching tx.args (abiEncoderProps, valueEncodingProofs)
 *   Layer 3 - Function body: compiled Venom body preserves semantics
 *     (stmtLoweringProps, exprLoweringProps)
 *
 * TOP-LEVEL:
 *   venom_env_rel, initial_venom_state_rel -- PLAN 5.7 entry boundary
 *   external_call_result_rel, source_unit_execution_correct -- oracle boundary
 *   compile_state_ok_initial -- label-space invariant of the initial compile state
 *   external_return_word_result_rel, external_return_prim_result_rel,
 *   external_return_static_result_rel, external_return_abi_result_rel,
 *   external_return_static_cenv_result_rel,
 *   external_return_abi_cenv_result_rel,
 *   external_return_none_result_rel,
 *   external_fallthrough_result_rel -- S1 halt bridge (#640) for the
 *     return sequences loweringHalt covers, and their _unlock versions,
 *     whose return may release a transient nonreentrant lock
 *   lower_vyper_runtime_unit_correct -- S1 (planned admission, Milestone 6)
 *   lower_vyper_runtime_unit_source_unit_ok -- S2 (Milestone 5)
 *   lower_vyper_runtime_unit_memory_ok -- S3 (Milestone 5)
 *
 * TASK056: obsolete NONE-mode relation retained as inactive source provenance.
 * STATUS: S2 is proved; S1 and S3 are statements, NOT proved correctness
 *   certificates.
 * Before major proof repair, check lowering definitions against the chosen
 * upstream compiler target; see docs/compiler-definition-parity.md.
 *)

Theory vyperLoweringCorrect
Ancestors
  vyperCompiler
  selectorDispatch
  moduleLoweringProps
  stmtLoweringProps
  exprLoweringProps
  valueEncodingProofs
  builtinProps
  contextProps
  arithmeticProps
  abiEncoderProps
  vyperInterpreter
  vyperContext
  venomExecSemantics
  venomState
  compileEnv e2eDefs supportedProgram compileVyper immutableSectionRel
  unitTransformDefs unitShapeDefs
  fragExec loweringHalt loweringShapeProps retAbiPlanProps

(* TASK056 RETIRED SOURCE ARCHIVE: old NONE-mode helpers, replaced by the
   exact oracle-mode boundary below. Original text retained without bridges.
(* ===== Cross-Domain Result Relation ===== *)

(* Observable state produced by an external source call. Function-local scope
   state is gone at this boundary, so this is intentionally smaller than
   compileEnv$state_rel but still includes all externally visible effects. *)
Definition external_logs_rel_def:
  external_logs_rel cenv (addr : address) (am : abstract_machine) ss ⇔
    LIST_REL (log_entry_equiv cenv addr) am.logs ss.vs_logs
End

Definition external_call_state_rel_def:
  external_call_state_rel cenv cx (am : abstract_machine) ss ⇔
    ss.vs_accounts = am.accounts ∧
    ss.vs_transient = am.tStorage ∧
    external_logs_rel cenv cx.txn.target am ss ∧
    call_ctx_rel cx.txn ss.vs_call_ctx ss.vs_tx_ctx ss.vs_block_ctx
End

(* Relates Vyper external call results to Venom execution results.
   call_external_simple projects the NONE-mode result to
   (value + exception, abstract_machine). No oracle-mode bridge is claimed.
   run_context returns exec_result.

   Parameterized by tenv (type environment), cenv/cx (the lowering
   state relation context), and ret_type (return type) for ABI encoding
   of the return value.

   Success case requires the external-call state relation, so logs,
   accounts, transient storage, call context, and returndata are all part
   of the lowering result relation instead of e2e-side patches. *)
(* TASK051 compatibility: the original NONE-mode result contract, unchanged
   except its explicit name. No old/new semantic bridge. Removal TASK056. *)
Definition external_call_result_rel_legacy_def:
  (* Successful return *)
  (external_call_result_rel_legacy tenv cenv cx ret_type (INL v, am') (Halt ss') <=>
    cenv.ce_type_env = tenv /\
    external_call_state_rel cenv cx am' ss' /\
    (?abi_val.
      vyper_to_abi tenv ret_type v = SOME abi_val /\
      ss'.vs_returndata =
        enc (vyper_to_abi_type tenv ret_type) abi_val)) /\
  (* Assert/revert => Abort revert *)
  (external_call_result_rel_legacy tenv cenv cx ret_type (INR (AssertException _), am')
                             (Abort Revert_abort ss') <=> T) /\
  (* Vyper error => any Venom abort or error *)
  (external_call_result_rel_legacy tenv cenv cx ret_type (INR (Error _), am')
                             (Abort _ ss') <=> T) /\
  (external_call_result_rel_legacy tenv cenv cx ret_type (INR (Error _), am')
                             (Error _) <=> T) /\
  (* All other combinations are invalid *)
  (external_call_result_rel_legacy _ _ _ _ _ _ <=> F)
End

*)

(* ===== PLAN 5.7 oracle-mode boundary ===== *)

(* No gas-reading/oracle equality is invented here: cc_gas, outcomes,
   code/labels and frame-pointer fields are deliberately free at entry. *)
Definition venom_env_rel_def:
  venom_env_rel tx vs <=>
    compileEnv$call_ctx_rel tx vs.vs_call_ctx vs.vs_tx_ctx vs.vs_block_ctx /\
    ~vs.vs_call_ctx.cc_static /\
    vs.vs_prev_hashes = tx.block_hashes /\
    (!n. vs.vs_block_ctx.bc_blockhash n =
         let idx = tx.block_number - n - 1 in
         if n < tx.block_number /\ tx.block_number - 256 <= n /\
            idx < LENGTH tx.block_hashes
         then EL idx tx.block_hashes else 0w)
End

Definition initial_venom_state_rel_def:
  initial_venom_state_rel tops am tx vs <=>
    value_transfer_ok tx am.accounts /\
    vs.vs_accounts = accounts_after_transfer tx am.accounts /\
    vs.vs_transient = am.tStorage /\ am.logs = [] /\ vs.vs_logs = [] /\
    am.pending_deletions = [] /\
    tx_env_ok tx /\ venom_env_rel tx vs /\
    vs.vs_vars = FEMPTY /\ ~vs.vs_halted /\ vs.vs_memory = [] /\
    vs.vs_allocas = FEMPTY /\ vs.vs_alloca_next = 0 /\
    vs.vs_returndata = [] /\ vs.vs_requests = [] /\
    immutables_section_rel tops (account_immutables am tx.target) vs.vs_data_section
End

(* The calldata Venom reads is the transaction's, which the source typing
   bounds; dispatch and the entry checks need the bound. *)
Theorem call_ctx_rel_calldata_length:
  call_tx_well_typed tx /\ call_ctx_rel tx cc tc bc ==>
  LENGTH cc.cc_calldata < dimword (:256)
Proof
  rw[vyperTypeContractSoundnessTheory.call_tx_well_typed_def,
     call_ctx_rel_def] >>
  simp[wordsTheory.dimword_def]
QED

Theorem initial_venom_state_calldata_length:
  source_typing_ok tops am tx /\ initial_venom_state_rel tops am tx vs ==>
  LENGTH vs.vs_call_ctx.cc_calldata < dimword (:256)
Proof
  rw[source_typing_ok_def, initial_venom_state_rel_def, venom_env_rel_def] >>
  drule_all call_ctx_rel_calldata_length >> simp[]
QED

(* Only success compares effects/requests. Runtime failure must abort, except
   the exact dynamic strict-decoding exemption on Halt. A failed external call
   (RevertData) must REVERT; as for assertions, the revert data itself is not
   compared. Error (stuck or fuel exhaustion), OK and IntRet are never
   acceptable results, even if exempt.
   Effects are compared up to dead bytes (storage_dead): the called
   contract's storage and transient storage, at the end and in each
   request's snapshot, agree with the source's except at bytes past a
   bytestring's (or nested DynArray's) length, which the lowering's
   full-capacity copy may overwrite and nothing reads.  The declared regions
   are those of tx.target in am'. *)
Definition external_call_result_rel_def:
  external_call_result_rel tops ret tx (res, am', rqs) vres <=>
    let cx = initial_evaluation_context am'.sources am'.layouts tx NONE in
    case (res, vres) of
      (INL v, Halt ss) =>
        return_bytes tops ret v ss.vs_returndata /\
        accounts_agree cx am'.accounts ss.vs_accounts /\
        transient_agree cx am'.tStorage ss.vs_transient /\
        logs_correspond (compiled_event_info tops) (type_env tops)
          tx.target am'.logs ss.vs_logs /\
        LIST_REL (request_agree cx) rqs ss.vs_requests
    | (INR (AssertException s), Abort Revert_abort _) => T
    | (INR (AssertException s), Abort ExHalt_abort _) => (s = "UNREACHABLE")
    | (INR (Error (RevertData _)), Abort Revert_abort _) => T
    | (INR (Error (RuntimeError m)), Abort _ _) => T
    | (INR (Error e), Halt _) => unspecified_behaviour_exempt tops e
    | _ => F
End

Definition source_unit_execution_correct_def:
  source_unit_execution_correct tops ret am tx unit vs <=>
    ?fuel. external_call_result_rel tops ret tx
             (call_external (SOME vs.vs_outcomes) am tx)
             (run_context fuel unit.cu_context vs)
End

(* ===== S1 halt bridge (#640) ===== *)

Theorem abstract_machine_from_state_context[local,simp]:
  (abstract_machine_from_state srcs exps layouts es).sources = srcs /\
  (abstract_machine_from_state srcs exps layouts es).layouts = layouts
Proof
  simp[abstract_machine_from_state_def]
QED

(* An external function's return sequences, run from state_rel at the
   return (whose accounts_rel gives every address's accounts and transient
   storage as in the source, with no pending deletions), halt in the
   success case of external_call_result_rel.  The source result is the one
   call_external_function builds: the returned value cast to the return
   type (NoneV when the body returns without a value or falls off its
   end), the machine of the state es' after the lock is released, with its
   pending deletions processed, and the requests of es'.  The statement
   simulation (#637) brings the run to the return, the entry bridge (#639)
   runs up to the body, and S1 (#642) composes them.

   The _unlock theorems allow a return that releases a transient
   nonreentrant lock (nr /\ ~iv ==> ut).  es' is es after the source
   releases the lock at the compiler's key nkey, as call_external_function
   does at cx.nonreentrant_slot.  S1 links nkey to cx.nonreentrant_slot,
   and the compiler's iv to the source's is_view; the lowering does not
   use transient locks yet (#564).  The theorems without _unlock are their
   case with no release (nr ==> iv), where es' = es. *)

(* Returning a value of a word type (is_word_type: bool, integers,
   decimal, flag, address, bytesN).  The operand holds the value's word at
   the return type tv, typed_val_to_w256 tv v0; compile_name_correct gives
   a local's word at its own type, which agrees with this one when the two
   types do. *)
Theorem external_return_prim_unlock_result_rel:
  !ctx op ei msz nr nkey ut iv st x st' func cenv cx es es' tenv ret tv v0 v
     tops tx srcs exps layouts Q.
    cx.sources = srcs /\ cx.layouts = layouts /\ cx.txn.target = tx.target /\
    compile_external_return (SOME op) T F ei msz nr nkey ut iv st =
      (x, st') /\
    (nr /\ ~iv ==> ut) /\ (!y. op = Var y ==> not_fresh_at st y) /\
    (if nr /\ ~iv then release_nonreentrant_lock cx.txn.target nkey
     else vyperState$return ()) es = (INL (), es') /\
    evaluate_type tenv ret = SOME tv /\ safe_cast tv v0 = SOME v /\
    is_word_type ret ==>
    frag_exec ctx st st'
      (\s. state_rel func cenv cx es s /\
           eval_operand op s = SOME (typed_val_to_w256 tv v0))
      Q
      (external_call_result_rel tops ret tx
         (INL v, finalize_pending_deletions
                   (abstract_machine_from_state srcs exps layouts es'),
          es'.requests))
Proof
  rpt strip_tac >>
  qspecl_then [`tops`, `tenv`, `ret`, `tv`, `v0`, `v`] mp_tac
    return_bytes_prim_value >>
  impl_tac >- asm_rewrite_tac[] >> strip_tac >>
  qspecl_then [`ctx`, `op`, `ei`, `msz`, `nr`, `nkey`, `ut`, `iv`, `st`,
               `x`, `st'`, `typed_val_to_w256 tv v0`] mp_tac
    compile_external_return_word_unlock_frag >>
  simp[] >> disch_then irule >> simp[] >> rpt strip_tac >>
  qspecl_then [`func`, `cenv`, `cx`, `es`, `es'`, `s`, `ss`, `nr`, `nkey`,
               `iv`, `tops`, `tx`, `srcs`, `exps`, `layouts`] mp_tac
    external_halt_success_unlock >>
  impl_tac >- gvs[] >>
  strip_tac >> gvs[external_call_result_rel_def]
QED

(* Its case for the values word_value covers, whose word is val_to_w256. *)
Theorem external_return_word_unlock_result_rel:
  !ctx op ei msz nr nkey ut iv st x st' func cenv cx es es' tenv ret tv v0 v
     tops tx srcs exps layouts Q.
    cx.sources = srcs /\ cx.layouts = layouts /\ cx.txn.target = tx.target /\
    compile_external_return (SOME op) T F ei msz nr nkey ut iv st =
      (x, st') /\
    (nr /\ ~iv ==> ut) /\ (!y. op = Var y ==> not_fresh_at st y) /\
    (if nr /\ ~iv then release_nonreentrant_lock cx.txn.target nkey
     else vyperState$return ()) es = (INL (), es') /\
    evaluate_type tenv ret = SOME tv /\ safe_cast tv v0 = SOME v /\
    word_value v0 ==>
    frag_exec ctx st st'
      (\s. state_rel func cenv cx es s /\
           eval_operand op s = SOME (val_to_w256 v0))
      Q
      (external_call_result_rel tops ret tx
         (INL v, finalize_pending_deletions
                   (abstract_machine_from_state srcs exps layouts es'),
          es'.requests))
Proof
  rpt strip_tac >>
  drule_all word_value_prim >> strip_tac >>
  qpat_x_assum `typed_val_to_w256 _ _ = _` (REWRITE_TAC o single o GSYM) >>
  qspecl_then [`ctx`, `op`, `ei`, `msz`, `nr`, `nkey`, `ut`, `iv`, `st`,
               `x`, `st'`, `func`, `cenv`, `cx`, `es`, `es'`, `tenv`, `ret`,
               `tv`, `v0`, `v`, `tops`, `tx`, `srcs`, `exps`, `layouts`, `Q`]
    mp_tac external_return_prim_unlock_result_rel >>
  simp[]
QED

(* A return without a value. *)
Theorem external_return_none_unlock_result_rel:
  !ctx cenv lctx ty st x st' nr nkey ut iv func cx es es' tops tx srcs exps
     layouts Q.
    cx.sources = srcs /\ cx.layouts = layouts /\ cx.txn.target = tx.target /\
    compile_stmt cenv lctx ty (Return NONE) st = (x, st') /\
    cenv.ce_return_pc = NONE /\
    cenv.ce_nonreentrant = (nr, nkey, ut, iv) /\ (nr /\ ~iv ==> ut) /\
    (if nr /\ ~iv then release_nonreentrant_lock cx.txn.target nkey
     else vyperState$return ()) es = (INL (), es') ==>
    frag_exec ctx st st'
      (\s. state_rel func cenv cx es s)
      Q
      (external_call_result_rel tops NoneT tx
         (INL NoneV, finalize_pending_deletions
                       (abstract_machine_from_state srcs exps layouts es'),
          es'.requests))
Proof
  rpt strip_tac >>
  qspecl_then [`ctx`, `cenv`, `lctx`, `ty`, `st`, `x`, `st'`, `nr`, `nkey`,
               `ut`, `iv`] mp_tac compile_return_none_external_unlock_frag >>
  simp[] >> disch_then irule >> simp[] >> rpt strip_tac >>
  qspecl_then [`func`, `cenv`, `cx`, `es`, `es'`, `s`, `ss`, `nr`, `nkey`,
               `iv`, `tops`, `tx`, `srcs`, `exps`, `layouts`] mp_tac
    external_halt_success_unlock >>
  impl_tac >- gvs[] >>
  strip_tac >> gvs[external_call_result_rel_def, return_bytes_def]
QED

(* Falling off the end of a function without a return type: from the end
   sb of the body's code, when it does not end its block. *)
Theorem external_fallthrough_unlock_result_rel:
  !ctx cenv nr nkey ut iv stmts st x st' sa sb func cx es es' tops tx srcs
     exps layouts Q.
    cx.sources = srcs /\ cx.layouts = layouts /\ cx.txn.target = tx.target /\
    compile_guarded_body cenv nr nkey ut iv stmts NONE st = (x, st') /\
    (nr /\ ~iv ==> ut) /\
    (if nr then compile_nonreentrant_lock nkey ut iv else comp_return ()) st =
      ((), sa) /\
    compile_stmts cenv NoLoop (BaseT BoolT) stmts sa = ((), sb) /\
    ~block_is_terminated sb /\
    (if nr /\ ~iv then release_nonreentrant_lock cx.txn.target nkey
     else vyperState$return ()) es = (INL (), es') ==>
    frag_exec ctx sb st'
      (\s. state_rel func cenv cx es s)
      Q
      (external_call_result_rel tops NoneT tx
         (INL NoneV, finalize_pending_deletions
                       (abstract_machine_from_state srcs exps layouts es'),
          es'.requests))
Proof
  rpt strip_tac >>
  qspecl_then [`ctx`, `cenv`, `nr`, `nkey`, `ut`, `iv`, `stmts`, `st`, `x`,
               `st'`, `sa`, `sb`] mp_tac
    compile_guarded_body_stop_unlock_frag >>
  simp[] >> disch_then irule >> simp[] >> rpt strip_tac >>
  qspecl_then [`func`, `cenv`, `cx`, `es`, `es'`, `s`, `ss`, `nr`, `nkey`,
               `iv`, `tops`, `tx`, `srcs`, `exps`, `layouts`] mp_tac
    external_halt_success_unlock >>
  impl_tac >- gvs[] >>
  strip_tac >> gvs[external_call_result_rel_def, return_bytes_def]
QED

(* The same four with no release (nr ==> iv). *)
Theorem external_return_prim_result_rel:
  !ctx op ei msz nr nkey ut iv st x st' func cenv cx es tenv ret tv v0 v
     tops tx srcs exps layouts Q.
    cx.sources = srcs /\ cx.layouts = layouts /\ cx.txn.target = tx.target /\
    compile_external_return (SOME op) T F ei msz nr nkey ut iv st =
      (x, st') /\
    (nr ==> iv) /\ (!y. op = Var y ==> not_fresh_at st y) /\
    evaluate_type tenv ret = SOME tv /\ safe_cast tv v0 = SOME v /\
    is_word_type ret ==>
    frag_exec ctx st st'
      (\s. state_rel func cenv cx es s /\
           eval_operand op s = SOME (typed_val_to_w256 tv v0))
      Q
      (external_call_result_rel tops ret tx
         (INL v, finalize_pending_deletions
                   (abstract_machine_from_state srcs exps layouts es),
          es.requests))
Proof
  rpt strip_tac >>
  qspecl_then [`ctx`, `op`, `ei`, `msz`, `nr`, `nkey`, `ut`, `iv`, `st`,
               `x`, `st'`, `func`, `cenv`, `cx`, `es`, `es`, `tenv`, `ret`,
               `tv`, `v0`, `v`, `tops`, `tx`, `srcs`, `exps`, `layouts`, `Q`]
    mp_tac external_return_prim_unlock_result_rel >>
  impl_tac
  >- (Cases_on `nr` >> Cases_on `iv` >> gvs[vyperStateTheory.return_def]) >>
  simp[]
QED

Theorem external_return_word_result_rel:
  !ctx op ei msz nr nkey ut iv st x st' func cenv cx es tenv ret tv v0 v
     tops tx srcs exps layouts Q.
    cx.sources = srcs /\ cx.layouts = layouts /\ cx.txn.target = tx.target /\
    compile_external_return (SOME op) T F ei msz nr nkey ut iv st =
      (x, st') /\
    (nr ==> iv) /\ (!y. op = Var y ==> not_fresh_at st y) /\
    evaluate_type tenv ret = SOME tv /\ safe_cast tv v0 = SOME v /\
    word_value v0 ==>
    frag_exec ctx st st'
      (\s. state_rel func cenv cx es s /\
           eval_operand op s = SOME (val_to_w256 v0))
      Q
      (external_call_result_rel tops ret tx
         (INL v, finalize_pending_deletions
                   (abstract_machine_from_state srcs exps layouts es),
          es.requests))
Proof
  rpt strip_tac >>
  qspecl_then [`ctx`, `op`, `ei`, `msz`, `nr`, `nkey`, `ut`, `iv`, `st`,
               `x`, `st'`, `func`, `cenv`, `cx`, `es`, `es`, `tenv`, `ret`,
               `tv`, `v0`, `v`, `tops`, `tx`, `srcs`, `exps`, `layouts`, `Q`]
    mp_tac external_return_word_unlock_result_rel >>
  impl_tac
  >- (Cases_on `nr` >> Cases_on `iv` >> gvs[vyperStateTheory.return_def]) >>
  simp[]
QED

Theorem external_return_none_result_rel:
  !ctx cenv lctx ty st x st' nr nkey ut iv func cx es tops tx srcs exps
     layouts Q.
    cx.sources = srcs /\ cx.layouts = layouts /\ cx.txn.target = tx.target /\
    compile_stmt cenv lctx ty (Return NONE) st = (x, st') /\
    cenv.ce_return_pc = NONE /\
    cenv.ce_nonreentrant = (nr, nkey, ut, iv) /\ (nr ==> iv) ==>
    frag_exec ctx st st'
      (\s. state_rel func cenv cx es s)
      Q
      (external_call_result_rel tops NoneT tx
         (INL NoneV, finalize_pending_deletions
                       (abstract_machine_from_state srcs exps layouts es),
          es.requests))
Proof
  rpt strip_tac >>
  qspecl_then [`ctx`, `cenv`, `lctx`, `ty`, `st`, `x`, `st'`, `nr`, `nkey`,
               `ut`, `iv`, `func`, `cx`, `es`, `es`, `tops`, `tx`, `srcs`,
               `exps`, `layouts`, `Q`]
    mp_tac external_return_none_unlock_result_rel >>
  impl_tac
  >- (Cases_on `nr` >> Cases_on `iv` >> gvs[vyperStateTheory.return_def]) >>
  simp[]
QED

Theorem external_fallthrough_result_rel:
  !ctx cenv nr nkey ut iv stmts st x st' sa sb func cx es tops tx srcs exps
     layouts Q.
    cx.sources = srcs /\ cx.layouts = layouts /\ cx.txn.target = tx.target /\
    compile_guarded_body cenv nr nkey ut iv stmts NONE st = (x, st') /\
    (nr ==> iv) /\
    (if nr then compile_nonreentrant_lock nkey ut iv else comp_return ()) st =
      ((), sa) /\
    compile_stmts cenv NoLoop (BaseT BoolT) stmts sa = ((), sb) /\
    ~block_is_terminated sb ==>
    frag_exec ctx sb st'
      (\s. state_rel func cenv cx es s)
      Q
      (external_call_result_rel tops NoneT tx
         (INL NoneV, finalize_pending_deletions
                       (abstract_machine_from_state srcs exps layouts es),
          es.requests))
Proof
  rpt strip_tac >>
  qspecl_then [`ctx`, `cenv`, `nr`, `nkey`, `ut`, `iv`, `stmts`, `st`, `x`,
               `st'`, `sa`, `sb`, `func`, `cx`, `es`, `es`, `tops`, `tx`,
               `srcs`, `exps`, `layouts`, `Q`]
    mp_tac external_fallthrough_unlock_result_rel >>
  impl_tac
  >- (Cases_on `nr` >> Cases_on `iv` >> gvs[vyperStateTheory.return_def]) >>
  simp[]
QED

(* A return of a static complex value (tuple, struct, fixed array), with
   the optional unlock first: the operand points at memory holding the
   value, and the returned AbiCopy size is its memory size.  The size is
   below dimword, so the size literal of the copy and the RETURN does not
   wrap; nothing in the lowering bounds it (vyper rejects allocations of
   2^64 bytes or more). *)
Theorem external_return_static_unlock_result_rel:
  !ctx op m msz nr nkey ut iv st x st' func cenv cx es es' ret tv v0 v
     tops tx srcs exps layouts Q.
    cx.sources = srcs /\ cx.layouts = layouts /\ cx.txn.target = tx.target /\
    compile_external_return (SOME op) F F (AbiCopy m) msz nr nkey ut iv st =
      (x, st') /\
    (nr /\ ~iv ==> ut) /\ (!y. op = Var y ==> not_fresh_at st y) /\
    (if nr /\ ~iv then release_nonreentrant_lock cx.txn.target nkey
     else vyperState$return ()) es = (INL (), es') /\
    evaluate_type (type_env tops) ret = SOME tv /\ safe_cast tv v0 = SOME v /\
    ~is_dynamic (vyper_to_abi_type (type_env tops) ret) /\
    m = type_memory_size tv /\ m < dimword(:256) ==>
    frag_exec ctx st st'
      (\s. state_rel func cenv cx es s /\
           (?p. eval_operand op s = SOME p /\
                val_in_memory tv v0 (w2n p) s.vs_memory))
      Q
      (external_call_result_rel tops ret tx
         (INL v, finalize_pending_deletions
                   (abstract_machine_from_state srcs exps layouts es'),
          es'.requests))
Proof
  rpt strip_tac >>
  qspecl_then [`ctx`, `op`, `m`, `msz`, `nr`, `nkey`, `ut`, `iv`, `st`,
               `x`, `st'`] mp_tac compile_external_return_copy_unlock_frag >>
  simp[] >> disch_then irule >> simp[] >> rpt strip_tac >>
  qexists_tac `p` >> simp[] >> rpt strip_tac >>
  qspecl_then [`tops`, `ret`, `tv`, `v0`, `v`, `w2n p`, `s.vs_memory`]
    mp_tac return_bytes_static_value >>
  impl_tac >- asm_rewrite_tac[] >> strip_tac >>
  qspecl_then [`func`, `cenv`, `cx`, `es`, `es'`, `s`, `ss`, `nr`, `nkey`,
               `iv`, `tops`, `tx`, `srcs`, `exps`, `layouts`] mp_tac
    external_halt_success_unlock >>
  impl_tac >- gvs[] >>
  strip_tac >> gvs[external_call_result_rel_def]
QED

(* Its case with no release (nr ==> iv). *)
Theorem external_return_static_result_rel:
  !ctx op m msz nr nkey ut iv st x st' func cenv cx es ret tv v0 v
     tops tx srcs exps layouts Q.
    cx.sources = srcs /\ cx.layouts = layouts /\ cx.txn.target = tx.target /\
    compile_external_return (SOME op) F F (AbiCopy m) msz nr nkey ut iv st =
      (x, st') /\
    (nr ==> iv) /\ (!y. op = Var y ==> not_fresh_at st y) /\
    evaluate_type (type_env tops) ret = SOME tv /\ safe_cast tv v0 = SOME v /\
    ~is_dynamic (vyper_to_abi_type (type_env tops) ret) /\
    m = type_memory_size tv /\ m < dimword(:256) ==>
    frag_exec ctx st st'
      (\s. state_rel func cenv cx es s /\
           (?p. eval_operand op s = SOME p /\
                val_in_memory tv v0 (w2n p) s.vs_memory))
      Q
      (external_call_result_rel tops ret tx
         (INL v, finalize_pending_deletions
                   (abstract_machine_from_state srcs exps layouts es),
          es.requests))
Proof
  rpt strip_tac >>
  qspecl_then [`ctx`, `op`, `m`, `msz`, `nr`, `nkey`, `ut`, `iv`, `st`,
               `x`, `st'`, `func`, `cenv`, `cx`, `es`, `es`, `ret`, `tv`,
               `v0`, `v`, `tops`, `tx`, `srcs`, `exps`, `layouts`, `Q`]
    mp_tac external_return_static_unlock_result_rel >>
  impl_tac
  >- (Cases_on `nr` >> Cases_on `iv` >> gvs[vyperStateTheory.return_def]) >>
  simp[]
QED

(* external_return_static_unlock_result_rel at a lowered function's
   compile env, where the return statement passes the env's return
   encoding and buffer size.  return_buffer_ok bounds the AbiCopy size; a
   unit that lowers has it for each external function with a valued
   return (lower_vyper_runtime_unit_return_buffer_ok). *)
Theorem external_return_static_cenv_unlock_result_rel:
  !ctx op m nr nkey ut iv st x st' func cenv cx es es' ret tv v0 v
     tops tx srcs exps layouts Q.
    cx.sources = srcs /\ cx.layouts = layouts /\ cx.txn.target = tx.target /\
    compile_external_return (SOME op) F F cenv.ce_ret_enc_info
      cenv.ce_max_return_size nr nkey ut iv st = (x, st') /\
    cenv.ce_ret_enc_info = AbiCopy m /\ return_buffer_ok cenv /\
    (nr /\ ~iv ==> ut) /\ (!y. op = Var y ==> not_fresh_at st y) /\
    (if nr /\ ~iv then release_nonreentrant_lock cx.txn.target nkey
     else vyperState$return ()) es = (INL (), es') /\
    evaluate_type (type_env tops) ret = SOME tv /\ safe_cast tv v0 = SOME v /\
    ~is_dynamic (vyper_to_abi_type (type_env tops) ret) /\
    m = type_memory_size tv ==>
    frag_exec ctx st st'
      (\s. state_rel func cenv cx es s /\
           (?p. eval_operand op s = SOME p /\
                val_in_memory tv v0 (w2n p) s.vs_memory))
      Q
      (external_call_result_rel tops ret tx
         (INL v, finalize_pending_deletions
                   (abstract_machine_from_state srcs exps layouts es'),
          es'.requests))
Proof
  rpt strip_tac >>
  `m < 2 ** 64` by
    (qpat_x_assum `return_buffer_ok _` mp_tac >>
     qpat_x_assum `_.ce_ret_enc_info = _`
       (fn th => simp[return_buffer_ok_def, th])) >>
  `2 ** 64 < dimword (:256)` by
    simp[wordsTheory.dimword_def, venomMemPropsTheory.dimindex_256] >>
  `m < dimword (:256)` by DECIDE_TAC >>
  qpat_x_assum `compile_external_return _ _ _ _ _ _ _ _ _ _ = _` mp_tac >>
  asm_rewrite_tac[] >> strip_tac >>
  drule external_return_static_unlock_result_rel >> disch_then irule >> gvs[] >>
  qexistsl_tac [`iv`, `cenv.ce_max_return_size`, `nkey`, `nr`, `ut`] >>
  simp[]
QED

(* Its case with no release (nr ==> iv). *)
Theorem external_return_static_cenv_result_rel:
  !ctx op m nr nkey ut iv st x st' func cenv cx es ret tv v0 v
     tops tx srcs exps layouts Q.
    cx.sources = srcs /\ cx.layouts = layouts /\ cx.txn.target = tx.target /\
    compile_external_return (SOME op) F F cenv.ce_ret_enc_info
      cenv.ce_max_return_size nr nkey ut iv st = (x, st') /\
    cenv.ce_ret_enc_info = AbiCopy m /\ return_buffer_ok cenv /\
    (nr ==> iv) /\ (!y. op = Var y ==> not_fresh_at st y) /\
    evaluate_type (type_env tops) ret = SOME tv /\ safe_cast tv v0 = SOME v /\
    ~is_dynamic (vyper_to_abi_type (type_env tops) ret) /\
    m = type_memory_size tv ==>
    frag_exec ctx st st'
      (\s. state_rel func cenv cx es s /\
           (?p. eval_operand op s = SOME p /\
                val_in_memory tv v0 (w2n p) s.vs_memory))
      Q
      (external_call_result_rel tops ret tx
         (INL v, finalize_pending_deletions
                   (abstract_machine_from_state srcs exps layouts es),
          es.requests))
Proof
  rpt strip_tac >>
  qspecl_then [`ctx`, `op`, `m`, `nr`, `nkey`, `ut`, `iv`, `st`, `x`, `st'`,
               `func`, `cenv`, `cx`, `es`, `es`, `ret`, `tv`, `v0`, `v`,
               `tops`, `tx`, `srcs`, `exps`, `layouts`, `Q`]
    mp_tac external_return_static_cenv_unlock_result_rel >>
  impl_tac
  >- (Cases_on `nr` >> Cases_on `iv` >> gvs[vyperStateTheory.return_def]) >>
  simp[]
QED

Theorem singleton_tuple_memory:
  !tv v p mem.
    val_in_memory (TupleTV [tv]) (ArrayV (TupleV [v])) p mem =
    val_in_memory tv v p mem
Proof
  simp[valueEncodingTheory.val_in_memory_def]
QED

Theorem singleton_tuple_memory_size:
  !tv. type_memory_size (TupleTV [tv]) = type_memory_size tv
Proof
  simp[valueEncodingTheory.type_memory_size_def]
QED

Theorem return_abi_value_package:
  !env ret tv v0 v wrap.
    evaluate_type env ret = SOME tv /\ safe_cast tv v0 = SOME v ==>
    ?tv' v' av.
      v' = (if wrap then ArrayV (TupleV [v]) else v) /\
      evaluate_type env (if wrap then TupleT [ret] else ret) = SOME tv' /\
      value_has_type tv' v' /\
      vyper_to_abi env (if wrap then TupleT [ret] else ret) v' = SOME av /\
      type_memory_size tv' = type_memory_size tv /\
      (!p mem. val_in_memory tv v0 p mem ==> val_in_memory tv' v' p mem) /\
      LENGTH (enc (vyper_to_abi_type env (if wrap then TupleT [ret] else ret)) av)
        <= vyper_abi_size_bound env (if wrap then TupleT [ret] else ret)
Proof
  rpt strip_tac >>
  `v = v0` by metis_tac[safe_cast_some_eq] >>
  `value_has_type tv v` by metis_tac[vyperTypingTheory.safe_cast_result_well_typed] >>
  `?av. vyper_to_abi env ret v = SOME av` by
    metis_tac[vyperTypeABITheory.vyper_to_abi_total] >>
  Cases_on `wrap`
  >- (`type_slot_size tv <= dimword (:256)` by
        metis_tac[vyperTypingTheory.evaluate_type_well_formed,
                  vyperTypingTheory.well_formed_type_value_slot_size] >>
      `evaluate_type env (TupleT [ret]) = SOME (TupleTV [tv])` by
        simp[vyperValueTheory.evaluate_type_def, vyperValueTheory.type_slot_size_def] >>
      `value_has_type (TupleTV [tv]) (ArrayV (TupleV [v]))` by
        simp[vyperTypingTheory.value_has_type_def] >>
      `vyper_to_abi env (TupleT [ret]) (ArrayV (TupleV [v])) = SOME (ListV [av])` by
        simp[vyperABITheory.vyper_to_abi_def] >>
      qexistsl_tac [`TupleTV [tv]`, `ArrayV (TupleV [v])`, `ListV [av]`] >>
      asm_rewrite_tac[singleton_tuple_memory_size, singleton_tuple_memory] >>
      metis_tac[vyperTypeABITheory.vyper_to_abi_enc_length_bound]) >>
  qexistsl_tac [`tv`, `v`, `av`] >> simp[] >>
  metis_tac[vyperTypeABITheory.vyper_to_abi_enc_length_bound]
QED

Theorem chosen_return_abi_bytes:
  !tops ret v av.
    vyper_to_abi (type_env tops)
      (if needs_external_call_wrap ret /\
          is_dynamic (vyper_to_abi_type (type_env tops) ret)
       then TupleT [ret] else ret)
      (if needs_external_call_wrap ret /\
          is_dynamic (vyper_to_abi_type (type_env tops) ret)
       then ArrayV (TupleV [v]) else v) = SOME av ==>
    return_bytes tops ret v
      (enc (vyper_to_abi_type (type_env tops)
        (if needs_external_call_wrap ret /\
            is_dynamic (vyper_to_abi_type (type_env tops) ret)
         then TupleT [ret] else ret)) av)
Proof
  rpt gen_tac >> Cases_on `ret = NoneT`
  >- (gvs[vyperABITheory.needs_external_call_wrap_def,
          vyperABITheory.vyper_to_abi_type_def,
          contractABITheory.is_dynamic_def] >>
      Cases_on `v` >>
      simp[vyperABITheory.vyper_to_abi_def, return_bytes_def,
           contractABITheory.enc_def, listTheory.REV_DEF]) >>
  Cases_on `needs_external_call_wrap ret /\
            is_dynamic (vyper_to_abi_type (type_env tops) ret)`
  >- (simp[vyperABITheory.vyper_to_abi_def, AllCaseEqs()] >>
      rpt strip_tac >> gvs[] >>
      simp[return_bytes_def, vyperABITheory.vyper_to_abi_type_def]) >>
  simp[] >> strip_tac >>
  simp[return_bytes_def] >>
  Cases_on `needs_external_call_wrap ret` >> gvs[] >>
  simp[contractABITheory.enc_def, listTheory.REV_DEF]
QED

(* A return through the ABI encoder, with the optional unlock first: the
   operand points at memory holding the value, below the alloca frontier,
   and ei is a plan for the value's type, wrapped in a singleton tuple
   when it is dynamic and the ABI wraps it (a static one encodes the same
   either way), with the buffer size msz at least the type's ABI size
   bound.  None of the return sequence's
   ALLOCAs has run, and the frontier stays below 2 ** 256 while they run;
   nothing in the lowering bounds it (vyper rejects allocations of 2^64
   bytes or more).  For the case with no release,
   external_return_abi_cenv_result_rel discharges the plan and the bound
   for the ei and msz update_cenv_ret_abi builds. *)
Theorem external_return_abi_unlock_result_rel:
  !ctx op ei msz nr nkey ut iv st x st' func cenv cx es es' ret tv v0 v
     tops tx srcs exps layouts Q.
    cx.sources = srcs /\ cx.layouts = layouts /\ cx.txn.target = tx.target /\
    compile_external_return (SOME op) F F ei msz nr nkey ut iv st =
      (x, st') /\
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
       then TupleT [ret] else ret) <= msz ==>
    frag_exec ctx st st'
      (\s. state_rel func cenv cx es s /\
           (?p. eval_operand op s = SOME p /\
                val_in_memory tv v0 (w2n p) s.vs_memory /\
                w2n p + type_memory_size tv <= s.vs_alloca_next) /\
           alloca_inv s /\
           (!i. i IN frag_ids st st' ==> FLOOKUP s.vs_allocas i = NONE) /\
           s.vs_alloca_next + msz + 32 * (st'.cs_next_id - st.cs_next_id) <
             dimword (:256))
      Q
      (external_call_result_rel tops ret tx
         (INL v, finalize_pending_deletions
                   (abstract_machine_from_state srcs exps layouts es'),
          es'.requests))
Proof
  rpt strip_tac >>
  drule_all return_abi_value_package >>
  disch_then (qspec_then
    `needs_external_call_wrap ret /\
     is_dynamic (vyper_to_abi_type (type_env tops) ret)` strip_assume_tac) >>
  drule compile_external_return_abi_unlock_frag >>
  disch_then irule >>
  asm_rewrite_tac[] >>
  qexistsl_tac [`av`, `type_env tops`, `tv'`,
    `if needs_external_call_wrap ret /\
        is_dynamic (vyper_to_abi_type (type_env tops) ret)
     then TupleT [ret] else ret`, `v'`] >>
  asm_rewrite_tac[] >> conj_tac
  >- (rpt strip_tac >> fs[] >>
      conj_tac >- metis_tac[] >>
      rpt strip_tac >>
      `return_bytes tops ret v ss.vs_returndata` by
        (gvs[] >> drule chosen_return_abi_bytes >> simp[]) >>
      qspecl_then [`func`, `cenv`, `cx`, `es`, `es'`, `s`, `ss`, `nr`,
                   `nkey`, `iv`, `tops`, `tx`, `srcs`, `exps`, `layouts`]
        mp_tac external_halt_success_unlock >>
      impl_tac >- simp[] >>
      simp[external_call_result_rel_def] >> metis_tac[]) >>
  metis_tac[arithmeticTheory.LESS_EQ_TRANS]
QED

(* Its case with no release (nr ==> iv). *)
Theorem external_return_abi_result_rel:
  !ctx op ei msz nr nkey ut iv st x st' func cenv cx es ret tv v0 v
     tops tx srcs exps layouts Q.
    cx.sources = srcs /\ cx.layouts = layouts /\ cx.txn.target = tx.target /\
    compile_external_return (SOME op) F F ei msz nr nkey ut iv st =
      (x, st') /\
    (nr ==> iv) /\ (!y. op = Var y ==> not_fresh_at st y) /\
    evaluate_type (type_env tops) ret = SOME tv /\ safe_cast tv v0 = SOME v /\
    abi_enc_plan (type_env tops)
      (if needs_external_call_wrap ret /\
          is_dynamic (vyper_to_abi_type (type_env tops) ret)
       then TupleT [ret] else ret) ei /\
    vyper_abi_size_bound (type_env tops)
      (if needs_external_call_wrap ret /\
          is_dynamic (vyper_to_abi_type (type_env tops) ret)
       then TupleT [ret] else ret) <= msz ==>
    frag_exec ctx st st'
      (\s. state_rel func cenv cx es s /\
           (?p. eval_operand op s = SOME p /\
                val_in_memory tv v0 (w2n p) s.vs_memory /\
                w2n p + type_memory_size tv <= s.vs_alloca_next) /\
           alloca_inv s /\
           (!i. i IN frag_ids st st' ==> FLOOKUP s.vs_allocas i = NONE) /\
           s.vs_alloca_next + msz + 32 * (st'.cs_next_id - st.cs_next_id) <
             dimword (:256))
      Q
      (external_call_result_rel tops ret tx
         (INL v, finalize_pending_deletions
                   (abstract_machine_from_state srcs exps layouts es),
          es.requests))
Proof
  rpt strip_tac >>
  qspecl_then [`ctx`, `op`, `ei`, `msz`, `nr`, `nkey`, `ut`, `iv`, `st`,
               `x`, `st'`, `func`, `cenv`, `cx`, `es`, `es`, `ret`, `tv`,
               `v0`, `v`, `tops`, `tx`, `srcs`, `exps`, `layouts`, `Q`]
    mp_tac external_return_abi_unlock_result_rel >>
  impl_tac
  >- (Cases_on `nr` >> Cases_on `iv` >> gvs[vyperStateTheory.return_def]) >>
  simp[]
QED

(* The same, for the plan and buffer size update_cenv_ret_abi builds from a
   compile env with the program's struct map (as build_compile_env's is), for
   a return type with no NoneT in it (retAbiPlanProps). *)
Theorem external_return_abi_cenv_result_rel:
  !ctx op nr nkey ut iv st x st' func cenv cenv0 cx es ret tv v0 v
     tops tx srcs exps layouts Q.
    cx.sources = srcs /\ cx.layouts = layouts /\ cx.txn.target = tx.target /\
    compile_external_return (SOME op) F F cenv.ce_ret_enc_info
      cenv.ce_max_return_size nr nkey ut iv st = (x, st') /\
    cenv.ce_ret_enc_info = (update_cenv_ret_abi cenv0 ret).ce_ret_enc_info /\
    cenv.ce_max_return_size =
      (update_cenv_ret_abi cenv0 ret).ce_max_return_size /\
    cenv0.ce_struct_fields = make_struct_fields_map tops /\
    ALL_DISTINCT (FLAT (MAP (type_def_keys_toplevel (NONE:num option)) tops)) /\
    assignable_type (type_env tops) ret /\
    (nr ==> iv) /\ (!y. op = Var y ==> not_fresh_at st y) /\
    evaluate_type (type_env tops) ret = SOME tv /\ safe_cast tv v0 = SOME v ==>
    frag_exec ctx st st'
      (\s. state_rel func cenv cx es s /\
           (?p. eval_operand op s = SOME p /\
                val_in_memory tv v0 (w2n p) s.vs_memory /\
                w2n p + type_memory_size tv <= s.vs_alloca_next) /\
           alloca_inv s /\
           (!i. i IN frag_ids st st' ==> FLOOKUP s.vs_allocas i = NONE) /\
           s.vs_alloca_next + cenv.ce_max_return_size +
             32 * (st'.cs_next_id - st.cs_next_id) < dimword (:256))
      Q
      (external_call_result_rel tops ret tx
         (INL v, finalize_pending_deletions
                   (abstract_machine_from_state srcs exps layouts es),
          es.requests))
Proof
  rpt gen_tac >> strip_tac >>
  drule_all update_cenv_ret_abi_plan >> strip_tac >>
  irule external_return_abi_result_rel >>
  reverse (rpt conj_tac)
  >- (qexistsl [`cenv.ce_ret_enc_info`, `iv`, `nkey`, `nr`, `ut`, `x`] >>
      gvs[]) >>
  gvs[]
QED

(* ===== Label-space invariant at the start of lowering ===== *)

(* Initial compile_state is well-formed for any entry label that is not
   itself a compiler-generated label (with any counter). The entry label
   in practice is user/frontend-provided (e.g. "global"). *)
Theorem compile_state_ok_initial:
  ∀ entry_lbl.
    entry_lbl ∉ compiler_labels_future 0
    ⇒ compile_state_ok (initial_compile_state entry_lbl)
Proof
  simp[compile_state_ok_def, initial_compile_state_def, bound_labels_def]
QED

(* ===== Planned lowering stages (NOT certificates) ===== *)

(* S1: planned admission, Milestone 6. Proof idea: supported syntax induction,
   selector/argument decoding, body simulation with the threaded oracle and
   requests; canonical wrapped returns and runtime-check aborts. *)
Theorem lower_vyper_runtime_unit_correct:
  !tops rpolicy unit am tx ret vs.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    source_storage_ok tops am tx /\
    source_deployment_rel tops am tx /\
    valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
    initial_venom_state_rel tops am tx vs /\
    call_outcomes_ok tops am tx vs.vs_outcomes
    ==>
    source_unit_execution_correct tops ret am tx unit vs
Proof
  cheat
QED

(* S2, Milestone 5: proved in loweringShapeProps as
   lower_vyper_runtime_unit_source_unit_ok_names. Raw O1 shape excludes
   DLOAD; the immutable-free hypothesis restricts this theorem's source
   domain, not the runtime immutable compiler. *)
Theorem lower_vyper_runtime_unit_source_unit_ok:
  !tops rpolicy unit.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\ supported_program tops /\
    immutable_free_program tops
    ==> o1_source_unit_ok unit
Proof
  ACCEPT_TAC lower_vyper_runtime_unit_source_unit_ok_names
QED

(* S3: planned admission, Milestone 5. Proof idea: allocation-budget and
   buffer-layout induction bound each reachable raw memory access. Excluding
   source_exempt is essential: dynamic decoding can read unchecked offsets. *)
Theorem lower_vyper_runtime_unit_memory_ok:
  !tops rpolicy unit am tx ret vs.
    lower_vyper_runtime_unit tops rpolicy = SOME unit /\
    supported_program tops /\
    source_typing_ok tops am tx /\
    source_storage_ok tops am tx /\
    source_deployment_rel tops am tx /\
    valid_vyper_call tops tx vs.vs_call_ctx.cc_calldata ret /\
    initial_venom_state_rel tops am tx vs /\
    call_outcomes_ok tops am tx vs.vs_outcomes /\
    ~source_exempt tops (call_external (SOME vs.vs_outcomes) am tx)
    ==> raw_unit_memory_ok unit.cu_context vs
Proof
  cheat
QED

(* ===== Superseded admission provenance ===== *)
(* TASK051 full-token consumer audit found no source consumer of
   vyper_to_venom_correct. Its original statement/proof below is INACTIVE,
   retained for provenance only, not saved and not an extra admission.


(* For a well-formed external call to a compiled module:

   If calldata correctly encodes a call to function tx.function_name
   with arguments tx.args, then Venom execution on the lowered context
   produces a result corresponding to Vyper evaluation.

   ctx is bound to run_lowering_pair_compat on the given compilation inputs.
   The selector_matches predicate links sel_num to tx.function_name
   via keccak256 of the ABI signature. *)
Theorem vyper_to_venom_correct:
  !tenv selectors ext_fns int_fns fb_fn dispatch
    bucket_count fn_meta_bytes dense_buckets entry_info entry_label
    vs am tx sel fn_lbl htz cenv
    args dflts ret body mut nr.
  let (ctx, _) = run_lowering_pair_compat selectors ext_fns int_fns fb_fn
                   dispatch bucket_count fn_meta_bytes
                   dense_buckets entry_info entry_label in
    (* tx targets a known external function *)
    lookup_exported_function
      (initial_evaluation_context am.sources am.layouts tx (find_function_module am tx.target tx.function_name)) am
      tx.function_name = SOME (mut, nr, args, dflts, ret, body) /\
    (* Calldata encodes the call *)
    calldata_encodes tenv tx.function_name (MAP SND args) tx.args
      vs.vs_call_ctx.cc_calldata /\
    (* Selector table entry matches function *)
    MEM (sel, fn_lbl, htz) selectors /\
    selector_matches sel tx.function_name
      (vyper_to_abi_types tenv (MAP SND args)) /\
    (* Venom state is initial *)
    vs.vs_inst_idx = 0
    ==>
    ?fuel.
      external_call_result_rel tenv cenv
        (initial_evaluation_context am.sources am.layouts tx (find_function_module am tx.target tx.function_name))
        ret (call_external_simple am tx) (run_context fuel ctx vs)
Proof
  cheat
QED
*)
