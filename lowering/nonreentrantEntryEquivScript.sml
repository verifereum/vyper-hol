(* TOP-LEVEL: guarded-function lock/release simulation at the actual
   deployment layout. Only the context's slot projection is required, so the
   result also applies inside internal-call frames and deployment contexts. *)
Theory nonreentrantEntryEquiv
Ancestors
  loweringStateRelDefs e2eDefs nonreentrantEquiv transientLockFrameProps
  vyperTypeContract vyperInterpreter vyperState
  compileEnv context venomState exprLoweringProps vyperStorageFootprint
  bodyPtrDefs nonreentrantSource sourceUnitExecution pred_set words

(* Horizon lock words cannot carry relocation taint. *)
Theorem nonreentrant_slot_untainted:
  stor_taint_ok H cx tn ss /\
  MEM nkey (SND H) /\ nkey < dimword (:256) ==>
  !b. ~((n2w nkey, b) IN tn.t_trans)
Proof
  strip_tac >>
  `!b. ~storage_dead H T
    (ss.vs_transient ss.vs_call_ctx.cc_address)
    (w2n ((n2w nkey):bytes32)) b` by
    (gen_tac >> irule nonreentrant_storage_live >> simp[]) >>
  fs[stor_taint_ok_def, cx_dead_def] >>
  Cases_on `ss.vs_call_ctx.cc_address = cx.txn.target` >>
  gvs[SUBSET_DEF] >> qx_gen_tac `b` >> strip_tac >>
  qpat_x_assum `!x. x IN tn.t_trans ==> _`
    (qspec_then `(n2w nkey,b)` mp_tac) >>
  simp[wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD]
QED

(* Writing a separated lock leaves the horizon's dead-byte mask intact. *)
Theorem nonreentrant_stor_taint_frame:
  storage_locks_separated (FST H) (SND H) /\
  MEM nkey (SND H) /\ nkey < dimword (:256) /\
  stor_taint_ok H cx tn ss ==>
  stor_taint_ok H cx tn (tstore (n2w nkey) value ss)
Proof
  strip_tac >>
  `!st j b. storage_dead H T (update_storage (n2w nkey) value st) j b =
             storage_dead H T st j b` by
    (rpt gen_tac >> irule nonreentrant_storage_dead_frame >> simp[]) >>
  gvs[stor_taint_ok_def, cx_dead_def, tstore_def,
      combinTheory.APPLY_UPDATE_THM]
QED

Theorem source_typing_function_header:
  source_typing_ok tops am tx /\
  MEM (FunctionDecl vis mut nr rr name args dflts ret stmts) tops ==>
  function_header_ok vis mut nr rr name args dflts ret
Proof
  fs[source_typing_ok_def] >>
  metis_tac[check_contract_function_header, listTheory.MEM]
QED


Theorem nonreentrant_entry_lock_source_correct:
  storage_locks_separated (FST H) (SND H) /\
  MEM global_nonreentrant_slot (SND H) /\
  global_nonreentrant_slot < dimword (:256) /\
  layouts_agree tops am tx /\
  MEM (FunctionDecl vis mut T rr name args dflts ret stmts) tops /\
  function_header_ok vis mut T rr name args dflts ret /\
  cx.nonreentrant_slot = lookup_nonreentrant_slot am.layouts tx.target /\
  state_rel H func cenv cx vs ss /\ fresh_vars_wrt st ss /\
  compile_nonreentrant_lock global_nonreentrant_slot T (mut = View) st = ((),st') /\
  tload (n2w global_nonreentrant_slot) ss <> 1w ==>
  ?vs' ss'.
    (case cx.nonreentrant_slot of
       NONE => vyperState$raise (vyperState$Error (TypeError "nonreentrant slot missing"))
     | SOME key => acquire_nonreentrant_lock cx.txn.target key
                     (mut = View \/ mut = Pure)) vs = (INL (),vs') /\
    run_inst_seq (emitted_insts st st') ss = OK ss' /\
    state_rel H func cenv cx vs' ss'
Proof
  strip_tac >>
  `cx.nonreentrant_slot = SOME global_nonreentrant_slot` by
    metis_tac[layouts_agree_nonreentrant_slot] >>
  drule function_header_nonreentrant_view >> strip_tac >> simp[] >>
  irule compile_nonreentrant_lock_source_correct >> gvs[]
QED


Theorem nonreentrant_entry_lock_source_revert:
  MEM global_nonreentrant_slot (SND H) /\
  global_nonreentrant_slot < dimword (:256) /\
  layouts_agree tops am tx /\
  MEM (FunctionDecl vis mut T rr name args dflts ret stmts) tops /\
  function_header_ok vis mut T rr name args dflts ret /\
  cx.nonreentrant_slot = lookup_nonreentrant_slot am.layouts tx.target /\
  state_rel H func cenv cx vs ss /\
  compile_nonreentrant_lock global_nonreentrant_slot T (mut = View) st = ((),st') /\
  tload (n2w global_nonreentrant_slot) ss = 1w ==>
  (case cx.nonreentrant_slot of
     NONE => vyperState$raise (vyperState$Error (TypeError "nonreentrant slot missing"))
   | SOME key => acquire_nonreentrant_lock cx.txn.target key
                   (mut = View \/ mut = Pure)) vs =
    (INR (vyperState$Error (RuntimeError "nonreentrant lock")),
     vs with storage_trace := vs.storage_trace ++ [StorageLock global_nonreentrant_slot]) /\
  ?ss'. run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss'
Proof
  strip_tac >>
  `cx.nonreentrant_slot = SOME global_nonreentrant_slot` by
    metis_tac[layouts_agree_nonreentrant_slot] >>
  drule function_header_nonreentrant_view >> strip_tac >> simp[] >>
  irule compile_nonreentrant_lock_source_revert >> gvs[] >> metis_tac[]
QED

(* The source uses this same action on fall-through and ReturnException. *)
Theorem nonreentrant_entry_unlock_source_correct:
  layouts_agree tops am tx /\
  MEM (FunctionDecl vis mut T rr name args dflts ret stmts) tops /\
  function_header_ok vis mut T rr name args dflts ret /\
  cx.nonreentrant_slot = lookup_nonreentrant_slot am.layouts tx.target /\
  state_rel H func cenv cx vs ss /\
  compile_nonreentrant_unlock global_nonreentrant_slot T (mut = View) st = ((),st') ==>
  ?vs' ss'.
    (if ~(mut = View \/ mut = Pure) then
       case cx.nonreentrant_slot of
         NONE => vyperState$return ()
       | SOME key => release_nonreentrant_lock cx.txn.target key
     else vyperState$return ()) vs = (INL (),vs') /\
    run_inst_seq (emitted_insts st st') ss = OK ss' /\
    state_rel H func cenv cx vs' ss'
Proof
  strip_tac >>
  `cx.nonreentrant_slot = SOME global_nonreentrant_slot` by
    metis_tac[layouts_agree_nonreentrant_slot] >>
  drule function_header_nonreentrant_view >> strip_tac >> simp[] >>
  drule_all compile_nonreentrant_unlock_source_correct >>
  Cases_on `mut = View` >> gvs[]
QED

(* The checked entry boundary also keeps already-decoded arguments and local
   buffers, so the simulation can continue into the guarded body. *)

Theorem checked_nonreentrant_entry_lock:
  storage_locks_separated (FST H) (SND H) /\
  MEM global_nonreentrant_slot (SND H) /\
  global_nonreentrant_slot < dimword (:256) /\
  source_typing_ok tops am tx /\ layouts_agree tops am tx /\
  MEM (FunctionDecl vis mut T rr name args dflts ret stmts) tops /\
  cx.nonreentrant_slot = lookup_nonreentrant_slot am.layouts tx.target /\
  state_rel H func cenv cx vs ss /\ fresh_vars_wrt st ss /\
  local_ptrs_rel func cenv scopes ss /\
  compile_nonreentrant_lock global_nonreentrant_slot T (mut = View) st = ((),st') /\
  tload (n2w global_nonreentrant_slot) ss <> 1w ==>
  ?vs' ss'.
    (case cx.nonreentrant_slot of
       NONE => vyperState$raise
         (vyperState$Error (TypeError "nonreentrant slot missing"))
     | SOME key => acquire_nonreentrant_lock cx.txn.target key
                     (mut = View \/ mut = Pure)) vs = (INL (),vs') /\
    run_inst_seq (emitted_insts st st') ss = OK ss' /\
    state_rel H func cenv cx vs' ss' /\ fresh_vars_wrt st' ss' /\
    local_ptrs_rel func cenv scopes ss' /\
    !op value. eval_operand op ss = SOME value ==> eval_operand op ss' = SOME value
Proof
  strip_tac >>
  `function_header_ok vis mut T rr name args dflts ret` by
    metis_tac[source_typing_function_header] >>
  `~ss.vs_call_ctx.cc_static` by fs[state_rel_def] >>
  drule_all nonreentrant_entry_lock_source_correct >> strip_tac >>
  drule_all compile_nonreentrant_lock_transient_frame >> strip_tac >>
  gvs[] >> metis_tac[]
QED
