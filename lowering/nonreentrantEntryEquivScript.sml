(* TOP-LEVEL: guarded-function lock/release simulation at the actual
   deployment layout. Only the context's slot projection is required, so the
   result also applies inside internal-call frames and deployment contexts. *)
Theory nonreentrantEntryEquiv
Ancestors
  e2eDefs nonreentrantEquiv transientLockFrameProps
  vyperTypeContract vyperInterpreter vyperState
  compileEnv context venomState exprLoweringProps

Theorem source_typing_function_header:
  source_typing_ok tops am tx /\
  MEM (FunctionDecl vis mut nr rr name args dflts ret stmts) tops ==>
  function_header_ok vis mut nr rr name args dflts ret
Proof
  fs[source_typing_ok_def] >>
  metis_tac[check_contract_function_header, listTheory.MEM]
QED

Theorem nonreentrant_entry_lock_source_correct:
  layouts_agree tops am tx /\
  MEM (FunctionDecl vis mut T rr name args dflts ret stmts) tops /\
  function_header_ok vis mut T rr name args dflts ret /\
  cx.nonreentrant_slot = lookup_nonreentrant_slot am.layouts tx.target /\
  state_rel cenv cx vs ss /\
  compile_nonreentrant_lock global_nonreentrant_slot T (mut = View) st = ((),st') /\
  tload (n2w global_nonreentrant_slot) ss <> 1w ==>
  ?vs' ss'.
    (case cx.nonreentrant_slot of
       NONE => vyperState$raise (vyperState$Error (TypeError "nonreentrant slot missing"))
     | SOME key => acquire_nonreentrant_lock cx.txn.target key
                     (mut = View \/ mut = Pure)) vs = (INL (),vs') /\
    run_inst_seq (emitted_insts st st') ss = OK ss' /\
    state_rel cenv cx vs' ss'
Proof
  strip_tac >>
  `cx.nonreentrant_slot = SOME global_nonreentrant_slot` by
    metis_tac[layouts_agree_nonreentrant_slot] >>
  drule function_header_nonreentrant_view >> strip_tac >> simp[] >>
  irule compile_nonreentrant_lock_source_correct >> gvs[]
QED

Theorem nonreentrant_entry_lock_source_revert:
  layouts_agree tops am tx /\
  MEM (FunctionDecl vis mut T rr name args dflts ret stmts) tops /\
  function_header_ok vis mut T rr name args dflts ret /\
  cx.nonreentrant_slot = lookup_nonreentrant_slot am.layouts tx.target /\
  state_rel cenv cx vs ss /\
  compile_nonreentrant_lock global_nonreentrant_slot T (mut = View) st = ((),st') /\
  tload (n2w global_nonreentrant_slot) ss = 1w ==>
  (case cx.nonreentrant_slot of
     NONE => vyperState$raise (vyperState$Error (TypeError "nonreentrant slot missing"))
   | SOME key => acquire_nonreentrant_lock cx.txn.target key
                   (mut = View \/ mut = Pure)) vs =
    (INR (vyperState$Error (RuntimeError "nonreentrant lock")),vs) /\
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
  state_rel cenv cx vs ss /\
  compile_nonreentrant_unlock global_nonreentrant_slot T (mut = View) st = ((),st') ==>
  ?vs' ss'.
    (if ~(mut = View \/ mut = Pure) then
       case cx.nonreentrant_slot of
         NONE => vyperState$return ()
       | SOME key => release_nonreentrant_lock cx.txn.target key
     else vyperState$return ()) vs = (INL (),vs') /\
    run_inst_seq (emitted_insts st st') ss = OK ss' /\
    state_rel cenv cx vs' ss'
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
  source_typing_ok tops am tx /\ layouts_agree tops am tx /\
  MEM (FunctionDecl vis mut T rr name args dflts ret stmts) tops /\
  cx.nonreentrant_slot = lookup_nonreentrant_slot am.layouts tx.target /\
  state_rel cenv cx vs ss /\ fresh_vars_wrt st ss /\
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
    state_rel cenv cx vs' ss' /\ fresh_vars_wrt st' ss' /\
    local_ptrs_rel func cenv scopes ss' /\
    !op value. eval_operand op ss = SOME value ==> eval_operand op ss' = SOME value
Proof
  strip_tac >>
  `function_header_ok vis mut T rr name args dflts ret` by
    metis_tac[source_typing_function_header] >>
  drule_all nonreentrant_entry_lock_source_correct >> strip_tac >>
  drule_all compile_nonreentrant_lock_transient_frame >> strip_tac >>
  gvs[] >> metis_tac[]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null (hyp th) andalso null axioms andalso
        List.all (fn s => s = "DISK_THM") oracles then ()
     else raise Fail ("entry lock simulation is not kernel closed: " ^ name)
  end) (DB.thms "nonreentrantEntryEquiv");
