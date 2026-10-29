(* TOP-LEVEL: execution and framing of transient reentrancy guards.
   Helpers: exact emitted code and the three scratch-register writes. *)
Theory transientLockProps
Ancestors
  context emitHelperProps exprLoweringProps emitHelper compileEnv
  venomExecSemantics venomState venomInst vfmState
  list rich_list arithmetic ASCIInumbers

Theorem step_TLOAD:
  eval_operand op ss = SOME key ==>
  step_inst_base (mk_inst id TLOAD [op] [out]) ss =
    OK (update_var out (tload key ss) ss)
Proof
  rw[step_inst_base_def, exec_read1_def]
QED

Theorem step_TSTORE:
  eval_operand op1 ss = SOME key /\ eval_operand op2 ss = SOME value ==>
  step_inst_base (mk_inst id TSTORE [op1;op2] []) ss =
    OK (tstore key value ss)
Proof
  rw[step_inst_base_def, exec_write2_def]
QED

Theorem tload_update_var[simp]:
  tload key (update_var var value ss) = tload key ss
Proof
  simp[tload_def, contract_transient_def, update_var_def]
QED

Theorem tload_tstore_same[simp]:
  tload key (tstore key value ss) = value
Proof
  simp[tload_def, tstore_def, contract_transient_def,
       lookup_storage_def, update_storage_def, combinTheory.APPLY_UPDATE_THM]
QED

Theorem step_TLOAD_lit[local]:
  step_inst_base (mk_inst id TLOAD [Lit key] [out]) ss =
    OK (update_var out (tload key ss) ss)
Proof
  simp[step_inst_base_def, exec_read1_def, eval_operand_def]
QED

Theorem step_TSTORE_lit:
  step_inst_base (mk_inst id TSTORE [Lit key;Lit value] []) ss =
    OK (tstore key value ss)
Proof
  simp[step_inst_base_def, exec_write2_def, eval_operand_def]
QED

Theorem step_EQ_recent_one[local]:
  step_inst_base (mk_inst id EQ [Var var;Lit 1w] [out])
    (update_var var value ss) =
  OK (update_var out (bool_to_word (value = 1w)) (update_var var value ss))
Proof
  simp[step_inst_base_def, exec_pure2_def,
       eval_operand_def, lookup_var_update_var]
QED

Theorem step_ISZERO_recent[local]:
  step_inst_base (mk_inst id ISZERO [Var var] [out])
    (update_var var value ss) =
  OK (update_var out (bool_to_word (value = 0w)) (update_var var value ss))
Proof
  simp[step_inst_base_def, exec_pure1_def,
       eval_operand_def, lookup_var_update_var]
QED

Theorem step_ASSERT_recent[local]:
  step_inst_base (mk_inst id ASSERT [Var var] []) (update_var var value ss) =
    if value = 0w then
      Abort Revert_abort
        (revert_state (set_returndata [] (update_var var value ss)))
    else OK (update_var var value ss)
Proof
  simp[step_inst_base_def, mk_inst_def, eval_operand_def, lookup_var_update_var]
QED

Definition transient_lock_code_def:
  transient_lock_code key is_view st =
    [mk_inst st.cs_next_id TLOAD [Lit (n2w key)]
       [STRING #"%" (toString st.cs_next_var)];
     mk_inst (st.cs_next_id + 1) EQ
       [Var (STRING #"%" (toString st.cs_next_var)); Lit 1w]
       [STRING #"%" (toString (st.cs_next_var + 1))];
     mk_inst (st.cs_next_id + 2) ISZERO
       [Var (STRING #"%" (toString (st.cs_next_var + 1)))]
       [STRING #"%" (toString (st.cs_next_var + 2))];
     mk_inst (st.cs_next_id + 3) ASSERT
       [Var (STRING #"%" (toString (st.cs_next_var + 2)))] []] ++
    if is_view then [] else
      [mk_inst (st.cs_next_id + 4) TSTORE [Lit (n2w key); Lit 1w] []]
End

Theorem compile_nonreentrant_lock_transient_code:
  compile_nonreentrant_lock key T is_view st = ((),st') ==>
  emitted_insts st st' = transient_lock_code key is_view st
Proof
  Cases_on `is_view` >> strip_tac >>
  gvs[compile_nonreentrant_lock_def, comp_bind_def,
      comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> gvs[] >>
  pairarg_tac >> gvs[] >>
  pairarg_tac >> gvs[] >>
  pairarg_tac >> gvs[] >>
  imp_res_tac emitted_insts_emit_op >>
  imp_res_tac emitted_insts_emit_void >> gvs[] >>
  simp[emitted_insts_def, DROP_LENGTH_APPEND, transient_lock_code_def]
QED

(* These scratch assignments do not require a freshness premise: each check
   immediately consumes the register produced by its predecessor. *)
Definition transient_lock_checked_state_def:
  transient_lock_checked_state st key ss =
    update_var (STRING #"%" (toString (st.cs_next_var + 2)))
      (bool_to_word (tload (n2w key) ss <> 1w))
      (update_var (STRING #"%" (toString (st.cs_next_var + 1)))
        (bool_to_word (tload (n2w key) ss = 1w))
        (update_var (STRING #"%" (toString st.cs_next_var))
          (tload (n2w key) ss) ss))
End

Theorem transient_lock_code_execution:
  run_inst_seq (transient_lock_code key is_view st) ss =
    let checked = transient_lock_checked_state st key ss in
    if tload (n2w key) ss = 1w then
      Abort Revert_abort (revert_state (set_returndata [] checked))
    else OK (if is_view then checked else tstore (n2w key) 1w checked)
Proof
  Cases_on `tload (n2w key) ss = 1w` >> Cases_on `is_view` >>
  simp[transient_lock_code_def, transient_lock_checked_state_def,
       run_inst_seq_def, step_TLOAD_lit, step_EQ_recent_one,
       step_ISZERO_recent, step_ASSERT_recent, step_TSTORE_lit,
       bool_to_word_def]
QED

Theorem compile_nonreentrant_lock_transient_correct:
  compile_nonreentrant_lock key T F st = ((),st') /\
  tload (n2w key) ss <> 1w ==>
  ?ss'. run_inst_seq (emitted_insts st st') ss = OK ss' /\
        tload (n2w key) ss' = 1w /\
        ss'.vs_accounts = ss.vs_accounts /\
        ss'.vs_memory = ss.vs_memory /\
        ss'.vs_transient = (tstore (n2w key) 1w ss).vs_transient
Proof
  strip_tac >> drule compile_nonreentrant_lock_transient_code >>
  simp[transient_lock_code_execution] >> strip_tac >>
  simp[transient_lock_checked_state_def, tstore_def, update_var_def,
       contract_transient_def, tload_def,
       lookup_storage_def, update_storage_def, combinTheory.APPLY_UPDATE_THM]
QED

Theorem compile_nonreentrant_lock_transient_revert:
  compile_nonreentrant_lock key T is_view st = ((),st') /\
  tload (n2w key) ss = 1w ==>
  ?ss'. run_inst_seq (emitted_insts st st') ss = Abort Revert_abort ss'
Proof
  strip_tac >> drule compile_nonreentrant_lock_transient_code >>
  simp[transient_lock_code_execution]
QED

Theorem compile_nonreentrant_lock_transient_view:
  compile_nonreentrant_lock key T T st = ((),st') /\
  tload (n2w key) ss <> 1w ==>
  ?ss'. run_inst_seq (emitted_insts st st') ss = OK ss' /\
        ss'.vs_transient = ss.vs_transient /\
        ss'.vs_accounts = ss.vs_accounts /\
        ss'.vs_memory = ss.vs_memory
Proof
  strip_tac >> drule compile_nonreentrant_lock_transient_code >>
  simp[transient_lock_code_execution] >> strip_tac >>
  simp[transient_lock_checked_state_def, update_var_def]
QED

Theorem compile_nonreentrant_unlock_transient_correct:
  compile_nonreentrant_unlock key T F st = ((),st') ==>
  run_inst_seq (emitted_insts st st') ss = OK (tstore (n2w key) 0w ss)
Proof
  simp[compile_nonreentrant_unlock_def] >> strip_tac >>
  drule emitted_insts_emit_void >> simp[] >> strip_tac >>
  simp[emitted_insts_def, DROP_LENGTH_APPEND, run_inst_seq_def,
       step_TSTORE_lit]
QED

Theorem compile_nonreentrant_unlock_transient_view:
  compile_nonreentrant_unlock key T T st = ((),st)
Proof
  simp[compile_nonreentrant_unlock_def, comp_return_def]
QED

Theorem compile_nonreentrant_unlock_transient_frame:
  compile_nonreentrant_unlock key T F st = ((),st') ==>
  ?ss'. run_inst_seq (emitted_insts st st') ss = OK ss' /\
        tload (n2w key) ss' = 0w /\
        ss'.vs_accounts = ss.vs_accounts /\
        ss'.vs_memory = ss.vs_memory
Proof
  strip_tac >> drule compile_nonreentrant_unlock_transient_correct >>
  simp[tstore_def, tload_def, contract_transient_def,
       lookup_storage_def, update_storage_def, combinTheory.APPLY_UPDATE_THM]
QED

(* A second function using the same slot cannot acquire either a view guard or
   a mutating guard while the first mutating guard is held. *)
Theorem compile_nonreentrant_transient_nested_revert:
  compile_nonreentrant_lock key T F st = ((),st') /\
  tload (n2w key) ss <> 1w /\
  run_inst_seq (emitted_insts st st') ss = OK held /\
  compile_nonreentrant_lock key T is_view next = ((),next') ==>
  ?ss'. run_inst_seq (emitted_insts next next') held = Abort Revert_abort ss'
Proof
  strip_tac >> drule_all compile_nonreentrant_lock_transient_correct >>
  strip_tac >> gvs[] >>
  drule_all compile_nonreentrant_lock_transient_revert >> simp[]
QED

(* Fail the build if any exported result depends on an admission. *)
val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null (hyp th) andalso null axioms andalso
        List.all (fn s => s = "DISK_THM") oracles then ()
     else raise Fail ("transient lock theorem is not kernel closed: " ^ name)
  end) (DB.thms "transientLockProps");
