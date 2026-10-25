(* Live local buffers and fresh SSA registers survive the transient guard. *)
Theory transientLockFrameProps
Ancestors
  transientLockProps localPtrsProps emitHelperProps exprLoweringProps
  compileEnv context emitHelper venomState finite_map integer_word

Theorem transient_lock_checked_local_ptrs:
  local_ptrs_rel func cenv scopes ss /\ fresh_vars_wrt st ss ==>
  local_ptrs_rel func cenv scopes (transient_lock_checked_state st key ss)
Proof
  strip_tac >>
  `!n. st.cs_next_var <= n ==>
    not_local_ptr cenv scopes (STRING #"%" (toString n))` by
    (rpt strip_tac >>
     irule local_ptrs_rel_fresh_not_local_ptr >>
     qexistsl_tac [`func`,`ss`,`st`] >> simp[]) >>
  simp[transient_lock_checked_state_def] >>
  irule local_ptrs_rel_update_var >> simp[] >>
  irule local_ptrs_rel_update_var >> simp[] >>
  irule local_ptrs_rel_update_var >> simp[]
QED

Theorem local_ptrs_rel_tstore[simp]:
  local_ptrs_rel func cenv scopes (tstore key value ss) =
  local_ptrs_rel func cenv scopes ss
Proof
  simp[local_ptrs_rel_def, local_region_def, local_backed_def,
       tstore_def, lookup_var_def]
QED

Theorem fresh_vars_wrt_tstore[simp]:
  fresh_vars_wrt st (tstore key value ss) = fresh_vars_wrt st ss
Proof
  simp[fresh_vars_wrt_def, tstore_def]
QED

Theorem eval_operand_tstore[simp]:
  eval_operand op (tstore key value ss) = eval_operand op ss
Proof
  Cases_on `op` >> simp[eval_operand_def, tstore_def, lookup_var_def]
QED

(* Return PCs and return-buffer operands live outside ce_vars. Preserve every
   already-defined operand as well as the local_ptrs_rel allocation invariant. *)
Theorem transient_lock_checked_operand:
  fresh_vars_wrt st ss /\ eval_operand op ss = SOME value ==>
  eval_operand op (transient_lock_checked_state st key ss) = SOME value
Proof
   strip_tac >> Cases_on `op` >> gvs[eval_operand_def]
   >- (rename1 `lookup_var p ss = SOME value` >>
       `!n. n >= st.cs_next_var ==>
         p <> STRING #"%" (toString n)` by
         (rpt strip_tac >>
          mp_tac (Q.SPECL [`st`,`ss`,`Var p`,`value`,`p`,`n`]
            fresh_vars_wrt_eval_operand) >> simp[eval_operand_def]) >>
       gvs[transient_lock_checked_state_def, eval_operand_def,
            lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
   simp[transient_lock_checked_state_def, update_var_def]
QED

Theorem compile_nonreentrant_lock_transient_counter:
  compile_nonreentrant_lock key T is_view st = ((),st') ==>
  st'.cs_next_var = st.cs_next_var + 3
Proof
  Cases_on `is_view` >>
  simp[compile_nonreentrant_lock_def, comp_bind_def, comp_ignore_bind_def,
       comp_return_def, emit_op_def, emit_void_def, fresh_id_def,
       fresh_var_def, emit_def] >> strip_tac >> gvs[]
QED

Theorem transient_lock_checked_fresh_vars:
  fresh_vars_wrt st ss /\ st'.cs_next_var >= st.cs_next_var + 3 ==>
  fresh_vars_wrt st' (transient_lock_checked_state st key ss)
Proof
  rw[fresh_vars_wrt_def, transient_lock_checked_state_def,
     update_var_def, FDOM_FUPDATE] >>
  FIRST [irule fresh_var_distinct >> decide_tac,
         first_x_assum irule >> decide_tac]
QED

Theorem compile_nonreentrant_lock_transient_frame:
  compile_nonreentrant_lock key T is_view st = ((),st') /\
  tload (n2w key) ss <> 1w /\
  fresh_vars_wrt st ss /\ local_ptrs_rel func cenv scopes ss ==>
  ?ss'. run_inst_seq (emitted_insts st st') ss = OK ss' /\
    fresh_vars_wrt st' ss' /\ local_ptrs_rel func cenv scopes ss' /\
    !op value. eval_operand op ss = SOME value ==> eval_operand op ss' = SOME value
Proof
  strip_tac >>
  drule compile_nonreentrant_lock_transient_code >> strip_tac >>
  drule compile_nonreentrant_lock_transient_counter >> strip_tac >>
  `fresh_vars_wrt st' (transient_lock_checked_state st key ss)` by
    (irule transient_lock_checked_fresh_vars >> simp[]) >>
  `local_ptrs_rel func cenv scopes (transient_lock_checked_state st key ss)` by
    (irule transient_lock_checked_local_ptrs >> simp[]) >>
  Cases_on `is_view` >> simp[transient_lock_code_execution] >>
   rpt strip_tac >> simp[] >>
   irule transient_lock_checked_operand >> simp[]
QED

Theorem compile_nonreentrant_unlock_transient_frame:
  compile_nonreentrant_unlock key T is_view st = ((),st') /\
  fresh_vars_wrt st ss /\ local_ptrs_rel func cenv scopes ss ==>
  ?ss'. run_inst_seq (emitted_insts st st') ss = OK ss' /\
    fresh_vars_wrt st' ss' /\ local_ptrs_rel func cenv scopes ss'
Proof
  Cases_on `is_view` >> strip_tac
  >- gvs[compile_nonreentrant_unlock_transient_view,
         emitted_insts_def, run_inst_seq_def] >>
  drule compile_nonreentrant_unlock_transient_correct >> strip_tac >> simp[] >>
  gvs[compile_nonreentrant_unlock_def, emit_void_def, comp_bind_def,
      comp_return_def, fresh_id_def, emit_def, fresh_vars_wrt_def]
QED

val () = List.app (fn (name,th) =>
  let val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null (hyp th) andalso null axioms andalso
        List.all (fn s => s = "DISK_THM") oracles then ()
     else raise Fail ("transient guard frame is not kernel closed: " ^ name)
  end) (DB.thms "transientLockFrameProps");
