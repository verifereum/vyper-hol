(* Source and target relations at internal-call frame boundaries. *)

Theory bodyIntCallSeams
Ancestors
  bodySim exprSimDefs exprSimHyps exprSimHypsDefs loweringPosts
  intCallCallee intCallFrame fragGasFocus gasOutcome gasContext
  compileVyper exprLowering exprLoweringProps compileEnv immSectionDead
  vyperInterpreter vyperState vyperAST venomState venomExecSemantics
Libs
  monadsyntax

(* A free lock slot supplies a successful source run when instantiating
   the body's induction hypothesis. *)
Theorem lock_if_nr_runs:
  (nr ==> IS_SOME cx.nonreentrant_slot) /\
  (nr /\ ~v ==> ~cx.txn.is_static) ==>
  ?s u t. lock_if_nr cx nr v s = (INL u,t)
Proof
  Cases_on `nr` >> simp[lock_if_nr_def, return_def] >> strip_tac >>
  Cases_on `cx.nonreentrant_slot` >> gvs[] >> Cases_on `v` >> gvs[] >>
  qexists `ARB with tStorage := empty_transient_storage` >>
  simp[acquire_nonreentrant_lock_def, get_transient_storage_def,
       update_transient_def, record_storage_event_def, bind_def,
       ignore_bind_def, return_def,
       vfmContextTheory.empty_transient_storage_def,
       vfmExecutionTheory.lookup_transient_storage_def,
       vfmStateTheory.lookup_storage_def, vfmStateTheory.empty_storage_def] >>
  rw[return_def, vyperStateTheory.update_transient_def]
QED

(* The source of an internal call after push_function: the nonreentrant
   lock, the body, the frame's cleanup with the lock's release, and the
   cast of the returned value.  The source takes the lock just before
   push_function; lock_if_nr touches only transient storage and
   push_function only the scopes, so taking it just after is the same
   run, and matches the compiled callee, which takes it in its prologue. *)
Definition intcall_rest_at_def:
  intcall_rest_at cx src name mut nr ss prev rtv =
    do lock_if_nr cx nr (is_view_mut mut);
       rv <- finally_unless_halt
         (finally
            (try (do eval_stmts (cx with stk updated_by CONS (src,name)) ss;
                     return NoneV
                  od) handle_function)
            (pop_function prev))
         (unlock_if_nr cx nr (is_view_mut mut));
       crv <- lift_option_type (safe_cast rtv rv) "IntCall cast ret";
       return (Value crv)
    od
End

Definition intcall_rest_singleton_def:
  intcall_rest cx name mut nr ss prev rtv =
    intcall_rest_at cx NONE name mut nr ss prev rtv
End

Theorem intcall_rest_def =
  PURE_REWRITE_RULE [intcall_rest_at_def] intcall_rest_singleton_def;

Theorem ignore_bind_return_unit[local]:
  ignore_bind f (return ()) = f
Proof
  simp[FUN_EQ_THM, ignore_bind_def, bind_def, return_def] >> gen_tac >>
  Cases_on `f x` >> Cases_on `q` >> simp[oneTheory.one]
QED

Theorem return_unit_ignore_bind[local]:
  ignore_bind (return ()) f = f
Proof
  simp[FUN_EQ_THM, ignore_bind_def, bind_def, return_def]
QED

(* Without the lock, the cleanup is the frame's pop alone. *)
Theorem intcall_rest_F:
  intcall_rest cx name mut F ss prev rtv =
    do rv <- finally
         (try (do eval_stmts (cx with stk updated_by CONS (NONE,name)) ss;
                  return NoneV
               od) handle_function)
         (do pop_function prev;
             unlock_if_nr cx F (is_view_mut mut)
          od);
       crv <- lift_option_type (safe_cast rtv rv) "IntCall cast ret";
       return (Value crv)
    od
Proof
  simp[intcall_rest_def, finally_unless_halt_return, ignore_bind_return_unit,
       lock_if_nr_def, unlock_if_nr_def, return_unit_ignore_bind]
QED

(* The callee as the INVOKE runs it: the nonreentrant lock its prologue
   takes, then its body. *)
Definition intcall_callee_src_at_def:
  intcall_callee_src_at cx src name mut nr ss =
    do lock_if_nr cx nr (is_view_mut mut);
       try (do eval_stmts (cx with stk updated_by CONS (src,name)) ss;
               return NoneV
            od) handle_function
    od
End

Definition intcall_callee_src_singleton_def:
  intcall_callee_src cx name mut nr ss =
    intcall_callee_src_at cx NONE name mut nr ss
End

Theorem intcall_callee_src_def =
  PURE_REWRITE_RULE [intcall_callee_src_at_def] intcall_callee_src_singleton_def;

(* Without the lock, the callee is its body alone. *)
Theorem intcall_callee_src_F:
  intcall_callee_src cx name mut F ss =
    try (do eval_stmts (cx with stk updated_by CONS (NONE,name)) ss;
            return NoneV
         od) handle_function
Proof
  simp[intcall_callee_src_def, lock_if_nr_def, return_unit_ignore_bind]
QED

(* How the callee's run ends, seen from the caller's state t at the
   INVOKE, whose call's code has the ALLOCA ids in [n, m): an abort the
   call's source exception allows (expr_exit), or an IntRet with the
   returned value v: the callee's global state, after the source releases
   the nonreentrant lock (ee'), related at the caller's compile env, its stack values v's words (rc of them), the return
   buffer rb, if any, holding v, and the caller's memory below t's
   frontier above the constructor's fixed immutable region untouched
   outside the call's own allocations (the return
   buffer and the staged memory arguments, which the callee may write).
   The memory frame is a fact of the callee's Venom code (it writes below
   its entry frontier only through the pointers it is passed), not of the
   body's simulation: stmt_frag's post carries no memory frame. *)
Definition intcall_callee_exit_mods_def:
  intcall_callee_exit_mods mods H func cenv cx mut nr rtv rc (rb:bytes32 option) (n:num)
                      (m:num)
                      (t:venom_state) res (ee:evaluation_state) r <=>
    (expr_exit res r /\ halt_exit H cx ee res r) \/
    ?v ir s' ee'.
      res = INL v /\ r = IntRet ir s' /\
      unlock_if_nr cx nr (is_view_mut mut) ee = (INL (),ee') /\
      state_rel H func cenv cx (ee' with scopes := []) s' /\
      intret_vals_match rtv v ir.iret_values /\
      LENGTH ir.iret_values = rc /\ ir.iret_adopt_fmp = NONE /\
      (!b sz. (cenv.ce_is_ctor ==> imm_len_mods mods <= b) /\
              b + sz <= t.vs_alloca_next /\
              (!aid off asz. FLOOKUP t.vs_allocas aid = SOME (off,asz) /\
                             n <= aid /\ aid < m ==>
                             regions_disjoint b sz off asz) ==>
              mem_bytes_at b sz s'.vs_memory = mem_bytes_at b sz t.vs_memory) /\
      (!p. rb = SOME p ==> val_in_memory rtv v (w2n p) s'.vs_memory)
End

Definition intcall_callee_exit_singleton_def:
  intcall_callee_exit H func cenv cx mut nr rtv rc rb n m t res ee r <=>
    intcall_callee_exit_mods [(NONE,cx_tops cx)] H func cenv cx mut nr rtv rc rb n m t res ee r
End

Theorem intcall_callee_exit_def =
  PURE_REWRITE_RULE [intcall_callee_exit_mods_def, imm_len_mods_singleton] intcall_callee_exit_singleton_def;

(* Without the lock, the IntRet's state is the callee's own. *)
Theorem intcall_callee_exit_F:
  intcall_callee_exit H func cenv cx mut F rtv retc rb n m t res ee r <=>
    (expr_exit res r /\ halt_exit H cx ee res r) \/
    ?v ir s'.
      res = INL v /\ r = IntRet ir s' /\
      state_rel H func cenv cx (ee with scopes := []) s' /\
      intret_vals_match rtv v ir.iret_values /\
      LENGTH ir.iret_values = retc /\ ir.iret_adopt_fmp = NONE /\
      (!b sz. (cenv.ce_is_ctor ==> imm_len (cx_tops cx) <= b) /\
              b + sz <= t.vs_alloca_next /\
              (!aid off asz. FLOOKUP t.vs_allocas aid = SOME (off,asz) /\
                             n <= aid /\ aid < m ==>
                             regions_disjoint b sz off asz) ==>
              mem_bytes_at b sz s'.vs_memory = mem_bytes_at b sz t.vs_memory) /\
      (!p. rb = SOME p ==> val_in_memory rtv v (w2n p) s'.vs_memory)
Proof
  simp[intcall_callee_exit_def, unlock_if_nr_def, return_def]
QED
