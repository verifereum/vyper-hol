(* Retain the actual counted source execution at a storage append landing. *)
Theory bodyIntCallFamStmtMutationAppendExec
Ancestors
  bodyIntCallFamStmtMutationAppendSuffix gasOutcome gasSummary

Theorem intcall_append_storage_suffix_exec:
  compile_dynarray_append ce (Lit slot) op 1 1 dt vt cap T
    (if tr then TLOAD else SLOAD) (if tr then TSTORE else SSTORE) sb = ((),sf) /\
  fn_has_code sb sf func /\ (!x. op = Var x ==> not_fresh_at sb x) /\
  eval_operand op s = SOME w /\ cap < dimword (:256) /\
  ~s.vs_halted /\ ~s.vs_call_ctx.cc_static /\
  s.vs_current_bb = sb.cs_current_bb /\
  s.vs_inst_idx = LENGTH sb.cs_current_insts /\
  stmt_state_rel ctx func ce cx es s /\ local_ptrs_reserved ce sb /\
  declared_storage_region cx mid n [] = SOME (tr,slot,ArrayTV tv (Dynamic cap)) /\
  type_slot_size tv = 1 /\ encode_value tv v = SOME [(0,w)] /\
  (if tr then tload slot s else sload slot s) =
    lookup_storage slot (get_storage cx es tr) ==>
  gas_outcome F (cx_tops cx) (ctx,func)
    (append_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic cap))) v)
    (es,s)
    (\res ee u. res = INL () /\ stmt_state_rel ctx func ce cx ee u /\
      ~u.vs_halted /\ u.vs_current_bb = sf.cs_current_bb /\
      u.vs_inst_idx = LENGTH sf.cs_current_insts /\
      ee.scopes = es.scopes /\ ee.immutables = es.immutables /\
      u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas /\
      u.vs_alloca_next = s.vs_alloca_next /\
      (!x a. not_fresh_at sb x /\ lookup_var x s = SOME a ==>
             lookup_var x u = SOME a) /\
      ?marks raw. ee = raw with gas_obs := [] /\
        gas_marked_exec F (ctx,func)
          (append_place cx (StoragePlace tr slot (ArrayTV tv (Dynamic cap))) v)
          (es,s) marks res raw (OK u))
    (\res ee r. expr_exit res r)
Proof
  strip_tac >> drule_all intcall_append_storage_suffix >>
  rewrite_tac[gas_outcome_def, gas_summary_at_def] >>
  strip_tac
  >- (gvs[] >> qexists_tac `marks` >> disj1_tac >>
      qexistsl_tac [`INL ()`, `es_end`, `OK t`] >> simp[] >>
      qexistsl_tac [`marks`, `es_end`] >> simp[])
  >- (qexists_tac `marks` >> disj1_tac >>
      qexistsl_tac [`res`, `es_end`, `r`] >> simp[]) >>
  qexists_tac `marks` >> disj2_tac >> metis_tac[]
QED
