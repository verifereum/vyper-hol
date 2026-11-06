(* Snapshot recovery uses the current outer ghost invariant, not a memory
   frame on the stmts callback. Typed supported source execution preserves
   the protected array lookup through finally/pop_scope. *)
Theory forPtrArraySnapshot
Ancestors forPtrElement forPtrRangeCallback forPtrScope forPtrAllocationFrame
  stmtSimForArrayFrame bodyPtrDefs vyperState vyperInterpreter
  compileEnv finite_map list
Libs monadsyntax

(* Loop handling changes only the result, including on continue and break.
   Bridge the actual bool round to plain finally/pop snapshot preservation. *)
Theorem for_handled_loop_cleanup_state:
  !source es res ee.
  finally (try (ignore_bind
    (source : evaluation_state -> unit evaluation_result) (return F))
    handle_loop_exception) pop_scope es = (res,ee) ==>
  ?raw. finally source pop_scope es = (raw,ee)
Proof
  rpt gen_tac >> Cases_on `source es` >> rename1 `_ = (outcome,after)` >>
  Cases_on `outcome`
  >- (simp[finally_def, try_def, ignore_bind_def, bind_def, return_def] >>
      Cases_on `pop_scope after` >> simp[ignore_bind_def, bind_def, return_def] >>
      Cases_on `q` >> simp[]) >>
  rename1 `INR exc` >> Cases_on `exc` >>
  simp[finally_def, try_def, ignore_bind_def, bind_def, return_def,
       raise_def, handle_loop_exception_def] >>
  Cases_on `pop_scope after` >> simp[ignore_bind_def, bind_def, return_def, raise_def] >>
  Cases_on `q` >> simp[]
QED

Theorem for_array_callback_snapshot_ptr:
  supported_stmts tops bindings stmts /\
  FLOOKUP env.var_types name = SOME (ArrayT elem bound) /\
  type_stmts env ret_ty stmts = SOME env' /\
  iterator_unmodified (Array (Name aty name)) stmts /\
  ~supported_stmts_expr_exists expr_internal_call_root stmts /\
  es.scopes = tmp :: outer /\
  finally (try (ignore_bind (eval_stmts cx stmts) (return F))
    handle_loop_exception) pop_scope es = (res,ee) /\
  lookup_scopes name outer = SOME snapshot /\
  FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz) /\
  snapshot.type = ArrayTV tv (Fixed n) /\
  snapshot.value = ArrayV (SArrayV kvs) /\
  ghost_inv d cenv cx ee G tn s ==>
  lookup_scopes name ee.scopes = SOME snapshot /\
  ptr_covers G tn p s sz /\
  (!w k mem. lookup_var p s = SOME w /\ k < n /\
    mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory tv
      (EL k (array_elements (ArrayTV tv (Fixed n)) (SArrayV kvs)))
      (w2n w + k * type_memory_size tv) mem)
Proof
  strip_tac >> drule for_handled_loop_cleanup_state >> strip_tac >>
  drule_all array_body_pop_snapshot >> strip_tac >>
  `lookup_scopes name ee.scopes = SOME snapshot` by metis_tac[] >>
  simp[] >> conj_tac
  >- (drule_all ghost_inv_local_ptr >> simp[]) >>
  rpt strip_tac >> drule_all for_local_array_element_robust >> simp[]
QED

(* The premises below are the successful checked callback endpoint, its
   source evaluation and its unmodified stmt_frag_ptr old-variable post.
   No memory-taint frame is imposed on that execution. *)
Theorem for_array_callback_recovery_ptr:
  cenv_top_ext cenv bc ei.scopes /\
  eval_stmts cx stmts ei = (res,ee) /\
  cenv_top_ext bc c3 ee.scopes /\ ghost_inv d c3 cx ee G tn s /\
  ee.scopes = sc :: rest /\
  (!name. name IN FDOM sc ==> lookup_scopes name rest = NONE) /\
  not_fresh_at sa p /\ ptr_covers G0 tn0 p s0 sz /\
  (!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
    lookup_var x s = SOME w) /\
  (!x. not_fresh_at sa x ==> FLOOKUP G x = FLOOKUP G0 x /\
    op_taint tn (Var x) = op_taint tn0 (Var x)) /\
  gas_path_ptr D lo ctx func PG G0 tn0 s0 steps G tn (OK s) /\
  FLOOKUP s0.vs_allocas aid = SOME region /\
  caller.cs_next_var <= sa.cs_next_var /\
  (!x. not_fresh_at caller x ==> FLOOKUP G0 x = FLOOKUP Gc x /\
    op_taint tn0 (Var x) = op_taint tc (Var x)) ==>
  ghost_inv d cenv cx (ee with scopes := rest) G tn s /\
  ptr_covers G tn p s sz /\
  FLOOKUP s.vs_allocas aid = SOME region /\
  (!x. not_fresh_at caller x ==> FLOOKUP G x = FLOOKUP Gc x /\
    op_taint tn (Var x) = op_taint tc (Var x))
Proof
  strip_tac >> conj_tac
  >- (irule ghost_inv_body_scope_projection >> conj_tac
      >- (qexists_tac `sc` >> simp[]) >>
      goal_assum (drule_at Any) >> metis_tac[]) >>
  conj_tac
  >- (irule callback_old_pointer_coverage >>
      goal_assum (drule_at Any) >> metis_tac[]) >>
  conj_tac
  >- (drule gas_path_ptr_old_allocations >> simp[]) >>
  rpt strip_tac >>
  `not_fresh_at sa x` by
    (irule stmtFragPtrTheory.not_fresh_at_mono >>
     goal_assum (drule_at Any) >> simp[]) >>
  metis_tac[]
QED


(* Consumer-premise audit for the frozen body For case:

   bodyPtrPreds.body_stmt_ptr_ok_def supplies supported_stmt and type_stmt
   for the whole For, plus expr_sim_inv and ce_locals_declared. The existing
   stmtSimForArray.array_for_hypotheses supplies, without a new restriction:
     - supported_stmts tops bindings stmts;
     - type_stmts (extend_local env id typ F) ret_ty stmts = SOME env_b;
     - iterator_unmodified for the fixed-array Name;
     - absence of supported internal-call roots in the body;
     - well_typed_expr for the Name and id NOTIN FDOM env.var_types.
   The Name typing gives FLOOKUP env.var_types name = SOME (ArrayT typ
   (Fixed n)). Thus name <> id, and extend_local_def/FLOOKUP_UPDATE retains
   that lookup in the body environment. This is exactly the environment
   passed to array_body_pop_snapshot, not the unextended outer environment.
   array_name_local_binding (already used by for_array_name_source_ptr)
   gives the source entry/type and compiler PtrVar binding. The source
   snapshot value/element list is the loop invariant, not a callback premise.

   For the target recovery interface, fresh_body_scope_shape supplies final
   head/tail shape and no shadow from source eval_stmts and the absent fresh
   binder; expr_sim_inv_absent_local obtains that absence at entry. Existing
   cenv_top_ext at entry and the actual stmt_frag_ptr normal post supply the
   two environment extensions and the final ghost_inv. Its old-variable
   value and ghost post, with the slot reserved before the body, recover
   coverage without any memory-taint equality. The checked normal endpoint
   supplies gas_path_ptr, whose allocation history preserves the recorded
   slot site. The caller prefix supplies only its older-variable ghost frame.
   The new for_handled_loop_cleanup_state explicitly connects the boolean
   handled round to the plain finally/pop theorem for every result branch.
   No typing/unmodified/internal-call premise was added to the frozen case.
*)
