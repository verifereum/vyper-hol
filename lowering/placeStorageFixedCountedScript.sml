(* Arbitrary-destination counted storage copies with semantic endpoint facts. *)
Theory placeStorageFixedCounted
Ancestors
  bodyMemAssignTopCopySuffix bodyMemAssignTopCopySem bodyMemAssignTopCopyCompiler
  bodyMemAssignTopCopyPaths stmtSimStoreCopy allocaHistoryFragment
  compileEnv venomState fragGasMode allocaHistory

Theorem storage_fixed_place_path:
  (loc = LocStorage \/ loc = LocTransient) /\
  compile_word_copy_loop src dst n LocMemory loc F sa = (u,sb) /\
  fn_has_code sa sb func /\ n < dimword (:256) /\
  w2n b + 32*n <= s.vs_alloca_next /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME b /\ eval_operand dst s = SOME k /\
  ~s.vs_halted /\ ~s.vs_call_ctx.cc_static /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  local_ptrs_reserved cenv sa /\ alloca_history func s /\
  stmt_state_rel ctx func cenv cx es (store_copy_prefix loc b k s n) ==>
  ?t. gas_marked_path T ctx func s 0 (OK t) /\
      stmt_state_rel ctx func cenv cx es t /\
      store_copy_frame sa loc b k s n t /\
      ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
      alloca_history func t
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all topcopy_compile_loop_path >>
  disch_then (qspec_then `ctx` (qx_choose_then `t` strip_assume_tac)) >>
  `stmt_state_rel ctx func cenv cx es t` by
    (irule topcopy_normalized_state >> qexistsl_tac [`s`, `sa`] >>
     fs[store_copy_frame_def, store_copy_normalize_def] >> gvs[]) >>
  `t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next` by
    (fs[store_copy_frame_def] >> drule topcopy_normalize_allocations >> simp[]) >>
  `sb.cs_current_insts = []` by
    (drule_all topcopy_code_certificate >> strip_tac >> simp[]) >>
  `alloca_history func t` by
    (irule alloca_history_jump >> simp[] >> qexists_tac `s` >> simp[]) >>
  qexists_tac `t` >> fs[store_copy_frame_def]
QED
