(* Same-source counted joins; these do not simulate an enclosing evaluator. *)
Theory bodyIntCallJointCounted
Ancestors
  bodyIntCallJointTuple gasOutcome gasSummary fragGasMode stmtSimDeclCompose

Theorem gas_outcome_zero_success_continuation:
  gas_outcome memory tops (ctx,func) source (es,s0) Q R /\
  (!res ee u. Q res ee u ==> ?v.
    gas_marked_path memory ctx func u 0 (OK v) /\ Q' res ee v) ==>
  gas_outcome memory tops (ctx,func) source (es,s0) Q' R
Proof
  simp[gas_outcome_def, gas_summary_at_def] >> strip_tac
  >- (qpat_x_assum `!res ee u. _` drule >> strip_tac >>
      qexists_tac `marks` >> disj1_tac >>
      qexistsl_tac [`res`, `es_end`, `OK v`] >> simp[] >>
      gvs[gas_marked_exec_def] >>
      drule_all gas_marked_path_then >> simp[]) 
  >- (qexists_tac `marks` >> disj1_tac >> metis_tac[]) >>
  qexists_tac `marks` >> disj2_tac >> metis_tac[]
QED

Theorem joint_tuple_word_suffix_outcome:
  emit_op ADD [pop; Lit 0w] sn = (dst,sp) /\
  compile_store_memory ce src dst ty sty sp = ((),sb) /\
  is_word_type ty /\ fn_has_code sn sb func /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  gas_outcome F tops (ctx,func) source (es,s0)
    (\res ee u. ?p w.
      P res ee u /\ stmt_state_rel ctx func ce cx ee u /\
      eval_operand pop u = SOME p /\ eval_operand src u = SOME w /\
      (!x. src = Var x ==> x <> STRING #"%" (toString sn.cs_next_var)) /\
      not_local_ptr ce ee.scopes (STRING #"%" (toString sn.cs_next_var)) /\
      FLOOKUP u.vs_allocas inst.inst_id = SOME (w2n p,sz) /\ 32 <= sz /\
      (!name lb len. local_region ce ee.scopes u name lb len ==>
        regions_disjoint (w2n p) sz lb len) /\
      EVERY (\(off,len). regions_disjoint (w2n p) sz off len) hs /\
      ~u.vs_halted /\ u.vs_current_bb = sn.cs_current_bb /\
      u.vs_inst_idx = LENGTH sn.cs_current_insts) R ==>
  gas_outcome F tops (ctx,func) source (es,s0)
    (\res ee v. ?u p w.
      P res ee u /\
      v = ((mstore (w2n p) w
        (update_var (STRING #"%" (toString sn.cs_next_var)) p u))
        with vs_inst_idx := LENGTH sb.cs_current_insts) /\
      stmt_state_rel ctx func ce cx ee v /\
      EVERY (\(off,len). mem_bytes_at off len v.vs_memory =
                            mem_bytes_at off len u.vs_memory) hs /\
      (ce.ce_is_ctor ==> !name tv value off.
        FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
        FLOOKUP (case ALOOKUP ee.immutables cx.txn.target of
          NONE => FEMPTY | SOME imms => get_source_immutables ce.ce_module imms)
          name = SOME (tv,value) ==>
        mem_bytes_at off (type_memory_size tv) v.vs_memory =
        mem_bytes_at off (type_memory_size tv) u.vs_memory)) R
Proof
  strip_tac >> drule gas_outcome_zero_success_continuation >>
  disch_then irule >> BETA_TAC >> rpt strip_tac >>
  drule_all joint_tuple_word_suffix_path >>
  disch_then (qspec_then `ctx` assume_tac) >>
  drule_all joint_tuple_word_suffix_frame >>
  disch_then (qspecl_then [`w`, `p`, `LENGTH sb.cs_current_insts`]
    strip_assume_tac) >>
  qexists_tac `((mstore (w2n p) w
    (update_var (STRING #"%" (toString sn.cs_next_var)) p u))
    with vs_inst_idx := LENGTH sb.cs_current_insts)` >>
  simp[gas_marked_path_def] >>
  qexistsl_tac [`u`, `p`, `w`] >> gvs[] >> first_assum ACCEPT_TAC
QED

(* Q can in particular be the exact framed post of the suffix theorem above.
   This transport retains that entire post, including its original child u. *)
Theorem joint_tuple_alloc_prefix_outcome:
  compile_alloc_buffer sz sa = (buf,sm) /\ fn_has_code sa sm func /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq (emitted_insts sa sm) s = OK t /\
  gas_outcome F tops (ctx,func) source
    (es,t with vs_inst_idx := LENGTH sm.cs_current_insts) Q R ==>
  gas_outcome F tops (ctx,func) source (es,s) Q R
Proof
  strip_tac >> drule_all joint_tuple_alloc_prefix_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  irule gas_outcome_zero_prefix >>
  qexists_tac `t with vs_inst_idx := LENGTH sm.cs_current_insts` >>
  simp[gas_marked_path_def]
QED
