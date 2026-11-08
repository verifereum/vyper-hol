(* Fresh result allocation, with the entry-expression frame retained. *)
Theory extcallReturnFrame
Ancestors
  exprSimAlloc exprSimProps loweringPosts exprLoweringProps compileEnv
  context fragExec venomState finite_map list arithmetic words

Theorem extcall_result_allocation:
  compile_alloc_buffer sz sr = (buf,sm) /\ fn_has_code sr sm func /\
  stmt_state_rel ctx func cenv cx ee t /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sr /\ local_ptrs_reserved cenv sa /\
  sz < dimword (:256) /\ wb_frame cenv es sa s0 t /\
  MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sr.cs_next_var /\ sa.cs_next_id <= sr.cs_next_id ==>
  ?u w. frag_exec ctx sr sm (\z. z = t) (\z. z = u) R /\
    stmt_state_rel ctx func cenv cx ee u /\
    eval_operand buf.buf_operand u = SOME w /\
    FLOOKUP u.vs_allocas sr.cs_next_id = SOME (w2n w,sz) /\
    w2n w + sz < dimword (:256) /\ u.vs_memory = t.vs_memory /\
    sr.cs_next_id < sm.cs_next_id /\
    wb_frame cenv es sa s0 u /\
    (!name b len. local_region cenv es.scopes s0 name b len ==>
       regions_disjoint (w2n w) sz b len) /\
    (!aid b len. aid < sr.cs_next_id /\
       FLOOKUP t.vs_allocas aid = SOME (b,len) ==>
       regions_disjoint (w2n w) sz b len) /\
    (!aid entry. FLOOKUP t.vs_allocas aid = SOME entry ==>
       FLOOKUP u.vs_allocas aid = SOME entry) /\
    (!x. not_fresh_at sr x ==> lookup_var x u = lookup_var x t) /\
    (?p. buf.buf_operand = Var p /\ not_fresh_at sm p) /\
    contract_storage u = contract_storage t /\
    contract_transient u = contract_transient t
Proof
  rpt strip_tac >>
  drule_all (alloc_buffer_source_frag |> SPEC_ALL |>
    Q.INST [`src` |-> `Lit 0w`, `a` |-> `0w`] |>
    SIMP_RULE (srw_ss()) [eval_operand_def]) >>
  disch_then (qspec_then `R` strip_assume_tac) >>
  `!x w. not_fresh_at sa x /\ lookup_var x s0 = SOME w ==>
     lookup_var x u = SOME w` by
    (rpt strip_tac >>
     `not_fresh_at sr x` by (gvs[not_fresh_at_def] >> decide_tac) >>
     fs[wb_frame_def] >> metis_tac[]) >>
  qexistsl_tac [`u`, `w`] >> simp[] >> conj_tac
  >- (fs[wb_frame_def] >> metis_tac[locals_kept_mem_tail]) >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!name b len. local_region cenv ee.scopes u name b len ==> _` irule >>
      qexists_tac `name` >> irule local_region_frame_fwd >>
      goal_assum (drule_at Any) >> simp[] >> qexists_tac `sa` >> simp[]) >>
  metis_tac[]
QED
