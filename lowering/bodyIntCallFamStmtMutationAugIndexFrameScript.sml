(* Resource-aware target transport across effectful forced indices. *)
Theory bodyIntCallFamStmtMutationAugIndexFrame
Ancestors
  bodyIntCallJointContract targetSubscriptMemory targetSubscriptSplit
  targetPlaceSimDefs loweringPosts exprSimDefs loweringStateRelDefs
  compileEnv freshWrites exprSimProps exprSimHypsDefs exprReasonOperand
  exprBopSimProps exprLoweringProps

Theorem intcall_target_index_frame:
  target_post fp.jc_ctx fp.jc_func ce fp.jc_cx es sa sm s0 es1 pv vt rb t /\
  intcall_expr_cont fp ce env es1 sm t es2 sn u /\
  stmt_state_rel fp.jc_ctx fp.jc_func ce fp.jc_cx es s0 /\
  local_ptrs_reserved ce sa /\ local_ptrs_reserved ce sm /\
  MAP FDOM es.scopes = MAP FDOM es1.scopes /\
  place_readable fp.jc_cx es2 pv /\
  sa.cs_next_var <= sm.cs_next_var /\ sm.cs_next_var <= sn.cs_next_var /\
  sa.cs_next_id <= sm.cs_next_id /\ (!l. FST rb <> Label l) ==>
  target_post fp.jc_ctx fp.jc_func ce fp.jc_cx es sa sn s0 es2 pv vt rb u
Proof
  simp[target_post_def, intcall_expr_cont_def, intcall_expr_res_def] >> strip_tac >>
  `!x. not_fresh_at sa x ==> not_fresh_at sm x` by
    metis_tac[not_fresh_at_mono] >>
  `!x. not_fresh_at sm x ==> not_fresh_at sn x` by
    metis_tac[not_fresh_at_mono] >>
  simp[] >> rpt conj_tac
  >- (qexists_tac `w` >> conj_tac
      >- (irule eval_operand_frame >> simp[] >> qexistsl_tac [`sm`, `t`] >> simp[]) >>
      irule target_place_ptr_values_frame >> qexistsl_tac [`t`, `sm`] >> simp[])
  >- (rpt strip_tac >>
      `local_ptrs_rel fp.jc_func ce es.scopes s0` by
        fs[stmt_state_rel_def, state_rel_def] >>
      `!n b sz'. local_region ce es1.scopes t n b sz' ==>
                  off + sz <= b \/ b + sz' <= off` by
        (rpt strip_tac >>
         qpat_x_assum `!n b sz'. local_region ce es.scopes s0 _ _ _ ==> _` irule >>
         qexists_tac `n` >> irule local_region_frame >>
         conj_tac >- (qexists_tac `fp.jc_func` >> simp[]) >>
         qexistsl_tac [`sa`, `es1.scopes`, `t`] >> simp[]) >>
      `FLOOKUP t.vs_allocas aid = SOME (off,sz)` by metis_tac[] >>
      `aid < sm.cs_next_id` by decide_tac >> metis_tac[]) >>
  irule locals_kept_trans >> qexistsl_tac [`es1`, `sa`, `t`] >> simp[]
QED
