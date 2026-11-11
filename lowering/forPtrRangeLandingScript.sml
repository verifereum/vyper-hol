(* Checked landing after the body: normal jumps, continue/break stay put. *)
Theory forPtrRangeLanding
Ancestors forPtrBoundary forPtrRangeCallback stmtSimDefs stmtSimProps
  exprLoweringProps
  bodyPtrDefs fragGasPathPtr stmtFragPtr venomState loweringPosts

Theorem for_body_lands_path_ptr:
  stmt_lands (InLoop exit_lbl incr_lbl) sb res s /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\
  (res = INL () ==> ~block_is_terminated sb) /\
  (~block_is_terminated sb ==>
    sj.cs_blocks = sb.cs_blocks /\ sj.cs_current_bb = sb.cs_current_bb /\
    sj.cs_current_insts = sb.cs_current_insts ++
      [mk_inst sb.cs_next_id JMP [Label incr_lbl] []] /\
    fn_has_code sb sj func) ==>
  gas_path_ptr D 0 ctx func PG G tn s 0 G tn
    (OK (if res = INL () then jump_to incr_lbl s else s)) /\
  (if res = INL () then jump_to incr_lbl s else s).vs_inst_idx = 0 /\
  (res = INR BreakException ==> s.vs_current_bb = exit_lbl) /\
  (res <> INR BreakException ==>
    (if res = INL () then jump_to incr_lbl s else s).vs_current_bb = incr_lbl)
Proof
  strip_tac >> Cases_on `res = INL ()`
  >- (gvs[stmt_lands_def] >>
      conj_tac
      >- (irule for_emit_jump_zero_path_ptr >> simp[] >>
          qexistsl_tac [`sb`, `sj`] >> simp[]) >>
      simp[jump_to_def]) >>
  gvs[stmt_lands_def] >> simp[jump_to_def] >>
  irule (cj 1 gas_path_ptr_rules) >> simp[]
QED

Theorem for_body_landing_transport:
  stmt_state_rel ctx func cenv cx es s /\ ghost_inv d cenv cx es G tn s /\
  ptr_covers G tn p s sz /\
  t = (if res = INL () then jump_to incr_lbl s else s) ==>
  stmt_state_rel ctx func cenv cx es t /\ ghost_inv d cenv cx es G tn t /\
  ptr_covers G tn p t sz /\ ~t.vs_halted = ~s.vs_halted /\
  t.vs_allocas = s.vs_allocas /\ (!x. lookup_var x t = lookup_var x s)
Proof
  strip_tac >> gvs[] >> Cases_on `res = INL ()` >> simp[] >>
  rewrite_tac[stmt_state_rel_jump_to, ghost_inv_jump_to] >>
  fs[ptr_covers_def, jump_to_def, lookup_var_def, ghost_inv_jump_to]
QED

Theorem for_range_callback_landing_ptr:
  for_code func cenv bc ty stmts id tyv p sz ainst cv ev dv nv
    cond_lbl exit_lbl body_lbl incr_lbl j1 j2 j3 bbb i1 i2 i3 sb0 sb1 sj /\
  lookup_scopes id esk.scopes = NONE /\
  not_local_ptr bc (FEMPTY :: esk.scopes) p /\
  eval_stmts cx stmts (esk with scopes :=
    (FEMPTY |+ (id,entry)) :: esk.scopes) = (res,ee) /\
  cenv_top_ext bc c3 ee.scopes /\ stmt_state_rel ctx func c3 cx ee s /\
  ghost_inv d c3 cx ee G tn s /\
  FLOOKUP s.vs_allocas ainst.inst_id = SOME (w2n a,sz) /\
  ptr_covers G tn p s sz /\
  stmt_lands (InLoop exit_lbl incr_lbl) sb1 res s /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ (res = INL () ==> ~block_is_terminated sb1) ==>
  ?sc rest t.
    ee.scopes = sc :: rest /\ lookup_scopes id rest = NONE /\
    t = (if res = INL () then jump_to incr_lbl s else s) /\
    gas_path_ptr D 0 ctx func PG G tn s 0 G tn (OK t) /\
    t.vs_inst_idx = 0 /\ ~t.vs_halted /\
    (res = INR BreakException ==> t.vs_current_bb = exit_lbl) /\
    (res <> INR BreakException ==> t.vs_current_bb = incr_lbl) /\
    stmt_state_rel ctx func cenv cx (ee with scopes := rest) t /\
    ghost_inv d cenv cx (ee with scopes := rest) G tn t /\
    ptr_covers G tn p t sz /\ t.vs_allocas = s.vs_allocas /\
    (!x. lookup_var x t = lookup_var x s) /\
    (!name lo z. local_region cenv rest t name lo z ==>
      regions_disjoint (w2n a) sz lo z)
Proof
  strip_tac >> drule_all for_range_callback_outer_state >> strip_tac >>
  `gas_path_ptr D 0 ctx func PG G tn s 0 G tn
    (OK (if res = INL () then jump_to incr_lbl s else s)) /\
   (if res = INL () then jump_to incr_lbl s else s).vs_inst_idx = 0 /\
   (res = INR BreakException ==> s.vs_current_bb = exit_lbl) /\
   (res <> INR BreakException ==>
     (if res = INL () then jump_to incr_lbl s else s).vs_current_bb = incr_lbl)` by
    (irule for_body_lands_path_ptr >> simp[] >>
     qexistsl_tac [`sb1`, `sj`] >>
     fs[stmtSimForLoopTheory.for_code_def]) >>
  qexistsl_tac [`sc`, `rest`,
    `if res = INL () then jump_to incr_lbl s else s`] >> simp[] >>
  Cases_on `res = INL ()` >> gvs[] >>
  rewrite_tac[stmt_state_rel_jump_to] >>
  fs[loweringStateRelDefsTheory.local_region_def, ptr_covers_def,
     jump_to_def, lookup_var_def, ghost_inv_jump_to] >> first_assum ACCEPT_TAC
QED
