(* Successful bounds checks leave the linked Slice operands available at sc. *)
Theory bodySliceBoundsLandingMods
Ancestors
  bodyFullBuiltinBytestringBounds bodyPtrBytestringBuiltinsExternalSlice
  bodyPtrBytestringBuiltinsBounds bodyFullUnwrapRun exprSimProps exprLoweringProps
  bodyPtrDefs fragExec ptrDiscipline venomState venomInst freshWrites list words

Theorem slice_bounds_landing_mods:
  compile_assert_slice_bounds start cnt limit sa = ((),sc) /\
  fn_has_code sa sc func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ alloca_history func s /\ alloca_inv s /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand start s = SOME (n2w i) /\
  eval_operand cnt s = SOME (n2w k) /\
  eval_operand limit s = SOME (n2w (LENGTH bs)) /\
  (!op. MEM op [start;cnt;limit] ==>
    op_prov G op = NONE /\ op_taint tn op = {} /\
    (!x. op = Var x ==> not_fresh_at sa x)) /\
  not_fresh_at sa src /\ lookup_var src s = SOME p /\
  ptr_covers G tn src s (LENGTH bs) /\
  w2n p + LENGTH bs < dimword (:256) /\ i+k <= LENGTH bs ==>
  ?zb G1 tn1.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK zb,G1,tn1)) /\
    (!es H. stmt_state_rel H ctx func cenv cx es s ==>
      stmt_state_rel H ctx func cenv cx es zb) /\
    zb = s with <|vs_vars := zb.vs_vars; vs_inst_idx := LENGTH sc.cs_current_insts|> /\
    s.vs_memory = zb.vs_memory /\ s.vs_allocas = zb.vs_allocas /\
    s.vs_alloca_next = zb.vs_alloca_next /\
    s.vs_labels = zb.vs_labels /\
    (!x. not_fresh_at sa x ==>
      lookup_var x zb = lookup_var x s /\ FLOOKUP G1 x = FLOOKUP G x /\
      op_taint tn1 (Var x) = op_taint tn (Var x)) /\
    tn1.t_mem = tn.t_mem /\ tn1.t_stor = tn.t_stor /\
    tn1.t_trans = tn.t_trans /\ tn1.t_imm = tn.t_imm /\
    alloca_history func zb /\ allocas_from lo zb /\ lo <= zb.vs_alloca_next /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp zb) /\
    zb.vs_current_bb = sc.cs_current_bb /\
    zb.vs_inst_idx = LENGTH sc.cs_current_insts /\ ~zb.vs_halted /\
    lookup_var src zb = SOME p /\ ptr_covers G1 tn1 src zb (LENGTH bs) /\
    eval_operand start zb = SOME (n2w i) /\
    eval_operand cnt zb = SOME (n2w k) /\
    eval_operand limit zb = SOME (n2w (LENGTH bs)) /\
    (!op. MEM op [start;cnt;limit] ==>
      op_prov G1 op = NONE /\ op_taint tn1 op = {}) /\
    sa.cs_next_var <= sc.cs_next_var /\ sa.cs_next_id <= sc.cs_next_id /\
    (!x. not_fresh_at sa x ==> not_fresh_at sc x) /\ local_ptrs_reserved cenv sc
Proof
  strip_tac >>
  `!op x. MEM op [start;cnt;limit] /\ op = Var x ==> not_fresh_at sa x` by
    (rpt strip_tac >> first_x_assum (drule_then strip_assume_tac) >> simp[]) >>
  `i < dimword (:256) /\ k < dimword (:256) /\
    LENGTH bs < dimword (:256) /\ i+k < dimword (:256)` by decide_tac >>
  drule_all_then strip_assume_tac slice_bounds_reserved_natural_runtime >>
  rename1 `run_inst_seq (emitted_insts sa sc) s = if _ then _ else OK u` >>
  `~(dimword (:256) <= i+k) /\ ~(LENGTH bs < i+k)` by decide_tac >>
  `run_inst_seq (emitted_insts sa sc) s = OK u` by simp[] >>
  drule_all bytestring_slice_bounds_full_run >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choose_then `G1` (qx_choose_then `tn1` strip_assume_tac))) >>
  qabbrev_tac `zb = u with vs_inst_idx := LENGTH sc.cs_current_insts` >>
  `zb = s with <|vs_vars := zb.vs_vars; vs_inst_idx := LENGTH sc.cs_current_insts|>` by
    (qpat_assum `u = s with vs_vars := u.vs_vars`
       (mp_tac o Q.AP_TERM `\st. st with vs_inst_idx := LENGTH sc.cs_current_insts`) >>
     simp[Abbr `zb`]) >>
  `!x. not_fresh_at sa x ==>
    lookup_var x zb = lookup_var x s /\ FLOOKUP G1 x = FLOOKUP G x /\
    op_taint tn1 (Var x) = op_taint tn (Var x)` by
    (simp[Abbr `zb`,lookup_var_def,NoAsms] >>
     qpat_assum `!x. not_fresh_at sa x ==> lookup_var x u = _ /\ _`
       (ACCEPT_TAC o REWRITE_RULE[lookup_var_def])) >>
  `alloca_history func zb` by
    (simp[Abbr `zb`] >> irule emitted_alloca_history >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl_tac [`emitted_insts sa sc`,`s`,`sa`] >>
     drule_then strip_assume_tac compile_assert_slice_bounds_layout >>
     fs[same_blocks_def,mk_inst_def,is_terminator_def]) >>
  `zb.vs_labels = s.vs_labels` by
    (qpat_assum `zb = s with <|vs_vars := _; vs_inst_idx := _|>` SUBST1_TAC >> simp[]) >>
  `!op. (!x. op = Var x ==> not_fresh_at sa x) ==>
    eval_operand op zb = eval_operand op s /\
    op_prov G1 op = op_prov G op /\ op_taint tn1 op = op_taint tn op` by
    (match_mp_tac reserved_operand_ghost_frame >> simp[]) >>
  `!op. MEM op [start;cnt;limit] ==>
    eval_operand op zb = eval_operand op s /\
    op_prov G1 op = NONE /\ op_taint tn1 op = {}` by
    (rpt strip_tac >>
     qpat_assum `!op. MEM op [start;cnt;limit] ==> _` (drule_then strip_assume_tac) >>
     qpat_assum `!op. (!x. op = Var x ==> _) ==> eval_operand op zb = _ /\ _`
       (drule_then strip_assume_tac) >> simp[]) >>
  `lookup_var src zb = SOME p /\ ptr_covers G1 tn1 src zb (LENGTH bs)` by
    (qpat_assum `!x. not_fresh_at sa x ==> lookup_var x zb = _ /\ _`
       (drule_then strip_assume_tac) >>
     qpat_x_assum `ptr_covers G tn src s _` mp_tac >>
     pure_rewrite_tac[ptr_covers_def] >> simp[]) >>
  drule_then strip_assume_tac compile_assert_slice_bounds_layout >>
  `!x. not_fresh_at sa x ==> not_fresh_at sc x` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  `local_ptrs_reserved cenv sc` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  qexistsl_tac [`zb`,`G1`,`tn1`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (rpt strip_tac >>
     qpat_assum `zb = s with <|vs_vars := _; vs_inst_idx := _|>` SUBST1_TAC >>
     simp[stmt_state_rel_inst_idx] >>
     irule stmt_state_rel_vars_frame >> simp[stmt_state_rel_inst_idx] >>
     rpt strip_tac >> rename1 `lookup_var x _ = lookup_var x _` >>
     `not_fresh_at sa x` by
       (qpat_x_assum `local_ptrs_reserved cenv sa` mp_tac >>
        simp[loweringStateRelDefsTheory.local_ptrs_reserved_def] >> metis_tac[]) >>
     qpat_assum `!x. not_fresh_at sa x ==> lookup_var x zb = _ /\ _`
       (qspec_then `x` (drule_then strip_assume_tac)) >> fs[lookup_var_def]) >>
  `eval_operand start zb = SOME (n2w i) /\ eval_operand cnt zb = SOME (n2w k) /\
    eval_operand limit zb = SOME (n2w (LENGTH bs))` by
    (qpat_assum `!op. MEM op [start;cnt;limit] ==> eval_operand op zb = _ /\ _`
      (fn th => map_every (fn q => qspec_then q mp_tac th) [`start`,`cnt`,`limit`]) >> simp[]) >>
  `!op. MEM op [start;cnt;limit] ==> op_prov G1 op = NONE /\ op_taint tn1 op = {}` by
    (rpt strip_tac >>
     qpat_assum `!op. MEM op [start;cnt;limit] ==> eval_operand op zb = _ /\ _`
       (drule_then strip_assume_tac) >> simp[]) >>
  `allocas_from lo zb /\ (ctx_has_dalloca ctx ==> allocas_below_fmp zb)` by
    (qpat_assum `zb = s with <|vs_vars := _; vs_inst_idx := _|>` SUBST1_TAC >>
     qpat_x_assum `allocas_from lo s` mp_tac >>
     qpat_x_assum `ctx_has_dalloca ctx ==> allocas_below_fmp s` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[allocas_from_def,allocas_below_fmp_def] >> metis_tac[]) >>
  `s.vs_memory = zb.vs_memory /\ s.vs_allocas = zb.vs_allocas /\
   s.vs_alloca_next = zb.vs_alloca_next /\ s.vs_labels = zb.vs_labels /\
   lo <= zb.vs_alloca_next /\ zb.vs_current_bb = sc.cs_current_bb /\
   zb.vs_inst_idx = LENGTH sc.cs_current_insts /\ ~zb.vs_halted` by
    (qpat_assum `zb = s with <|vs_vars := _; vs_inst_idx := _|>` SUBST1_TAC >>
     fs[same_blocks_def]) >>
  `sa.cs_next_var <= sc.cs_next_var /\ sa.cs_next_id <= sc.cs_next_id` by simp[] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
