(* Readonly unwrap endpoints, including the caller's state frame. *)
Theory bodyIntCallStageUnwrapRead
Ancestors
  bodyIntCallHeldStorageWord bodyIntCallHeldImmutableWord exprSimConvertBytes
  exprOperandVar exprSimHypsDefs venomState exprLoweringProps bodyIntCallHeldRead

Theorem intcall_readonly_state_frame:
  stmt_state_rel ctx func ce cx es s /\ local_ptrs_reserved ce sm /\
  (t with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s /\
  (!x w. not_fresh_at sm x /\ lookup_var x s = SOME w ==>
         lookup_var x t = SOME w) ==>
  stmt_state_rel ctx func ce cx es t
Proof
  strip_tac >>
  `t with vs_inst_idx := s.vs_inst_idx = s with vs_vars := t.vs_vars` by
    gvs[venom_state_component_equality] >>
  `stmt_state_rel ctx func ce cx es (t with vs_inst_idx := s.vs_inst_idx)` by
    (irule convert_readonly_state_frame >>
     qexistsl_tac [`s`, `sm`] >> gvs[lookup_var_def]) >>
  gvs[stmt_state_rel_inst_idx]
QED

Theorem intcall_readonly_unwrap_run:
  unwrap_value ce vv sm = (op,sn) /\
  ((?sty x. vv = StackValue sty x) \/
   (?sty p. vv = LocatedValue sty p /\
      (p.ptr_location = LocMemory \/ is_word_type sty))) /\
  vv_holds ce cx ty raw vv es s /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  stmt_state_rel ctx func ce cx es s /\ local_ptrs_reserved ce sm /\
  fn_has_code sm sn func /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?v t. gas_marked_exec F (ctx,func) (read_result cx raw) (es,s)
          [] (INL v) es (OK t) /\
    expr_val_rel cx ty v op t /\ ~t.vs_halted /\
    t.vs_current_bb = sn.cs_current_bb /\
    t.vs_inst_idx = LENGTH sn.cs_current_insts /\
    (t with <|vs_vars := s.vs_vars; vs_inst_idx := s.vs_inst_idx|>) = s /\
    (!x w. not_fresh_at sm x /\ lookup_var x s = SOME w ==>
           lookup_var x t = SOME w)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `(?sty x. vv = StackValue sty x) \/
            (?sty p. vv = LocatedValue sty p /\ p.ptr_location = LocMemory)`
  >- (irule intcall_held_nonallocating_read >> metis_tac[]) >>
  `?sty p. vv = LocatedValue sty p /\ is_word_type sty /\
     p.ptr_location <> LocMemory` by metis_tac[] >>
  gvs[] >> Cases_on `p.ptr_location`
  >- gvs[]
  >- (drule intcall_held_storage_word_read >> simp[] >>
      disch_then (qspec_then `ctx` mp_tac) >> simp[])
  >- (drule intcall_held_storage_word_read >> simp[] >>
      disch_then (qspec_then `ctx` mp_tac) >> simp[])
  >- (`!x. p.ptr_operand = Var x ==> not_fresh_at sm x` by
        gvs[contextTheory.vv_operand_def] >>
      drule intcall_held_immutable_word_read >> simp[]) >>
  gvs[loweringPostsTheory.vv_holds_def]
QED

Theorem intcall_stage_unwrap_readonly:
  unwrap_value ce vv sm = (op,sn) /\
  ((?sty x. vv = StackValue sty x) \/
   (?sty p. vv = LocatedValue sty p /\
      (p.ptr_location = LocMemory \/ is_word_type sty))) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  stmt_state_rel ctx func ce cx es s /\ local_ptrs_reserved ce sm /\
  intcall_held_args ce cx a sm es s ((ty,raw,vv)::H) /\
  fn_has_code sm sn func /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?v w t. gas_marked_path F ctx func s 0 (OK t) /\
    read_result cx raw es = (INL v,es) /\ eval_operand op t = SOME w /\
    value_has_type tv v /\ val_wf tv v /\
    (if is_word_type ty then w = typed_val_to_w256 tv v
     else val_in_memory tv v (w2n w) t.vs_memory) /\
    stmt_state_rel ctx func ce cx es t /\
    intcall_held_args ce cx a sn es t H /\ wb_frame ce es sm s t /\
    ~t.vs_halted /\ t.vs_current_bb = sn.cs_current_bb /\
    t.vs_inst_idx = LENGTH sn.cs_current_insts /\
    (!x q. not_fresh_at sm x /\ lookup_var x s = SOME q ==>
           lookup_var x t = SOME q) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
                 FLOOKUP t.vs_allocas aid = SOME entry) /\
    (!aid. sn.cs_next_id <= aid /\ aid NOTIN FDOM s.vs_allocas ==>
           aid NOTIN FDOM t.vs_allocas)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `MEM (ty,raw,vv) ((ty,raw,vv)::H)` by simp[] >>
  drule_all bodyIntCallHeldArgsTheory.intcall_held_args_member >> strip_tac >>
  drule_all intcall_readonly_unwrap_run >> strip_tac >>
  `sm.cs_next_id <= sn.cs_next_id /\ sm.cs_next_var <= sn.cs_next_var` by
    (mp_tac (Q.SPECL [`ce`, `vv`, `sm`] ci_mono_unwrap_value) >>
     simp[ci_mono_def]) >>
  `local_ptrs_rel func ce es.scopes s` by
    gvs[stmt_state_rel_def, compileEnvTheory.state_rel_def] >>
  `intcall_held_args ce cx a sn es t H` by
    (irule intcall_held_args_readonly_tail >>
     qexistsl_tac [`func`, `s`, `sm`] >>
     gvs[bodyIntCallHeldArgsTheory.intcall_held_args_def]) >>
  `stmt_state_rel ctx func ce cx es t` by
    (irule intcall_readonly_state_frame >> metis_tac[]) >>
  `t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas` by
    (qpat_x_assum `_ with <|vs_vars := _; vs_inst_idx := _|> = s`
       (SUBST1_TAC o SYM) >> simp[]) >>
  `wb_frame ce es sm s t` by
    simp[loweringPostsTheory.wb_frame_def, exprSimPropsTheory.locals_kept_mem] >>
  `read_result cx raw es = (INL v,es)` by
    (qpat_x_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
     simp[gasSummaryTheory.gas_marked_exec_def] >> strip_tac >>
     qpat_x_assum `!tail. _` (qspec_then `es.gas_obs` mp_tac) >> simp[]) >>
  gvs[loweringPostsTheory.expr_val_rel_def] >>
  qexistsl_tac [`w`, `t`] >> simp[] >>
  gvs[gasSummaryTheory.gas_marked_exec_def]
QED
