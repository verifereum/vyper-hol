Theory bodyIntCallSourceReturn
Ancestors
  bodyIntCallReturnAdapters exprLowering compileEnv exprLoweringProps
  loweringPosts intCallResult venomExecSemantics

(* The compiler's stronger, provenance-carrying branches are consumed here;
   the final source state is restored explicitly, not a matching parameter. *)
Theorem source_return_dispatch:
  !nret.
  post_value_type ce e = expr_type e /\
  compile_multi_vvs compile_expr ce es sa = (vals,s1) /\
  compile_stage_intcall_args ce vals flags tys s2 = (args,si) /\
  fn_has_code sa sb func /\ local_ptrs_reserved ce sa /\
  nr = nret /\ rb = rbs /\ cty = expr_type e /\
  (nr = 0 /\ cty = NoneT ==>
    s2 = s1 /\ arg_ops = args /\
    (?u. emit_void INVOKE (Label lbl::args) si = (u,sb)) /\
    vv = StackValue cty (Lit 0w)) /\
  (0 < nr \/ cty <> NoneT ==>
    ?buf aid off.
      compile_alloc_buffer (if 0 < nr then 32 * nr else rb) s1 = (buf,s2) /\
      vv = LocatedValue cty (base_ptr buf) /\
      eval_operand buf.buf_operand t = SOME (n2w off) /\
      FLOOKUP t.vs_allocas aid = SOME (off,buf.buf_size) /\ aid = s1.cs_next_id /\
      (?ai. MEM ai (fn_insts func) /\ ai.inst_opcode = ALLOCA /\ ai.inst_id = aid) /\
      sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\
      (0 < nr ==> arg_ops = args /\
        ?results sj u. emit_multi_op INVOKE (Label lbl::args) nr si = (results,sj) /\
          store_multi_results buf.buf_operand results 0 sj = (u,sb)) /\
      (nr = 0 ==> arg_ops = buf.buf_operand::args /\
        (?u. emit_void INVOKE (Label lbl::buf.buf_operand::args) si = (u,sb)) /\
        (w:256 word) = n2w off /\ type_memory_size tv <= buf.buf_size /\
        w2n w + type_memory_size tv <= t.vs_alloca_next)) /\
  t.vs_current_bb = si.cs_current_bb /\
  t.vs_inst_idx = LENGTH si.cs_current_insts /\
  gas_invoke_entry (ctx,func) t callee entered /\
  gas_path ctx callee entered n (IntRet ir cs) /\
  ir.iret_adopt_fmp = NONE /\ LENGTH ir.iret_values = nret /\
  (nret = 0 /\ expr_type e <> NoneT ==> val_in_memory tv v (w2n w) cs.vs_memory) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
  (0 < nret ==> 0 < returns_stack_count
    (\name. MAP (FST o SND) (get_struct_fields ce.ce_struct_fields name)) (expr_type e)) /\
  value_has_type tv v /\ intret_vals_match tv v ir.iret_values /\
  stmt_state_rel ctx func ce cx (es1 with scopes := prev) t /\
  state_rel other ce cx (ee with <|scopes := []; gas_obs := []|>) cs /\
  immutable_alloca_sep func ce cx (ee with scopes := prev) t /\
  wb_frame ce es0 sa s0 t /\
  (!id b sz. local_region ce es0.scopes s0 id b sz ==>
    local_region ce prev t id b sz) /\
  (!id b sz aid off asz.
    local_region ce prev t id b sz /\ FLOOKUP t.vs_allocas aid = SOME (off,asz) /\
    sa.cs_next_id <= aid /\ aid < sb.cs_next_id ==> regions_disjoint b sz off asz) /\
  (!b sz. b + sz <= t.vs_alloca_next /\
    (!aid off asz. FLOOKUP t.vs_allocas aid = SOME (off,asz) /\
      sa.cs_next_id <= aid /\ aid < sb.cs_next_id ==> regions_disjoint b sz off asz) ==>
    mem_bytes_at b sz cs.vs_memory = mem_bytes_at b sz t.vs_memory) ==>
  ?k out. gas_path ctx func t (n + k) (OK out) /\
    vv_post ctx func ce cx e es0 sa sb s0
      (ee with <|scopes := prev; gas_obs := []|>) (Value v) vv out /\
    out.vs_current_bb = sb.cs_current_bb /\
    out.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  gen_tac >> strip_tac >>
  irule compiled_return_dispatch >>
  simp[] >>
  goal_assum (drule_at (Pat `compile_multi_vvs _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `compile_stage_intcall_args _ _ _ _ _ = _`)) >>
  goal_assum (drule_at (Pat `gas_path _ _ _ _ _`)) >>
  goal_assum (drule_at (Pat `state_rel _ _ _ _ _`)) >>
  qexistsl_tac [`es1`,`lbl`,`prev`,`rbs`,`w`] >>
  gvs[] >> asm_rewrite_tac[] >> disch_tac >>
  qpat_x_assum `(_ ==> 0 < LENGTH ir.iret_values) ==> _` mp_tac >>
  (impl_tac >- asm_rewrite_tac[]) >> strip_tac >>
  qexistsl_tac [`buf`,`s1.cs_next_id`,`off`] >>
  asm_rewrite_tac[] >> metis_tac[]
QED
