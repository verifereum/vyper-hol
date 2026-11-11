Theory bodyIntCallReturnAdapters
Ancestors
  bodyIntCallAssemblyModes bodyIntCallCompilerBoundary vyperValue exprLoweringProps venomMemDefs

Theorem compiled_void_return:
  expr_has_effect e /\
  post_value_type ce e = expr_type e /\
  compile_multi_vvs compile_expr ce es sa = (vals,s1) /\
  ci_mono s1 s2 /\
  compile_stage_intcall_args ce vals flags tys s2 = (args,si) /\
  emit_void INVOKE ops si = ((),sb) /\
  fn_has_code sa sb func /\ local_ptrs_reserved ce sa /\
  t.vs_current_bb = si.cs_current_bb /\
  t.vs_inst_idx = LENGTH si.cs_current_insts /\
  gas_invoke_entry (ctx,func) t callee entered /\
  gas_path ctx callee entered n (IntRet ir cs) /\
  ir.iret_values = [] /\ ir.iret_adopt_fmp = NONE /\
  expr_type e = NoneT /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  value_has_type tv v /\
  stmt_state_rel ctx func ce cx (es1 with scopes := prev) t /\
  state_rel other ce cx (ee with <|scopes := []; gas_obs := []|>) cs /\
  immutable_alloca_sep func ce cx (ee with scopes := prev) t /\
  wb_frame ce es0 (es1 with scopes := prev) sa s0 t /\
  (!id b sz. local_region ce es0.scopes s0 id b sz ==>
    local_region ce prev t id b sz) /\
  (!id b sz aid off asz.
    local_region ce prev t id b sz /\
    FLOOKUP t.vs_allocas aid = SOME (off,asz) /\
    sa.cs_next_id <= aid /\ aid < hi ==> regions_disjoint b sz off asz) /\
  (!b sz. b + sz <= t.vs_alloca_next /\
    (!aid off asz. FLOOKUP t.vs_allocas aid = SOME (off,asz) /\
      sa.cs_next_id <= aid /\ aid < hi ==> regions_disjoint b sz off asz) ==>
    mem_bytes_at b sz cs.vs_memory = mem_bytes_at b sz t.vs_memory) /\
  ef = (ee with <|scopes := prev; gas_obs := []|>) /\
  vv = StackValue NoneT (Lit 0w) ==>
  ?k out. gas_path ctx func t (n + k) (OK out) /\
    vv_post ctx func ce cx e es0 sa sb s0 ef (Value v) vv out /\
    out.vs_current_bb = sb.cs_current_bb /\
    out.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  drule_all intcall_void_compiler_boundary >> strip_tac >>
  `tv = NoneTV` by
    (qpat_x_assum `evaluate_type _ _ = _` mp_tac >>
     asm_rewrite_tac[evaluate_type_def] >> simp[]) >>
  `value_has_type NoneTV v` by metis_tac[] >>
  `v = NoneV` by fs[] >>
  `immutable_alloca_sep func ce cx
    (ee with <|scopes := prev; gas_obs := []|>) t` by
    (irule immutable_alloca_sep_fields >> goal_assum (drule_at Any) >>
     simp[] >> metis_tac[]) >>
  drule_all (Q.INST [`es` |-> `es1 with scopes := prev`,
    `ee` |-> `ee with gas_obs := []`] (SPEC_ALL void_return_endpoint)
    |> SIMP_RULE (srw_ss()) [] |> GEN_ALL) >>
  strip_tac >> qexistsl_tac [`k`,`out`] >> gvs[]
QED

Theorem compiled_memory_return:
  expr_has_effect e /\
  post_value_type ce e = expr_type e /\
  compile_multi_vvs compile_expr ce es sa = (vals,s1) /\
  ci_mono s1 s2 /\
  compile_stage_intcall_args ce vals flags tys s2 = (args,si) /\
  emit_void INVOKE ops si = ((),sb) /\
  fn_has_code sa sb func /\ local_ptrs_reserved ce sa /\
  t.vs_current_bb = si.cs_current_bb /\
  t.vs_inst_idx = LENGTH si.cs_current_insts /\
  gas_invoke_entry (ctx,func) t callee entered /\
  gas_path ctx callee entered n (IntRet ir cs) /\
  ir.iret_values = [] /\ ir.iret_adopt_fmp = NONE /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  value_has_type tv v /\ type_memory_size tv <= buf.buf_size /\
  eval_operand buf.buf_operand t = SOME w /\
  FLOOKUP t.vs_allocas aid = SOME (w2n w,buf.buf_size) /\
  sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\
  val_in_memory tv v (w2n w) cs.vs_memory /\
  stmt_state_rel ctx func ce cx (es1 with scopes := prev) t /\
  state_rel other ce cx (ee with <|scopes := []; gas_obs := []|>) cs /\
  immutable_alloca_sep func ce cx (ee with scopes := prev) t /\
  wb_frame ce es0 (es1 with scopes := prev) sa s0 t /\
  (!id b sz. local_region ce es0.scopes s0 id b sz ==>
    local_region ce prev t id b sz) /\
  (!id b sz aid off asz.
    local_region ce prev t id b sz /\
    FLOOKUP t.vs_allocas aid = SOME (off,asz) /\
    sa.cs_next_id <= aid /\ aid < sb.cs_next_id ==> regions_disjoint b sz off asz) /\
  (!b sz. b + sz <= t.vs_alloca_next /\
    (!aid off asz. FLOOKUP t.vs_allocas aid = SOME (off,asz) /\
      sa.cs_next_id <= aid /\ aid < sb.cs_next_id ==> regions_disjoint b sz off asz) ==>
    mem_bytes_at b sz cs.vs_memory = mem_bytes_at b sz t.vs_memory) /\
  ef = (ee with <|scopes := prev; gas_obs := []|>) /\
  vv = LocatedValue (expr_type e) (base_ptr buf) ==>
  ?k out. gas_path ctx func t (n + k) (OK out) /\
    vv_post ctx func ce cx e es0 sa sb s0 ef (Value v) vv out /\
    out.vs_current_bb = sb.cs_current_bb /\
    out.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  drule_all intcall_void_compiler_boundary >> strip_tac >>
  `immutable_alloca_sep func ce cx
    (ee with <|scopes := prev; gas_obs := []|>) t` by
    (irule immutable_alloca_sep_fields >> goal_assum (drule_at Any) >>
     simp[] >> metis_tac[]) >>
  drule_all (Q.INST [`es` |-> `es1 with scopes := prev`,
    `ee` |-> `ee with gas_obs := []`] (SPEC_ALL memory_return_endpoint)
    |> SIMP_RULE (srw_ss()) [] |> GEN_ALL) >>
  strip_tac >> qexistsl_tac [`k`,`out`] >> gvs[]
QED

Theorem compiled_stack_return:
  expr_has_effect e /\
  post_value_type ce e = expr_type e /\
  compile_multi_vvs compile_expr ce es sa = (vals,s1) /\
  ci_mono s1 s2 /\
  compile_stage_intcall_args ce vals flags tys s2 = (args,si) /\
  emit_multi_op INVOKE ops nret si = (results,sj) /\
  store_multi_results buf.buf_operand results 0 sj = ((),sb) /\
  fn_has_code sa sb func /\ local_ptrs_reserved ce sa /\
  t.vs_current_bb = si.cs_current_bb /\
  t.vs_inst_idx = LENGTH si.cs_current_insts /\
  gas_invoke_entry (ctx,func) t callee entered /\
  gas_path ctx callee entered n (IntRet ir cs) /\
  ir.iret_adopt_fmp = NONE /\ LENGTH ir.iret_values = nret /\ 0 < nret /\
  compile_alloc_buffer (32 * nret) s1 = (buf,s2) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
  0 < returns_stack_count
    (\name. MAP (FST o SND) (get_struct_fields ce.ce_struct_fields name))
    (expr_type e) /\
  value_has_type tv v /\ intret_vals_match tv v ir.iret_values /\
  eval_operand buf.buf_operand t = SOME (n2w off) /\
  FLOOKUP t.vs_allocas aid = SOME (off,buf.buf_size) /\
  sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\
  (?ai. MEM ai (fn_insts func) /\ ai.inst_opcode = ALLOCA /\ ai.inst_id = aid) /\
  stmt_state_rel ctx func ce cx (es1 with scopes := prev) t /\
  state_rel other ce cx (ee with <|scopes := []; gas_obs := []|>) cs /\
  immutable_alloca_sep func ce cx (ee with scopes := prev) t /\
  wb_frame ce es0 (es1 with scopes := prev) sa s0 t /\
  (!id b sz. local_region ce es0.scopes s0 id b sz ==>
    local_region ce prev t id b sz) /\
  (!id b sz aid off asz.
    local_region ce prev t id b sz /\
    FLOOKUP t.vs_allocas aid = SOME (off,asz) /\
    sa.cs_next_id <= aid /\ aid < sb.cs_next_id ==> regions_disjoint b sz off asz) /\
  (!b sz. b + sz <= t.vs_alloca_next /\
    (!aid off asz. FLOOKUP t.vs_allocas aid = SOME (off,asz) /\
      sa.cs_next_id <= aid /\ aid < sb.cs_next_id ==> regions_disjoint b sz off asz) ==>
    mem_bytes_at b sz cs.vs_memory = mem_bytes_at b sz t.vs_memory) /\
  ef = (ee with <|scopes := prev; gas_obs := []|>) /\
  vv = LocatedValue (expr_type e) (base_ptr buf) ==>
  ?k out. gas_path ctx func t (n + k) (OK out) /\
    vv_post ctx func ce cx e es0 sa sb s0 ef (Value v) vv out /\
    out.vs_current_bb = sb.cs_current_bb /\
    out.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  drule_all intcall_stack_compiler_boundary >> strip_tac >>
  `immutable_alloca_sep func ce cx
    (ee with <|scopes := prev; gas_obs := []|>) t` by
    (irule immutable_alloca_sep_fields >> goal_assum (drule_at Any) >>
     simp[] >> metis_tac[]) >>
  Q.SUBGOAL_THEN
    `?ai. MEM ai (fn_insts func) /\ ai.inst_opcode = ALLOCA /\ ai.inst_id = aid`
    assume_tac >- metis_tac[] >>
  drule_all (Q.INST [`es` |-> `es1 with scopes := prev`,
    `ee` |-> `ee with gas_obs := []`] (SPEC_ALL stack_return_endpoint)
    |> SIMP_RULE (srw_ss()) [] |> GEN_ALL) >>
  strip_tac >> qexistsl_tac [`k`,`out`] >> gvs[]
QED

Theorem compiled_return_dispatch:
  !nret.
  expr_has_effect e /\
  post_value_type ce e = expr_type e /\
  compile_multi_vvs compile_expr ce es sa = (vals,s1) /\
  compile_stage_intcall_args ce vals flags tys s2 = (args,si) /\
  fn_has_code sa sb func /\ local_ptrs_reserved ce sa /\
  ((nret:num) = 0 /\ expr_type e = NoneT ==>
    s2 = s1 /\ (?u. emit_void INVOKE (Label lbl::args) si = (u,sb)) /\
    vv = StackValue (expr_type e) (Lit 0w)) /\
  (0 < nret \/ expr_type e <> NoneT ==>
    ?buf aid off.
      compile_alloc_buffer (if 0 < nret then 32 * nret else rbs) s1 = (buf,s2) /\
      vv = LocatedValue (expr_type e) (base_ptr buf) /\
      eval_operand buf.buf_operand t = SOME (n2w off) /\
      FLOOKUP t.vs_allocas aid = SOME (off,buf.buf_size) /\
      (?ai. MEM ai (fn_insts func) /\ ai.inst_opcode = ALLOCA /\ ai.inst_id = aid) /\
      sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\
      (0 < nret ==>
        ?results sj u. emit_multi_op INVOKE (Label lbl::args) nret si = (results,sj) /\
          store_multi_results buf.buf_operand results 0 sj = (u,sb)) /\
      (nret = 0 ==>
        (?u. emit_void INVOKE (Label lbl::buf.buf_operand::args) si = (u,sb)) /\
        (w:256 word) = n2w off /\ type_memory_size tv <= buf.buf_size)) /\
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
  wb_frame ce es0 (es1 with scopes := prev) sa s0 t /\
  (!id b sz. local_region ce es0.scopes s0 id b sz ==>
    local_region ce prev t id b sz) /\
  (!id b sz aid off asz.
    local_region ce prev t id b sz /\
    FLOOKUP t.vs_allocas aid = SOME (off,asz) /\
    sa.cs_next_id <= aid /\ aid < sb.cs_next_id ==> regions_disjoint b sz off asz) /\
  (!b sz. b + sz <= t.vs_alloca_next /\
    (!aid off asz. FLOOKUP t.vs_allocas aid = SOME (off,asz) /\
      sa.cs_next_id <= aid /\ aid < sb.cs_next_id ==> regions_disjoint b sz off asz) ==>
    mem_bytes_at b sz cs.vs_memory = mem_bytes_at b sz t.vs_memory) /\
  ef = (ee with <|scopes := prev; gas_obs := []|>) ==>
  ?k out. gas_path ctx func t (n + k) (OK out) /\
    vv_post ctx func ce cx e es0 sa sb s0 ef (Value v) vv out /\
    out.vs_current_bb = sb.cs_current_bb /\
    out.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  gen_tac >> strip_tac >> Cases_on `nret = 0`
  >- (`ir.iret_values = []` by (Cases_on `ir.iret_values` >> fs[]) >>
      Cases_on `expr_type e = NoneT`
      >- (qpat_x_assum `_ ==> s2 = s1 /\ _` mp_tac >>
          (impl_tac >- simp[]) >> strip_tac >>
          `ci_mono s1 s2` by fs[ci_mono_refl] >>
          Cases_on `u` >>
          `vv = StackValue NoneT (Lit 0w)` by fs[] >>
          drule_all compiled_void_return >> simp[]) >>
      qpat_x_assum `0 < nret \/ _ ==> _` mp_tac >> simp[] >> strip_tac >>
      `ci_mono s1 s2` by
        (qspecl_then [`rbs`,`s1`] mp_tac ci_mono_compile_alloc_buffer >> simp[]) >>
      `eval_operand buf.buf_operand t = SOME w` by fs[] >>
      `off < dimword (:256)` by
        (qpat_x_assum `stmt_state_rel _ _ _ _ _ _` mp_tac >>
         pure_rewrite_tac [stmt_state_rel_def] >> strip_tac >>
         drule alloca_room_next_lt >>
         fs[alloca_inv_def, alloca_next_valid_def] >>
         qpat_x_assum `!aid base sz. _`
           (qspecl_then [`aid`,`off`,`buf.buf_size`] mp_tac) >>
         simp[] >> decide_tac) >>
      `FLOOKUP t.vs_allocas aid = SOME (w2n w,buf.buf_size)` by fs[] >>
      `val_in_memory tv v (w2n w) cs.vs_memory` by metis_tac[] >>
      drule_all compiled_memory_return >> simp[]) >>
  `0 < nret` by decide_tac >>
  qpat_x_assum `0 < nret \/ _ ==> _` mp_tac >> simp[] >> strip_tac >>
  `ci_mono s1 s2` by
    (qspecl_then [`32 * nret`,`s1`] mp_tac ci_mono_compile_alloc_buffer >> simp[]) >>
  Q.SUBGOAL_THEN
    `?ai. MEM ai (fn_insts func) /\ ai.inst_opcode = ALLOCA /\ ai.inst_id = aid`
    assume_tac >- metis_tac[] >>
  `0 < returns_stack_count
    (\name. MAP (FST o SND) (get_struct_fields ce.ce_struct_fields name))
    (expr_type e)` by metis_tac[] >>
  drule_all compiled_stack_return >> simp[]
QED
