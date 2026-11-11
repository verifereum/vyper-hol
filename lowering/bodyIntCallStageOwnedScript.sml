(* Staged arguments own their physical buffers at one actual endpoint. *)
Theory bodyIntCallStageOwned
Ancestors
  bodyIntCallStageUnwrap bodyIntCallValueWindow actualAllocExec
  exprSimOperands localPtrsProps exprSimProps loweringHalt venomInst

Definition staged_arg_def:
  staged_arg ce func es a sm s (ty: type, tv, v, byval, op) <=>
    value_has_type tv v /\ val_wf tv v /\
    (!x. op = Var x ==> not_fresh_at sm x) /\
    ?w. eval_operand op s = SOME w /\
      (if byval then w = typed_val_to_w256 tv v else
       val_in_memory tv v (w2n w) s.vs_memory /\
       ?aid off sz.
         FLOOKUP s.vs_allocas aid = SOME (off,sz) /\
         (?inst. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
                 inst.inst_id = aid) /\
         a.cs_next_id <= aid /\ aid < sm.cs_next_id /\
         off <= w2n w /\ w2n w + type_memory_size tv <= off + sz /\
         (!n b lsz. local_region ce es.scopes s n b lsz ==>
                    regions_disjoint off sz b lsz))
End

(* The instruction witness includes the compiler's actual fresh output. *)
Theorem staged_buffer_local_disjoint:
  compile_alloc_buffer n sa = (buf,sb) /\ fn_has_code sa sb func /\
  local_ptrs_reserved ce sa /\ stmt_state_rel ctx func ce cx es s /\
  fn_inst_ids_distinct func /\
  FLOOKUP s.vs_allocas sa.cs_next_id = SOME (b,n) ==>
  !name lo sz. local_region ce es.scopes s name lo sz ==>
    regions_disjoint b n lo sz
Proof
  strip_tac >>
  `alloca_inv s /\ local_ptrs_rel func ce es.scopes s` by
    gvs[exprLoweringPropsTheory.stmt_state_rel_def,
        compileEnvTheory.state_rel_def] >>
  drule_all actual_alloc_buffer_site >> strip_tac >>
  drule compile_alloc_buffer_parts >> strip_tac >> rpt strip_tac >>
  irule local_ptrs_rel_alloca_disjoint >>
  goal_assum (drule_at Any) >> simp[] >>
  qexists_tac `func` >> qexists_tac `mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)]
       [STRING #"%" (toString sa.cs_next_var)]` >>
  simp[mk_inst_def] >>
  metis_tac[fresh_not_local_ptr]
QED

Theorem intcall_stage_memory_owned:
  unwrap_value ce vv sa = (op,sm) /\ vv_type vv = ty /\
  compile_alloc_buffer (MAX 32 (type_memory_bytes ce ty)) sm = (buf,si) /\
  compile_store_memory ce op buf.buf_operand ty ty si = ((),sn) /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  type_memory_bytes ce ty = type_memory_size tv /\
  type_memory_bytes ce ty < dimword(:256) /\
  (!aid. sa.cs_next_id <= aid ==> aid NOTIN FDOM s.vs_allocas) /\
  stmt_state_rel ctx func ce cx es s /\ fn_inst_ids_distinct func /\
  fn_has_code sa sm func /\ fn_has_code sm si func /\ fn_has_code si sn func /\
  local_ptrs_reserved ce sa /\ expr_sim_inv ce cx env es /\
  fn_directly_calls ctx func.fn_name name /\ MEM func ctx.ctx_functions /\
  intcall_held_args ce cx a sa es s ((ty,raw,vv)::H) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?v w t inst lb.
    gas_marked_path F ctx func s 0 (OK t) /\
    read_result cx raw es = (INL v,es) /\
    staged_arg ce func es sa sn t (ty,tv,v,F,buf.buf_operand) /\
    value_has_type tv v /\ val_wf tv v /\
    eval_operand buf.buf_operand t = SOME w /\ w2n w = lb /\
    val_in_memory tv v lb t.vs_memory /\
    stmt_state_rel ctx func ce cx es t /\
    intcall_held_args ce cx a sn es t H /\ wb_frame ce es sa s t /\
    ~t.vs_halted /\ t.vs_current_bb = sn.cs_current_bb /\
    t.vs_inst_idx = LENGTH sn.cs_current_insts /\
    local_ptrs_reserved ce sn /\
    (!x. buf.buf_operand = Var x ==> not_fresh_at sn x) /\
    (!x q. not_fresh_at sa x /\ lookup_var x s = SOME q ==> lookup_var x t = SOME q) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP t.vs_allocas aid = SOME entry) /\
    (!aid. sn.cs_next_id <= aid /\ aid NOTIN FDOM s.vs_allocas ==>
      aid NOTIN FDOM t.vs_allocas) /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id = sm.cs_next_id /\
    sa.cs_next_id <= sm.cs_next_id /\ sm.cs_next_id < sn.cs_next_id /\
    FLOOKUP t.vs_allocas sm.cs_next_id =
      SOME (lb,MAX 32 (type_memory_bytes ce ty)) /\
    type_memory_size tv <= MAX 32 (type_memory_bytes ce ty) /\
    (!aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) ==>
      regions_disjoint lb (MAX 32 (type_memory_bytes ce ty)) b sz)
Proof
  strip_tac >> drule_all intcall_stage_memory_head >> strip_tac >>
  `local_ptrs_reserved ce sm` by
    (irule exprLoweringPropsTheory.local_ptrs_reserved_next_var >>
     qexists_tac `sa` >> simp[] >>
     mp_tac (Q.SPECL [`ce`,`vv`,`sa`]
       exprLoweringPropsTheory.ci_mono_unwrap_value) >>
     simp[exprLoweringPropsTheory.ci_mono_def]) >>
  `!n b lsz. local_region ce es.scopes t n b lsz ==>
      regions_disjoint lb (MAX 32 (type_memory_bytes ce ty)) b lsz` by
    metis_tac[staged_buffer_local_disjoint] >>
  qexistsl_tac [`v`,`w`,`t`,`inst`,`lb`] >> simp[] >>
  simp[staged_arg_def] >> reverse conj_tac >- metis_tac[] >>
  qexistsl_tac [`sm.cs_next_id`,`lb`,`MAX 32 (type_memory_bytes ce ty)`] >>
  gvs[] >> metis_tac[]
QED

Theorem intcall_stage_word_owned:
  unwrap_value ce vv sa = (op,sn) /\ vv_type vv = ty /\ is_word_type ty /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  type_memory_bytes ce ty < dimword(:256) /\
  sa.cs_next_id NOTIN FDOM s.vs_allocas /\
  stmt_state_rel ctx func ce cx es s /\ fn_inst_ids_distinct func /\
  fn_has_code sa sn func /\ local_ptrs_reserved ce sa /\
  expr_sim_inv ce cx env es /\ fn_directly_calls ctx func.fn_name name /\
  MEM func ctx.ctx_functions /\
  intcall_held_args ce cx a sa es s ((ty,raw,vv)::H) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?v w z. gas_marked_path F ctx func s 0 (OK z) /\
    read_result cx raw es = (INL v,es) /\ eval_operand op z = SOME w /\
    staged_arg ce func es sa sn z (ty,tv,v,T,op) /\
    value_has_type tv v /\ val_wf tv v /\ w = typed_val_to_w256 tv v /\
    stmt_state_rel ctx func ce cx es z /\ local_ptrs_reserved ce sn /\
    intcall_held_args ce cx a sn es z H /\ wb_frame ce es sa s z /\
    ~z.vs_halted /\ z.vs_current_bb = sn.cs_current_bb /\
    z.vs_inst_idx = LENGTH sn.cs_current_insts /\
    (!x q. not_fresh_at sa x /\ lookup_var x s = SOME q ==> lookup_var x z = SOME q) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP z.vs_allocas aid = SOME entry) /\
    (!aid. sn.cs_next_id <= aid /\ aid NOTIN FDOM s.vs_allocas ==>
      aid NOTIN FDOM z.vs_allocas)
Proof
  strip_tac >> drule_all intcall_stage_unwrap >> strip_tac >>
  `!x. vv_operand vv = Var x ==> not_fresh_at sa x` by
    gvs[bodyIntCallHeldArgsTheory.intcall_held_args_def] >>
  drule_all intcall_stage_unwrap_compiler >> strip_tac >>
  qexistsl_tac [`v`,`w`,`z`] >> simp[staged_arg_def] >> gvs[]
QED
