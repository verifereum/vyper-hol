Theory bodyPtrIfExpActiveCopyPost
Ancestors bodyPtrIfExpCopyPost bodyPtrIfExpAllocSource exprSimPrecompiles exprSimOperands
  exprSimAlloc localPtrsProps loweringHalt exprLoweringProps exprSimStorageCopy
  compileEnv venomState venomInst finite_map words arithmetic loweringPosts

(* The allocation endpoint is the actual step result, not an independently
   chosen semantic run.  The copy supplies its ordinary frame at that endpoint. *)
Theorem ifexp_allocated_copy_post:
  post_value_type ce e = expr_type e /\
  vv_post ctx fn ce cx e es sa sb s0 ee raw vv s /\
  read_result cx raw ee = (INL v,ee) /\
  local_ptrs_reserved ce sa /\ MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id /\
  fn_inst_ids_distinct fn /\
  compile_alloc_buffer sz sb = (buf,cs) /\ fn_has_code sb cs fn /\
  buf.buf_operand = Var out /\ sz < dimword (:256) /\
  step_inst_base (mk_inst sb.cs_next_id ALLOCA [Lit (n2w sz)] [out]) s = OK u /\
  eval_operand (Var out) u = SOME d /\
  copy_static t = copy_static u /\
  (!x. not_fresh_at cs x ==> lookup_var x t = lookup_var x u) /\
  LENGTH u.vs_memory <= LENGTH t.vs_memory /\
  (!b len. b+len <= w2n d \/ w2n d+sz <= b ==>
    mem_bytes_at b len t.vs_memory = mem_bytes_at b len u.vs_memory) /\
  cs.cs_next_id <= sd.cs_next_id /\
  ~is_word_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME ty /\
  val_wf ty v /\ val_in_memory ty v (w2n d) t.vs_memory /\
  val_footprint ty v <= sz /\ eval_operand op t = SOME d ==>
  expr_post ctx fn ce cx e es sa sd s0 ee v op t
Proof
  strip_tac >>
  `stmt_state_rel ctx fn ce cx ee s` by fs[vv_post_def] >>
  `local_ptrs_reserved ce sb` by metis_tac[local_ptrs_reserved_next_var] >>
  drule_all compile_alloc_buffer_raw_resources >> strip_tac >>
  drule compile_alloc_buffer_parts >> strip_tac >>
  drule_all buffer_alloc_code >> strip_tac >>
  `FLOOKUP u.vs_allocas sb.cs_next_id = SOME (w2n d,sz)` by metis_tac[] >>
  `!aid b len. aid < sb.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
     regions_disjoint (w2n d) sz b len` by
    (rpt strip_tac >> irule state_allocations_disjoint >>
     qexistsl_tac [`sb.cs_next_id`, `aid`, `ce`, `ctx`, `cx`, `ee`, `fn`, `u`] >>
     simp[] >> metis_tac[]) >>
  `not_local_ptr ce ee.scopes out` by
    (irule fresh_not_local_ptr >> qexists_tac `sb` >> gvs[]) >>
  `!name b len. local_region ce ee.scopes u name b len ==>
     regions_disjoint (w2n d) sz b len` by
    (rpt strip_tac >> irule local_ptrs_rel_alloca_disjoint >>
     qexistsl_tac [`ce`, `fn`,
       `mk_inst sb.cs_next_id ALLOCA [Lit (n2w sz)] [out]`, `name`, `out`, `ee.scopes`, `u`] >>
     gvs[stmt_state_rel_def, state_rel_def, mk_inst_def] >> metis_tac[]) >>
  irule ifexp_copy_buffer_post_transport >>
  simp[] >>
  qexistsl_tac [`mk_inst sb.cs_next_id ALLOCA [Lit (n2w sz)] [out]`,
    `cs`, `raw`, `s`, `sb`, `sz`, `u`, `vv`] >>
  simp[mk_inst_def] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!b len. _ ==> mem_bytes_at _ _ t.vs_memory = _`
    (qspecl_then [`off`, `len`] mp_tac) >> simp[ADD_COMM]
QED
