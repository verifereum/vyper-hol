Theory bodyPtrIfExpSingleCopyPost
Ancestors bodyPtrIfExpActiveCopyPost bodyPtrIfExpStorageAllocationFrame
  loweringPosts compileEnv venomState finite_map words arithmetic

Theorem ifexp_single_allocated_copy_post:
  vv_post ctx fn ce cx e es sa sb s0 ee raw vv s /\
  read_result cx raw ee = (INL v,ee) /\
  local_ptrs_reserved ce sa /\ MAP FDOM es.scopes = MAP FDOM ee.scopes /\
  sa.cs_next_var <= sb.cs_next_var /\ sa.cs_next_id <= sb.cs_next_id /\
  fn_inst_ids_distinct fn /\
  compile_alloc_buffer 32 sb = (buf,cs) /\ fn_has_code sb cs fn /\
  buf.buf_operand = Var out /\
  step_inst_base (mk_inst sb.cs_next_id ALLOCA [Lit 32w] [out]) s = OK u /\
  eval_operand (Var out) u = SOME d /\ cs.cs_next_id <= sd.cs_next_id /\
  (!x. not_fresh_at cs x ==> x <> tmp) /\
  t = (mstore (w2n d) w (update_var tmp w (u with vs_inst_idx := j))) with vs_inst_idx := k /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME ty /\
  val_wf ty v /\ val_in_memory ty v (w2n d) t.vs_memory /\
  val_footprint ty v <= 32 /\ eval_operand op t = SOME d ==>
  (~is_word_type (expr_type e) ==> expr_post ctx fn ce cx e es sa sd s0 ee v op t)
Proof
  strip_tac >> strip_tac >>
  `copy_static t = copy_static u /\
   (!x. not_fresh_at cs x ==> lookup_var x t = lookup_var x u) /\
   LENGTH u.vs_memory <= LENGTH t.vs_memory /\
   (!off len. off+len <= w2n d \/ w2n d+32 <= off ==>
     mem_bytes_at off len t.vs_memory = mem_bytes_at off len u.vs_memory)` by
    (irule ifexp_single_copy_frame >>
     qexistsl_tac [`j`, `k`, `tmp`, `w`] >> metis_tac[]) >>
  irule ifexp_allocated_copy_post >> simp[] >>
  qexistsl_tac [`buf`, `cs`, `out`, `raw`, `s`, `sb`, `32`, `u`, `vv`] >>
  simp[dimword_def] >>
  gvs[ADD_COMM] >> metis_tac[ADD_COMM]
QED
