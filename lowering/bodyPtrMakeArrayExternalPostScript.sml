(* Reuse the semantic copy boundary on the caller's captured read result. *)
Theory bodyPtrMakeArrayExternalPost
Ancestors
  exprSimCopy exprSimUnwrapProps loweringPosts context compileEnv
  finite_map list

Theorem copy_buffer_read_post_transport:
  post_value_type cenv e = expr_type e /\
  vv_post ctx func cenv cx e es sa sm s0 es' raw vv s /\
  read_result cx raw es' = (INL v,es') /\
  local_ptrs_reserved cenv sa /\
  MAP FDOM es.scopes = MAP FDOM es'.scopes /\
  sa.cs_next_var <= sm.cs_next_var /\ sm.cs_next_var <= mid.cs_next_var /\
  sa.cs_next_id <= sm.cs_next_id /\ sm.cs_next_id < sb.cs_next_id /\
  stmt_state_rel ctx func cenv cx es' u /\
  u.vs_memory = s.vs_memory /\
  (!x. not_fresh_at sm x ==> lookup_var x u = lookup_var x s) /\
  (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
     FLOOKUP u.vs_allocas aid = SOME entry) /\
  (!aid b len. aid < sm.cs_next_id /\
     FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
     regions_disjoint (w2n w) sz b len) /\
  (!name b len. local_region cenv es'.scopes u name b len ==>
     regions_disjoint (w2n w) sz b len) /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  inst.inst_id = sm.cs_next_id /\
  FLOOKUP u.vs_allocas sm.cs_next_id = SOME (w2n w,sz) /\
  copy_static z = copy_static u /\
  (!x. not_fresh_at mid x ==> lookup_var x z = lookup_var x u) /\
  LENGTH u.vs_memory <= LENGTH z.vs_memory /\
  (!off len. off + len <= w2n w \/ w2n w + sz <= off ==>
     mem_bytes_at off len z.vs_memory = mem_bytes_at off len u.vs_memory) /\
  ~is_word_type (expr_type e) /\
  evaluate_type (get_tenv cx) (expr_type e) = SOME tv /\
  val_wf tv v /\ val_in_memory tv v (w2n w) z.vs_memory /\
  val_footprint tv v <= sz /\ eval_operand op z = SOME w ==>
  expr_post ctx func cenv cx e es sa sb s0 es' v op z
Proof
  strip_tac >>
  `vv_post ctx func cenv cx e es sa sm s0 es' (Value v) vv s` by
    metis_tac[vv_post_read_result] >>
  drule_all copy_buffer_post_transport >> simp[]
QED
