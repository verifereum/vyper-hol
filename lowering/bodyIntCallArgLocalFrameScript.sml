(* Re-read an earlier local subvalue at the actual later expression endpoint.
   The final local relation restores dynamic headers as well as payloads. *)
Theory bodyIntCallArgLocalFrame
Ancestors
  bodyIntCallLocalFrame exprLoweringProps loweringPosts compileEnv

Theorem vv_post_local_sub_layout_value:
  vv_post ctx func cenv cx e es sm sn s0 ee raw vv s /\
  ee.scopes = es.scopes /\
  lookup_scopes n es.scopes = SOME entry /\
  FLOOKUP cenv.ce_vars n = SOME (PtrVar (Var p) sz) /\
  not_fresh_at sm p /\ lookup_var p s0 = SOME w /\
  sub_layout entry.type entry.value k tv v ==>
  val_in_memory tv v (w2n w + k) s.vs_memory
Proof
  strip_tac >> irule local_ptrs_rel_sub_layout >>
  gvs[vv_post_def, stmt_state_rel_def, state_rel_def] >>
  metis_tac[]
QED
