(* Package either return branch's decoded value in its actual result allocation. *)
Theory extcallReturnPostMemory
Ancestors
  exprSimAbiDecodeValueFrame exprSimIfExpWidenedProvenance exprSimHash
  exprSimMemDefs valueTypingMemoryProps valueEncodingProps loweringPosts
  loweringStateRelDefs exprLoweringProps exprSimProps compileEnv venomState
  context vyperState words arithmetic

Theorem extcall_return_allocated_post:
  expr_type e = rt /\ post_value_type ce e = rt /\ expr_has_effect e /\
  evaluate_type (get_tenv cx) rt = SOME tv /\ value_has_type tv v /\
  val_in_memory tv v d t.vs_memory /\
  eval_operand out t = SOME (n2w d) /\ d < dimword (:256) /\
  FLOOKUP t.vs_allocas aid = SOME (b,sz) /\
  sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\
  b <= d /\ d + type_memory_size tv <= b + sz /\
  b + sz <= t.vs_alloca_next /\
  (!n lb len. local_region ce ee.scopes t n lb len ==>
    b + sz <= lb \/ lb + len <= b) /\
  stmt_state_rel ctx func ce cx ee t /\ wb_frame ce es ee sa s0 t ==>
  vv_post ctx func ce cx e es sa sb s0 ee (Value v)
    (LocatedValue rt (mk_ptr out LocMemory)) t /\
  vv_store_bound cx rt rt ee (Value v)
    (LocatedValue rt (mk_ptr out LocMemory)) t
Proof
  strip_tac >>
  `val_wf tv v` by metis_tac[value_has_type_memory_wf] >>
  `val_footprint tv v <= type_memory_size tv` by
    metis_tac[val_footprint_le] >>
  `d + val_footprint tv v <= b + sz` by decide_tac >>
  `vv_holds ce cx rt (Value v) (LocatedValue rt (mk_ptr out LocMemory)) ee t` by
    (irule abi_decode_memory_vv_holds >> metis_tac[]) >>
  `vv_at ce cx rt sa sb ee (Value v)
     (LocatedValue rt (mk_ptr out LocMemory)) t` by
    (irule allocated_vv_at >>
     qexistsl_tac [`sz`, `aid`, `b`, `tv`, `v`, `n2w d`] >>
     simp[vyperStateTheory.read_result_def, vyperStateTheory.return_def,
       w2n_n2w] >> first_assum ACCEPT_TAC) >>
  `vv_post ctx func ce cx e es sa sb s0 ee (Value v)
     (LocatedValue rt (mk_ptr out LocMemory)) t` by
    (irule vv_post_frame_intro >> simp[]) >>
  simp[vv_store_bound_def, mk_ptr_def, vyperStateTheory.read_result_def,
    vyperStateTheory.return_def] >> rpt strip_tac >> gvs[w2n_n2w] >>
  imp_res_tac val_store_size_le >> decide_tac
QED
