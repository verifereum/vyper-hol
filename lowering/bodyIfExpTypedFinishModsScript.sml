(* Interpret the endpoint of the selected arm's typed store. *)
Theory bodyIfExpTypedFinishMods
Ancestors
  bodyFullIfExpWidenCall bodyFullPostsMods exprSimCopy exprSimProps
  exprSimIfExp exprSimDefs bodyPtrDefs typedMemoryCopy loweringPosts loweringStateRelDefs
  exprLowering context vyperAST vyperInterpreter vyperState vyperTypeSystem
  venomState venomInst finite_map compileEnv freshWrites words arithmetic

Theorem ifexp_typed_destination_result[local]:
  evaluate_type (get_tenv cx) t = SOME rty /\ ~is_word_type t /\ val_wf rty v /\
  type_memory_bytes ce t = type_memory_size rty /\
  lookup_var xd f = SOME w /\ FLOOKUP Gf xd = SOME (w2n w,type_memory_size rty) /\
  op_taint tf (Var xd) = {} /\
  (!mem. mem_agree_outside tf.t_mem f.vs_memory mem ==>
    val_in_memory rty v (w2n w) mem) /\
  w2n w + type_memory_size rty <= f.vs_alloca_next /\
  FLOOKUP f.vs_allocas aid = SOME (w2n w,type_memory_size rty) /\
  sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\
  (!n lb len. local_region ce ee.scopes f n lb len ==>
    w2n w + type_memory_size rty <= lb \/ lb + len <= w2n w) ==>
  vv_own ce cx t sa sb ee (Value v) (LocatedValue t (mk_ptr (Var xd) LocMemory)) f /\
  ptr_val_ok cx t v (Var xd) Gf tf f /\
  (!e'. lowered_value_type ce e' = t ==> ptr_buf_ok ce e' (Var xd) Gf f) /\
  (!rt w'. evaluate_type (get_tenv cx) t = SOME rt /\
    eval_operand (Var xd) f = SOME w' ==>
    type_memory_size rt = 0 \/ w2n w' + type_memory_size rt <= f.vs_alloca_next)
Proof
  strip_tac >> conj_tac
  >- (simp[vv_own_def,mk_ptr_def,read_result_def,return_def,eval_operand_def] >>
      disj1_tac >> qexistsl [`aid`,`w2n w`,`type_memory_size rty`] >>
      simp[exprSimPropsTheory.val_footprint_le] >>
      rpt strip_tac >> first_x_assum drule >> decide_tac) >>
  conj_tac
  >- (simp[ptr_val_ok_def,ptr_mem_ok_def,eval_operand_def] >>
      simp[exprSimPropsTheory.val_store_size_le]) >>
  simp[ptr_buf_ok_def,eval_operand_def]
QED

Theorem ifexp_typed_result_at_site_mods:
  compile_ifexp_arm ce t (lowered_value_type ce e) vv sm = (Var xd,sb) /\
  (e = a \/ e = b) /\ expr_type e = t /\
  expr_post_mods H ctx func ce cx e es sa k s0 ee v src q /\
  read_result cx tv ee = (INL v,ee) /\
  evaluate_type (get_tenv cx) t = SOME rty /\ ~is_word_type t /\
  value_has_type rty v /\ val_wf rty v /\
  type_memory_bytes ce t = type_memory_size rty /\
  lookup_var xd q = SOME w /\ not_fresh_at k xd /\
  sa.cs_next_var <= k.cs_next_var /\ local_ptrs_reserved ce k /\
  typed_copy_state_frame k (w2n w) (type_memory_size rty) q f /\
  FLOOKUP q.vs_allocas inst.inst_id = SOME (w2n w,type_memory_size rty) /\
  MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
  sa.cs_next_id <= inst.inst_id /\ inst.inst_id < sb.cs_next_id /\
  w2n w + type_memory_size rty <= q.vs_alloca_next /\
  (!n lb len. local_region ce ee.scopes q n lb len ==>
    w2n w + type_memory_size rty <= lb \/ lb + len <= w2n w) /\
  (!n lb len. local_region ce es.scopes s0 n lb len ==>
    local_region ce ee.scopes q n lb len) /\
  (!old off len. FLOOKUP s0.vs_allocas old = SOME (off,len) /\
    old < sa.cs_next_id ==>
    w2n w + type_memory_size rty <= off \/ off + len <= w2n w) /\
  immutable_frame_mods func ce cx ee f /\
  (!mem. mem_agree_outside tf.t_mem f.vs_memory mem ==>
    val_in_memory rty v (w2n w) mem) /\
  FLOOKUP Ga xd = SOME (w2n w,type_memory_size rty) /\
  op_taint ta (Var xd) = {} /\
  (!p. not_fresh_at k p ==> FLOOKUP Gf p = FLOOKUP Ga p /\
    op_taint tf (Var p) = op_taint ta (Var p)) /\
  ~same_memory_layout ce (lowered_value_type ce e) t /\
  (!id path. tv = PlaceR (MemoryPlace id path) ==>
    same_memory_layout ce (lowered_value_type ce e) t) ==>
  expr_post_mods H ctx func ce cx (IfExp t c a b) es sa sb s0 ee v (Var xd) f /\
  vv_at ce cx t sa sb ee tv (LocatedValue t (mk_ptr (Var xd) LocMemory)) f /\
  (!id path. tv = PlaceR (MemoryPlace id path) ==>
    vv_place_ptr ce cx ee f tv (LocatedValue t (mk_ptr (Var xd) LocMemory))) /\
  (!ctv v'. conditional_result cx tv ee = (INL ctv,ee) /\
    ctv = Value v' /\ ~is_word_type t /\ ~is_bytestring_type t ==>
    vv_own ce cx t sa sb ee ctv (LocatedValue t (mk_ptr (Var xd) LocMemory)) f) /\
  expr_store_bound cx t v (Var xd) f /\
  ptr_val_ok cx t v (Var xd) Gf tf f /\
  (!e'. lowered_value_type ce e' = t ==> ptr_buf_ok ce e' (Var xd) Gf f) /\
  (!rt w'. evaluate_type (get_tenv cx) t = SOME rt /\
    eval_operand (Var xd) f = SOME w' ==>
    type_memory_size rt = 0 \/ w2n w' + type_memory_size rt <= f.vs_alloca_next)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qhdtm_assum `expr_post_mods`
    (strip_assume_tac o REWRITE_RULE [expr_post_mods_def]) >>
  `val_in_memory rty v (w2n w) f.vs_memory` by
    (first_x_assum irule >> simp[mem_agree_outside_def]) >>
  `expr_post H ctx func ce cx (IfExp t c a b) es sa sb s0 ee v (Var xd) f /\
   vv_at ce cx t sa sb ee tv (LocatedValue t (mk_ptr (Var xd) LocMemory)) f /\
   expr_store_bound cx t v (Var xd) f` by
    (irule ifexp_widened_call_copy_semantic_frame >> simp[] >> conj_tac
     >- (qexistsl [`sm`,`lowered_value_type ce e`,`vv`] >> simp[]) >>
     qexistsl [`e`,`inst`,`k`,`q`,`k`,`src`,`w`] >>
     gs[AC ADD_ASSOC ADD_COMM] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `f.vs_allocas = q.vs_allocas /\ f.vs_alloca_next = q.vs_alloca_next` by
    fs[typed_copy_state_frame_def,venom_state_component_equality] >>
  `!x. not_fresh_at k x ==> lookup_var x f = lookup_var x q` by
    fs[typed_copy_state_frame_def] >>
  `lookup_var xd f = SOME w` by simp[] >>
  `FLOOKUP Gf xd = SOME (w2n w,type_memory_size rty) /\ op_taint tf (Var xd) = {}` by
    (qpat_assum `!p. not_fresh_at k p ==> FLOOKUP Gf p = _ /\ _`
       (qspec_then `xd` mp_tac) >> simp[]) >>
  `!n lb len. local_region ce ee.scopes f n lb len ==>
    w2n w + type_memory_size rty <= lb \/ lb + len <= w2n w` by
    (drule_all exprSimCopyTheory.copy_buffer_local_region_frame >>
     disch_then (fn th => pure_rewrite_tac[th]) >> first_assum ACCEPT_TAC) >>
  `FLOOKUP f.vs_allocas inst.inst_id = SOME (w2n w,type_memory_size rty) /\
   w2n w + type_memory_size rty <= f.vs_alloca_next` by simp[] >>
  drule_all_then strip_assume_tac ifexp_typed_destination_result >>
  simp[expr_post_mods_def] >> conj_tac
  >- (rpt strip_tac >> fs[]) >>
  rpt strip_tac >> gvs[] >>
  `expr_vv_res_ok (INL (Value v'))` by simp[expr_vv_res_ok_def] >>
  drule_all_then strip_assume_tac ifexp_arm_conditional_read >>
  gvs[read_result_def,return_def]
QED
