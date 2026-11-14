Theory assignEffectfulIndexAllocUnwrap
Ancestors
  exprSimIfExpWidenedAdapter exprSimAlloc exprSimConcatResult
  stmtSimDefs exprSimCopy
  exprLoweringProps exprLowering context compileEnv fragGasMode
  venomState venomInst venomExecSemantics loweringPosts
  exprSimVVFrame freshWrites loweringStateRelDefs
  exprSafeOperand valueEncoding

(* Allocation transports the original post; the physical retag is used only
   by the subsequent unwrap, not to change that post's semantic type. *)
Theorem assign_effectful_alloc_post[local]:
  compile_alloc_buffer sz sm = (buf,sn) /\
  fn_has_code sm sn func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sm /\ sz < dimword (:256) /\
  vv_post ctx func ce cx e es sa sm s0 ee tv vv s /\
  sa.cs_next_var <= sm.cs_next_var /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?u x b.
    buf.buf_operand = Var x /\ not_fresh_at sn x /\
    sm.cs_next_id < sn.cs_next_id /\
    gas_marked_path F ctx func s 0 (OK u) /\
    vv_post ctx func ce cx e es sa sn s0 ee tv vv u /\
    stmt_state_rel ctx func ce cx ee u /\
    lookup_var x u = SOME (n2w b) /\
    FLOOKUP u.vs_allocas sm.cs_next_id = SOME (b,sz) /\
    b + sz < dimword (:256) /\
    (!name p n. local_region ce ee.scopes u name p n ==>
      regions_disjoint b sz p n) /\
    (!z. not_fresh_at sm z ==> lookup_var z u = lookup_var z s) /\
    (!aid a. FLOOKUP s.vs_allocas aid = SOME a ==>
      FLOOKUP u.vs_allocas aid = SOME a) /\
    alloca_frame ce ee sm s ce ee u /\
    ~u.vs_halted /\ u.vs_current_bb = sn.cs_current_bb /\
    u.vs_inst_idx = LENGTH sn.cs_current_insts
Proof
  strip_tac >>
  `stmt_state_rel ctx func ce cx ee s` by fs[vv_post_def] >>
  drule_all buffer_alloc_code >> strip_tac >>
  drule_all literal_alloc_buffer_run >> strip_tac >>
  `contract_storage t = contract_storage s /\
   contract_transient t = contract_transient s` by
    metis_tac[alloc_buffer_storage] >>
  `!name p n. local_region ce ee.scopes t name p n <=>
               local_region ce ee.scopes s name p n` by
    (rpt gen_tac >> irule copy_buffer_local_region_frame >>
     qexists_tac `sm` >> simp[]) >>
  `t.vs_labels = s.vs_labels` by metis_tac[hash_alloc_buffer_labels] >>
  `eval_operand (vv_operand vv) t = eval_operand (vv_operand vv) s` by
    (Cases_on `vv_operand vv` >> gvs[eval_operand_def]) >>
  `sm.cs_next_id <= sn.cs_next_id` by decide_tac >>
  `vv_post ctx func ce cx e es sa sn s0 ee tv vv t` by
    (irule vv_post_alloc_mono_frame >> simp[] >> qexistsl_tac [`s`,`sm`] >> simp[] >>
     rpt strip_tac >> first_x_assum irule >>
     irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  `sn.cs_current_bb = sm.cs_current_bb /\
   sn.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sn /\
   EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sm sn) /\
   FILTER (\i. i.inst_opcode = GAS) (emitted_insts sm sn) = []` by
    (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     simp[compile_alloc_buffer_def, comp_bind_def, comp_return_def] >>
     pairarg_tac >> strip_tac >> gvs[] >>
     drule emitHelperPropsTheory.emitted_insts_emit_op >>
     simp[mk_inst_def, is_terminator_def] >>
     gvs[emitHelperTheory.emit_op_def, comp_bind_def, comp_return_def,
         comp_ignore_bind_def, fresh_var_def, fresh_id_def, emit_def]) >>
  drule_all concat_straight_gas_path >> strip_tac >>
  qexistsl_tac [`t with vs_inst_idx := LENGTH sn.cs_current_insts`,
                `p`, `w2n w`] >>
  gvs[gas_marked_path_def, vv_post_inst_idx, stmt_state_rel_inst_idx,
      eval_operand_def, lookup_var_def, wordsTheory.n2w_w2n,
      alloca_frame_def, local_region_def] >>
  metis_tac[]
QED

(* The unwrap frame is relative to sn: the allocation created at sm is now
   old.  An sa- or sm-relative frame would not justify this handoff. *)
Theorem assign_effectful_alloc_unwrap_path:
  compile_alloc_buffer sz sm = (buf,sn) /\
  unwrap_value ce (vv_with_type pty vv) sn = (op,sk) /\
  fn_has_code sm sn func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sm /\ sz < dimword (:256) /\
  vv_post ctx func ce cx e es sa sm s0 ee tv vv s /\
  sa.cs_next_var <= sm.cs_next_var /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  (!u. vv_post ctx func ce cx e es sa sn s0 ee tv vv u /\
       ~u.vs_halted /\ u.vs_current_bb = sn.cs_current_bb /\
       u.vs_inst_idx = LENGTH sn.cs_current_insts ==>
    ?t vty a.
      evaluate_type (get_tenv cx) pty = SOME vty /\
      value_has_type vty v /\ val_wf vty v /\
      gas_marked_path F ctx func u 0 (OK t) /\
      stmt_state_rel ctx func ce cx ee t /\
      eval_operand op t = SOME a /\ safe_operand sk op /\
      val_in_memory vty v (w2n a) t.vs_memory /\
      (!z. not_fresh_at sn z ==> lookup_var z t = lookup_var z u) /\
      (!aid entry. FLOOKUP u.vs_allocas aid = SOME entry ==>
        FLOOKUP t.vs_allocas aid = SOME entry) /\
      alloca_frame ce ee sn u ce ee t /\
      ~t.vs_halted /\ t.vs_current_bb = sk.cs_current_bb /\
      t.vs_inst_idx = LENGTH sk.cs_current_insts) ==>
  ?t vty a x b.
    evaluate_type (get_tenv cx) pty = SOME vty /\
    value_has_type vty v /\ val_wf vty v /\
    gas_marked_path F ctx func s 0 (OK t) /\
    stmt_state_rel ctx func ce cx ee t /\
    eval_operand op t = SOME a /\ safe_operand sk op /\
    val_in_memory vty v (w2n a) t.vs_memory /\
    buf.buf_operand = Var x /\ not_fresh_at sn x /\
    sm.cs_next_id < sn.cs_next_id /\
    lookup_var x t = SOME (n2w b) /\
    FLOOKUP t.vs_allocas sm.cs_next_id = SOME (b,sz) /\
    b + sz < dimword (:256) /\
    (!name p n. local_region ce ee.scopes t name p n ==>
      regions_disjoint b sz p n) /\
    (!z. not_fresh_at sm z ==> lookup_var z t = lookup_var z s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP t.vs_allocas aid = SOME entry) /\
    alloca_frame ce ee sm s ce ee t /\
    ~t.vs_halted /\ t.vs_current_bb = sk.cs_current_bb /\
    t.vs_inst_idx = LENGTH sk.cs_current_insts
Proof
  strip_tac >>
  drule_all assign_effectful_alloc_post >> strip_tac >>
  first_x_assum drule >> simp[] >> strip_tac >>
  `sm.cs_next_var <= sn.cs_next_var` by
    (qspec_then `sz` (qspec_then `sm` mp_tac) ci_mono_compile_alloc_buffer >>
     simp[ci_mono_def]) >>
  `!z. not_fresh_at sm z ==> not_fresh_at sn z` by
    metis_tac[not_fresh_at_mono] >>
  `alloca_frame ce ee sm s ce ee t` by
    (irule alloca_frame_trans >> qexistsl_tac [`ce`,`ee`,`u`,`sn`] >>
     simp[] >> decide_tac) >>
  `!name p n. local_region ce ee.scopes t name p n ==>
     regions_disjoint b sz p n` by
    (qpat_x_assum `alloca_frame ce ee sn u ce ee t` mp_tac >>
     simp[alloca_frame_def] >> strip_tac >>
     first_x_assum (qspecl_then [`sm.cs_next_id`,`b`,`sz`] mp_tac) >>
     fs[regions_disjoint_def] >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  `gas_marked_path F ctx func s 0 (OK t)` by
    (drule_all gas_marked_path_then >> simp[]) >>
  qexistsl_tac [`t`,`vty`,`a`,`b`] >> simp[] >>
  metis_tac[]
QED
