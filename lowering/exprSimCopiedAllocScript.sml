(* The copied-base snapshot reserves its destination before reading its base.
   Keep the base's complete postcondition and its original history across this
   allocation, including when the allocation site has already been executed. *)
Theory exprSimCopiedAlloc
Ancestors
  exprSimIfExpWidenedAdapter exprSimAlloc exprSimVVFrame
  exprLoweringProps loweringPosts freshWrites localPtrsProps
  fragBlockPath fragExec context compileEnv venomState venomInst
  loweringStateRelDefs exprSimProps finite_map list rich_list words

Theorem copied_array_alloc_transport:
  compile_alloc_buffer sz sm = (buf,sn) /\
  fn_has_code sm sn func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ local_ptrs_reserved cenv sm /\
  sa.cs_next_var <= sm.cs_next_var /\ sz < dimword (:256) /\
  vv_post ctx func cenv cx e es sa sm s0 ee tv vv s /\
  eval_operand (vv_operand vv) s = SOME a /\
  (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?u w. fragment_path ctx func s u /\
    u.vs_current_bb = sn.cs_current_bb /\
    u.vs_inst_idx = LENGTH sn.cs_current_insts /\
    vv_post ctx func cenv cx e es sa sn s0 ee tv vv u /\
    eval_operand (vv_operand vv) u = SOME a /\
    eval_operand buf.buf_operand u = SOME w /\
    FLOOKUP u.vs_allocas sm.cs_next_id = SOME (w2n w,sz) /\
    w2n w + sz < dimword (:256) /\ sm.cs_next_id < sn.cs_next_id /\
    (!name b len. local_region cenv ee.scopes u name b len ==>
       regions_disjoint (w2n w) sz b len) /\
    (?p. buf.buf_operand = Var p /\ not_fresh_at sn p)
Proof
  strip_tac >>
  `stmt_state_rel ctx func cenv cx ee s` by fs[vv_post_def] >>
  drule_all buffer_alloc_code >> strip_tac >>
  drule_all literal_alloc_buffer_run >> strip_tac >>
  `contract_storage t = contract_storage s /\
   contract_transient t = contract_transient s` by
    metis_tac[alloc_buffer_storage] >>
  `t.vs_labels = s.vs_labels` by metis_tac[hash_alloc_buffer_labels] >>
  `eval_operand (vv_operand vv) t = eval_operand (vv_operand vv) s` by
    (Cases_on `vv_operand vv` >> gvs[eval_operand_def]) >>
  `!n b k. local_region cenv ee.scopes t n b k <=>
           local_region cenv ee.scopes s n b k` by
    (rpt gen_tac >> eq_tac
     >- (strip_tac >> irule local_region_frame >> conj_tac
         >- (qexists `func` >> fs[stmt_state_rel_def, state_rel_def]) >>
         qexistsl [`sm`, `ee.scopes`, `t`] >> simp[] >> metis_tac[]) >>
     strip_tac >> irule local_region_frame_fwd >>
     qexistsl [`s`, `sm`, `ee.scopes`] >> simp[] >> metis_tac[]) >>
  `vv_post ctx func cenv cx e es sa sn s0 ee tv vv t` by
    (irule vv_post_alloc_mono_frame >> simp[] >>
     qexistsl [`s`, `sm`] >> simp[] >> rpt strip_tac >>
     first_x_assum irule >> irule not_fresh_at_mono >>
     goal_assum (drule_at Any) >> simp[]) >>
  `same_blocks sm sn /\
   sn.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sn /\
   EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sm sn)` by
    (gvs[compile_alloc_buffer_def, emitHelperTheory.emit_op_def,
         comp_bind_def, comp_return_def, comp_ignore_bind_def,
         fresh_id_def, fresh_var_def, emit_def, same_blocks_def,
         emitted_insts_def, DROP_LENGTH_APPEND, mk_inst_def,
         is_terminator_def]) >>
  drule_all fragment_path_emitted >> strip_tac >>
  qexistsl [`t with vs_inst_idx := LENGTH sn.cs_current_insts`, `w`] >>
  simp[] >> rpt strip_tac >>
  qpat_x_assum `!name b len. local_region _ _ t _ _ _ ==> _` irule >>
  qexists `name` >> fs[local_region_def, lookup_var_def]
QED
