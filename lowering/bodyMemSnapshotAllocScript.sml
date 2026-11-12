(* Counted snapshot allocation, retaining the original RHS view. *)
Theory bodyMemSnapshotAlloc
Ancestors
  exprSimIfExp exprSimMemUnwrap bodyMemAssignAttrStorage
  exprSimMemDefs loweringPosts exprLoweringProps exprSimAlloc
  compileEnv context venomState venomInst venomExecSemantics
  fragGasPathMem allocaHistory

Theorem snapshot_alloc_source_mem:
  !ctx func cenv cx e es sa sm mid s0 ee tv vv s sz buf.
    compile_alloc_buffer sz sm = (buf,mid) /\
    fn_has_code sm mid func /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sm /\ sa.cs_next_var <= sm.cs_next_var /\
    sz < dimword (:256) /\
    (!x. vv_operand vv = Var x ==> not_fresh_at sm x) /\
    vv_post ctx func cenv cx e es sa sm s0 ee tv vv s /\
    vv_store_bound cx (expr_type e) (lowered_value_type cenv e) ee tv vv s /\
    alloca_history func s /\ ~s.vs_halted /\
    s.vs_current_bb = sm.cs_current_bb /\
    s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
    ?u w. gas_path_mem ctx func s 0 (OK u) /\
      vv_post ctx func cenv cx e es sa mid s0 ee tv vv u /\
      vv_store_bound cx (expr_type e) (lowered_value_type cenv e) ee tv vv u /\
      eval_operand buf.buf_operand u = SOME w /\
      FLOOKUP u.vs_allocas sm.cs_next_id = SOME (w2n w,sz) /\
      w2n w + sz < dimword (:256) /\ w2n w + sz <= u.vs_alloca_next /\
      u.vs_memory = s.vs_memory /\ sm.cs_next_id < mid.cs_next_id /\
      (!x. not_fresh_at sm x ==> lookup_var x u = lookup_var x s) /\
      (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
         FLOOKUP u.vs_allocas aid = SOME entry) /\
      (!aid b len. aid < sm.cs_next_id /\
         FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
         regions_disjoint (w2n w) sz b len) /\
      (!name b len. local_region cenv ee.scopes u name b len ==>
         regions_disjoint (w2n w) sz b len) /\
      (?p. buf.buf_operand = Var p /\ not_fresh_at mid p) /\
      eval_operand (vv_operand vv) u = eval_operand (vv_operand vv) s /\
      pure_frame cenv func ee sm s u /\
      alloca_history func u /\ s.vs_alloca_next <= u.vs_alloca_next /\
      ~u.vs_halted /\ u.vs_current_bb = mid.cs_current_bb /\
      u.vs_inst_idx = LENGTH mid.cs_current_insts
Proof
  rpt gen_tac >> strip_tac >>
  `stmt_state_rel ctx func cenv cx ee s` by fs[vv_post_def] >>
  `eval_operand (Lit 0w) s = SOME 0w` by simp[eval_operand_def] >>
  `!x. Lit 0w = Var x ==> not_fresh_at sm x` by simp[] >>
  drule_all alloc_buffer_source_path_mem_endpoint >> strip_tac >>
  `eval_operand (vv_operand vv) u = eval_operand (vv_operand vv) s` by
    (Cases_on `vv_operand vv` >> gvs[eval_operand_def]) >>
  drule_all buffer_alloc_code >> strip_tac >>
  drule_all ifexp_alloc_preserves_post >> strip_tac >>
  gvs[] >>
  qexistsl_tac [`q with vs_inst_idx := LENGTH mid.cs_current_insts`, `w`] >>
  `!ctx9 func9 cenv9 cx9 e9 es9 sa9 sb9 s09 ee9 raw9 vv9 s9 n9.
     vv_post ctx9 func9 cenv9 cx9 e9 es9 sa9 sb9 s09 ee9 raw9 vv9
       (s9 with vs_inst_idx := n9) <=>
     vv_post ctx9 func9 cenv9 cx9 e9 es9 sa9 sb9 s09 ee9 raw9 vv9 s9` by
    (rpt gen_tac >>
     `!op. eval_operand op (s9 with vs_inst_idx := n9) = eval_operand op s9` by
       (Cases >> simp[eval_operand_def, lookup_var_def]) >>
     Cases_on `vv9` >>
     simp[vv_post_def, stmt_state_rel_inst_idx, vv_holds_def, vv_at_def,
          vv_own_def, expr_val_rel_def, expr_val_at_def, expr_val_own_def,
          lookup_var_def, loweringStateRelDefsTheory.local_region_def, storage_holds_def,
          immutable_holds_def, venomStateTheory.contract_storage_def,
          venomStateTheory.contract_transient_def]) >>
  simp[] >>
  conj_tac
  >- (irule vv_store_bound_frame_mem_src >> qexists_tac `s` >>
      simp[eval_operand_def, lookup_var_def] >>
      Cases_on `vv_operand vv` >> gvs[eval_operand_def, lookup_var_def]) >>
  gvs[eval_operand_def, lookup_var_def] >> metis_tac[]
QED
