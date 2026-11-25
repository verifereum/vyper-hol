(* The fixed RawLog scratch run reaches the allocator's own first exit. *)
Theory entryCreateRawLogScratch
Ancestors
  bodyFullRawLogFixedAlloc entryCreateAdminSequence entryCreateFocusSpec
Libs pairLib

Theorem create_raw_log_fixed_scratch_scoped:
  expr_type data = BaseT (BytesT (Fixed 32)) /\
  compile_call compile_expr cenv ret_ty ty RawLog [topics;data] dflt call_sa = (vv,call_sb) /\
  compile_alloc_buffer 32 sm = (buf,sd) /\ fn_has_code sm sd func /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sm /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sm x) /\
  (!H. valid_horizon cx st0 H ee.storage_trace ==>
    stmt_state_rel H ctx func cenv cx ee s /\ storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx ee G tn s /\ return_buf_frame d cenv sm s /\
    alloca_history func s /\ ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
    s.vs_inst_idx = LENGTH sm.cs_current_insts) /\
  sd.cs_current_bb = sm.cs_current_bb /\
  sd.cs_current_insts = sm.cs_current_insts ++ emitted_insts sm sd /\
  EVERY (\i. i.inst_id IN frag_ids sm sd /\ i.inst_opcode <> INVOKE /\
    i.inst_opcode <> GAS /\ ~is_terminator i.inst_opcode /\
    ~MEM i.inst_opcode [CREATE;CREATE2]) (emitted_insts sm sd) ==>
  ?u Gu tnu p w. !H. valid_horizon cx st0 H ee.storage_trace ==>
    create_operand_full_scope sm sd explicit ctx func s [] (OK u) /\
    gas_origin_ptr_path (DF H,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK u,Gu,tnu) /\
    stmt_state_rel H ctx func cenv cx ee u /\ storage_well_formed_on cx ee (FST H) /\
    ghost_inv_at (DF H) lo d cenv cx ee Gu tnu u /\
    return_buf_frame d cenv sd u /\ alloca_history func u /\
    s.vs_alloca_next <= u.vs_alloca_next /\ ~u.vs_halted /\
    u.vs_current_bb = sd.cs_current_bb /\ u.vs_inst_idx = LENGTH sd.cs_current_insts /\
    buf.buf_operand = Var p /\ not_fresh_at sd p /\
    eval_operand buf.buf_operand u = SOME w /\ ptr_covers Gu tnu p u 32 /\
    FLOOKUP u.vs_allocas sm.cs_next_id = SOME (w2n w,32) /\
    w2n w + 32 < dimword (:256) /\ u.vs_memory = s.vs_memory /\
    tnu.t_mem = tn.t_mem UNION new_site_bytes s u /\
    (!x. not_fresh_at sm x ==> lookup_var x u = lookup_var x s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==> FLOOKUP u.vs_allocas aid = SOME entry) /\
    (!aid b n. aid < sm.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,n) ==>
      regions_disjoint (w2n w) 32 b n) /\
    (!name b n. local_region cenv ee.scopes u name b n ==> regions_disjoint (w2n w) 32 b n) /\
    ghost_kept_at lo cenv ee sm G tn s Gu tnu
Proof
  strip_tac >> drule_all raw_log_fixed_alloc_run >>
  disch_then (qspecl_then [`explicit`, `PG`] strip_assume_tac) >>
  qexistsl_tac [`u`, `Gu`, `tnu`, `p`, `w`] >>
  gen_tac >> strip_tac >>
  qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
    (drule_then strip_assume_tac) >>
  qpat_x_assum `!H. valid_horizon _ _ H _ ==> (?t. _) /\ _`
    (drule_then strip_assume_tac) >>
  conj_tac
  >- (qpat_x_assum `u = _` SUBST1_TAC >> irule create_admin_sequence_scope >>
      simp[create_operand_at_def] >>
      gvs[listTheory.EVERY_MEM]) >>
  asm_rewrite_tac[]
QED
