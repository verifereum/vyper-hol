(* The fixed-byte staging cut and its protected payload across both word reads. *)
Theory bodySliceOrdinaryFixedContinuationMods
Ancestors
  bodySliceOrdinaryFixedLandingMods bodySliceFixedCaptureMods
  bodySliceWordEntryMods exprPtrUnwrapAllocSemantic exprSimOperands
  bodyFullIfExpReach exprOperandVar exprSimAlloc stmtSimLogArgs
  exprSimWordArgs stateRelProj wordArgsPtr bodyFullPostsMods
  vyperStorageFootprint vyperTypeExprSoundness bodyPtrDefs loweringPosts
  vyperValue loweringHalt exprLoweringProps loweringShapeDefs emitHelperProps
  bodyFullHashKeccakFixed loweringStateRelDefs venomState venomInst arithmetic words
Libs horizonTypeLib

val entry = ``\es sa s0 G0 tn0.
  local_ptrs_reserved cenv sa /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  return_buf_frame d cenv sa s0 /\ alloca_history func s0 /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s0) /\
  (!fn inst u. frag_reachable ctx func s0 fn inst u ==> dalloca_fmp_headroom inst u) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func cenv cx es s0 /\ immutable_frame_mods func cenv cx es s0 /\
    storage_well_formed_on cx es (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx es G0 tn0 s0) /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\ s0.vs_inst_idx = LENGTH sa.cs_current_insts``;

val apart = ``\ec t b. !name off sz. local_region cenv ec.scopes t name off sz ==>
    b + 32 <= off \/ off + sz <= b``;
val clean = ``\b (bs:word8 list) tn. !i. b <= i /\ i < b + LENGTH bs ==> i NOTIN tn.t_mem``;

Triviality fixed_stage_clean_step:
  FLOOKUP s.vs_allocas aid = SOME (b,32) /\ aid < sc.cs_next_id /\
  ^apart ec s b /\ LENGTH bs <= 32 /\ ^clean b bs tn /\
  ghost_kept_at lo cenv ec sc G tn s G' tn' /\
  b <= i /\ i < b + LENGTH bs ==> i NOTIN tn'.t_mem
Proof
  BETA_TAC >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `ghost_kept_at _ _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE [ghost_kept_at_def]) >>
  strip_tac >>
  `i < b + 32` by decide_tac >>
  qpat_x_assum `!aid off sz j. FLOOKUP _ _ = _ /\ _ ==> _`
    (qspecl_then [`aid`,`b`,`32`,`i`] assume_tac) >>
  metis_tac[]
QED

Triviality fixed_stage_through_words:
  stmt_state_rel (H:(bool # 256 word # type_value) list # num list) ctx func cenv cx ec scs /\
  local_ptrs_reserved cenv sc /\
  MAP FDOM ec.scopes = MAP FDOM e1.scopes /\
  FLOOKUP scs.vs_allocas aid = SOME (b,32) /\
  aid < sc.cs_next_id /\ aid < sd.cs_next_id /\ LENGTH bs <= 32 /\
  ^apart ec scs b /\ ^clean b bs tc /\
  mem_bytes_at b (LENGTH bs) scs.vs_memory = bs /\
  expr_post_mods H ctx func cenv cx start ec sc sd scs e1 v1 op1 sds /\
  expr_post_mods H ctx func cenv cx len e1 sd se sds e2 v2 op2 ses /\
  ghost_kept_at lo cenv ec sc (Gc:string |-> num # num) tc scs Gd td /\
  ghost_kept_at lo cenv e1 sd Gd td sds Ge te ==>
  mem_bytes_at b (LENGTH bs) ses.vs_memory = bs /\ ^clean b bs te
Proof
  BETA_TAC >> disch_then (map_every assume_tac o CONJUNCTS) >>
  rpt (qhdtm_x_assum `expr_post_mods`
    (strip_assume_tac o REWRITE_RULE [expr_post_mods_def])) >>
  conj_tac
  >- (irule (horizonTypeLib.at_horizon_named "H" slice_ordinary_fixed_landing_mods) >>
      qpat_assum `expr_post _ _ _ _ _ start _ _ _ _ _ _ _ _` (irule_at Any) >>
      qpat_assum `expr_post _ _ _ _ _ len _ _ _ _ _ _ _ _` (irule_at Any) >>
      qexists_tac `aid` >> asm_rewrite_tac[]) >>
  `!i. b <= i /\ i < b + LENGTH bs ==> i NOTIN td.t_mem` by
    (gen_tac >> strip_tac >>
     qpat_assum `ghost_kept_at _ _ _ _ Gc tc _ _ _`
       (mp_then Any mp_tac (BETA_RULE fixed_stage_clean_step)) >>
     disch_then irule >> qexistsl_tac [`aid`,`b`,`bs`] >> asm_rewrite_tac[]) >>
  `FLOOKUP sds.vs_allocas aid = SOME (b,32)` by
    (qpat_assum `expr_post _ _ _ _ _ start _ _ _ _ _ _ _ _`
       (strip_assume_tac o REWRITE_RULE [expr_post_def]) >>
     first_assum (drule_then ACCEPT_TAC)) >>
  `!name off sz. local_region cenv e1.scopes sds name off sz ==>
     b + 32 <= off \/ off + sz <= b` by
    (gen_tac >> gen_tac >> gen_tac >> disch_tac >>
     qpat_assum `expr_post _ _ _ _ _ start _ _ _ _ _ _ _ _`
       (assume_tac o MATCH_MP expr_post_frame) >>
     drule_all_then (fn th => fs[th]) log_frame_local_region >>
     first_assum (drule_then ACCEPT_TAC)) >>
  gen_tac >> strip_tac >>
  qpat_assum `ghost_kept_at _ _ _ _ Gd td _ _ _`
    (mp_then Any mp_tac (BETA_RULE fixed_stage_clean_step)) >>
  disch_then irule >> qexistsl_tac [`aid`,`b`,`bs`] >> asm_rewrite_tac[]
QED

Theorem slice_ordinary_fixed_continuation_mods:
  compile_alloc_buffer 32 sm = (buf,stage) /\
  emit_void MSTORE [buf.buf_operand;op] stage = ((),sc) /\
  fn_has_code sm stage func /\ fn_has_code sm sc func /\ fn_inst_ids_distinct func /\
  ci_mono sm sc /\ local_ptrs_reserved cenv sc /\
  lower_value compile_expr cenv (expr_type src) src sa = (op,sm) /\
  local_ptrs_reserved cenv sa /\
  expr_type src = BaseT (BytesT (Fixed m)) /\
  value_runtime_typed env (expr_type src) v /\
  storage_trace_domain cx st0 ec.storage_trace /\
  (!H. valid_horizon cx st0 H ec.storage_trace ==>
    expr_post_mods H ctx func cenv cx src es sa sm s0 ec v op sms /\
    ptr_val_ok cx (expr_type src) v op Gm tm sms) /\
  ^entry ec sm sms Gm tm /\
  (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) ==>
  ?scs Gc tc root p bs.
    v = BytesV bs /\ LENGTH bs = m /\ m <= 32 /\
    buf.buf_operand = Var root /\ not_fresh_at sc root /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (sms,Gm,tm) [] (OK scs,Gc,tc)) /\
    ^entry ec sc scs Gc tc /\
    eval_operand (Lit (n2w m)) scs = SOME (n2w (LENGTH bs)) /\
    op_taint tc (Lit (n2w m)) = {} /\ op_prov Gc (Lit (n2w m)) = NONE /\
    lookup_var root scs = SOME p /\ ptr_covers Gc tc root scs (LENGTH bs) /\
    w2n p + LENGTH bs < dimword (:256) /\ w2n p + LENGTH bs <= scs.vs_alloca_next /\
    (!x. not_fresh_at sm x ==> lookup_var x scs = lookup_var x sms /\
       FLOOKUP Gc x = FLOOKUP Gm x /\ op_taint tc (Var x) = op_taint tm (Var x)) /\
    sms.vs_alloca_next <= scs.vs_alloca_next /\
    FLOOKUP scs.vs_allocas sm.cs_next_id = SOME (w2n p,32) /\
    (!aid entry. FLOOKUP sms.vs_allocas aid = SOME entry ==>
      FLOOKUP scs.vs_allocas aid = SOME entry) /\
    (!aid b len. aid < sm.cs_next_id /\ FLOOKUP sms.vs_allocas aid = SOME (b,len) ==>
      mem_bytes_at b len scs.vs_memory = mem_bytes_at b len sms.vs_memory) /\
    (!name b len. local_region cenv ec.scopes scs name b len ==>
      mem_bytes_at b len scs.vs_memory = mem_bytes_at b len sms.vs_memory) /\
    (!b len. b+len <= w2n p \/ w2n p+32 <= b ==>
      mem_bytes_at b len scs.vs_memory = mem_bytes_at b len sms.vs_memory) /\
    (!i. i < sms.vs_alloca_next /\ ~(w2n p <= i /\ i < w2n p+32) ==>
      (i IN tc.t_mem <=> i IN tm.t_mem)) /\
    (!H sd se start len e1 e2 v1 v2 op1 op2 sds ses Gd Ge td te.
      valid_horizon cx st0 H ec.storage_trace /\ sc.cs_next_id <= sd.cs_next_id /\
      MAP FDOM ec.scopes = MAP FDOM e1.scopes /\
      expr_post_mods H ctx func cenv cx start ec sc sd scs e1 v1 op1 sds /\
      expr_post_mods H ctx func cenv cx len e1 sd se sds e2 v2 op2 ses /\
      ghost_kept_at lo cenv ec sc Gc tc scs Gd td /\
      ghost_kept_at lo cenv e1 sd Gd td sds Ge te ==>
      mem_bytes_at (w2n p) (LENGTH bs) ses.vs_memory = bs /\ ^clean (w2n p) bs te)
Proof
  BETA_TAC >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `valid_horizon cx st0 (storage_trace_horizon ec.storage_trace) ec.storage_trace` by
    fs[storage_trace_domain_def] >>
  `m <= 32 /\ value_has_type (BaseTV (BytesT (Fixed m))) v` by
    (qpat_assum `value_runtime_typed _ _ _` mp_tac >>
     qpat_assum `expr_type src = _` SUBST1_TAC >>
     Cases_on `m <= 32` >> simp[value_runtime_typed_def,evaluate_type_def]) >>
  pop_assum strip_assume_tac >>
  `evaluate_type (get_tenv cx) (expr_type src) = SOME (BaseTV (BytesT (Fixed m)))` by
    simp[evaluate_type_def] >>
  `!x. op = Var x ==> not_fresh_at sm x` by
    (drule compile_lower_value_var >> simp[]) >>
  `ptr_val_ok cx (expr_type src) v op Gm tm sms` by
    (qpat_assum `!H. valid_horizon _ _ _ _ ==> expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  `!H. valid_horizon cx st0 H ec.storage_trace ==>
    expr_post_mods H ctx func cenv cx src es sa sm s0 ec v op sms /\
    storage_well_formed_on cx ec (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx ec Gm tm sms` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ _ _ ==> expr_post_mods _ _ _ _ _ _ _ _ _ _ _ _ _ _ /\ _`
       (drule_then strip_assume_tac) >>
     qpat_assum `!H. valid_horizon _ _ _ _ ==> stmt_state_rel _ _ _ _ _ _ sms /\ _`
       (drule_then strip_assume_tac) >> asm_rewrite_tac[]) >>
  mp_tac (Q.INST [`e` |-> `src`, `es` |-> `ec`, `es0` |-> `es`,
                 `sb` |-> `stage`, `ce` |-> `cenv`, `s` |-> `sms`,
                 `G` |-> `Gm`, `tn` |-> `tm`, `tv` |-> `BaseTV (BytesT (Fixed m))`]
    slice_fixed_capture_source_mods) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choosel_then [`scs`,`Gc`,`tc`,`root`,`p`,`bs`]
    (map_every assume_tac o CONJUNCTS)) >>
  suspend "separation"
QED

Resume slice_ordinary_fixed_continuation_mods[separation]:
  `MEM (mk_inst sm.cs_next_id ALLOCA [Lit 32w] [root]) (fn_insts func) /\
   ~not_fresh_at sm root /\ sm.cs_next_id < sc.cs_next_id` by
    (drule_then strip_assume_tac compile_alloc_buffer_parts >>
     `root = STRING #"%" (toString sm.cs_next_var)` by metis_tac[operand_11] >>
     qpat_x_assum `root = _` SUBST_ALL_TAC >> asm_rewrite_tac[] >> conj_tac
     >- (drule_all_then ACCEPT_TAC (SIMP_RULE (srw_ss()) [] (Q.SPEC `32` buffer_alloc_code))) >>
     qpat_assum `emit_void MSTORE _ stage = _` (strip_assume_tac o MATCH_MP emitted_insts_emit_void) >>
     simp[]) >>
  `not_local_ptr cenv ec.scopes root` by
    (irule fresh_not_local_ptr >> qexists_tac `sm` >> asm_rewrite_tac[]) >>
  `stmt_state_rel (storage_trace_horizon ec.storage_trace) ctx func cenv cx ec scs` by
    (qpat_assum `!H. valid_horizon _ _ _ _ ==> stmt_state_rel _ _ _ _ _ _ scs /\ _`
       (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  `^apart ec scs (w2n p)` by
    (BETA_TAC >>
     qpat_assum `stmt_state_rel _ _ _ _ _ _ scs`
       (mp_then Any mp_tac (Q.INST [`aid` |-> `sm.cs_next_id`,
         `dst` |-> `w2n p`, `nb` |-> `32`, `n` |-> `32w`] unwrap_alloc_local_disjoint)) >>
     rewrite_tac[regions_disjoint_def] >>
     disch_then (qspecl_then [`sm`,`root`,`p`] mp_tac) >>
     asm_rewrite_tac[]) >>
  suspend "entry"
QED

Resume slice_ordinary_fixed_continuation_mods[entry]:
  `^entry ec sc scs Gc tc` by
    (BETA_TAC >> asm_rewrite_tac[] >> rpt conj_tac
     >- (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sm` >> fs[ci_mono_def])
     >- (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sm` >> fs[ci_mono_def])
     >- (qpat_assum `stmt_state_rel _ _ _ _ _ _ scs`
           (mp_then Any ACCEPT_TAC stmt_state_rel_allocas_below_fmp)) >>
     qpat_assum `!D. gas_origin_ptr_path _ (sms,Gm,tm) [] _`
       (qspec_then `DF (storage_trace_horizon ec.storage_trace)` mp_tac) >>
     disch_then (mp_then Any mp_tac gas_origin_ptr_path_dalloca_fmp_headroom) >>
     asm_rewrite_tac[]) >>
  qexistsl_tac [`scs`,`Gc`,`tc`,`root`,`p`,`bs`] >>
  qpat_assum `^entry ec sc scs Gc tc` (strip_assume_tac o BETA_RULE) >>
  asm_rewrite_tac[] >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  RULE_ASSUM_TAC BETA_RULE >>
  qpat_assum `LENGTH bs = m` (pure_once_rewrite_tac o single o SYM) >>
  `stmt_state_rel H ctx func cenv cx ec scs` by
    (qpat_assum `!H. valid_horizon _ _ _ _ ==> stmt_state_rel _ _ _ _ _ _ scs /\ _`
       (qspec_then `H` (drule_then strip_assume_tac)) >> first_assum ACCEPT_TAC) >>
  `sm.cs_next_id < sd.cs_next_id` by (irule LESS_LESS_EQ_TRANS >> qexists_tac `sc.cs_next_id` >> asm_rewrite_tac[]) >>
  `LENGTH bs <= 32` by asm_rewrite_tac[] >>
  irule (BETA_RULE fixed_stage_through_words) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qpat_assum `expr_post_mods H _ _ _ _ len _ _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `expr_post_mods H _ _ _ _ start _ _ _ _ _ _ _ _` (irule_at Any) >>
  qpat_assum `ghost_kept_at _ _ _ _ Gc tc _ _ _` (irule_at Any) >>
  qpat_assum `ghost_kept_at _ _ _ _ Gd td _ _ _` (irule_at Any) >>
  qexists_tac `sm.cs_next_id` >> asm_rewrite_tac[]
QED

Finalise slice_ordinary_fixed_continuation_mods
