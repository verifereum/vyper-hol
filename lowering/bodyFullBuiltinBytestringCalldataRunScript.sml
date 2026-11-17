(* One successful calldata suffix, with its physical and ghost endpoint shared. *)
Theory bodyFullBuiltinBytestringCalldataRun
Ancestors
  bodyFullBuiltinBytestringCalldataPrefix bodyFullBuiltinBytestringOutBuffer
  bodyFullBuiltinBytestringCopy bodyPtrBytestringBuiltinsCalldataFrame
  bodyPtrBytestringBuiltinsExternalSlice
  bodyPtrBytestringBuiltinsBuffer bodyPtrBytestringBuiltinsBounds
  exprSimCalldataSlice exprSimProps exprLoweringProps bodyPtrDefs
  fragGasOriginPtr fragExec emitHelper emitHelperProps freshWrites
  compileEnv loweringStateRelDefs localPtrsProps ptrDiscipline allocaHistory
  venomExecSemantics venomState venomInst context words list finite_map
  loweringPosts valueEncodingProofs instMemFrontier pred_set vyperTypeInvariants instIdxIndep
  bodyMemoryDefs
  codegenRel bodyPtrBytestringBuiltinsSliceEndpoint exprSimAlloc

(* Instantiate the closed provider before its existential witnesses enter scope. *)
fun calldata_horizons initial target provider =
  let
    val post = fst (dest_forall (find_term (fn tm => is_forall tm andalso
      fst (dest_var (fst (dest_forall tm))) = "H'") (concl provider)))
    val formal = first (fn v => (fst (dest_var v) = "H" orelse fst (dest_var v) = "H0")) (free_vars (concl provider))
    val tys = match_type (type_of (pairSyntax.mk_pair (formal,post)))
      (type_of (pairSyntax.mk_pair (initial,target)))
  in INST [inst tys formal |-> initial] (INST_TYPE tys provider) end;

Theorem bytestring_calldata_full_run_resources:
  compile_slice_calldata start (Lit (n2w n)) N sa = (out,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  stmt_state_rel H0 ctx func cenv cx es s /\ context_well_typed cx /\
  0 < n /\ n < dimword (:256) /\ a < dimword (:256) /\
  32+n <= N /\ N < dimword (:256) /\
  eval_operand start s = SOME (n2w a) /\
  op_prov G start = NONE /\ op_taint tn start = {} /\
  (!x. start = Var x ==> not_fresh_at sa x) /\
  a+n < dimword (:256) /\ a+n <= LENGTH cx.txn.calldata /\
  alloca_history func s /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?p w t HG tm.
    out = Var p /\ not_fresh_at sb p /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,HG,tm)) /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~t.vs_halted /\
    lookup_var p t = SOME w /\ ptr_covers HG tm p t N /\
    FLOOKUP t.vs_allocas (sa.cs_next_id+7) = SOME (w2n w,N) /\
    w2n w+N < dimword (:256) /\ w2n w+N <= t.vs_alloca_next /\
    val_in_memory (BaseTV (BytesT (Dynamic n)))
      (BytesV (TAKE n (DROP a cx.txn.calldata))) (w2n w) t.vs_memory /\
    (!i. w2n w <= i /\ i < w2n w+32+n ==> i NOTIN tm.t_mem) /\
    (!H'. stmt_state_rel H' ctx func cenv cx es s ==>
       stmt_state_rel H' ctx func cenv cx es t) /\
    alloca_history func t /\ allocas_from lo t /\ lo <= t.vs_alloca_next /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP HG x = FLOOKUP G x /\
      op_taint tm (Var x) = op_taint tn (Var x)) /\
    (!aid e. FLOOKUP s.vs_allocas aid = SOME e ==>
      FLOOKUP t.vs_allocas aid = SOME e) /\
    (!aid b len. FLOOKUP s.vs_allocas aid = SOME (b,len) /\
      aid < sa.cs_next_id ==>
      mem_bytes_at b len t.vs_memory = mem_bytes_at b len s.vs_memory) /\
    (!name b len. local_region cenv es.scopes s name b len ==>
      mem_bytes_at b len t.vs_memory = mem_bytes_at b len s.vs_memory /\
      (!i. b <= i /\ i < b+len /\ i IN tm.t_mem ==> i IN tn.t_mem)) /\
    mem_bytes_at 0 lo t.vs_memory = mem_bytes_at 0 lo s.vs_memory /\
    tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    ghost_kept_at lo cenv es sa G tn s HG tm /\
    locals_kept cenv es es s t /\ pure_frame cenv func es sa s t /\
    t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
    t.vs_call_ctx = s.vs_call_ctx /\ t.vs_immutables = s.vs_immutables /\
    s.vs_alloca_next <= t.vs_alloca_next
Proof
  strip_tac >> drule compile_slice_calldata_stages >> strip_tac >>
  `fn_has_code sa s2 func /\ fn_has_code s2 s3 func /\
   fn_has_code s3 s4 func /\ fn_has_code s4 sb func /\
   fn_has_code s2 sb func` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  `s.vs_call_ctx.cc_calldata = cx.txn.calldata` by
    fs[stmt_state_rel_def, state_rel_def, call_ctx_rel_def] >>
  `LENGTH s.vs_call_ctx.cc_calldata < dimword (:256)` by
    fs[context_well_typed_def, dimword_def] >>
  (fn (asl,w) => qpat_assum `stmt_state_rel H0 ctx func cenv cx es s`
    (fn th => mp_tac (Q.INST [`sb` |-> `s2`,`sm` |-> `s1`]
      (calldata_horizons (hd (snd (strip_comb (concl th))))
        (hd (snd (strip_comb (concl th)))) bytestring_calldata_prefix_full_run))) (asl,w)) >>
  impl_tac >- simp[] >>
  disch_then (qx_choose_then `u` (qx_choose_then `G1`
    (qx_choose_then `tn1` strip_assume_tac))) >>
  `stmt_state_rel H0 ctx func cenv cx es u` by
    (qpat_assum `!H'. _ ==> stmt_state_rel _ _ _ _ _ _ u`
      (qspec_then `H0` match_mp_tac) >> simp[]) >>
  `allocas_from lo u /\ lo <= u.vs_alloca_next` by
    (qpat_assum `u = s with <|vs_vars := _; vs_inst_idx := _|>` SUBST1_TAC >>
     simp[allocas_from_def] >> qpat_assum `allocas_from lo s`
       (ACCEPT_TAC o REWRITE_RULE[allocas_from_def])) >>
  `sa.cs_next_var <= s2.cs_next_var /\ sa.cs_next_id <= s2.cs_next_id /\
   s2.cs_next_id = sa.cs_next_id+7` by
    (qpat_assum `emit_op CALLDATASIZE [] sa = _`
       (mp_then Any strip_assume_tac emitted_insts_emit_op) >>
     drule compile_assert_slice_bounds_layout >> simp[]) >>
  `local_ptrs_reserved cenv s2` by
    (fs[local_ptrs_reserved_def] >> rpt strip_tac >>
     metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  `u.vs_labels = s.vs_labels` by
    (qpat_assum `u = s with <|vs_vars := _; vs_inst_idx := _|>`
      (mp_tac o Q.AP_TERM `\st. st.vs_labels`) >> simp[]) >>
  qpat_assum `u = s with <|vs_vars := _; vs_inst_idx := _|>`
    (assume_tac o SIMP_RULE (srw_ss()) [] o
      Q.AP_TERM `\st. st.vs_call_ctx.cc_calldata`) >>
  `eval_operand start u = SOME (n2w a) /\
   op_prov G1 start = NONE /\ op_taint tn1 start = {}` by
    (Cases_on `start` >> gvs[eval_operand_def, op_prov_def, op_taint_def] >>
     metis_tac[]) >>
  `u.vs_allocas = s.vs_allocas /\ u.vs_alloca_next = s.vs_alloca_next /\
   u.vs_memory = s.vs_memory /\ u.vs_accounts = s.vs_accounts /\
   u.vs_transient = s.vs_transient /\ u.vs_call_ctx = s.vs_call_ctx /\
   u.vs_immutables = s.vs_immutables` by
    (qpat_assum `u = s with <|vs_vars := _; vs_inst_idx := _|>`
      (ACCEPT_TAC o SIMP_RULE (srw_ss()) [] o
        Q.AP_TERM `\st. (st.vs_allocas,st.vs_alloca_next,st.vs_memory,
          st.vs_accounts,st.vs_transient,st.vs_call_ctx,st.vs_immutables)`)) >>
  qabbrev_tac `bytes = TAKE n (DROP a cx.txn.calldata)` >>
  `LENGTH bytes = n` by simp[Abbr `bytes`,LENGTH_TAKE_EQ] >>
  `!v wd. v.vs_accounts = u.vs_accounts /\ v.vs_call_ctx = u.vs_call_ctx /\
      eval_operand data v = SOME wd /\ eval_operand start v = SOME (n2w a) /\
      eval_operand (Lit (n2w n)) v = SOME (n2w n) /\
      (CALLDATACOPY = EXTCODECOPY ==> eval_operand addr v = eval_operand addr u) ==>
      step_inst_base
        (mk_inst s3.cs_next_id CALLDATACOPY [data;start;Lit (n2w n)] []) v =
      OK (write_memory_with_expansion (w2n wd) bytes v)` by
    (rpt strip_tac >>
     qspecl_then [`data`,`start`,`Lit (n2w n)`,`v`,`wd`,
       `(n2w a:bytes32)`,`(n2w n:bytes32)`,`s3.cs_next_id`]
       mp_tac calldata_copy_step >>
     simp[Abbr `bytes`,w2n_n2w]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at s2 x` by
    (rpt strip_tac >> irule freshWritesTheory.not_fresh_at_mono >>
     qexists_tac `sa` >> simp[]) >>
  (fn (asl,w) =>
    let val post = fst (dest_forall (find_term (fn tm => is_forall tm andalso
      fst (dest_var (fst (dest_forall tm))) = "H'") w))
    in qpat_assum `stmt_state_rel H0 ctx func cenv cx es u` (fn th =>
      mp_tac (Q.INST [`sa` |-> `s2`,`sc` |-> `s3`,`sd` |-> `s4`,
        `s` |-> `u`,`G` |-> `G1`,`tn` |-> `tn1`,
        `opc` |-> `CALLDATACOPY`,`ops` |-> `[data;start;Lit (n2w n)]`,
        `cnt` |-> `Lit (n2w n)`,`wa` |-> `(n2w a:bytes32)`,`bound` |-> `n`]
        (calldata_horizons (hd (snd (strip_comb (concl th)))) post
          bytestring_external_output_full_resources))) (asl,w) end) >>
  impl_tac >- (simp[eval_operand_def,op_taint_def] >> metis_tac[]) >>
  disch_then (qx_choose_then `root` (qx_choose_then `w`
    (qx_choose_then `t` (qx_choose_then `G2`
      (qx_choose_then `tm` strip_assume_tac))))) >>
  `!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP G2 x = FLOOKUP G x /\
      op_taint tm (Var x) = op_taint tn (Var x)` by
    (qpat_assum `!x. not_fresh_at sa x ==> lookup_var x u = _ /\ _` mp_tac >>
     qpat_assum `!x. not_fresh_at s2 x ==> lookup_var x t = _ /\ _` mp_tac >>
     qpat_assum `!x. not_fresh_at sa x ==> not_fresh_at s2 x` mp_tac >>
     rpt (pop_assum kall_tac) >> metis_tac[]) >>
  `local_ptrs_rel func cenv es.scopes s` by
    (qpat_assum `stmt_state_rel H0 ctx func cenv cx es s` mp_tac >>
     rpt (pop_assum kall_tac) >> simp[stmt_state_rel_def,state_rel_def]) >>
  `!name b len. local_region cenv es.scopes s name b len <=>
      local_region cenv es.scopes u name b len` by
    (rpt gen_tac >> eq_tac
     >- (strip_tac >> irule local_region_frame_fwd >>
         qexistsl_tac [`s`,`sa`,`es.scopes`] >> simp[] >> metis_tac[]) >>
     strip_tac >>
     qspecl_then [`func`,`cenv`,`es.scopes`,`s`,`sa`,`es.scopes`,`u`,
       `name`,`b`,`len`] match_mp_tac local_region_frame >>
     simp[] >> metis_tac[]) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK t,G2,tm)` by
    (gen_tac >>
     qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) _ _` (qspec_then `D` mp_tac) >>
     qpat_assum `!D. gas_origin_ptr_path _ (u,G1,tn1) _ _` (qspec_then `D` mp_tac) >>
     rpt (pop_assum kall_tac) >> metis_tac[gas_origin_ptr_path_append,APPEND_NIL]) >>
  `!aid e. FLOOKUP s.vs_allocas aid = SOME e ==>
      FLOOKUP t.vs_allocas aid = SOME e` by metis_tac[] >>
  `!aid b len. FLOOKUP s.vs_allocas aid = SOME (b,len) /\ aid < sa.cs_next_id ==>
      mem_bytes_at b len t.vs_memory = mem_bytes_at b len s.vs_memory` by
    (rpt strip_tac >>
     qpat_assum `!aid b len. FLOOKUP u.vs_allocas aid = SOME (b,len) /\ _ ==> _`
       (qspecl_then [`aid`,`b`,`len`] mp_tac) >> simp[] >> decide_tac) >>
  `!name b len. local_region cenv es.scopes s name b len ==>
      mem_bytes_at b len t.vs_memory = mem_bytes_at b len s.vs_memory /\
      (!i. b <= i /\ i < b+len /\ i IN tm.t_mem ==> i IN tn.t_mem)` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `!name b len. local_region cenv es.scopes u name b len ==> _`
       (qspecl_then [`name`,`b`,`len`] mp_tac) >>
     qpat_assum `!name b len. local_region cenv es.scopes s name b len <=> _`
       (qspecl_then [`name`,`b`,`len`] mp_tac) >>
     qpat_assum `u.vs_memory = s.vs_memory` mp_tac >>
     qpat_assum `tn1.t_mem = tn.t_mem` mp_tac >>
     qpat_assum `local_region cenv es.scopes s name b len` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >> metis_tac[]) >>
  `locals_kept cenv es es s t` by
    (irule locals_kept_regions >> rpt strip_tac >> metis_tac[]) >>
  `pure_frame cenv func es sa s t` by
    (qpat_assum `pure_frame cenv func es s2 u t` mp_tac >>
     qpat_assum `!name b len. local_region cenv es.scopes s name b len <=> _` mp_tac >>
     qpat_assum `u.vs_memory = s.vs_memory` mp_tac >>
     qpat_assum `sa.cs_next_id <= s2.cs_next_id` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[NoAsms,pure_frame_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  `ghost_kept_at lo cenv es sa G tn s G2 tm` by
    (qpat_assum `ghost_kept_at lo cenv es s2 G1 tn1 u G2 tm`
       (strip_assume_tac o REWRITE_RULE[ghost_kept_at_def]) >>
     rewrite_tac[ghost_kept_at_def] >> rpt conj_tac
     >- (rpt strip_tac >>
         qpat_assum `!x. not_fresh_at sa x ==> lookup_var x t = _ /\ _`
           (qspec_then `x` mp_tac) >> simp[])
     >- (rpt strip_tac >>
         `aid < s2.cs_next_id` by decide_tac >>
         `!name b len. local_region cenv es.scopes u name b len ==>
             off+sz <= b \/ b+len <= off` by metis_tac[] >>
         qpat_assum `!aid off sz i. FLOOKUP u.vs_allocas aid = SOME (off,sz) /\ _ ==> _`
           (qspecl_then [`aid`,`off`,`sz`,`i`] mp_tac) >> simp[] >>
         disch_then match_mp_tac >> first_assum ACCEPT_TAC)
     >- (qx_genl_tac [`name`,`b`,`sz`,`i`] >> strip_tac >>
         qpat_assum `!name b len. local_region cenv es.scopes s name b len ==> _ /\ _`
           (qspecl_then [`name`,`b`,`sz`] mp_tac) >> simp[] >> metis_tac[]) >>
     rpt strip_tac >>
     qpat_assum `tn1.t_mem = tn.t_mem` (fn eq =>
       qpat_assum `!i. i < lo /\ i IN tm.t_mem ==> i IN tn1.t_mem`
         (match_mp_tac o REWRITE_RULE[eq])) >> simp[]) >>
  (fn (asl,w) =>
    sg [ANTIQUOTE (find_term (fn tm => is_forall tm andalso
      fst (dest_var (fst (dest_forall tm))) = "H'") w)] (asl,w))
  >- (rpt strip_tac >>
      `stmt_state_rel H' ctx func cenv cx es u` by
        (qpat_assum `stmt_state_rel H' ctx func cenv cx es s` mp_tac >>
         qpat_assum `!x. not_fresh_at sa x ==> lookup_var x u = _ /\ _` mp_tac >>
         qpat_assum `u = s with <|vs_vars := _; vs_inst_idx := _|>` mp_tac >>
         qpat_assum `local_ptrs_reserved cenv sa` mp_tac >>
         rpt (pop_assum kall_tac) >> rpt strip_tac >>
         qpat_assum `u = _` SUBST1_TAC >>
         simp[stmt_state_rel_inst_idx] >> irule stmt_state_rel_vars_frame >>
         fs[local_ptrs_reserved_def,lookup_var_def,stmt_state_rel_inst_idx] >> metis_tac[]) >>
      (fn (asl,w) =>
        qpat_assum `!h. _ ==> stmt_state_rel _ _ _ _ _ _ t`
          (match_mp_tac o ISPEC (hd (snd (strip_comb w)))) (asl,w)) >>
      first_assum ACCEPT_TAC) >>
  qexistsl_tac [`root`,`w`,`t`,`G2`,`tm`] >>
  asm_simp_tac bool_ss [] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  simp[Abbr `bytes`] >> TRY (first_assum ACCEPT_TAC) >> metis_tac[]
QED

Theorem bytestring_calldata_full_run_frame:
  compile_slice_calldata start (Lit (n2w n)) N sa = (out,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  stmt_state_rel H0 ctx func cenv cx es s /\ context_well_typed cx /\
  0 < n /\ n < dimword (:256) /\ a < dimword (:256) /\
  32+n <= N /\ N < dimword (:256) /\
  eval_operand start s = SOME (n2w a) /\
  op_prov G start = NONE /\ op_taint tn start = {} /\
  (!x. start = Var x ==> not_fresh_at sa x) /\
  a+n < dimword (:256) /\ a+n <= LENGTH cx.txn.calldata /\
  alloca_history func s /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?p w t HG tm.
    out = Var p /\ not_fresh_at sb p /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,HG,tm)) /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~t.vs_halted /\
    lookup_var p t = SOME w /\ ptr_covers HG tm p t N /\
    FLOOKUP t.vs_allocas (sa.cs_next_id+7) = SOME (w2n w,N) /\
    w2n w+N < dimword (:256) /\ w2n w+N <= t.vs_alloca_next /\
    val_in_memory (BaseTV (BytesT (Dynamic n)))
      (BytesV (TAKE n (DROP a cx.txn.calldata))) (w2n w) t.vs_memory /\
    (!i. w2n w <= i /\ i < w2n w+32+n ==> i NOTIN tm.t_mem) /\
    (!H'. stmt_state_rel H' ctx func cenv cx es s ==>
       stmt_state_rel H' ctx func cenv cx es t) /\
    alloca_history func t /\ allocas_from lo t /\ lo <= t.vs_alloca_next /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP HG x = FLOOKUP G x /\
      op_taint tm (Var x) = op_taint tn (Var x)) /\
    (!aid e. FLOOKUP s.vs_allocas aid = SOME e ==>
      FLOOKUP t.vs_allocas aid = SOME e) /\
    (!aid b len. FLOOKUP s.vs_allocas aid = SOME (b,len) /\
      aid < sa.cs_next_id ==>
      mem_bytes_at b len t.vs_memory = mem_bytes_at b len s.vs_memory) /\
    (!name b len. local_region cenv es.scopes s name b len ==>
      mem_bytes_at b len t.vs_memory = mem_bytes_at b len s.vs_memory /\
      (!i. b <= i /\ i < b+len /\ i IN tm.t_mem ==> i IN tn.t_mem)) /\
    mem_bytes_at 0 lo t.vs_memory = mem_bytes_at 0 lo s.vs_memory /\
    tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    ghost_kept_at lo cenv es sa G tn s HG tm /\
    locals_kept cenv es es s t /\ pure_frame cenv func es sa s t /\
    t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
    t.vs_call_ctx = s.vs_call_ctx /\ t.vs_immutables = s.vs_immutables
Proof
  strip_tac >> drule_all bytestring_calldata_full_run_resources >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  qexistsl_tac [`p`,`w`,`t`,`HG`,`tm`] >> asm_rewrite_tac[]
QED

Theorem bytestring_calldata_full_run:
  compile_slice_calldata start (Lit (n2w n)) N sa = (out,sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  stmt_state_rel H0 ctx func cenv cx es s /\ context_well_typed cx /\
  0 < n /\ n < dimword (:256) /\ a < dimword (:256) /\
  32+n <= N /\ N < dimword (:256) /\
  eval_operand start s = SOME (n2w a) /\
  op_prov G start = NONE /\ op_taint tn start = {} /\
  (!x. start = Var x ==> not_fresh_at sa x) /\
  a+n < dimword (:256) /\ a+n <= LENGTH cx.txn.calldata /\
  alloca_history func s /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?p w t HG tm.
    out = Var p /\ not_fresh_at sb p /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,HG,tm)) /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~t.vs_halted /\
    lookup_var p t = SOME w /\ ptr_covers HG tm p t N /\
    FLOOKUP t.vs_allocas (sa.cs_next_id+7) = SOME (w2n w,N) /\
    w2n w+N < dimword (:256) /\ w2n w+N <= t.vs_alloca_next /\
    val_in_memory (BaseTV (BytesT (Dynamic n)))
      (BytesV (TAKE n (DROP a cx.txn.calldata))) (w2n w) t.vs_memory /\
    (!i. w2n w <= i /\ i < w2n w+32+n ==> i NOTIN tm.t_mem) /\
    (!H'. stmt_state_rel H' ctx func cenv cx es s ==>
       stmt_state_rel H' ctx func cenv cx es t) /\
    alloca_history func t /\ allocas_from lo t /\ lo <= t.vs_alloca_next /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP HG x = FLOOKUP G x /\
      op_taint tm (Var x) = op_taint tn (Var x)) /\
    (!aid e. FLOOKUP s.vs_allocas aid = SOME e ==>
      FLOOKUP t.vs_allocas aid = SOME e) /\
    (!aid b len. FLOOKUP s.vs_allocas aid = SOME (b,len) /\
      aid < sa.cs_next_id ==>
      mem_bytes_at b len t.vs_memory = mem_bytes_at b len s.vs_memory) /\
    (!name b len. local_region cenv es.scopes s name b len ==>
      mem_bytes_at b len t.vs_memory = mem_bytes_at b len s.vs_memory /\
      (!i. b <= i /\ i < b+len /\ i IN tm.t_mem ==> i IN tn.t_mem)) /\
    mem_bytes_at 0 lo t.vs_memory = mem_bytes_at 0 lo s.vs_memory /\
    tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
    ghost_kept_at lo cenv es sa G tn s HG tm /\
    locals_kept cenv es es s t /\ pure_frame cenv func es sa s t
Proof
  strip_tac >> drule_all bytestring_calldata_full_run_frame >>
  disch_then (qspecl_then [`explicit`,`PG`] strip_assume_tac) >>
  qexistsl_tac [`p`,`w`,`t`,`HG`,`tm`] >> asm_rewrite_tac[]
QED
