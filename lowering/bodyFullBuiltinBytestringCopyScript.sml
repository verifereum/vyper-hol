(* External slice copies and their length words on the joint path. *)
Theory bodyFullBuiltinBytestringCopy
Ancestors
  bodyPtrBytestringBuiltinsExternalSlice bodyFullUnwrapRun
  bodyFullBuiltinBytestringOutBuffer bodyPtrBytestringBuiltinsCalldataFrame
  bodyPtrBytestringBuiltinsBuffer loweringPosts bodyMemoryDefs codegenRel
  exprSimAlloc exprSimProps exprSimCalldataSlice valueEncodingProofs localPtrsProps
  allocaHistory context words pred_set instIdxIndep
  fragExec fragExecPtr fragGasSeqPtr fragGasOriginPtr ptrSafetyTransport bodyPtrDefs
  instMemFrontier memSafeRun ptrDiscipline venomExecSemantics
  venomState venomInst emitHelper emitHelperProps exprLoweringProps
  compileEnv loweringStateRelDefs wordLoadStorePtr list finite_map

Theorem bytestring_external_copy_origin_edge:
  emit_void opc ops sa = ((),sb) /\ fn_has_code sa sb func /\
  (((opc = CALLDATACOPY \/ opc = CODECOPY) /\
     ops = [Var dst;start;cnt]) \/
   (opc = EXTCODECOPY /\ ops = [addr;Var dst;start;cnt] /\
    (?wa. eval_operand addr s = SOME wa) /\ op_taint tn addr = {})) /\
  eval_operand (Var dst) s = SOME wd /\
  eval_operand start s = SOME wa /\ eval_operand cnt s = SOME wn /\
  op_taint tn start = {} /\ op_taint tn cnt = {} /\
  ptr_covers G tn dst s (w2n wn) /\
  w2n wd + w2n wn <= s.vs_alloca_next /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  step_inst_base (mk_inst sa.cs_next_id opc ops []) s = OK u ==>
  !D. gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (u with vs_inst_idx := SUC s.vs_inst_idx),
     step_prov PG G (mk_inst sa.cs_next_id opc ops []) u,
     step_taint (mk_inst sa.cs_next_id opc ops []) s u tn)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >> gen_tac >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++
     [mk_inst sa.cs_next_id opc ops []]` by
    gvs[emit_void_def, comp_bind_def, comp_ignore_bind_def,
        comp_return_def, fresh_id_def, emit_def] >>
  drule_all fn_has_code_same_block >> strip_tac >>
  first_x_assum (qspec_then `0` mp_tac) >> simp[] >> strip_tac >>
  `opc = CALLDATACOPY \/ opc = CODECOPY \/ opc = EXTCODECOPY` by
    metis_tac[] >>
  `inst_mem_below_frontier (mk_inst sa.cs_next_id opc ops []) s` by
    (gvs[below_frontier_CALLDATACOPY, below_frontier_CODECOPY,
         below_frontier_EXTCODECOPY]) >>
  `ptr_inst_ok D lo 0 ctx func G tn
     (mk_inst sa.cs_next_id opc ops []) s` by
    (irule ptr_inst_ok_lower_bound_transport >> simp[] >>
     qexists_tac `0` >> simp[] >>
     irule ptr_inst_ok_external_copy >> metis_tac[]) >>
  drule_at (Pat `ptr_inst_ok _ _ _ _ _ _ _ _ _`)
    straight_line_origin_ptr_edge >>
  simp[mk_inst_def, is_terminator_def, inst_dload_in_section_def] >>
  metis_tac[]
QED

Theorem bytestring_length_store_origin_edge:
  emit_void MSTORE [Var root;cnt] sa = ((),sb) /\
  fn_has_code sa sb func /\
  lookup_var root s = SOME b /\ eval_operand cnt s = SOME n /\
  ptr_covers G tn root s 32 /\ op_taint tn cnt = {} /\
  w2n b + 32 <= s.vs_alloca_next /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  !D. gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (mstore (w2n b) n s with vs_inst_idx := SUC s.vs_inst_idx),
     step_prov PG G (mk_inst sa.cs_next_id MSTORE [Var root;cnt] [])
       (mstore (w2n b) n s),
     step_taint (mk_inst sa.cs_next_id MSTORE [Var root;cnt] []) s
       (mstore (w2n b) n s) tn)
Proof
  strip_tac >> gen_tac >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++
     [mk_inst sa.cs_next_id MSTORE [Var root;cnt] []]` by
    gvs[emit_void_def, comp_bind_def, comp_ignore_bind_def,
        comp_return_def, fresh_id_def, emit_def] >>
  drule_all fn_has_code_same_block >> strip_tac >>
  first_x_assum (qspec_then `0` mp_tac) >> simp[] >> strip_tac >>
  `inst_mem_below_frontier
     (mk_inst sa.cs_next_id MSTORE [Var root;cnt] []) s` by
    simp[below_frontier_MSTORE, eval_operand_def] >>
  `ptr_inst_ok D lo 0 ctx func G tn
     (mk_inst sa.cs_next_id MSTORE [Var root;cnt] []) s` by
    (irule ptr_inst_ok_lower_bound_transport >> simp[] >>
     qexists_tac `0` >> simp[] >> irule ptr_inst_ok_mstore >> simp[]) >>
  drule_at (Pat `ptr_inst_ok _ _ _ _ _ _ _ _ _`)
    straight_line_origin_ptr_edge >>
  simp[mk_inst_def, is_terminator_def, inst_dload_in_section_def,
       step_inst_base_opcode_eqs, exec_write2_def, eval_operand_def] >>
  metis_tac[]
QED

(* Both instructions use the same physical states and ghosts for every
   horizon.  In particular, the copy does not pick a second allocation. *)
Theorem bytestring_external_copy_length_full_run:
  emit_void opc ops sa = ((),sm) /\ fn_has_code sa sm func /\
  emit_void MSTORE [Var root;cnt] sm = ((),sb) /\
  fn_has_code sm sb func /\
  (((opc = CALLDATACOPY \/ opc = CODECOPY) /\
     ops = [Var dst;start;cnt]) \/
   (opc = EXTCODECOPY /\ ops = [addr;Var dst;start;cnt] /\
    (?wa. eval_operand addr s = SOME wa) /\ op_taint tn addr = {})) /\
  eval_operand (Var dst) s = SOME wd /\
  eval_operand start s = SOME wa /\ eval_operand cnt s = SOME wn /\
  lookup_var root s = SOME b /\
  op_taint tn start = {} /\ op_taint tn cnt = {} /\
  ptr_covers G tn dst s (w2n wn) /\
  32 <= N /\ ptr_covers G tn root s N /\
  w2n wd + w2n wn <= s.vs_alloca_next /\
  w2n b + 32 <= s.vs_alloca_next /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  step_inst_base (mk_inst sa.cs_next_id opc ops []) s =
    OK (write_memory_with_expansion (w2n wd) bytes s) ==>
  ?u t tf.
    u = (write_memory_with_expansion (w2n wd) bytes s)
      with vs_inst_idx := SUC s.vs_inst_idx /\
    t = (mstore (w2n b) wn u) with vs_inst_idx := SUC u.vs_inst_idx /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
       (OK t,G,tf)) /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~t.vs_halted /\
    ptr_covers G tf root t N /\ mem_word_at (w2n b) t.vs_memory = wn /\
    tf.t_var = tn.t_var /\ tf.t_stor = tn.t_stor /\
    tf.t_trans = tn.t_trans /\ tf.t_imm = tn.t_imm /\
    tf.t_mem = (tn.t_mem DIFF
      range_bytes (source_memory_write_ranges
        (mk_inst sa.cs_next_id opc ops []) s))
      DIFF {i | w2n b <= i /\ i < w2n b + 32}
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `step_inst_base _ s = _`
    (mp_then Any mp_tac external_copy_store_counted) >>
  disch_then drule_all >>
  disch_then (qspecl_then [`ARB`,`PG`] strip_assume_tac) >>
  rename1 `tm.t_var = tn.t_var` >>
  rename1 `u = (write_memory_with_expansion _ _ s) with vs_inst_idx := _` >>
  `opc = CALLDATACOPY \/ opc = CODECOPY \/ opc = EXTCODECOPY` by
    metis_tac[] >>
  qabbrev_tac `tc = step_taint (mk_inst sa.cs_next_id opc ops []) s
    (write_memory_with_expansion (w2n wd) bytes s) tn` >>
  `step_prov PG G (mk_inst sa.cs_next_id opc ops [])
       (write_memory_with_expansion (w2n wd) bytes s) = G /\
   tc.t_var = tn.t_var /\ tc.t_stor = tn.t_stor /\
   tc.t_trans = tn.t_trans /\ tc.t_imm = tn.t_imm` by
    (simp[Abbr `tc`] >> metis_tac[external_copy_ghost_frame]) >>
  `tc.t_mem = tn.t_mem DIFF
      range_bytes (source_memory_write_ranges
        (mk_inst sa.cs_next_id opc ops []) s)` by
    (simp[Abbr `tc`] >> irule external_copy_ghost_memory >>
     qpat_assum `((opc = CALLDATACOPY \/ opc = CODECOPY) /\ _) \/ _`
       strip_assume_tac >>
     gvs[write_memory_with_expansion_def]) >>
  `(!op. eval_operand op u = eval_operand op s /\
         op_taint tc op = op_taint tn op) /\
   allocas_from lo u /\ u.vs_alloca_next = s.vs_alloca_next /\
   lookup_var root u = SOME b /\ ~u.vs_halted` by
    (gvs[write_memory_with_expansion_def, write_memory_def,
         expand_memory_def, allocas_from_def, lookup_var_def] >>
     conj_tac
     >- (Cases >> simp[eval_operand_def, op_taint_def, lookup_var_def] >> metis_tac[]) >>
     metis_tac[]) >>
  `u.vs_current_bb = sm.cs_current_bb /\
   u.vs_inst_idx = LENGTH sm.cs_current_insts` by
    gvs[emit_void_def, comp_bind_def, comp_ignore_bind_def,
        comp_return_def, fresh_id_def, emit_def,
        write_memory_with_expansion_def, write_memory_def, expand_memory_def] >>
  `ptr_covers G tc root u 32` by
    (gvs[ptr_covers_def, op_taint_def, lookup_var_def,
         write_memory_with_expansion_def, write_memory_def,
         expand_memory_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  `step_prov PG G (mk_inst sm.cs_next_id MSTORE [Var root;cnt] [])
      (mstore (w2n b) wn u) = G /\
   step_taint (mk_inst sm.cs_next_id MSTORE [Var root;cnt] []) u
      (mstore (w2n b) wn u) tc = tm` by
    (qspecl_then [`PG`,`G`,`tc`,`u`,`sm.cs_next_id`,`root`,`cnt`,`b`,`wn`]
       mp_tac mstore_ghost_frame >>
     impl_tac >- simp[] >> strip_tac >>
     `(step_taint (mk_inst sm.cs_next_id MSTORE [Var root;cnt] []) u
        (mstore (w2n b) wn u) tc).t_imm = tc.t_imm` by
       simp[step_taint_def, imm_taint_def, mk_inst_def] >>
     simp_tac pure_ss [taint_component_equality] >> metis_tac[]) >>
  qexistsl_tac [`u`,`t`,`tm`] >> asm_simp_tac bool_ss [] >> gen_tac >>
  `gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (s,G,tn) []
     (OK u,G,tc)` by
    (mp_tac (bytestring_external_copy_origin_edge |> Q.INST
       [`sb` |-> `sm`,
        `u` |-> `write_memory_with_expansion (w2n wd) bytes s`]) >>
     impl_tac >- simp[] >>
     disch_then (qspec_then `D` mp_tac) >> simp[Abbr `tc`]) >>
  `gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (u,G,tc) []
     (OK t,G,tm)` by
    (mp_tac (bytestring_length_store_origin_edge |> Q.INST
       [`sa` |-> `sm`, `s` |-> `u`, `n` |-> `wn`, `tn` |-> `tc`]) >>
     impl_tac >- simp[] >>
     disch_then (qspec_then `D` mp_tac) >> simp[]) >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (u,G,tc) []
     (OK t,G,tm)` by
    (qpat_assum `gas_origin_ptr_edge _ (u,G,tc) [] (OK t,G,tm)` mp_tac >>
     qpat_assum `~t.vs_halted` mp_tac >>
     rpt (pop_assum kall_tac) >>
     metis_tac[gas_origin_ptr_path_rules, APPEND]) >>
  qpat_assum `gas_origin_ptr_edge _ (s,G,tn) [] (OK u,G,tc)` mp_tac >>
  qpat_assum `gas_origin_ptr_path _ (u,G,tc) [] (OK t,G,tm)` mp_tac >>
  qpat_assum `u = _` mp_tac >> qpat_assum `t = _` mp_tac >>
  qpat_assum `s.vs_inst_idx = _` mp_tac >>
  qpat_assum `u.vs_inst_idx = _` mp_tac >>
  rpt (pop_assum kall_tac) >>
  rpt strip_tac >> gvs[] >>
  metis_tac[gas_origin_ptr_path_rules, APPEND]
QED


(* Proposed shared Copy owner interface. Existing exports stay unchanged. *)
Theorem bytestring_external_output_full_resources:
  compile_slice_out_buf N sa = ((out,data),sc) /\
  emit_void opc ops sc = ((),sd) /\
  emit_void MSTORE [out;cnt] sd = ((),sb) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\
  stmt_state_rel H0 ctx func cenv cx es s /\
  0 < n /\ n < dimword (:256) /\ 32+n <= N /\ N < dimword (:256) /\
  LENGTH bytes = n /\
  eval_operand start s = SOME wa /\ eval_operand cnt s = SOME (n2w n) /\
  op_taint tn start = {} /\ op_taint tn cnt = {} /\
  (!x. (start = Var x \/ cnt = Var x) ==> not_fresh_at sa x) /\
  (((opc = CALLDATACOPY \/ opc = CODECOPY) /\ ops = [data;start;cnt]) \/
   (opc = EXTCODECOPY /\ ops = [addr;data;start;cnt] /\
    (?aw. eval_operand addr s = SOME aw) /\ op_taint tn addr = {} /\
    (!x. addr = Var x ==> not_fresh_at sa x))) /\
  (!v wd. v.vs_accounts = s.vs_accounts /\ v.vs_call_ctx = s.vs_call_ctx /\
    v.vs_code = s.vs_code /\
    eval_operand data v = SOME wd /\ eval_operand start v = SOME wa /\
    eval_operand cnt v = SOME (n2w n) /\
    (opc = EXTCODECOPY ==> eval_operand addr v = eval_operand addr s) ==>
    step_inst_base (mk_inst sc.cs_next_id opc ops []) v =
      OK (write_memory_with_expansion (w2n wd) bytes v)) /\
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
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,N) /\
    w2n w+N < dimword (:256) /\ w2n w+N <= t.vs_alloca_next /\
    val_in_memory (BaseTV (BytesT (Dynamic bound))) (BytesV bytes)
      (w2n w) t.vs_memory /\
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
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `cs_extends sa sc` by
    metis_tac[compile_slice_out_buf_compiler_parts,cs_extends_trans] >>
  `cs_extends sc sd /\ cs_extends sd sb` by
    metis_tac[cs_appends_emit_helpers,cs_appends_def] >>
  `fn_has_code sa sc func /\ fn_has_code sc sd func /\
   fn_has_code sd sb func` by metis_tac[fn_has_code_split,cs_extends_trans] >>
  `32 <= N` by decide_tac >>
  (fn (asl,w) =>
    let
      val provider = bytestring_out_buffer_full_run
      val post = fst (dest_forall (find_term (fn tm => is_forall tm andalso
        fst (dest_var (fst (dest_forall tm))) = "H'") (concl provider)))
      val target = fst (dest_forall (find_term (fn tm => is_forall tm andalso
        fst (dest_var (fst (dest_forall tm))) = "H'") w))
      val formal = first (fn v => fst (dest_var v) = "H") (free_vars (concl provider))
    in qpat_assum `stmt_state_rel H0 ctx func cenv cx es s` (fn hyp =>
      let val actual = hd (snd (strip_comb (concl hyp)))
          val tys = match_type (type_of (pairSyntax.mk_pair (formal,post)))
            (type_of (pairSyntax.mk_pair (actual,target)))
      in mp_tac (Q.INST [`root` |-> `out`,`sb` |-> `sc`,`n` |-> `N`]
        (INST [inst tys formal |-> actual] (INST_TYPE tys provider))) end) (asl,w)
    end) >>
  impl_tac >- simp[] >>
  disch_then (qx_choose_then `root` (qx_choose_then `dst`
    (qx_choose_then `w` (qx_choose_then `v` (qx_choose_then `G2`
      (qx_choose_then `tn2` strip_assume_tac)))))) >>
  qpat_assum `out = Var root` SUBST_ALL_TAC >>
  qpat_assum `data = Var dst` SUBST_ALL_TAC >>
  `v.vs_accounts = s.vs_accounts /\ v.vs_call_ctx = s.vs_call_ctx /\
   v.vs_code = s.vs_code /\
   v.vs_labels = s.vs_labels /\ v.vs_memory = s.vs_memory /\
   v.vs_transient = s.vs_transient /\ v.vs_immutables = s.vs_immutables` by
    (qpat_assum `v with <|vs_vars := _;vs_allocas := _;
      vs_alloca_next := _;vs_inst_idx := _|> = s` mp_tac >>
     simp[venom_state_component_equality]) >>
  `eval_operand start v = SOME wa /\ op_taint tn2 start = {}` by
    (Cases_on `start` >> gvs[eval_operand_def,op_taint_def] >> metis_tac[]) >>
  `eval_operand cnt v = SOME (n2w n) /\ op_taint tn2 cnt = {}` by
    (Cases_on `cnt` >> gvs[eval_operand_def,op_taint_def] >> metis_tac[]) >>
  `opc = EXTCODECOPY ==>
     eval_operand addr v = eval_operand addr s /\ op_taint tn2 addr = {}` by
    (strip_tac >> gvs[] >> Cases_on `addr` >>
     gvs[eval_operand_def,op_taint_def] >> metis_tac[]) >>
  `w2n (w+32w) = w2n w+32` by
    (`w2n w+32 < dimword (:256)` by decide_tac >>
     simp[w2n_add_2,w2n_n2w]) >>
  `ptr_covers G2 tn2 dst v n` by
    (fs[ptr_covers_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  `step_inst_base (mk_inst sc.cs_next_id opc ops []) v =
     OK (write_memory_with_expansion (w2n (w+32w)) bytes v)` by
    (qpat_assum `!v wd. _ ==> step_inst_base _ v = _`
       (qspecl_then [`v`,`w+32w`] match_mp_tac) >>
     simp[eval_operand_def]) >>
  mp_tac (bytestring_external_copy_length_full_run |> Q.INST
    [`sa` |-> `sc`,`sm` |-> `sd`,`s` |-> `v`,`G` |-> `G2`,
     `tn` |-> `tn2`,`wd` |-> `w+32w`,`wn` |-> `n2w n`,`b` |-> `w`]) >>
  impl_tac >-
    (simp[eval_operand_def,w2n_n2w] >>
     qpat_assum `(_ /\ ops = [Var dst;start;cnt]) \/ _` mp_tac >>
     qpat_assum `opc = EXTCODECOPY ==> _` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >> simp[] >> metis_tac[]) >>
  disch_then (qx_choose_then `vc` (qx_choose_then `t`
    (qx_choose_then `tm` strip_assume_tac))) >>
  `t = mstore (w2n w) (n2w n)
      (write_memory_with_expansion (w2n w+32) bytes v)
        with vs_inst_idx := LENGTH sb.cs_current_insts` by
    (qpat_assum `t = _` mp_tac >> qpat_assum `vc = _` mp_tac >>
     qpat_assum `t.vs_inst_idx = LENGTH sb.cs_current_insts` mp_tac >>
     qpat_assum `w2n (w+32w) = w2n w+32` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >> gvs[mstore_idx]) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,G2,tm)` by
    (gen_tac >>
     qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) _ _`
       (qspec_then `D` mp_tac) >>
     qpat_assum `!D. gas_origin_ptr_path _ (v,G2,tn2) _ _`
       (qspec_then `D` mp_tac) >>
     rpt (pop_assum kall_tac) >>
     metis_tac[gas_origin_ptr_path_append,APPEND_NIL]) >>
  `t.vs_vars = v.vs_vars /\ t.vs_allocas = v.vs_allocas /\
   t.vs_alloca_next = v.vs_alloca_next` by
    (qpat_assum `t = _`
       (strip_assume_tac o SIMP_RULE (srw_ss())
         [mstore_def,write_memory_with_expansion_def,LET_THM] o
         Q.AP_TERM `\st. (st.vs_vars,st.vs_allocas,st.vs_alloca_next)`) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `s.vs_alloca_next <= t.vs_alloca_next` by decide_tac >>
  `t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
   t.vs_call_ctx = s.vs_call_ctx /\ t.vs_immutables = s.vs_immutables` by
    (qpat_assum `t = _`
       (mp_tac o SIMP_RULE (srw_ss())
         [mstore_def,write_memory_with_expansion_def,LET_THM] o
         Q.AP_TERM `\st. (st.vs_accounts,st.vs_transient,st.vs_call_ctx,st.vs_immutables)`) >>
     simp[]) >>
  `lookup_var root t = SOME w` by fs[lookup_var_def] >>
  `FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,N)` by simp[] >>
  `lo <= t.vs_alloca_next` by decide_tac >>
  `allocas_from lo t` by
    (qpat_assum `allocas_from lo v` mp_tac >>
     simp[NoAsms,allocas_from_def] >> simp[]) >>
  `!aid e. FLOOKUP s.vs_allocas aid = SOME e ==>
     FLOOKUP t.vs_allocas aid = SOME e` by (rpt strip_tac >> simp[]) >>
  `!x. not_fresh_at sa x ==>
     lookup_var x t = lookup_var x s /\ FLOOKUP G2 x = FLOOKUP G x /\
     op_taint tm (Var x) = op_taint tn (Var x)` by
    (rpt strip_tac >>
     qpat_assum `!x. not_fresh_at sa x ==> lookup_var x v = _ /\ _`
       (qspec_then `x` mp_tac) >>
     qpat_assum `t.vs_vars = v.vs_vars` mp_tac >>
     qpat_assum `tm.t_var = tn2.t_var` mp_tac >>
     qpat_assum `not_fresh_at sa x` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     fs[lookup_var_def,op_taint_def]) >>
  `tm.t_mem = (tn2.t_mem DIFF
      {i | w2n (w+32w) <= i /\ i < w2n (w+32w)+n})
      DIFF {i | w2n w <= i /\ i < w2n w+32}` by
    (qpat_assum `tm.t_mem = _` mp_tac >>
     Cases_on `opc = CALLDATACOPY` >> gvs[] >>
     Cases_on `opc = CODECOPY` >>
     gvs[source_memory_write_ranges_def,sized_source_write_range_def,
       range_bytes_def,mk_inst_def,eval_operand_def,w2n_n2w,EXTENSION]) >>
  `!i. w2n w <= i /\ i < w2n w+32+n ==> i NOTIN tm.t_mem` by
    (qpat_assum `tm.t_mem = (tn2.t_mem DIFF
        {i | w2n (w+32w) <= i /\ i < w2n (w+32w)+n}) DIFF _` mp_tac >>
     qpat_assum `w2n (w+32w) = w2n w+32` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     qpat_x_assum `i IN tm.t_mem` mp_tac >>
     qpat_assum `tm.t_mem = _` (fn th => pure_rewrite_tac[th]) >>
     qpat_assum `w2n (w+32w) = w2n w+32` (fn th => pure_rewrite_tac[th]) >>
     simp[] >> rpt strip_tac >> decide_tac) >>
  `?inst. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
     inst.inst_id = sa.cs_next_id` by
    (drule compile_slice_out_buf_compiler_parts >> strip_tac >>
     rename1 `compile_alloc_buffer _ _ = (abuf,asc)` >>
     qspecl_then [`sa`,`asc`,`sc`,`func`] mp_tac fn_has_code_split >>
     simp[] >> strip_tac >>
     qspecl_then [`N`,`sa`,`asc`,`abuf`,`func`] mp_tac buffer_alloc_code >>
     simp[] >> strip_tac >>
     qexists_tac `mk_inst sa.cs_next_id ALLOCA [Lit (n2w N)]
       [STRING #"%" (toString sa.cs_next_var)]` >> simp[mk_inst_def] >>
     qpat_assum `MEM (mk_inst _ ALLOCA _ _) (fn_insts func)`
       (ACCEPT_TAC o REWRITE_RULE[mk_inst_def])) >>
  rename1 `MEM allocinst (fn_insts func)` >>
  `tm.t_mem SUBSET tn2.t_mem` by
    (qpat_assum `tm.t_mem = (tn2.t_mem DIFF
       {i | w2n (w+32w) <= i /\ i < w2n (w+32w)+n}) DIFF _` SUBST1_TAC >>
     simp[SUBSET_DEF]) >>
  `!i. i < s.vs_alloca_next /\ i IN tm.t_mem ==> i IN tn.t_mem` by
    (rpt strip_tac >>
     `i IN tn2.t_mem` by
       (qpat_assum `tm.t_mem SUBSET tn2.t_mem`
         (qspec_then `i` mp_tac o REWRITE_RULE[SUBSET_DEF]) >> simp[]) >>
     qpat_assum `!i. i IN tn2.t_mem <=> _` (qspec_then `i` mp_tac) >>
     simp[] >> decide_tac) >>
  `!name b len. local_region cenv es.scopes s name b len ==>
      local_region cenv es.scopes v name b len` by
    (rpt strip_tac >> irule local_region_frame_fwd >>
     qexistsl_tac [`s`,`sa`,`es.scopes`] >> simp[] >>
     rpt strip_tac >>
     qpat_assum `!x. not_fresh_at sa x ==> lookup_var x t = _ /\ _`
       mp_tac >>
     qpat_assum `t.vs_vars = v.vs_vars` mp_tac >>
     qpat_assum `not_fresh_at sa x` mp_tac >>
     qpat_assum `lookup_var x s = SOME _` mp_tac >>
     rpt (pop_assum kall_tac) >> rpt strip_tac >>
     fs[lookup_var_def] >> metis_tac[]) >>
  qpat_assum `t = _`
    (assume_tac o SIMP_RULE (srw_ss()) [] o Q.AP_TERM `\st. st.vs_memory`) >>
  `!off len. regions_disjoint off len (w2n w) N ==>
     mem_bytes_at off len t.vs_memory = mem_bytes_at off len s.vs_memory` by
    (rpt strip_tac >>
     qpat_assum `t.vs_memory = _` (fn th => once_rewrite_tac[th]) >>
     qpat_assum `v.vs_memory = s.vs_memory`
       (fn th => pure_once_rewrite_tac[GSYM th]) >>
     `n2w n = (n2w (LENGTH bytes):bytes32)` by simp[] >>
     pop_assum SUBST1_TAC >> irule bytes_buffer_write_frame >>
     fs[regions_disjoint_def] >> decide_tac) >>
  `!name b len. local_region cenv es.scopes s name b len ==>
     mem_bytes_at b len t.vs_memory = mem_bytes_at b len s.vs_memory` by
    (rpt strip_tac >>
     qpat_assum `!off len. regions_disjoint _ _ _ _ ==> _` irule >>
     qpat_assum `!name b len. local_region _ _ v _ _ _ ==> _`
       (qspecl_then [`name`,`b`,`len`] mp_tac) >>
     impl_tac
     >- (qpat_assum `!name b len. local_region _ _ s _ _ _ ==> _`
           (qspecl_then [`name`,`b`,`len`] match_mp_tac) >> simp[]) >>
     simp[regions_disjoint_def] >> decide_tac) >>
  `!aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) ==>
     b+sz <= s.vs_alloca_next` by
    (qpat_assum `stmt_state_rel H0 ctx func cenv cx es s`
      (mp_tac o CONJUNCT1 o CONJUNCT2 o REWRITE_RULE[stmt_state_rel_def]) >>
     rpt (pop_assum kall_tac) >>
     simp[venomMemDefsTheory.alloca_inv_def,
       venomMemDefsTheory.alloca_next_valid_def] >>
     strip_tac >> first_assum ACCEPT_TAC) >>
  `!name b len. local_region cenv es.scopes s name b len ==>
     mem_bytes_at b len t.vs_memory = mem_bytes_at b len s.vs_memory /\
     (!i. b <= i /\ i < b+len /\ i IN tm.t_mem ==> i IN tn.t_mem)` by
    (rpt gen_tac >> disch_tac >> conj_tac
     >- (qpat_assum `!name b len. local_region _ _ s _ _ _ ==>
           mem_bytes_at _ _ _ = _`
           (qspecl_then [`name`,`b`,`len`] match_mp_tac) >> simp[]) >>
     rpt strip_tac >>
     qpat_assum `!i. i < s.vs_alloca_next /\ _ ==> _` irule >> simp[] >>
     `b+len <= s.vs_alloca_next` by
       (drule_all body_local_region_frontier >> simp[]) >> decide_tac) >>
  `ghost_kept_at lo cenv es sa G tn s G2 tm` by
    (rewrite_tac[ghost_kept_at_def] >> rpt conj_tac
     >- (rpt strip_tac >>
         qpat_assum `!x. not_fresh_at sa x ==> lookup_var x t = _ /\ _`
           (qspec_then `x` mp_tac) >> simp[])
     >- (rpt strip_tac >>
         qpat_assum `!i. i < s.vs_alloca_next /\ _ ==> _` irule >> simp[] >>
         `off+sz <= s.vs_alloca_next` by
           (qpat_assum `!aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) ==> _`
             (qspecl_then [`aid`,`off`,`sz`] match_mp_tac) >> simp[]) >>
         decide_tac)
     >- (rpt strip_tac >>
         qpat_assum `!i. i < s.vs_alloca_next /\ _ ==> _` irule >> simp[] >>
         `b+sz <= s.vs_alloca_next` by
           (drule_all body_local_region_frontier >> simp[]) >> decide_tac) >>
     rpt strip_tac >>
     qpat_assum `!i. i < s.vs_alloca_next /\ _ ==> _` irule >> simp[] >>
     decide_tac) >>
  `locals_kept cenv es es s t` by
    (irule locals_kept_regions >> first_assum ACCEPT_TAC) >>
  `!aid b len. FLOOKUP s.vs_allocas aid = SOME (b,len) /\ aid < sa.cs_next_id ==>
     mem_bytes_at b len t.vs_memory = mem_bytes_at b len s.vs_memory` by
    (rpt strip_tac >>
     qpat_assum `!off len. regions_disjoint _ _ _ _ ==> _` irule >>
     qpat_assum `!aid b len. _ /\ _ ==> regions_disjoint _ _ _ _`
       (qspecl_then [`aid`,`b`,`len`] mp_tac) >>
     impl_tac >- (simp[] >> decide_tac) >>
     simp[regions_disjoint_def] >> decide_tac) >>
  `lo <= w2n w` by
    (qpat_assum `allocas_from lo t`
      (qspecl_then [`sa.cs_next_id`,`w2n w`,`N`] match_mp_tac o
        REWRITE_RULE[allocas_from_def]) >> first_assum ACCEPT_TAC) >>
  `mem_bytes_at 0 lo t.vs_memory = mem_bytes_at 0 lo s.vs_memory` by
    (qpat_assum `!off len. regions_disjoint _ _ _ _ ==> _`
      (qspecl_then [`0`,`lo`] match_mp_tac) >> simp[regions_disjoint_def]) >>
  `pure_frame cenv func es sa s t` by
    (rewrite_tac[pure_frame_def] >> conj_tac
     >- first_assum ACCEPT_TAC >>
     rpt strip_tac >>
     qpat_assum `!off len. regions_disjoint _ _ _ _ ==> _` irule >>
     qpat_assum `!inst b sz. _ ==> regions_disjoint off len b sz`
       (qspecl_then [`allocinst`,`w2n w`,`N`] match_mp_tac) >> simp[]) >>
  `alloca_history func t` by
    (qpat_assum `emit_void opc ops sc = ((),sd)`
       (mp_then Any strip_assume_tac emitted_insts_emit_void) >>
     qpat_assum `emit_void MSTORE _ _ = _`
       (mp_then Any strip_assume_tac emitted_insts_emit_void) >>
     qpat_assum `emit_void opc ops sc = ((),sd)`
       (mp_then Any mp_tac emit_void_extends) >>
     simp[same_blocks_def] >> strip_tac >>
     qpat_assum `emit_void MSTORE _ _ = _`
       (mp_then Any mp_tac emit_void_extends) >>
     simp[same_blocks_def] >> strip_tac >>
     qpat_assum `vc = _`
       (strip_assume_tac o SIMP_RULE (srw_ss())
         [write_memory_with_expansion_def,LET_THM] o
         Q.AP_TERM `\st. (st.vs_allocas,st.vs_current_bb,st.vs_inst_idx)`) >>
     `vc.vs_current_bb = sd.cs_current_bb /\
      vc.vs_inst_idx = LENGTH sd.cs_current_insts` by simp[] >>
     qspecl_then [`sc`,`sd`,`func`,
       `[mk_inst sc.cs_next_id opc ops []]`] mp_tac fn_has_code_same_block >>
     simp[] >> disch_then (qx_choose_then `copybb` strip_assume_tac) >>
     `get_instruction copybb v.vs_inst_idx =
       SOME (mk_inst sc.cs_next_id opc ops [])` by simp[] >>
     `alloca_history func (v with vs_inst_idx := SUC v.vs_inst_idx)` by
       (irule history_nonalloca_advance >> conj_tac
        >- (qexistsl_tac [`copybb`,`mk_inst sc.cs_next_id opc ops []`] >>
            simp[mk_inst_def] >>
            qpat_assum `(_ /\ ops = [Var dst;start;cnt]) \/ _` mp_tac >>
            rpt (pop_assum kall_tac) >> rpt strip_tac >> gvs[]) >>
        first_assum ACCEPT_TAC) >>
     `alloca_history func vc` by
       (irule alloca_history_frame >>
        qexists_tac `v with vs_inst_idx := SUC v.vs_inst_idx` >> simp[]) >>
     qspecl_then [`sd`,`sb`,`func`,
       `[mk_inst sd.cs_next_id MSTORE [Var root;cnt] []]`]
       mp_tac fn_has_code_same_block >> simp[] >> strip_tac >>
     `get_instruction copybb vc.vs_inst_idx =
       SOME (mk_inst sd.cs_next_id MSTORE [Var root;cnt] [])` by simp[] >>
     `alloca_history func (vc with vs_inst_idx := SUC vc.vs_inst_idx)` by
       (irule history_nonalloca_advance >> conj_tac
        >- (qexistsl_tac [`copybb`,`mk_inst sd.cs_next_id MSTORE [Var root;cnt] []`] >>
            simp[mk_inst_def]) >> first_assum ACCEPT_TAC) >>
     irule alloca_history_frame >>
     qexists_tac `vc with vs_inst_idx := SUC vc.vs_inst_idx` >>
     simp[] >> simp[NoAsms,mstore_def,write_memory_with_expansion_def,LET_THM] >>
     simp[]) >>
  qexistsl_tac [`root`,`w`,`t`,`G2`,`tm`] >>
  asm_simp_tac bool_ss [] >> rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
  >- (irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sc` >>
      simp[] >> qpat_assum `emit_void opc ops sc = ((),sd)`
        (mp_then Any strip_assume_tac emitted_insts_emit_void) >>
      qpat_assum `emit_void MSTORE _ _ = _`
        (mp_then Any strip_assume_tac emitted_insts_emit_void) >> simp[]) >>
  TRY (first_assum ACCEPT_TAC)
  >- (qpat_assum `t = _` SUBST1_TAC >>
      qspecl_then [`w2n w`,`bytes`,`bound`,`v`] mp_tac bytes_buffer_write_encoding >>
      simp[]) >>
  TRY (first_assum ACCEPT_TAC)
  >- (rpt strip_tac >>
      `stmt_state_rel H' ctx func cenv cx es v` by
        ((fn (asl,w) => qpat_assum `!h. _ ==> stmt_state_rel _ _ _ _ _ _ v`
          (match_mp_tac o ISPEC (hd (snd (strip_comb w)))) (asl,w)) >> simp[]) >>
      qpat_assum `t = _` SUBST1_TAC >>
      simp[NoAsms,stmt_state_rel_inst_idx] >>
      irule allocated_bytes_write_state_rel >>
      conj_tac >- first_assum ACCEPT_TAC >> conj_tac
      >- (qexistsl_tac [`N`,`allocinst`] >> rpt conj_tac >>
          TRY (first_assum ACCEPT_TAC) >> metis_tac[]) >>
      first_assum ACCEPT_TAC) >>
  metis_tac[]
QED
