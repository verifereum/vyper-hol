(* Uniform array element traversal with body-aware child stores. *)
Theory bodyMemArrayAdapters
Ancestors
  bodyMemArrayHeader bodyMemAggregateTraversal exprSimAggregateLayout exprSimAggregateLoops
  gasOutcome gasSummary valueEncoding vyperTypeABI exprLowering compileEnv
  exprSimDefs exprSimMemDefs loweringPosts venomState venomMemDefs
  stmtSimProps stmtSimDeclCompose exprBopSimProps exprLoweringProps
  emitHelperProps loweringSlice fragGasMode bodyDeclMemoryCompose fragExec

Theorem aggregate_make_array_elems_body_sim_mem:
  !args ce cx env elem_ty tv header idx off sa out sb es func inst x b asz s0 ctx tops.
  EVERY (\e. expr_type e = elem_ty) args /\
  evaluate_type (get_tenv cx) elem_ty = SOME tv /\
  type_memory_bytes ce elem_ty = type_memory_size tv /\
  off = (if header then 32 else 0) + idx * type_memory_size tv /\
  compile_make_array_elems compile_expr ce args elem_ty
    (type_memory_bytes ce elem_ty) header (Var x) idx sa = (out,sb) /\
  expr_sim_inv ce cx env es /\
  (!e st. MEM e args /\ expr_sim_inv ce cx env st ==>
    expr_body_pre ce cx env e st) /\
  body_inv tops ctx ce cx /\ body_exprs_mem_ok cx args /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ MEM inst (fn_insts func) /\
  inst.inst_outputs = [x] /\ inst.inst_id < sa.cs_next_id /\
  (!st. expr_sim_inv ce cx env st ==> not_local_ptr ce st.scopes x) /\
  not_fresh_at sa x /\ lookup_var x s0 = SOME (n2w b) /\
  FLOOKUP s0.vs_allocas inst.inst_id = SOME (b,asz) /\
  off + LENGTH args * type_memory_size tv <= asz /\ b + asz < dimword (:256) /\
  (ce.ce_is_ctor ==>
   !name itv iv io.
     FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc io) /\
     FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
       | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
     regions_disjoint io (type_memory_size itv) (b+off)
       (LENGTH args * type_memory_size tv)) /\
  stmt_state_rel ctx func ce cx es s0 /\ alloca_history func s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  out = Var x /\
  gas_outcome T (cx_tops cx) (ctx,func) (eval_exprs cx args) (es,s0)
    (\res es' r. ?vs. res = INL vs /\ r.vs_current_bb = sb.cs_current_bb /\
      r.vs_inst_idx = LENGTH sb.cs_current_insts /\ expr_sim_inv ce cx env es' /\
      stmt_state_rel ctx func ce cx es' r /\
      elems_in_memory vs (b+off) tv r.vs_memory /\
      (!z w. not_fresh_at sa z /\ lookup_var z s0 = SOME w ==>
        lookup_var z r = SOME w) /\
      (!aid a. FLOOKUP s0.vs_allocas aid = SOME a ==>
        FLOOKUP r.vs_allocas aid = SOME a) /\
      (!p n. b <= p /\ p+n <= b+asz /\
        (p+n <= b+off \/ b+off+LENGTH args * type_memory_size tv <= p) ==>
        mem_bytes_at p n r.vs_memory = mem_bytes_at p n s0.vs_memory) /\
      (!aid p n. FLOOKUP s0.vs_allocas aid = SOME (p,n) /\
        aid < sa.cs_next_id /\ (p+n <= b \/ b+asz <= p) /\
        (!name lo sz. local_region ce es.scopes s0 name lo sz ==>
          p+n <= lo \/ lo+sz <= p) ==>
        mem_bytes_at p n r.vs_memory = mem_bytes_at p n s0.vs_memory) /\
      locals_kept ce es s0 r /\ alloca_history func r /\
      s0.vs_alloca_next <= r.vs_alloca_next)
    (\res es' exit. ?exc. res = INR exc /\
      expr_exit (INR exc : eval_result + exception) exit)
Proof
  rpt gen_tac >> strip_tac >>
  drule compile_make_array_elems_as_tuple >>
  disch_then (qspecl_then [`header`, `compile_expr`, `ce`, `Var x`, `idx`] mp_tac) >>
  strip_tac >>
  `OPT_MMAP (evaluate_type (get_tenv cx)) (MAP expr_type args) =
     SOME (REPLICATE (LENGTH args) tv)` by
    (irule exprSimAggregateEncodingTheory.OPT_MMAP_uniform_map >> metis_tac[]) >>
  `compile_make_tuple compile_expr ce args (Var x) off sa = (out,sb)` by
    (gvs[] >> metis_tac[]) >>
  drule aggregate_make_tuple_body_sim_mem >> disch_then drule >>
  disch_then (drule_at (Pat `body_inv _ _ _ _`)) >>
  disch_then (drule_at (Pat `expr_sim_inv _ _ _ _`)) >>
  disch_then (drule_at (Pat `FLOOKUP _.vs_allocas _ = SOME (_,_)`)) >>
  disch_then (qspecl_then [`es`, `func`] mp_tac) >>
  pure_rewrite_tac[exprSimAggregateEncodingTheory.type_memory_size_list_replicate] >>
  (impl_tac >- (gvs[] >> simp[] >> first_assum ACCEPT_TAC)) >>
  strip_tac >> gvs[] >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _` mp_tac >>
  rpt (pop_assum kall_tac) >>
  pure_rewrite_tac[gas_outcome_def, gas_summary_at_def] >> strip_tac
  >- (qexists_tac `marks` >> disj1_tac >>
      qexistsl_tac [`res`, `es_end`, `r`] >> gvs[] >>
      qpat_assum `gas_marked_exec _ _ _ _ _ _ _ _` mp_tac >>
      pure_rewrite_tac[gas_marked_exec_def] >> strip_tac >>
      first_x_assum (qspec_then `[]` mp_tac) >> strip_tac >>
      drule vyperInterpreterTheory.eval_exprs_length >> strip_tac >>
      conj_tac
      >- (irule (iffLR exprSimAggregateEncodingTheory.tuple_in_memory_replicate_elems) >>
          metis_tac[]) >>
      conj_tac >> first_assum ACCEPT_TAC) >>
  metis_tac[]
QED

Theorem array_header_frames[local]:
  32 + extent <= asz /\ sa.cs_next_id <= sm.cs_next_id /\
  sh = (mstore b w s0 with vs_inst_idx := SUC s0.vs_inst_idx) /\
  (!p n. p+n <= b \/ b+32 <= p ==>
    mem_bytes_at p n sh.vs_memory = mem_bytes_at p n s0.vs_memory) /\
  (!p n. b <= p /\ p+n <= b+asz /\
    (p+n <= b+32 \/ b+32+extent <= p) ==>
    mem_bytes_at p n r.vs_memory = mem_bytes_at p n sh.vs_memory) /\
  (!aid p n. FLOOKUP sh.vs_allocas aid = SOME (p,n) /\
    aid < sm.cs_next_id /\ (p+n <= b \/ b+asz <= p) /\
    (!name lo sz. local_region ce es.scopes sh name lo sz ==>
      p+n <= lo \/ lo+sz <= p) ==>
    mem_bytes_at p n r.vs_memory = mem_bytes_at p n sh.vs_memory) ==>
  (!p n. b <= p /\ p+n <= b+asz /\
    (p+n <= b \/ b+32+extent <= p) ==>
    mem_bytes_at p n r.vs_memory = mem_bytes_at p n s0.vs_memory) /\
  (!aid p n. FLOOKUP s0.vs_allocas aid = SOME (p,n) /\
    aid < sa.cs_next_id /\ (p+n <= b \/ b+asz <= p) /\
    (!name lo sz. local_region ce es.scopes s0 name lo sz ==>
      p+n <= lo \/ lo+sz <= p) ==>
    mem_bytes_at p n r.vs_memory = mem_bytes_at p n s0.vs_memory)
Proof
  strip_tac >> conj_tac
  >- (rpt strip_tac >>
      `mem_bytes_at p n r.vs_memory = mem_bytes_at p n sh.vs_memory` by
        (qpat_x_assum `!p n. b <= p /\ _ ==> _` irule >> simp[] >> decide_tac) >>
      `mem_bytes_at p n sh.vs_memory = mem_bytes_at p n s0.vs_memory` by
        (qpat_x_assum `!p n. _ \/ _ ==> _` irule >> decide_tac) >> simp[]) >>
  rpt strip_tac >>
  `mem_bytes_at p n r.vs_memory = mem_bytes_at p n sh.vs_memory` by
    (qpat_x_assum `!aid p n. _ ==> _` irule >>
     conj_tac
     >- (simp[mstore_def, local_region_def, lookup_var_def] >>
         gvs[local_region_def, lookup_var_def]) >>
     conj_tac >- (qexists_tac `aid` >> simp[mstore_def] >> decide_tac) >>
     simp[]) >>
  `mem_bytes_at p n sh.vs_memory = mem_bytes_at p n s0.vs_memory` by
    (qpat_x_assum `!p n. _ \/ _ ==> _` irule >> decide_tac) >> simp[]
QED

Theorem array_header_success_post:
  sm.cs_next_var = sa.cs_next_var /\ sa.cs_next_id <= sm.cs_next_id /\
  32 + LENGTH args * type_memory_size tv <= asz /\
  sh = (mstore b (n2w (LENGTH args)) s0 with vs_inst_idx := SUC s0.vs_inst_idx) /\
  locals_kept ce es s0 sh /\ mem_word_at b sh.vs_memory = n2w (LENGTH args) /\
  (!p n. p+n <= b \/ b+32 <= p ==>
    mem_bytes_at p n sh.vs_memory = mem_bytes_at p n s0.vs_memory) ==>
  !res es' r.
  (?vs. res = INL vs /\ r.vs_current_bb = sb.cs_current_bb /\
    r.vs_inst_idx = LENGTH sb.cs_current_insts /\ expr_sim_inv ce cx env es' /\
    stmt_state_rel ctx func ce cx es' r /\
    elems_in_memory vs (b+32) tv r.vs_memory /\
    (!z w. not_fresh_at sm z /\ lookup_var z sh = SOME w ==>
      lookup_var z r = SOME w) /\
    (!aid a. FLOOKUP sh.vs_allocas aid = SOME a ==>
      FLOOKUP r.vs_allocas aid = SOME a) /\
    (!p n. b <= p /\ p+n <= b+asz /\
      (p+n <= b+32 \/ b+32+LENGTH args * type_memory_size tv <= p) ==>
      mem_bytes_at p n r.vs_memory = mem_bytes_at p n sh.vs_memory) /\
    (!aid p n. FLOOKUP sh.vs_allocas aid = SOME (p,n) /\
      aid < sm.cs_next_id /\ (p+n <= b \/ b+asz <= p) /\
      (!name lo sz. local_region ce es.scopes sh name lo sz ==>
        p+n <= lo \/ lo+sz <= p) ==>
      mem_bytes_at p n r.vs_memory = mem_bytes_at p n sh.vs_memory) /\
    locals_kept ce es sh r /\ alloca_history func r /\
    sh.vs_alloca_next <= r.vs_alloca_next) ==>
  (?vs. res = INL vs /\ r.vs_current_bb = sb.cs_current_bb /\
    r.vs_inst_idx = LENGTH sb.cs_current_insts /\ expr_sim_inv ce cx env es' /\
    stmt_state_rel ctx func ce cx es' r /\
    elems_in_memory vs (b+32) tv r.vs_memory /\
    mem_word_at b r.vs_memory = n2w (LENGTH args) /\
    (!z w. not_fresh_at sa z /\ lookup_var z s0 = SOME w ==>
      lookup_var z r = SOME w) /\
    (!aid a. FLOOKUP s0.vs_allocas aid = SOME a ==>
      FLOOKUP r.vs_allocas aid = SOME a) /\
    (!p n. b <= p /\ p+n <= b+asz /\
      (p+n <= b \/ b+32+LENGTH args * type_memory_size tv <= p) ==>
      mem_bytes_at p n r.vs_memory = mem_bytes_at p n s0.vs_memory) /\
    (!aid p n. FLOOKUP s0.vs_allocas aid = SOME (p,n) /\
      aid < sa.cs_next_id /\ (p+n <= b \/ b+asz <= p) /\
      (!name lo sz. local_region ce es.scopes s0 name lo sz ==>
        p+n <= lo \/ lo+sz <= p) ==>
      mem_bytes_at p n r.vs_memory = mem_bytes_at p n s0.vs_memory) /\
    locals_kept ce es s0 r /\ alloca_history func r /\
    s0.vs_alloca_next <= r.vs_alloca_next)
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  drule_all array_header_frames >> strip_tac >>
  `mem_bytes_at b 32 r.vs_memory = mem_bytes_at b 32 sh.vs_memory` by
    (qpat_x_assum `!p n. b <= p /\ _ ==> _` irule >> simp[] >> decide_tac) >>
  `mem_word_at b r.vs_memory = n2w (LENGTH args)` by
    metis_tac[abiStaticAggregatePropsTheory.mem_word_at_bytes] >>
  `!name lo sz. local_region ce es.scopes sh name lo sz <=>
                local_region ce es.scopes s0 name lo sz` by
    (rpt gen_tac >> irule local_region_lookup_cong >>
     simp[lookup_var_def, mstore_def]) >>
  `locals_kept ce es s0 r` by
    (fs[locals_kept_def] >> rpt gen_tac >> strip_tac >>
     irule EQ_TRANS >> qexists_tac `mem_bytes_at off len sh.vs_memory` >>
     conj_tac
     >- (qpat_x_assum `!n b sz off len. _ ==> mem_bytes_at _ _ r.vs_memory = _`
           irule >> simp[] >> metis_tac[]) >>
     qpat_x_assum `!n b sz off len. _ ==> mem_bytes_at _ _ sh.vs_memory = _`
       irule >> simp[] >> metis_tac[]) >>
  qexists_tac `vs` >> simp[] >>
  conj_tac
  >- (rpt strip_tac >> qpat_x_assum `!z w. _ ==> _` irule >>
      gvs[not_fresh_at_def, mstore_def, lookup_var_def]) >>
  gvs[mstore_def] >> metis_tac[]
QED

Theorem aggregate_make_array_body_sim_mem:
  !args ce cx env elem_ty tv stride header sa out sb es func inst x b asz s0 ctx tops.
  EVERY (\e. expr_type e = elem_ty) args /\
  evaluate_type (get_tenv cx) elem_ty = SOME tv /\
  stride = type_memory_size tv /\
  type_memory_bytes ce elem_ty = type_memory_size tv /\
  compile_make_array compile_expr ce args elem_ty stride header (Var x) sa = (out,sb) /\
  expr_sim_inv ce cx env es /\
  (!e st. MEM e args /\ expr_sim_inv ce cx env st ==>
    expr_body_pre ce cx env e st) /\
  body_inv tops ctx ce cx /\ body_exprs_mem_ok cx args /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ MEM inst (fn_insts func) /\
  inst.inst_outputs = [x] /\ inst.inst_id < sa.cs_next_id /\
  (!st. expr_sim_inv ce cx env st ==> not_local_ptr ce st.scopes x) /\
  not_fresh_at sa x /\ lookup_var x s0 = SOME (n2w b) /\
  FLOOKUP s0.vs_allocas inst.inst_id = SOME (b,asz) /\
  (if header then 32 else 0) + LENGTH args * type_memory_size tv <= asz /\
  b + asz < dimword (:256) /\
  (ce.ce_is_ctor ==>
   !name itv iv io.
     FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc io) /\
     FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
       | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
     regions_disjoint io (type_memory_size itv) b
       ((if header then 32 else 0) + LENGTH args * type_memory_size tv)) /\
  stmt_state_rel ctx func ce cx es s0 /\ alloca_history func s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  out = Var x /\
  gas_outcome T (cx_tops cx) (ctx,func) (eval_exprs cx args) (es,s0)
    (\res es' r. ?vs. res = INL vs /\ r.vs_current_bb = sb.cs_current_bb /\
      r.vs_inst_idx = LENGTH sb.cs_current_insts /\ expr_sim_inv ce cx env es' /\
      stmt_state_rel ctx func ce cx es' r /\
      elems_in_memory vs (b+(if header then 32 else 0)) tv r.vs_memory /\
      (header ==> mem_word_at b r.vs_memory = n2w (LENGTH args)) /\
      (!z w. not_fresh_at sa z /\ lookup_var z s0 = SOME w ==>
        lookup_var z r = SOME w) /\
      (!aid a. FLOOKUP s0.vs_allocas aid = SOME a ==>
        FLOOKUP r.vs_allocas aid = SOME a) /\
      (!p n. b <= p /\ p+n <= b+asz /\
        (p+n <= b \/ b+(if header then 32 else 0)+LENGTH args * type_memory_size tv <= p) ==>
        mem_bytes_at p n r.vs_memory = mem_bytes_at p n s0.vs_memory) /\
      (!aid p n. FLOOKUP s0.vs_allocas aid = SOME (p,n) /\
        aid < sa.cs_next_id /\ (p+n <= b \/ b+asz <= p) /\
        (!name lo sz. local_region ce es.scopes s0 name lo sz ==>
          p+n <= lo \/ lo+sz <= p) ==>
        mem_bytes_at p n r.vs_memory = mem_bytes_at p n s0.vs_memory) /\
      locals_kept ce es s0 r /\ alloca_history func r /\
      s0.vs_alloca_next <= r.vs_alloca_next)
    (\res es' exit. ?exc. res = INR exc /\
      expr_exit (INR exc : eval_result + exception) exit)
Proof
  rpt gen_tac >> strip_tac >> reverse (Cases_on `header`)
  >- (gvs[compile_make_array_def, comp_ignore_bind_def, comp_bind_def,
          comp_return_def] >>
      mp_tac (SRULE [] (Q.INST [`header` |-> `F`, `idx` |-> `0`, `off` |-> `0`]
        (SPEC_ALL aggregate_make_array_elems_body_sim_mem))) >>
      (impl_tac >- (gvs[] >> metis_tac[])) >> simp[]) >>
  gvs[compile_make_array_def, comp_ignore_bind_def, comp_bind_def, AllCaseEqs()] >>
  Cases_on `emit_void MSTORE [Var x; Lit (n2w (LENGTH args))] sa` >>
  rename1 `emit_void MSTORE _ sa = (u,sm)` >> Cases_on `u` >> gvs[] >>
  `ci_mono sa sm` by metis_tac[ci_mono_emit_void, pairTheory.SND] >>
  `ci_mono sm sb` by
    (drule compile_make_array_elems_as_tuple >>
     disch_then (qspecl_then [`T`, `compile_expr`, `ce`, `Var x`, `0`] mp_tac) >>
     strip_tac >> gvs[] >>
     metis_tac[ci_mono_compile_make_tuple_cfn, compile_expr_ci_mono, pairTheory.SND]) >>
  `cs_extends sa sm /\ cs_extends sm sb` by gvs[ci_mono_def] >>
  drule_all fn_has_code_split >> strip_tac >>
  qabbrev_tac `sh = mstore b (n2w (LENGTH args)) s0 with
    vs_inst_idx := SUC s0.vs_inst_idx` >>
  `32 <= asz /\ not_local_ptr ce es.scopes x` by (simp[] >> decide_tac) >>
  drule array_header_mem_entry >>
  disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  disch_then (drule_at (Pat `stmt_state_rel _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `FLOOKUP _.vs_allocas _ = SOME (_,_)`)) >>
  disch_then (qspec_then `sh` mp_tac) >>
  (impl_tac >-
    (simp[Abbr `sh`] >> rpt strip_tac >> first_x_assum drule_all >>
     simp[compileEnvTheory.regions_disjoint_def] >> decide_tac)) >> strip_tac >>
  mp_tac (Q.INST [`header` |-> `T`, `idx` |-> `0`, `off` |-> `32`,
     `sa` |-> `sm`, `s0` |-> `sh`] (SPEC_ALL aggregate_make_array_elems_body_sim_mem)) >>
  (impl_tac >-
    (simp[] >> rpt strip_tac >> first_x_assum drule_all >>
     simp[compileEnvTheory.regions_disjoint_def] >> decide_tac)) >>
  strip_tac >> conj_tac >- simp[] >>
  irule bodyDeclMemoryComposeTheory.gas_outcome_zero_prefix_mem >>
  qexists_tac `sh` >> conj_tac >- fs[gas_marked_path_def] >>
  drule struct_gas_outcome_post >> disch_then irule >>
  CONV_TAC (DEPTH_CONV BETA_CONV) >> rpt gen_tac >> strip_tac >>
  pure_rewrite_tac [AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM] >>
  irule (SRULE [AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM]
    array_header_success_post) >>
  drule array_header_emit_entry >>
  disch_then (qspecl_then [`x`, `ce`] strip_assume_tac) >>
  simp[] >> conj_tac
  >- (qexists_tac `sm` >>
      gvs[Abbr `sh`, AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM] >>
      metis_tac[]) >>
  gvs[Abbr `sh`, AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM] >>
  metis_tac[]
QED
