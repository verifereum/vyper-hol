(* Layout adapters for the checked allocated traversal. *)
Theory bodyMemAggregateAdapters
Ancestors
  bodyMemAggregateLoops exprSimAggregateLayout exprSimAggregateLoops
  gasOutcome gasSummary valueEncoding vyperTypeABI bodyDeclWordMemory
  exprLowering compileEnv loweringStateRelDefs exprLoweringProps emitHelperProps loweringSlice
  localPtrsProps venomState venomMemDefs stmtSimProps stmtSimDefs
  stmtSimDeclCompose gasSummaryCompose fragGasMode fragGasPathMem fragExec
  exprSimDefs loweringPosts abiStaticAggregateProps exprBopSimProps

Theorem aggregate_struct_fields_sim_mem:
  !fields ce cx env ty off sa out sb es tvs func inst x b asz s0 ctx tops.
  EVERY (\(name,e).
    ALOOKUP (get_struct_fields ce.ce_struct_fields
      (case ty of StructT nsid => nsid_to_string nsid | _ => "")) name =
      SOME (expr_type e,type_memory_bytes ce (expr_type e))) fields /\
  compile_struct_lit compile_expr ce ty fields (Var x) off sa = (out,sb) /\
  OPT_MMAP (evaluate_type (get_tenv cx)) (MAP expr_type (MAP SND fields)) = SOME tvs /\
  expr_sim_inv ce cx env es /\
  (!e st. MEM e (MAP SND fields) /\ expr_sim_inv ce cx env st ==>
    expr_body_pre ce cx env e st) /\
  body_inv tops ctx ce cx /\ body_exprs_mem_ok cx (MAP SND fields) /\
  (!e. MEM e (MAP SND fields) ==>
     int_calls_expr e = [] \/ lowered_value_type ce e = expr_type e) /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ MEM inst (fn_insts func) /\
  inst.inst_outputs = [x] /\ inst.inst_id < sa.cs_next_id /\
  (!st. expr_sim_inv ce cx env st ==> not_local_ptr ce st.scopes x) /\
  not_fresh_at sa x /\ lookup_var x s0 = SOME (n2w b) /\
  FLOOKUP s0.vs_allocas inst.inst_id = SOME (b,asz) /\
  off + type_memory_size_list tvs <= asz /\ b + asz < dimword (:256) /\
  (ce.ce_is_ctor ==>
   !name itv iv io.
     FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc io) /\
     FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
       | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
     regions_disjoint io (type_memory_size itv) (b+off) (type_memory_size_list tvs)) /\
  stmt_state_rel ctx func ce cx es s0 /\ alloca_history func s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  out = Var x /\
  gas_outcome T (cx_tops cx) (ctx,func) (eval_exprs cx (MAP SND fields)) (es,s0)
    (\res es' r. ?vs. res = INL vs /\ r.vs_current_bb = sb.cs_current_bb /\
      r.vs_inst_idx = LENGTH sb.cs_current_insts /\ expr_sim_inv ce cx env es' /\
      stmt_state_rel ctx func ce cx es' r /\
      fields_in_memory (ZIP (MAP FST fields,vs))
        (ZIP (MAP FST fields,tvs)) (b+off) r.vs_memory /\
      (!z w. not_fresh_at sa z /\ lookup_var z s0 = SOME w ==>
        lookup_var z r = SOME w) /\
      (!aid a. FLOOKUP s0.vs_allocas aid = SOME a ==>
        FLOOKUP r.vs_allocas aid = SOME a) /\
      (!p n. b <= p /\ p+n <= b+asz /\
        (p+n <= b+off \/ b+off+type_memory_size_list tvs <= p) ==>
        mem_bytes_at p n r.vs_memory = mem_bytes_at p n s0.vs_memory) /\
      (!aid p n. FLOOKUP s0.vs_allocas aid = SOME (p,n) /\
        aid < sa.cs_next_id /\ (p+n <= b \/ b+asz <= p) /\
        (!name lo sz. local_region ce es.scopes s0 name lo sz ==>
          p+n <= lo \/ lo+sz <= p) ==>
        mem_bytes_at p n r.vs_memory = mem_bytes_at p n s0.vs_memory) /\
      locals_kept ce es es' s0 r /\ alloca_history func r /\
      s0.vs_alloca_next <= r.vs_alloca_next)
    (\res es' exit. ?exc. res = INR exc /\
      expr_exit (INR exc : eval_result + exception) exit)
Proof
  rpt gen_tac >> strip_tac >>
  drule exprSimAggregateLayoutTheory.compile_struct_lit_as_tuple >>
  disch_then (qspecl_then [`compile_expr`, `Var x`, `off`] assume_tac) >>
  gvs[] >>
  drule aggregate_make_tuple_sim_mem >>
  disch_then drule >>
  disch_then (drule_at (Pat `body_inv _ _ _ _`)) >>
  disch_then (drule_at (Pat `expr_sim_inv _ _ _ _`)) >>
  disch_then (drule_at (Pat `FLOOKUP _.vs_allocas _ = SOME (_,_)`)) >>
  disch_then (qspecl_then [`es`, `func`] mp_tac) >>
  (impl_tac >- (simp[] >> first_assum ACCEPT_TAC)) >> strip_tac >> simp[] >>
  drule vyperTypeABITheory.OPT_MMAP_LENGTH >> simp[] >> strip_tac >>
  irule struct_gas_outcome_post >>
  goal_assum (drule_at Any) >>
  BETA_TAC >> rpt strip_tac >> qexists_tac `vs` >> gvs[] >> simp[] >>
  conj_tac >- (irule struct_tuple_memory_post >> simp[]) >>
  conj_tac >> first_assum ACCEPT_TAC
QED

Theorem aggregate_make_array_elems_sim_mem:
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
  (!e. MEM e args ==>
     int_calls_expr e = [] \/ lowered_value_type ce e = expr_type e) /\
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
      locals_kept ce es es' s0 r /\ alloca_history func r /\
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
  `compile_make_tuple compile_expr ce args (MAP expr_type args) (Var x) off sa =
     (out,sb)` by
    (gvs[] >> metis_tac[]) >>
  drule aggregate_make_tuple_sim_mem >> disch_then drule >>
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

Theorem aggregate_make_array_sim_mem:
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
  (!e. MEM e args ==>
     int_calls_expr e = [] \/ lowered_value_type ce e = expr_type e) /\
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
      locals_kept ce es es' s0 r /\ alloca_history func r /\
      s0.vs_alloca_next <= r.vs_alloca_next)
    (\res es' exit. ?exc. res = INR exc /\
      expr_exit (INR exc : eval_result + exception) exit)
Proof
  rpt gen_tac >> strip_tac >> reverse (Cases_on `header`)
  >- (gvs[compile_make_array_def, comp_ignore_bind_def, comp_bind_def,
          comp_return_def] >>
      mp_tac (SRULE [] (Q.INST [`header` |-> `F`, `idx` |-> `0`, `off` |-> `0`]
        (SPEC_ALL aggregate_make_array_elems_sim_mem))) >>
      (impl_tac >- (gvs[] >> metis_tac[])) >> simp[]) >>
  gvs[compile_make_array_def, comp_ignore_bind_def, comp_bind_def,
      AllCaseEqs()] >>
  Cases_on `emit_void MSTORE [Var x; Lit (n2w (LENGTH args))] sa` >>
  rename1 `emit_void MSTORE _ sa = (u,sm)` >> Cases_on `u` >> gvs[] >>
  `ci_mono sa sm` by
    metis_tac[ci_mono_emit_void, pairTheory.SND] >>
  `ci_mono sm sb` by
    (drule compile_make_array_elems_as_tuple >>
     disch_then (qspecl_then [`T`, `compile_expr`, `ce`, `Var x`, `0`] mp_tac) >>
     strip_tac >> gvs[] >>
     metis_tac[ci_mono_compile_make_tuple_cfn, compile_expr_ci_mono, pairTheory.SND]) >>
  `cs_extends sa sm /\ cs_extends sm sb` by gvs[ci_mono_def] >>
  drule_all fn_has_code_split >> strip_tac >>
  qmatch_goalsub_abbrev_tac `gas_outcome T _ _ _ _ post exitrel` >>
  qabbrev_tac `sh = mstore b (n2w (LENGTH args)) s0 with
    vs_inst_idx := SUC s0.vs_inst_idx` >>
  `sm.cs_current_bb = sa.cs_current_bb /\
   LENGTH sm.cs_current_insts = SUC (LENGTH sa.cs_current_insts) /\
   sm.cs_next_id = SUC sa.cs_next_id /\ sm.cs_next_var = sa.cs_next_var` by
    gvs[emitHelperTheory.emit_void_def, comp_bind_def, fresh_id_def,
        comp_ignore_bind_def, comp_return_def, emit_def] >>
  `gas_marked_path T ctx func s0 0 (OK sh) /\ alloca_history func sh` by
    suspend "header_path" >>
  `stmt_state_rel ctx func ce cx es (mstore b (n2w (LENGTH args)) s0) /\
   locals_kept ce es es s0 (mstore b (n2w (LENGTH args)) s0) /\
   mem_word_at b (mstore b (n2w (LENGTH args)) s0).vs_memory = n2w (LENGTH args) /\
   (!p n. p+n <= b \/ b+32 <= p ==>
     mem_bytes_at p n (mstore b (n2w (LENGTH args)) s0).vs_memory =
     mem_bytes_at p n s0.vs_memory)` by
    suspend "header_boundary" >>
  `stmt_state_rel ctx func ce cx es sh /\ ~sh.vs_halted /\
   sh.vs_current_bb = sm.cs_current_bb /\
   sh.vs_inst_idx = LENGTH sm.cs_current_insts` by
    simp[Abbr `sh`, stmt_state_rel_inst_idx, mstore_def] >>
  `local_ptrs_reserved ce sm /\ not_fresh_at sm x /\
   inst.inst_id < sm.cs_next_id` by
    (conj_tac
     >- (qpat_x_assum `local_ptrs_reserved ce sa` mp_tac >>
         pure_rewrite_tac[local_ptrs_reserved_def, not_fresh_at_def] >>
         qpat_x_assum `sm.cs_next_var = _` (fn th => rewrite_tac[th])) >>
     conj_tac
     >- (qpat_x_assum `not_fresh_at sa x` mp_tac >>
         pure_rewrite_tac[not_fresh_at_def] >>
         qpat_x_assum `sm.cs_next_var = _` (fn th => rewrite_tac[th])) >>
     decide_tac) >>
  mp_tac (Q.INST [`header` |-> `T`, `idx` |-> `0`, `off` |-> `32`,
     `sa` |-> `sm`, `s0` |-> `sh`] (SPEC_ALL aggregate_make_array_elems_sim_mem)) >>
  (impl_tac >-
    (qpat_x_assum `Abbrev (post = _)` kall_tac >>
     qpat_x_assum `Abbrev (exitrel = _)` kall_tac >>
     `lookup_var x sh = SOME (n2w b) /\
      FLOOKUP sh.vs_allocas inst.inst_id = SOME (b,asz)` by
       (simp[Abbr `sh`, mstore_def, lookup_var_def] >>
        gvs[lookup_var_def]) >>
     simp[] >> rpt strip_tac >> first_x_assum drule_all >>
     simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac)) >>
  strip_tac >> conj_tac >- simp[] >>
  irule bodyDeclMemoryComposeTheory.gas_outcome_zero_prefix_mem >>
  qexists_tac `sh` >> conj_tac
  >- fs[gas_marked_path_def] >>
  qpat_x_assum `gas_outcome _ _ _ _ _ _ _` mp_tac >>
  pure_rewrite_tac[gas_outcome_def, gas_summary_at_def] >>
  strip_tac
  >- (qexists_tac `marks` >> disj1_tac >>
      qexistsl_tac [`res`, `es_end`, `r`] >> simp[] >>
      disj1_tac >> suspend "array_post_transport") >>
  metis_tac[]
QED

Resume aggregate_make_array_sim_mem[header_path]:
  `alloca_inv s0` by fs[stmt_state_rel_def] >>
  `b + 32 <= s0.vs_alloca_next` by
    (fs[alloca_inv_def, alloca_next_valid_def] >>
     first_x_assum drule >> decide_tac) >>
  `b < dimword (:256)` by decide_tac >>
  drule annassign_word_mstore_path_mem >>
  disch_then (drule_at (Pat `fn_has_code _ _ _`)) >>
  disch_then (qspecl_then [`n2w (LENGTH args)`, `n2w b`, `s0`, `ctx`] mp_tac) >>
  simp[eval_operand_def, Abbr `sh`, gas_marked_path_def]
QED

Resume aggregate_make_array_sim_mem[array_post_transport]:
  qpat_x_assum `EVERY _ _` kall_tac >>
  qpat_x_assum `evaluate_type _ _ = _` kall_tac >>
  qpat_x_assum `type_memory_bytes _ _ = _` kall_tac >>
  qpat_x_assum `compile_make_array_elems _ _ _ _ _ _ _ _ _ = _` kall_tac >>
  qpat_x_assum `!e st. MEM e args /\ expr_sim_inv ce cx env st ==> _` kall_tac >>
  qpat_x_assum `body_inv _ _ _ _` kall_tac >>
  qpat_x_assum `body_exprs_mem_ok _ _` kall_tac >>
  qpat_x_assum `!e. MEM e args ==> _` kall_tac >>
  qpat_x_assum `ce.ce_is_ctor ==> _` kall_tac >>
  gvs[Abbr `post`] >>
  conj_tac >- suspend "header_word" >>
  conj_tac >- suspend "variables" >>
  conj_tac >- suspend "allocas" >>
  conj_tac >- suspend "inner_frame" >>
  conj_tac >- suspend "outer_frame" >>
  conj_tac >- suspend "locals" >>
  gvs[Abbr `sh`, mstore_def]
QED

Resume aggregate_make_array_sim_mem[header_word]:
  `mem_bytes_at b 32 t.vs_memory = mem_bytes_at b 32 sh.vs_memory` by
    (qpat_x_assum `!p n. b <= p /\ _ ==> _` irule >> simp[]) >>
  `mem_word_at b t.vs_memory = mem_word_at b sh.vs_memory` by
    simp[mem_word_at_bytes] >>
  simp[Abbr `sh`]
QED

Resume aggregate_make_array_sim_mem[variables]:
  rpt strip_tac >> qpat_x_assum `!z w. not_fresh_at sm z /\ _ ==> _` irule >>
  simp[not_fresh_at_def, Abbr `sh`, mstore_def, lookup_var_def] >>
  gvs[not_fresh_at_def, lookup_var_def]
QED

Resume aggregate_make_array_sim_mem[allocas]:
  rpt strip_tac >> first_x_assum irule >> simp[Abbr `sh`, mstore_def]
QED

Resume aggregate_make_array_sim_mem[inner_frame]:
  rpt strip_tac >>
  `mem_bytes_at p n t.vs_memory = mem_bytes_at p n sh.vs_memory` by
    (qpat_x_assum `!p n. b <= p /\ _ ==> _` irule >> simp[] >> decide_tac) >>
  `mem_bytes_at p n (mstore b (n2w (LENGTH args)) s0).vs_memory =
   mem_bytes_at p n s0.vs_memory` by
    (qpat_x_assum `!p n. _ \/ _ ==> _` irule >> decide_tac) >>
  gvs[Abbr `sh`]
QED

Resume aggregate_make_array_sim_mem[outer_frame]:
  rpt strip_tac >>
  `mem_bytes_at p n t.vs_memory = mem_bytes_at p n sh.vs_memory` by
    (qpat_x_assum `!aid p n. FLOOKUP sh.vs_allocas aid = _ /\ _ ==> _` irule >>
     conj_tac
     >- (simp[Abbr `sh`, mstore_def, local_region_def, lookup_var_def] >>
         gvs[local_region_def, lookup_var_def]) >>
     conj_tac >- (qexists_tac `aid` >> simp[Abbr `sh`, mstore_def]) >>
     simp[]) >>
  `mem_bytes_at p n (mstore b (n2w (LENGTH args)) s0).vs_memory =
   mem_bytes_at p n s0.vs_memory` by
    (qpat_x_assum `!p n. _ \/ _ ==> _` irule >> decide_tac) >>
  gvs[Abbr `sh`]
QED

Resume aggregate_make_array_sim_mem[locals]:
  irule locals_kept_trans >> qexistsl_tac [`es`, `sa`, `sh`] >>
  simp[Abbr `sh`, mstore_def, lookup_var_def]
QED

Resume aggregate_make_array_sim_mem[header_boundary]:
  irule array_header_store_boundary >>
  simp[] >> conj_tac
  >- (rpt strip_tac >> first_x_assum drule_all >>
      simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
  qexistsl_tac [`asz`, `inst`, `x`] >> simp[]
QED

Finalise aggregate_make_array_sim_mem
