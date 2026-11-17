(* Allocated aggregate traversal, with checked memory accesses. *)
Theory bodyMemAggregateLoops
Ancestors
  bodyMemAggregateLoopBoundary bodyMemAggregateTraversal bodyMemoryPreds
  exprSimAggregateChildren exprSimAggregateLayout exprSimHyps
  exprLowering exprLoweringProps exprOperandVar compileEnv loweringStateRelDefs loweringPosts
  gasOutcome gasSummary exprSimWordArgs vyperState vyperInterpreter
  freshWrites valueEncoding valueEncodingDefs fragExec exprSimDefs exprSimMemDefs
  fragGasMode fragGasPath fragGasPathMem exprSimAggregateLoops valueEncodingProofs
  exprSimAggregateNestedStore bodyMemAggregatePhysicalRead
  bodyMemAggregateConsContinuation bodyMemAggregateBodyContinuation
  bodyMemAggregateHeadContinuation
  bodySim bodyMemAggregateSide
  typedCopyRankPathMem typedMemoryCopy wideningZeroLayout
  exprSimHypsDefs vyperTypeSystem vyperTypeInvariants
  memoryLayoutDefs memoryLayoutSource memoryLayoutRel memoryValueEncoding
  exprSimBufferStore bodyMemAggregatePath fragGasPathFrameMem
  exprSimProps context typedCopyCompatibility vyperTypeArgFits
Libs
  monadsyntax

(* aggregate_make_tuple_sim_mem at the declared member types tys, as
   exprSimAggregateLoops' aggregate_make_tuple_flat_sim. *)
Theorem aggregate_make_tuple_flat_sim_mem:
  !st0 args tys ce cx env off sa out sb es tvs func inst x b asz s0 ctx tops.
  compile_make_tuple compile_expr ce args tys (Var x) off sa = (out,sb) /\
  LIST_REL (\t e. arg_type_fits (expr_type e) t) tys args /\
  LIST_REL (\t e. t = expr_type e \/
    is_bytestring_type t /\ is_bytestring_type (expr_type e)) tys args /\
  OPT_MMAP (evaluate_type (get_tenv cx)) tys = SOME tvs /\
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
  off + type_memory_size_list tvs <= asz /\ b + asz < dimword (:256) /\
  (ce.ce_is_ctor ==>
   !name itv iv io.
     FLOOKUP ce.ce_module_vars (ce.ce_module,name) =
       SOME (ImmutableLoc io) /\
     FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
       | SOME imms => get_source_immutables ce.ce_module imms) name =
       SOME (itv,iv) ==>
     regions_disjoint io (type_memory_size itv) (b+off)
       (type_memory_size_list tvs)) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func ce cx es s0 /\
    storage_well_formed_on cx es (FST H)) /\ alloca_history func s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  out = Var x /\
  gas_outcome T (cx_tops cx) (ctx,func) cx st0 (eval_exprs cx args) (es,s0)
    (\H res es' r. ?vs. res = INL vs /\ r.vs_current_bb = sb.cs_current_bb /\
      r.vs_inst_idx = LENGTH sb.cs_current_insts /\ expr_sim_inv ce cx env es' /\
      stmt_state_rel H ctx func ce cx es' r /\
      storage_well_formed_on cx es' (FST H) /\
      tuple_in_memory vs tvs (b+off) r.vs_memory /\
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
      locals_kept ce es es' s0 r /\
      alloca_history func r /\ s0.vs_alloca_next <= r.vs_alloca_next /\
      (~EXISTS expr_has_effect args ==>
        (!n lb lsz. local_region ce es.scopes s0 n lb lsz ==>
          mem_bytes_at lb lsz r.vs_memory = mem_bytes_at lb lsz s0.vs_memory) /\
        !p n. (p + n <= b \/ b + asz <= p) /\
          (!i c sz. MEM i (fn_insts func) /\ i.inst_opcode = ALLOCA /\
             sa.cs_next_id <= i.inst_id /\
             FLOOKUP r.vs_allocas i.inst_id = SOME (c,sz) ==>
             regions_disjoint p n c sz) ==>
          mem_bytes_at p n r.vs_memory = mem_bytes_at p n s0.vs_memory))
    (\H res es' exit. ?exc. res = INR exc /\
      expr_exit (INR exc : eval_result + exception) exit /\
      exprSimDefs$halt_exit H cx es' (INR exc : eval_result + exception) exit)
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (SPEC_ALL aggregate_make_tuple_body_sim_mem) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then ACCEPT_TAC
QED

(* The equal-type case of aggregate_make_tuple_flat_sim_mem. *)
Theorem aggregate_make_tuple_sim_mem:
  !st0 args ce cx env off sa out sb es tvs func inst x b asz s0 ctx tops.
  compile_make_tuple compile_expr ce args (MAP expr_type args) (Var x) off sa =
    (out,sb) /\
  OPT_MMAP (evaluate_type (get_tenv cx)) (MAP expr_type args) = SOME tvs /\
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
  off + type_memory_size_list tvs <= asz /\ b + asz < dimword (:256) /\
  (ce.ce_is_ctor ==>
   !name itv iv io.
     FLOOKUP ce.ce_module_vars (ce.ce_module,name) =
       SOME (ImmutableLoc io) /\
     FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
       | SOME imms => get_source_immutables ce.ce_module imms) name =
       SOME (itv,iv) ==>
     regions_disjoint io (type_memory_size itv) (b+off)
       (type_memory_size_list tvs)) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func ce cx es s0 /\
    storage_well_formed_on cx es (FST H)) /\ alloca_history func s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  out = Var x /\
  gas_outcome T (cx_tops cx) (ctx,func) cx st0 (eval_exprs cx args) (es,s0)
    (\H res es' r. ?vs. res = INL vs /\ r.vs_current_bb = sb.cs_current_bb /\
      r.vs_inst_idx = LENGTH sb.cs_current_insts /\ expr_sim_inv ce cx env es' /\
      stmt_state_rel H ctx func ce cx es' r /\
      storage_well_formed_on cx es' (FST H) /\
      tuple_in_memory vs tvs (b+off) r.vs_memory /\
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
      locals_kept ce es es' s0 r /\
      alloca_history func r /\ s0.vs_alloca_next <= r.vs_alloca_next /\
      (~EXISTS expr_has_effect args ==>
        (!n lb lsz. local_region ce es.scopes s0 n lb lsz ==>
          mem_bytes_at lb lsz r.vs_memory = mem_bytes_at lb lsz s0.vs_memory) /\
        !p n. (p + n <= b \/ b + asz <= p) /\
          (!i c sz. MEM i (fn_insts func) /\ i.inst_opcode = ALLOCA /\
             sa.cs_next_id <= i.inst_id /\
             FLOOKUP r.vs_allocas i.inst_id = SOME (c,sz) ==>
             regions_disjoint p n c sz) ==>
          mem_bytes_at p n r.vs_memory = mem_bytes_at p n s0.vs_memory))
    (\H res es' exit. ?exc. res = INR exc /\
      expr_exit (INR exc : eval_result + exception) exit /\
      exprSimDefs$halt_exit H cx es' (INR exc : eval_result + exception) exit)
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  mp_tac (Q.INST [`tys` |-> `MAP expr_type args`] (SPEC_ALL aggregate_make_tuple_flat_sim_mem)) >>
  impl_tac
  >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      simp[listTheory.LIST_REL_MAP1] >> irule listTheory.EVERY2_refl >> simp[]) >>
  simp[]
QED

Theorem aggregate_nested_store_mem:
  compile_store_memory ce op (Var x) dty (lowered_value_type ce e) su = ((),sb) /\
  arg_type_fits (expr_type e) dty /\ dty <> expr_type e /\
  ~is_bytestring_type dty /\ acyclic_struct_metadata ce.ce_struct_fields /\
  expr_body_pre ce cx env e es /\
  (do res <- eval_expr cx e; read_result cx res od) es = (INL v,es') /\
  not_fresh_at sm x /\ lookup_var x r = SOME w /\
  sm.cs_next_var <= su.cs_next_var /\
  (!z. op = Var z ==> not_fresh_at su z) /\
  local_ptrs_reserved ce sm /\ local_ptrs_reserved ce su /\
  evaluate_type (get_tenv cx) dty = SOME tv /\
  value_has_type tv v /\ val_wf tv v /\
  type_memory_bytes ce dty = type_memory_size tv /\
  type_memory_size tv < dimword (:256) /\
  stmt_state_rel H ctx func ce cx es' r /\
  FLOOKUP r.vs_allocas did = SOME (b,k) /\ did < sa.cs_next_id /\
  b <= w2n w /\ w2n w + type_memory_size tv <= b+k /\
  w2n w + type_memory_size tv < dimword (:256) /\
  (!name a len. local_region ce es'.scopes r name a len ==>
    a+len <= w2n w \/ w2n w + type_memory_size tv <= a) /\
  (ce.ce_is_ctor ==> !name itv iv off.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc off) /\
    FLOOKUP (case ALOOKUP es'.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
    regions_disjoint off (type_memory_size itv) (w2n w) (type_memory_size tv)) /\
  expr_post H ctx func ce cx e es' (sa with cs_next_var := sm.cs_next_var)
    su r es' v op s /\
  (!stv sw. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME stv /\
    eval_operand op s = SOME sw ==>
    type_memory_size stv = 0 \/ w2n sw + type_memory_size stv <= s.vs_alloca_next) /\
  alloca_history func s /\ fn_has_code su sb func /\ fn_inst_ids_distinct func /\
  ~s.vs_halted /\ s.vs_current_bb = su.cs_current_bb /\
  s.vs_inst_idx = LENGTH su.cs_current_insts ==>
  ?q. gas_path_mem ctx func s 0 (OK q) /\
    ~q.vs_halted /\ q.vs_current_bb = sb.cs_current_bb /\
    q.vs_inst_idx = LENGTH sb.cs_current_insts /\
    val_in_memory tv v (w2n w) q.vs_memory /\
    stmt_state_rel H ctx func ce cx es' q /\
    (!z a. not_fresh_at sm z /\ lookup_var z r = SOME a ==> lookup_var z q = SOME a) /\
    (!aid a. FLOOKUP r.vs_allocas aid = SOME a ==> FLOOKUP q.vs_allocas aid = SOME a) /\
    (!aid off sz a len.
      FLOOKUP r.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
      (!name b k. local_region ce es'.scopes r name b k ==>
        off+sz <= b \/ b+k <= off) /\
      off <= a /\ a+len <= off+sz /\
      (a+len <= w2n w \/ w2n w+type_memory_size tv <= a) ==>
      mem_bytes_at a len q.vs_memory = mem_bytes_at a len r.vs_memory) /\
    locals_kept ce es' es' r q /\
    (!aid a. FLOOKUP s.vs_allocas aid = SOME a ==>
      FLOOKUP q.vs_allocas aid = SOME a) /\
    (!a len. a + len <= w2n w \/ w2n w + type_memory_size tv <= a ==>
      mem_bytes_at a len q.vs_memory = mem_bytes_at a len s.vs_memory) /\
    alloca_history func q /\ q.vs_alloca_next = s.vs_alloca_next /\
    q.vs_accounts = s.vs_accounts /\ q.vs_transient = s.vs_transient /\
    q.vs_requests = s.vs_requests /\ q.vs_call_ctx = s.vs_call_ctx
Proof
  strip_tac >>
  `well_typed_expr env e /\ expr_sim_inv ce cx env es` by
    fs[expr_body_pre_def] >>
  `type_widens_to (get_tenv cx) (expr_type e) dty` by
    simp[type_widens_to_def, well_formed_type_def] >>
  `~is_word_type dty` by metis_tac[type_widens_to_word] >>
  `~is_word_type (expr_type e)` by metis_tac[return_source_word_widens_eq] >>
  `~is_bytestring_type (expr_type e)` by metis_tac[type_widens_from_bytestring] >>
  `lowered_value_type ce e = post_value_type ce e` by
    metis_tac[aggregate_nested_lowered_post] >>
  `type_widens_to (get_tenv cx) (post_value_type ce e) (expr_type e)` by
    (drule_all post_value_type_widens >>
     fs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def]) >>
  `type_widens_to (get_tenv cx) (post_value_type ce e) dty` by
    metis_tac[typedCopyCompatibilityTheory.type_widens_to_trans] >>
  `~is_word_type (post_value_type ce e) /\
   ~is_bytestring_type (post_value_type ce e)` by
    metis_tac[return_source_word_widens_eq, type_widens_from_bytestring] >>
  `lookup_var x s = SOME w` by metis_tac[expr_post_rebased_lookup] >>
  `not_fresh_at su x` by metis_tac[not_fresh_at_mono] >>
  `stmt_state_rel H ctx func ce cx es' s /\
   FLOOKUP s.vs_allocas did = SOME (b,k)` by fs[expr_post_def] >>
  `alloca_inv s` by fs[stmt_state_rel_def, loweringStateRelDefsTheory.state_rel_def] >>
  `!name a len. local_region ce es'.scopes s name a len ==>
    a+len <= w2n w \/ w2n w + type_memory_size tv <= a` by
    (rpt strip_tac >>
     `local_region ce es'.scopes r name a len` by
       (irule local_region_frame >> conj_tac
        >- (qexists `func` >>
            fs[stmt_state_rel_def, loweringStateRelDefsTheory.state_rel_def]) >>
        qexistsl_tac [`sm`, `es'.scopes`, `s`] >> simp[] >>
        metis_tac[expr_post_rebased_lookup]) >>
     first_x_assum drule >> simp[arithmeticTheory.ADD_COMM]) >>
  drule_all aggregate_child_physical_encoding >> strip_tac >>
  `type_memory_size stv <> 0` by
    (strip_tac >>
     `post_value_type ce e = dty` by metis_tac[type_widens_to_zero_layout] >>
     `?etv. evaluate_type (get_tenv cx) (expr_type e) = SOME etv` by
       metis_tac[type_widens_to_value_has_type] >>
     `post_value_type ce e = expr_type e` by metis_tac[type_widens_to_zero_layout] >>
     gvs[]) >>
  `w2n sw + type_memory_size stv <= s.vs_alloca_next` by metis_tac[] >>
  `w2n w + type_memory_size tv <= s.vs_alloca_next` by
    (`b+k <= s.vs_alloca_next` by
       (fs[venomMemDefsTheory.alloca_inv_def,
           venomMemDefsTheory.alloca_next_valid_def] >> metis_tac[]) >>
     decide_tac) >>
  `w2n sw + type_memory_size stv < dimword (:256) /\
   (w2n sw + type_memory_size stv <= w2n w \/
    w2n w + type_memory_size tv <= w2n sw)` by
    (`expr_val_at ce cx (post_value_type ce e)
       (sa with cs_next_var := sm.cs_next_var) su es' v op s` by
       fs[expr_post_def] >>
     irule aggregate_physical_source_slot_bounds >>
     goal_assum (drule_at (Pat `expr_val_at _ _ _ _ _ _ _ _ _`)) >>
     goal_assum (drule_at (Pat `type_widens_to _ _ dty`)) >>
     goal_assum (drule_at (Pat `stmt_state_rel H _ _ _ _ _ s`)) >>
     goal_assum (drule_at (Pat `FLOOKUP _ _ = SOME (b,k)`)) >>
     simp[arithmeticTheory.ADD_COMM] >>
     first_assum (ACCEPT_TAC o SRULE [arithmeticTheory.ADD_COMM])) >>
  `?q. gas_path_mem ctx func s 0 (OK q) /\ ~q.vs_halted /\
     q.vs_current_bb = sb.cs_current_bb /\
     q.vs_inst_idx = LENGTH sb.cs_current_insts /\
     val_in_memory tv v (w2n w) q.vs_memory /\
     (!a len. a+len <= w2n w \/ w2n w+type_memory_size tv <= a ==>
       mem_bytes_at a len q.vs_memory = mem_bytes_at a len s.vs_memory) /\
     (q with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
       vs_prev_bb := s.vs_prev_bb; vs_current_bb := s.vs_current_bb;
       vs_inst_idx := s.vs_inst_idx|>) = s /\
     (!z. not_fresh_at su z ==> lookup_var z q = lookup_var z s)` by
    (Cases_on `dty = post_value_type ce e \/
       tuple_memory_layout_eq dty (post_value_type ce e)`
     >- suspend "bulk" >>
     pop_assum (strip_assume_tac o SRULE [DE_MORGAN_THM]) >>
     `compile_store_memory_typed ce (Var x) dty op
        (post_value_type ce e) su = ((),sb)` by
       (qpat_x_assum `compile_store_memory _ _ _ _ _ _ = _` mp_tac >>
        asm_simp_tac bool_ss [compile_store_memory_def]) >>
     `sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
      (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
        ALL_DISTINCT (MAP FST fields) /\
        EVERY (\(fname,fty,sz). !tv.
          evaluate_type (get_tenv cx) fty = SOME tv ==>
          sz = type_memory_size tv) fields)` by
       (fs[expr_sim_inv_def] >> rpt strip_tac >> first_x_assum drule >> simp[]) >>
     mp_tac (Q.INST [`tenv` |-> `get_tenv cx`, `sty` |-> `post_value_type ce e`,
       `dtv` |-> `tv`, `dst` |-> `Var x`, `src` |-> `op`,
       `sa` |-> `su`, `fn` |-> `func`, `dw` |-> `w`]
       (SPEC_ALL compile_store_memory_typed_path_mem)) >>
     (impl_tac >- (fs[venomStateTheory.eval_operand_def] >>
                   rpt strip_tac >> gvs[] >> metis_tac[])) >>
     strip_tac >> qexists `t` >>
     fs[AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM] >>
     rpt strip_tac >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  `LENGTH s.vs_memory <= LENGTH q.vs_memory` by
    metis_tac[gas_path_mem_memory_length] >>
  drule_all aggregate_store_rebased_control_frame >> strip_tac >>
  `alloca_history func q` by
    (irule gas_path_mem_zero_history >> simp[] >>
     metis_tac[aggregate_mem_path_alloca_inv]) >>
  qexists `q` >> simp[] >>
  gvs[venomStateTheory.venom_state_component_equality] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume aggregate_nested_store_mem[bulk]:
  markerLib.RESUME_TAC >>
  `compile_store_memory ce op (Var x) dty dty su = ((),sb)` by
    (qpat_x_assum `compile_store_memory _ _ _ _ _ _ = _` mp_tac >>
     simp_tac bool_ss [compile_store_memory_def] >>
     qpat_x_assum `_ \/ _` strip_assume_tac >> asm_simp_tac bool_ss []) >>
  `type_memory_size stv = type_memory_size tv` by
    (qpat_x_assum `_ \/ _` strip_assume_tac >- gvs[] >>
     drule tuple_memory_layout_eq_bytes >>
     disch_then (qspec_then `ce` mp_tac) >>
     metis_tac[expr_sim_inv_memory_size]) >>
  `val_in_memory tv v (w2n sw) s.vs_memory` by
    (qpat_x_assum `_ \/ _` strip_assume_tac >- gvs[] >>
     `memory_layout_key dty = memory_layout_key (post_value_type ce e)` by
       (Cases_on `dty` >> fs[tuple_memory_layout_eq_def] >>
        Cases_on `post_value_type ce e` >>
        fs[tuple_memory_layout_eq_def] >> simp[memory_layout_key_tuple]) >>
     drule_all memory_layout_key_evaluated >> strip_tac >>
     irule memory_value_rel_val_in_memory >> simp[] >>
     irule memory_layout_rel_value >> qexists `stv` >> simp[] >>
     irule val_in_memory_memory_value_rel >> simp[]) >>
  `compile_copy_memory (Var x) op (type_memory_size tv) su = ((),sb)` by
    (qpat_x_assum `compile_store_memory _ _ _ dty dty _ = _` mp_tac >>
     asm_simp_tac bool_ss [compile_store_memory_def]) >>
  `eval_operand (Var x) s = SOME w` by simp[venomStateTheory.eval_operand_def] >>
  `w2n sw + type_memory_size tv <= s.vs_alloca_next` by metis_tac[] >>
  drule_all aggregate_layout_copy_path_mem >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qabbrev_tac `t = q with vs_inst_idx := LENGTH sb.cs_current_insts` >>
  drule buffer_store_memory_shape >> strip_tac >>
  qexists `t` >>
  gvs[Abbr `t`, venomStateTheory.venom_state_component_equality,
      exprLoweringPropsTheory.same_blocks_def, venomStateTheory.lookup_var_def] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Finalise aggregate_nested_store_mem[local]

Theorem aggregate_declared_head_continuation_mem:
  body_inv tops ctx ce cx /\ expr_sim_inv ce cx env es /\
  expr_body_pre ce cx env e es /\ body_exprs_mem_ok cx (e::args) /\
  compile_expr ce (expr_type e) e sa = (vv,sm) /\
  emit_op ADD [Var x; Lit (n2w off)] sm = (dst,sn) /\
  unwrap_value ce vv sn = (op,su) /\
  compile_store_memory ce op dst dty (lowered_value_type ce e) su = ((),ss) /\
  arg_type_fits (expr_type e) dty /\
  ci_mono sa sm /\ local_ptrs_reserved ce sa /\ fn_has_code sm ss func /\
  fn_inst_ids_distinct func /\ MEM inst (fn_insts func) /\
  inst.inst_outputs = [x] /\ inst.inst_id < sa.cs_next_id /\
  (!st. expr_sim_inv ce cx env st ==> not_local_ptr ce st.scopes x) /\
  not_fresh_at sa x /\ lookup_var x s0 = SOME (n2w b) /\
  FLOOKUP s0.vs_allocas inst.inst_id = SOME (b,asz) /\
  stmt_state_rel H ctx func ce cx es s0 /\
  evaluate_type (get_tenv cx) dty = SOME htv /\
  off + type_memory_size htv <= asz /\ b+asz < dimword (:256) /\
  (ce.ce_is_ctor ==> !name itv iv io.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc io) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
    regions_disjoint io (type_memory_size itv) (b+off) (type_memory_size htv)) /\
  gas_marked_exec T (ctx,func) (eval_expr cx e) (es,s0)
    marks (INL tv) es1 (OK t1) /\ es1.gas_obs = [] /\
  vv_post H ctx func ce cx e es sa sm s0 es1 tv vv t1 /\
  vv_store_bound cx (expr_type e) (lowered_value_type ce e) es1 tv vv t1 /\
  t1.vs_current_bb = sm.cs_current_bb /\
  t1.vs_inst_idx = LENGTH sm.cs_current_insts /\ alloca_history func t1 ==>
  ?v q. (~expr_has_effect e /\ MAP FDOM es.scopes = MAP FDOM es1.scopes /\
     (!n lb lsz. local_region ce es.scopes s0 n lb lsz ==>
        b + asz <= lb \/ lb + lsz <= b) ==>
     (!n lb lsz. local_region ce es.scopes s0 n lb lsz ==>
        mem_bytes_at lb lsz q.vs_memory = mem_bytes_at lb lsz s0.vs_memory) /\
     !p n. (p + n <= b \/ b + asz <= p) /\
       (!inst c sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
          sa.cs_next_id <= inst.inst_id /\
          FLOOKUP q.vs_allocas inst.inst_id = SOME (c,sz) ==>
          regions_disjoint p n c sz) ==>
       mem_bytes_at p n q.vs_memory = mem_bytes_at p n s0.vs_memory) /\
    gas_marked_exec T (ctx,func) (read_result cx tv) (es1,t1)
      [] (INL v) es1 (OK q) /\
    val_in_memory htv v (b+off) q.vs_memory /\
    stmt_state_rel H ctx func ce cx es1 q /\
    (!z a. not_fresh_at sm z /\ lookup_var z t1 = SOME a ==> lookup_var z q = SOME a) /\
    (!i a. FLOOKUP t1.vs_allocas i = SOME a ==> FLOOKUP q.vs_allocas i = SOME a) /\
    (!i lo sz a k. FLOOKUP t1.vs_allocas i = SOME (lo,sz) /\ i < sa.cs_next_id /\
      (!name lb len. local_region ce es1.scopes t1 name lb len ==>
        lo+sz <= lb \/ lb+len <= lo) /\
      lo <= a /\ a+k <= lo+sz /\ (a+k <= b+off \/ b+off+type_memory_size htv <= a) ==>
      mem_bytes_at a k q.vs_memory = mem_bytes_at a k t1.vs_memory) /\
    locals_kept ce es1 es1 t1 q /\ q.vs_current_bb = ss.cs_current_bb /\
    q.vs_inst_idx = LENGTH ss.cs_current_insts /\
    alloca_history func q /\ t1.vs_alloca_next <= q.vs_alloca_next /\
    lookup_var x q = SOME (n2w b) /\
    FLOOKUP q.vs_allocas inst.inst_id = SOME (b,asz) /\
    expr_sim_inv ce cx env es1 /\ body_exprs_mem_ok cx args /\
    value_has_type htv v /\ MAP FDOM es.scopes = MAP FDOM es1.scopes /\
    mem_bytes_at b asz t1.vs_memory = mem_bytes_at b asz s0.vs_memory /\
    q.vs_accounts = t1.vs_accounts /\ q.vs_transient = t1.vs_transient /\
    q.vs_requests = t1.vs_requests /\ q.vs_call_ctx = t1.vs_call_ctx
Proof
  strip_tac >>
  Cases_on `dty = expr_type e \/
    is_bytestring_type dty /\ is_bytestring_type (expr_type e)`
  >- (mp_tac (SPEC_ALL aggregate_body_head_continuation_mem) >>
      (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
      disch_then ACCEPT_TAC) >>
  rename1 `gas_marked_exec T (ctx,func) (eval_expr cx e) (es,s0)
    marks (INL tvv) es1 (OK t1)` >>
  `dty <> expr_type e /\ ~is_bytestring_type dty` by
    metis_tac[compileEnvTheory.arg_type_fits_bytestring_source] >>
  `well_typed_expr env e /\ acyclic_struct_metadata ce.ce_struct_fields` by
    fs[expr_body_pre_def, body_inv_def, expr_sim_inv_def] >>
  `~is_word_type dty /\ ~is_word_type (expr_type e) /\
   ~is_bytestring_type (expr_type e)` by
    ( `type_widens_to (get_tenv cx) (expr_type e) dty` by
        simp[type_widens_to_def, well_formed_type_def] >>
      metis_tac[type_widens_to_word, return_source_word_widens_eq,
                type_widens_from_bytestring]) >>
  `lowered_value_type ce e = post_value_type ce e` by
    metis_tac[aggregate_nested_lowered_post] >>
  `ci_mono sm sn /\ ci_mono sn su /\ ci_mono su ss` by
    metis_tac[ci_mono_emit_op, ci_mono_unwrap_value,
              ci_mono_compile_store_memory, pairTheory.SND] >>
  `fn_has_code sm sn func /\ fn_has_code sn su func /\
   fn_has_code su ss func` by
    (fs[ci_mono_def] >> metis_tac[fn_has_code_split, cs_extends_trans]) >>
  `local_ptrs_reserved ce sm /\ local_ptrs_reserved ce sn /\
   local_ptrs_reserved ce su` by metis_tac[compiler_ci_mono_reserved] >>
  `not_fresh_at sm x` by metis_tac[not_fresh_at_mono, ci_mono_def] >>
  `!z. op = Var z ==> not_fresh_at su z` by
    metis_tac[aggregate_child_unwrap_var, ci_mono_def] >>
  `!z. vv_operand vv = Var z ==> not_fresh_at sn z` by
    (rpt strip_tac >> irule not_fresh_at_mono >>
     qexists `sm` >> fs[ci_mono_def] >>
     drule (cj 1 compiler_compile_var) >> simp[]) >>
  `es1 with gas_obs := [] = es1` by
    simp[vyperStateTheory.evaluation_state_component_equality] >>
  drule_all aggregate_tuple_marked_child_declared_source_any >>
  qpat_assum `es1 with gas_obs := [] = es1` (fn eq => rewrite_tac[eq]) >>
  strip_tac >>
  rename1 `evaluate_type (get_tenv cx) (expr_type e) = SOME stv` >>
  `type_memory_bytes ce dty = type_memory_size htv /\
   type_memory_bytes ce (expr_type e) = type_memory_size stv /\
   type_memory_size stv < 2 ** 64` by
    metis_tac[expr_sim_inv_memory_size, aggregate_child_memory_size_bound] >>
  `type_memory_size htv < dimword (:256)` by decide_tac >>
  `lookup_var x t1 = SOME (n2w b) /\
   FLOOKUP t1.vs_allocas inst.inst_id = SOME (b,asz) /\
   stmt_state_rel H ctx func ce cx es1 t1` by
    (fs[vv_post_def] >> metis_tac[]) >>
  `~t1.vs_halted` by
    metis_tac[gas_marked_exec_def, gas_marked_path_exec, gas_path_normal] >>
  `alloca_inv t1` by fs[stmt_state_rel_def] >>
  `!name lo sz. local_region ce es1.scopes t1 name lo sz ==>
      lo+sz <= b+off \/ b+off+type_memory_size htv <= lo` by
    (rpt strip_tac >> metis_tac[aggregate_alloca_slice_excludes_local]) >>
  `mem_bytes_at b asz t1.vs_memory = mem_bytes_at b asz s0.vs_memory` by
    (irule vv_post_old_buffer >> goal_assum (drule_at Any) >>
     qexists `inst.inst_id` >> simp[] >> rpt strip_tac >>
     mp_tac (GEN_ALL (Q.INST [`off` |-> `0`, `n` |-> `asz`]
       (SPEC_ALL aggregate_alloca_slice_excludes_local))) >>
     simp[] >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  drule_at (Pat `gas_marked_exec _ _ _ _ _ _ _ _`) aggregate_tuple_marked_footprint_any >>
  disch_then (drule_at (Pat `expr_body_pre _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `ce.ce_is_ctor ==> _`)) >> strip_tac >>
  mp_tac (Q.INST [`tv` |-> `htv:type_value`, `r` |-> `t1`, `es'` |-> `es1`,
     `aid` |-> `inst.inst_id`]
    (SPEC_ALL aggregate_add_slice_entry_mem)) >>
  (impl_tac >- (fs[ci_mono_def] >> rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choosel_then [`d`, `u`] strip_assume_tac) >> gvs[] >>
  mp_tac (Q.INST [`si` |-> `sa`, `sj` |-> `sm`, `sm` |-> `sn`,
     `ty` |-> `expr_type e`, `r` |-> `u`, `es'` |-> `es1`]
    (SPEC_ALL aggregate_body_rebased_marked_read_mem_capacity)) >>
  (impl_tac >- (fs[ci_mono_def] >> rpt strip_tac >> gvs[] >>
      metis_tac[expr_sim_inv_memory_size])) >>
  disch_then (qx_choosel_then [`v`, `s`] strip_assume_tac) >>
  suspend "store_join"
QED

Resume aggregate_declared_head_continuation_mem[store_join]:
  markerLib.RESUME_TAC >>
  `read_result cx tvv es1 = (INL v,es1)` by
    (qpat_x_assum `gas_marked_exec _ _ (read_result _ _) _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def] >> strip_tac >>
     first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  `value_has_type htv v /\ val_wf htv v` by
    (qpat_x_assum `!v. read_result _ _ _ = _ ==> _` drule >> simp[]) >>
  `(do res <- eval_expr cx e; read_result cx res od)
      (es with gas_obs := gas_explicit marks s0.vs_gas_readings) = (INL v,es1)` by
    (`eval_expr cx e (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
        (INL tvv,es1)` by
       (qpat_x_assum `gas_marked_exec _ _ (eval_expr _ _) _ _ _ _ _` mp_tac >>
        simp[gas_marked_exec_def] >> strip_tac >>
        first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
     simp[bind_def]) >>
  `stmt_state_rel H ctx func ce cx es1 u` by fs[vv_post_def] >>
  `~s.vs_halted` by
    metis_tac[gas_marked_exec_def, gas_marked_path_exec, gas_path_normal] >>
  `!name a len. local_region ce es1.scopes u name a len ==>
      a+len <= b+off \/ b+off+type_memory_size htv <= a` by
    metis_tac[arithmeticTheory.ADD_ASSOC] >>
  `~is_word_type (post_value_type ce e)` by
    (`type_widens_to (get_tenv cx) (post_value_type ce e) (expr_type e)` by
       (drule_all post_value_type_widens >>
        fs[expr_sim_inv_def, env_consistent_def, env_context_consistent_def]) >>
     metis_tac[return_source_word_widens_eq]) >>
  `!stv sw. evaluate_type (get_tenv cx) (lowered_value_type ce e) = SOME stv /\
      eval_operand op s = SOME sw ==>
      type_memory_size stv = 0 \/ w2n sw+type_memory_size stv <= s.vs_alloca_next` by
    (Cases_on `post_value_type ce e = expr_type e` >> fs[] >> metis_tac[]) >>
  `w2n (n2w (b+off):bytes32) = b+off` by
    (`b+off < dimword (:256)` by decide_tac >> simp[wordsTheory.w2n_n2w]) >>
  mp_tac (Q.INST [`sm` |-> `sn`, `r` |-> `u`, `x` |-> `d:string`,
     `w` |-> `n2w (b+off):bytes32`, `tv` |-> `htv:type_value`,
     `es` |-> `es with gas_obs := gas_explicit marks s0.vs_gas_readings`,
     `es'` |-> `es1`, `sb` |-> `ss`, `did` |-> `inst.inst_id`, `k` |-> `asz`]
    (SPEC_ALL aggregate_nested_store_mem)) >>
  (impl_tac >- (simp[] >> fs[ci_mono_def] >> rpt strip_tac >>
      gvs[] >> metis_tac[arithmeticTheory.ADD_ASSOC])) >>
  disch_then (qx_choose_then `q` strip_assume_tac) >>
  `!z. not_fresh_at sm z ==> not_fresh_at sn z` by
    (rpt strip_tac >> irule not_fresh_at_mono >>
     qexists `sm` >> fs[ci_mono_def]) >>
  drule_at (Pat `locals_kept _ _ _ _ _`) aggregate_slice_frame_transport >>
  disch_then (qspecl_then [`sn`, `sm`, `t1`, `sa.cs_next_id`,
    `\a k. a+k <= b+off \/ b+off+type_memory_size htv <= a`] mp_tac) >>
  (impl_tac >- (gvs[] >> rpt strip_tac >> first_x_assum irule >>
      (conj_tac >-
        (rename1 `FLOOKUP t1.vs_allocas aid = SOME (alo,asz0)` >>
         qexistsl_tac [`aid`, `alo`, `asz0`] >>
         rpt conj_tac >> first_assum ACCEPT_TAC) >>
       simp[]))) >>
  strip_tac >>
  `gas_marked_exec T (ctx,func) (read_result cx tvv) (es1,t1)
      [] (INL v) es1 (OK q)` by
    (`u.vs_gas_readings = t1.vs_gas_readings` by
       (drule gas_marked_path_ok_suffix >> simp[]) >>
     qpat_x_assum `gas_marked_exec _ _ (read_result _ _) _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def, gas_marked_path_def] >>
     strip_tac >>
     irule (SRULE [] (Q.INST [`n` |-> `0`, `m` |-> `0`]
       (SPEC_ALL gas_path_mem_then))) >>
     qexists `u` >> conj_tac >- fs[gas_marked_path_def] >>
     irule (SRULE [] (Q.INST [`n` |-> `0`, `m` |-> `0`]
       (SPEC_ALL gas_path_mem_then))) >>
     qexists `s` >> simp[]) >>
  `body_exprs_mem_ok cx args` by metis_tac[aggregate_body_exprs_mem_tail] >>
  `~expr_has_effect e /\ MAP FDOM es.scopes = MAP FDOM es1.scopes /\
    (!n lb lsz. local_region ce es.scopes s0 n lb lsz ==>
       b+asz <= lb \/ lb+lsz <= b) ==>
    (!n lb lsz. local_region ce es.scopes s0 n lb lsz ==>
       mem_bytes_at lb lsz q.vs_memory = mem_bytes_at lb lsz s0.vs_memory) /\
    !p n. (p+n <= b \/ b+asz <= p) /\
      (!i c sz. MEM i (fn_insts func) /\ i.inst_opcode = ALLOCA /\
         sa.cs_next_id <= i.inst_id /\
         FLOOKUP q.vs_allocas i.inst_id = SOME (c,sz) ==>
         regions_disjoint p n c sz) ==>
      mem_bytes_at p n q.vs_memory = mem_bytes_at p n s0.vs_memory` by
    (strip_tac >>
     `pure_frame ce func es sa s0 u` by fs[vv_post_def] >>
     `pure_frame ce func es1 (sa with cs_next_var := sn.cs_next_var) u s` by
       metis_tac[expr_post_pure_frame] >>
     `pure_frame ce func es sa s0 s` by
       (irule pure_frame_trans >>
        conj_tac >- first_assum ACCEPT_TAC >>
        qexistsl_tac [`es1`, `sa with cs_next_var := sn.cs_next_var`, `u`] >>
        fs[vv_post_def, expr_post_def]) >>
     match_mp_tac aggregate_pure_frame_store >>
     qexistsl_tac [`s`, `b+off`, `type_memory_size htv`] >> simp[] >>
     rpt strip_tac >> metis_tac[arithmeticTheory.ADD_ASSOC, arithmeticTheory.ADD_COMM]) >>
  qexistsl_tac [`v`, `q`] >> simp[] >>
  gvs[AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Finalise aggregate_declared_head_continuation_mem[local]


(* Declared nested members use the checked physical read and typed store. *)
Theorem aggregate_make_tuple_nested_sim_mem:
  !st0 args tys ce cx env off sa out sb es tvs func inst x b asz s0 ctx tops.
  compile_make_tuple compile_expr ce args tys (Var x) off sa = (out,sb) /\
  LIST_REL (\t e. arg_type_fits (expr_type e) t) tys args /\
  (?t e. MEM (t,e) (ZIP (tys,args)) /\ t <> expr_type e /\
     ~is_bytestring_type t) /\
  OPT_MMAP (evaluate_type (get_tenv cx)) tys = SOME tvs /\
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
  off + type_memory_size_list tvs <= asz /\ b + asz < dimword (:256) /\
  (ce.ce_is_ctor ==>
   !name itv iv io.
     FLOOKUP ce.ce_module_vars (ce.ce_module,name) =
       SOME (ImmutableLoc io) /\
     FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
       | SOME imms => get_source_immutables ce.ce_module imms) name =
       SOME (itv,iv) ==>
     regions_disjoint io (type_memory_size itv) (b+off)
       (type_memory_size_list tvs)) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func ce cx es s0 /\
    storage_well_formed_on cx es (FST H)) /\ alloca_history func s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  out = Var x /\
  gas_outcome T (cx_tops cx) (ctx,func) cx st0 (eval_exprs cx args) (es,s0)
    (\H res es' r. ?vs. res = INL vs /\ r.vs_current_bb = sb.cs_current_bb /\
      r.vs_inst_idx = LENGTH sb.cs_current_insts /\ expr_sim_inv ce cx env es' /\
      stmt_state_rel H ctx func ce cx es' r /\
      storage_well_formed_on cx es' (FST H) /\
      tuple_in_memory vs tvs (b+off) r.vs_memory /\
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
      locals_kept ce es es' s0 r /\
      alloca_history func r /\ s0.vs_alloca_next <= r.vs_alloca_next /\
      (~EXISTS expr_has_effect args ==>
        (!n lb lsz. local_region ce es.scopes s0 n lb lsz ==>
          mem_bytes_at lb lsz r.vs_memory = mem_bytes_at lb lsz s0.vs_memory) /\
        !p n. (p + n <= b \/ b + asz <= p) /\
          (!i c sz. MEM i (fn_insts func) /\ i.inst_opcode = ALLOCA /\
             sa.cs_next_id <= i.inst_id /\
             FLOOKUP r.vs_allocas i.inst_id = SOME (c,sz) ==>
             regions_disjoint p n c sz) ==>
          mem_bytes_at p n r.vs_memory = mem_bytes_at p n s0.vs_memory))
    (\H res es' exit. ?exc. res = INR exc /\
      expr_exit (INR exc : eval_result + exception) exit /\
      exprSimDefs$halt_exit H cx es' (INR exc : eval_result + exception) exit)
Proof
  Induct_on `args`
  >- (rpt gen_tac >> strip_tac >> gvs[]) >>
  pop_assum (fn ih =>
    rpt gen_tac >> strip_tac >>
    Cases_on `tys` >- fs[] >> gns[] >>
    `out = Var x` by metis_tac[compiler_make_tuple_result] >>
    gnvs[] >> assume_tac ih) >>
  rename1 `compile_make_tuple compile_expr ce (h::args) (dty::dtys) _ _ _ = _` >>
  `expr_body_pre ce cx env h es` by metis_tac[listTheory.MEM] >>
  drule exprSimAggregateLoopsTheory.compile_make_tuple_cons >> strip_tac >>
  rename1 `compile_expr ce (expr_type h) h sa = (vv,sm)` >>
  rename1 `emit_op ADD [Var x; Lit (n2w off)] sm = (dst,sn)` >>
  rename1 `unwrap_value ce vv sn = (op,su)` >>
  rename1 `compile_store_memory ce op dst dty (lowered_value_type ce h) su = ((),ss)` >>
  drule_all aggregate_tuple_cons_order_mem >> strip_tac >>
  drule_all aggregate_tuple_child_outcome_mem >> strip_tac >>
  rewrite_tac[aggregate_tuple_eval_cons] >>
  match_mp_tac (Q.SPEC `\H tv ee r.
    vv_post H ctx func ce cx h es sa sm s0 ee tv vv r /\
    vv_store_bound cx (expr_type h) (lowered_value_type ce h) ee tv vv r /\
    r.vs_current_bb = sm.cs_current_bb /\ r.vs_inst_idx = LENGTH sm.cs_current_insts /\
    alloca_history func r /\ s0.vs_alloca_next <= r.vs_alloca_next`
    (Q.GEN `P` aggregate_tuple_bind_outcome)) >>
  rpt conj_tac
  >- (irule aggregate_tuple_gas_outcome_mono >> goal_assum (drule_at Any) >>
      simp[] >> rpt strip_tac >> Cases_on `res` >>
      qpat_x_assum `expr_exit _ _` mp_tac >> simp[exprSimDefsTheory.expr_exit_def])
  >- (gen_tac >> BETA_TAC >>
      irule vyperStorageTraceTheory.storage_trace_frame_bind_all >>
      simp[vyperStorageTraceTheory.storage_trace_frame_read_result] >> gen_tac >>
      irule vyperStorageTraceTheory.storage_trace_frame_bind_all >>
      simp[vyperStorageTraceTheory.evaluate_storage_trace_frame,
           vyperStorageTraceTheory.storage_trace_frame_return]) >>
  rpt gen_tac >> BETA_TAC >> strip_tac >>
  rename1 `gas_marked_exec T _ (eval_expr cx h) _ marks (INL tv) es1 (OK t1)` >>
  (* Off the trace's own domain the run is a bad-storage one; on it, its
     own horizon is valid at es1 and, by the frame, at es. *)
  reverse (Cases_on `storage_trace_domain cx st0 es1.storage_trace`)
  >- (rewrite_tac[gasOutcomeTheory.gas_outcome_def] >> qexists_tac `[]` >> disj1_tac >>
      irule gasStorageTheory.gas_bad_storage_at_initial >> asm_rewrite_tac[] >>
      irule vyperStorageTraceTheory.storage_trace_frame_bind_all >>
      simp[vyperStorageTraceTheory.storage_trace_frame_read_result] >> gen_tac >>
      irule vyperStorageTraceTheory.storage_trace_frame_bind_all >>
      simp[vyperStorageTraceTheory.evaluate_storage_trace_frame,
           vyperStorageTraceTheory.storage_trace_frame_return]) >>
  `?H0. valid_horizon cx st0 H0 es1.storage_trace` by
    (qexists_tac `storage_trace_horizon es1.storage_trace` >>
     fs[vyperStorageFootprintTheory.storage_trace_domain_def]) >>
  `eval_expr cx h (es with gas_obs := gas_explicit marks s0.vs_gas_readings) =
     (INL tv, es1 with gas_obs := [])` by
    (qpat_x_assum `gas_marked_exec _ _ (eval_expr _ _) _ _ _ _ _` mp_tac >>
     simp[gas_marked_exec_def] >> strip_tac >>
     first_x_assum (qspec_then `[]` mp_tac) >> simp[]) >>
  `valid_horizon cx st0 H0 es.storage_trace` by
    (qpat_x_assum `eval_expr cx h _ = (INL tv,_)` assume_tac >>
     drule_at (Pos (el 2)) vyperStorageFootprintTheory.valid_horizon_frame >>
     disch_then (qspecl_then [`st0`, `cx`, `H0`] mp_tac) >>
     simp[vyperStorageTraceTheory.evaluate_storage_trace_frame]) >>
  `stmt_state_rel H0 ctx func ce cx es s0` by metis_tac[] >>
  qpat_assum `!H. valid_horizon cx st0 H es1.storage_trace ==> _`
    (qspec_then `H0` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  `!H. valid_horizon cx st0 H es1.storage_trace ==>
     vv_post H ctx func ce cx h es sa sm s0 es1 tv vv t1` by metis_tac[] >>
  qpat_x_assum `arg_type_fits _ _ /\ _`
    (CONJUNCTS_THEN2 assume_tac assume_tac) >>
  qpat_x_assum `?v. evaluate_type _ _ = _ /\ _` strip_assume_tac >>
  gnvs[] >>
  rename1 `evaluate_type (get_tenv cx) dty = SOME htv` >>
  rename1 `OPT_MMAP (evaluate_type (get_tenv cx)) dtys = SOME ttvs` >>
  suspend "cons_join"
QED

Resume aggregate_make_tuple_nested_sim_mem[cons_join]:
  markerLib.RESUME_TAC >>
  `off + type_memory_size htv <= asz` by
    (fs[type_memory_size_def] >> decide_tac) >>
  `ce.ce_is_ctor ==> !name itv iv io.
    FLOOKUP ce.ce_module_vars (ce.ce_module,name) = SOME (ImmutableLoc io) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
      | SOME imms => get_source_immutables ce.ce_module imms) name = SOME (itv,iv) ==>
    regions_disjoint io (type_memory_size itv) (b+off) (type_memory_size htv)` by
    (rpt strip_tac >> qpat_x_assum `ce.ce_is_ctor ==> _` mp_tac >>
     simp[] >> disch_then drule_all >>
     simp[regions_disjoint_def, type_memory_size_def] >> decide_tac) >>
  drule_at (Pat `compile_expr _ _ _ _ = _`)
    (Q.INST [`H` |-> `H0`]
      (INST_TYPE [alpha |-> ``:256``] aggregate_declared_head_continuation_mem)) >>
  disch_then (drule_at (Pat `gas_marked_exec _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `evaluate_type _ _ = _`)) >>
  disch_then (drule_at (Pat `FLOOKUP s0.vs_allocas _ = _`)) >>
  disch_then (drule_at (Pat `emit_op _ _ _ = _`)) >>
  disch_then (drule_at (Pat `unwrap_value _ _ _ = _`)) >>
  disch_then (drule_at (Pat `compile_store_memory _ _ _ _ _ _ = _`)) >>
  disch_then (drule_at (Pat `arg_type_fits _ _`)) >>
  disch_then (drule_at (Pat `body_inv _ _ _ _`)) >>
  disch_then (drule_at (Pat `expr_sim_inv _ _ _ _`)) >>
  disch_then (mp_tac o SPEC_ALL) >>
  (impl_tac >- (simp[] >> asm_rewrite_tac[])) >> strip_tac >>
  `not_fresh_at ss x /\ inst.inst_id < ss.cs_next_id` by
    (fs[ci_mono_def] >>
     metis_tac[not_fresh_at_mono, arithmeticTheory.LESS_LESS_EQ_TRANS]) >>
  `OPT_MMAP (evaluate_type (get_tenv cx)) (dty::dtys) = SOME (htv::ttvs)` by simp[] >>
  drule_at (Pat `gas_marked_exec _ _ (read_result _ _) _ _ _ _ _`)
    (Q.INST [`H` |-> `H0`]
      (INST_TYPE [alpha |-> ``:256``] aggregate_tuple_tail_entry_mem)) >>
  disch_then (drule_at (Pat `gas_marked_exec _ _ (eval_expr _ _) _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `FLOOKUP q.vs_allocas _ = _`)) >>
  disch_then (drule_at (Pat `body_inv _ _ _ _`)) >>
  disch_then (drule_at (Pat `fn_has_code ss sb _`)) >>
  disch_then (drule_at (Pat `expr_sim_inv _ _ _ es1`)) >>
  disch_then (drule_at (Pat `inst.inst_outputs = _`)) >>
  disch_then (drule_at (Pat `OPT_MMAP _ _ = _`)) >>
  disch_then (mp_tac o SPEC_ALL) >>
  (impl_tac >- (simp[] >> asm_rewrite_tac[])) >> strip_tac >>
  suspend "tail"
QED

Resume aggregate_make_tuple_nested_sim_mem[tail]:
  markerLib.RESUME_TAC >>
  `stmt_state_rel H0 ctx func ce cx es s0` by metis_tac[] >>
  `!name lo sz. local_region ce es.scopes s0 name lo sz ==>
    b+asz <= lo \/ lo+sz <= b` by
    (rpt strip_tac >>
     `not_local_ptr ce es.scopes x` by metis_tac[] >>
     qpat_assum `stmt_state_rel H0 ctx func ce cx es s0`
       (mp_then (Pat `stmt_state_rel _ _ _ _ _ _ _`) mp_tac
         (SRULE [] (Q.INST [`off` |-> `0`, `n` |-> `asz`] aggregate_alloca_slice_excludes_local))) >>
     disch_then (drule_at (Pat `FLOOKUP s0.vs_allocas _ = _`)) >>
     disch_then (drule_at (Pat `inst.inst_outputs = _`)) >>
     disch_then (drule_at (Pat `local_region _ _ _ _ _ _`)) >> simp[]) >>
  `~expr_has_effect h ==>
     (!n lb lsz. local_region ce es.scopes s0 n lb lsz ==>
         mem_bytes_at lb lsz q.vs_memory = mem_bytes_at lb lsz s0.vs_memory) /\
      !p n. (p + n <= b \/ b + asz <= p) /\
        (!inst c sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
           sa.cs_next_id <= inst.inst_id /\
           FLOOKUP q.vs_allocas inst.inst_id = SOME (c,sz) ==>
           regions_disjoint p n c sz) ==>
        mem_bytes_at p n q.vs_memory = mem_bytes_at p n s0.vs_memory` by
    (strip_tac >>
     qpat_x_assum `~expr_has_effect h /\ MAP FDOM _ = _ /\ _ ==> _` mp_tac >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
     disch_then ACCEPT_TAC) >>
  `type_memory_bytes ce dty = type_memory_size htv` by
    metis_tac[expr_sim_inv_memory_size] >>
  fs[] >>
  (* The tail starts at q under every horizon of es1's trace: the head's
     read and store leave the fields stmt_state_rel's horizon part reads. *)
  `!H. valid_horizon cx st0 H es1.storage_trace ==>
     stmt_state_rel H ctx func ce cx es1 q /\
     storage_well_formed_on cx es1 (FST H)` by
    (gen_tac >> strip_tac >>
     qpat_assum `!H. valid_horizon cx st0 H es1.storage_trace ==> _`
       (qspec_then `H` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     rewrite_tac[loweringPostsTheory.vv_post_def] >> strip_tac >>
     asm_rewrite_tac[] >>
     MATCH_MP_TAC
       (Q.INST [`H0` |-> `H0`, `H` |-> `H`, `ctx` |-> `ctx`,
                `func` |-> `func`, `cenv` |-> `ce`, `cx` |-> `cx`,
                `es` |-> `es1`, `u` |-> `q`, `s` |-> `t1`]
         (INST_TYPE [alpha |-> ``:256``, beta |-> ``:256``]
           exprLoweringPropsTheory.stmt_state_rel_fields_transport)) >>
     asm_rewrite_tac[]) >>
  `!elt. MEM elt args ==>
     int_calls_expr elt = [] \/ lowered_value_type ce elt = expr_type elt` by
    (rpt strip_tac >>
     qpat_x_assum `!e. e = h \/ MEM e args ==> _` (qspec_then `elt` mp_tac) >>
     simp[]) >>
  `gas_outcome T (cx_tops cx) (ctx,func) cx st0 (eval_exprs cx args) (es1,q)
    (\H res es2 r. ?vs. res = INL vs /\ r.vs_current_bb = sb.cs_current_bb /\
      r.vs_inst_idx = LENGTH sb.cs_current_insts /\ expr_sim_inv ce cx env es2 /\
      stmt_state_rel H ctx func ce cx es2 r /\
      storage_well_formed_on cx es2 (FST H) /\
      tuple_in_memory vs ttvs (b+(off+type_memory_size htv)) r.vs_memory /\
      (!z w. not_fresh_at ss z /\ lookup_var z q = SOME w ==> lookup_var z r = SOME w) /\
      (!aid a. FLOOKUP q.vs_allocas aid = SOME a ==> FLOOKUP r.vs_allocas aid = SOME a) /\
      (!p n. b <= p /\ p+n <= b+asz /\
        (p+n <= b+(off+type_memory_size htv) \/
         b+(off+type_memory_size htv)+type_memory_size_list ttvs <= p) ==>
        mem_bytes_at p n r.vs_memory = mem_bytes_at p n q.vs_memory) /\
      (!aid p n. FLOOKUP q.vs_allocas aid = SOME (p,n) /\
        aid < ss.cs_next_id /\ (p+n <= b \/ b+asz <= p) /\
        (!name lo sz. local_region ce es1.scopes q name lo sz ==> p+n <= lo \/ lo+sz <= p) ==>
        mem_bytes_at p n r.vs_memory = mem_bytes_at p n q.vs_memory) /\
      locals_kept ce es1 es2 q r /\ alloca_history func r /\ q.vs_alloca_next <= r.vs_alloca_next /\
      (~EXISTS expr_has_effect args ==>
        (!n lb lsz. local_region ce es1.scopes q n lb lsz ==>
          mem_bytes_at lb lsz r.vs_memory = mem_bytes_at lb lsz q.vs_memory) /\
        !p n. (p + n <= b \/ b + asz <= p) /\
          (!i c sz. MEM i (fn_insts func) /\ i.inst_opcode = ALLOCA /\
             ss.cs_next_id <= i.inst_id /\
             FLOOKUP r.vs_allocas i.inst_id = SOME (c,sz) ==>
             regions_disjoint p n c sz) ==>
          mem_bytes_at p n r.vs_memory = mem_bytes_at p n q.vs_memory))
    (\H res es' exit. ?exc. res = INR exc /\ expr_exit (INR exc : eval_result + exception) exit /\
      exprSimDefs$halt_exit H cx es' (INR exc : eval_result + exception) exit)` by
    (Cases_on `LIST_REL (\t e. t = expr_type e \/
       is_bytestring_type t /\ is_bytestring_type (expr_type e)) dtys args`
     >- (mp_tac (Q.SPECL [`st0`, `args`, `dtys`, `ce`, `cx`, `env`, `off + type_memory_size htv`,
        `ss`, `Var x`, `sb`, `es1`, `ttvs`, `func`, `inst`, `x`, `b`,
        `asz`, `q`, `ctx`, `tops`]
          (INST_TYPE [alpha |-> ``:256``, beta |-> ``:256``]
            aggregate_make_tuple_flat_sim_mem)) >>
         (impl_tac >- (simp[] >> asm_rewrite_tac[])) >> simp[]) >>
     mp_tac (Q.SPECL [`dtys`, `args`] aggregate_member_not_flat) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> disch_tac >>
     qpat_x_assum `!st0 tys ce cx env off sa out sb es tvs func inst x b asz s0 ctx tops. _`
       (qspecl_then [`st0`, `dtys`, `ce`, `cx`, `env`, `off + type_memory_size htv`,
        `ss`, `Var x`, `sb`, `es1`, `ttvs`, `func`, `inst`, `x`, `b`,
        `asz`, `q`, `ctx`, `tops`] mp_tac) >>
     (impl_tac >-
       (simp[AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM] >>
        asm_rewrite_tac[])) >> simp[]) >>
  `FLOOKUP t1.vs_allocas inst.inst_id = SOME (b,asz) /\
   stmt_state_rel H0 ctx func ce cx es1 t1` by (fs[loweringPostsTheory.vv_post_def] >> metis_tac[]) >>
  `vv_post H0 ctx func ce cx h es sa sm s0 es1 tv vv t1` by metis_tac[] >>
  fs[AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM] >>
  drule_at (Pat `gas_outcome _ _ _ _ _ (eval_exprs _ _) _ _ _`)
    (SRULE [AC arithmeticTheory.ADD_ASSOC arithmeticTheory.ADD_COMM]
      (INST_TYPE [alpha |-> ``:256``, beta |-> ``:256``]
        aggregate_tuple_tail_outcome_mem)) >>
  disch_then (drule_at (Pat `vv_post _ _ _ _ _ _ _ _ _ _ _ _ _ _`)) >>
  disch_then (drule_at (Pat `val_in_memory _ _ _ q.vs_memory`)) >>
  disch_then (drule_at (Pat `inst.inst_outputs = _`)) >>
  (impl_tac >-
    (simp_tac (srw_ss()) [] >> asm_rewrite_tac[] >>
     fs[loweringPostsTheory.vv_post_def] >> metis_tac[])) >> simp[]
QED

Finalise aggregate_make_tuple_nested_sim_mem

Theorem aggregate_make_tuple_fits_sim_mem:
  !st0 args tys ce cx env off sa out sb es tvs func inst x b asz s0 ctx tops.
  compile_make_tuple compile_expr ce args tys (Var x) off sa = (out,sb) /\
  LIST_REL (\t e. arg_type_fits (expr_type e) t) tys args /\
  OPT_MMAP (evaluate_type (get_tenv cx)) tys = SOME tvs /\
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
  off + type_memory_size_list tvs <= asz /\ b + asz < dimword (:256) /\
  (ce.ce_is_ctor ==>
   !name itv iv io.
     FLOOKUP ce.ce_module_vars (ce.ce_module,name) =
       SOME (ImmutableLoc io) /\
     FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
       | SOME imms => get_source_immutables ce.ce_module imms) name =
       SOME (itv,iv) ==>
     regions_disjoint io (type_memory_size itv) (b+off)
       (type_memory_size_list tvs)) /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
    stmt_state_rel H ctx func ce cx es s0 /\
    storage_well_formed_on cx es (FST H)) /\ alloca_history func s0 /\ ~s0.vs_halted /\
  s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  out = Var x /\
  gas_outcome T (cx_tops cx) (ctx,func) cx st0 (eval_exprs cx args) (es,s0)
    (\H res es' r. ?vs. res = INL vs /\ r.vs_current_bb = sb.cs_current_bb /\
      r.vs_inst_idx = LENGTH sb.cs_current_insts /\ expr_sim_inv ce cx env es' /\
      stmt_state_rel H ctx func ce cx es' r /\
      storage_well_formed_on cx es' (FST H) /\
      tuple_in_memory vs tvs (b+off) r.vs_memory /\
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
      locals_kept ce es es' s0 r /\
      alloca_history func r /\ s0.vs_alloca_next <= r.vs_alloca_next /\
      (~EXISTS expr_has_effect args ==>
        (!n lb lsz. local_region ce es.scopes s0 n lb lsz ==>
          mem_bytes_at lb lsz r.vs_memory = mem_bytes_at lb lsz s0.vs_memory) /\
        !p n. (p + n <= b \/ b + asz <= p) /\
          (!i c sz. MEM i (fn_insts func) /\ i.inst_opcode = ALLOCA /\
             sa.cs_next_id <= i.inst_id /\
             FLOOKUP r.vs_allocas i.inst_id = SOME (c,sz) ==>
             regions_disjoint p n c sz) ==>
          mem_bytes_at p n r.vs_memory = mem_bytes_at p n s0.vs_memory))
    (\H res es' exit. ?exc. res = INR exc /\
      expr_exit (INR exc : eval_result + exception) exit /\
      exprSimDefs$halt_exit H cx es' (INR exc : eval_result + exception) exit)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `LIST_REL (\t e. t = expr_type e \/
    is_bytestring_type t /\ is_bytestring_type (expr_type e)) tys args`
  >- (mp_tac (SPEC_ALL aggregate_make_tuple_flat_sim_mem) >>
      impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
      simp[]) >>
  mp_tac (SPEC_ALL aggregate_make_tuple_nested_sim_mem) >>
  impl_tac
  >- (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
      irule aggregate_member_not_flat >> simp[]) >>
  simp[]
QED
