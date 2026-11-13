(* Staged typed normalization followed by an immutable destination copy. *)
Theory immutableAssignNormalizedMem
Ancestors
  immutableNormalizedCopyFrame immutableNormalizeMem immutableAssignFixedMem immutableFixedCopyTransportMem
  immutableDeployAssignBytes stmtLowering compileEnv context
  immutableFixedCopyMem fragExec loweringSlice exprLoweringProps localPtrsProps valueEncodingProps
  venomState venomExecSemantics loweringStateRelDefs finite_map words arithmetic list pair

Theorem immutable_assign_normalized_mem_endpoint:
  compile_assign_value ce dst LocCode src F sl dty sty di
    (type_memory_bytes ce dty) sm = ((),sb) /\
  ce.ce_imm_alloca = SOME region /\
  fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
  stmt_state_rel ctx func ce cx es s /\ local_ptrs_reserved ce sm /\
  expr_val_at ce cx sty sa sm es v src s /\ expr_val_rel cx sty v src s /\
  type_widens_to (get_tenv cx) sty dty /\ sty <> dty /\
  ~is_word_type dty /\ ~is_bytestring_type dty /\
  evaluate_type (get_tenv cx) sty = SOME stv /\ value_has_type stv v /\
  evaluate_type (get_tenv cx) dty = SOME dtv /\
  immutable_value_admissible dtv v /\
  (!ty tv. evaluate_type (get_tenv cx) ty = SOME tv ==>
     type_memory_bytes ce ty = type_memory_size tv) /\
  0 < type_memory_size dtv /\ type_memory_size dtv MOD 32 = 0 /\
  type_memory_size dtv < dimword (:256) /\
  acyclic_struct_metadata ce.ce_struct_fields /\
  sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
  (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !tv. evaluate_type (get_tenv cx) fty = SOME tv ==>
      sz = type_memory_size tv) fields) /\
  (emitted_blocks sm sb <> [] ==>
    ?bb. lookup_block sb.cs_current_bb func.fn_blocks = SOME bb /\
      phi_prefix_length bb.bb_instructions = 0) /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  eval_operand src s = SOME p /\ eval_operand dst s = SOME (n2w off) /\
  eval_operand region s = SOME 0w /\
  (!x. src = Var x \/ dst = Var x \/ region = Var x ==> not_fresh_at sm x) /\
  off + type_memory_size dtv <= s.vs_alloca_next /\
  off + type_memory_size dtv < dimword (:256) /\
  (!aid q k. FLOOKUP s.vs_allocas aid = SOME (q,k) ==>
     regions_disjoint off (type_memory_size dtv) q k)
  ==>
  ?buf mid sn u r t b.
    compile_alloc_buffer (type_memory_bytes ce dty) sm = (buf,mid) /\
    compile_store_memory_typed ce buf.buf_operand dty src sty mid = ((),sn) /\
    mem_cont_sim ctx func s u /\ mem_cont_sim ctx func u r /\
    mem_cont_sim ctx func r t /\ mem_cont_sim ctx func s t /\
    exec_alloca (mk_inst sm.cs_next_id ALLOCA
      [Lit (n2w (type_memory_bytes ce dty))]
      [STRING #"%" (toString sm.cs_next_var)]) s
      (n2w (type_memory_bytes ce dty) : bytes32) =
      OK (u with vs_inst_idx := s.vs_inst_idx) /\
    u.vs_memory = s.vs_memory /\
    eval_operand buf.buf_operand r = SOME (n2w b) /\
    val_in_memory dtv v b r.vs_memory /\
    b + type_memory_size dtv <= r.vs_alloca_next /\
    b + type_memory_size dtv < dimword (:256) /\
    regions_disjoint off (type_memory_size dtv) b (type_memory_size dtv) /\
    r.vs_allocas = u.vs_allocas /\ r.vs_alloca_next = u.vs_alloca_next /\
    (!q k. q+k <= b \/ b+type_memory_size dtv <= q ==>
       mem_bytes_at q k r.vs_memory = mem_bytes_at q k s.vs_memory) /\
    t.vs_allocas = r.vs_allocas /\ t.vs_alloca_next = r.vs_alloca_next /\
    (!aid q k. FLOOKUP s.vs_allocas aid = SOME (q,k) ==>
       FLOOKUP t.vs_allocas aid = SOME (q,k)) /\
    s.vs_alloca_next <= t.vs_alloca_next /\
    (!aid q k. FLOOKUP t.vs_allocas aid = SOME (q,k) /\
       FLOOKUP s.vs_allocas aid = NONE ==>
       aid = sm.cs_next_id /\ q = s.vs_alloca_next /\ k = type_memory_size dtv) /\
    alloca_inv t /\ alloca_room ctx func t /\
    val_in_memory dtv v off t.vs_memory /\
    immutable_value_bytes_rel dtv v
      (mem_bytes_at off (type_memory_size dtv) t.vs_memory) /\
    (!q k. q+k <= off \/ off+type_memory_size dtv <= q ==>
       mem_bytes_at q k t.vs_memory = mem_bytes_at q k r.vs_memory) /\
    (!x. not_fresh_at sm x ==> lookup_var x t = lookup_var x s) /\
    (r with <|vs_vars := u.vs_vars; vs_memory := u.vs_memory;
      vs_current_bb := mid.cs_current_bb; vs_inst_idx := LENGTH mid.cs_current_insts;
      vs_prev_bb := u.vs_prev_bb|>) = u /\
    t = r with <|vs_vars := t.vs_vars; vs_memory := t.vs_memory;
      vs_immutables := t.vs_immutables; vs_inst_idx := LENGTH sb.cs_current_insts|> /\
    ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  strip_tac >>
  `type_memory_bytes ce dty = type_memory_size dtv` by metis_tac[] >>
  drule_all immutable_normalized_compiler_parts >> strip_tac >>
  drule_all immutable_normalized_code_windows >> strip_tac >>
  `!x. src = Var x ==> not_fresh_at sm x` by metis_tac[] >>
  `compile_alloc_buffer (type_memory_bytes ce dty) sm = (buf,mid) /\
   type_memory_bytes ce dty < dimword (:256) /\
   ~(is_bytestring_type dty /\ is_bytestring_type sty)` by
    (conj_tac >- metis_tac[] >> simp[] >> decide_tac) >>
  drule_all immutable_normalize_mem_endpoint >>
  disch_then (qx_choose_then `dtv1` (qx_choose_then `u`
    (qx_choose_then `r` (qx_choose_then `b` (map_every assume_tac o CONJUNCTS))))) >>
  `dtv1 = dtv` by gvs[] >> qpat_x_assum `dtv1 = dtv` SUBST_ALL_TAC >>
  `!x. dst = Var x \/ region = Var x ==> not_fresh_at sm x` by metis_tac[] >>
  drule_all immutable_normalized_copy_freshness >> strip_tac >>
  drule_all immutable_normalized_copy_operands >> strip_tac >>
  `off + type_memory_bytes ce dty <= s.vs_alloca_next /\
   FLOOKUP u.vs_allocas sm.cs_next_id = SOME (b,type_memory_bytes ce dty) /\
   (!aid q k. FLOOKUP s.vs_allocas aid = SOME (q,k) ==>
     regions_disjoint off (type_memory_bytes ce dty) q k)` by metis_tac[] >>
  drule_all immutable_normalized_allocation_extension >> strip_tac >>
  drule_all immutable_normalized_copy_bounds >> strip_tac >>
  `r.vs_current_bb = sb.cs_current_bb` by metis_tac[] >>
  drule_all immutable_normalized_copy_mem_endpoint >> strip_tac >>
  rename1 `mem_cont_sim ctx func r t` >>
  `mem_cont_sim ctx func s t` by metis_tac[memContinuationTheory.mem_cont_sim_trans] >>
  `!x. not_fresh_at sm x ==> lookup_var x t = lookup_var x s` by
    (qpat_assum `!x. not_fresh_at sm x ==> lookup_var x r = _` mp_tac >>
     qpat_assum `!x. not_fresh_at sn x ==> lookup_var x t = _` mp_tac >>
     qpat_assum `sm.cs_next_var <= sn.cs_next_var` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> metis_tac[loweringShapeDefsTheory.not_fresh_at_mono]) >>
  drule_all immutable_normalized_allocation_transport >> strip_tac >>
  qexistsl_tac [`buf`,`mid`,`sn`,`u`,`r`,`t`,`b`] >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >> first_assum ACCEPT_TAC
QED
