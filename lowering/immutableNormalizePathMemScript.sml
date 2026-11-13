(* Counted paths for allocation and typed normalization before an immutable write. *)
Theory immutableNormalizePathMem
Ancestors
  externalReturnNormalizeRun externalNormalizePremises typedStorePathEndpoint
  typedStoreAllocationFrame typedNormalizeStraightPathMem fragGasMode memSafeRun instMemFrontier
  memContinuation loweringHalt exprLoweringProps localPtrsProps
  exprSimDefs loweringPosts fragExecMem venomState venomExecSemantics
  compileEnv context words arithmetic finite_map

Theorem normalize_alloc_mem_path[local]:
  compile_alloc_buffer n sm = (buf,mid) /\ fn_has_code sm mid func /\
  exec_alloca (mk_inst sm.cs_next_id ALLOCA [Lit (n2w n)]
    [STRING #"%" (toString sm.cs_next_var)]) s (n2w n : bytes32) = OK t /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  gas_marked_path T ctx func s 0
    (OK (t with vs_inst_idx := LENGTH mid.cs_current_insts))
Proof
  strip_tac >> drule compile_alloc_buffer_insts >> strip_tac >>
  qabbrev_tac `code = [mk_inst sm.cs_next_id ALLOCA [Lit (n2w n)]
    [STRING #"%" (toString sm.cs_next_var)]]` >>
  `run_inst_seq code s = OK t` by
    simp[Abbr `code`, run_inst_seq_def, step_inst_base_opcode_eqs,
      eval_operand_def] >>
  `run_inst_seq_mem_ok code s` by
    (simp[Abbr `code`, run_inst_seq_mem_ok_last] >>
     irule below_frontier_no_ranges >> simp[venomInstTheory.mk_inst_def]) >>
  mp_tac (Q.INST [`sa` |-> `sm`, `sb` |-> `mid`, `code` |-> `code`,
    `s` |-> `s`, `t` |-> `t`, `ctx` |-> `ctx`, `func` |-> `func`]
    typed_normalize_straight_mem_path) >>
  simp[Abbr `code`, venomInstTheory.mk_inst_def,
    venomInstTheory.is_terminator_def]
QED

Theorem immutable_normalize_mem_path_endpoint:
  compile_alloc_buffer (type_memory_bytes ce dty) sm = (buf,mid) /\
  compile_store_memory_typed ce buf.buf_operand dty src sty mid = ((),sb) /\
  fn_has_code sm mid func /\ fn_has_code mid sb func /\ fn_inst_ids_distinct func /\
  stmt_state_rel ctx func ce cx es s /\ local_ptrs_reserved ce sm /\
  expr_val_at ce cx sty sa sm es v src s /\ expr_val_rel cx sty v src s /\
  type_widens_to (get_tenv cx) sty dty /\ sty <> dty /\
  ~is_word_type dty /\ ~(is_bytestring_type dty /\ is_bytestring_type sty) /\
  evaluate_type (get_tenv cx) sty = SOME stv /\ value_has_type stv v /\
  (!ty tv. evaluate_type (get_tenv cx) ty = SOME tv ==>
     type_memory_bytes ce ty = type_memory_size tv) /\
  type_memory_bytes ce dty < dimword (:256) /\
  acyclic_struct_metadata ce.ce_struct_fields /\
  sfields_tenv_consistent ce.ce_struct_fields (get_tenv cx) /\
  (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !tv. evaluate_type (get_tenv cx) fty = SOME tv ==>
      sz = type_memory_size tv) fields) /\
  (emitted_blocks mid sb <> [] ==>
    ?bb. lookup_block sb.cs_current_bb func.fn_blocks = SOME bb /\
      phi_prefix_length bb.bb_instructions = 0) /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\ eval_operand src s = SOME p /\
  (!x. src = Var x ==> not_fresh_at sm x) ==>
  ?dtv u t b. evaluate_type (get_tenv cx) dty = SOME dtv /\
    value_has_type dtv v /\ mem_cont_sim ctx func s u /\
    mem_cont_sim ctx func u t /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    eval_operand buf.buf_operand t = SOME (n2w b) /\
    val_in_memory dtv v b t.vs_memory /\
    b + type_memory_size dtv <= t.vs_alloca_next /\
    b + type_memory_size dtv < dimword (:256) /\
    (w2n p + type_memory_size stv <= b \/
      b + type_memory_size dtv <= w2n p) /\
    alloca_inv t /\ alloca_room ctx func t /\
    t.vs_allocas = u.vs_allocas /\ t.vs_alloca_next = u.vs_alloca_next /\
    u.vs_memory = s.vs_memory /\
    (!q k. q+k <= b \/ b+type_memory_size dtv <= q ==>
       mem_bytes_at q k t.vs_memory = mem_bytes_at q k s.vs_memory) /\
    (t with <|vs_vars := u.vs_vars; vs_memory := u.vs_memory;
      vs_current_bb := mid.cs_current_bb; vs_inst_idx := LENGTH mid.cs_current_insts;
      vs_prev_bb := u.vs_prev_bb|>) = u /\
    (!x. not_fresh_at sm x ==> lookup_var x t = lookup_var x s) /\
    exec_alloca (mk_inst sm.cs_next_id ALLOCA
      [Lit (n2w (type_memory_bytes ce dty))]
      [STRING #"%" (toString sm.cs_next_var)]) s
      (n2w (type_memory_bytes ce dty) : bytes32) =
      OK (u with vs_inst_idx := s.vs_inst_idx) /\
    FLOOKUP u.vs_allocas sm.cs_next_id = SOME (b,type_memory_size dtv) /\
    gas_marked_path T ctx func s 0 (OK u) /\
    gas_marked_path T ctx func u 0 (OK t) /\
    gas_marked_path T ctx func s 0 (OK t)
Proof
  strip_tac >> drule_all normalize_return_typed_windows >>
  disch_then (qx_choose_then `dtv` (qx_choose_then `t`
    (qx_choose_then `b` (map_every assume_tac o CONJUNCTS)))) >>
  `b < dimword (:256)` by decide_tac >>
  `FLOOKUP t.vs_allocas sm.cs_next_id = SOME (b,type_memory_size dtv)` by
    (drule_all normalize_alloc_registered >> simp[]) >>
  drule_all normalize_alloc_mem_cont >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  drule_all normalize_alloc_mem_path >>
  disch_then (qspec_then `ctx` assume_tac) >>
  qmatch_asmsub_abbrev_tac `mem_cont_sim ctx func s u` >>
  `t.vs_inst_idx = s.vs_inst_idx` by
    (qpat_x_assum `exec_alloca _ _ _ = OK t` mp_tac >>
     simp[exec_alloca_def, venomInstTheory.mk_inst_def, AllCaseEqs(), update_var_def] >>
     strip_tac >> gvs[]) >>
  `u.vs_inst_idx = LENGTH mid.cs_current_insts /\
   eval_operand src u = SOME p /\ eval_operand buf.buf_operand u = SOME (n2w b) /\
   u.vs_memory = t.vs_memory /\ u.vs_alloca_next = t.vs_alloca_next` by
    simp[Abbr `u`, eval_operand_def, lookup_var_def] >>
  drule compile_alloc_buffer_parts >> strip_tac >>
  `!x. buf.buf_operand = Var x \/ src = Var x ==> not_fresh_at mid x` by
    (gen_tac >> strip_tac >> gvs[] >> metis_tac[]) >>
  `w2n (n2w b : bytes32) = b` by
    (simp[w2n_n2w] >> irule LESS_MOD >> decide_tac) >>
  `alloca_inv u /\ alloca_room ctx func u` by
    (conj_tac
     >- (irule alloca_inv_fields >> qexists_tac `t` >> simp[Abbr `u`]) >>
     irule alloca_room_fields >> qexists_tac `t` >> simp[Abbr `u`]) >>
  suspend "store"
QED

Resume immutable_normalize_mem_path_endpoint[store]:
  `val_in_memory stv v (w2n p) u.vs_memory /\
   w2n p + type_memory_size stv <= u.vs_alloca_next /\
   w2n (n2w b : bytes32) + type_memory_size dtv <= u.vs_alloca_next /\
   w2n p + type_memory_size stv < dimword (:256) /\
   w2n (n2w b : bytes32) + type_memory_size dtv < dimword (:256)` by metis_tac[] >>
  Q.SUBGOAL_THEN
    `w2n p + type_memory_size stv <= w2n (n2w b : bytes32) \/
      w2n (n2w b : bytes32) + type_memory_size dtv <= w2n p` assume_tac
  >- metis_tac[] >>
  drule_all typed_store_mem_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  rename1 `mem_cont_sim ctx func u z` >>
  `z.vs_allocas = u.vs_allocas /\ z.vs_alloca_next = u.vs_alloca_next` by
    (irule typed_store_frame_allocations >> goal_assum (drule_at Any)) >>
  `alloca_inv z /\ alloca_room ctx func z` by
    (irule typed_store_frame_resources >> goal_assum (drule_at Any) >> simp[]) >>
  `gas_marked_path T ctx func s 0 (OK z)` by
    (irule (SRULE [] (Q.INST [`n` |-> `0`, `m` |-> `0`]
      gas_marked_path_then)) >> qexists_tac `u` >> simp[]) >>
  qexistsl_tac [`dtv`,`u`,`z`,`b`] >> simp[] >>
  suspend "frame"
QED

Resume immutable_normalize_mem_path_endpoint[frame]:
  conj_tac
  >- (simp[eval_operand_def] >>
      qpat_x_assum `!x. not_fresh_at mid x ==> _` (qspec_then `STRING #"%" (toString sm.cs_next_var)` mp_tac) >>
      gvs[eval_operand_def]) >>
  conj_tac >- metis_tac[] >>
  conj_tac >- (rpt strip_tac >> metis_tac[ADD_COMM]) >>
  drule_at (Pos (el 2)) stmtSimDeclPathTheory.exec_alloca_frames >>
  simp[emitHelperPropsTheory.mk_inst_outputs] >> strip_tac >>
  reverse conj_tac
  >- (conj_tac >- suspend "allocation_execution" >> simp[Abbr `u`]) >>
  simp[Abbr `u`, lookup_var_def] >> metis_tac[lookup_var_def]
QED

Resume immutable_normalize_mem_path_endpoint[allocation_execution]:
  `(u with vs_inst_idx := s.vs_inst_idx) = t` by
        (qunabbrev_tac `u` >>
         qpat_x_assum `t.vs_inst_idx = s.vs_inst_idx` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >>
         simp[venom_state_component_equality]) >>
      qpat_assum `exec_alloca _ _ _ = OK t` mp_tac >>
      qpat_assum `type_memory_bytes ce dty = type_memory_size dtv` mp_tac >>
      qpat_assum `(u with vs_inst_idx := s.vs_inst_idx) = t` mp_tac >>
      qpat_assum `s.vs_inst_idx = LENGTH sm.cs_current_insts` mp_tac >>
      POP_ASSUM_LIST (K all_tac) >> simp[] >> metis_tac[]
QED

Finalise immutable_normalize_mem_path_endpoint
