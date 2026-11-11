Theory placeMemoryStaging
Ancestors
  exprSimAlloc placeMemoryTypedPrimitive placeMemoryPrimitiveForward
  placeMemoryCopyEffect context exprLoweringProps compileEnv loweringStateRelDefs venomExecSemantics
  venomState venomInst emitHelper fragExec rich_list instIdxIndep finite_map
  loweringHalt abiTupleProps placeMemoryCopyFrames fragGasMode

Theorem compile_alloc_buffer_forward:
  compile_alloc_buffer n sa = (buf,sm) /\
  stmt_state_rel ctx func cenv cx ee s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ n < dimword (:256) /\
  fn_has_code sa sm func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?r tw. gas_marked_path F ctx func s 0 (OK r) /\
    stmt_state_rel ctx func cenv cx ee r /\
    eval_operand buf.buf_operand r = SOME tw /\
    FLOOKUP r.vs_allocas sa.cs_next_id = SOME (w2n tw,n) /\
    w2n tw + n < dimword (:256) /\ r.vs_memory = s.vs_memory /\
    sa.cs_next_id < sm.cs_next_id /\
    (!x. not_fresh_at sa x ==> lookup_var x r = lookup_var x s) /\
    (!aid e. FLOOKUP s.vs_allocas aid = SOME e ==>
       FLOOKUP r.vs_allocas aid = SOME e) /\
    (!name b len. local_region cenv ee.scopes r name b len ==>
       regions_disjoint (w2n tw) n b len) /\
    (?p. buf.buf_operand = Var p /\ not_fresh_at sm p) /\
    ((FLOOKUP s.vs_allocas sa.cs_next_id = NONE /\ w2n tw = s.vs_alloca_next) \/
      FLOOKUP s.vs_allocas sa.cs_next_id = SOME (w2n tw,n)) /\
    (r with <|vs_vars := s.vs_vars; vs_allocas := s.vs_allocas;
      vs_alloca_next := s.vs_alloca_next; vs_inst_idx := s.vs_inst_idx|>) = s /\
    ~r.vs_halted /\ r.vs_current_bb = sm.cs_current_bb /\
    r.vs_inst_idx = LENGTH sm.cs_current_insts
Proof
  rpt strip_tac >>
  drule_all buffer_alloc_code >> strip_tac >>
  drule_all literal_alloc_buffer_run >> strip_tac >>
  `sm.cs_current_bb = sa.cs_current_bb /\
   sm.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sm /\
   EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
     (emitted_insts sa sm) /\
   EVERY (\i. i.inst_opcode <> GAS) (emitted_insts sa sm)` by
    (qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
     simp[compile_alloc_buffer_def, emit_op_def, comp_bind_def, comp_return_def] >>
     pairarg_tac >> strip_tac >>
     gvs[fresh_id_def, fresh_var_def, emit_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
         emitted_insts_def, DROP_APPEND, mk_inst_def, is_terminator_def]) >>
  `gas_marked_path F ctx func s 0
    (OK (t with vs_inst_idx := LENGTH sm.cs_current_insts))` by
    (irule straight_line_zero_gas_path >> simp[] >> metis_tac[]) >>
  `((FLOOKUP s.vs_allocas sa.cs_next_id = NONE /\ w2n w = s.vs_alloca_next) \/
    FLOOKUP s.vs_allocas sa.cs_next_id = SOME (w2n w,n)) /\
   (t with <|vs_vars := s.vs_vars; vs_allocas := s.vs_allocas;
      vs_alloca_next := s.vs_alloca_next; vs_inst_idx := s.vs_inst_idx|>) = s /\
   ~t.vs_halted /\ t.vs_current_bb = s.vs_current_bb` by
     suspend "allocation_effect" >>
  (qpat_assum `!x. not_fresh_at sa x ==> _`
    (assume_tac o SRULE [lookup_var_def]) >>
  qpat_assum `!name b len. local_region _ _ _ _ _ _ ==> _`
    (assume_tac o SRULE [local_region_def, lookup_var_def]) >>
  qpat_assum `(t with <|vs_vars := _; vs_allocas := _; vs_alloca_next := _; vs_inst_idx := _|>) = s`
    (strip_assume_tac o SRULE [venom_state_component_equality]) >>
  qexistsl_tac [`t with vs_inst_idx := LENGTH sm.cs_current_insts`, `w`] >>
  simp[stmt_state_rel_inst_idx, eval_op_inst_idx, lookup_var_def,
       local_region_def, venom_state_component_equality] >>
  qpat_x_assum `!name b len. (?entry p w. _) ==> _` mp_tac >> simp[])
QED
Resume compile_alloc_buffer_forward[allocation_effect]:
  `s.vs_alloca_next < dimword (:256)` by
    metis_tac[alloca_room_next_lt, stmt_state_rel_def] >>
  qpat_x_assum `sm.cs_current_insts = _` kall_tac >>
  qpat_x_assum `gas_marked_path _ _ _ _ _ _` kall_tac >>
  qpat_x_assum `EVERY _ (emitted_insts sa sm)` kall_tac >>
  qpat_x_assum `EVERY _ (emitted_insts sa sm)` kall_tac >>
  qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
  simp[compile_alloc_buffer_def, emit_op_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> strip_tac >>
  gvs[fresh_id_def, fresh_var_def, emit_def, comp_bind_def,
      comp_ignore_bind_def, comp_return_def, emitted_insts_def, DROP_APPEND] >>
  qpat_x_assum `run_inst_seq _ _ = OK t` mp_tac >>
  simp[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def, eval_operand_def] >>
  Cases_on `FLOOKUP s.vs_allocas sa.cs_next_id`
  >- (simp[exec_alloca_def] >> strip_tac >>
      gvs[update_var_def, lookup_var_def, eval_operand_def, FLOOKUP_UPDATE,
          wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD] >>
      simp[venom_state_component_equality]) >>
  rename1 `FLOOKUP s.vs_allocas sa.cs_next_id = SOME entry` >>
  PairCases_on `entry` >> simp[exec_alloca_def] >> strip_tac >>
  gvs[update_var_def, lookup_var_def, eval_operand_def, venom_state_component_equality]
QED
Finalise compile_alloc_buffer_forward

Theorem compile_staging_prefix_forward:
  compile_alloc_buffer n sa = (buf,sm) /\
  compile_copy_memory buf.buf_operand op n sm = ((),sn) /\
  stmt_state_rel ctx func cenv cx ee s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sa /\ n < dimword (:256) /\
  fn_has_code sa sn func /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!x. op = Var x ==> not_fresh_at sa x) /\
  eval_operand op s = SOME sw /\ n = type_memory_size stv /\
  val_wf stv v /\ val_in_memory stv v (w2n sw) s.vs_memory /\
  w2n sw + n <= s.vs_alloca_next /\
  (!aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) /\
      sa.cs_next_id <= aid ==> w2n sw + n <= b \/ b + sz <= w2n sw) ==>
  ?r u tw. gas_marked_path F ctx func s 0 (OK r) /\
    stmt_state_rel ctx func cenv cx ee r /\
    eval_operand buf.buf_operand r = SOME tw /\
    FLOOKUP r.vs_allocas sa.cs_next_id = SOME (w2n tw,n) /\
    w2n tw + n < dimword (:256) /\ r.vs_memory = s.vs_memory /\
    sa.cs_next_id < sm.cs_next_id /\
    (!x. not_fresh_at sa x ==> lookup_var x r = lookup_var x s) /\
    (!aid e. FLOOKUP s.vs_allocas aid = SOME e ==>
       FLOOKUP r.vs_allocas aid = SOME e) /\
    (!name b len. local_region cenv ee.scopes r name b len ==>
       regions_disjoint (w2n tw) n b len) /\
    (?p. buf.buf_operand = Var p /\ not_fresh_at sm p) /\
    ((FLOOKUP s.vs_allocas sa.cs_next_id = NONE /\ w2n tw = s.vs_alloca_next) \/
      FLOOKUP s.vs_allocas sa.cs_next_id = SOME (w2n tw,n)) /\
    (r with <|vs_vars := s.vs_vars; vs_allocas := s.vs_allocas;
      vs_alloca_next := s.vs_alloca_next; vs_inst_idx := s.vs_inst_idx|>) = s /\
    ~r.vs_halted /\ r.vs_current_bb = sm.cs_current_bb /\
    r.vs_inst_idx = LENGTH sm.cs_current_insts /\
    gas_marked_path F ctx func r 0 (OK u) /\
    gas_marked_path F ctx func s 0 (OK u) /\
    val_in_memory stv v (w2n tw) u.vs_memory /\
    val_in_memory stv v (w2n sw) u.vs_memory /\
    (w2n sw+n <= w2n tw \/ w2n tw+n <= w2n sw) /\
    u.vs_allocas = r.vs_allocas /\
    (u with <|vs_vars := r.vs_vars; vs_memory := r.vs_memory;
      vs_prev_bb := r.vs_prev_bb; vs_current_bb := r.vs_current_bb;
      vs_inst_idx := r.vs_inst_idx|>) = r /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
    (!a len. a+len <= w2n tw \/ w2n tw+n <= a ==>
       mem_bytes_at a len u.vs_memory = mem_bytes_at a len s.vs_memory) /\
    (!name b len. local_region cenv ee.scopes r name b len ==>
       mem_bytes_at b len u.vs_memory = mem_bytes_at b len s.vs_memory) /\
    LENGTH s.vs_memory <= LENGTH u.vs_memory /\
    ~u.vs_halted /\ u.vs_current_bb = sn.cs_current_bb /\
    u.vs_inst_idx = LENGTH sn.cs_current_insts /\
    eval_operand buf.buf_operand u = SOME tw
Proof
  strip_tac >>
  `cs_extends sa sm` by metis_tac[compile_alloc_buffer_extends] >>
  `cs_extends sm sn` by
    (drule_all compile_copy_memory_extends >> strip_tac >>
     gvs[same_blocks_def] >> irule cs_extends_same_block >> simp[IS_PREFIX_APPEND]) >>
  drule_all fn_has_code_split >> strip_tac >>
  drule_all compile_alloc_buffer_forward >> strip_tac >>
  `eval_operand op r = SOME sw` by
    (qpat_assum `(r with <|vs_vars := _; vs_allocas := _;
        vs_alloca_next := _; vs_inst_idx := _|>) = s`
       (strip_assume_tac o SRULE [venom_state_component_equality]) >>
     Cases_on `op` >> gvs[eval_operand_def, lookup_var_def]) >>
  `w2n sw + n <= w2n tw \/ w2n tw + n <= w2n sw` by
    (first_x_assum (qspecl_then [`sa.cs_next_id`, `w2n tw`, `n`] mp_tac) >>
     simp[] >> decide_tac) >>
  drule_all compile_copy_memory_forward >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  `gas_marked_path F ctx func s 0 (OK t)` by
    (drule_all gas_marked_path_then >> simp[]) >>
  `val_in_memory stv v (w2n tw) t.vs_memory` by
    (irule valueEncodingPropsTheory.val_in_memory_relocate >>
     conj_tac >- simp[] >> qexistsl_tac [`s.vs_memory`, `n`, `w2n sw`] >> simp[]) >>
  `val_in_memory stv v (w2n sw) t.vs_memory` by
    (irule val_in_memory_outside_write >>
     conj_tac >- simp[] >> qexistsl_tac [`w2n tw`, `s.vs_memory`, `n`] >>
     metis_tac[]) >>
  qexistsl_tac [`r`, `t`, `tw`] >> simp[] >>
  rpt conj_tac >> rpt strip_tac >>
  gvs[regions_disjoint_def, eval_operand_def, lookup_var_def] >>
  metis_tac[]
QED
