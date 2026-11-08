(* The concrete counted endpoint of a fresh buffer allocation. *)
Theory bodyIntCallStorageAllocate
Ancestors
  bodyIntCallConsumerProbe storageCopyGasPath exprSimStorageCopy
  stmtReasonLitFragMemory fragExec exprLoweringProps venomExecSemantics
  venomState venomInst context compileEnv words finite_map rich_list
  exprSimAlloc loweringPosts loweringSlice
Libs
  monadsyntax

Theorem fresh_buffer_allocation_path:
  compile_alloc_buffer nb sa = (buf,sm) /\ fn_has_code sa sm func /\
  nb < dimword(:256) /\ sa.cs_next_id NOTIN FDOM s.vs_allocas /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u x. buf.buf_operand = Var x /\
    (!y. not_fresh_at sa y ==> y <> x) /\
    gas_marked_path F ctx func s 0 (OK u) /\
    u = (update_var x (n2w s.vs_alloca_next)
      (s with <|vs_allocas := s.vs_allocas |+
           (sa.cs_next_id,(s.vs_alloca_next,nb));
         vs_alloca_next := s.vs_alloca_next + nb|>)) with
      vs_inst_idx := LENGTH sm.cs_current_insts /\
    sm.cs_current_bb = sa.cs_current_bb
Proof
  strip_tac >> drule storage_copy_alloc_layout >> strip_tac >>
  `sm.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sm` by
    metis_tac[prefix_drop_equiv, emitted_insts_def] >>
  `sm.cs_current_bb = sa.cs_current_bb` by gvs[same_blocks_def] >>
  drule_all fn_has_code_code >> strip_tac >>
  qmatch_asmsub_abbrev_tac `emitted_insts sa sm = [mk_inst _ _ _ [x]]` >>
  qabbrev_tac `a = update_var x (n2w s.vs_alloca_next)
    (s with <|vs_allocas := s.vs_allocas |+
       (sa.cs_next_id,(s.vs_alloca_next,nb));
      vs_alloca_next := s.vs_alloca_next + nb|>)` >>
  `run_inst_seq (emitted_insts sa sm) s = OK a` by
    (simp[run_inst_seq_def, step_inst_base_def, exec_alloca_def,
          mk_inst_def, FLOOKUP_DEF, Abbr `a`, w2n_n2w]) >>
  `gas_marked_path F ctx func s 0
    (OK (a with vs_inst_idx := LENGTH sm.cs_current_insts))` by
    (mp_tac (Q.SPECL [`emitted_insts sa sm`, `s`, `a`, `F`, `ctx`, `func`, `bb`]
      storage_copy_seq_path) >>
     simp[mk_inst_def, is_terminator_def] >>
     impl_tac >- (qpat_x_assum `isPREFIX _ _` mp_tac >> simp[mk_inst_def]) >>
     simp[]) >>
  qexistsl_tac [`a with vs_inst_idx := LENGTH sm.cs_current_insts`, `x`] >>
  gvs[same_blocks_def, Abbr `a`, Abbr `x`]
QED

(* Capacity and physical frame at that very counted endpoint. *)
Theorem storage_copy_allocation_endpoint:
  compile_alloc_buffer nb sa = (buf,sm) /\ fn_has_code sa sm func /\
  nb < dimword(:256) /\ sa.cs_next_id NOTIN FDOM s.vs_allocas /\
  alloca_room ctx func s /\ fn_directly_calls ctx func.fn_name name /\
  MEM func ctx.ctx_functions /\ 32*n <= nb /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?u b. gas_marked_path F ctx func s 0 (OK u) /\ b = s.vs_alloca_next /\
    eval_operand buf.buf_operand u = SOME (n2w b) /\
    eval_operand src u = eval_operand src s /\
    FLOOKUP u.vs_allocas sa.cs_next_id = SOME (b,nb) /\
    b + 32*n < 2**256 /\ n < 2**256 /\
    ~u.vs_halted /\ u.vs_current_bb = sm.cs_current_bb /\
    u.vs_inst_idx = LENGTH sm.cs_current_insts /\
    (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
    u.vs_allocas = s.vs_allocas |+ (sa.cs_next_id,(b,nb)) /\
    u.vs_alloca_next = b+nb /\
    (u with <|vs_vars := s.vs_vars; vs_allocas := s.vs_allocas;
      vs_alloca_next := s.vs_alloca_next; vs_inst_idx := s.vs_inst_idx|>) = s
Proof
  strip_tac >>
  `s.vs_alloca_next + nb < dimword(:256)` by
    (drule_all alloc_buffer_own_site_reserve >> simp[]) >>
  drule_all fresh_buffer_allocation_path >>
  disch_then (qspec_then `ctx` strip_assume_tac) >>
  qexistsl_tac [`u`, `s.vs_alloca_next`] >> simp[] >>
  `!y. src = Var y ==> y <> x` by metis_tac[] >>
  `eval_operand src u = eval_operand src s` by
    (Cases_on `src` >> gvs[eval_operand_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE]) >>
  qpat_x_assum `u = _` SUBST_ALL_TAC >>
  simp[update_var_def, lookup_var_def, eval_operand_def,
       venom_state_component_equality, FLOOKUP_UPDATE] >>
  conj_tac >- (Cases_on `src` >>
    gvs[eval_operand_def, lookup_var_def, FLOOKUP_UPDATE]) >>
  rpt conj_tac >> rpt strip_tac >>
  gvs[FLOOKUP_UPDATE, dimword_def] >> decide_tac
QED

(* Transport to the exact endpoint, rather than selecting a second run. *)
Theorem fresh_buffer_allocation_state_rel:
  compile_alloc_buffer nb sa = (buf,sm) /\ fn_has_code sa sm func /\
  nb < dimword(:256) /\ sa.cs_next_id NOTIN FDOM s.vs_allocas /\
  stmt_state_rel ctx func ce cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved ce sa /\ buf.buf_operand = Var x /\
  u = (update_var x (n2w s.vs_alloca_next)
    (s with <|vs_allocas := s.vs_allocas |+
       (sa.cs_next_id,(s.vs_alloca_next,nb));
      vs_alloca_next := s.vs_alloca_next + nb|>)) with
    vs_inst_idx := LENGTH sm.cs_current_insts ==>
  stmt_state_rel ctx func ce cx es u /\
  (!tr ty raw w. storage_holds cx tr ty raw w es s ==>
     storage_holds cx tr ty raw w es u)
Proof
  strip_tac >> drule_all buffer_alloc_code >> strip_tac >>
  drule_all literal_alloc_buffer_run >> strip_tac >>
  drule storage_copy_alloc_layout >> strip_tac >>
  `run_inst_seq (emitted_insts sa sm) s =
    OK (update_var x (n2w s.vs_alloca_next)
      (s with <|vs_allocas := s.vs_allocas |+
         (sa.cs_next_id,(s.vs_alloca_next,nb));
        vs_alloca_next := s.vs_alloca_next + nb|>))` by
    (gvs[run_inst_seq_def, step_inst_base_def, exec_alloca_def,
         mk_inst_def, FLOOKUP_DEF, w2n_n2w]) >>
  conj_tac >- gvs[stmt_state_rel_inst_idx] >>
  gvs[storage_holds_def, contract_storage_def, contract_transient_def,
      update_var_def]
QED
