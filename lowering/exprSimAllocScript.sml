(* Shared execution interface for expression buffer allocations. *)
Theory exprSimAlloc
Ancestors
  list rich_list finite_map context compileEnv loweringSlice exprLoweringProps
  emitHelperProps fragExec localPtrsProps venomInst venomState
  venomExecSemantics

Theorem literal_alloca_run[local]:
  !func cenv cx es s inst p (n:bytes32) ctx.
    stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_operands = [Lit n] /\ inst.inst_outputs = [p] /\
    not_local_ptr cenv es.scopes p ==>
    ?t w. exec_alloca inst s n = OK t /\
      stmt_state_rel ctx func cenv cx es t /\ lookup_var p t = SOME w /\
      FLOOKUP t.vs_allocas inst.inst_id = SOME (w2n w, w2n n) /\
      w2n w + w2n n < dimword (:256) /\ t.vs_memory = s.vs_memory /\
      (!x. x <> p ==> lookup_var x t = lookup_var x s) /\
      (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
         FLOOKUP t.vs_allocas aid = SOME entry) /\
      (!aid b sz. aid <> inst.inst_id /\
         FLOOKUP s.vs_allocas aid = SOME (b,sz) ==>
         regions_disjoint (w2n w) (w2n n) b sz) /\
      (!name b sz. local_region cenv es.scopes t name b sz ==>
         regions_disjoint (w2n w) (w2n n) b sz)
Proof
  rpt strip_tac >>
  `?t. exec_alloca inst s n = OK t` by
    (Cases_on `FLOOKUP s.vs_allocas inst.inst_id`
     >- simp[venomExecSemanticsTheory.exec_alloca_def] >>
     rename1 `FLOOKUP s.vs_allocas inst.inst_id = SOME entry` >>
     PairCases_on `entry` >> simp[venomExecSemanticsTheory.exec_alloca_def]) >>
  drule_all stmt_state_rel_exec_alloca >> strip_tac >>
  `alloca_inv t /\ local_ptrs_rel func cenv es.scopes t` by
    gvs[exprLoweringPropsTheory.stmt_state_rel_def, state_rel_def] >>
  qexistsl_tac [`t`, `w`] >> simp[] >>
  conj_tac
  >- (`t.vs_alloca_next < dimword (:256)` by
        metis_tac[exprLoweringPropsTheory.alloca_room_next_lt,
                  exprLoweringPropsTheory.stmt_state_rel_def] >>
      gvs[venomMemDefsTheory.alloca_inv_def, venomMemDefsTheory.alloca_next_valid_def] >>
      first_x_assum drule >> decide_tac) >>
  `t.vs_memory = s.vs_memory /\
   (!x. x <> p ==> lookup_var x t = lookup_var x s) /\
   (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
     FLOOKUP t.vs_allocas aid = SOME entry)` by
    (qpat_x_assum `exec_alloca _ _ _ = _` mp_tac >>
     Cases_on `FLOOKUP s.vs_allocas inst.inst_id`
     >- (simp[venomExecSemanticsTheory.exec_alloca_def] >> strip_tac >>
         gvs[update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
         rpt strip_tac >> Cases_on `inst.inst_id = aid` >> gvs[]) >>
     rename1 `FLOOKUP s.vs_allocas inst.inst_id = SOME entry` >>
     PairCases_on `entry` >>
     simp[venomExecSemanticsTheory.exec_alloca_def] >> strip_tac >>
     gvs[update_var_def, lookup_var_def, FLOOKUP_UPDATE]) >>
  simp[] >> conj_tac
  >- (rpt strip_tac >>
      `FLOOKUP t.vs_allocas aid = SOME (b,sz)` by metis_tac[] >>
      gvs[venomMemDefsTheory.alloca_inv_def,
          venomMemDefsTheory.allocas_non_overlapping_def,
          compileEnvTheory.regions_disjoint_def] >>
      qpat_x_assum `!a1 a2 b1 sz1 b2 sz2. _` drule >>
      disch_then (qspecl_then [`b`, `sz`, `w2n w`, `w2n n`] mp_tac) >>
      simp[arithmeticTheory.ADD_COMM]) >>
  rpt strip_tac >> irule localPtrsPropsTheory.local_ptrs_rel_alloca_disjoint >>
  goal_assum drule >> simp[] >> metis_tac[]
QED

Theorem literal_alloc_buffer_run:
  !func cenv cx es sa sm buf sz s ctx.
    compile_alloc_buffer sz sa = (buf,sm) /\
    stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sa /\ sz < dimword (:256) /\
    MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)]
      [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func) ==>
    ?t w. run_inst_seq (emitted_insts sa sm) s = OK t /\
      stmt_state_rel ctx func cenv cx es t /\
      eval_operand buf.buf_operand t = SOME w /\
      FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,sz) /\
      w2n w + sz < dimword (:256) /\ t.vs_memory = s.vs_memory /\
      sa.cs_next_id < sm.cs_next_id /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
         FLOOKUP t.vs_allocas aid = SOME entry) /\
      (!aid b len. aid < sa.cs_next_id /\
         FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
         regions_disjoint (w2n w) sz b len) /\
      (!name b len. local_region cenv es.scopes t name b len ==>
         regions_disjoint (w2n w) sz b len) /\
      (?p. buf.buf_operand = Var p /\ not_fresh_at sm p)
Proof
  rpt strip_tac >>
  qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
  simp[contextTheory.compile_alloc_buffer_def, comp_bind_def, comp_return_def] >>
  pairarg_tac >> strip_tac >> gvs[] >>
  drule emitHelperPropsTheory.emitted_insts_emit_op >> strip_tac >>
  `not_local_ptr cenv es.scopes (STRING #"%" (toString sa.cs_next_var))` by
    (irule exprLoweringPropsTheory.local_ptrs_reserved_fresh >>
     qexists_tac `sa` >> simp[]) >>
  qmatch_asmsub_abbrev_tac `MEM inst (fn_insts func)` >>
  `inst.inst_opcode = ALLOCA /\ inst.inst_operands = [Lit (n2w sz)] /\
   inst.inst_outputs = [STRING #"%" (toString sa.cs_next_var)] /\
   inst.inst_id = sa.cs_next_id` by simp[Abbr `inst`, venomInstTheory.mk_inst_def] >>
  drule_all literal_alloca_run >> strip_tac >>
  gvs[Abbr `inst`, venomInstTheory.mk_inst_def,
      wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD] >>
  qexistsl_tac [`t`, `w`] >>
  simp[exprLoweringPropsTheory.run_inst_seq_def,
       venomExecSemanticsTheory.step_inst_base_def,
       venomInstTheory.mk_inst_def, eval_operand_def,
       wordsTheory.w2n_n2w, arithmeticTheory.LESS_MOD] >>
  conj_tac
  >- (rpt strip_tac >> first_x_assum irule >>
      gvs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!aid b sz'. aid <> sa.cs_next_id /\ _ ==> _` irule >>
      qexists_tac `aid` >> simp[]) >>
  simp[not_fresh_at_def, ASCIInumbersTheory.toString_11] >>
  rpt strip_tac >> first_x_assum drule >> simp[]
QED

Theorem buffer_alloc_code:
  !size sa sb buf func.
    compile_alloc_buffer size sa = (buf, sb) /\
    fn_has_code sa sb func ==>
    MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w size)]
         [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func)
Proof
  rpt strip_tac >>
  gvs[compile_alloc_buffer_def, emitHelperTheory.emit_op_def,
      comp_bind_def, comp_return_def] >>
  gvs[fresh_id_def, fresh_var_def, emit_def, comp_bind_def,
      comp_ignore_bind_def, comp_return_def] >>
  gvs[fn_has_code_def, IS_PREFIX_APPEND] >>
  irule lookup_block_fn_insts >> goal_assum (drule_at Any) >>
  simp[MEM_APPEND]
QED

(* A bounded store into an allocation separated from local regions. *)
Theorem literal_mstore_state_rel:
  !func cenv cx es s a (w:bytes32) inst b sz ctx.
    stmt_state_rel ctx func cenv cx es s /\ b <= a /\ a + 32 <= b + sz /\
    MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) /\
    (!name lb lsz. local_region cenv es.scopes s name lb lsz ==>
       b + sz <= lb \/ lb + lsz <= b) ==>
    stmt_state_rel ctx func cenv cx es (mstore a w s)
Proof
  rpt strip_tac >>
  qpat_x_assum `stmt_state_rel ctx _ _ _ _ _` mp_tac >>
  rewrite_tac[Once exprLoweringPropsTheory.stmt_state_rel_def] >> strip_tac >>
  `local_ptrs_rel func cenv es.scopes (mstore a w s)` by
    (irule localPtrsPropsTheory.local_ptrs_rel_mstore >>
     reverse conj_tac >- gvs[state_rel_def] >>
     rpt strip_tac >>
     qpat_x_assum `!name lb lsz. local_region _ _ _ _ _ _ ==> _` drule >>
     decide_tac) >>
  `immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor es
     (mstore a w s)` by
    (irule immutables_rel_mstore_alloca >> conj_tac
     >- (qexistsl_tac [`b`, `func`, `inst`, `sz`] >> simp[]) >>
     gvs[state_rel_def]) >>
  rewrite_tac[exprLoweringPropsTheory.stmt_state_rel_def] >>
  conj_tac
  >- (irule exprLoweringPropsTheory.state_rel_frame >>
      conj_tac >- first_assum ACCEPT_TAC >>
      qexistsl_tac [`es`, `s`] >> simp[] >> simp[mstore_def]) >>
  conj_tac
  >- (irule localPtrsPropsTheory.alloca_inv_fields >>
      qexists_tac `s` >> simp[mstore_def]) >>
  conj_tac
  >- (irule exprLoweringPropsTheory.alloca_room_fields >>
      qexists_tac `s` >> simp[mstore_def]) >>
  conj_tac
  >- (irule exprLoweringPropsTheory.immutable_alloca_sep_fields >>
      qexistsl_tac [`s`, `es`] >> simp[mstore_def] >>
      rpt strip_tac >> qexists_tac `id` >>
      fs[local_region_def, lookup_var_def]) >>
  simp[mstore_def] >> metis_tac[]
QED

(* Allocation preserves label operands as well as older registers. *)
Theorem hash_alloc_buffer_labels:
  compile_alloc_buffer sz sa = (buf,sm) /\
  run_inst_seq (emitted_insts sa sm) s = OK t ==>
  t.vs_labels = s.vs_labels
Proof
  simp[contextTheory.compile_alloc_buffer_def, emitHelperTheory.emit_op_def, comp_bind_def,
       comp_return_def, comp_ignore_bind_def, fresh_id_def, fresh_var_def,
       emit_def] >> strip_tac >> gvs[emitted_insts_def,
       rich_listTheory.DROP_LENGTH_APPEND, run_inst_seq_def,
       step_inst_base_def, mk_inst_def, exec_alloca_def, AllCaseEqs()] >>
  gvs[update_var_def]
QED

Theorem alloc_buffer_source_frag:
  !ctx func cenv cx es sm mid buf sz s src a R.
    compile_alloc_buffer sz sm = (buf,mid) /\ fn_has_code sm mid func /\
    stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
    local_ptrs_reserved cenv sm /\ sz < dimword (:256) /\
    eval_operand src s = SOME a /\
    (!x. src = Var x ==> not_fresh_at sm x) ==>
    ?u w. frag_exec ctx sm mid (\z. z = s) (\z. z = u) R /\
      eval_operand src u = SOME a /\
      stmt_state_rel ctx func cenv cx es u /\
      eval_operand buf.buf_operand u = SOME w /\
      FLOOKUP u.vs_allocas sm.cs_next_id = SOME (w2n w,sz) /\
      w2n w + sz < dimword (:256) /\ u.vs_memory = s.vs_memory /\
      sm.cs_next_id < mid.cs_next_id /\
      (!x. not_fresh_at sm x ==> lookup_var x u = lookup_var x s) /\
      (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
         FLOOKUP u.vs_allocas aid = SOME entry) /\
      (!aid b len. aid < sm.cs_next_id /\
         FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
         regions_disjoint (w2n w) sz b len) /\
      (!name b len. local_region cenv es.scopes u name b len ==>
         regions_disjoint (w2n w) sz b len) /\
      (?p. buf.buf_operand = Var p /\ not_fresh_at mid p)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all buffer_alloc_code >> strip_tac >>
  drule_all literal_alloc_buffer_run >> strip_tac >>
  `t.vs_labels = s.vs_labels` by metis_tac[hash_alloc_buffer_labels] >>
  `eval_operand src t = SOME a` by
    (Cases_on `src` >> gvs[eval_operand_def]) >>
  qexistsl_tac [`t with vs_inst_idx := LENGTH mid.cs_current_insts`, `w`] >>
  simp[] >> reverse conj_tac
  >- (Cases_on `src` >>
      gvs[stmt_state_rel_inst_idx, eval_operand_def, lookup_var_def,
          local_region_def] >> metis_tac[]) >>
  irule frag_exec_run_inst_seq >>
  qpat_x_assum `compile_alloc_buffer _ _ = _` mp_tac >>
  simp[contextTheory.compile_alloc_buffer_def, emitHelperTheory.emit_op_def,
       comp_bind_def, comp_return_def] >> pairarg_tac >> strip_tac >> gvs[] >>
  gvs[fresh_id_def, fresh_var_def, emit_def, comp_bind_def,
      comp_ignore_bind_def, comp_return_def, emitted_insts_def,
      rich_listTheory.DROP_LENGTH_APPEND, rich_listTheory.IS_PREFIX_APPEND,
      mk_inst_def, is_terminator_def]
QED
