(* Allocation exposes the same checked SHA input at every memory bound. *)
Theory bodyFullHashShaAlloc
Ancestors
  bodyFullAllocGeneric bodyFullHashAllocFrame bodyFullHashCleanFrame
  bodyPtrHashBuiltinsAllocFrame bodyPtrHashBuiltinsShaAllocInput
  bodyPtrHashBuiltinsShaAlloc bodyPtrHashBuiltinsShaFixed
  exprSimAlloc bodyPtrDefs emitHelperProps exprLoweringProps loweringStateRelDefs
  loweringHalt allocationPtr
  compileEnv ptrDiscipline venomState venomInst venomExecSemantics
  fragExec finite_map pred_set words

Theorem sha_literal_alloc_frame_at:
  !H:(bool # bytes32 # type_value) list # num list.
  !D lo fn cenv cx es sa sm buf n s ctx d PG G tn.
    compile_alloc_buffer n sa = (buf,sm) /\ fn_has_code sa sm fn /\
    stmt_state_rel H ctx fn cenv cx es s /\ fn_inst_ids_distinct fn /\
    local_ptrs_reserved cenv sa /\ n < dimword (:256) /\
    MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)]
      [STRING #"%" (toString sa.cs_next_var)]) (fn_insts fn) /\
    ghost_inv_at D lo d cenv cx es G tn s /\
    (!x k. cenv.ce_return_buf = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
    (!x k. cenv.ce_return_pc = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) ==>
    ?t w p G1 tn1.
      run_inst_seq (emitted_insts sa sm) s = OK t /\
      stmt_state_rel H ctx fn cenv cx es t /\
      buf.buf_operand = Var p /\ eval_operand buf.buf_operand t = SOME w /\
      FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n w,n) /\
      w2n w+n < dimword (:256) /\ t.vs_memory = s.vs_memory /\
      sa.cs_next_id < sm.cs_next_id /\
      (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
      (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
        FLOOKUP t.vs_allocas aid = SOME entry) /\
      (!aid b k. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,k) ==>
        regions_disjoint (w2n w) n b k) /\
      (!name b k. local_region cenv es.scopes t name b k ==>
        regions_disjoint (w2n w) n b k) /\ not_fresh_at sm p /\
      G1 = step_prov PG G (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [p]) t /\
      tn1 = step_taint (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)] [p]) s t tn /\
      ghost_inv_at D lo d cenv cx es G1 tn1 t /\
      ghost_kept_at lo cenv es sa G tn s G1 tn1 /\
      ptr_covers G1 tn1 p t n /\ lo <= w2n w
Proof
  rpt gen_tac >> strip_tac >>
  drule_all literal_alloc_buffer_run >> strip_tac >>
  drule compile_alloc_buffer_parts >> strip_tac >>
  `emitted_insts sa sm = [mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)]
    [STRING #"%" (toString sa.cs_next_var)]]` by
    (drule compile_alloc_buffer_emission >> strip_tac >>
     drule emitted_insts_emit_inst >> simp[emitted_insts_def] >>
     strip_tac >> gvs[]) >>
  `step_inst_base (mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)]
    [STRING #"%" (toString sa.cs_next_var)]) s = OK t` by
    gvs[run_inst_seq_def, AllCaseEqs()] >>
  qabbrev_tac `i = mk_inst sa.cs_next_id ALLOCA [Lit (n2w n)]
    [STRING #"%" (toString sa.cs_next_var)]` >>
  `ghost_inv_at D lo d cenv cx es (step_prov PG G i t)
    (step_taint i s t tn) t` by
    (qunabbrev_tac `i` >> irule compile_alloc_buffer_ghost_frame_at >>
     simp[] >> conj_tac >- (qexists_tac `sa` >> simp[]) >>
     qexistsl_tac [`H`, `ctx`, `fn`] >> simp[]) >>
  `ghost_kept_at lo cenv es sa G tn s (step_prov PG G i t)
    (step_taint i s t tn)` by
    (qunabbrev_tac `i` >> irule (INST_TYPE [alpha |-> ``:256``]
       hash_compile_alloc_entry_kept_at) >>
     goal_assum (drule_at Any) >> fs[ghost_inv_at_def] >> metis_tac[]) >>
  `ptr_covers (step_prov PG G i t) (step_taint i s t tn)
    (STRING #"%" (toString sa.cs_next_var)) t n` by
    (qunabbrev_tac `i` >> drule_all alloca_step_ptr_covers >> simp[]) >>
  `lo <= w2n w` by
    (`allocas_from lo t` by fs[ghost_inv_at_def] >>
     fs[allocas_from_def] >>
     qpat_x_assum `!aid b sz. FLOOKUP t.vs_allocas aid = SOME (b,sz) ==> _`
       (qspecl_then [`sa.cs_next_id`, `w2n w`, `n`] mp_tac) >> simp[]) >>
  qexistsl_tac [`t`, `w`, `STRING #"%" (toString sa.cs_next_var)`,
    `step_prov PG G i t`, `step_taint i s t tn`] >> simp[] >>
  rpt strip_tac >> metis_tac[]
QED
