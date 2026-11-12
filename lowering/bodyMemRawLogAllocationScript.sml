(* Counted memory allocation prefix for fixed RawLog payloads. *)
Theory bodyMemRawLogAllocation
Ancestors
  exprSimMemUnwrap bodySimCallRawLog bodySimRawLogTails exprSimPrecompiles exprSimWordArgs
  exprSimProps compileEnv venomState words list

Theorem raw_log_alloc_mem_counted:
  compile_alloc_buffer sz sm = (buf,sn) /\ fn_has_code sm sn func /\
  stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
  local_ptrs_reserved cenv sm /\ sz < dimword (:256) /\
  wb_frame cenv es0 es sa s0 s /\ sa.cs_next_var <= sm.cs_next_var /\
  alloca_history func s /\
  ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
  ?t w. gas_path_mem ctx func s 0 (OK t) /\
    stmt_state_rel ctx func cenv cx es t /\ wb_frame cenv es0 es sa s0 t /\
    eval_operand buf.buf_operand t = SOME w /\
    FLOOKUP t.vs_allocas sm.cs_next_id = SOME (w2n w,sz) /\
    w2n w + sz < dimword (:256) /\ t.vs_memory = s.vs_memory /\
    sm.cs_next_id < sn.cs_next_id /\
    (!x. not_fresh_at sm x ==> lookup_var x t = lookup_var x s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
       FLOOKUP t.vs_allocas aid = SOME entry) /\
    (!aid b len. aid < sm.cs_next_id /\
       FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
       regions_disjoint (w2n w) sz b len) /\
    (!name b len. local_region cenv es.scopes t name b len ==>
       regions_disjoint (w2n w) sz b len) /\
    (?p. buf.buf_operand = Var p /\ not_fresh_at sn p) /\
    ~t.vs_halted /\ t.vs_current_bb = sn.cs_current_bb /\
    t.vs_inst_idx = LENGTH sn.cs_current_insts /\
    alloca_history func t /\ s.vs_alloca_next <= t.vs_alloca_next /\
    w2n w + sz <= t.vs_alloca_next
Proof
  strip_tac >>
  `eval_operand (Lit 0w) s = SOME 0w /\
   (!x. Lit 0w = Var x ==> not_fresh_at sm x)` by simp[eval_operand_def] >>
  drule_all alloc_buffer_source_path_mem >> strip_tac >>
  qexistsl_tac [`u`, `w`] >> simp[] >>
  conj_tac
  >- (irule wb_frame_readonly_tail >> qexistsl_tac [`sm`, `s`] >> simp[]) >>
  conj_tac >> first_assum ACCEPT_TAC
QED
