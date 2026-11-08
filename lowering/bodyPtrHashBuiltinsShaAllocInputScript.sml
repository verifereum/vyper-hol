(* Input ownership keeps allocation's new taint away from hash read bytes. *)
Theory bodyPtrHashBuiltinsShaAllocInput
Ancestors
  bodyPtrHashBuiltinsInputWindow bodyPtrHashBuiltinsAllocFrame arithmetic compileEnv pred_set exprSimAlloc emitHelperProps exprLoweringProps
  bodyPtrDefs ptrDiscipline venomState venomInst words finite_map loweringHalt

Theorem hash_owned_window_excludes_allocation:
  (n = 0 \/
   (?aid b k. FLOOKUP s.vs_allocas aid = SOME (b,k) /\
      aid < sa.cs_next_id /\ b <= a /\ a+n <= b+k) \/
   (?name b k. local_region cenv es.scopes s name b k /\
      b <= a /\ a+n <= b+k)) /\
  (!aid b k. aid < sa.cs_next_id /\
     FLOOKUP s.vs_allocas aid = SOME (b,k) ==> regions_disjoint out m b k) /\
  (!name b k. local_region cenv es.scopes s name b k ==>
     regions_disjoint out m b k) ==>
  !i. a <= i /\ i < a+n ==> ~(out <= i /\ i < out+m)
Proof
  rpt strip_tac
  >- decide_tac
  >- (qpat_x_assum `!aid b k. _` (drule_all_then mp_tac) >>
      simp[regions_disjoint_def] >> decide_tac)
  >> qpat_x_assum `!name b k. _` (drule_all_then mp_tac) >>
  simp[regions_disjoint_def] >> decide_tac
QED

Theorem hash_clean_window_allocation_taint:
  (!i. a <= i /\ i < a+n ==> i NOTIN tn.t_mem) /\
  (!i. a <= i /\ i < a+n ==> ~(out <= i /\ i < out+m)) /\
  tn1.t_mem SUBSET tn.t_mem UNION {i | out <= i /\ i < out+m} ==>
  !i. a <= i /\ i < a+n ==> i NOTIN tn1.t_mem
Proof
  simp[SUBSET_DEF] >> metis_tac[]
QED

Theorem hash_literal_alloc_memory_taint:
  compile_alloc_buffer m sa = (buf,sm) /\
  stmt_state_rel ctx fn cenv cx es s /\ m < dimword (:256) /\
  MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w m)]
    [STRING #"%" (toString sa.cs_next_var)]) (fn_insts fn) /\
  run_inst_seq (emitted_insts sa sm) s = OK t /\
  buf.buf_operand = Var q /\ FLOOKUP t.vs_allocas sa.cs_next_id = SOME (b,m) ==>
  (step_taint (mk_inst sa.cs_next_id ALLOCA [Lit (n2w m)] [q]) s t tn).t_mem
    SUBSET tn.t_mem UNION {i | b <= i /\ i < b+m}
Proof
  rpt strip_tac >> drule compile_alloc_buffer_parts >> strip_tac >>
  `emitted_insts sa sm = [mk_inst sa.cs_next_id ALLOCA [Lit (n2w m)]
    [STRING #"%" (toString sa.cs_next_var)]]` by
    (drule compile_alloc_buffer_emission >> strip_tac >>
     drule emitted_insts_emit_inst >> simp[emitted_insts_def] >>
     strip_tac >> gvs[]) >>
  `step_inst_base (mk_inst sa.cs_next_id ALLOCA [Lit (n2w m)]
    [STRING #"%" (toString sa.cs_next_var)]) s = OK t` by
    gvs[run_inst_seq_def, AllCaseEqs()] >>
  drule_all hash_alloca_exterior_effects >>
  disch_then (qspecl_then [`ARB`, `FEMPTY`, `tn`] strip_assume_tac) >> gvs[]
QED

Theorem hash_old_operand_frame:
  t.vs_labels = s.vs_labels /\
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
  ghost_kept cenv es sa G tn s G1 tn1 /\
  (!x. value = Var x ==> not_fresh_at sa x) /\
  eval_operand value s = SOME w /\ op_taint tn value = {} ==>
  eval_operand value t = SOME w /\ op_taint tn1 value = {}
Proof
  Cases_on `value` >> simp[eval_operand_def, op_taint_def, ghost_kept_def] >>
  metis_tac[]
QED

Theorem hash_old_pointer_frame:
  (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
  ghost_kept cenv es sa G tn s G1 tn1 /\ not_fresh_at sa p /\
  ptr_covers G tn p s n ==>
  ptr_covers G1 tn1 p t n
Proof
  simp[ghost_kept_def, ptr_covers_def] >> metis_tac[]
QED

Theorem hash_literal_alloc_input_frame:
  !fn cenv cx es sa sm buf m s ctx d PG G tn p len w n.
  compile_alloc_buffer m sa = (buf,sm) /\
  stmt_state_rel ctx fn cenv cx es s /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved cenv sa /\ m < dimword (:256) /\
  MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w m)]
    [STRING #"%" (toString sa.cs_next_var)]) (fn_insts fn) /\
  ghost_inv d cenv cx es G tn s /\
  (!x k. cenv.ce_return_buf = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
  (!x k. cenv.ce_return_pc = SOME (PtrVar (Var x) k) ==> not_fresh_at sa x) /\
  eval_operand (Var p) s = SOME w /\ eval_operand len s = SOME n /\
  ptr_covers G tn p s (w2n n) /\ op_taint tn len = {} /\
  (!i. w2n w <= i /\ i < w2n w+w2n n ==> i NOTIN tn.t_mem) /\
  (!x. x=p \/ len=Var x ==> not_fresh_at sa x) /\
  (w2n n = 0 \/
   (?aid b k. FLOOKUP s.vs_allocas aid = SOME (b,k) /\
      aid < sa.cs_next_id /\ b <= w2n w /\ w2n w+w2n n <= b+k) \/
   (?name b k. local_region cenv es.scopes s name b k /\
      b <= w2n w /\ w2n w+w2n n <= b+k)) ==>
  ?t v q G1 tn1.
    run_inst_seq (emitted_insts sa sm) s = OK t /\
    stmt_state_rel ctx fn cenv cx es t /\
    buf.buf_operand = Var q /\ eval_operand buf.buf_operand t = SOME v /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n v,m) /\
    w2n v+m < dimword (:256) /\ t.vs_memory = s.vs_memory /\
    sa.cs_next_id < sm.cs_next_id /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP t.vs_allocas aid = SOME entry) /\
    (!aid b k. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,k) ==>
      regions_disjoint (w2n v) m b k) /\
    (!name b k. local_region cenv es.scopes t name b k ==>
      regions_disjoint (w2n v) m b k) /\ not_fresh_at sm q /\
    G1 = step_prov PG G (mk_inst sa.cs_next_id ALLOCA [Lit (n2w m)] [q]) t /\
    tn1 = step_taint (mk_inst sa.cs_next_id ALLOCA [Lit (n2w m)] [q]) s t tn /\
    ghost_inv d cenv cx es G1 tn1 t /\ ghost_kept cenv es sa G tn s G1 tn1 /\
    ptr_covers G1 tn1 q t m /\
    eval_operand (Var p) t = SOME w /\ eval_operand len t = SOME n /\
    ptr_covers G1 tn1 p t (w2n n) /\ op_taint tn1 len = {} /\
    (!i. w2n w <= i /\ i < w2n w+w2n n ==> i NOTIN tn1.t_mem)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all hash_literal_alloc_buffer_frame >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  `t.vs_labels = s.vs_labels` by metis_tac[hash_alloc_buffer_labels] >>
  `not_fresh_at sa p` by metis_tac[] >>
  `eval_operand (Var p) t = SOME w` by
    (gvs[eval_operand_def] >> metis_tac[]) >>
  `!x. len = Var x ==> not_fresh_at sa x` by metis_tac[] >>
  `eval_operand len t = SOME n /\ op_taint tn1 len = {}` by
    (drule_all hash_old_operand_frame >> simp[]) >>
  `ptr_covers G1 tn1 p t (w2n n)` by
    (drule_all hash_old_pointer_frame >> simp[]) >>
  `!i. w2n w <= i /\ i < w2n w+w2n n ==> i NOTIN tn1.t_mem` by
    (ho_match_mp_tac (Q.INST [`out` |-> `w2n (w':bytes32)`] hash_clean_window_allocation_taint) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     reverse conj_tac
     >- (qpat_x_assum `tn1 = _` SUBST1_TAC >>
         drule_all hash_literal_alloc_memory_taint >> simp[]) >>
     ho_match_mp_tac hash_owned_window_excludes_allocation >>
     conj_tac >- metis_tac[] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     `!name b k. local_region cenv es.scopes s name b k ==>
        local_region cenv es.scopes t name b k` by
       (gvs[local_region_def, local_ptrs_reserved_def] >> metis_tac[]) >>
     metis_tac[]) >>
  qexistsl_tac [`t`, `w'`, `p'`, `G1`, `tn1`] >> asm_rewrite_tac[]
QED

