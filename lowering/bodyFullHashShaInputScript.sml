(* Output allocation preserves the source-owned SHA read window. *)
Theory bodyFullHashShaInput
Ancestors
  bodyFullHashShaAlloc bodyPtrHashBuiltinsShaAllocInput
  bodyPtrHashBuiltinsInputWindow bodyPtrHashBuiltinsAllocFrame
  exprSimAlloc bodyPtrDefs ptrDiscipline venomState venomInst
  loweringHalt exprLoweringProps emitHelperProps loweringStateRelDefs
  compileEnv finite_map pred_set words arithmetic

Theorem sha_literal_alloc_input_frame_at:
  !H:(bool # bytes32 # type_value) list # num list.
  !D lo fn cenv cx es sa sm buf m s ctx d PG G tn p len w n.
  compile_alloc_buffer m sa = (buf,sm) /\ fn_has_code sa sm fn /\
  stmt_state_rel H ctx fn cenv cx es s /\ fn_inst_ids_distinct fn /\
  local_ptrs_reserved cenv sa /\ m < dimword (:256) /\
  MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w m)]
    [STRING #"%" (toString sa.cs_next_var)]) (fn_insts fn) /\
  ghost_inv_at D lo d cenv cx es G tn s /\
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
    stmt_state_rel H ctx fn cenv cx es t /\
    buf.buf_operand = Var q /\ eval_operand buf.buf_operand t = SOME v /\
    FLOOKUP t.vs_allocas sa.cs_next_id = SOME (w2n v,m) /\
    w2n v+m < dimword (:256) /\ lo <= w2n v /\ t.vs_memory = s.vs_memory /\
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
    ghost_inv_at D lo d cenv cx es G1 tn1 t /\ ghost_kept_at lo cenv es sa G tn s G1 tn1 /\
    ptr_covers G1 tn1 q t m /\
    eval_operand (Var p) t = SOME w /\ eval_operand len t = SOME n /\
    ptr_covers G1 tn1 p t (w2n n) /\ op_taint tn1 len = {} /\
    (!i. w2n w <= i /\ i < w2n w+w2n n ==> i NOTIN tn1.t_mem)
Proof
  rpt gen_tac >> strip_tac >>
  drule_all sha_literal_alloc_frame_at >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  `ghost_kept cenv es sa G tn s G1 tn1` by
    (qpat_assum `ghost_kept_at lo cenv es sa G tn s G1 tn1` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[ghost_kept_at_def, ghost_kept_def] >> metis_tac[]) >>
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

