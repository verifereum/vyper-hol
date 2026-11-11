(* Actual cursor boundary for dynamic input preparation; no new definitions. *)
Theory bodyPtrHashBuiltinsShaEndpoint
Ancestors bodyPtrHashBuiltinsShaPrefix bodyPtrHashBuiltinsGhostFrame
  ghostPcTransportPtr exprSimProps ptrDiscipline venomState venomInst
  bodyPtrHashBuiltinsGhostCompose
  words arithmetic finite_map pred_set compileEnv exprLoweringProps freshWrites bodyPtrDefs

Theorem hash_bytes_prepare_endpoint:
  !D ctx fn PG G tn s bb x sa len_op sl data_op sm b base cap n d cenv cx es.
  emit_op MLOAD [Var x] sa = (len_op,sl) /\
  emit_op ADD [Var x;Lit 32w] sl = (data_op,sm) /\ not_fresh_at sa x /\
  eval_operand (Var x) s = SOME (n2w b) /\
  FLOOKUP G x = SOME (base,cap) /\ base <= b /\ b+32+n <= base+cap /\
  b+32 < dimword (:256) /\ n < dimword (:256) /\ op_taint tn (Var x) = {} /\
  (!i. b <= i /\ i < b+32+n ==> i NOTIN tn.t_mem) /\
  mem_word_at b s.vs_memory = n2w n /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sm) (DROP s.vs_inst_idx bb.bb_instructions) /\
  stmt_state_rel ctx fn cenv cx es s /\ local_ptrs_reserved cenv sa /\
  ghost_inv d cenv cx es G tn s /\
  (!p k. cenv.ce_return_buf = SOME (PtrVar (Var p) k) ==> not_fresh_at sa p) /\
  (!p k. cenv.ce_return_pc = SOME (PtrVar (Var p) k) ==> not_fresh_at sa p) /\
  (n = 0 \/
   (?aid lb k. FLOOKUP s.vs_allocas aid = SOME (lb,k) /\
      aid < sa.cs_next_id /\ lb <= b+32 /\ b+32+n <= lb+k) \/
   (?name lb k. local_region cenv es.scopes s name lb k /\
      lb <= b+32 /\ b+32+n <= lb+k)) ==>
  ?t a G1 tn1 p.
  a = t with vs_inst_idx := s.vs_inst_idx+2 /\
  run_inst_seq (emitted_insts sa sm) s = OK t /\
  gas_path_ptr D 0 ctx fn PG G tn s 0 G1 tn1 (OK a) /\
  stmt_state_rel ctx fn cenv cx es a /\ ghost_inv d cenv cx es G1 tn1 a /\
  ghost_kept cenv es sa G tn s G1 tn1 /\ data_op = Var p /\
  eval_operand data_op a = SOME (n2w (b+32)) /\ eval_operand len_op a = SOME (n2w n) /\
  ptr_covers G1 tn1 p a n /\ op_taint tn1 len_op = {} /\
  (!i. b+32 <= i /\ i < b+32+n ==> i NOTIN tn1.t_mem) /\
  a.vs_memory = s.vs_memory /\ a.vs_allocas = s.vs_allocas /\
  a.vs_outcomes = s.vs_outcomes /\ ~a.vs_halted /\ 
  lookup_block a.vs_current_bb fn.fn_blocks = SOME bb /\
  a.vs_inst_idx = s.vs_inst_idx+2 /\
  (!z. not_fresh_at sa z ==> lookup_var z a = lookup_var z s) /\
  (!z. len_op = Var z \/ data_op = Var z ==> not_fresh_at sm z) /\
  local_ptrs_reserved cenv sm /\
  (!z k. cenv.ce_return_buf = SOME (PtrVar (Var z) k) ==> not_fresh_at sm z) /\
  (!z k. cenv.ce_return_pc = SOME (PtrVar (Var z) k) ==> not_fresh_at sm z) /\
  sm.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sm /\
  sm.cs_next_var = sa.cs_next_var+2 /\ sm.cs_next_id = sa.cs_next_id+2 /\
  (n = 0 \/
   (?aid lb k. FLOOKUP a.vs_allocas aid = SOME (lb,k) /\
      aid < sm.cs_next_id /\ lb <= b+32 /\ b+32+n <= lb+k) \/
   (?name lb k. local_region cenv es.scopes a name lb k /\
      lb <= b+32 /\ b+32+n <= lb+k))
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all hash_bytes_prepare_frame >>
  disch_then (qspecl_then [`D`, `PG`] strip_assume_tac) >>
  `local_ptrs_reserved cenv sm` by
    (irule local_ptrs_reserved_next_var >> qexists_tac `sa` >> simp[]) >>
  `!z k. cenv.ce_return_buf = SOME (PtrVar (Var z) k) ==> not_fresh_at sm z` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  `!z k. cenv.ce_return_pc = SOME (PtrVar (Var z) k) ==> not_fresh_at sm z` by
    (rpt strip_tac >> irule not_fresh_at_mono >> qexists_tac `sa` >> simp[]) >>
  Q.SUBGOAL_THEN
    `n = 0 \/
     (?aid lb k. FLOOKUP t.vs_allocas aid = SOME (lb,k) /\
        aid < sm.cs_next_id /\ lb <= b+32 /\ b+32+n <= lb+k) \/
     (?name lb k. local_region cenv es.scopes t name lb k /\
        lb <= b+32 /\ b+32+n <= lb+k)` assume_tac >-
    (irule hash_readonly_input_window >> qexistsl_tac [`s`, `sa`] >> simp[]) >>
  `t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
   t.vs_outcomes = s.vs_outcomes /\ t.vs_halted = s.vs_halted /\
   t.vs_current_bb = s.vs_current_bb` by
    (qpat_assum `(t with vs_vars := _) = s`
       (mp_tac o Q.AP_TERM `\v. (v.vs_memory,v.vs_allocas,v.vs_outcomes,v.vs_halted,v.vs_current_bb)`) >> simp[]) >>
  `!z. not_fresh_at sa z ==> FLOOKUP t.vs_vars z = FLOOKUP s.vs_vars z` by
    (qpat_x_assum `!z. not_fresh_at sa z ==> lookup_var z t = _` mp_tac >>
     simp[lookup_var_def]) >>
  `!z. len_op = Var z \/ p = z ==> not_fresh_at sm z` by metis_tac[] >>
  qexistsl_tac [`t`, `t with vs_inst_idx := s.vs_inst_idx+2`, `G1`, `tn1`, `p`] >>
  simp[stmt_state_rel_inst_idx, hash_ghost_inv_inst_idx, lookup_var_def] >>
  conj_tac >- metis_tac[] >>
  qpat_x_assum `n = 0 \/ (?aid lb k. FLOOKUP t.vs_allocas aid = _ /\ aid < sm.cs_next_id /\ _) \/ _` mp_tac >>
  simp[local_region_def, lookup_var_def] >>
  POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[ADD_COMM]
QED

Theorem hash_ghost_kept_then:
  ghost_kept cenv es sa G tn s G1 tn1 /\
  ghost_kept cenv es sm G1 tn1 a Gf tf /\
  local_ptrs_reserved cenv sa /\
  (!z. not_fresh_at sa z ==> not_fresh_at sm z) /\
  (!z. not_fresh_at sa z ==> lookup_var z a = lookup_var z s) /\
  (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
    FLOOKUP a.vs_allocas aid = SOME entry) /\ sa.cs_next_id <= sm.cs_next_id ==>
  ghost_kept cenv es sa G tn s Gf tf
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!name b k. local_region cenv es.scopes a name b k <=>
              local_region cenv es.scopes s name b k` by
    (simp[local_region_def] >>
     qpat_x_assum `local_ptrs_reserved cenv sa` mp_tac >>
     simp[local_ptrs_reserved_def] >> metis_tac[]) >>
  irule hash_ghost_kept_compose >>
  first_assum (irule_at (Pat `ghost_kept _ _ sa _ _ _ _ _`)) >>
  first_assum (irule_at (Pat `ghost_kept _ _ sm _ _ _ _ _`)) >> simp[]
QED
