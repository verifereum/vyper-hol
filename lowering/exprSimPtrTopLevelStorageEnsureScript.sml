(* Actual compiler allocation followed by its counted storage-copy suffix. *)
Theory exprSimPtrTopLevelStorageEnsure
Ancestors
  exprSimPtrTopLevelStorageAlloc exprSimPtrTopLevelStoragePost
  exprSimPtrTopLevelStorageFrame exprSimUnwrap loweringHalt fragExec
  ghostPcTransportPtr fragGasPathPtr exprSimStorageCopy
  compileEnv context exprLoweringProps venomInst venomState words ptrDiscipline

Theorem toplevel_storage_ensure_ptr_path:
  (loc = LocStorage \/ loc = LocTransient) /\
  compile_ensure_in_memory (Lit a) loc nb n ctor imm sa = (op,sb) /\
  fn_has_code sa sb fn /\ stmt_state_rel ctx fn cenv cx es s /\
  fn_inst_ids_distinct fn /\ local_ptrs_reserved cenv sa /\
  nb = 32*n /\ nb < dimword (:256) /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t Gf tnf p.
    op = Var p /\ gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK t) /\
    ptr_covers Gf tnf p t nb /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `compile_ensure_in_memory (Lit a) loc nb n ctor imm =
    do buf <- compile_alloc_buffer nb;
       (if n = 1 then
          do v <- emit_op (if loc = LocStorage then SLOAD else TLOAD) [Lit a];
             emit_void MSTORE [buf.buf_operand;v] od
        else do compile_word_copy_loop (Lit a) buf.buf_operand n loc LocMemory F;
                return () od);
       return buf.buf_operand od` by
    (irule ensure_storage_memory_layout >> simp[]) >>
  qpat_x_assum `compile_ensure_in_memory _ _ _ _ _ _ sa = _` mp_tac >>
  asm_rewrite_tac[] >>
  Cases_on `compile_alloc_buffer (32*n) sa` >>
  simp[comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> strip_tac >> gnvs[] >>
  drule_all (SRULE[comp_ignore_bind_def] storage_copy_suffix_extends) >> strip_tac >>
  drule compile_alloc_buffer_extends >> strip_tac >>
  drule_all fn_has_code_split >> strip_tac >>
  drule_all toplevel_alloc_buffer_ptr_run >>
  disch_then (qspecl_then [`tn`, `PG`, `G`, `D`] strip_assume_tac) >>
  qpat_x_assum `q.buf_operand = op /\ _` strip_assume_tac >> gnvs[] >>
  `n < 2**256` by (fs[dimword_def] >> decide_tac) >>
  qabbrev_tac `s1 = u with vs_inst_idx := LENGTH r.cs_current_insts` >>
  `eval_operand (Lit a) s1 = SOME a /\ op_taint tnf (Lit a) = {} /\
   lookup_var p s1 = SOME w /\ ptr_covers Gf tnf p s1 (32*n) /\
   w2n w+32*n < 2**256 /\ w2n w+32*n <= s1.vs_alloca_next /\
   ~s1.vs_halted /\ s1.vs_current_bb = r.cs_current_bb /\
   s1.vs_inst_idx = LENGTH r.cs_current_insts` by
    fs[Abbr `s1`, eval_operand_def, lookup_var_def, op_taint_def, dimword_def] >>
  `w = n2w (w2n w)` by simp[] >>
  `lookup_var p s1 = SOME (n2w (w2n w))` by metis_tac[] >>
  `32*n <= 32*n /\ (!x. Lit a = Var x ==> not_fresh_at r x)` by simp[] >>
  drule_all (REWRITE_RULE[comp_ignore_bind_def] toplevel_copy_suffix_post) >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  drule_all gas_path_ptr_then >> simp[] >> strip_tac >>
  qexistsl_tac [`t`, `Gf'`, `tnf'`] >> simp[]
QED
