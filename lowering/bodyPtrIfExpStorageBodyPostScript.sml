Theory bodyPtrIfExpStorageBodyPost
Ancestors
  bodyPtrIfExpStorageBody bodyPtrIfExpCopyPrefix
  bodyPtrIfExpMaterializeFrame slotCopyExecution copyExecution
  venomState ptrDiscipline finite_map words
  robustCopyTransportPtr typedCopyPtr valueEncodingProps exprSimProps
  bodyPtrIfExpBytesFrame bodyPtrDefs compileEnv loweringStateRelDefs
  fragGasPathPtr gasCount ptrSafeRun venomExecProofs venomExecSemantics fragExec
  venomInst emitHelper contextCodegenRel codegenRel

Theorem ifexp_copy_body_path:
  MEM load [SLOAD;TLOAD] /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (TAKE 7 (slot_copy_body_insts cs src dst load))
    (DROP s.vs_inst_idx bb.bb_instructions) /\
  slot_copy_external cs src /\ slot_copy_external cs dst /\
  eval_operand src s = SOME p /\ eval_operand dst s = SOME d /\
  eval_operand (Var (slot_copy_var cs 0)) s = SOME (n2w i) /\
  op_taint tn src = {} /\ op_taint tn dst = {} /\
  op_taint tn (Var (slot_copy_var cs 0)) = {} /\
  op_prov G (Var (slot_copy_var cs 0)) = NONE /\
  op_prov G dst = SOME (b,n) /\
  b <= w2n (d+n2w i*32w) /\ w2n (d+n2w i*32w)+32 <= b+n ==>
  ?t G' tn'.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    t.vs_inst_idx = s.vs_inst_idx+7 /\
    jump_to (slot_copy_cond cs) t = slot_copy_body_result cs p d load i s /\
    lookup_var (slot_copy_var cs 0) t = SOME (n2w (i+1)) /\
    op_prov G' (Var (slot_copy_var cs 0)) = NONE /\
    op_taint tn' (Var (slot_copy_var cs 0)) = {} /\
    tn'.t_mem = (tn.t_mem DIFF
      {j | w2n (d+n2w i*32w) <= j /\ j < w2n (d+n2w i*32w)+32}) UNION
      {w2n (d+n2w i*32w) + k | k | k IN
        (if load = SLOAD then key_taint tn.t_stor (p+n2w i)
         else key_taint tn.t_trans (p+n2w i))} /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. (!k. k < 7 ==> x <> slot_copy_var cs k) ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  `?t G' tn'.
    run_inst_seq (TAKE 7 (slot_copy_body_insts cs src dst load)) s = OK t /\
    inst_seq_ptr D 0 ctx fn PG G tn
      (TAKE 7 (slot_copy_body_insts cs src dst load)) s G' tn' /\
    lookup_var (slot_copy_var cs 0) t = SOME (n2w i+1w) /\
    op_prov G' (Var (slot_copy_var cs 0)) = NONE /\
    op_taint tn' (Var (slot_copy_var cs 0)) = {} /\
    tn'.t_mem = (tn.t_mem DIFF
      {j | w2n (d+n2w i*32w) <= j /\ j < w2n (d+n2w i*32w)+32}) UNION
      {w2n (d+n2w i*32w) + k | k | k IN
        (if load = SLOAD then key_taint tn.t_stor (p+n2w i)
         else key_taint tn.t_trans (p+n2w i))} /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. (!k. k < 7 ==> x <> slot_copy_var cs k) ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x))` by
    (irule ifexp_copy_body_seven >> simp[]) >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn'
     (OK (t with vs_inst_idx := s.vs_inst_idx+7))` by
    (irule ifexp_copy_body_counted >> simp[] >>
     qexistsl_tac [`cs`, `dst`, `load`, `src`] >> gvs[]) >>
  `?r. run_inst_seq (TAKE 7 (slot_copy_body_insts cs src dst load)) s = OK r /\
    jump_to (slot_copy_cond cs) r = slot_copy_body_result cs p d load i s` by
    (irule ifexp_copy_body_runtime >> simp[] >>
     gvs[eval_operand_def]) >>
  gvs[] >> qexistsl_tac [`r with vs_inst_idx := s.vs_inst_idx+7`, `G'`, `tn'`] >>
  simp[lookup_var_def, jump_to_def, GSYM word_add_n2w] >>
  gvs[lookup_var_def, jump_to_def]
QED

Theorem ifexp_copy_body_runtime_frame:
  jump_to (slot_copy_cond cs) t = slot_copy_body_result cs p d load i s ==>
  t.vs_memory = (mstore (w2n (d+n2w i*32w))
    (slot_copy_word load s (p+n2w i)) s).vs_memory /\
  t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
  t.vs_call_ctx = s.vs_call_ctx /\ t.vs_allocas = s.vs_allocas /\
  t.vs_halted = s.vs_halted /\
  (!op. slot_copy_external cs op ==> eval_operand op t = eval_operand op s)
Proof
  strip_tac >>
  `t.vs_memory = (slot_copy_body_result cs p d load i s).vs_memory /\
   t.vs_accounts = (slot_copy_body_result cs p d load i s).vs_accounts /\
   t.vs_transient = (slot_copy_body_result cs p d load i s).vs_transient /\
   t.vs_call_ctx = (slot_copy_body_result cs p d load i s).vs_call_ctx /\
   t.vs_allocas = (slot_copy_body_result cs p d load i s).vs_allocas /\
   t.vs_halted = (slot_copy_body_result cs p d load i s).vs_halted` by
    (qpat_assum `jump_to _ _ = _` (fn th => pure_rewrite_tac [GSYM th]) >>
     simp[NoAsms, jump_to_def]) >>
  simp[slot_copy_body_memory, slot_copy_body_sources] >>
  conj_tac >- simp[slot_copy_body_result_def, update_var_def, mstore_def, jump_to_def] >>
  rpt strip_tac >>
  `eval_operand op t = eval_operand op (jump_to (slot_copy_cond cs) t)` by
    (Cases_on `op` >> simp[NoAsms, eval_operand_def, lookup_var_def, jump_to_def]) >>
  pop_assum (fn th => pure_once_rewrite_tac [th]) >>
  asm_rewrite_tac [] >> irule slot_copy_body_operand >> simp[]
QED

Theorem ifexp_copy_body_word_prefix:
  jump_to (slot_copy_cond cs) t = slot_copy_body_result cs p d load i s /\
  w2n (d+n2w i*32w) = pos+32*i /\
  (!j. j < i ==> mem_word_at (pos+32*j) s.vs_memory =
    slot_copy_word load s (p+n2w j)) ==>
  !j. j < SUC i ==> mem_word_at (pos+32*j) t.vs_memory =
    slot_copy_word load s (p+n2w j)
Proof
  strip_tac >> drule ifexp_copy_body_runtime_frame >> strip_tac >>
  pure_asm_rewrite_tac [] >>
  ho_match_mp_tac ifexp_copy_word_prefix_store >> simp[]
QED

Theorem ifexp_copy_body_taint_prefix:
  w2n (d+n2w i*32w) = pos+32*i /\
  tn'.t_mem = (tn.t_mem DIFF
    {j | w2n (d+n2w i*32w) <= j /\ j < w2n (d+n2w i*32w)+32}) UNION
    {w2n (d+n2w i*32w)+k | k | k IN
      (if load = SLOAD then key_taint tn.t_stor (p+n2w i)
       else key_taint tn.t_trans (p+n2w i))} /\
  (!j k. j < i /\ k < 32 /\ pos+32*j+k IN tn.t_mem ==> (j,k) IN X) /\
  (!k. k IN (if load = SLOAD then key_taint tn.t_stor (p+n2w i)
             else key_taint tn.t_trans (p+n2w i)) ==> (i,k) IN X) ==>
  !j k. j < SUC i /\ k < 32 /\ pos+32*j+k IN tn'.t_mem ==> (j,k) IN X
Proof
  strip_tac >> ho_match_mp_tac ifexp_copy_taint_prefix_store >>
  qexists_tac `tn.t_mem` >>
  qexists_tac `if load = SLOAD then key_taint tn.t_stor (p+n2w i)
              else key_taint tn.t_trans (p+n2w i)` >> simp[]
QED

Theorem ifexp_copy_body_taint_exterior:
  tn'.t_mem = (tn.t_mem DIFF {j | a <= j /\ j < a+32}) UNION
    {a+k | k | k IN (if load = SLOAD then key_taint tn.t_stor key
                     else key_taint tn.t_trans key)} ==>
  !j. ~(a <= j /\ j < a+32) ==> (j IN tn'.t_mem <=> j IN tn.t_mem)
Proof
  simp[key_taint_def, pred_setTheory.EXTENSION, pred_setTheory.IN_DIFF,
       pred_setTheory.IN_UNION, pred_setTheory.GSPECIFICATION] >>
  rpt strip_tac >> IF_CASES_TAC >> gvs[] >> eq_tac >> rpt strip_tac >> gvs[] >>
  decide_tac
QED

Theorem ifexp_copy_body_robust_frame:
  t.vs_memory = (mstore (w2n (d+n2w i*32w))
    (slot_copy_word load s (p+n2w i)) s).vs_memory /\
  tn'.t_mem = (tn.t_mem DIFF
    {j | w2n (d+n2w i*32w) <= j /\ j < w2n (d+n2w i*32w)+32}) UNION
    {w2n (d+n2w i*32w)+k | k | k IN
      (if load = SLOAD then key_taint tn.t_stor (p+n2w i)
       else key_taint tn.t_trans (p+n2w i))} /\
  val_wf ft fv /\
  (pos+type_memory_size ft <= w2n (d+n2w i*32w) \/
   w2n (d+n2w i*32w)+32 <= pos) /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==> val_in_memory ft fv pos m) ==>
  !m. mem_agree_outside tn'.t_mem t.vs_memory m ==> val_in_memory ft fv pos m
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  rpt gen_tac >> disch_tac >>
  irule robust_val_in_memory_exterior_frame >> conj_tac >- simp[] >>
  qexistsl_tac [`s.vs_memory`, `t.vs_memory`, `tn.t_mem`, `tn'.t_mem`,
    `{j | w2n (d+n2w i*32w) <= j /\ j < w2n (d+n2w i*32w)+32}`] >>
  simp[IgnAsm `tn'.t_mem = _`] >>
  conj_tac >-
    (rpt strip_tac >> irule ifexp_copy_body_taint_exterior >> metis_tac[]) >>
  conj_tac >-
    (rpt strip_tac >> irule mstore_mem_bytes_at_disjoint >> decide_tac) >>
  rpt strip_tac >> drule val_footprint_le >> decide_tac
QED

Theorem ifexp_copy_body_ghost_kept:
  ghost_kept ce es sa G0 tn0 s0 G tn /\
  (!x. not_fresh_at sa x ==> !k. k < 7 ==> x <> slot_copy_var cs k) /\
  (!x. (!k. k < 7 ==> x <> slot_copy_var cs k) ==>
    FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
  tn'.t_mem = (tn.t_mem DIFF {j | a <= j /\ j < a+32}) UNION
    {a+k | k | k IN (if load = SLOAD then key_taint tn.t_stor key
                     else key_taint tn.t_trans key)} /\
  (!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
    (!name p len. local_region ce es.scopes s0 name p len ==>
      off+sz <= p \/ p+len <= off) ==> off+sz <= a \/ a+32 <= off) /\
  (!name p len. local_region ce es.scopes s0 name p len ==>
    p+len <= a \/ a+32 <= p) ==>
  ghost_kept ce es sa G0 tn0 s0 G' tn'
Proof
  strip_tac >>
  irule (Q.INST [`b` |-> `a:num`, `n` |-> `32`] bytes_writer_ghost_kept) >>
  qexistsl_tac [`G`, `a`, `tn`] >> simp[IgnAsm `tn'.t_mem = _`] >>
  conj_tac >- metis_tac[arithmeticTheory.ADD_COMM] >>
  conj_tac >- metis_tac[arithmeticTheory.ADD_COMM] >>
  rpt strip_tac >> irule ifexp_copy_body_taint_exterior >> metis_tac[]
QED

Theorem ifexp_copy_body_ghost_inv:
  ghost_inv rty ce cx es G tn s /\ local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x. not_fresh_at sa x ==> !k. k < 7 ==> x <> slot_copy_var cs k) /\
  (!x. (!k. k < 7 ==> x <> slot_copy_var cs k) ==>
    lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
    op_taint tn' (Var x) = op_taint tn (Var x)) /\
  t.vs_memory = (mstore (w2n (d+n2w i*32w))
    (slot_copy_word load s (p+n2w i)) s).vs_memory /\
  t.vs_accounts = s.vs_accounts /\ t.vs_transient = s.vs_transient /\
  t.vs_call_ctx = s.vs_call_ctx /\
  tn'.t_mem = (tn.t_mem DIFF
    {j | w2n (d+n2w i*32w) <= j /\ j < w2n (d+n2w i*32w)+32}) UNION
    {w2n (d+n2w i*32w)+k | k | k IN
      (if load = SLOAD then key_taint tn.t_stor (p+n2w i)
       else key_taint tn.t_trans (p+n2w i))} /\
  tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
  (!name entry v sz w. lookup_scopes name es.scopes = SOME entry /\
    FLOOKUP ce.ce_vars name = SOME (PtrVar (Var v) sz) /\ lookup_var v s = SOME w ==>
    val_wf entry.type entry.value /\
    (w2n w+type_memory_size entry.type <= w2n (d+n2w i*32w) \/
     w2n (d+n2w i*32w)+32 <= w2n w)) ==>
  ghost_inv rty ce cx es G' tn' t
Proof
  strip_tac >>
  irule (Q.INST [`n` |-> `32`] bytes_writer_ghost_inv) >>
  conj_tac >-
    (irule bytes_writer_stor_taint_ok >> qexistsl_tac [`s`, `tn`] >>
     gvs[ghost_inv_def]) >>
  qexistsl_tac [`G`, `w2n (d+n2w i*32w)`, `s`, `sa`, `tn`] >>
  simp[IgnAsm `tn'.t_mem = _`] >>
  conj_tac >- metis_tac[arithmeticTheory.ADD_COMM] >>
  conj_tac >- (gvs[local_ptrs_reserved_def] >> metis_tac[]) >>
  rpt strip_tac >> irule ifexp_copy_body_robust_frame >> metis_tac[]
QED

Theorem ifexp_copy_body_prejump_block:
  jump_to (slot_copy_cond cs) t = slot_copy_body_result cs p d load i s ==>
  t.vs_current_bb = s.vs_current_bb
Proof
  simp[jump_to_def, slot_copy_body_result_def, update_var_def, mstore_def,
       venom_state_component_equality] >> rpt strip_tac >> gvs[]
QED

(* The copy-body consumer has a fetched JMP rather than emit_jump compiler states. *)
Theorem ifexp_copy_body_jump_path:
  ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx =
    SOME (mk_inst (cs.cs_next_id+11) JMP [Label (slot_copy_cond cs)] []) ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0 G tn (OK (jump_to (slot_copy_cond cs) s))
Proof
  strip_tac >>
  `ptr_safe_step D 0 0 ctx fn PG G tn
    (mk_inst (cs.cs_next_id+11) JMP [Label (slot_copy_cond cs)] []) s` by
    (simp[ptr_safe_step_def, ptr_inst_ok_def, access_ok_def, taint_ok_def,
          allocas_from_def, mk_inst_def, source_memory_write_ranges_def,
          source_memory_read_ranges_def, op_taint_def] >>
     simp[GSYM mk_inst_def, step_inst_non_invoke] >>
     simp[mk_inst_def, step_jmp_behavior, jump_to_def]) >>
  `gas_path_ptr_edge D 0 ctx fn PG G tn s 0 G tn
    (OK (jump_to (slot_copy_cond cs) s))` by
    (rewrite_tac[gas_path_ptr_edge_def] >> simp[] >>
     qexists_tac `0:num` >>
     simp[step_inst_non_invoke, mk_inst_def, gas_count_step_def,
          step_jmp_behavior, is_terminator_def] >>
     fs[mk_inst_def] >> metis_tac[]) >>
  `~(jump_to (slot_copy_cond cs) s).vs_halted` by simp[jump_to_def] >>
  metis_tac[gas_path_ptr_rules, arithmeticTheory.ADD_CLAUSES]
QED

Theorem ifexp_copy_body_finish_path:
  gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
  ~ctx_has_dalloca ctx /\ t.vs_inst_idx = s.vs_inst_idx+7 /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb (s.vs_inst_idx+7) =
    SOME (mk_inst (cs.cs_next_id+11) JMP [Label (slot_copy_cond cs)] []) /\
  jump_to (slot_copy_cond cs) t = slot_copy_body_result cs p d load i s ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn'
    (OK (slot_copy_body_result cs p d load i s))
Proof
  strip_tac >>
  `~t.vs_halted` by metis_tac[fragGasSeqPtrTheory.gas_path_ptr_ok_not_halted] >>
  `t.vs_current_bb = s.vs_current_bb` by
    (irule ifexp_copy_body_prejump_block >> metis_tac[]) >>
  `gas_path_ptr D 0 ctx fn PG G' tn' t 0 G' tn'
    (OK (jump_to (slot_copy_cond cs) t))` by
    (irule ifexp_copy_body_jump_path >> simp[] >> metis_tac[]) >>
  metis_tac[gas_path_ptr_then, arithmeticTheory.ADD_CLAUSES]
QED

Theorem ifexp_copy_body_transition:
  MEM load [SLOAD;TLOAD] /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (TAKE 7 (slot_copy_body_insts cs src dst load))
    (DROP s.vs_inst_idx bb.bb_instructions) /\
  get_instruction bb (s.vs_inst_idx+7) =
    SOME (mk_inst (cs.cs_next_id+11) JMP [Label (slot_copy_cond cs)] []) /\
  slot_copy_external cs src /\ slot_copy_external cs dst /\
  eval_operand src s = SOME p /\ eval_operand dst s = SOME d /\
  eval_operand (Var (slot_copy_var cs 0)) s = SOME (n2w i) /\
  op_taint tn src = {} /\ op_taint tn dst = {} /\
  op_taint tn (Var (slot_copy_var cs 0)) = {} /\
  op_prov G (Var (slot_copy_var cs 0)) = NONE /\
  op_prov G dst = SOME (b,n) /\
  b <= w2n (d+n2w i*32w) /\ w2n (d+n2w i*32w)+32 <= b+n ==>
  ?G' tn'.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn'
      (OK (slot_copy_body_result cs p d load i s)) /\
    op_prov G' (Var (slot_copy_var cs 0)) = NONE /\
    op_taint tn' (Var (slot_copy_var cs 0)) = {} /\
    tn'.t_mem = (tn.t_mem DIFF
      {j | w2n (d+n2w i*32w) <= j /\ j < w2n (d+n2w i*32w)+32}) UNION
      {w2n (d+n2w i*32w) + k | k | k IN
        (if load = SLOAD then key_taint tn.t_stor (p+n2w i)
         else key_taint tn.t_trans (p+n2w i))} /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. (!k. k < 7 ==> x <> slot_copy_var cs k) ==>
      lookup_var x (slot_copy_body_result cs p d load i s) = lookup_var x s /\
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  `?t G' tn'.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn' (OK t) /\
    t.vs_inst_idx = s.vs_inst_idx+7 /\
    jump_to (slot_copy_cond cs) t = slot_copy_body_result cs p d load i s /\
    lookup_var (slot_copy_var cs 0) t = SOME (n2w (i+1)) /\
    op_prov G' (Var (slot_copy_var cs 0)) = NONE /\
    op_taint tn' (Var (slot_copy_var cs 0)) = {} /\
    tn'.t_mem = (tn.t_mem DIFF
      {j | w2n (d+n2w i*32w) <= j /\ j < w2n (d+n2w i*32w)+32}) UNION
      {w2n (d+n2w i*32w) + k | k | k IN
        (if load = SLOAD then key_taint tn.t_stor (p+n2w i)
         else key_taint tn.t_trans (p+n2w i))} /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. (!k. k < 7 ==> x <> slot_copy_var cs k) ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x))` by
    (irule ifexp_copy_body_path >> simp[] >> metis_tac[]) >>
  qexistsl_tac [`G'`, `tn'`] >>
  reverse conj_tac >-
    (simp[] >> gen_tac >> strip_tac >>
     qpat_assum `!x. (!k. _ ==> _) ==> _` (qspec_then `x` mp_tac) >>
     (impl_tac >- simp[]) >> strip_tac >>
     qpat_assum `jump_to _ _ = _` (fn th => pure_rewrite_tac [GSYM th]) >>
     simp[NoAsms, lookup_var_def, jump_to_def] >> gvs[lookup_var_def]) >>
  irule ifexp_copy_body_finish_path >> metis_tac[]
QED

Theorem ifexp_copy_body_external_ghost:
  slot_copy_external cs op /\
  (!x. (!k. k < 7 ==> x <> slot_copy_var cs k) ==>
    FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) ==>
  op_prov G' op = op_prov G op /\ op_taint tn' op = op_taint tn op
Proof
  Cases_on `op` >> simp[op_prov_def, op_taint_def, slot_copy_external_def]
QED

Theorem ifexp_copy_body_destination_coverage:
  slot_copy_external cs (Var dst) /\
  ptr_covers G tn dst s capacity /\
  (!x. (!k. k < 7 ==> x <> slot_copy_var cs k) ==>
    lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
    op_taint tn' (Var x) = op_taint tn (Var x)) ==>
  ptr_covers G' tn' dst t capacity
Proof
  strip_tac >>
  `lookup_var dst t = lookup_var dst s /\ FLOOKUP G' dst = FLOOKUP G dst /\
   op_taint tn' (Var dst) = op_taint tn (Var dst)` by
    (qpat_x_assum `!x. _ ==> _` irule >> gvs[slot_copy_external_def]) >>
  gvs[ptr_covers_def, op_taint_def]
QED
