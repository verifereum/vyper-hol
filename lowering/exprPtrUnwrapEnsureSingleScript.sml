(* Assemble allocation and the checked singleton on the same endpoint. *)
Theory exprPtrUnwrapEnsureSingle
Ancestors
  exprPtrUnwrapLoopEntry exprPtrUnwrapEnsureShape exprPtrUnwrapSingleExecution
  exprSimStorageCopy exprSimAlloc exprPtrUnwrapAllocSeparation
  createMemoryInterface bodyPtrDefs compileEnv context fragGasPathPtr
  venomState venomInst words arithmetic copyExecution slotCopyExecution
  ptrSafeRun ptrDiscipline ASCIInumbers exprPtrUnwrapRuntimeFrame
  exprPtrUnwrapFrames valueEncodingProps venomMemProps finite_map

Theorem unwrap_single_layout[local]:
  (loc = LocStorage \/ loc = LocTransient) /\
  compile_ensure_in_memory src loc nb 1 ctor imm sa = (op,sb) /\
  fn_has_code sa sb func ==>
  ?buf sm.
    compile_alloc_buffer nb sa = (buf,sm) /\ op = buf.buf_operand /\
    fn_has_code sa sm func /\ fn_has_code sm sb func /\
    same_blocks sm sb /\ isPREFIX sm.cs_current_insts sb.cs_current_insts /\
    emitted_insts sm sb =
      [mk_inst sm.cs_next_id (if loc=LocStorage then SLOAD else TLOAD) [src]
         [STRING #"%" (toString sm.cs_next_var)];
       mk_inst (sm.cs_next_id+1) MSTORE
         [buf.buf_operand; Var (STRING #"%" (toString sm.cs_next_var))] []] /\
    (!x. not_fresh_at sm x ==> x <> STRING #"%" (toString sm.cs_next_var))
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  drule_all ensure_slot_memory_single_code >> strip_tac >>
  drule_all ensure_slot_memory_split >> simp[] >> strip_tac >>
  drule storage_copy_word_layout >> strip_tac >>
  metis_tac[]
QED

Theorem unwrap_single_endpoint_frame[local]:
  t = (mstore (w2n d) w (update_var (STRING #"%" (toString sm.cs_next_var)) w a)
        with vs_inst_idx := idx) ==>
  slot_copy_runtime_frame sm d 1 a t /\ mem_word_at (w2n d) t.vs_memory = w
Proof
  strip_tac >> reverse conj_tac
  >- simp[mstore_mem_word_at_same] >>
  `copy_static t = copy_static a` by
    simp[copy_static_def, mstore_def, write_memory_with_expansion_def, update_var_def] >>
  drule copy_static_fields >> strip_tac >>
  simp[slot_copy_runtime_frame_def] >> conj_tac
  >- (rpt strip_tac >> Cases_on `op` >>
      simp[eval_operand_def, lookup_var_def, mstore_def,
        write_memory_with_expansion_def, update_var_def, FLOOKUP_UPDATE] >>
      qpat_x_assum `slot_copy_external _ _` mp_tac >>
      simp[slot_copy_external_def, slot_copy_var_def] >>
      disch_then (qspec_then `0` mp_tac) >> simp[] >> metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >>
      `a'+1 <= w2n d \/ w2n d+32 <= a'` by decide_tac >>
      simp[mstore_mem_bytes_at_disjoint, update_var_def]) >>
  conj_tac >- simp[LENGTH_mstore_eq, update_var_def] >>
  rpt strip_tac >> simp[mstore_mem_bytes_at_disjoint, update_var_def]
QED

Theorem unwrap_slot_load_choice[local]:
  !loc. (if loc=LocStorage then SLOAD else TLOAD) = SLOAD \/
        (if loc=LocStorage then SLOAD else TLOAD) = TLOAD
Proof
  gen_tac >> Cases_on `loc=LocStorage` >> simp[]
QED

Theorem unwrap_single_taint_outside[local]:
  tf.t_mem = (tn.t_mem DIFF {j | w2n d <= j /\ j < w2n d+32}) UNION
    {w2n d+k | k IN key_taint keys p} ==>
  !j. j < w2n d \/ w2n d+32 <= j ==> (j IN tf.t_mem <=> j IN tn.t_mem)
Proof
  strip_tac >> rpt strip_tac >>
  `~(w2n d <= j /\ j < w2n d+32)` by decide_tac >>
  `~(?k. j = w2n d+k /\ k IN key_taint keys p)` by
    (strip_tac >> fs[key_taint_def] >> decide_tac) >>
  simp[pred_setTheory.IN_UNION, pred_setTheory.IN_DIFF, pred_setTheory.GSPECIFICATION] >>
  metis_tac[ADD_COMM]
QED

Theorem unwrap_ensure_slot_single:
  (loc = LocStorage \/ loc = LocTransient) /\
  compile_ensure_in_memory src loc nb 1 ctor imm sa = (op,sb) /\
  fn_has_code sa sb func /\ stmt_state_rel ctx func cenv cx es s /\
  nb < dimword (:256) /\ 32 <= nb /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!x. src = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME p /\ op_taint tn src = {} ==>
  ?root d a G0 tn0 Gf tnf t sm buf u.
    fn_has_code sa sm func /\ fn_has_code sm sb func /\
    u = update_var root d (buffer_allocation_fields s sa.cs_next_id nb) /\
    step_inst_base (mk_inst sa.cs_next_id ALLOCA [Lit (n2w nb)] [root]) s = OK u /\
    a = u with vs_inst_idx := SUC s.vs_inst_idx /\
    G0 = step_prov PG G (mk_inst sa.cs_next_id ALLOCA [Lit (n2w nb)] [root]) u /\
    tn0 = step_taint (mk_inst sa.cs_next_id ALLOCA [Lit (n2w nb)] [root]) s u tn /\
    op = Var root /\ (d:bytes32) = n2w (buffer_allocation_base s sa.cs_next_id) /\
    compile_alloc_buffer nb sa = (buf,sm) /\ buf.buf_operand = Var root /\
    gas_path_ptr D 0 ctx func PG G tn s 0 G0 tn0 (OK a) /\
    gas_path_ptr D 0 ctx func PG G0 tn0 a 0 Gf tnf (OK t) /\
    gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (OK t) /\
    t.vs_current_bb = sb.cs_current_bb /\ t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    ptr_covers Gf tnf root t nb /\
    t = (mstore (w2n d) (slot_copy_word (if loc=LocStorage then SLOAD else TLOAD) a p)
      (update_var (STRING #"%" (toString sm.cs_next_var))
        (slot_copy_word (if loc=LocStorage then SLOAD else TLOAD) a p) a)
          with vs_inst_idx := LENGTH sb.cs_current_insts) /\
    tnf.t_mem = (tn0.t_mem DIFF {j | w2n d <= j /\ j < w2n d+32}) UNION
      {w2n d+k | k IN key_taint (if loc=LocStorage then tn.t_stor else tn.t_trans) p} /\
    (!b. b < 32 /\ w2n d+b IN tnf.t_mem ==>
      b IN key_taint (if loc=LocStorage then tn.t_stor else tn.t_trans) p) /\
    (!j. j < w2n d \/ w2n d+32 <= j ==> (j IN tnf.t_mem <=> j IN tn0.t_mem)) /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!x. x <> STRING #"%" (toString sm.cs_next_var) ==>
       FLOOKUP Gf x = FLOOKUP G0 x /\ op_taint tnf (Var x) = op_taint tn0 (Var x)) /\
    (!x k. x <> STRING #"%" (toString sm.cs_next_var) /\ ptr_covers G0 tn0 x a k ==>
       ptr_covers Gf tnf x t k) /\
    (!x k. slot_copy_external sm (Var x) ==>
      (ptr_covers Gf tnf x t k <=> ptr_covers G0 tn0 x a k)) /\
    slot_copy_runtime_frame sm d 1 a t /\
    mem_word_at (w2n d) t.vs_memory =
      slot_copy_word (if loc=LocStorage then SLOAD else TLOAD) s p /\
    lookup_var root a = SOME d /\
    a.vs_memory = s.vs_memory /\ a.vs_accounts = s.vs_accounts /\
    a.vs_transient = s.vs_transient /\ a.vs_call_ctx = s.vs_call_ctx /\
    a.vs_immutables = s.vs_immutables /\
    tn0.t_stor = tn.t_stor /\ tn0.t_trans = tn.t_trans /\ tn0.t_imm = tn.t_imm
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  drule_all unwrap_single_layout >> strip_tac >>
  `32*1 <= nb` by simp[] >>
  drule_all unwrap_alloc_loop_entry >>
  disch_then (qspecl_then [`PG`, `G`, `D`] strip_assume_tac) >>
  `root <> STRING #"%" (toString sm.cs_next_var)` by
    (qpat_x_assum `slot_copy_external sm (Var root)` mp_tac >>
     simp[slot_copy_external_def, slot_copy_var_def] >>
     disch_then (qspec_then `0` mp_tac) >> simp[]) >>
  `allocas_from 0 a /\ (ctx_has_dalloca ctx ==> allocas_below_fmp a)` by
    simp[allocas_from_def] >>
  `ptr_covers G0 tn0 root a 32` by fs[] >>
  qpat_assum `buf.buf_operand = Var root` (fn th =>
    qpat_x_assum `emitted_insts sm sb = _` (assume_tac o REWRITE_RULE [th])) >>
  qspec_then `loc` assume_tac unwrap_slot_load_choice >>
  drule_all unwrap_single_slot_execution >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (OK t)` by
    metis_tac[gas_path_ptr_then, ADD_0] >>
  drule unwrap_single_endpoint_frame >> strip_tac >>
  `!x k. slot_copy_external sm (Var x) ==>
    (ptr_covers Gf tnf x t k <=> ptr_covers G0 tn0 x a k)` by
    (rpt strip_tac >>
     `x <> STRING #"%" (toString sm.cs_next_var)` by
       (qpat_x_assum `slot_copy_external _ _` mp_tac >>
        simp[slot_copy_external_def, slot_copy_var_def] >>
        disch_then (qspec_then `0` mp_tac) >> simp[]) >>
     irule copy_ptr_covers_transport >>
     simp[lookup_var_def, mstore_def, write_memory_with_expansion_def,
          update_var_def, FLOOKUP_UPDATE]) >>
  `slot_copy_word (if loc=LocStorage then SLOAD else TLOAD) a p =
    slot_copy_word (if loc=LocStorage then SLOAD else TLOAD) s p` by
    simp[slot_copy_word_def, sload_def, tload_def, contract_storage_def,
      contract_transient_def] >>
  drule unwrap_single_taint_outside >> strip_tac >>
  qexistsl [`root`, `d`, `a`, `G0`, `tn0`, `Gf`, `tnf`, `t`, `sm`, `buf`, `u`] >>
  `ptr_covers Gf tnf root t nb` by metis_tac[] >>
  simp[] >> Cases_on `loc=LocStorage` >> gvs[] >>
  rpt strip_tac >> gvs[pred_setTheory.IN_UNION, pred_setTheory.IN_DIFF,
    pred_setTheory.GSPECIFICATION]
QED
