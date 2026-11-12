Theory bodyPtrIfExpMaterializeWord
Ancestors
  bodyPtrIfExpScalarLoad fragExecPtr ptrSafeRun ptrDiscipline
  venomExecSemantics venomInst venomState finite_map pred_set
  contextCodegenRel codegenRel emitHelper compileEnv loweringStateRelDefs bodyPtrDefs memLocDefs
  exprSimPtrProps fragGasPathPtr bodyPtrIfExpBytesFrame
  robustCopyTransportPtr typedCopyPtr valueEncodingProps exprSimProps

Theorem ifexp_materialize_load_taint:
  MEM opc [SLOAD;TLOAD;DLOAD] /\ eval_operand arg s = SOME a ==>
  step_taint (mk_inst id opc [arg] [out]) s (update_var out w s) tn =
    tn with t_var := tn.t_var |+ (out,
      if opc = SLOAD then key_taint tn.t_stor a
      else if opc = TLOAD then key_taint tn.t_trans a else {})
Proof
  strip_tac >>
  `new_site_bytes s (update_var out w s) = {}` by
    simp[new_site_bytes_def, update_var_def, FLOOKUP_DEF,
         pred_setTheory.EXTENSION, SF CONJ_ss] >>
  gvs[] >>
  simp[step_taint_def, set_var_taint_def, mk_inst_def, out_taint_def,
       mem_taint_def, step_writes_def, source_memory_write_ranges_def,
       written_taint_def, store_taint_def, adopt_reset_def, imm_taint_def,
       range_bytes_def, taint_component_equality, DRESTRICT_UNIV]
QED

Theorem ifexp_materialize_mstore_check:
  ptr_covers G tn p s 32 /\ ~ctx_has_dalloca ctx ==>
  ptr_inst_ok D 0 fuel ctx fn G tn
    (mk_inst id MSTORE [Var p; v] []) s
Proof
  strip_tac >> gvs[ptr_covers_def] >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
       mk_inst_def, source_memory_write_ranges_def,
       source_memory_read_ranges_def, fixed_source_write_range_def,
       eval_operand_def] >>
  conj_tac >-
    (Cases_on `eval_operand v s` >> simp[] >>
     rpt strip_tac >> gvs[] >> simp[mem_write_ops_def] >> metis_tac[]) >>
  conj_tac >- (rpt strip_tac >> gvs[]) >>
  simp[step_inst_non_invoke] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  pure_rewrite_tac[instruction_accessors, instruction_accfupds, opcode_case_def] >>
  simp[exec_write2_def, eval_operand_def, AllCaseEqs(), mstore_def] >>
  rpt strip_tac >> gvs[]
QED

Theorem ifexp_materialize_load_covers:
  MEM opc [SLOAD;TLOAD;DLOAD] /\ eval_operand arg s = SOME a /\
  out <> dst /\ ptr_covers G tn dst s n ==>
  ptr_covers
    (step_prov PG G (mk_inst id opc [arg] [out]) (update_var out w s))
    (step_taint (mk_inst id opc [arg] [out]) s (update_var out w s) tn)
    dst (update_var out w s) n
Proof
  strip_tac >> drule_all ifexp_materialize_load_taint >> strip_tac >>
  gvs[ptr_covers_def, step_prov_def, set_prov_def, out_prov_def,
      op_taint_def, mk_inst_def, update_var_def, lookup_var_def,
      FLOOKUP_DRESTRICT, FLOOKUP_UPDATE]
QED

Theorem ifexp_materialize_mstore_taint:
  eval_operand addr s = SOME a /\ eval_operand value s = SOME w ==>
  (step_taint (mk_inst id MSTORE [addr;value] []) s
    (mstore (w2n a) w s) tn).t_mem =
    (tn.t_mem DIFF {i | w2n a <= i /\ i < w2n a + 32}) UNION
      {w2n a + k | k IN op_taint tn value}
Proof
  strip_tac >>
  simp[step_taint_def, mk_inst_def, mem_taint_def, new_site_bytes_def,
       mstore_def, write_memory_with_expansion_def, FLOOKUP_DEF,
       step_writes_def, source_memory_write_ranges_def,
       fixed_source_write_range_def, eval_operand_def, written_taint_def,
       range_bytes_def, pred_setTheory.EXTENSION] >>
  metis_tac[]
QED

Theorem ifexp_materialize_word_path:
  MEM opc [SLOAD;TLOAD;DLOAD] /\ ~ctx_has_dalloca ctx /\
  eval_operand arg s = SOME a /\ op_taint tn arg = {} /\
  out <> dst /\ ptr_covers G tn dst s 32 /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx = SOME (mk_inst id opc [arg] [out]) /\
  get_instruction bb (SUC s.vs_inst_idx) =
    SOME (mk_inst sid MSTORE [Var dst;Var out] []) /\
  step_inst_base (mk_inst id opc [arg] [out]) s = OK (update_var out w s) /\
  s1 = (update_var out w s with vs_inst_idx := SUC s.vs_inst_idx) /\
  G1 = step_prov PG G (mk_inst id opc [arg] [out]) (update_var out w s) /\
  tn1 = step_taint (mk_inst id opc [arg] [out]) s (update_var out w s) tn /\
  eval_operand (Var dst) s1 = SOME p /\
  u = mstore (w2n p) w s1 /\
  G2 = step_prov PG G1 (mk_inst sid MSTORE [Var dst;Var out] []) u /\
  tn2 = step_taint (mk_inst sid MSTORE [Var dst;Var out] []) s1 u tn1 ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0 G2 tn2
    (OK (u with vs_inst_idx := SUC s1.vs_inst_idx))
Proof
  strip_tac >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 G1 tn1 (OK s1)` by
    (gvs[] >> irule gas_path_ptr_one_step >>
     simp[mk_inst_def, update_var_def] >>
     gvs[is_terminator_def] >> simp[GSYM mk_inst_def] >>
     irule ifexp_scalar_load_check >> simp[] >> metis_tac[]) >>
  `ptr_covers G1 tn1 dst s1 32` by
    (gvs[] >> irule ifexp_materialize_load_covers >> simp[] >> metis_tac[]) >>
  `eval_operand (Var out) s1 = SOME w` by
    simp[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  `step_inst_base (mk_inst sid MSTORE [Var dst;Var out] []) s1 = OK u` by
    (gvs[] >> pure_once_rewrite_tac[step_inst_base_def] >>
     pure_rewrite_tac[instruction_accessors, instruction_accfupds, opcode_case_def,
                      mk_inst_def, combinTheory.K_THM] >>
     simp[exec_write2_def] >>
     qpat_assum `eval_operand (Var dst) s1 = _` mp_tac >>
     qpat_assum `eval_operand (Var out) s1 = _` mp_tac >> simp[]) >>
  `ptr_inst_ok D 0 0 ctx fn G1 tn1
     (mk_inst sid MSTORE [Var dst;Var out] []) s1` by
    (irule ifexp_materialize_mstore_check >> simp[]) >>
  `gas_path_ptr D 0 ctx fn PG G1 tn1 s1 0 G2 tn2
     (OK (u with vs_inst_idx := SUC s1.vs_inst_idx))` by
    (qpat_x_assum `G2 = _` SUBST1_TAC >>
     qpat_x_assum `tn2 = _` SUBST1_TAC >>
     irule gas_path_ptr_one_step >>
     simp[mk_inst_def, is_terminator_def, update_var_def, mstore_def,
          write_memory_with_expansion_def]) >>
  drule_all gas_path_ptr_then >> simp[]
QED

Theorem ifexp_materialize_mstore_ghost:
  step_prov PG G (mk_inst id MSTORE [addr;value] []) (mstore off w s) = G /\
  (step_taint (mk_inst id MSTORE [addr;value] []) s (mstore off w s) tn).t_var = tn.t_var /\
  (step_taint (mk_inst id MSTORE [addr;value] []) s (mstore off w s) tn).t_stor = tn.t_stor /\
  (step_taint (mk_inst id MSTORE [addr;value] []) s (mstore off w s) tn).t_trans = tn.t_trans /\
  (step_taint (mk_inst id MSTORE [addr;value] []) s (mstore off w s) tn).t_imm = tn.t_imm
Proof
  simp[step_prov_def, set_prov_def, step_taint_def, mk_inst_def,
       set_var_taint_def, DRESTRICT_UNIV, store_taint_def, adopt_reset_def,
       imm_taint_def]
QED

Theorem ifexp_materialize_load_old:
  MEM opc [SLOAD;TLOAD;DLOAD] /\ eval_operand arg s = SOME a /\ x <> out ==>
  FLOOKUP (step_prov PG G (mk_inst id opc [arg] [out]) (update_var out w s)) x =
    FLOOKUP G x /\
  op_taint (step_taint (mk_inst id opc [arg] [out]) s (update_var out w s) tn)
    (Var x) = op_taint tn (Var x) /\
  lookup_var x (mstore off w' (update_var out w s)) = lookup_var x s
Proof
  strip_tac >> drule_all ifexp_materialize_load_taint >> strip_tac >>
  simp[step_prov_def, set_prov_def, mk_inst_def, FLOOKUP_UPDATE,
       FLOOKUP_DRESTRICT, op_taint_def, lookup_var_def, mstore_def,
       update_var_def, write_memory_with_expansion_def] >>
  Cases_on `out_prov PG G (mk_inst id opc [arg] [out]) (update_var out w s)` >>
  gvs[mk_inst_def, update_var_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT]
QED

Theorem ifexp_materialize_store_mem_frame:
  eval_operand addr s = SOME a /\ eval_operand value s = SOME w /\
  ~(w2n a <= i /\ i < w2n a + 32) /\
  op_taint tn value SUBSET count 32 ==>
  (i IN (step_taint (mk_inst id MSTORE [addr;value] []) s
           (mstore (w2n a) w s) tn).t_mem <=> i IN tn.t_mem)
Proof
  strip_tac >> simp[ifexp_materialize_mstore_taint] >>
  gvs[pred_setTheory.SUBSET_DEF] >>
  eq_tac >> strip_tac >> gvs[] >> res_tac >> decide_tac
QED

Theorem ifexp_materialize_store_kept:
  ghost_kept ce es sa G0 tn0 s0 G tn /\
  eval_operand addr s = SOME a /\ eval_operand value s = SOME w /\
  op_taint tn value SUBSET count 32 /\
  (!aid off sz. FLOOKUP s0.vs_allocas aid = SOME (off,sz) /\ aid < sa.cs_next_id /\
    (!name p len. local_region ce es.scopes s0 name p len ==>
      off+sz <= p \/ p+len <= off) ==>
    off+sz <= w2n a \/ w2n a+32 <= off) /\
  (!name p len. local_region ce es.scopes s0 name p len ==>
    p+len <= w2n a \/ w2n a+32 <= p) ==>
  ghost_kept ce es sa G0 tn0 s0
    (step_prov PG G (mk_inst id MSTORE [addr;value] []) (mstore (w2n a) w s))
    (step_taint (mk_inst id MSTORE [addr;value] []) s (mstore (w2n a) w s) tn)
Proof
  strip_tac >>
  irule (Q.INST [`b` |-> `w2n (a:bytes32)`, `n` |-> `32`] bytes_writer_ghost_kept) >>
  qexistsl_tac [`G`,`a`,`tn`] >> simp[ifexp_materialize_mstore_ghost] >>
  conj_tac >- simp[op_taint_def, ifexp_materialize_mstore_ghost] >>
  conj_tac >- metis_tac[arithmeticTheory.ADD_COMM] >>
  conj_tac >- metis_tac[arithmeticTheory.ADD_COMM] >>
  rpt strip_tac >> irule ifexp_materialize_store_mem_frame >> metis_tac[]
QED

Theorem ifexp_materialize_store_robust_frame:
  eval_operand addr s = SOME a /\ eval_operand value s = SOME w /\
  op_taint tn value SUBSET count 32 /\ val_wf tv v /\
  (p + type_memory_size tv <= w2n a \/ w2n a + 32 <= p) /\
  (!m. mem_agree_outside tn.t_mem s.vs_memory m ==> val_in_memory tv v p m) ==>
  !m. mem_agree_outside
    (step_taint (mk_inst id MSTORE [addr;value] []) s (mstore (w2n a) w s) tn).t_mem
    (mstore (w2n a) w s).vs_memory m ==> val_in_memory tv v p m
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  rpt gen_tac >> disch_tac >>
  qmatch_asmsub_abbrev_tac `mem_agree_outside tf mf m` >>
  irule robust_val_in_memory_exterior_frame >> conj_tac >- simp[] >>
  qexists_tac `s.vs_memory` >> qexists_tac `mf` >>
  qexists_tac `tn.t_mem` >> qexists_tac `tf` >>
  qexists_tac `{i | w2n a <= i /\ i < w2n a + 32}` >> simp[] >>
  conj_tac >-
    (simp[Abbr `tf`] >> rpt strip_tac >>
     irule ifexp_materialize_store_mem_frame >> metis_tac[]) >>
  conj_tac >-
    (simp[Abbr `mf`] >> rpt strip_tac >>
     irule mstore_mem_bytes_at_disjoint >> decide_tac) >>
  rpt strip_tac >> drule val_footprint_le >> decide_tac
QED

Theorem ifexp_materialize_store_inv:
  ghost_inv d ce cx es G tn s /\ local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  eval_operand addr s = SOME a /\ eval_operand value s = SOME w /\
  op_taint tn value SUBSET count 32 /\
  (!name entry p sz v. lookup_scopes name es.scopes = SOME entry /\
    FLOOKUP ce.ce_vars name = SOME (PtrVar (Var p) sz) /\ lookup_var p s = SOME v ==>
    val_wf entry.type entry.value /\
    (w2n v + type_memory_size entry.type <= w2n a \/ w2n a+32 <= w2n v)) ==>
  ghost_inv d ce cx es
    (step_prov PG G (mk_inst id MSTORE [addr;value] []) (mstore (w2n a) w s))
    (step_taint (mk_inst id MSTORE [addr;value] []) s (mstore (w2n a) w s) tn)
    (mstore (w2n a) w s)
Proof
  strip_tac >>
  irule (Q.INST [`sc` |-> `sa`, `b` |-> `w2n (a:bytes32)`, `n` |-> `32`]
    bytes_writer_ghost_inv) >>
  conj_tac >-
    (simp[stor_taint_ok_def, ifexp_materialize_mstore_ghost, mstore_def,
          write_memory_with_expansion_def] >> gvs[ghost_inv_def, stor_taint_ok_def]) >>
  qexistsl_tac [`G`,`a`,`s`,`sa`,`tn`] >> simp[] >>
  conj_tac >- metis_tac[arithmeticTheory.ADD_COMM] >>
  conj_tac >- (gvs[local_ptrs_reserved_def] >> metis_tac[]) >>
  conj_tac >- simp[ifexp_materialize_mstore_ghost, op_taint_def] >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  rpt gen_tac >> disch_tac >>
  irule ifexp_materialize_store_robust_frame >> metis_tac[]
QED

Theorem ifexp_materialize_load_kept:
  MEM opc [SLOAD;TLOAD;DLOAD] /\ eval_operand arg s = SOME a /\
  (!x. not_fresh_at sa x ==> x <> out) /\
  ghost_kept ce es sa G0 tn0 s0 G tn ==>
  ghost_kept ce es sa G0 tn0 s0
    (step_prov PG G (mk_inst id opc [arg] [out]) (update_var out w s))
    (step_taint (mk_inst id opc [arg] [out]) s (update_var out w s) tn)
Proof
  strip_tac >> rewrite_tac[ghost_kept_def] >>
  conj_tac >-
    (rpt strip_tac >> `x <> out` by metis_tac[] >>
     drule_all ifexp_materialize_load_old >>
     strip_tac >> gvs[ghost_kept_def] >> metis_tac[]) >>
  drule_all ifexp_materialize_load_taint >> strip_tac >>
  simp[] >> gvs[ghost_kept_def] >> metis_tac[]
QED

Theorem ifexp_materialize_load_inv:
  MEM opc [SLOAD;TLOAD;DLOAD] /\ eval_operand arg s = SOME a /\
  (!x. not_fresh_at sa x ==> x <> out) /\
  ghost_inv d ce cx es G tn s /\ local_ptrs_reserved ce sa /\
  (!x sz. ce.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) /\
  (!x sz. ce.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sa x) ==>
  ghost_inv d ce cx es
    (step_prov PG G (mk_inst id opc [arg] [out]) (update_var out w s))
    (step_taint (mk_inst id opc [arg] [out]) s (update_var out w s) tn)
    (update_var out w s)
Proof
  strip_tac >> irule ghost_inv_fresh_frame >>
  qexistsl_tac [`G`,`es`,`s`,`sa`,`tn`] >>
  drule_all ifexp_materialize_load_taint >> strip_tac >>
  asm_rewrite_tac[] >> simp[update_var_def] >>
  rpt strip_tac >> `x <> out` by metis_tac[] >>
  drule_all ifexp_materialize_load_old >> strip_tac >>
  gvs[lookup_var_def, update_var_def, FLOOKUP_UPDATE, op_taint_def]
QED
