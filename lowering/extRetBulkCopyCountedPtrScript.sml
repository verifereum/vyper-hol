Theory extRetBulkCopyCountedPtr
Ancestors
  extRetBytesCopyCountedPtr fragGasPathPtr context compileEnv emitHelper
  venomState venomInst venomExecSemantics ptrDiscipline bodyPtrDefs
  words arithmetic finite_map ptrSafeRun fragExecPtr typedCopyPtr emitHelper
  venomInst venomInstProofs codegenRel contextCodegenRel wordLoadStorePtr

(* A static zero-sized copy emits no instruction, unlike a dynamic MCOPY
   whose evaluated size happens to be zero. *)
Theorem compile_copy_memory_counted_ptr:
  compile_copy_memory (Var dst) (Var src) n sa = ((),sb) /\
  fn_has_code sa sb fn /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ n < dimword(:256) /\
  (0 < n ==> lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
    ptr_covers G tn src s n /\ ptr_covers G tn dst s n) ==>
  ?tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    sf.vs_allocas = s.vs_allocas /\ sf.vs_alloca_next = s.vs_alloca_next /\
    sf.vs_fmp = s.vs_fmp /\
    sf.vs_memory = (if n = 0 then s.vs_memory else
      (mcopy (w2n b) (w2n a) n s).vs_memory) /\
    tnf.t_mem = (if n = 0 then tn.t_mem else
      (tn.t_mem DIFF {i | w2n b <= i /\ i < w2n b + n}) UNION
      {w2n b + i | i < n /\ w2n a + i IN tn.t_mem}) /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!p. lookup_var p sf = lookup_var p s /\
         op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  Cases_on `n` >-
    (simp[compile_copy_memory_def, comp_return_def] >> strip_tac >> gvs[] >>
     qexistsl_tac [`tn`, `s`] >> simp[] >>
     irule (cj 1 gas_path_ptr_rules) >> simp[]) >>
  rename1 `compile_copy_memory _ _ (SUC n) _ = _` >>
  simp[compile_copy_memory_def] >> strip_tac >>
  `eval_operand (Lit (n2w (SUC n))) s = SOME (n2w (SUC n)) /\
   op_taint tn (Lit (n2w (SUC n))) = {} /\
   ptr_covers G tn src s (w2n (n2w (SUC n) : bytes32)) /\
   ptr_covers G tn dst s (w2n (n2w (SUC n) : bytes32))` by
    simp[eval_operand_def, op_taint_def, wordsTheory.w2n_n2w, LESS_MOD] >>
  drule_all emit_mcopy_counted_ptr >>
  disch_then (qspecl_then [`PG`, `D`] mp_tac) >>
  simp[wordsTheory.w2n_n2w, LESS_MOD]
QED

Theorem compile_copy_memory_dynamic_counted_ptr:
  compile_copy_memory_dynamic (Var dst) (Var src) count_op sa = ((),sb) /\
  fn_has_code sa sb fn /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  eval_operand count_op s = SOME n /\ op_taint tn count_op = {} /\
  ptr_covers G tn src s (w2n n) /\ ptr_covers G tn dst s (w2n n) ==>
  ?tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    sf.vs_allocas = s.vs_allocas /\ sf.vs_alloca_next = s.vs_alloca_next /\
    sf.vs_fmp = s.vs_fmp /\
    sf.vs_memory = (mcopy (w2n b) (w2n a) (w2n n) s).vs_memory /\
    tnf.t_mem = (tn.t_mem DIFF {i | w2n b <= i /\ i < w2n b + w2n n}) UNION
      {w2n b + i | i < w2n n /\ w2n a + i IN tn.t_mem} /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!p. lookup_var p sf = lookup_var p s /\
         op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  simp[compile_copy_memory_dynamic_def] >>
  strip_tac >> drule_all emit_mcopy_counted_ptr >>
  disch_then (qspecl_then [`PG`, `D`] mp_tac) >> simp[]
QED

Theorem compile_copy_sarray_bulk_counted_ptr:
  type_memory_bytes cenv dst_ty = type_memory_bytes cenv src_ty /\
  ~is_abi_dynamic cenv.ce_struct_fields dst_ty /\
  n = cnt * type_memory_bytes cenv dst_ty /\
  compile_copy_sarray_typed cenv (Var dst) dst_ty (Var src) src_ty cnt sa = ((),sb) /\
  fn_has_code sa sb fn /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ n < dimword(:256) /\
  (0 < n ==> lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
    ptr_covers G tn src s n /\ ptr_covers G tn dst s n) ==>
  ?tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    sf.vs_allocas = s.vs_allocas /\ sf.vs_alloca_next = s.vs_alloca_next /\
    sf.vs_fmp = s.vs_fmp /\
    sf.vs_memory = (if n = 0 then s.vs_memory else
      (mcopy (w2n b) (w2n a) n s).vs_memory) /\
    tnf.t_mem = (if n = 0 then tn.t_mem else
      (tn.t_mem DIFF {i | w2n b <= i /\ i < w2n b + n}) UNION
      {w2n b + i | i < n /\ w2n a + i IN tn.t_mem}) /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!p. lookup_var p sf = lookup_var p s /\
         op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  `compile_copy_memory (Var dst) (Var src) n sa = ((),sb)` by
    (qpat_x_assum `compile_copy_sarray_typed _ _ _ _ _ _ _ = _` mp_tac >>
     simp[Once compile_store_memory_typed_def]) >>
  drule_all compile_copy_memory_counted_ptr >>
  disch_then (qspecl_then [`PG`, `D`] mp_tac) >> simp[]
QED

(* Even a zero-length MCOPY evaluates all its operands, but it does not
   require either address to carry provenance. *)
Theorem ptr_inst_ok_mcopy_empty_operand:
  eval_operand count_op s = SOME 0w /\ op_taint tn count_op = {} /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  op_taint tn (Var src) = {} /\ op_taint tn (Var dst) = {} /\
  ~ctx_has_dalloca ctx ==>
  ptr_inst_ok D 0 fuel ctx fn G tn
    (mk_inst id MCOPY [Var dst;Var src;count_op] []) s
Proof
  strip_tac >>
  `step_inst fuel ctx (mk_inst id MCOPY [Var dst;Var src;count_op] []) s =
     OK (mcopy (w2n b) (w2n a) 0 s)` by
    (simp[step_inst_non_invoke] >> pure_once_rewrite_tac[step_inst_base_def] >>
     simp[mk_inst_def, eval_operand_def]) >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
       mk_inst_def, source_memory_write_ranges_def,
       source_memory_read_ranges_def, fixed_source_write_range_def,
       sized_source_write_range_def, eval_operand_def,
       mcopy_def, write_memory_with_expansion_def] >>
  gen_tac >> Cases_on `op = Var dst` >> gvs[] >>
  Cases_on `op = Var src` >> gvs[] >>
  Cases_on `op = count_op` >> gvs[op_taint_def]
QED

Theorem compile_copy_memory_dynamic_empty_counted_ptr:
  compile_copy_memory_dynamic (Var dst) (Var src) count_op sa = ((),sb) /\
  fn_has_code sa sb fn /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  eval_operand count_op s = SOME 0w /\ op_taint tn count_op = {} /\
  op_taint tn (Var src) = {} /\ op_taint tn (Var dst) = {} ==>
  ?tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    sf.vs_memory = (mcopy (w2n b) (w2n a) 0 s).vs_memory /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!p. lookup_var p sf = lookup_var p s /\
         op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++
     [mk_inst sa.cs_next_id MCOPY [Var dst;Var src;count_op] []]` by
    gvs[compile_copy_memory_dynamic_def, emit_void_def, comp_bind_def,
        comp_ignore_bind_def, fresh_id_def, emit_def, comp_return_def] >>
  qabbrev_tac `inst = mk_inst sa.cs_next_id MCOPY [Var dst;Var src;count_op] []` >>
  qabbrev_tac `t = mcopy (w2n b) (w2n a) 0 s` >>
  qabbrev_tac `tnf = step_taint inst s t tn` >>
  `step_prov PG G inst t = G /\ tnf.t_var = tn.t_var /\
   tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_mem = tn.t_mem` by
    (qunabbrev_tac `tnf` >> qunabbrev_tac `inst` >> qunabbrev_tac `t` >>
     simp[step_prov_def, set_prov_def, out_prov_def, step_taint_def,
          mk_inst_def, set_var_taint_def, DRESTRICT_UNIV,
          store_taint_def, adopt_reset_def, mem_taint_def, step_writes_def,
          source_memory_write_ranges_def, fixed_source_write_range_def,
          sized_source_write_range_def, written_taint_def, range_bytes_def,
          new_site_bytes_def, mcopy_def, write_memory_with_expansion_def,
          eval_operand_def, FLOOKUP_DEF, pred_setTheory.EXTENSION] >> metis_tac[]) >>
  qexistsl_tac [`tnf`, `t with vs_inst_idx := SUC s.vs_inst_idx`] >>
  conj_tac >-
    (`gas_path_ptr D 0 ctx fn PG G tn s 0 (step_prov PG G inst t) tnf
       (OK (t with vs_inst_idx := SUC s.vs_inst_idx))` suffices_by simp[] >>
     qunabbrev_tac `tnf` >> irule emitted_step_counted_ptr >>
     simp[Abbr `inst`, mk_inst_def, is_terminator_def] >>
     conj_tac >-
       (pure_once_rewrite_tac[step_inst_base_def] >>
        simp[Abbr `t`, mk_inst_def, eval_operand_def]) >>
     conj_tac >- (qexistsl_tac [`sa`, `sb`] >> simp[mk_inst_def]) >>
     irule (SRULE [mk_inst_def] ptr_inst_ok_mcopy_empty_operand) >> simp[]) >>
  simp[Abbr `t`, mcopy_def, write_memory_with_expansion_def,
       lookup_var_def, op_taint_def]
QED

(* Clean size arithmetic and capacity comparisons do not touch memory. *)
Theorem ptr_inst_ok_bulk_binop[local]:
  (opc = MUL \/ (opc = GT /\ ?k. right = Lit k)) /\
  op_taint tn left = {} /\ op_taint tn right = {} /\
  ~ctx_has_dalloca ctx ==>
  ptr_inst_ok D 0 fuel ctx fn G tn
    (mk_inst id opc [left;right] [out]) s
Proof
  strip_tac >> gvs[] >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
       mk_inst_def, source_memory_write_ranges_def,
       source_memory_read_ranges_def] >>
  conj_tac >- metis_tac[] >>
  simp[step_inst_non_invoke] >>
  pure_once_rewrite_tac[step_inst_base_def] >>
  pure_rewrite_tac[instruction_accessors, instruction_accfupds,
                   combinTheory.K_THM, opcode_case_def] >>
  simp[exec_pure2_def, AllCaseEqs(), update_var_def] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem bulk_binop_prov_frame[local]:
  (opc = MUL \/ opc = GT) /\ p <> out ==>
  FLOOKUP (step_prov PG G (mk_inst id opc [left;right] [out])
    (update_var out w s)) p = FLOOKUP G p
Proof
  strip_tac >> simp[step_prov_def, set_prov_def, mk_inst_def] >>
  BasicProvers.EVERY_CASE_TAC >> simp[FLOOKUP_DRESTRICT, FLOOKUP_UPDATE]
QED

Theorem bulk_binop_ghost_frame[local]:
  (opc = MUL \/ opc = GT) /\ op_taint tn left = {} /\ op_taint tn right = {} ==>
  op_taint (step_taint (mk_inst id opc [left;right] [out]) s
    (update_var out w s) tn) (Var out) = {} /\
  (step_taint (mk_inst id opc [left;right] [out]) s
    (update_var out w s) tn).t_mem = tn.t_mem /\
  (step_taint (mk_inst id opc [left;right] [out]) s
    (update_var out w s) tn).t_stor = tn.t_stor /\
  (step_taint (mk_inst id opc [left;right] [out]) s
    (update_var out w s) tn).t_trans = tn.t_trans /\
  (!p. p <> out ==>
    FLOOKUP (step_prov PG G (mk_inst id opc [left;right] [out])
      (update_var out w s)) p = FLOOKUP G p /\
    op_taint (step_taint (mk_inst id opc [left;right] [out]) s
      (update_var out w s) tn) (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  `new_site_bytes s (update_var out w s) = {}` by
    simp[new_site_bytes_def, update_var_def, FLOOKUP_DEF,
         pred_setTheory.EXTENSION, SF CONJ_ss] >>
  gvs[] >> Cases_on `eval_operand left s` >>
  qpat_x_assum `op_taint tn left = _` (assume_tac o SRULE [op_taint_def]) >>
  qpat_x_assum `op_taint tn right = _` (assume_tac o SRULE [op_taint_def]) >>
  simp[step_prov_def, set_prov_def, out_prov_def, step_taint_def,
       mk_inst_def, set_var_taint_def, out_taint_def, op_taint_def,
       store_taint_def, adopt_reset_def, mem_taint_def, step_writes_def,
       source_memory_write_ranges_def, written_taint_def, range_bytes_def,
       FLOOKUP_DRESTRICT, FLOOKUP_UPDATE]
QED

Theorem emit_bulk_binop_counted_ptr:
  (opc = MUL /\ f = word_mul \/
   opc = GT /\ (?k. right = Lit k) /\
   f = (\a b. bool_to_word (w2n a > w2n b))) /\
  emit_op opc [left;right] sa = (Var out,sb) /\
  fn_has_code sa sb fn /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\
  eval_operand left s = SOME a /\ eval_operand right s = SOME b /\
  op_taint tn left = {} /\ op_taint tn right = {} ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    lookup_var out sf = SOME (f a b) /\ op_taint tnf (Var out) = {} /\
    sf.vs_allocas = s.vs_allocas /\ sf.vs_alloca_next = s.vs_alloca_next /\
    sf.vs_fmp = s.vs_fmp /\
    sf.vs_memory = s.vs_memory /\ tnf.t_mem = tn.t_mem /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!p. not_fresh_at sa p ==>
      lookup_var p sf = lookup_var p s /\
      FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++
     [mk_inst sa.cs_next_id opc [left;right] [out]] /\
   (!p. not_fresh_at sa p ==> p <> out)` by
    (gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
         fresh_id_def, emit_def, comp_return_def, not_fresh_at_def] >>
     metis_tac[LESS_EQ_REFL]) >>
  `opc <> GAS /\ opc <> INVOKE /\ ~is_terminator opc` by
    gvs[is_terminator_def] >>
  qabbrev_tac `t = update_var out (f a b) s` >>
  qabbrev_tac `Gf = step_prov PG G
    (mk_inst sa.cs_next_id opc [left;right] [out]) t` >>
  qabbrev_tac `tnf = step_taint
    (mk_inst sa.cs_next_id opc [left;right] [out]) s t tn` >>
  qexistsl_tac [`Gf`, `tnf`, `t with vs_inst_idx := SUC s.vs_inst_idx`] >>
  conj_tac >-
    (qunabbrev_tac `Gf` >> qunabbrev_tac `tnf` >>
     irule emitted_step_counted_ptr >>
     simp[mk_inst_def, is_terminator_def] >>
     conj_tac >-
       (gvs[] >> pure_once_rewrite_tac[step_inst_base_def] >>
        simp[mk_inst_def, exec_pure2_def, Abbr `t`]) >>
     conj_tac >- (qexistsl_tac [`sa`, `sb`] >> simp[mk_inst_def]) >>
     irule (SRULE [mk_inst_def] ptr_inst_ok_bulk_binop) >> metis_tac[]) >>
  gvs[] >> simp[Abbr `t`, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  simp[Abbr `tnf`, Abbr `Gf`,
       bulk_binop_ghost_frame |> SPEC_ALL |> Q.INST [`opc` |-> `MUL`] |> SRULE [],
       bulk_binop_ghost_frame |> SPEC_ALL |> Q.INST [`opc` |-> `GT`] |> SRULE []] >>
  rpt strip_tac >> `p <> out` by metis_tac[] >>
  simp[bulk_binop_prov_frame, bulk_binop_ghost_frame, lookup_var_def,
       update_var_def, FLOOKUP_UPDATE]
QED

Theorem emit_iszero_counted_ptr:
  emit_op ISZERO [arg] sa = (Var out,sb) /\ fn_has_code sa sb fn /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ eval_operand arg s = SOME a /\
  op_taint tn arg = {} ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    lookup_var out sf = SOME (bool_to_word (a = 0w)) /\
    op_taint tnf (Var out) = {} /\
    sf.vs_allocas = s.vs_allocas /\ sf.vs_alloca_next = s.vs_alloca_next /\
    sf.vs_fmp = s.vs_fmp /\
    sf.vs_memory = s.vs_memory /\ tnf.t_mem = tn.t_mem /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!p. not_fresh_at sa p ==>
      lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++
     [mk_inst sa.cs_next_id ISZERO [arg] [out]] /\
   (!p. not_fresh_at sa p ==> p <> out)` by
    (gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
         fresh_id_def, emit_def, comp_return_def, not_fresh_at_def] >>
     metis_tac[LESS_EQ_REFL]) >>
  qabbrev_tac `t = update_var out (bool_to_word (a = 0w)) s` >>
  qabbrev_tac `inst = mk_inst sa.cs_next_id ISZERO [arg] [out]` >>
  qabbrev_tac `Gf = step_prov PG G inst t` >>
  qabbrev_tac `tnf = step_taint inst s t tn` >>
  qexistsl_tac [`Gf`, `tnf`, `t with vs_inst_idx := SUC s.vs_inst_idx`] >>
  conj_tac >-
    (qunabbrev_tac `Gf` >> qunabbrev_tac `tnf` >>
     irule emitted_step_counted_ptr >> simp[Abbr `inst`, mk_inst_def, is_terminator_def] >>
     conj_tac >-
       (pure_once_rewrite_tac[step_inst_base_def] >>
        simp[mk_inst_def, exec_pure1_def, Abbr `t`]) >>
     conj_tac >- (qexistsl_tac [`sa`, `sb`] >> simp[mk_inst_def]) >>
     simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
          source_memory_write_ranges_def, source_memory_read_ranges_def] >>
     simp[step_inst_non_invoke] >> pure_once_rewrite_tac[step_inst_base_def] >>
     simp[exec_pure1_def, update_var_def]) >>
  `new_site_bytes s t = {}` by
    simp[Abbr `t`, new_site_bytes_def, update_var_def, FLOOKUP_DEF,
         pred_setTheory.EXTENSION, SF CONJ_ss] >>
  simp[Abbr `t`, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  simp[Abbr `tnf`, Abbr `Gf`, Abbr `inst`, step_prov_def, set_prov_def,
       out_prov_def, step_taint_def, set_var_taint_def, out_taint_def,
       op_taint_def, store_taint_def, adopt_reset_def, mem_taint_def,
       step_writes_def, source_memory_write_ranges_def, written_taint_def,
       range_bytes_def, mk_inst_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE] >>
  rpt strip_tac >> `p <> out` by metis_tac[] >> simp[]
QED

Theorem emit_assert_success_counted_ptr:
  emit_void ASSERT [arg] sa = ((),sb) /\ fn_has_code sa sb fn /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ eval_operand arg s = SOME a /\ a <> 0w /\
  op_taint tn arg = {} ==>
  gas_path_ptr D 0 ctx fn PG G tn s 0 G tn
    (OK (s with vs_inst_idx := SUC s.vs_inst_idx)) /\
  sb.cs_current_bb = sa.cs_current_bb /\
  LENGTH sb.cs_current_insts = SUC (LENGTH sa.cs_current_insts)
Proof
  strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++
     [mk_inst sa.cs_next_id ASSERT [arg] []]` by
    gvs[emit_void_def, comp_bind_def, comp_ignore_bind_def,
        fresh_id_def, emit_def, comp_return_def] >>
  simp[] >>
  qabbrev_tac `inst = mk_inst sa.cs_next_id ASSERT [arg] []` >>
  `step_prov PG G inst s = G /\ step_taint inst s s tn = tn` by
    (simp[Abbr `inst`, step_prov_def, set_prov_def, out_prov_def,
          step_taint_def, set_var_taint_def, mk_inst_def, DRESTRICT_UNIV,
          store_taint_def, adopt_reset_def, mem_taint_def, step_writes_def,
          source_memory_write_ranges_def, written_taint_def, range_bytes_def,
          new_site_bytes_def, pred_setTheory.EXTENSION, FLOOKUP_DEF,
          SF CONJ_ss] >>
     Cases_on `tn` >> simp[imm_taint_def, taint_component_equality]) >>
  `gas_path_ptr D 0 ctx fn PG G tn s 0 (step_prov PG G inst s)
     (step_taint inst s s tn) (OK (s with vs_inst_idx := SUC s.vs_inst_idx))`
    suffices_by simp[] >>
  irule emitted_step_counted_ptr >>
  simp[Abbr `inst`, mk_inst_def, is_terminator_def] >>
  conj_tac >-
    (pure_once_rewrite_tac[step_inst_base_def] >> simp[mk_inst_def]) >>
  conj_tac >- (qexistsl_tac [`sa`, `sb`] >> simp[mk_inst_def]) >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
       source_memory_write_ranges_def, source_memory_read_ranges_def,
       step_inst_non_invoke] >>
  pure_once_rewrite_tac[step_inst_base_def] >> simp[]
QED

Theorem emit_mstore_clean_ambient_counted_ptr:
  emit_void MSTORE [Var dst;value] sa = ((),sb) /\ fn_has_code sa sb fn /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ ptr_covers G tn dst s 32 /\
  lookup_var dst s = SOME a /\ eval_operand value s = SOME w /\
  op_taint tn value = {} ==>
  ?tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    sf.vs_allocas = s.vs_allocas /\ sf.vs_alloca_next = s.vs_alloca_next /\
    sf.vs_fmp = s.vs_fmp /\
    sf.vs_memory = (mstore (w2n a) w s).vs_memory /\
    tnf.t_mem = tn.t_mem DIFF {i | w2n a <= i /\ i < w2n a + 32} /\
    tnf.t_imm = tn.t_imm /\ sf.vs_accounts = s.vs_accounts /\
    sf.vs_transient = s.vs_transient /\ sf.vs_call_ctx = s.vs_call_ctx /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!p. lookup_var p sf = lookup_var p s /\
         op_taint tnf (Var p) = op_taint tn (Var p)) /\
    sf.vs_labels = s.vs_labels
Proof
  strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++
     [mk_inst sa.cs_next_id MSTORE [Var dst;value] []]` by
    gvs[emit_void_def, comp_bind_def, comp_ignore_bind_def,
        fresh_id_def, emit_def, comp_return_def] >>
  qabbrev_tac `t = mstore (w2n a) w s` >>
  qabbrev_tac `inst = mk_inst sa.cs_next_id MSTORE [Var dst;value] []` >>
  qabbrev_tac `tnf = step_taint inst s t tn` >>
  `step_prov PG G inst t = G /\ tnf.t_var = tn.t_var /\
   tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
   tnf.t_mem = tn.t_mem DIFF {i | w2n a <= i /\ i < w2n a + 32}` by
    (simp[Abbr `inst`, Abbr `t`, Abbr `tnf`] >>
     irule mstore_ghost_frame >> simp[]) >>
  qexistsl_tac [`tnf`, `t with vs_inst_idx := SUC s.vs_inst_idx`] >>
  conj_tac >-
    (`gas_path_ptr D 0 ctx fn PG G tn s 0 (step_prov PG G inst t) tnf
       (OK (t with vs_inst_idx := SUC s.vs_inst_idx))` suffices_by simp[] >>
     qunabbrev_tac `tnf` >> irule emitted_step_counted_ptr >>
     simp[Abbr `inst`, mk_inst_def, is_terminator_def] >>
     conj_tac >-
       (pure_once_rewrite_tac[step_inst_base_def] >>
        simp[mk_inst_def, exec_write2_def, eval_operand_def, Abbr `t`]) >>
     conj_tac >- (qexistsl_tac [`sa`, `sb`] >> simp[mk_inst_def]) >>
     irule (SRULE [mk_inst_def] ptr_inst_ok_mstore) >> simp[]) >>
  simp[Abbr `t`, mstore_def, write_memory_with_expansion_def,
       Abbr `tnf`, Abbr `inst`, step_taint_def, imm_taint_def, mk_inst_def,
       lookup_var_def, op_taint_def]
QED

(* Original interface, retained for consumers not needing ambient fields. *)
Theorem emit_mstore_clean_counted_ptr:
  emit_void MSTORE [Var dst;value] sa = ((),sb) /\ fn_has_code sa sb fn /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ ptr_covers G tn dst s 32 /\
  lookup_var dst s = SOME a /\ eval_operand value s = SOME w /\
  op_taint tn value = {} ==>
  ?tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    sf.vs_allocas = s.vs_allocas /\ sf.vs_alloca_next = s.vs_alloca_next /\
    sf.vs_fmp = s.vs_fmp /\
    sf.vs_memory = (mstore (w2n a) w s).vs_memory /\
    tnf.t_mem = tn.t_mem DIFF {i | w2n a <= i /\ i < w2n a + 32} /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!p. lookup_var p sf = lookup_var p s /\
         op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >> drule_all emit_mstore_clean_ambient_counted_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`tnf`, `sf`] >> simp[]
QED

(* The compiler's capacity check is a successful three-instruction path.
   Neither provenance for the length nor cleanliness of array padding is
   needed: the comparison is against a literal, and the header is clean. *)
Theorem emit_bulk_capacity_check_counted_ptr:
  emit_op GT [len_op;Lit (n2w capacity)] sa = (Var gt,sb) /\
  emit_op ISZERO [Var gt] sb = (Var ok,sc) /\
  emit_void ASSERT [Var ok] sc = ((),sd) /\
  fn_has_code sa sb fn /\ fn_has_code sb sc fn /\ fn_has_code sc sd fn /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ eval_operand len_op s = SOME (n2w len) /\
  op_taint tn len_op = {} /\ len <= capacity /\ capacity < dimword(:256) ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sd.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sd.cs_current_insts /\ ~sf.vs_halted /\
    sf.vs_allocas = s.vs_allocas /\ sf.vs_alloca_next = s.vs_alloca_next /\
    sf.vs_fmp = s.vs_fmp /\
    sf.vs_memory = s.vs_memory /\ tnf.t_mem = tn.t_mem /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!p. not_fresh_at sa p ==>
      lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  `!p. not_fresh_at sa p ==> not_fresh_at sb p` by
    (gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
         fresh_id_def, emit_def, comp_return_def, not_fresh_at_def] >>
     rpt strip_tac >> gvs[] >> metis_tac[LESS_EQ_TRANS]) >>
  `eval_operand (Lit (n2w capacity)) s = SOME (n2w capacity) /\
   op_taint tn (Lit (n2w capacity)) = {}` by
    simp[eval_operand_def, op_taint_def] >>
  drule_all (emit_bulk_binop_counted_ptr |>
    Q.INST [`opc` |-> `GT`, `right` |-> `Lit (n2w capacity)`,
      `f` |-> `(\a b. bool_to_word (w2n a > w2n b))`] |> SRULE []) >>
  disch_then (qspecl_then [`PG`, `G`, `D`] strip_assume_tac) >>
  `lookup_var gt sf = SOME 0w` by
    (gvs[wordsTheory.w2n_n2w, LESS_MOD, bool_to_word_def] >>
     `len < dimword(:256)` by decide_tac >> gvs[LESS_MOD]) >>
  `eval_operand (Var gt) sf = SOME 0w` by simp[eval_operand_def] >>
  drule_all emit_iszero_counted_ptr >>
  disch_then (qspecl_then [`PG`, `Gf`, `D`] strip_assume_tac) >>
  `eval_operand (Var ok) sf' = SOME 1w /\ (1w:bytes32) <> 0w` by
    simp[eval_operand_def, bool_to_word_def] >>
  drule_all emit_assert_success_counted_ptr >>
  disch_then (qspecl_then [`PG`, `Gf'`, `D`] strip_assume_tac) >>
  qexistsl_tac [`Gf'`, `tnf'`, `sf' with vs_inst_idx := SUC sf'.vs_inst_idx`] >>
  conj_tac >-
    (irule (gas_path_ptr_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SRULE []) >>
     qexistsl_tac [`Gf`, `sf`, `tnf`] >> simp[] >>
     irule (gas_path_ptr_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SRULE []) >>
     qexistsl_tac [`Gf'`, `sf'`, `tnf'`] >> gvs[]) >>
  gvs[lookup_var_def] >> metis_tac[]
QED


(* Pointer arithmetic exports the new provenance, not just cleanliness. *)
Theorem emit_bulk_offset_ambient_counted_ptr:
  emit_op ADD [Var root; Lit (n2w off)] sa = (Var out,sb) /\
  fn_has_code sa sb fn /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ lookup_var root s = SOME a /\
  ptr_covers G tn root s extent /\ off+n <= extent /\
  w2n a + off < dimword(:256) ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    lookup_var out sf = SOME (n2w (w2n a+off)) /\
    ptr_covers Gf tnf out sf n /\
    sf.vs_allocas = s.vs_allocas /\ sf.vs_alloca_next = s.vs_alloca_next /\
    sf.vs_fmp = s.vs_fmp /\
    sf.vs_memory = s.vs_memory /\ tnf.t_mem = tn.t_mem /\
    tnf.t_imm = tn.t_imm /\ sf.vs_accounts = s.vs_accounts /\
    sf.vs_transient = s.vs_transient /\ sf.vs_call_ctx = s.vs_call_ctx /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!p. not_fresh_at sa p ==>
      lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++
     [mk_inst sa.cs_next_id ADD [Var root; Lit (n2w off)] [out]] /\
   (!p. not_fresh_at sa p ==> p <> out)` by
    (gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
         fresh_id_def, emit_def, comp_return_def, not_fresh_at_def] >>
     metis_tac[LESS_EQ_REFL]) >>
  qabbrev_tac `t = update_var out (a + n2w off) s` >>
  qabbrev_tac `gf = step_prov PG G
    (mk_inst sa.cs_next_id ADD [Var root; Lit (n2w off)] [out]) t` >>
  qabbrev_tac `tf = step_taint
    (mk_inst sa.cs_next_id ADD [Var root; Lit (n2w off)] [out]) s t tn` >>
  qexistsl_tac [`gf`, `tf`, `t with vs_inst_idx := SUC s.vs_inst_idx`] >>
  conj_tac >-
    (qunabbrev_tac `gf` >> qunabbrev_tac `tf` >>
     irule emitted_step_counted_ptr >> simp[mk_inst_def, is_terminator_def] >>
     conj_tac >-
       (pure_once_rewrite_tac[step_inst_base_def] >>
        simp[mk_inst_def, exec_pure2_def, Abbr `t`, eval_operand_def]) >>
     conj_tac >- (qexistsl_tac [`sa`, `sb`] >> simp[mk_inst_def]) >>
     irule (SRULE [mk_inst_def] ptr_inst_ok_copy_len_binop) >>
     simp[eval_operand_def, op_taint_def] >> gvs[ptr_covers_def, op_taint_def]) >>
  conj_tac >- simp[Abbr `t`, update_var_def] >>
  conj_tac >- simp[Abbr `t`, update_var_def] >>
  conj_tac >- simp[Abbr `t`, update_var_def] >>
  conj_tac >-
    simp[Abbr `t`, lookup_var_def, update_var_def, FLOOKUP_UPDATE,
         GSYM word_add_n2w] >>
  conj_tac >-
    (`op_taint tf (Var out) = {}` by
       simp[Abbr `tf`, Abbr `t`, copy_len_binop_ghost_frame] >>
     gvs[ptr_covers_def] >>
     `off < dimword(:256)` by decide_tac >>
     simp[Abbr `gf`, Abbr `t`, step_prov_def, set_prov_def, out_prov_def,
          first_prov_def, op_prov_def, mk_inst_def, FLOOKUP_UPDATE,
          lookup_var_def, update_var_def, w2n_add_2, w2n_n2w, LESS_MOD] >> decide_tac) >>
  simp[Abbr `tf`, Abbr `gf`, Abbr `t`, copy_len_binop_ghost_frame,
       step_taint_def, imm_taint_def, mk_inst_def,
       update_var_def, lookup_var_def, FLOOKUP_UPDATE] >> rpt strip_tac >>
  `p <> out` by metis_tac[] >>
  simp[copy_len_binop_ghost_frame, update_var_def, lookup_var_def, FLOOKUP_UPDATE]
QED


Theorem emit_bulk_offset_counted_ptr:
  emit_op ADD [Var root; Lit (n2w off)] sa = (Var out,sb) /\
  fn_has_code sa sb fn /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ lookup_var root s = SOME a /\
  ptr_covers G tn root s extent /\ off+n <= extent /\
  w2n a + off < dimword(:256) ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    lookup_var out sf = SOME (n2w (w2n a+off)) /\
    ptr_covers Gf tnf out sf n /\
    sf.vs_allocas = s.vs_allocas /\ sf.vs_alloca_next = s.vs_alloca_next /\
    sf.vs_fmp = s.vs_fmp /\
    sf.vs_memory = s.vs_memory /\ tnf.t_mem = tn.t_mem /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!p. not_fresh_at sa p ==>
      lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >> drule_all emit_bulk_offset_ambient_counted_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`Gf`, `tnf`, `sf`] >> simp[]
QED

(* The data suffix of the equal-element dynamic-array branch. *)
Theorem emit_bulk_data_counted_ptr:
  emit_op ADD [Var src;Lit 32w] sa = (Var sp,sb) /\
  emit_op ADD [Var dst;Lit 32w] sb = (Var dp,sc) /\
  emit_op MUL [Var length;Lit (n2w elem)] sc = (Var nbytes,sd) /\
  compile_copy_memory_dynamic (Var dp) (Var sp) (Var nbytes) sd = ((),se) /\
  fn_has_code sa sb fn /\ fn_has_code sb sc fn /\
  fn_has_code sc sd fn /\ fn_has_code sd se fn /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\
  not_fresh_at sa src /\ not_fresh_at sa dst /\ not_fresh_at sa length /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  lookup_var length s = SOME (n2w len) /\ op_taint tn (Var length) = {} /\
  ptr_covers G tn src s (32+len*elem) /\
  ptr_covers G tn dst s (32+len*elem) /\
  w2n a + 32 < dimword(:256) /\ w2n b + 32 < dimword(:256) /\
  len < dimword(:256) /\ elem < dimword(:256) /\ len*elem < dimword(:256) ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = se.cs_current_bb /\
    sf.vs_inst_idx = LENGTH se.cs_current_insts /\ ~sf.vs_halted /\
    sf.vs_memory = (mcopy (w2n b+32) (w2n a+32) (len*elem) s).vs_memory /\
    tnf.t_mem = (tn.t_mem DIFF {i | w2n b+32 <= i /\ i < w2n b+32+len*elem}) UNION
      {w2n b+32+i | i < len*elem /\ w2n a+32+i IN tn.t_mem} /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!p. not_fresh_at sa p ==>
      lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  `(!p. not_fresh_at sa p ==> not_fresh_at sb p) /\
   (!p. not_fresh_at sb p ==> not_fresh_at sc p) /\
   (!p. not_fresh_at sc p ==> not_fresh_at sd p) /\
   not_fresh_at sb sp /\ not_fresh_at sc dp` by
    (gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
         fresh_id_def, emit_def, comp_return_def, not_fresh_at_def] >>
     metis_tac[LESS_EQ_REFL, LESS_EQ_TRANS]) >>
  `emit_op ADD [Var src;Lit (n2w 32)] sa = (Var sp,sb)` by simp[] >>
  drule_all (emit_bulk_offset_ambient_counted_ptr |>
    Q.INST [`off` |-> `32`, `n` |-> `len*elem`, `extent` |-> `32+len*elem`] |> SRULE []) >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `lookup_var dst sf = SOME b /\ lookup_var length sf = SOME (n2w len) /\
   op_taint tnf (Var length) = {} /\ ptr_covers Gf tnf dst sf (32+len*elem)` by
    (gvs[ptr_covers_def] >> metis_tac[]) >>
  `emit_op ADD [Var dst;Lit (n2w 32)] sb = (Var dp,sc)` by simp[] >>
  drule_all (emit_bulk_offset_ambient_counted_ptr |>
    Q.INST [`off` |-> `32`, `n` |-> `len*elem`, `extent` |-> `32+len*elem`] |> SRULE []) >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `eval_operand (Var length) sf' = SOME (n2w len) /\
   op_taint tnf' (Var length) = {} /\
   eval_operand (Lit (n2w elem)) sf' = SOME (n2w elem) /\
   op_taint tnf' (Lit (n2w elem)) = {}` by
    (simp[eval_operand_def, op_taint_def] >> metis_tac[]) >>
  drule_all (emit_bulk_binop_counted_ptr |>
    Q.INST [`opc` |-> `MUL`, `f` |-> `word_mul`] |> SRULE []) >>
  disch_then (qspecl_then [`PG`, `Gf'`, `D`] strip_assume_tac) >>
  `lookup_var sp sf'' = SOME (n2w (w2n a+32)) /\
   lookup_var dp sf'' = SOME (n2w (w2n b+32)) /\
   ptr_covers Gf'' tnf'' sp sf'' (w2n (n2w (len*elem):bytes32)) /\
   ptr_covers Gf'' tnf'' dp sf'' (w2n (n2w (len*elem):bytes32)) /\
   eval_operand (Var nbytes) sf'' = SOME (n2w (len*elem))` by
    (simp[eval_operand_def, word_mul_n2w, w2n_n2w, LESS_MOD] >>
     gvs[ptr_covers_def] >> metis_tac[]) >>
  drule_all compile_copy_memory_dynamic_counted_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`Gf''`, `tnf'''`, `sf'''`] >>
  conj_tac >-
    (irule (gas_path_ptr_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SRULE []) >>
     qexistsl_tac [`Gf`, `sf`, `tnf`] >> simp[] >>
     irule (gas_path_ptr_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SRULE []) >>
     qexistsl_tac [`Gf'`, `sf'`, `tnf'`] >> simp[] >>
     irule (gas_path_ptr_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SRULE []) >>
     qexistsl_tac [`Gf''`, `sf''`, `tnf''`] >> simp[]) >>
  conj_tac >- simp[] >> conj_tac >- simp[] >> conj_tac >- simp[] >>
  conj_tac >- gvs[w2n_n2w, LESS_MOD, mcopy_def, read_memory_def,
                  write_memory_with_expansion_def, expand_memory_def] >>
  gvs[w2n_n2w, LESS_MOD] >> metis_tac[]
QED


Theorem emit_bulk_header_counted_ptr:
  emit_op MLOAD [Var src] sa = (Var length,sb) /\
  emit_op GT [Var length;Lit (n2w capacity)] sb = (Var gt,sc) /\
  emit_op ISZERO [Var gt] sc = (Var ok,sd) /\
  emit_void ASSERT [Var ok] sd = ((),se) /\
  emit_void MSTORE [Var dst;Var length] se = ((),sg) /\
  fn_has_code sa sb fn /\ fn_has_code sb sc fn /\
  fn_has_code sc sd fn /\ fn_has_code sd se fn /\ fn_has_code se sg fn /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ not_fresh_at sa src /\ not_fresh_at sa dst /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  ptr_covers G tn src s 32 /\ ptr_covers G tn dst s 32 /\
  (!i. w2n a <= i /\ i < w2n a+32 ==> i NOTIN tn.t_mem) /\
  mload (w2n a) s = n2w len /\ len <= capacity /\ capacity < dimword(:256) ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sg.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sg.cs_current_insts /\ ~sf.vs_halted /\
    lookup_var length sf = SOME (n2w len) /\ op_taint tnf (Var length) = {} /\
    sf.vs_memory = (mstore (w2n b) (n2w len) s).vs_memory /\
    tnf.t_mem = tn.t_mem DIFF {i | w2n b <= i /\ i < w2n b+32} /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!p. not_fresh_at sa p ==>
      lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  `(!p. not_fresh_at sa p ==> not_fresh_at sb p) /\
   not_fresh_at sb length` by
    (gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
         fresh_id_def, emit_def, comp_return_def, not_fresh_at_def] >>
     metis_tac[LESS_EQ_REFL, LESS_EQ_TRANS]) >>
  drule_all emit_mload_clean_counted_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `eval_operand (Var length) sf = SOME (n2w len)` by simp[eval_operand_def] >>
  drule_all emit_bulk_capacity_check_counted_ptr >>
  disch_then (qspecl_then [`PG`, `Gf`, `D`] strip_assume_tac) >>
  `lookup_var dst sf' = SOME b /\
   ptr_covers Gf' tnf' dst sf' 32 /\
   eval_operand (Var length) sf' = SOME (n2w len) /\
   op_taint tnf' (Var length) = {}` by
    (gvs[ptr_covers_def, eval_operand_def] >> metis_tac[]) >>
  drule_all emit_mstore_clean_ambient_counted_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`Gf'`, `tnf''`, `sf''`] >>
  conj_tac >-
    (irule (gas_path_ptr_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SRULE []) >>
     qexistsl_tac [`Gf`, `sf`, `tnf`] >> simp[] >>
     irule (gas_path_ptr_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SRULE []) >>
     qexistsl_tac [`Gf'`, `sf'`, `tnf'`] >> simp[]) >>
  conj_tac >- simp[] >> conj_tac >- simp[] >> conj_tac >- simp[] >>
  conj_tac >- metis_tac[eval_operand_def] >>
  conj_tac >- metis_tac[] >>
  conj_tac >- gvs[mstore_def, write_memory_with_expansion_def, expand_memory_def] >>
  gvs[] >> metis_tac[]
QED


Theorem compile_bulk_dynarray_code:
  compile_copy_dynarray_typed cenv (Var dst) ty capacity (Var src) ty sa = ((),sz) ==>
  ?length gt ok sp dp nb sb sc sd se sg sh si sj.
    emit_op MLOAD [Var src] sa = (Var length,sb) /\
    emit_op GT [Var length;Lit (n2w capacity)] sb = (Var gt,sc) /\
    emit_op ISZERO [Var gt] sc = (Var ok,sd) /\
    emit_void ASSERT [Var ok] sd = ((),se) /\
    emit_void MSTORE [Var dst;Var length] se = ((),sg) /\
    emit_op ADD [Var src;Lit 32w] sg = (Var sp,sh) /\
    emit_op ADD [Var dst;Lit 32w] sh = (Var dp,si) /\
    emit_op MUL [Var length;Lit (n2w (type_memory_bytes cenv ty))] si = (Var nb,sj) /\
    compile_copy_memory_dynamic (Var dp) (Var sp) (Var nb) sj = ((),sz)
Proof
  simp[Once compile_store_memory_typed_def] >>
  simp[emit_op_def, emit_void_def, compile_copy_memory_dynamic_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def, fresh_var_def,
       fresh_id_def, emit_def] >> strip_tac >> gvs[]
QED

Theorem compile_copy_dynarray_bulk_counted_ptr:
  compile_copy_dynarray_typed cenv (Var dst) ty capacity (Var src) ty sa = ((),sz) /\
  fn_has_code sa sz fn /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ not_fresh_at sa src /\ not_fresh_at sa dst /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  ptr_covers G tn src s (32+len*type_memory_bytes cenv ty) /\
  ptr_covers G tn dst s (32+len*type_memory_bytes cenv ty) /\
  (!i. w2n a <= i /\ i < w2n a+32 ==> i NOTIN tn.t_mem) /\
  mload (w2n a) s = n2w len /\ len <= capacity /\ capacity < dimword(:256) /\
  w2n a+32 < dimword(:256) /\ w2n b+32 < dimword(:256) /\
  type_memory_bytes cenv ty < dimword(:256) /\
  len*type_memory_bytes cenv ty < dimword(:256) ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sz.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sz.cs_current_insts /\ ~sf.vs_halted /\
    sf.vs_memory =
      (mcopy (w2n b+32) (w2n a+32) (len*type_memory_bytes cenv ty)
        (mstore (w2n b) (n2w len) s)).vs_memory /\
    tnf.t_mem =
      ((tn.t_mem DIFF {i | w2n b <= i /\ i < w2n b+32}) DIFF
        {i | w2n b+32 <= i /\ i < w2n b+32+len*type_memory_bytes cenv ty}) UNION
      {w2n b+32+i | i | i < len*type_memory_bytes cenv ty /\
        w2n a+32+i IN (tn.t_mem DIFF {j | w2n b <= j /\ j < w2n b+32})} /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!p. not_fresh_at sa p ==>
      lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >> drule compile_bulk_dynarray_code >> strip_tac >>
  `fn_has_code sa sb fn /\ fn_has_code sb sc fn /\
   fn_has_code sc sd fn /\ fn_has_code sd se fn /\ fn_has_code se sg fn /\
   fn_has_code sg sh fn /\ fn_has_code sh si fn /\
   fn_has_code si sj fn /\ fn_has_code sj sz fn` by
    (gvs[emit_op_def, emit_void_def, compile_copy_memory_dynamic_def,
         comp_bind_def, comp_ignore_bind_def, fresh_var_def, fresh_id_def,
         emit_def, comp_return_def, fragExecTheory.fn_has_code_def,
         fragExecTheory.emitted_blocks_def] >>
     rpt conj_tac >> irule listTheory.isPREFIX_TRANS >>
     goal_assum (drule_at Any) >>
     pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC] >> simp[NoAsms]) >>
  `ptr_covers G tn src s 32 /\ ptr_covers G tn dst s 32` by
    (gvs[ptr_covers_def] >> metis_tac[LESS_EQ_ADD]) >>
  drule_all emit_bulk_header_counted_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `not_fresh_at sg src /\ not_fresh_at sg dst /\ not_fresh_at sg length /\
   (!p. not_fresh_at sa p ==> not_fresh_at sg p)` by
    (gvs[emit_op_def, emit_void_def, comp_bind_def, comp_ignore_bind_def,
         fresh_var_def, fresh_id_def, emit_def, comp_return_def, not_fresh_at_def] >>
     metis_tac[LESS_EQ_REFL, LESS_EQ_TRANS]) >>
  `lookup_var src sf = SOME a /\ lookup_var dst sf = SOME b /\
   ptr_covers Gf tnf src sf (32+len*type_memory_bytes cenv ty) /\
   ptr_covers Gf tnf dst sf (32+len*type_memory_bytes cenv ty) /\
   len < dimword(:256)` by
    (gvs[ptr_covers_def] >> metis_tac[LESS_EQ_LESS_TRANS]) >>
  drule_all emit_bulk_data_counted_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`Gf'`, `tnf'`, `sf'`] >>
  conj_tac >-
    (irule (gas_path_ptr_then |> Q.INST [`n` |-> `0`, `m` |-> `0`] |> SRULE []) >>
     qexistsl_tac [`Gf`, `sf`, `tnf`] >> simp[]) >>
  conj_tac >- simp[] >> conj_tac >- simp[] >> conj_tac >- simp[] >>
  conj_tac >-
    gvs[mcopy_def, read_memory_def, write_memory_with_expansion_def, expand_memory_def] >>
  gvs[] >> metis_tac[]
QED

