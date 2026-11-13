(* Source-independent checked bounds for clean provenance-free words. *)
Theory bodyPtrCodeSliceBounds
Ancestors
  exprSimSliceBounds typedCopyPtr exprSendPtr bodyPtrHashBuiltinsGhostFrame
  fragGasSeqPtr bodyPtrDefs ptrSafeRun ptrDiscipline venomExecSemantics
  venomInst venomState codegenRel contextCodegenRel compileEnv
  loweringStateRelDefs words finite_map pred_set list
  decoderGhostFramePtr venomInstProofs1 venomMemProofs

Theorem slice_bounds_binop_checked:
  !D ctx fn G tn s id opc a b dst fuel.
    (opc = ADD \/ opc = LT \/ opc = GT \/ opc = OR) /\
    op_taint tn a = {} /\ op_taint tn b = {} /\
    op_prov G a = NONE /\ op_prov G b = NONE /\
    ~ctx_has_dalloca ctx ==>
    ptr_inst_ok D 0 fuel ctx fn G tn (mk_inst id opc [a;b] [dst]) s
Proof
  rpt gen_tac >> strip_tac >>
  `!u. a = Var u ==> u NOTIN FDOM G` by
    (rpt strip_tac >> gvs[op_prov_def, FLOOKUP_DEF]) >>
  `!u. b = Var u ==> u NOTIN FDOM G` by
    (rpt strip_tac >> gvs[op_prov_def, FLOOKUP_DEF]) >>
  gvs[] >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
    mk_inst_def, source_memory_write_ranges_def, source_memory_read_ranges_def] >>
  conj_tac >- metis_tac[] >>
  simp[step_inst_non_invoke] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  pure_rewrite_tac[instruction_accessors, instruction_accfupds,
    combinTheory.K_THM, opcode_case_def] >>
  simp[exec_pure2_def, AllCaseEqs(), update_var_def] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem slice_bounds_iszero_checked:
  !D ctx fn G tn s id a dst fuel.
    op_taint tn a = {} /\ ~ctx_has_dalloca ctx ==>
    ptr_inst_ok D 0 fuel ctx fn G tn (mk_inst id ISZERO [a] [dst]) s
Proof
  rpt gen_tac >> strip_tac >>
  simp[ptr_inst_ok_def, access_ok_def, taint_ok_def, allocas_from_def,
    mk_inst_def, source_memory_write_ranges_def, source_memory_read_ranges_def] >>
  simp[step_inst_non_invoke] >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  pure_rewrite_tac[instruction_accessors, instruction_accfupds,
    combinTheory.K_THM, opcode_case_def] >>
  simp[exec_pure1_def, AllCaseEqs(), update_var_def] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem slice_bounds_scalar_ghost:
  !PG G tn s id opc ops out u.
    (opc = ADD \/ opc = LT \/ opc = GT \/ opc = OR \/ opc = ISZERO) /\
    EVERY (\op. op_prov G op = NONE) ops /\
    u.vs_allocas = s.vs_allocas /\ u.vs_fmp = s.vs_fmp ==>
    step_prov PG G (mk_inst id opc ops [out]) u =
      DRESTRICT G (COMPL {out}) /\
    step_taint (mk_inst id opc ops [out]) s u tn =
      (tn with t_var := tn.t_var |+ (out,{}))
Proof
  rpt gen_tac >> disch_tac >>
  `out_prov PG G (mk_inst id opc ops [out]) u = NONE` by
    (Cases_on `opc = ADD`
     >- (irule out_prov_arith_none >> simp[mk_inst_def]) >>
     irule out_prov_other_none >> gvs[mk_inst_def]) >>
  `new_site_bytes s u = {}` by
    simp[new_site_bytes_def, FLOOKUP_DEF, EXTENSION, SF CONJ_ss] >>
  conj_tac >- simp[step_prov_def, set_prov_def, mk_inst_def] >>
  gvs[] >>
  simp[step_taint_def, set_var_taint_def, mk_inst_def,
       mem_taint_def, step_writes_def, source_memory_write_ranges_def,
       written_taint_def, store_taint_def, adopt_reset_def,
       imm_taint_def, range_bytes_def, taint_component_equality] >>
  (Cases_on `ops` >- simp[out_taint_def] >>
   Cases_on `t` >- (simp[out_taint_def] >> CASE_TAC >> simp[]) >>
   Cases_on `t'` >- (simp[out_taint_def] >> CASE_TAC >> simp[]) >>
   Cases_on `t` >> simp[out_taint_def])
QED

Theorem slice_bounds_scalar_frame:
  !d cenv cx es G tn s sa out w.
    ghost_inv d cenv cx es G tn s /\
    local_ptrs_reserved cenv sa /\
    (!p k. cenv.ce_return_buf = SOME (PtrVar (Var p) k) ==> not_fresh_at sa p) /\
    (!p k. cenv.ce_return_pc = SOME (PtrVar (Var p) k) ==> not_fresh_at sa p) /\
    ~not_fresh_at sa out ==>
    ghost_inv d cenv cx es (DRESTRICT G (COMPL {out}))
      (tn with t_var := tn.t_var |+ (out,{})) (update_var out w s) /\
    ghost_kept cenv es sa G tn s (DRESTRICT G (COMPL {out}))
      (tn with t_var := tn.t_var |+ (out,{}))
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- (irule hash_readonly_ghost_inv >> qexistsl_tac [`G`, `s`, `sa`, `tn`] >>
      simp[update_var_def, lookup_var_def, FLOOKUP_UPDATE,
           FLOOKUP_DRESTRICT, op_taint_def] >>
      rpt strip_tac >> metis_tac[]) >>
  irule hash_ghost_kept_frame >>
  simp[FLOOKUP_DRESTRICT, op_taint_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> metis_tac[]
QED

Theorem slice_bounds_scalar_operand_frame:
  !G tn s op out w.
    op <> Var out ==>
    eval_operand op (update_var out w s) = eval_operand op s /\
    op_prov (DRESTRICT G (COMPL {out})) op = op_prov G op /\
    op_taint (tn with t_var := tn.t_var |+ (out,{})) op = op_taint tn op
Proof
  rpt gen_tac >> Cases_on `op` >>
  simp[eval_operand_def, lookup_var_def, update_var_def, op_prov_def,
       op_taint_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE] >>
  metis_tac[]
QED


Theorem slice_bounds_scalar_cons[local]:
  !D ctx fn PG G tn s i u G1 tn1 code Gf tnf.
    ptr_inst_ok D 0 0 ctx fn G tn i s /\
    step_inst_base i s = OK u /\
    step_prov PG G i u = G1 /\ step_taint i s u tn = tn1 /\
    inst_seq_ptr D 0 ctx fn PG G1 tn1 code
      (u with vs_inst_idx := SUC s.vs_inst_idx) Gf tnf ==>
    inst_seq_ptr D 0 ctx fn PG G tn (i::code) s Gf tnf
Proof
  rpt gen_tac >> strip_tac >> simp[Once inst_seq_ptr_def]
QED

Theorem slice_bounds_binop_cons[local]:
  !D ctx fn PG G tn s id opc a b out wa wb f code.
    (opc = ADD /\ f = $+ \/
     opc = LT /\ f = (\x y. bool_to_word (w2n x < w2n y)) \/
     opc = GT /\ f = (\x y. bool_to_word (w2n y < w2n x)) \/
     opc = OR /\ f = $||) /\
    eval_operand a s = SOME wa /\ eval_operand b s = SOME wb /\
    op_taint tn a = {} /\ op_taint tn b = {} /\
    op_prov G a = NONE /\ op_prov G b = NONE /\ ~ctx_has_dalloca ctx /\
    (?Gf tnf. inst_seq_ptr D 0 ctx fn PG (DRESTRICT G (COMPL {out}))
      (tn with t_var := tn.t_var |+ (out,{})) code
      (update_var out (f wa wb) s with vs_inst_idx := SUC s.vs_inst_idx) Gf tnf) ==>
    ?Gf tnf. inst_seq_ptr D 0 ctx fn PG G tn
      (mk_inst id opc [a;b] [out]::code) s Gf tnf
Proof
  rpt gen_tac >> strip_tac >> qexistsl_tac [`Gf`, `tnf`] >>
  (irule slice_bounds_scalar_cons >>
   conj_tac >- (irule slice_bounds_binop_checked >> simp[]) >>
   qexistsl_tac [`DRESTRICT G (COMPL {out})`,
     `tn with t_var := tn.t_var |+ (out,{})`, `update_var out (f wa wb) s`] >>
   gvs[] >>
   simp[update_var_def, step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def,
     arithmeticTheory.GREATER_DEF] >>
   irule (SRULE [mk_inst_def] slice_bounds_scalar_ghost) >> simp[])
QED

Theorem slice_bounds_iszero_cons[local]:
  !D ctx fn PG G tn s id a out wa code.
    eval_operand a s = SOME wa /\ op_taint tn a = {} /\
    op_prov G a = NONE /\ ~ctx_has_dalloca ctx /\
    (?Gf tnf. inst_seq_ptr D 0 ctx fn PG (DRESTRICT G (COMPL {out}))
      (tn with t_var := tn.t_var |+ (out,{})) code
      (update_var out (bool_to_word (wa = 0w)) s with
        vs_inst_idx := SUC s.vs_inst_idx) Gf tnf) ==>
    ?Gf tnf. inst_seq_ptr D 0 ctx fn PG G tn
      (mk_inst id ISZERO [a] [out]::code) s Gf tnf
Proof
  rpt gen_tac >> strip_tac >> qexistsl_tac [`Gf`, `tnf`] >>
  irule slice_bounds_scalar_cons >>
  conj_tac >- (irule slice_bounds_iszero_checked >> simp[]) >>
  qexistsl_tac [`DRESTRICT G (COMPL {out})`,
    `tn with t_var := tn.t_var |+ (out,{})`,
    `update_var out (bool_to_word (wa = 0w)) s`] >>
  simp[update_var_def, step_inst_base_opcode_eqs, mk_inst_def, exec_pure1_def] >>
  irule (SRULE [mk_inst_def] slice_bounds_scalar_ghost) >> simp[]
QED

Theorem slice_bounds_assert_checked[local]:
  !D ctx fn PG G tn s id a w.
    eval_operand a s = SOME w /\ op_taint tn a = {} /\
    ~ctx_has_dalloca ctx ==>
    ?Gf tnf. inst_seq_ptr D 0 ctx fn PG G tn [mk_inst id ASSERT [a] []] s Gf tnf
Proof
  rpt gen_tac >> strip_tac >> qexistsl_tac [`G`, `tn`] >>
  simp[Once inst_seq_ptr_def] >>
  conj_tac >- (irule ptr_inst_ok_assert >> metis_tac[]) >>
  drule venomExecProofsTheory.step_assert_behavior >> strip_tac >> Cases_on `w = 0w` >>
  simp[mk_inst_def, inst_seq_ptr_def, SRULE [mk_inst_def] assert_ghost_unchanged]
QED

Theorem slice_bounds_checked_ptr:
  !D ctx fn PG G tn s a n limit sa sb wa wn wl.
    compile_assert_slice_bounds a n limit sa = ((),sb) /\
    eval_operand a s = SOME wa /\ eval_operand n s = SOME wn /\
    eval_operand limit s = SOME wl /\
    op_taint tn a = {} /\ op_taint tn n = {} /\ op_taint tn limit = {} /\
    op_prov G a = NONE /\ op_prov G n = NONE /\ op_prov G limit = NONE /\
    (!z. a = Var z ==> not_fresh_at sa z) /\
    (!z. n = Var z ==> not_fresh_at sa z) /\
    (!z. limit = Var z ==> not_fresh_at sa z) /\ ~ctx_has_dalloca ctx ==>
    ?Gf tnf. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s Gf tnf
Proof
  rpt gen_tac >> strip_tac >>
  `!j. sa.cs_next_var <= j ==> a <> Var (STRING #"%" (toString j)) /\
       n <> Var (STRING #"%" (toString j)) /\
       limit <> Var (STRING #"%" (toString j))` by
    (rpt strip_tac >> spose_not_then assume_tac >> gvs[not_fresh_at_def] >>
     metis_tac[]) >>
  drule slice_bounds_shape >> strip_tac >> asm_rewrite_tac[] >>
  irule slice_bounds_binop_cons >>
  simp[] >>
  irule slice_bounds_binop_cons >>
  simp[ghostPcTransportPtrTheory.eval_operand_inst_idx,
       slice_bounds_scalar_operand_frame] >>
  simp[eval_operand_def, emitHelperPropsTheory.lookup_var_update_var,
       op_taint_def, op_prov_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE] >>
  irule slice_bounds_binop_cons >>
  simp[ghostPcTransportPtrTheory.eval_operand_inst_idx,
       slice_bounds_scalar_operand_frame] >>
  simp[eval_operand_def, emitHelperPropsTheory.lookup_var_update_var,
       op_taint_def, op_prov_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE] >>
  conj_tac >- (Cases_on `limit` >> gvs[op_taint_def] >>
    rpt IF_CASES_TAC >> gvs[]) >>
  conj_tac >- (Cases_on `limit` >> gvs[op_prov_def] >>
    rpt IF_CASES_TAC >> gvs[]) >>
  irule slice_bounds_binop_cons >>
  simp[ghostPcTransportPtrTheory.eval_operand_inst_idx,
       eval_operand_def, emitHelperPropsTheory.lookup_var_update_var,
       op_taint_def, op_prov_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE] >>
  simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  irule slice_bounds_iszero_cons >>
  simp[eval_operand_def, lookup_var_def, update_var_def,
       op_taint_def, op_prov_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE] >>
  irule slice_bounds_assert_checked >>
  simp[eval_operand_def, lookup_var_def, update_var_def,
       op_taint_def, FLOOKUP_UPDATE]
QED

Theorem slice_bounds_step_frame[local]:
  !i s u tn.
    MEM i.inst_opcode [ADD;LT;GT;OR;ISZERO;ASSERT] /\
    step_inst_base i s = OK u ==>
    (step_taint i s u tn).t_mem = tn.t_mem /\
    (step_taint i s u tn).t_stor = tn.t_stor /\
    (step_taint i s u tn).t_trans = tn.t_trans /\
    (step_taint i s u tn).t_imm = tn.t_imm
Proof
  rpt gen_tac >> strip_tac >>
  `u.vs_allocas = s.vs_allocas` by
    (irule step_inst_base_preserves_allocas >> qexists_tac `i` >>
     gvs[] >> metis_tac[]) >>
  `u.vs_fmp = s.vs_fmp` by
    (irule step_inst_base_preserves_fmp_ordinary >> qexists_tac `i` >>
     gvs[] >> simp[is_terminator_def, is_alloca_op_def, is_ext_call_op_def]) >>
  `new_site_bytes s u = {}` by
    simp[new_site_bytes_def, FLOOKUP_DEF, EXTENSION, SF CONJ_ss] >>
  gvs[] >>
  simp[step_taint_def, mem_taint_def, step_writes_def,
       source_memory_write_ranges_def, written_taint_def, store_taint_def,
       adopt_reset_def, imm_taint_def, range_bytes_def] >>
  Cases_on `i.inst_operands` >> simp[] >>
  Cases_on `t` >> simp[] >> Cases_on `t'` >> simp[] >>
  Cases_on `t` >> simp[]
QED

Theorem slice_bounds_seq_frame[local]:
  !code sa D ctx fn PG G tn s Gf tnf.
    EVERY (\i. MEM i.inst_opcode [ADD;LT;GT;OR;ISZERO;ASSERT] /\
      EVERY (\x. ~not_fresh_at sa x) i.inst_outputs) code /\
    inst_seq_ptr D 0 ctx fn PG G tn code s Gf tnf ==>
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==> FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tnf (Var x) = op_taint tn (Var x))
Proof
  Induct >- simp[inst_seq_ptr_def] >>
  rpt gen_tac >> simp_tac pure_ss [Once inst_seq_ptr_def, EVERY_DEF] >> strip_tac >>
  Cases_on `step_inst_base h s` >>
  full_simp_tac bool_ss [exec_result_case_def] >>
  rename1 `step_inst_base h s = OK u` >>
  (first_x_assum (drule_all_then strip_assume_tac) >>
      drule_at (Pat `step_inst_base _ _ = _`) slice_bounds_step_frame >>
      simp[] >> disch_then (qspec_then `tn` strip_assume_tac) >>
      simp[] >> rpt strip_tac >>
      `~MEM x h.inst_outputs` by (gvs[EVERY_MEM] >> metis_tac[]) >>
      metis_tac[step_prov_other_output, step_taint_other_output])
QED

Theorem slice_bounds_ghost_frame:
  !d cenv cx es D ctx fn PG G tn s a n limit sa sb t Gf tnf.
    compile_assert_slice_bounds a n limit sa = ((),sb) /\
    inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sa sb) s Gf tnf /\
    run_inst_seq (emitted_insts sa sb) s = OK t /\
    ghost_inv d cenv cx es G tn s /\ local_ptrs_reserved cenv sa /\
    (!p k. cenv.ce_return_buf = SOME (PtrVar (Var p) k) ==> not_fresh_at sa p) /\
    (!p k. cenv.ce_return_pc = SOME (PtrVar (Var p) k) ==> not_fresh_at sa p) ==>
    ghost_inv d cenv cx es Gf tnf t /\ ghost_kept cenv es sa G tn s Gf tnf
Proof
  rpt gen_tac >> strip_tac >>
  `EVERY (\i. MEM i.inst_opcode [ADD;LT;GT;OR;ISZERO;ASSERT] /\
     EVERY (\x. ~not_fresh_at sa x) i.inst_outputs) (emitted_insts sa sb)` by
    (drule slice_bounds_shape >> strip_tac >>
     simp[mk_inst_def, not_fresh_at_def]) >>
  drule_all slice_bounds_seq_frame >> strip_tac >>
  `writes_fresh sa (emitted_insts sa sb)` by
    (irule slice_bounds_writes_fresh >> metis_tac[]) >>
  drule_all freshWritesTheory.run_inst_seq_writes_fresh >> strip_tac >>
  `t with vs_vars := s.vs_vars = s` by
    (qpat_x_assum `t = s with vs_vars := _` (fn th => once_rewrite_tac [th]) >>
     simp[]) >>
  conj_tac
  >- (irule hash_readonly_ghost_inv >> qexistsl_tac [`G`, `s`, `sa`, `tn`] >>
      simp[lookup_var_def] >> metis_tac[]) >>
  irule hash_ghost_kept_frame >> simp[]
QED
