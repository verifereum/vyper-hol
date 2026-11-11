(* Source-independent checked bounds for clean provenance-free words. *)
Theory bodyPtrCodeSliceBounds
Ancestors
  exprSimSliceBounds typedCopyPtr exprSendPtr bodyPtrHashBuiltinsGhostFrame
  fragGasSeqPtr bodyPtrDefs ptrSafeRun ptrDiscipline venomExecSemantics
  venomInst venomState codegenRel contextCodegenRel compileEnv
  loweringStateRelDefs words finite_map pred_set list

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
