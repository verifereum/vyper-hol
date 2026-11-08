(* The storage pop header may be computed, rather than literal. *)
Theory bodyPtrPopStoragePureTransfer
Ancestors
  bodyPtrPopRootTransfer bodyPtrPopScalarTransfer exprSimPopNestedBase
  stmtAppendStorageRunPtr fragGasSeqPtr ptrSafeRun ptrDiscipline
  venomExecSemantics venomInst venomState codegenRel contextCodegenRel
  finite_map pred_set list instSeqComposePtr exprSimPop exprLoweringProps
  forPtrSeqCompose

Theorem pop_storage_header_transfer:
  ~ctx_has_dalloca ctx /\ eval_operand hdr s = SOME slot /\
  op_taint tn hdr = {} /\ op_prov G hdr = NONE /\
  key_taint (if tr then tn.t_trans else tn.t_stor) slot = {} ==>
  inst_seq_ptr D 0 ctx fn PG G tn
    [mk_inst id (if tr then TLOAD else SLOAD) [hdr] [out]] s
    (DRESTRICT G (COMPL {out}))
    (tn with t_var := tn.t_var |+ (out,{}))
Proof
  strip_tac >>
  `step_inst_base (mk_inst id (if tr then TLOAD else SLOAD) [hdr] [out]) s =
    OK (update_var out (if tr then tload slot s else sload slot s) s)` by
    (simp[nested_pop_step_load]) >>
  `ptr_inst_ok D 0 0 ctx fn G tn
     (mk_inst id (if tr then TLOAD else SLOAD) [hdr] [out]) s` by
    (irule append_scalar_inst_check >> simp[] >> Cases_on `tr` >> simp[]) >>
  simp[inst_seq_ptr_def] >> conj_tac
  >- (simp[step_prov_def, out_prov_def, set_prov_def, mk_inst_def] >>
      Cases_on `tr` >> simp[]) >>
  sym_tac >> irule scalar_storage_load_taint >>
  simp[update_var_def]
QED

Theorem pop_storage_prefix_transfer:
  ~ctx_has_dalloca ctx /\ eval_operand hdr s = SOME slot /\
  op_taint tn hdr = {} /\ op_prov G hdr = NONE /\
  key_taint (if tr then tn.t_trans else tn.t_stor) slot = {} /\
  Gf = DRESTRICT (DRESTRICT (DRESTRICT G (COMPL {x0})) (COMPL {x1})) (COMPL {x2}) /\
  tnf = (tn with t_var := tn.t_var |+ (x0,{}) |+ (x1,{}) |+ (x2,{})) ==>
  inst_seq_ptr D 0 ctx fn PG G tn
    [mk_inst id (if tr then TLOAD else SLOAD) [hdr] [x0];
     mk_inst (id+1) ISZERO [Var x0] [x1];
     mk_inst (id+2) ISZERO [Var x1] [x2];
     mk_inst (id+3) ASSERT [Var x2] []] s Gf tnf
Proof
  strip_tac >>
  `inst_seq_ptr D 0 ctx fn PG G tn
    [mk_inst id (if tr then TLOAD else SLOAD) [hdr] [x0]] s
    (DRESTRICT G (COMPL {x0})) (tn with t_var := tn.t_var |+ (x0,{}))` by
    (irule pop_storage_header_transfer >> metis_tac[]) >>
  pop_assum mp_tac >> simp[Once inst_seq_ptr_def, nested_pop_step_load] >>
  strip_tac >> simp[Once inst_seq_ptr_def, nested_pop_step_load] >>
  qpat_x_assum `inst_seq_ptr _ _ _ _ _ _ _ [] _ _ _`
    (strip_assume_tac o SRULE [inst_seq_ptr_def]) >>
  qpat_x_assum `DRESTRICT _ _ = _` (fn th => rewrite_tac[GSYM th]) >>
  qpat_x_assum `(_ with t_var := _) = _` (fn th => rewrite_tac[GSYM th]) >>
  irule pop_root_guard_transfer_at >>
  simp[lookup_var_def, update_var_def, op_taint_def, FLOOKUP_UPDATE] >>
  goal_assum (drule_at Any) >> simp[]
QED

(* The empty branch never reaches the store, even in static calls. *)
Theorem pop_storage_slice_transfer_empty:
  ~ctx_has_dalloca ctx /\ eval_operand hdr s = SOME slot /\
  op_taint tn hdr = {} /\ op_prov G hdr = NONE /\
  (if tr then tload slot s else sload slot s) = 0w /\
  key_taint (if tr then tn.t_trans else tn.t_stor) slot = {} /\
  Gf = DRESTRICT (DRESTRICT (DRESTRICT G (COMPL {x0})) (COMPL {x1})) (COMPL {x2}) /\
  tnf = (tn with t_var := tn.t_var |+ (x0,{}) |+ (x1,{}) |+ (x2,{})) ==>
  inst_seq_ptr D 0 ctx fn PG G tn
    ([mk_inst id (if tr then TLOAD else SLOAD) [hdr] [x0];
      mk_inst (id+1) ISZERO [Var x0] [x1];
      mk_inst (id+2) ISZERO [Var x1] [x2];
      mk_inst (id+3) ASSERT [Var x2] []] ++ rest) s Gf tnf
Proof
  strip_tac >> irule inst_seq_ptr_abort_append >> conj_tac
  >- (simp[run_inst_seq_def, nested_pop_step_load,
           exprSimPopTheory.pop_step_ISZERO, exprSimPopTheory.pop_step_ASSERT,
           lookup_var_def, update_var_def, FLOOKUP_UPDATE, bool_to_word_def]) >>
  conj_tac >- (Cases_on `tr` >> simp[mk_inst_def, is_terminator_def]) >>
  irule pop_storage_prefix_transfer >> metis_tac[]
QED

(* Exact ghosts, uniformly in the cursor, for exported sequence composition. *)
Theorem pop_storage_binary_singleton:
  (opc = SUB /\ z = x-y \/ opc = ADD /\ z = x+y \/ opc = MUL /\ z = x*y) /\
  eval_operand a s = SOME x /\ eval_operand b s = SOME y /\
  op_prov G a = NONE /\ op_prov G b = NONE /\
  op_taint tn a = {} /\ op_taint tn b = {} /\ ~ctx_has_dalloca ctx /\
  Gf = DRESTRICT G (COMPL {out}) /\
  tnf = (tn with t_var := tn.t_var |+ (out,{})) ==>
  !k. inst_seq_ptr D 0 ctx fn PG G tn [mk_inst id opc [a;b] [out]]
    (s with vs_inst_idx := k) Gf tnf
Proof
  rpt strip_tac >>
  `step_inst_base (mk_inst id opc [a;b] [out]) (s with vs_inst_idx := k) =
     OK (update_var out z (s with vs_inst_idx := k)) /\
   ptr_inst_ok D 0 0 ctx fn G tn (mk_inst id opc [a;b] [out])
     (s with vs_inst_idx := k)` by
    (irule pop_scalar_binary_step >> gvs[eval_operand_def, lookup_var_def]) >>
  `step_prov PG G (mk_inst id opc [a;b] [out])
     (update_var out z (s with vs_inst_idx := k)) = DRESTRICT G (COMPL {out}) /\
   step_taint (mk_inst id opc [a;b] [out]) (s with vs_inst_idx := k)
     (update_var out z (s with vs_inst_idx := k)) tn =
       tn with t_var := tn.t_var |+ (out,{})` by
    (irule pop_scalar_binary_ghost >> metis_tac[]) >>
  simp[inst_seq_ptr_def] >> gvs[]
QED

Theorem pop_storage_address_transfer:
  ALL_DISTINCT [x3;x4;x5;x6] /\ ~ctx_has_dalloca ctx /\
  eval_operand hdr s = SOME slot /\ op_prov G hdr = NONE /\ op_taint tn hdr = {} /\
  lookup_var x3 s = SOME n /\ op_prov G (Var x3) = NONE /\
  op_taint tn (Var x3) = {} ==>
  ?Gf tnf.
    (!k. inst_seq_ptr D 0 ctx fn PG G tn
      [mk_inst id ADD [hdr; Lit 1w] [x4];
       mk_inst (id+1) MUL [Var x3; Lit esz] [x5];
       mk_inst (id+2) ADD [Var x4; Var x5] [x6]]
      (s with vs_inst_idx := k) Gf tnf) /\
    op_prov Gf (Var x6) = NONE /\ op_taint tnf (Var x6) = {} /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!v. ~MEM v [x4;x5;x6] ==> FLOOKUP Gf v = FLOOKUP G v /\
         op_taint tnf (Var v) = op_taint tn (Var v))
Proof
  strip_tac >>
  qexistsl
    [`DRESTRICT (DRESTRICT (DRESTRICT G (COMPL {x4})) (COMPL {x5})) (COMPL {x6})`,
     `tn with t_var := tn.t_var |+ (x4,{}) |+ (x5,{}) |+ (x6,{})`] >>
  reverse conj_tac
  >- (gvs[ALL_DISTINCT, op_prov_def, op_taint_def, FLOOKUP_DRESTRICT,
           FLOOKUP_UPDATE] >> rpt strip_tac >> simp[]) >>
  irule for_inst_seq_ptr_cons_nonterminator >>
  conj_tac >- simp[mk_inst_def, is_terminator_def] >>
  qexistsl [`DRESTRICT G (COMPL {x4})`,
    `tn with t_var := tn.t_var |+ (x4,{})`, `update_var x4 (slot+1w) s`] >>
  conj_tac >- (irule pop_storage_binary_singleton >>
    simp[eval_operand_def, op_prov_def, op_taint_def] >> metis_tac[]) >>
  reverse conj_tac
  >- simp[nested_pop_step_add] >>
  irule for_inst_seq_ptr_cons_nonterminator >>
  conj_tac >- simp[mk_inst_def, is_terminator_def] >>
  qexistsl [`DRESTRICT (DRESTRICT G (COMPL {x4})) (COMPL {x5})`,
    `tn with t_var := tn.t_var |+ (x4,{}) |+ (x5,{})`,
    `update_var x5 (n*esz) (update_var x4 (slot+1w) s)`] >>
  conj_tac >- (irule pop_storage_binary_singleton >>
    gvs[ALL_DISTINCT, eval_operand_def, op_prov_def, op_taint_def,
        lookup_var_def, update_var_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE]) >>
  reverse conj_tac
  >- (irule emitHelperPropsTheory.step_MUL >>
      gvs[ALL_DISTINCT, eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  irule pop_storage_binary_singleton >>
  gvs[ALL_DISTINCT, eval_operand_def, op_prov_def, op_taint_def,
      lookup_var_def, update_var_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE]
QED

Theorem pop_storage_store_transfer:
  ~ctx_has_dalloca ctx /\ ~s.vs_call_ctx.cc_static /\
  eval_operand hdr s = SOME slot /\ op_taint tn hdr = {} /\
  op_prov G hdr = NONE /\ eval_operand v s = SOME w /\ op_taint tn v = {} ==>
  !k. inst_seq_ptr D 0 ctx fn PG G tn
    [mk_inst id (if tr then TSTORE else SSTORE) [hdr;v] []]
    (s with vs_inst_idx := k) G
    (if tr then tn with t_trans := key_update tn.t_trans slot {}
     else tn with t_stor := key_update tn.t_stor slot {})
Proof
  rpt strip_tac >>
  qabbrev_tac `u = if tr then tstore slot w (s with vs_inst_idx := k)
                   else sstore slot w (s with vs_inst_idx := k)` >>
  `step_inst_base (mk_inst id (if tr then TSTORE else SSTORE) [hdr;v] [])
     (s with vs_inst_idx := k) = OK u` by
    (Cases_on `tr` >>
     simp[step_inst_base_opcode_eqs, mk_inst_def, exec_write2_def,
          eval_operand_def, lookup_var_def, Abbr `u`] >>
     Cases_on `hdr` >> Cases_on `v` >> gvs[eval_operand_def, lookup_var_def]) >>
  `ptr_inst_ok D 0 0 ctx fn G tn
     (mk_inst id (if tr then TSTORE else SSTORE) [hdr;v] [])
     (s with vs_inst_idx := k)` by
    (irule append_scalar_inst_check >>
     Cases_on `tr` >> simp[Abbr `u`, sstore_def, tstore_def] >>
     rpt strip_tac >> gvs[]) >>
  `u.vs_allocas = s.vs_allocas /\ u.vs_fmp = s.vs_fmp /\
   u.vs_requests = s.vs_requests` by
    (Cases_on `tr` >> simp[Abbr `u`, sstore_def, tstore_def]) >>
  simp[inst_seq_ptr_def, scalar_void_prov] >>
  sym_tac >> irule scalar_storage_store_taint >>
  Cases_on `hdr` >> Cases_on `v` >> gvs[eval_operand_def, lookup_var_def]
QED
