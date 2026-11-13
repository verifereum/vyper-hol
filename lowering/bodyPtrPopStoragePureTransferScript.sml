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

Theorem pop_storage_store_address_transfer:
  ALL_DISTINCT [x3;x4;x5;x6] /\ ~ctx_has_dalloca ctx /\
  ~s.vs_call_ctx.cc_static /\ lookup_var x3 s = SOME n /\
  eval_operand hdr s = SOME slot /\ op_prov G hdr = NONE /\ op_taint tn hdr = {} /\
  op_prov G (Var x3) = NONE /\ op_taint tn (Var x3) = {} ==>
  ?Gf tnf.
    (!k. inst_seq_ptr D 0 ctx fn PG G tn
      [mk_inst id (if tr then TSTORE else SSTORE) [hdr; Var x3] [];
       mk_inst (id+1) ADD [hdr; Lit 1w] [x4];
       mk_inst (id+2) MUL [Var x3; Lit esz] [x5];
       mk_inst (id+3) ADD [Var x4; Var x5] [x6]]
      (s with vs_inst_idx := k) Gf tnf) /\
    op_prov Gf (Var x6) = NONE /\ op_taint tnf (Var x6) = {} /\
    tnf.t_mem = tn.t_mem /\ tnf.t_imm = tn.t_imm /\
    tnf.t_stor = (if tr then tn.t_stor else key_update tn.t_stor slot {}) /\
    tnf.t_trans = (if tr then key_update tn.t_trans slot {} else tn.t_trans) /\
    (!v. ~MEM v [x4;x5;x6] ==> FLOOKUP Gf v = FLOOKUP G v /\
         op_taint tnf (Var v) = op_taint tn (Var v))
Proof
  strip_tac >>
  qabbrev_tac `t = if tr then tstore slot n s else sstore slot n s` >>
  qabbrev_tac `tn1 = if tr then tn with t_trans := key_update tn.t_trans slot {}
                    else tn with t_stor := key_update tn.t_stor slot {}` >>
  `?Gf tnf.
    (!k. inst_seq_ptr D 0 ctx fn PG G tn1
      [mk_inst (id+1) ADD [hdr; Lit 1w] [x4];
       mk_inst ((id+1)+1) MUL [Var x3; Lit esz] [x5];
       mk_inst ((id+1)+2) ADD [Var x4; Var x5] [x6]]
       (t with vs_inst_idx := k) Gf tnf) /\
    op_prov Gf (Var x6) = NONE /\ op_taint tnf (Var x6) = {} /\
    tnf.t_mem = tn1.t_mem /\ tnf.t_stor = tn1.t_stor /\
    tnf.t_trans = tn1.t_trans /\ tnf.t_imm = tn1.t_imm /\
    (!v. ~MEM v [x4;x5;x6] ==> FLOOKUP Gf v = FLOOKUP G v /\
         op_taint tnf (Var v) = op_taint tn1 (Var v))` by
    (irule pop_storage_address_transfer >>
     Cases_on `tr` >> gvs[Abbr `t`, Abbr `tn1`, sstore_def, tstore_def,
       lookup_var_def, op_taint_def, eval_operand_def] >>
     Cases_on `hdr` >> gvs[eval_operand_def, lookup_var_def, op_taint_def]) >>
  fs[arithmeticTheory.ADD_ASSOC] >> qexistsl [`Gf`, `tnf`] >>
  reverse conj_tac
  >- (Cases_on `tr` >> gvs[Abbr `tn1`, op_taint_def]) >>
  irule for_inst_seq_ptr_cons_nonterminator >> conj_tac
  >- (Cases_on `tr` >> simp[mk_inst_def, is_terminator_def]) >>
  qexistsl [`G`, `tn1`, `t`] >> simp[] >> conj_tac
  >- (simp[Abbr `tn1`] >> irule pop_storage_store_transfer >>
      gvs[eval_operand_def]) >>
  Cases_on `tr` >> simp[Abbr `t`, step_inst_base_opcode_eqs, mk_inst_def,
    exec_write2_def, eval_operand_def] >> gvs[eval_operand_def]
QED

Theorem pop_storage_suffix_transfer:
  ALL_DISTINCT [x0;x3;x4;x5;x6] /\ ~ctx_has_dalloca ctx /\
  ~s.vs_call_ctx.cc_static /\ lookup_var x0 s = SOME n /\
  eval_operand hdr s = SOME slot /\ op_prov G hdr = NONE /\ op_taint tn hdr = {} /\
  hdr <> Var x3 /\ op_prov G (Var x0) = NONE /\ op_taint tn (Var x0) = {} ==>
  ?Gf tnf.
    (!k. inst_seq_ptr D 0 ctx fn PG G tn
      [mk_inst id SUB [Var x0; Lit 1w] [x3];
       mk_inst (id+1) (if tr then TSTORE else SSTORE) [hdr; Var x3] [];
       mk_inst (id+2) ADD [hdr; Lit 1w] [x4];
       mk_inst (id+3) MUL [Var x3; Lit esz] [x5];
       mk_inst (id+4) ADD [Var x4; Var x5] [x6]]
      (s with vs_inst_idx := k) Gf tnf) /\
    op_prov Gf (Var x6) = NONE /\ op_taint tnf (Var x6) = {} /\
    tnf.t_mem = tn.t_mem /\ tnf.t_imm = tn.t_imm /\
    tnf.t_stor = (if tr then tn.t_stor else key_update tn.t_stor slot {}) /\
    tnf.t_trans = (if tr then key_update tn.t_trans slot {} else tn.t_trans) /\
    (!v. ~MEM v [x3;x4;x5;x6] ==> FLOOKUP Gf v = FLOOKUP G v /\
         op_taint tnf (Var v) = op_taint tn (Var v))
Proof
  strip_tac >>
  qabbrev_tac `t = update_var x3 (n-1w) s` >>
  qabbrev_tac `G1 = DRESTRICT G (COMPL {x3})` >>
  qabbrev_tac `tn1 = tn with t_var := tn.t_var |+ (x3,{})` >>
  `?Gf tnf.
    (!k. inst_seq_ptr D 0 ctx fn PG G1 tn1
      [mk_inst (id+1) (if tr then TSTORE else SSTORE) [hdr; Var x3] [];
       mk_inst ((id+1)+1) ADD [hdr; Lit 1w] [x4];
       mk_inst ((id+1)+2) MUL [Var x3; Lit esz] [x5];
       mk_inst ((id+1)+3) ADD [Var x4; Var x5] [x6]]
      (t with vs_inst_idx := k) Gf tnf) /\
    op_prov Gf (Var x6) = NONE /\ op_taint tnf (Var x6) = {} /\
    tnf.t_mem = tn1.t_mem /\ tnf.t_imm = tn1.t_imm /\
    tnf.t_stor = (if tr then tn1.t_stor else key_update tn1.t_stor slot {}) /\
    tnf.t_trans = (if tr then key_update tn1.t_trans slot {} else tn1.t_trans) /\
    (!v. ~MEM v [x4;x5;x6] ==> FLOOKUP Gf v = FLOOKUP G1 v /\
         op_taint tnf (Var v) = op_taint tn1 (Var v))` by
    (irule pop_storage_store_address_transfer >>
     Cases_on `hdr` >>
     gvs[ALL_DISTINCT, Abbr `t`, Abbr `G1`, Abbr `tn1`, lookup_var_def,
         eval_operand_def, update_var_def, op_prov_def, op_taint_def,
         FLOOKUP_DRESTRICT, FLOOKUP_UPDATE]) >>
  fs[arithmeticTheory.ADD_ASSOC] >> qexistsl [`Gf`, `tnf`] >>
  reverse conj_tac
  >- (gvs[Abbr `G1`, Abbr `tn1`, FLOOKUP_DRESTRICT, op_taint_def] >>
      rpt strip_tac >> first_x_assum drule >> simp[FLOOKUP_UPDATE]) >>
  irule for_inst_seq_ptr_cons_nonterminator >> conj_tac
  >- simp[mk_inst_def, is_terminator_def] >>
  qexistsl [`G1`, `tn1`, `t`] >> simp[] >> conj_tac
  >- (irule pop_storage_binary_singleton >>
      gvs[Abbr `G1`, Abbr `tn1`, eval_operand_def, op_prov_def, op_taint_def]) >>
  simp[Abbr `t`, exprSimPopTheory.pop_step_SUB_lit]
QED

Theorem pop_storage_slice_transfer_nonempty:
  ALL_DISTINCT [x0;x1;x2;x3;x4;x5;x6] /\ ~ctx_has_dalloca ctx /\
  ~s.vs_call_ctx.cc_static /\
  eval_operand hdr s = SOME slot /\ op_prov G hdr = NONE /\ op_taint tn hdr = {} /\
  (!x. MEM x [x0;x1;x2;x3] ==> hdr <> Var x) /\
  n = (if tr then tload slot s else sload slot s) /\ n <> 0w /\
  key_taint (if tr then tn.t_trans else tn.t_stor) slot = {} ==>
  ?Gf tnf.
    inst_seq_ptr D 0 ctx fn PG G tn
      ([mk_inst id (if tr then TLOAD else SLOAD) [hdr] [x0];
        mk_inst (id+1) ISZERO [Var x0] [x1];
        mk_inst (id+2) ISZERO [Var x1] [x2];
        mk_inst (id+3) ASSERT [Var x2] []] ++
       [mk_inst (id+4) SUB [Var x0; Lit 1w] [x3];
        mk_inst ((id+4)+1) (if tr then TSTORE else SSTORE) [hdr; Var x3] [];
        mk_inst ((id+4)+2) ADD [hdr; Lit 1w] [x4];
        mk_inst ((id+4)+3) MUL [Var x3; Lit esz] [x5];
        mk_inst ((id+4)+4) ADD [Var x4; Var x5] [x6]]) s Gf tnf /\
    op_prov Gf (Var x6) = NONE /\ op_taint tnf (Var x6) = {} /\
    tnf.t_mem = tn.t_mem /\ tnf.t_imm = tn.t_imm /\
    tnf.t_stor = (if tr then tn.t_stor else key_update tn.t_stor slot {}) /\
    tnf.t_trans = (if tr then key_update tn.t_trans slot {} else tn.t_trans) /\
    (!v. ~MEM v [x0;x1;x2;x3;x4;x5;x6] ==> FLOOKUP Gf v = FLOOKUP G v /\
         op_taint tnf (Var v) = op_taint tn (Var v))
Proof
  strip_tac >>
  qmatch_goalsub_abbrev_tac `inst_seq_ptr D 0 ctx fn PG G tn (pre ++ suf) s` >>
  qabbrev_tac `t = update_var x2 1w (update_var x1 0w (update_var x0 n s))` >>
  qabbrev_tac `G1 = DRESTRICT (DRESTRICT (DRESTRICT G (COMPL {x0}))
                               (COMPL {x1})) (COMPL {x2})` >>
  qabbrev_tac `tn1 = tn with t_var := tn.t_var |+ (x0,{}) |+ (x1,{}) |+ (x2,{})` >>
  `?Gf tnf.
    (!k. inst_seq_ptr D 0 ctx fn PG G1 tn1 suf
      (t with vs_inst_idx := k) Gf tnf) /\
    op_prov Gf (Var x6) = NONE /\ op_taint tnf (Var x6) = {} /\
    tnf.t_mem = tn1.t_mem /\ tnf.t_imm = tn1.t_imm /\
    tnf.t_stor = (if tr then tn1.t_stor else key_update tn1.t_stor slot {}) /\
    tnf.t_trans = (if tr then key_update tn1.t_trans slot {} else tn1.t_trans) /\
    (!v. ~MEM v [x3;x4;x5;x6] ==> FLOOKUP Gf v = FLOOKUP G1 v /\
         op_taint tnf (Var v) = op_taint tn1 (Var v))` by
    (qunabbrev_tac `suf` >> irule pop_storage_suffix_transfer >>
     Cases_on `hdr` >>
     gvs[ALL_DISTINCT, Abbr `t`, Abbr `G1`, Abbr `tn1`, lookup_var_def,
         eval_operand_def, update_var_def, op_prov_def, op_taint_def,
         FLOOKUP_DRESTRICT, FLOOKUP_UPDATE] >> metis_tac[MEM]) >>
  qexistsl [`Gf`, `tnf`] >> reverse conj_tac
  >- (gvs[Abbr `G1`, Abbr `tn1`, FLOOKUP_DRESTRICT, op_taint_def] >>
      rpt strip_tac >> first_x_assum drule >> simp[FLOOKUP_UPDATE]) >>
  irule inst_seq_ptr_append >> conj_tac
  >- (Cases_on `tr` >> simp[Abbr `pre`, mk_inst_def, is_terminator_def]) >>
  qexistsl [`G1`, `t`, `tn1`] >> simp[] >> conj_tac
  >- (simp[Abbr `pre`, Abbr `t`, run_inst_seq_def, nested_pop_step_load,
        exprSimPopTheory.pop_step_ISZERO, exprSimPopTheory.pop_step_ASSERT,
        lookup_var_def, update_var_def, FLOOKUP_UPDATE, bool_to_word_def] >> gvs[]) >>
  simp[Abbr `pre`] >> irule pop_storage_prefix_transfer >>
  simp[Abbr `G1`, Abbr `tn1`]
QED
