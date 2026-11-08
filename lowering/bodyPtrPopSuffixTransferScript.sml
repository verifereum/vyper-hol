Theory bodyPtrPopSuffixTransfer
Ancestors
  bodyPtrPopScalarTransfer stmtAppendStorageRunPtr instSeqComposePtr
  fragGasSeqPtr ptrSafeRun ptrDiscipline venomExecSemantics venomInst venomState
  codegenRel contextCodegenRel finite_map pred_set list

Theorem pop_root_store_transfer:
  ~ctx_has_dalloca ctx /\ ~s.vs_call_ctx.cc_static /\
  eval_operand v s = SOME w /\ op_taint tn v = {} ==>
  inst_seq_ptr D 0 ctx fn PG G tn
    [mk_inst id (if tr then TSTORE else SSTORE) [Lit slot;v] []] s G
    (if tr then tn with t_trans := key_update tn.t_trans slot {}
     else tn with t_stor := key_update tn.t_stor slot {})
Proof
  strip_tac >>
  qabbrev_tac `t = if tr then tstore slot w s else sstore slot w s` >>
  `step_inst_base (mk_inst id (if tr then TSTORE else SSTORE) [Lit slot;v] []) s = OK t` by
    (Cases_on `tr` >>
     simp[step_inst_base_def, mk_inst_def, eval_operands_def,
          eval_operand_def, exec_write2_def, Abbr `t`]) >>
  `t.vs_allocas = s.vs_allocas /\ t.vs_fmp = s.vs_fmp /\
   t.vs_requests = s.vs_requests` by
    (Cases_on `tr` >> simp[Abbr `t`, sstore_def, tstore_def]) >>
  `ptr_inst_ok D 0 0 ctx fn G tn
     (mk_inst id (if tr then TSTORE else SSTORE) [Lit slot;v] []) s` by
    (irule append_scalar_inst_check >>
     conj_tac >- (rpt strip_tac >> gvs[] >> simp[op_taint_def]) >>
     simp[] >> Cases_on `tr` >> simp[]) >>
  simp[inst_seq_ptr_def, scalar_void_prov] >>
  sym_tac >> irule scalar_storage_store_taint >> simp[eval_operand_def]
QED

Theorem pop_scalar_cons[local]:
  ~is_terminator i.inst_opcode /\ step_inst_base i s = OK t /\
  inst_seq_ptr D 0 ctx fn PG G tn [i] s G1 tn1 /\
  (!k. inst_seq_ptr D 0 ctx fn PG G1 tn1 rest
         (t with vs_inst_idx := k) G2 tn2) ==>
  inst_seq_ptr D 0 ctx fn PG G tn (i::rest) s G2 tn2
Proof
  strip_tac >>
  qpat_x_assum `inst_seq_ptr _ _ _ _ _ _ _ [_] _ _ _` mp_tac >>
  simp[inst_seq_ptr_def] >> strip_tac >>
  simp[Once inst_seq_ptr_def] >>
  first_x_assum (qspec_then `SUC s.vs_inst_idx` mp_tac) >> simp[]
QED

Theorem pop_binary_cons[local]:
  (opc = SUB /\ z = x-y \/ opc = ADD /\ z = x+y \/ opc = MUL /\ z = x*y) /\
  eval_operand a s = SOME x /\ eval_operand b s = SOME y /\
  op_prov G a = NONE /\ op_prov G b = NONE /\
  op_taint tn a = {} /\ op_taint tn b = {} /\ ~ctx_has_dalloca ctx /\
  (!k. inst_seq_ptr D 0 ctx fn PG (DRESTRICT G (COMPL {out}))
       (tn with t_var := tn.t_var |+ (out,{})) rest
       ((update_var out z s) with vs_inst_idx := k) Gf tnf) ==>
  inst_seq_ptr D 0 ctx fn PG G tn (mk_inst id opc [a;b] [out]::rest) s Gf tnf
Proof
  strip_tac >>
  `step_inst_base (mk_inst id opc [a;b] [out]) s = OK (update_var out z s) /\
   ptr_inst_ok D 0 0 ctx fn G tn (mk_inst id opc [a;b] [out]) s` by
    (irule pop_scalar_binary_step >> metis_tac[]) >>
  `step_prov PG G (mk_inst id opc [a;b] [out]) (update_var out z s) =
     DRESTRICT G (COMPL {out}) /\
   step_taint (mk_inst id opc [a;b] [out]) s (update_var out z s) tn =
     tn with t_var := tn.t_var |+ (out,{})` by
    (irule pop_scalar_binary_ghost >> metis_tac[]) >>
  simp[Once inst_seq_ptr_def] >>
  first_x_assum (qspec_then `SUC s.vs_inst_idx` mp_tac) >> gvs[]
QED

Theorem pop_root_address_transfer:
  ALL_DISTINCT [x3;x4;x5;x6] /\ ~ctx_has_dalloca ctx /\
  lookup_var x3 s = SOME n /\ op_prov G (Var x3) = NONE /\
  op_taint tn (Var x3) = {} ==>
  ?Gf tnf.
    (!k. inst_seq_ptr D 0 ctx fn PG G tn
      [mk_inst id ADD [Lit slot; Lit 1w] [x4];
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
  qexistsl_tac
    [`DRESTRICT (DRESTRICT (DRESTRICT G (COMPL {x4})) (COMPL {x5})) (COMPL {x6})`,
     `tn with t_var := tn.t_var |+ (x4,{}) |+ (x5,{}) |+ (x6,{})`] >>
  reverse conj_tac
  >- (gvs[ALL_DISTINCT, op_prov_def, op_taint_def, FLOOKUP_DRESTRICT,
           FLOOKUP_UPDATE] >> rpt strip_tac >> simp[]) >>
  gen_tac >> irule pop_binary_cons >>
  simp[op_prov_def, op_taint_def, eval_operand_def] >> gen_tac >>
  irule pop_binary_cons >>
  gvs[ALL_DISTINCT, op_prov_def, op_taint_def, FLOOKUP_DRESTRICT,
      FLOOKUP_UPDATE, eval_operand_def, lookup_var_def, update_var_def] >>
  gen_tac >> irule pop_binary_cons >>
  simp[op_prov_def, op_taint_def, FLOOKUP_DRESTRICT,
       FLOOKUP_UPDATE, eval_operand_def, lookup_var_def, update_var_def,
       inst_seq_ptr_def, DRESTRICT_DRESTRICT, AC INTER_ASSOC INTER_COMM]
QED

Theorem pop_root_store_address_transfer:
  ALL_DISTINCT [x3;x4;x5;x6] /\ ~ctx_has_dalloca ctx /\
  ~s.vs_call_ctx.cc_static /\ lookup_var x3 s = SOME n /\
  op_prov G (Var x3) = NONE /\ op_taint tn (Var x3) = {} ==>
  ?Gf tnf.
    (!k. inst_seq_ptr D 0 ctx fn PG G tn
      [mk_inst id (if tr then TSTORE else SSTORE) [Lit slot; Var x3] [];
       mk_inst (id+1) ADD [Lit slot; Lit 1w] [x4];
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
      [mk_inst (id+1) ADD [Lit slot; Lit 1w] [x4];
       mk_inst ((id+1)+1) MUL [Var x3; Lit esz] [x5];
       mk_inst ((id+1)+2) ADD [Var x4; Var x5] [x6]]
       (t with vs_inst_idx := k) Gf tnf) /\
    op_prov Gf (Var x6) = NONE /\ op_taint tnf (Var x6) = {} /\
    tnf.t_mem = tn1.t_mem /\ tnf.t_stor = tn1.t_stor /\
    tnf.t_trans = tn1.t_trans /\ tnf.t_imm = tn1.t_imm /\
    (!v. ~MEM v [x4;x5;x6] ==> FLOOKUP Gf v = FLOOKUP G v /\
         op_taint tnf (Var v) = op_taint tn1 (Var v))` by
    (irule pop_root_address_transfer >>
     Cases_on `tr` >> gvs[Abbr `t`, Abbr `tn1`, sstore_def, tstore_def,
       lookup_var_def, op_taint_def, arithmeticTheory.ADD_ASSOC]) >>
  fs[arithmeticTheory.ADD_ASSOC] >>
  qexistsl_tac [`Gf`, `tnf`] >> reverse conj_tac
  >- (Cases_on `tr` >> gvs[Abbr `tn1`, op_taint_def]) >>
  gen_tac >> irule pop_scalar_cons >> conj_tac
  >- (Cases_on `tr` >> simp[mk_inst_def, is_terminator_def]) >>
  qexistsl_tac [`G`, `t with vs_inst_idx := k`, `tn1`] >> simp[] >>
  conj_tac
  >- (Cases_on `tr` >> gvs[Abbr `t`, step_inst_base_def, mk_inst_def,
       exec_write2_def, eval_operands_def, eval_operand_def, sstore_def, tstore_def]) >>
  simp[Abbr `tn1`, GSYM mk_inst_def] >> irule pop_root_store_transfer >>
  gvs[eval_operand_def, lookup_var_def]
QED

Theorem pop_root_suffix_transfer:
  ALL_DISTINCT [x0;x3;x4;x5;x6] /\ ~ctx_has_dalloca ctx /\
  ~s.vs_call_ctx.cc_static /\ lookup_var x0 s = SOME n /\
  op_prov G (Var x0) = NONE /\ op_taint tn (Var x0) = {} ==>
  ?Gf tnf.
    (!k. inst_seq_ptr D 0 ctx fn PG G tn
      [mk_inst id SUB [Var x0; Lit 1w] [x3];
       mk_inst (id+1) (if tr then TSTORE else SSTORE) [Lit slot; Var x3] [];
       mk_inst (id+2) ADD [Lit slot; Lit 1w] [x4];
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
      [mk_inst (id+1) (if tr then TSTORE else SSTORE) [Lit slot; Var x3] [];
       mk_inst ((id+1)+1) ADD [Lit slot; Lit 1w] [x4];
       mk_inst ((id+1)+2) MUL [Var x3; Lit esz] [x5];
       mk_inst ((id+1)+3) ADD [Var x4; Var x5] [x6]]
      (t with vs_inst_idx := k) Gf tnf) /\
    op_prov Gf (Var x6) = NONE /\ op_taint tnf (Var x6) = {} /\
    tnf.t_mem = tn1.t_mem /\ tnf.t_imm = tn1.t_imm /\
    tnf.t_stor = (if tr then tn1.t_stor else key_update tn1.t_stor slot {}) /\
    tnf.t_trans = (if tr then key_update tn1.t_trans slot {} else tn1.t_trans) /\
    (!v. ~MEM v [x4;x5;x6] ==> FLOOKUP Gf v = FLOOKUP G1 v /\
         op_taint tnf (Var v) = op_taint tn1 (Var v))` by
    (irule pop_root_store_address_transfer >>
     gvs[ALL_DISTINCT, Abbr `t`, Abbr `G1`, Abbr `tn1`, lookup_var_def,
         update_var_def, op_prov_def, op_taint_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE]) >>
  fs[arithmeticTheory.ADD_ASSOC] >> qexistsl_tac [`Gf`, `tnf`] >>
  reverse conj_tac
  >- (gvs[Abbr `G1`, Abbr `tn1`, FLOOKUP_DRESTRICT, op_taint_def] >>
      rpt strip_tac >> first_x_assum drule >> simp[FLOOKUP_UPDATE]) >>
  gen_tac >> irule pop_binary_cons >>
  gvs[eval_operand_def, lookup_var_def, op_prov_def, op_taint_def] >>
  gen_tac >> simp[GSYM lookup_var_def, GSYM op_prov_def, GSYM op_taint_def,
                  Abbr `t`, Abbr `G1`, Abbr `tn1`, update_var_def] >>
  qpat_x_assum `!k. inst_seq_ptr _ _ _ _ _ _ _ _ _ _ _`
    (qspec_then `k'` mp_tac) >> simp[update_var_def]
QED
