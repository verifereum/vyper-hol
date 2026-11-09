Theory bodyPtrPopSliceTransfer
Ancestors
  bodyPtrPopSuffixTransfer bodyPtrPopRootTransfer exprSimPop instSeqComposePtr
  fragGasSeqPtr venomExecSemantics venomInst venomState ptrSafeRun ptrDiscipline
  codegenRel contextCodegenRel finite_map pred_set list exprLoweringProps instIdxIndep

Theorem pop_root_load_step[local]:
  step_inst_base (mk_inst id (if tr then TLOAD else SLOAD) [Lit slot] [x0]) s =
  OK (update_var x0 (if tr then tload slot s else sload slot s) s)
Proof
  Cases_on `tr` >> simp_tac std_ss [] >>
  simp[step_inst_base_opcode_eqs, mk_inst_def] >>
  simp[exec_read1_def, eval_operand_def]
QED

Theorem pop_root_prefix_run:
  n = (if tr then tload slot s else sload slot s) /\ n <> 0w ==>
  run_inst_seq
    [mk_inst id (if tr then TLOAD else SLOAD) [Lit slot] [x0];
     mk_inst (id+1) ISZERO [Var x0] [x1];
     mk_inst (id+2) ISZERO [Var x1] [x2];
     mk_inst (id+3) ASSERT [Var x2] []] s =
    OK (update_var x2 1w (update_var x1 0w (update_var x0 n s)))
Proof
  strip_tac >>
  simp[run_inst_seq_def, pop_root_load_step, pop_step_ISZERO, pop_step_ASSERT,
       lookup_var_def, update_var_def, FLOOKUP_UPDATE, bool_to_word_def,
       arithmeticTheory.ADD_ASSOC] >> gvs[]
QED

Theorem pop_root_slice_transfer_nonempty:
  ALL_DISTINCT [x0;x1;x2;x3;x4;x5;x6] /\ ~ctx_has_dalloca ctx /\
  ~s.vs_call_ctx.cc_static /\
  n = (if tr then tload slot s else sload slot s) /\ n <> 0w /\
  key_taint (if tr then tn.t_trans else tn.t_stor) slot = {} ==>
  ?Gf tnf.
    inst_seq_ptr D 0 ctx fn PG G tn
      ([mk_inst id (if tr then TLOAD else SLOAD) [Lit slot] [x0];
        mk_inst (id+1) ISZERO [Var x0] [x1];
        mk_inst (id+2) ISZERO [Var x1] [x2];
        mk_inst (id+3) ASSERT [Var x2] []] ++
       [mk_inst (id+4) SUB [Var x0; Lit 1w] [x3];
        mk_inst ((id+4)+1) (if tr then TSTORE else SSTORE) [Lit slot; Var x3] [];
        mk_inst ((id+4)+2) ADD [Lit slot; Lit 1w] [x4];
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
    (qunabbrev_tac `suf` >> irule pop_root_suffix_transfer >>
     gvs[ALL_DISTINCT, Abbr `t`, Abbr `G1`, Abbr `tn1`, lookup_var_def,
         update_var_def, op_prov_def, op_taint_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE]) >>
  qexistsl_tac [`Gf`, `tnf`] >> reverse conj_tac
  >- (gvs[Abbr `G1`, Abbr `tn1`, FLOOKUP_DRESTRICT, op_taint_def] >>
      rpt strip_tac >> first_x_assum drule >> simp[FLOOKUP_UPDATE]) >>
  irule inst_seq_ptr_append >> conj_tac
  >- (Cases_on `tr` >> simp[Abbr `pre`, mk_inst_def, is_terminator_def]) >>
  qexistsl_tac [`G1`, `t`, `tn1`] >> simp[] >> conj_tac
  >- (simp[Abbr `pre`, Abbr `t`] >> irule pop_root_prefix_run >> gvs[]) >>
  simp[Abbr `pre`] >> irule pop_root_prefix_transfer >> simp[Abbr `G1`, Abbr `tn1`]
QED

Theorem pop_root_prefix_run_empty:
  (if tr then tload slot s else sload slot s) = 0w ==>
  ?a t. run_inst_seq
    [mk_inst id (if tr then TLOAD else SLOAD) [Lit slot] [x0];
     mk_inst (id+1) ISZERO [Var x0] [x1];
     mk_inst (id+2) ISZERO [Var x1] [x2];
     mk_inst (id+3) ASSERT [Var x2] []] s = Abort a t
Proof
  strip_tac >>
  simp[run_inst_seq_def, pop_root_load_step, pop_step_ISZERO, pop_step_ASSERT,
       lookup_var_def, update_var_def, FLOOKUP_UPDATE, bool_to_word_def]
QED

(* An empty header aborts before any suffix check, even in static calls. *)
Theorem pop_root_slice_transfer_empty:
  ~ctx_has_dalloca ctx /\
  (if tr then tload slot s else sload slot s) = 0w /\
  key_taint (if tr then tn.t_trans else tn.t_stor) slot = {} /\
  Gf = DRESTRICT (DRESTRICT (DRESTRICT G (COMPL {x0})) (COMPL {x1})) (COMPL {x2}) /\
  tnf = (tn with t_var := tn.t_var |+ (x0,{}) |+ (x1,{}) |+ (x2,{})) ==>
  inst_seq_ptr D 0 ctx fn PG G tn
    ([mk_inst id (if tr then TLOAD else SLOAD) [Lit slot] [x0];
      mk_inst (id+1) ISZERO [Var x0] [x1];
      mk_inst (id+2) ISZERO [Var x1] [x2];
      mk_inst (id+3) ASSERT [Var x2] []] ++ rest) s Gf tnf
Proof
  strip_tac >> irule inst_seq_ptr_abort_append >> conj_tac
  >- (irule pop_root_prefix_run_empty >> simp[]) >>
  conj_tac >- (Cases_on `tr` >> simp[mk_inst_def, is_terminator_def]) >>
  irule pop_root_prefix_transfer >> simp[]
QED
