(* Counted dynamic-array length guard and header setup. *)
Theory annAssignTypedCopyDynamicHeaderPtr
Ancestors
  bodyPtrBopScalarSeq annAssignPtrLength annAssignPtrStore
  typedMemoryCopy typedNormalizeDynarray fragGasPathPtr bodyPtrDefs
  venomState venomExecSemantics venomInst ptrDiscipline finite_map
  words arithmetic list pred_set emitHelper compileEnv fragExec exprLoweringProps

Theorem annassign_dynamic_capacity_guard_counted:
  !s fn bb id len too_long ok n cap tn G ctx D PG.
    ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    isPREFIX
      [mk_inst id GT [Var len;Lit (n2w cap)] [too_long];
       mk_inst (id+1) ISZERO [Var too_long] [ok];
       mk_inst (id+2) ASSERT [Var ok] []]
      (DROP s.vs_inst_idx bb.bb_instructions) /\
    lookup_var len s = SOME (n2w n) /\ n <= cap /\ cap < dimword (:256) /\
    op_prov G (Var len) = NONE /\ op_taint tn (Var len) = {} /\
    ALL_DISTINCT [len;too_long;ok] ==>
    ?H tm t.
      gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t) /\
      t = (update_var ok 1w (update_var too_long 0w s)
        with vs_inst_idx := s.vs_inst_idx+3) /\
      tm.t_mem = tn.t_mem /\ tm.t_stor = tn.t_stor /\
      tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
      (!x. x <> too_long /\ x <> ok ==>
        FLOOKUP H x = FLOOKUP G x /\
        op_taint tm (Var x) = op_taint tn (Var x))
Proof
  rpt gen_tac >> strip_tac >>
  qabbrev_tac `code =
    [mk_inst id GT [Var len;Lit (n2w cap)] [too_long];
     mk_inst (id+1) ISZERO [Var too_long] [ok];
     mk_inst (id+2) ASSERT [Var ok] []]` >>
  `run_inst_seq code s = OK (update_var ok 1w (update_var too_long 0w s))` by
    (simp[Abbr `code`, run_inst_seq_def, step_inst_base_opcode_eqs,
      mk_inst_def, exec_pure2_def, exec_pure1_def, eval_operand_def,
      lookup_var_def, update_var_def, FLOOKUP_UPDATE, w2n_n2w,
      bool_to_word_def] >>
     `n < dimword (:256)` by decide_tac >>
     simp[LESS_MOD] >> `~(cap < n)` by decide_tac >> simp[]) >>
  `bop_scalar_seq (COMPL {too_long;ok}) {Var len;Lit (n2w cap)} code
    {Var ok;Var too_long;Var len;Lit (n2w cap)}` by
    (simp[Abbr `code`, Once bop_scalar_seq_def] >> disj1_tac >>
     qexistsl_tac [`id`,`GT`,`[Var len;Lit (n2w cap)]`,`too_long`] >> simp[] >>
     simp[Once bop_scalar_seq_def] >> disj1_tac >>
     qexistsl_tac [`id+1`,`ISZERO`,`[Var too_long]`,`ok`] >> simp[] >>
     simp[Once bop_scalar_seq_def] >> disj2_tac >>
     qexistsl_tac [`id+2`,`ASSERT`,`Var ok`] >> simp[]) >>
  `!op. op IN {Var len;Lit (n2w cap)} ==>
    op_prov G op = NONE /\ op_taint tn op = {}` by
    (rpt strip_tac >> gvs[op_prov_def, op_taint_def]) >>
  drule_all bop_scalar_seq_path >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  qexistsl_tac [`G'`,`tn'`,
    `update_var ok 1w (update_var too_long 0w s) with vs_inst_idx := s.vs_inst_idx+3`] >>
  gvs[Abbr `code`, op_taint_def] >> metis_tac[]
QED
