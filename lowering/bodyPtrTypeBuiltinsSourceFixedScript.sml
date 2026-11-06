(* Fixed-run source prefix: the endpoint is supplied, never existential. *)
Theory bodyPtrTypeBuiltinsSourceFixed
Ancestors
  bodyPtrTypeBuiltinsSourceCompile bodyPtrTypeBuiltinsSourcePrefix
  typedCopyPtr typedCopyLoopHeaderPtr fragGasSeqPtr ghostPcTransportPtr
  instIdxIndep fragExec exprLoweringProps venomInstProofs venomState
  venomExecSemantics venomInst finite_map ptrDiscipline emitHelperProps bodyPtrDefs

Theorem bytestring_source_run_endpoint:
  src <> len /\ lookup_var src s = SOME a /\
  run_inst_seq [mk_inst i MLOAD [Var src] [len];
                mk_inst j ADD [Var src;Lit 32w] [dp]] s = OK t ==>
  t = update_var dp (a+32w) (update_var len (mload (w2n a) s) s)
Proof
  strip_tac >>
  `eval_operand (Var src) s = SOME a` by simp[eval_operand_def] >>
  `step_inst_base (mk_inst i MLOAD [Var src] [len]) s =
     OK (update_var len (mload (w2n a) s) s)` by simp[step_MLOAD] >>
  `eval_operand (Var src) (update_var len (mload (w2n a) s) s) = SOME a` by
    fs[eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  `eval_operand (Lit 32w) (update_var len (mload (w2n a) s) s) = SOME 32w` by
    simp[eval_operand_def] >>
  `step_inst_base (mk_inst j ADD [Var src;Lit 32w] [dp])
      (update_var len (mload (w2n a) s) s) =
    OK (update_var dp (a+32w) (update_var len (mload (w2n a) s) s))` by
    (irule step_ADD >> simp[]) >>
  qpat_x_assum `run_inst_seq _ _ = _` mp_tac >> simp[run_inst_seq_def]
QED

Theorem bytestring_source_uniform_checks:
  !D ctx fn PG G tn s src len dp i j a capacity t.
    ALL_DISTINCT [src;len;dp] /\ lookup_var src s = SOME a /\
    ptr_covers G tn src s capacity /\ 32 <= capacity /\
    ~ctx_has_dalloca ctx /\
    run_inst_seq [mk_inst i MLOAD [Var src] [len];
                  mk_inst j ADD [Var src;Lit 32w] [dp]] s = OK t ==>
    ?H th.
      (!k. inst_seq_ptr D 0 ctx fn PG G tn
        [mk_inst i MLOAD [Var src] [len];
         mk_inst j ADD [Var src;Lit 32w] [dp]]
        (s with vs_inst_idx := k) H th) /\
      H = step_prov PG
        (step_prov PG G (mk_inst i MLOAD [Var src] [len])
          (update_var len (mload (w2n a) s) s))
        (mk_inst j ADD [Var src;Lit 32w] [dp]) t /\
      th = step_taint (mk_inst j ADD [Var src;Lit 32w] [dp])
        (update_var len (mload (w2n a) s) s) t
        (step_taint (mk_inst i MLOAD [Var src] [len]) s
          (update_var len (mload (w2n a) s) s) tn)
Proof
  rpt gen_tac >> strip_tac >>
  `src <> len` by fs[] >>
  drule_all bytestring_source_run_endpoint >> strip_tac >>
  qmatch_goalsub_abbrev_tac `step_prov PG G _ u` >>
  qabbrev_tac `G1 = step_prov PG G (mk_inst i MLOAD [Var src] [len]) u` >>
  qabbrev_tac `tn1 = step_taint (mk_inst i MLOAD [Var src] [len]) s u tn` >>
  `op_taint tn1 (Var src) = {}` by
    (simp[Abbr `tn1`, Abbr `u`, bodyPtrTypeBuiltinsLoadTheory.mload_ambient_frame] >>
     fs[ptr_covers_def]) >>
  qexistsl_tac [`step_prov PG G1 (mk_inst j ADD [Var src;Lit 32w] [dp]) t`,
    `step_taint (mk_inst j ADD [Var src;Lit 32w] [dp]) u t tn1`] >>
  reverse conj_tac >- simp[Abbr `G1`, Abbr `tn1`] >>
  gen_tac >>
  `step_inst_base (mk_inst i MLOAD [Var src] [len]) (s with vs_inst_idx := k) =
     OK (u with vs_inst_idx := k)` by
    (`step_inst_base (mk_inst i MLOAD [Var src] [len]) (s with vs_inst_idx := k) =
       OK (update_var len (mload (w2n a) (s with vs_inst_idx := k))
         (s with vs_inst_idx := k))` by
       (irule step_MLOAD >> fs[eval_operand_def, lookup_var_def]) >>
     gvs[Abbr `u`, update_var_def, mload_def]) >>
  `step_inst_base (mk_inst j ADD [Var src;Lit 32w] [dp])
     (u with vs_inst_idx := SUC k) =
     OK (t with vs_inst_idx := SUC k)` by
    (`step_inst_base (mk_inst j ADD [Var src;Lit 32w] [dp])
        (u with vs_inst_idx := SUC k) =
       OK (update_var dp (a+32w) (u with vs_inst_idx := SUC k))` by
       (irule step_ADD >>
        fs[Abbr `u`, eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
     simp[update_var_def]) >>
  simp[inst_seq_ptr_def, Abbr `G1`, Abbr `tn1`] >>
  conj_tac
  >- (irule ptr_inst_ok_mload >> simp[eval_operand_def] >>
      fs[ptr_covers_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS]) >>
  irule ptr_inst_ok_copy_len_binop >>
  simp[op_taint_def]
QED
