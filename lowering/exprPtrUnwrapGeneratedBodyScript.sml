(* Compose the generated checked blocks without exposing individual edges. *)
Theory exprPtrUnwrapGeneratedBody
Ancestors
  exprPtrUnwrapGeneratedSource exprPtrUnwrapGeneratedDestination
  exprPtrUnwrapGeneratedStore exprPtrUnwrapFrames instSeqComposePtr
  slotCopyExecution copyExecution exprLoweringProps fragGasSeqPtr
  bodyPtrDefs ptrDiscipline venomState venomInst finite_map list

Theorem copy_generated_first_four:
  (load = SLOAD \/ load = TLOAD) /\
  eval_operand src s = SOME srcword /\
  eval_operand (Var (slot_copy_var cs 0)) s = SOME k /\
  op_taint tn src = {} /\ op_taint tn (Var (slot_copy_var cs 0)) = {} /\
  root <> slot_copy_var cs 2 /\ root <> slot_copy_var cs 3 /\
  root <> slot_copy_var cs 4 /\ root <> slot_copy_var cs 5 /\
  k * 32w = n2w off /\ lookup_var root s = SOME a /\
  ptr_covers G tn root s capacity /\ off < capacity /\ off+32 <= capacity /\
  w2n a+off < dimword(:256) /\ allocas_from lo s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?Gf tnf t.
    t = update_var (slot_copy_var cs 5) (a+n2w off)
      (update_var (slot_copy_var cs 4) (n2w off)
        (update_var (slot_copy_var cs 3) (slot_copy_word load s (srcword+k))
          (update_var (slot_copy_var cs 2) (srcword+k) s))) /\
    run_inst_seq (TAKE 4 (slot_copy_body_insts cs src (Var root) load)) s = OK t /\
    (!ix. inst_seq_ptr D lo ctx fn PG G tn
      (TAKE 4 (slot_copy_body_insts cs src (Var root) load))
      (s with vs_inst_idx := ix) Gf tnf) /\
    ptr_covers Gf tnf (slot_copy_var cs 5) t 32 /\
    op_taint tnf (Var (slot_copy_var cs 3)) =
      key_taint (if load=SLOAD then tn.t_stor else tn.t_trans) (srcword+k) /\
    tnf.t_mem = tn.t_mem /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    (!p. p <> slot_copy_var cs 2 /\ p <> slot_copy_var cs 3 /\
         p <> slot_copy_var cs 4 /\ p <> slot_copy_var cs 5 ==>
      FLOOKUP Gf p = FLOOKUP G p /\ op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  rev_drule_all copy_generated_source_segment >>
  disch_then (qspecl_then [`fn`, `PG`, `G`, `D`] strip_assume_tac) >>
  rename1 `run_inst_seq _ s = OK u` >>
  rename1 `inst_seq_ptr D lo ctx fn PG G tn _ _ G1 tn1` >>
  `eval_operand (Var (slot_copy_var cs 0)) u = SOME k /\
   op_taint tn1 (Var (slot_copy_var cs 0)) = {} /\
   lookup_var root u = SOME a /\ ptr_covers G1 tn1 root u capacity /\
   allocas_from lo u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u)` by
    (`ptr_covers G1 tn1 root u capacity` by
       (irule (iffRL copy_ptr_covers_transport) >>
        qexistsl [`G`, `s`, `tn`] >>
        fs[lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
     fs[slot_copy_var_distinct, eval_operand_def, lookup_var_def,
        update_var_def, FLOOKUP_UPDATE, allocas_from_def, allocas_below_fmp_def] >>
     metis_tac[]) >>
  drule_all copy_generated_destination_segment >>
  disch_then (qspecl_then [`fn`, `PG`, `D`] strip_assume_tac) >>
  rename1 `run_inst_seq _ u = OK t` >>
  rename1 `inst_seq_ptr D lo ctx fn PG G1 tn1 _ _ G2 tn2` >>
  qmatch_asmsub_abbrev_tac `run_inst_seq xs s` >>
  qmatch_asmsub_abbrev_tac `run_inst_seq ys u` >>
  `TAKE 4 (slot_copy_body_insts cs src (Var root) load) = xs ++ ys` by
    simp[Abbr `xs`, Abbr `ys`, slot_copy_body_insts_def, TAKE_def] >>
  qexistsl [`G2`, `tn2`, `t`] >>
  conj_tac >- simp[] >>
  conj_tac
  >- (rev_drule run_inst_seq_append >> disch_then (qspec_then `ys` mp_tac) >>
      asm_rewrite_tac[]) >>
  conj_tac
  >- (asm_rewrite_tac[] >> irule inst_seq_ptr_uniform_append >>
      reverse conj_tac
      >- (fs[Abbr `xs`, mk_inst_def, is_terminator_def]) >>
      qexistsl [`G1`, `u`, `tn1`] >> asm_rewrite_tac[]) >>
  simp[slot_copy_var_distinct] >> metis_tac[]
QED

Theorem copy_generated_body_segment:
  (load = SLOAD \/ load = TLOAD) /\
  eval_operand src s = SOME srcword /\
  eval_operand (Var (slot_copy_var cs 0)) s = SOME k /\
  op_taint tn src = {} /\ op_taint tn (Var (slot_copy_var cs 0)) = {} /\
  root <> slot_copy_var cs 2 /\ root <> slot_copy_var cs 3 /\
  root <> slot_copy_var cs 4 /\ root <> slot_copy_var cs 5 /\
  k * 32w = n2w off /\ lookup_var root s = SOME a /\
  ptr_covers G tn root s capacity /\ off < capacity /\ off + 32 <= capacity /\
  w2n a + off < dimword(:256) /\ allocas_from lo s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?Gf tnf t.
    run_inst_seq (TAKE 7 (slot_copy_body_insts cs src (Var root) load)) s = OK t /\
    (!ix. inst_seq_ptr D lo ctx fn PG G tn
      (TAKE 7 (slot_copy_body_insts cs src (Var root) load))
      (s with vs_inst_idx := ix) Gf tnf) /\
    t = update_var (slot_copy_var cs 0) (k+1w)
      (update_var (slot_copy_var cs 6) (k+1w)
        (mstore (w2n (a+n2w off)) (slot_copy_word load s (srcword+k))
          (update_var (slot_copy_var cs 5) (a+n2w off)
            (update_var (slot_copy_var cs 4) (n2w off)
              (update_var (slot_copy_var cs 3) (slot_copy_word load s (srcword+k))
                (update_var (slot_copy_var cs 2) (srcword+k) s)))))) /\
    op_taint tnf (Var (slot_copy_var cs 0)) = {} /\
    tnf.t_mem =
      (tn.t_mem DIFF {j | w2n (a+n2w off) <= j /\ j < w2n (a+n2w off) + 32}) UNION
      {w2n (a+n2w off) + j | j IN
        key_taint (if load = SLOAD then tn.t_stor else tn.t_trans) (srcword+k)} /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    (!p. p <> slot_copy_var cs 2 /\ p <> slot_copy_var cs 3 /\
         p <> slot_copy_var cs 4 /\ p <> slot_copy_var cs 5 /\
         p <> slot_copy_var cs 0 /\ p <> slot_copy_var cs 6 ==>
      FLOOKUP Gf p = FLOOKUP G p /\ op_taint tnf (Var p) = op_taint tn (Var p)) /\
    (!p c. p <> slot_copy_var cs 2 /\ p <> slot_copy_var cs 3 /\
      p <> slot_copy_var cs 4 /\ p <> slot_copy_var cs 5 /\
      p <> slot_copy_var cs 0 /\ p <> slot_copy_var cs 6 /\
      ptr_covers G tn p s c ==> ptr_covers Gf tnf p t c)
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
  rev_drule_all copy_generated_first_four >>
  disch_then (qspecl_then [`fn`, `PG`, `D`] strip_assume_tac) >>
  rename1 `run_inst_seq _ s = OK u` >>
  rename1 `inst_seq_ptr D lo ctx fn PG G tn _ _ G1 tn1` >>
  `eval_operand (Var (slot_copy_var cs 5)) u = SOME (a+n2w off) /\
   eval_operand (Var (slot_copy_var cs 3)) u = SOME (slot_copy_word load s (srcword+k)) /\
   eval_operand (Var (slot_copy_var cs 0)) u = SOME k /\
   op_taint tn1 (Var (slot_copy_var cs 0)) = {} /\
   allocas_from lo u /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u)` by
    (fs[slot_copy_var_distinct, eval_operand_def, lookup_var_def,
        update_var_def, FLOOKUP_UPDATE, allocas_from_def, allocas_below_fmp_def] >>
     metis_tac[]) >>
  drule_all copy_generated_store_segment >>
  disch_then (qspecl_then [`fn`, `PG`, `D`] strip_assume_tac) >>
  rename1 `run_inst_seq _ u = OK t` >>
  rename1 `inst_seq_ptr D lo ctx fn PG G1 tn1 _ _ G2 tn2` >>
  qmatch_asmsub_abbrev_tac `run_inst_seq xs s` >>
  qmatch_asmsub_abbrev_tac `run_inst_seq ys u` >>
  `TAKE 7 (slot_copy_body_insts cs src (Var root) load) = xs ++ ys` by
    simp[Abbr `xs`, Abbr `ys`, slot_copy_body_insts_def, TAKE_def] >>
  qexistsl [`G2`, `tn2`, `t`] >> conj_tac
  >- (rev_drule run_inst_seq_append >> disch_then (qspec_then `ys` mp_tac) >>
      asm_rewrite_tac[]) >>
  conj_tac
  >- (asm_rewrite_tac[] >> irule inst_seq_ptr_uniform_append >>
      reverse conj_tac
      >- fs[Abbr `xs`, slot_copy_body_insts_def, TAKE_def, mk_inst_def, is_terminator_def] >>
      qexistsl [`G1`, `u`, `tn1`] >> asm_rewrite_tac[]) >>
  `!p. p <> slot_copy_var cs 2 /\ p <> slot_copy_var cs 3 /\
       p <> slot_copy_var cs 4 /\ p <> slot_copy_var cs 5 /\
       p <> slot_copy_var cs 0 /\ p <> slot_copy_var cs 6 ==>
       FLOOKUP G2 p = FLOOKUP G p /\ op_taint tn2 (Var p) = op_taint tn (Var p)` by
    metis_tac[] >>
  simp[] >> conj_tac
  >- (fs[allocas_from_def, mstore_def, update_var_def] >> metis_tac[]) >>
  reverse conj_tac
  >- (rpt strip_tac >> irule (iffRL copy_ptr_covers_transport) >>
      qexistsl [`G`, `s`, `tn`] >>
      fs[lookup_var_def, update_var_def, mstore_def, FLOOKUP_UPDATE]) >>
  fs[allocas_below_fmp_def, update_var_def, mstore_def] >> metis_tac[]
QED
