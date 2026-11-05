(* Seven straight-line instructions of a storage/transient copy body. *)
Theory exprPtrUnwrapBodySegment
Ancestors
  exprPtrUnwrapFirstFour exprPtrUnwrapStoreIncrement exprPtrUnwrapSeq
  exprPtrUnwrapFrames ghostPcTransportPtr slotCopyExecution fragGasSeqPtr
  fragExec bodyPtrDefs ptrDiscipline ptrSafeRun venomExecSemantics venomInst
  venomState finite_map exprLoweringProps instIdxIndep list

Theorem copy_body_segment:
  (load = SLOAD \/ load = TLOAD) /\
  eval_operand src s = SOME srcword /\ eval_operand (Var ctr) s = SOME k /\
  op_taint tn src = {} /\ op_taint tn (Var ctr) = {} /\
  ctr <> addr /\ ctr <> valvar /\ ctr <> tmp /\ ctr <> out /\
  ctr <> next /\ root <> addr /\ root <> valvar /\ root <> tmp /\ root <> out /\
  valvar <> tmp /\ valvar <> out /\
  k * 32w = n2w off /\ lookup_var root s = SOME a /\
  ptr_covers G tn root s capacity /\ off < capacity /\ off + 32 <= capacity /\
  w2n a + off < dimword(:256) /\ allocas_from lo s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) ==>
  ?Gf tnf t.
    run_inst_seq [mk_inst id ADD [src;Var ctr] [addr];
      mk_inst lid load [Var addr] [valvar];
      mk_inst mid MUL [Var ctr;Lit 32w] [tmp];
      mk_inst aid ADD [Var root;Var tmp] [out];
      mk_inst sid MSTORE [Var out;Var valvar] [];
      mk_inst iid ADD [Var ctr;Lit 1w] [next];
      mk_inst cid ASSIGN [Var next] [ctr]] s = OK t /\
    inst_seq_ptr D lo ctx fn PG G tn
      [mk_inst id ADD [src;Var ctr] [addr];
       mk_inst lid load [Var addr] [valvar];
       mk_inst mid MUL [Var ctr;Lit 32w] [tmp];
       mk_inst aid ADD [Var root;Var tmp] [out];
       mk_inst sid MSTORE [Var out;Var valvar] [];
       mk_inst iid ADD [Var ctr;Lit 1w] [next];
       mk_inst cid ASSIGN [Var next] [ctr]] s Gf tnf /\
    t = update_var ctr (k+1w) (update_var next (k+1w)
      (mstore (w2n (a+n2w off)) (slot_copy_word load s (srcword+k))
        (update_var out (a+n2w off) (update_var tmp (n2w off)
          (update_var valvar (slot_copy_word load s (srcword+k))
            (update_var addr (srcword+k) s)))))) /\
    op_taint tnf (Var ctr) = {} /\
    tnf.t_mem =
      (tn.t_mem DIFF {j | w2n (a+n2w off) <= j /\ j < w2n (a+n2w off) + 32}) UNION
      {w2n (a+n2w off) + j | j IN
        key_taint (if load = SLOAD then tn.t_stor else tn.t_trans) (srcword+k)} /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    allocas_from lo t /\ (ctx_has_dalloca ctx ==> allocas_below_fmp t) /\
    (!p. p <> addr /\ p <> valvar /\ p <> tmp /\ p <> out /\
         p <> ctr /\ p <> next ==>
      FLOOKUP Gf p = FLOOKUP G p /\ op_taint tnf (Var p) = op_taint tn (Var p)) /\
    (!p c. p <> addr /\ p <> valvar /\ p <> tmp /\ p <> out /\
      p <> ctr /\ p <> next /\ ptr_covers G tn p s c ==>
      ptr_covers Gf tnf p t c)
Proof
  strip_tac >> (
  mp_tac (Q.INST [`counter` |-> `Var ctr`, `n` |-> `32`, `value` |-> `valvar`]
    (SPEC_ALL copy_first_four_segment)) >>
  (impl_tac >- simp[]) >> disch_then strip_assume_tac >>
  rename1 `inst_seq_ptr D lo ctx fn PG G tn _ s Gm tnm` >>
  qmatch_asmsub_abbrev_tac `t = u` >>
  qabbrev_tac `w = u with vs_inst_idx := s.vs_inst_idx + 4` >>
  `eval_operand (Var out) w = SOME (a+n2w off) /\
   eval_operand (Var valvar) w = SOME (slot_copy_word load s (srcword+k)) /\
   eval_operand (Var ctr) w = SOME k /\ op_taint tnm (Var ctr) = {} /\
   ptr_covers Gm tnm out w 32 /\ allocas_from lo w /\
   (ctx_has_dalloca ctx ==> allocas_below_fmp w)` by
    (fs[Abbr `w`, Abbr `u`, slot_copy_operand_update, eval_operand_def,
        lookup_var_def, update_var_def, FLOOKUP_UPDATE, ptr_covers_inst_idx,
        allocas_from_def, allocas_below_fmp_def] >> metis_tac[]) >>
  mp_tac (Q.INST [`s` |-> `w`, `G` |-> `Gm`, `tn` |-> `tnm`,
    `root` |-> `out`, `addr` |-> `a+n2w off`, `v` |-> `Var valvar`,
    `value` |-> `slot_copy_word load s (srcword+k)`, `x` |-> `k`,
    `id` |-> `sid`, `aid` |-> `cid`, `counter` |-> `ctr`] (SPEC_ALL copy_store_increment_segment)) >>
  (impl_tac >- simp[]) >> disch_then strip_assume_tac >>
  rename1 `inst_seq_ptr D lo ctx fn PG Gm tnm _ w Gf tnf` >>
  qexistsl_tac [`Gf`, `tnf`, `update_var ctr (k+1w) (update_var next (k+1w)
    (mstore (w2n (a+n2w off)) (slot_copy_word load s (srcword+k)) u))`] >>
  conj_tac
  >- (qpat_assum `run_inst_seq _ s = OK t` (mp_tac o MATCH_MP run_inst_seq_append) >>
      disch_then (qspec_then `[mk_inst sid MSTORE [Var out;Var valvar] [];
        mk_inst iid ADD [Var ctr;Lit 1w] [next];
        mk_inst cid ASSIGN [Var next] [ctr]]` mp_tac) >>
      simp[] >> disch_then SUBST1_TAC >>
      `eval_operand (Var out) u = SOME (a+n2w off) /\
       eval_operand (Var valvar) u = SOME (slot_copy_word load s (srcword+k)) /\
       eval_operand (Var ctr) u = SOME k` by fs[Abbr `w`, eval_operand_def, lookup_var_def] >>
      simp[Once run_inst_seq_def, step_inst_base_def, mk_inst_def, exec_write2_def] >>
      fs[eval_operand_def, lookup_var_def] >>
      simp[run_inst_seq_def, step_inst_base_def, mk_inst_def, exec_pure2_def,
           eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE]) >>
  conj_tac
  >- (irule (SRULE [] (Q.INST [`prefix` |->
        `[mk_inst id ADD [src;Var ctr] [addr]; mk_inst lid load [Var addr] [valvar];
          mk_inst mid MUL [Var ctr;Lit 32w] [tmp];
          mk_inst aid ADD [Var root;Var tmp] [out]]`] (SPEC_ALL inst_seq_ptr_append))) >>
      simp[mk_inst_def, is_terminator_def] >> qexistsl_tac [`Gm`, `tnm`] >>
      gvs[Abbr `w`, mk_inst_def, is_terminator_def]) >>
  gvs[Abbr `w`, copy_mstore_inst_idx, copy_update_inst_idx, ptr_covers_inst_idx,
      allocas_from_def, allocas_below_fmp_def] >> metis_tac[])
QED
