Theory bodyPtrBopHashSequence
Ancestors
  bodyPtrBopHashStep bodyPtrBopScalarProbe typedCopyPtr fragGasSeqPtr
  ptrDiscipline venomInst finite_map codegenRel venomExecSemantics venomState
  valueEncodingProps ghostPcTransportPtr

Theorem bop_hash_add_provenance:
  FLOOKUP G p = SOME site ==>
  FLOOKUP (step_prov PG G (mk_inst id ADD [Var p; Lit 32w] [q]) u) q =
    SOME site
Proof
  simp[step_prov_def, set_prov_def, out_prov_def, first_prov_def,
       op_prov_def, mk_inst_def, FLOOKUP_UPDATE]
QED

Theorem bop_hash_binary_taint_frame:
  (opc = ADD \/ opc = SHA3) /\
  u.vs_allocas = s.vs_allocas /\ u.vs_fmp = s.vs_fmp ==>
  (step_taint (mk_inst id opc [left; right] [q]) s u tn).t_mem = tn.t_mem /\
  (step_taint (mk_inst id opc [left; right] [q]) s u tn).t_stor = tn.t_stor /\
  (step_taint (mk_inst id opc [left; right] [q]) s u tn).t_trans = tn.t_trans
Proof
  strip_tac >> gvs[] >>
  simp[step_taint_def, set_var_taint_def, mk_inst_def, mem_taint_def,
       new_site_bytes_def, step_writes_def, written_taint_def,
       source_memory_write_ranges_def, store_taint_def, adopt_reset_def,
       FLOOKUP_UPDATE, range_bytes_def] >>
  simp[pred_setTheory.EXTENSION] >>
  rpt strip_tac >> (eq_tac >- (strip_tac >> gvs[FLOOKUP_DEF])) >> simp[]
QED

Theorem bop_hash_add_state:
  lookup_var p s = SOME w /\
  step_inst_base (mk_inst id ADD [Var p; Lit 32w] [q]) s = OK u ==>
  u = update_var q (w + 32w) s
Proof
  strip_tac >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  PURE_ONCE_REWRITE_TAC[venomExecSemanticsTheory.step_inst_base_def] >>
  simp[mk_inst_def, venomExecSemanticsTheory.exec_pure2_def,
       eval_operand_def]
QED

Theorem bop_hash_add_preserves_ptr_covers:
  q <> x /\ ptr_covers G tn x s n ==>
  ptr_covers
    (step_prov PG G (mk_inst id ADD [Var p; Lit 32w] [q])
      (update_var q v s))
    (step_taint (mk_inst id ADD [Var p; Lit 32w] [q]) s
      (update_var q v s) tn)
    x (update_var q v s) n
Proof
  rpt strip_tac >>
  gvs[bodyPtrDefsTheory.ptr_covers_def, step_prov_def, set_prov_def,
      out_prov_def, first_prov_def, op_prov_def, step_taint_def,
      set_var_taint_def, op_taint_def, mk_inst_def, update_var_def,
      lookup_var_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >>
  Cases_on `FLOOKUP G p` >>
  gvs[FLOOKUP_UPDATE, FLOOKUP_DRESTRICT] >> metis_tac[]
QED

Theorem bop_hash_mload_state:
  lookup_var p s = SOME w /\
  step_inst_base (mk_inst id MLOAD [Var p] [l]) s = OK u ==>
  u = update_var l (mload (w2n w) s) s
Proof
  strip_tac >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  simp[mk_inst_def, exec_read1_def, eval_operand_def]
QED

Theorem bop_hash_sha3_state_frame:
  step_inst_base (mk_inst id SHA3 [a; n] [h]) s = OK u ==>
  u.vs_memory = s.vs_memory /\ u.vs_allocas = s.vs_allocas /\
  u.vs_fmp = s.vs_fmp /\
  (!x. x <> h ==> lookup_var x u = lookup_var x s)
Proof
  PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
  simp[mk_inst_def] >>
  Cases_on `eval_operand a s` >> simp[] >>
  Cases_on `eval_operand n s` >>
  simp[update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> gvs[lookup_var_def, FLOOKUP_UPDATE]
QED

Theorem bop_hash_sha3_output_clean:
  FLOOKUP (step_taint (mk_inst id SHA3 [a; b] [h]) s u tn).t_var h = SOME {} /\
  op_taint (step_taint (mk_inst id SHA3 [a; b] [h]) s u tn) (Var h) = {}
Proof
  simp[step_taint_def, set_var_taint_def, out_taint_def, op_taint_def,
       mk_inst_def, FLOOKUP_UPDATE] >>
  Cases_on `eval_operand a s` >> simp[]
QED

Theorem bop_hash_sequence_state_frame:
  p <> q /\ x <> q /\ x <> l /\ x <> h /\
  lookup_var p s = SOME w /\
  iA = mk_inst aId ADD [Var p; Lit 32w] [q] /\
  iL = mk_inst lId MLOAD [Var p] [l] /\
  iH = mk_inst hId SHA3 [Var q; Var l] [h] /\
  step_inst_base iA s = OK uA /\
  sA = uA with vs_inst_idx := SUC s.vs_inst_idx /\
  step_inst_base iL sA = OK uL /\
  sL = uL with vs_inst_idx := SUC sA.vs_inst_idx /\
  step_inst_base iH sL = OK uH /\
  t = uH with vs_inst_idx := SUC sL.vs_inst_idx ==>
  t.vs_memory = s.vs_memory /\ lookup_var x t = lookup_var x s
Proof
  strip_tac >> gvs[] >>
  drule_all bop_hash_add_state >> strip_tac >> gvs[] >>
  `lookup_var p (update_var q (w + 32w) s with
     vs_inst_idx := SUC s.vs_inst_idx) = SOME w` by
    gvs[lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  drule_all bop_hash_mload_state >> strip_tac >> gvs[] >>
  drule bop_hash_sha3_state_frame >> strip_tac >>
  gvs[lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED

Theorem bop_hash_add_payload_covers:
  FLOOKUP G p = SOME (b,sz) /\
  b <= w2n v /\ w2n v + n <= b + sz ==>
  ptr_covers
    (step_prov PG G (mk_inst id ADD [Var p; Lit 32w] [q])
      (update_var q v s))
    (step_taint (mk_inst id ADD [Var p; Lit 32w] [q]) s
      (update_var q v s) tn)
    q (update_var q v s) n
Proof
  strip_tac >>
  simp[bodyPtrDefsTheory.ptr_covers_def, lookup_var_def, update_var_def,
       FLOOKUP_UPDATE, op_taint_def, bop_add_output_clean,
       bop_hash_add_provenance] >>
  drule bop_hash_add_provenance >> disch_then (fn th => simp[th]) >>
  qexistsl [`b`, `sz`] >> simp[]
QED

Theorem bop_hash_mload_sha3_ok:
  l <> q /\ lookup_var p s = SOME w /\ lookup_var q s = SOME v /\
  mload (w2n w) s = n2w n /\ n < dimword(:256) /\
  (0 < n ==> ptr_covers G tn q s n) /\ op_taint tn (Var q) = {} /\
  (!i. w2n w <= i /\ i < w2n w + 32 ==> i NOTIN tn.t_mem) /\
  (!i. w2n v <= i /\ i < w2n v + n ==> i NOTIN tn.t_mem) /\
  ~ctx_has_dalloca ctx /\
  u = update_var l (mload (w2n w) s) s /\
  G' = step_prov PG G (mk_inst id MLOAD [Var p] [l]) u /\
  tn' = step_taint (mk_inst id MLOAD [Var p] [l]) s u tn ==>
  ptr_inst_ok D 0 0 ctx fn G' tn'
    (mk_inst hId SHA3 [Var q; Var l] [h]) (u with vs_inst_idx := k)
Proof
  strip_tac >>
  `op_taint tn' (Var l) = {} /\ tn'.t_mem = tn.t_mem` by
    (`eval_operand (Var p) s = SOME w` by simp[eval_operand_def] >>
     drule mload_ghost_clean >> simp[] >>
     disch_then (qspecl_then [`id`, `l`] mp_tac) >>
     gvs[] >> metis_tac[]) >>
  `0 < n ==> ptr_covers G' tn' q u n` by
    (strip_tac >> qpat_x_assum `mload _ _ = _` kall_tac >>
     gvs[] >> irule mload_preserves_ptr_covers >> simp[]) >>
  `op_taint tn' (Var q) = {}` by
    gvs[step_taint_def, set_var_taint_def, op_taint_def,
        mk_inst_def, FLOOKUP_UPDATE] >>
  irule ptr_inst_ok_sha3 >> simp[] >>
  qexistsl [`v`, `n2w n`] >>
  gvs[eval_operand_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE,
      wordsTheory.w2n_n2w, step_taint_def, set_var_taint_def, op_taint_def,
      mk_inst_def]
QED

Theorem bop_hash_load_hash_old_prov:
  (opc = MLOAD \/ opc = SHA3) /\ x <> out ==>
  FLOOKUP (step_prov PG G (mk_inst id opc ops [out]) u) x = FLOOKUP G x
Proof
  strip_tac >> gvs[step_prov_def, out_prov_def, mk_inst_def,
                  set_prov_def, FLOOKUP_DRESTRICT]
QED

Theorem bop_hash_mload_old_taint:
  x <> l ==>
  FLOOKUP (step_taint (mk_inst id MLOAD [a] [l]) s u tn).t_var x =
  FLOOKUP tn.t_var x
Proof
  simp[step_taint_def, mk_inst_def, set_var_taint_def, FLOOKUP_UPDATE]
QED

Theorem bop_hash_sequence_checks:
  p <> q /\ l <> q /\ ~ctx_has_dalloca ctx /\
  lookup_var p s = SOME w /\ ptr_covers G tn p s 32 /\
  mload (w2n w) s = n2w n /\ n < dimword(:256) /\
  FLOOKUP G p = SOME (b,sz) /\
  (0 < n ==> b <= w2n (w + 32w) /\ w2n (w + 32w) + n <= b + sz) /\
  (!i. w2n w <= i /\ i < w2n w + 32 ==> i NOTIN tn.t_mem) /\
  (!i. w2n (w + 32w) <= i /\ i < w2n (w + 32w) + n ==> i NOTIN tn.t_mem) /\
  iA = mk_inst aId ADD [Var p; Lit 32w] [q] /\
  iL = mk_inst lId MLOAD [Var p] [l] /\
  iH = mk_inst hId SHA3 [Var q; Var l] [h] /\
  step_inst_base iA s = OK uA /\
  sA = uA with vs_inst_idx := SUC s.vs_inst_idx /\
  G1 = step_prov PG G iA uA /\ tn1 = step_taint iA s uA tn /\
  step_inst_base iL sA = OK uL /\
  sL = uL with vs_inst_idx := SUC sA.vs_inst_idx /\
  G2 = step_prov PG G1 iL uL /\ tn2 = step_taint iL sA uL tn1 ==>
  ptr_inst_ok D 0 0 ctx fn G tn iA s /\
  ptr_inst_ok D 0 0 ctx fn G1 tn1 iL sA /\
  ptr_inst_ok D 0 0 ctx fn G2 tn2 iH sL
Proof
  strip_tac >>
  `uA = update_var q (w + 32w) s` by
    (irule bop_hash_add_state >> gvs[] >> metis_tac[]) >>
  `ptr_covers G1 tn1 p sA 32` by
    (gvs[] >> irule bop_hash_add_preserves_ptr_covers >> simp[]) >>
  conj_tac
  >- (gvs[] >> irule ptr_inst_ok_copy_len_binop >>
      gvs[bodyPtrDefsTheory.ptr_covers_def, op_taint_def]) >>
  conj_tac >- (gvs[] >> irule ptr_inst_ok_mload >> simp[]) >>
  `lookup_var p sA = SOME w /\ lookup_var q sA = SOME (w + 32w)` by
    gvs[lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  `tn1.t_mem = tn.t_mem` by
    (gvs[] >> irule (cj 1 bop_hash_binary_taint_frame) >>
     simp[update_var_def]) >>
  `mload (w2n w) sA = n2w n` by gvs[mload_def, update_var_def] >>
  `op_taint tn1 (Var q) = {}` by
    gvs[op_taint_def, bop_add_output_clean] >>
  `0 < n ==> ptr_covers G1 tn1 q sA n` by
    (strip_tac >> gvs[] >> irule bop_hash_add_payload_covers >> simp[]) >>
  `uL = update_var l (mload (w2n w) sA) sA` by
    (irule bop_hash_mload_state >> gvs[] >> metis_tac[]) >>
  `!i. w2n w <= i /\ i < w2n w + 32 ==> i NOTIN tn1.t_mem` by metis_tac[] >>
  `!i. w2n (w + 32w) <= i /\ i < w2n (w + 32w) + n ==>
       i NOTIN tn1.t_mem` by metis_tac[] >>
  qpat_x_assum `iL = _` SUBST_ALL_TAC >>
  drule_all bop_hash_mload_sha3_ok >> simp[]
QED

Theorem bop_hash_sha3_output_no_prov:
  op_prov (step_prov PG G (mk_inst id SHA3 ops [h]) u) (Var h) = NONE
Proof
  simp[op_prov_def, step_prov_def, set_prov_def, out_prov_def,
       mk_inst_def, FLOOKUP_DRESTRICT]
QED

Theorem bop_hash_sequence_ghost_frame:
  tn1.t_mem = tn.t_mem /\ tn1.t_stor = tn.t_stor /\ tn1.t_trans = tn.t_trans /\
  tn2.t_mem = tn1.t_mem /\ tn2.t_stor = tn1.t_stor /\ tn2.t_trans = tn1.t_trans /\
  tn3.t_mem = tn2.t_mem /\ tn3.t_stor = tn2.t_stor /\ tn3.t_trans = tn2.t_trans /\
  G1 = step_prov PG G (mk_inst aId ADD [Var p; Lit 32w] [q]) uA /\
  G2 = step_prov PG G1 (mk_inst lId MLOAD [Var p] [l]) uL /\
  G3 = step_prov PG G2 (mk_inst hId SHA3 [Var q; Var l] [h]) uH /\
  tn1 = step_taint (mk_inst aId ADD [Var p; Lit 32w] [q]) s uA tn /\
  tn2 = step_taint (mk_inst lId MLOAD [Var p] [l]) sA uL tn1 /\
  tn3 = step_taint (mk_inst hId SHA3 [Var q; Var l] [h]) sL uH tn2 ==>
  op_prov G3 (Var h) = NONE /\ op_taint tn3 (Var h) = {} /\
  tn3.t_mem = tn.t_mem /\ tn3.t_stor = tn.t_stor /\ tn3.t_trans = tn.t_trans /\
  (!x. x <> q /\ x <> l /\ x <> h ==>
    FLOOKUP G3 x = FLOOKUP G x /\ FLOOKUP tn3.t_var x = FLOOKUP tn.t_var x)
Proof
  strip_tac >>
  `op_taint tn3 (Var h) = {}` by
    gvs[bop_hash_sha3_output_clean] >>
  `op_prov G3 (Var h) = NONE` by gvs[bop_hash_sha3_output_no_prov] >>
  simp[] >> rpt strip_tac
  >- (gvs[] >> simp[bop_add_preserves_old_prov, bop_hash_load_hash_old_prov]) >>
  simp[mk_inst_def] >>
  simp[step_taint_def, set_var_taint_def, FLOOKUP_UPDATE]
QED

Theorem bop_hash_seq_cons:
  step_inst_base i s = OK u /\
  t = u with vs_inst_idx := SUC s.vs_inst_idx /\
  G1 = step_prov PG G i u /\ tn1 = step_taint i s u tn /\
  ptr_inst_ok D lo 0 ctx fn G tn i s /\
  inst_seq_ptr D lo ctx fn PG G1 tn1 rest t G' tn' ==>
  inst_seq_ptr D lo ctx fn PG G tn (i::rest) s G' tn'
Proof
  strip_tac >> pure_once_rewrite_tac[inst_seq_ptr_def] >> gvs[]
QED

Theorem bop_hash_sequence_checked:
  p <> q /\ l <> q /\ ~ctx_has_dalloca ctx /\
  lookup_var p s = SOME w /\ ptr_covers G tn p s 32 /\
  mem_word_at (w2n w) s.vs_memory = n2w n /\ n < dimword(:256) /\
  FLOOKUP G p = SOME (b,sz) /\
  (0 < n ==> b <= w2n (w + 32w) /\ w2n (w + 32w) + n <= b + sz) /\
  (!i. w2n w <= i /\ i < w2n w + 32 ==> i NOTIN tn.t_mem) /\
  (!i. w2n (w + 32w) <= i /\ i < w2n (w + 32w) + n ==> i NOTIN tn.t_mem) /\
  iA = mk_inst aId ADD [Var p; Lit 32w] [q] /\
  iL = mk_inst lId MLOAD [Var p] [l] /\
  iH = mk_inst hId SHA3 [Var q; Var l] [h] /\
  step_inst_base iA s = OK uA /\
  sA = uA with vs_inst_idx := SUC s.vs_inst_idx /\
  G1 = step_prov PG G iA uA /\ tn1 = step_taint iA s uA tn /\
  step_inst_base iL sA = OK uL /\
  sL = uL with vs_inst_idx := SUC sA.vs_inst_idx /\
  G2 = step_prov PG G1 iL uL /\ tn2 = step_taint iL sA uL tn1 /\
  step_inst_base iH sL = OK uH /\
  G3 = step_prov PG G2 iH uH /\ tn3 = step_taint iH sL uH tn2 ==>
  inst_seq_ptr D 0 ctx fn PG G tn [iA;iL;iH] s G3 tn3 /\
  op_prov G3 (Var h) = NONE /\ op_taint tn3 (Var h) = {} /\
  tn3.t_mem = tn.t_mem /\ tn3.t_stor = tn.t_stor /\ tn3.t_trans = tn.t_trans /\
  (!x. x <> q /\ x <> l /\ x <> h ==>
    FLOOKUP G3 x = FLOOKUP G x /\ FLOOKUP tn3.t_var x = FLOOKUP tn.t_var x)
Proof
  strip_tac >>
  `mload (w2n w) s = n2w n` by gvs[GSYM mem_word_at_eq_mload] >>
  drule_all bop_hash_sequence_checks >> strip_tac >>
  conj_tac
  >- (`inst_seq_ptr D 0 ctx fn PG G2 tn2 [iH] sL G3 tn3` by
        (pure_once_rewrite_tac[inst_seq_ptr_def] >>
         gvs[inst_seq_ptr_def]) >>
      `inst_seq_ptr D 0 ctx fn PG G1 tn1 [iL;iH] sA G3 tn3` by
        (irule bop_hash_seq_cons >> metis_tac[]) >>
      irule bop_hash_seq_cons >> metis_tac[]) >>
  `uA = update_var q (w + 32w) s` by
    (irule bop_hash_add_state >> gvs[] >> metis_tac[]) >>
  `lookup_var p sA = SOME w` by
    gvs[lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  `uL = update_var l (mload (w2n w) sA) sA` by
    (irule bop_hash_mload_state >> gvs[] >> metis_tac[]) >>
  `tn1.t_mem = tn.t_mem /\ tn1.t_stor = tn.t_stor /\ tn1.t_trans = tn.t_trans` by
    (gvs[] >> irule bop_hash_binary_taint_frame >> simp[update_var_def]) >>
  `tn2.t_mem = tn1.t_mem /\ tn2.t_stor = tn1.t_stor /\ tn2.t_trans = tn1.t_trans` by
    (`eval_operand (Var p) sA = SOME w` by simp[eval_operand_def] >>
     drule mload_ghost_clean >> simp[] >>
     disch_then (qspecl_then [`tn1`, `lId`, `l`] mp_tac) >>
     gvs[] >> metis_tac[]) >>
  `uH.vs_allocas = sL.vs_allocas /\ uH.vs_fmp = sL.vs_fmp` by
    (qpat_x_assum `iH = _` SUBST_ALL_TAC >>
     drule bop_hash_sha3_state_frame >> simp[]) >>
  `tn3.t_mem = tn2.t_mem /\ tn3.t_stor = tn2.t_stor /\ tn3.t_trans = tn2.t_trans` by
    (qpat_x_assum `tn3 = _` SUBST1_TAC >>
     qpat_x_assum `iH = _` SUBST1_TAC >>
     irule bop_hash_binary_taint_frame >> simp[]) >>
  qpat_x_assum `iA = _` SUBST_ALL_TAC >>
  qpat_x_assum `iL = _` SUBST_ALL_TAC >>
  qpat_x_assum `iH = _` SUBST_ALL_TAC >>
  drule_all bop_hash_sequence_ghost_frame >> simp[]
QED
