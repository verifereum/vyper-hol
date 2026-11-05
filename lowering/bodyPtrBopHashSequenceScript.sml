Theory bodyPtrBopHashSequence
Ancestors
  bodyPtrBopHashStep bodyPtrBopScalarProbe typedCopyPtr fragGasSeqPtr
  ptrDiscipline venomInst finite_map codegenRel venomExecSemantics venomState

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
  (step_taint (mk_inst id opc [left; right] [q]) s u tn).t_trans = tn.t_trans /\
  (!x. x <> q ==>
    FLOOKUP (step_taint (mk_inst id opc [left; right] [q]) s u tn).t_var x =
    FLOOKUP tn.t_var x)
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
