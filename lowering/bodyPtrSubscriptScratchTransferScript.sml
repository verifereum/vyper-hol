(* Exact taint transfer for scratch writes, including tainted data. *)
Theory bodyPtrSubscriptScratchTransfer
Ancestors
  bodyPtrSubscriptScratchStore bodyPtrDefs typedCopyPtr ptrDiscipline
  ptrSafeRun venomExecSemantics venomState venomInst contextCodegenRel
  codegenRel finite_map pred_set

Theorem scratch_mstore_memory_taint:
  lookup_var dst s = SOME a /\ eval_operand value s = SOME w /\
  t = mstore (w2n a) w s /\
  tnf = step_taint (mk_inst iid MSTORE [Var dst;value] []) s t tn ==>
  tnf.t_mem = (tn.t_mem DIFF {i | w2n a <= i /\ i < w2n a + 32})
    UNION {w2n a + k | k IN op_taint tn value}
Proof
  strip_tac >>
  gvs[step_taint_def, mk_inst_def, mem_taint_def, step_writes_def,
      source_memory_write_ranges_def, fixed_source_write_range_def,
      eval_operand_def, written_taint_def, range_bytes_def, new_site_bytes_def,
      mstore_def, FLOOKUP_DEF, EXTENSION] >> metis_tac[]
QED

Theorem scratch_mstore_ghost_frame:
  t = mstore off w s /\
  Gf = step_prov PG G (mk_inst iid MSTORE [Var dst;value] []) t /\
  tnf = step_taint (mk_inst iid MSTORE [Var dst;value] []) s t tn ==>
  Gf = G /\ tnf.t_var = tn.t_var /\ tnf.t_stor = tn.t_stor /\
  tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm
Proof
  strip_tac >>
  gvs[step_prov_def, set_prov_def, out_prov_def, step_taint_def,
      mk_inst_def, set_var_taint_def, DRESTRICT_UNIV,
      store_taint_def, adopt_reset_def, imm_taint_def, mstore_def]
QED

Theorem scratch_mstore_coverage:
  t = mstore off w s /\
  Gf = step_prov PG G (mk_inst iid MSTORE [Var dst;value] []) t /\
  tnf = step_taint (mk_inst iid MSTORE [Var dst;value] []) s t tn /\
  ptr_covers G tn p s n ==>
  ptr_covers Gf tnf p (t with vs_inst_idx := SUC s.vs_inst_idx) n
Proof
  strip_tac >> drule_all scratch_mstore_ghost_frame >> strip_tac >>
  gvs[ptr_covers_def, mstore_def, lookup_var_def, op_taint_def]
QED

Theorem scratch_mstore_byte_taint:
  lookup_var dst s = SOME a /\ eval_operand value s = SOME w /\
  t = mstore (w2n a) w s /\
  tnf = step_taint (mk_inst iid MSTORE [Var dst;value] []) s t tn /\
  k < 32 ==>
  (w2n a + k IN tnf.t_mem <=> k IN op_taint tn value)
Proof
  strip_tac >> drule_all scratch_mstore_memory_taint >>
  disch_then SUBST1_TAC >> simp[]
QED

Theorem scratch_mstore_counted:
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  get_instruction bb s.vs_inst_idx =
    SOME (mk_inst iid MSTORE [Var dst;value] []) /\
  ptr_covers G tn dst s 32 /\ op_taint tn (Var dst) = {} /\
  lookup_var dst s = SOME a /\ eval_operand value s = SOME w ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf = ((mstore (w2n a) w s) with vs_inst_idx := SUC s.vs_inst_idx) /\
    Gf = G /\ tnf.t_var = tn.t_var /\ tnf.t_stor = tn.t_stor /\
    tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
    tnf.t_mem = (tn.t_mem DIFF {i | w2n a <= i /\ i < w2n a + 32})
      UNION {w2n a + k | k IN op_taint tn value} /\
    sf.vs_accounts = s.vs_accounts /\ sf.vs_transient = s.vs_transient /\
    sf.vs_call_ctx = s.vs_call_ctx /\
    (!p n. ptr_covers G tn p s n ==> ptr_covers Gf tnf p sf n)
Proof
  strip_tac >>
  drule_all bodyPtrSubscriptScratchStoreTheory.mstore_counted_edge >>
  disch_then (qspecl_then [`PG`, `D`] assume_tac) >>
  qmatch_asmsub_abbrev_tac `gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf)` >>
  qexistsl_tac [`Gf`, `tnf`, `sf`] >> simp[] >>
  `Gf = G /\ tnf.t_var = tn.t_var /\ tnf.t_stor = tn.t_stor /\
   tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm` by
    (simp[Abbr `Gf`, Abbr `tnf`] >> metis_tac[scratch_mstore_ghost_frame]) >>
  `tnf.t_mem = (tn.t_mem DIFF {i | w2n a <= i /\ i < w2n a + 32})
     UNION {w2n a + k | k IN op_taint tn value}` by
    (irule scratch_mstore_memory_taint >> simp[Abbr `tnf`] >> metis_tac[]) >>
  `!p n. ptr_covers G tn p s n ==> ptr_covers Gf tnf p sf n` by
    (rpt strip_tac >> simp[Abbr `sf`] >>
     metis_tac[scratch_mstore_coverage]) >>
  simp[Abbr `sf`, mstore_def]
QED
