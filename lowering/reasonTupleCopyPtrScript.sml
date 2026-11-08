(* Shared checked copy boundaries for the raise/assert Error(string) tuple. *)
Theory reasonTupleCopyPtr
Ancestors
  wordLoadStorePtr reasonPrefixPtr reasonResourcesPtr robustCopyTransportPtr typedCopyPtr
  valueEncodingProps valueEncodingProofs venomMemProofs ptrDiscipline
  venomExecSemantics venomState words list pred_set arithmetic fragExecPtr
  emitHelper bodyPtrDefs venomInst compileEnv fragExec finite_map fragGasPathPtr
  exprSimBufferStore vfmConstants ghostPcTransportPtr exprSimProps

(* Resetting the three scratch fields composes without identifying states
   merely from their memory projections. *)
Theorem reason_scratch_frame_trans:
  (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
            vs_inst_idx := s.vs_inst_idx|>) = s /\
  (u with <|vs_vars := t.vs_vars; vs_memory := t.vs_memory;
            vs_inst_idx := t.vs_inst_idx|>) = t ==>
  (u with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
            vs_inst_idx := s.vs_inst_idx|>) = s
Proof
  simp[venom_state_component_equality] >> metis_tac[]
QED

(* Actual MCOPY taint, including arbitrary tainted padding, transports the
   robust representation. No cleanliness assumption on payload bytes is used. *)
Theorem reason_mcopy_robust_representation:
  !tn s id dst src count_op a b n tv v.
    eval_operand dst s = SOME b /\ eval_operand src s = SOME a /\
    eval_operand count_op s = SOME n /\
    val_wf tv v /\ val_footprint tv v <= w2n n /\
    (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
      val_in_memory tv v (w2n a) mem) ==>
    !mem. mem_agree_outside
      (step_taint (mk_inst id MCOPY [dst;src;count_op] []) s
        (mcopy (w2n b) (w2n a) (w2n n) s) tn).t_mem
      (mcopy (w2n b) (w2n a) (w2n n) s).vs_memory mem ==>
      val_in_memory tv v (w2n b) mem
Proof
  rpt gen_tac >> strip_tac >>
  ` (step_taint (mk_inst id MCOPY [dst;src;count_op] []) s
       (mcopy (w2n b) (w2n a) (w2n n) s) tn).t_mem =
      (tn.t_mem DIFF {i | w2n b <= i /\ i < w2n b + w2n n}) UNION
      {w2n b + i | i < w2n n /\ w2n a + i IN tn.t_mem}` by
    (irule (cj 5 mcopy_operand_ghost_frame) >> simp[]) >>
  rpt strip_tac >> irule robust_val_in_memory_copy_transport >>
  conj_tac >- simp[] >>
  qexistsl_tac [`s.vs_memory`,
    `(mcopy (w2n b) (w2n a) (w2n n) s).vs_memory`, `w2n n`,
    `w2n a`, `tn.t_mem`,
    `(step_taint (mk_inst id MCOPY [dst;src;count_op] []) s
      (mcopy (w2n b) (w2n a) (w2n n) s) tn).t_mem`] >>
  simp[mcopy_mem_bytes_at_same, IN_DIFF, IN_UNION, GSPECIFICATION]
QED

Theorem reason_mcopy_live_covers:
  !PG G tn s id dst src count_op a b n p k.
    eval_operand dst s = SOME b /\ eval_operand src s = SOME a /\
    eval_operand count_op s = SOME n /\ ptr_covers G tn p s k ==>
    ptr_covers
      (step_prov PG G (mk_inst id MCOPY [dst;src;count_op] [])
        (mcopy (w2n b) (w2n a) (w2n n) s))
      (step_taint (mk_inst id MCOPY [dst;src;count_op] []) s
        (mcopy (w2n b) (w2n a) (w2n n) s) tn)
      p (mcopy (w2n b) (w2n a) (w2n n) s) k
Proof
  rpt gen_tac >> strip_tac >>
  `step_prov PG G (mk_inst id MCOPY [dst;src;count_op] [])
      (mcopy (w2n b) (w2n a) (w2n n) s) = G` by
    (irule (cj 1 mcopy_operand_ghost_frame) >> simp[]) >>
  `(step_taint (mk_inst id MCOPY [dst;src;count_op] []) s
      (mcopy (w2n b) (w2n a) (w2n n) s) tn).t_var = tn.t_var` by
    (irule (cj 2 mcopy_operand_ghost_frame) >> simp[]) >>
  fs[ptr_covers_def, mcopy_def, write_memory_with_expansion_def,
     lookup_var_def, op_taint_def]
QED

Theorem reason_mcopy_path_ptr:
  emit_void MCOPY [Var dst;Var src;count_op] sa = ((),sb) /\
  fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  eval_operand (Var dst) s = SOME b /\
  eval_operand (Var src) s = SOME a /\
  eval_operand count_op s = SOME n /\ op_taint tn count_op = {} /\
  ptr_covers G tn dst s (w2n n) /\ ptr_covers G tn src s (w2n n) ==>
  gas_path_ptr D 0 ctx func PG G tn s 0
    (step_prov PG G (mk_inst sa.cs_next_id MCOPY [Var dst;Var src;count_op] [])
      (mcopy (w2n b) (w2n a) (w2n n) s))
    (step_taint (mk_inst sa.cs_next_id MCOPY [Var dst;Var src;count_op] []) s
      (mcopy (w2n b) (w2n a) (w2n n) s) tn)
    (OK (mcopy (w2n b) (w2n a) (w2n n) s with
      vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >> irule reason_encoder_emit_path_ptr >>
  simp[GSYM emit_void_def, is_terminator_def] >> conj_tac
  >- (PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
      gvs[mk_inst_def, eval_operand_def]) >>
  conj_tac
  >- (qexists_tac `sb` >> fs[emit_void_def, emit_inst_def]) >>
  irule ptr_inst_ok_mcopy_operand >> simp[] >> metis_tac[]
QED


Theorem reason_copy_binop_path_ptr:
  emit_inst opc [left;right] [out] sa = ((),sb) /\
  fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\
  (opc = ADD /\ f = word_add \/ opc = AND /\ f = word_and) /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  eval_operand left s = SOME a /\ eval_operand right s = SOME b /\
  op_taint tn left = {} /\ op_taint tn right = {} ==>
  gas_path_ptr D 0 ctx func PG G tn s 0
    (step_prov PG G (mk_inst sa.cs_next_id opc [left;right] [out])
      (update_var out (f a b) s))
    (step_taint (mk_inst sa.cs_next_id opc [left;right] [out]) s
      (update_var out (f a b) s) tn)
    (OK (update_var out (f a b) s with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >> irule reason_encoder_emit_path_ptr >>
  simp[is_terminator_def] >> conj_tac >>
  all_tac
  >>~- ([`step_inst_base _ _ = _`],
    PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
    simp[mk_inst_def, exec_pure2_def]) >>
  irule typedCopyPtrTheory.ptr_inst_ok_copy_len_binop >> simp[]
QED

Theorem reason_copy_mload_path_ptr:
  emit_inst MLOAD [Var src] [out] sa = ((),sb) /\
  fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  lookup_var src s = SOME a /\ ptr_covers G tn src s 32 ==>
  gas_path_ptr D 0 ctx func PG G tn s 0
    (step_prov PG G (mk_inst sa.cs_next_id MLOAD [Var src] [out])
      (update_var out (mload (w2n a) s) s))
    (step_taint (mk_inst sa.cs_next_id MLOAD [Var src] [out]) s
      (update_var out (mload (w2n a) s) s) tn)
    (OK (update_var out (mload (w2n a) s) s with
      vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >> irule reason_encoder_emit_path_ptr >>
  simp[is_terminator_def] >> conj_tac
  >- (PURE_ONCE_REWRITE_TAC[step_inst_base_def] >>
      simp[mk_inst_def, exec_read1_def, eval_operand_def]) >>
  irule ptr_inst_ok_mload >> simp[]
QED

(* Counted scalar boundary with the old-variable resources needed when
   composing the rounded-copy prefix. The ghost frame is reused, not unfolded. *)
Theorem reason_copy_binop_resources_ptr:
  emit_inst opc [left;right] [out] sa = ((),sb) /\
  fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\
  (opc = ADD /\ f = word_add \/ opc = AND /\ f = word_and) /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  eval_operand left s = SOME a /\ eval_operand right s = SOME b /\
  op_taint tn left = {} /\ op_taint tn right = {} ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    lookup_var out sf = SOME (f a b) /\ op_taint tnf (Var out) = {} /\
    (sf with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
               vs_inst_idx := s.vs_inst_idx|>) = s /\
    sf.vs_allocas = s.vs_allocas /\
    sf.vs_memory = s.vs_memory /\ tnf.t_mem = tn.t_mem /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!p. p <> out ==>
      lookup_var p sf = lookup_var p s /\
      FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `t = update_var out (f a b) s` >>
  qabbrev_tac `Gf = step_prov PG G
    (mk_inst sa.cs_next_id opc [left;right] [out]) t` >>
  qabbrev_tac `tnf = step_taint
    (mk_inst sa.cs_next_id opc [left;right] [out]) s t tn` >>
  qexistsl_tac [`Gf`, `tnf`, `t with vs_inst_idx := SUC s.vs_inst_idx`] >>
  conj_tac
  >- (unabbrev_all_tac >>
      irule reason_copy_binop_path_ptr >> simp[]) >>
  `opc = ADD \/ opc = AND` by metis_tac[] >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   LENGTH sb.cs_current_insts = SUC (LENGTH sa.cs_current_insts)` by
    (gvs[emit_inst_def, fresh_id_def, emit_def, comp_bind_def,
         comp_ignore_bind_def, comp_return_def]) >>
  simp[Abbr `Gf`, Abbr `tnf`, Abbr `t`, copy_len_binop_ghost_frame,
       update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> simp[copy_len_binop_ghost_frame, venom_state_component_equality]
QED

Theorem reason_copy_mload_resources_ptr:
  emit_inst MLOAD [Var src] [out] sa = ((),sb) /\
  fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  lookup_var src s = SOME a /\ ptr_covers G tn src s 32 /\
  (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem) ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    lookup_var out sf = SOME (mload (w2n a) s) /\
    op_taint tnf (Var out) = {} /\
    (sf with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
               vs_inst_idx := s.vs_inst_idx|>) = s /\
    sf.vs_allocas = s.vs_allocas /\
    sf.vs_memory = s.vs_memory /\ tnf.t_mem = tn.t_mem /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!p. p <> out ==>
      lookup_var p sf = lookup_var p s /\
      FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  qabbrev_tac `t = update_var out (mload (w2n a) s) s` >>
  qabbrev_tac `Gf = step_prov PG G
    (mk_inst sa.cs_next_id MLOAD [Var src] [out]) t` >>
  qabbrev_tac `tnf = step_taint
    (mk_inst sa.cs_next_id MLOAD [Var src] [out]) s t tn` >>
  qexistsl_tac [`Gf`, `tnf`, `t with vs_inst_idx := SUC s.vs_inst_idx`] >>
  conj_tac
  >- (unabbrev_all_tac >> irule reason_copy_mload_path_ptr >> simp[]) >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   LENGTH sb.cs_current_insts = SUC (LENGTH sa.cs_current_insts)` by
    (gvs[emit_inst_def, fresh_id_def, emit_def, comp_bind_def,
         comp_ignore_bind_def, comp_return_def]) >>
  `op_taint tnf (Var out) = {} /\ tnf.t_mem = tn.t_mem /\
   tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans` by
    (simp[Abbr `tnf`, Abbr `t`] >> irule mload_ghost_clean >>
     simp[eval_operand_def]) >>
  simp[Abbr `t`, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >>
  simp[Abbr `Gf`, Abbr `tnf`, step_prov_def, set_prov_def,
       out_prov_def, step_taint_def, set_var_taint_def, mk_inst_def,
       op_taint_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE,
       venom_state_component_equality]
QED

(* Shared scalar rounding; the input may alias either output. *)
Theorem reason_round_scalar_ptr:
  emit_inst ADD [Var len;Lit 31w] [tmp] sa = ((),c1) /\
  emit_inst AND [Var tmp;Lit (i2w (-32))] [rounded] c1 = ((),sb) /\
  fn_has_code sa c1 func /\ fn_has_code c1 sb func /\
  ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  lookup_var len s = SOME n /\ op_taint tn (Var len) = {} ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    lookup_var rounded sf = SOME ((n + 31w) && i2w (-32)) /\
    op_taint tnf (Var rounded) = {} /\
    (sf with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
               vs_inst_idx := s.vs_inst_idx|>) = s /\
    sf.vs_allocas = s.vs_allocas /\
    sf.vs_memory = s.vs_memory /\ tnf.t_mem = tn.t_mem /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!p. p <> tmp /\ p <> rounded ==>
      lookup_var p sf = lookup_var p s /\
      FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  `eval_operand (Var len) s = SOME n /\
   eval_operand (Lit 31w) s = SOME 31w /\
   op_taint tn (Lit 31w) = {}` by simp[eval_operand_def, op_taint_def] >>
  drule_all (SRULE [] (Q.INST [`opc` |-> `ADD`, `f` |-> `word_add`]
    reason_copy_binop_resources_ptr)) >>
  disch_then (qspecl_then [`PG`, `G`, `D`] (qx_choose_then `G1`
    (qx_choose_then `tn1` (qx_choose_then `s1` strip_assume_tac)))) >>
  `eval_operand (Var tmp) s1 = SOME (n + 31w) /\
   eval_operand (Lit (i2w (-32))) s1 = SOME (i2w (-32)) /\
   op_taint tn1 (Lit (i2w (-32))) = {}` by simp[eval_operand_def, op_taint_def] >>
  drule_all (SRULE [] (Q.INST [`opc` |-> `AND`, `f` |-> `word_and`]
    reason_copy_binop_resources_ptr)) >>
  disch_then (qspecl_then [`PG`, `G1`, `D`] (qx_choose_then `G2`
    (qx_choose_then `tn2` (qx_choose_then `s2` strip_assume_tac)))) >>
  qexistsl_tac [`G2`, `tn2`, `s2`] >> conj_tac
  >- metis_tac[gas_path_ptr_then, ADD_CLAUSES] >>
  ` (s2 with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
               vs_inst_idx := s.vs_inst_idx|>) = s` by
    (irule reason_scratch_frame_trans >> qexists_tac `s1` >> gvs[]) >>
  simp[] >> rpt strip_tac >> metis_tac[]
QED

Theorem reason_load_round_ptr:
  emit_inst MLOAD [Var src] [len] sa = ((),c1) /\
  emit_inst ADD [Var len;Lit 31w] [tmp] c1 = ((),c2) /\
  emit_inst AND [Var tmp;Lit (i2w (-32))] [rounded] c2 = ((),sb) /\
  fn_has_code sa c1 func /\ fn_has_code c1 c2 func /\
  fn_has_code c2 sb func /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  lookup_var src s = SOME a /\ ptr_covers G tn src s 32 /\
  (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem) /\
  len <> tmp /\ len <> rounded ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    lookup_var len sf = SOME (mload (w2n a) s) /\
    op_taint tnf (Var len) = {} /\
    lookup_var rounded sf = SOME ((mload (w2n a) s + 31w) && i2w (-32)) /\
    op_taint tnf (Var rounded) = {} /\
    (sf with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
               vs_inst_idx := s.vs_inst_idx|>) = s /\
    sf.vs_allocas = s.vs_allocas /\
    sf.vs_memory = s.vs_memory /\ tnf.t_mem = tn.t_mem /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!p. p <> len /\ p <> tmp /\ p <> rounded ==>
      lookup_var p sf = lookup_var p s /\
      FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >> drule_all reason_copy_mload_resources_ptr >>
  disch_then (qspecl_then [`PG`, `D`] (qx_choose_then `G1`
    (qx_choose_then `tn1` (qx_choose_then `s1` strip_assume_tac)))) >>
  drule_all reason_round_scalar_ptr >>
  disch_then (qspecl_then [`PG`, `G1`, `D`] (qx_choose_then `G2`
    (qx_choose_then `tn2` (qx_choose_then `s2` strip_assume_tac)))) >>
  qexistsl_tac [`G2`, `tn2`, `s2`] >> conj_tac
  >- metis_tac[gas_path_ptr_then, ADD_CLAUSES] >>
  ` (s2 with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
               vs_inst_idx := s.vs_inst_idx|>) = s` by
    (irule reason_scratch_frame_trans >> qexists_tac `s1` >> gvs[]) >>
  simp[] >> rpt strip_tac >> metis_tac[]
QED

Theorem reason_copy_round_prefix_ptr:
  emit_inst MLOAD [Var src] [v1] sa = ((),c1) /\
  emit_inst ADD [Var v1;Lit 31w] [v2] c1 = ((),c2) /\
  emit_inst AND [Var v2;Lit (i2w (-32))] [v3] c2 = ((),c3) /\
  emit_inst ADD [Lit 32w;Var v3] [v4] c3 = ((),sb) /\
  fn_has_code sa c1 func /\ fn_has_code c1 c2 func /\
  fn_has_code c2 c3 func /\ fn_has_code c3 sb func /\
  ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  lookup_var src s = SOME a /\ ptr_covers G tn src s 32 /\
  (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem) ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    lookup_var v4 sf = SOME (32w + (mload (w2n a) s + 31w && i2w (-32))) /\
    op_taint tnf (Var v4) = {} /\
    (sf with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
               vs_inst_idx := s.vs_inst_idx|>) = s /\
    sf.vs_allocas = s.vs_allocas /\
    sf.vs_memory = s.vs_memory /\ tnf.t_mem = tn.t_mem /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!p. p <> v1 /\ p <> v2 /\ p <> v3 /\ p <> v4 ==>
      lookup_var p sf = lookup_var p s /\
      FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  drule_all reason_copy_mload_resources_ptr >>
  disch_then (qspecl_then [`PG`, `D`] (qx_choose_then `G1`
    (qx_choose_then `tn1` (qx_choose_then `s1` strip_assume_tac)))) >>
  drule_all reason_round_scalar_ptr >>
  disch_then (qspecl_then [`PG`, `G1`, `D`] (qx_choose_then `G3`
    (qx_choose_then `tn3` (qx_choose_then `s3` strip_assume_tac)))) >>
  `eval_operand (Var v3) s3 = SOME (mload (w2n a) s + 31w && i2w (-32)) /\
   eval_operand (Lit 32w) s3 = SOME 32w /\
   op_taint tn3 (Lit 32w) = {}` by simp[eval_operand_def, op_taint_def] >>
  drule_all (SRULE [] (Q.INST [`opc` |-> `ADD`, `f` |-> `word_add`]
    reason_copy_binop_resources_ptr)) >>
  disch_then (qspecl_then [`PG`, `G3`, `D`] (qx_choose_then `G4`
    (qx_choose_then `tn4` (qx_choose_then `s4` strip_assume_tac)))) >>
  qexistsl_tac [`G4`, `tn4`, `s4`] >>
  conj_tac >- suspend "path" >> suspend "resources"
QED

Resume reason_copy_round_prefix_ptr[path]:
  metis_tac[gas_path_ptr_then, ADD_CLAUSES]
QED

Resume reason_copy_round_prefix_ptr[resources]:
  ` (s3 with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
               vs_inst_idx := s.vs_inst_idx|>) = s` by
    (irule reason_scratch_frame_trans >> qexists_tac `s1` >> gvs[]) >>
  ` (s4 with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
               vs_inst_idx := s.vs_inst_idx|>) = s` by
    (irule reason_scratch_frame_trans >> qexists_tac `s3` >> gvs[]) >>
  simp[] >> rpt strip_tac >> metis_tac[]
QED

Finalise reason_copy_round_prefix_ptr

Theorem reason_tuple_copy_path_ptr:
  emit_inst MLOAD [Var src] [v1] sa = ((),c1) /\
  emit_inst ADD [Var v1;Lit 31w] [v2] c1 = ((),c2) /\
  emit_inst AND [Var v2;Lit (i2w (-32))] [v3] c2 = ((),c3) /\
  emit_inst ADD [Lit 32w;Var v3] [v4] c3 = ((),c4) /\
  emit_void MCOPY [Var dst;Var src;Var v4] c4 = ((),sb) /\
  fn_has_code sa c1 func /\ fn_has_code c1 c2 func /\
  fn_has_code c2 c3 func /\ fn_has_code c3 c4 func /\ fn_has_code c4 sb func /\
  ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  ptr_covers G tn src s n /\ ptr_covers G tn dst s n /\
  32 <= n /\ n = 32 + 32 * word_size len /\ n < dimword (:256) /\
  mload (w2n a) s = n2w len /\
  (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem) /\
  (!p. p = src \/ p = dst ==> p <> v1 /\ p <> v2 /\ p <> v3 /\ p <> v4) ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    sf = (s with <|vs_vars := sf.vs_vars; vs_memory := sf.vs_memory;
                  vs_inst_idx := sf.vs_inst_idx|>) /\
    sf.vs_allocas = s.vs_allocas /\
    sf.vs_memory = (mcopy (w2n b) (w2n a) n s).vs_memory /\
    tnf.t_mem = (tn.t_mem DIFF {i | w2n b <= i /\ i < w2n b + n}) UNION
      {w2n b + i | i < n /\ w2n a + i IN tn.t_mem} /\
    (!p k. p <> v1 /\ p <> v2 /\ p <> v3 /\ p <> v4 /\
      ptr_covers G tn p s k ==> ptr_covers Gf tnf p sf k) /\
    (!p. p <> v1 /\ p <> v2 /\ p <> v3 /\ p <> v4 ==>
      lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  `ptr_covers G tn src s 32` by
    (fs[ptr_covers_def] >> metis_tac[LESS_EQ_TRANS]) >>
  drule_all reason_copy_round_prefix_ptr >>
  disch_then (qspecl_then [`PG`, `D`] (qx_choose_then `G4`
    (qx_choose_then `tn4` (qx_choose_then `s4` strip_assume_tac)))) >>
  `lookup_var src s4 = SOME a /\ lookup_var dst s4 = SOME b /\
   ptr_covers G4 tn4 src s4 n /\ ptr_covers G4 tn4 dst s4 n` by
    (gvs[ptr_covers_def] >> metis_tac[]) >>
  `eval_operand (Var v4) s4 = SOME (n2w n)` by
    (qspec_then `len` mp_tac buffer_round_size >>
     gvs[eval_operand_def, WORD_ADD_COMM]) >>
  qabbrev_tac `t = mcopy (w2n b) (w2n a) n s4` >>
  qabbrev_tac `Gf = step_prov PG G4
    (mk_inst c4.cs_next_id MCOPY [Var dst;Var src;Var v4] []) t` >>
  qabbrev_tac `tnf = step_taint
    (mk_inst c4.cs_next_id MCOPY [Var dst;Var src;Var v4] []) s4 t tn4` >>
  qexistsl_tac [`Gf`, `tnf`, `t with vs_inst_idx := SUC s4.vs_inst_idx`] >>
  rpt conj_tac
  >- suspend "path"
  >- suspend "bb"
  >- suspend "index"
  >- suspend "halted"
  >- suspend "frame"
  >- suspend "allocas"
  >- suspend "memory"
  >- suspend "taint"
  >- suspend "coverage" >> suspend "variables"
QED

Resume reason_tuple_copy_path_ptr[path]:
  `gas_path_ptr D 0 ctx func PG G4 tn4 s4 0 Gf tnf
    (OK (t with vs_inst_idx := SUC s4.vs_inst_idx))` by
    (unabbrev_all_tac >>
     `eval_operand (Var src) s4 = SOME a /\
      eval_operand (Var dst) s4 = SOME b /\
      ptr_covers G4 tn4 src s4 (w2n (n2w n : bytes32)) /\
      ptr_covers G4 tn4 dst s4 (w2n (n2w n : bytes32))` by
       gvs[eval_operand_def] >>
     drule_all reason_mcopy_path_ptr >>
     disch_then (qspecl_then [`PG`, `D`] mp_tac) >> simp[]) >>
  metis_tac[gas_path_ptr_then, ADD_CLAUSES]
QED

Resume reason_tuple_copy_path_ptr[bb]:
  gvs[emit_void_def, emit_inst_def, fresh_id_def, emit_def, comp_bind_def,
      comp_ignore_bind_def, comp_return_def, Abbr `t`, mcopy_def,
      write_memory_with_expansion_def]
QED

Resume reason_tuple_copy_path_ptr[index]:
  gvs[emit_void_def, emit_inst_def, fresh_id_def, emit_def, comp_bind_def,
      comp_ignore_bind_def, comp_return_def]
QED

Resume reason_tuple_copy_path_ptr[halted]:
  simp[Abbr `t`, mcopy_def, write_memory_with_expansion_def]
QED

Resume reason_tuple_copy_path_ptr[frame]:
  qpat_x_assum `(_ with <|vs_vars := _; vs_memory := _; vs_inst_idx := _|>) = s` mp_tac >>
  simp[Abbr `t`, mcopy_def, write_memory_with_expansion_def,
       venom_state_component_equality]
QED

Resume reason_tuple_copy_path_ptr[allocas]:
  simp[Abbr `t`, mcopy_def, write_memory_with_expansion_def]
QED

Resume reason_tuple_copy_path_ptr[memory]:
  simp[Abbr `t`, mcopy_def, write_memory_with_expansion_def]
QED

Resume reason_tuple_copy_path_ptr[taint]:
  unabbrev_all_tac >>
  `n = w2n (n2w n : bytes32)` by simp[] >>
  qpat_x_assum `n = w2n _` (fn th => once_rewrite_tac [th]) >>
  qpat_x_assum `tn4.t_mem = tn.t_mem`
    (fn th => once_rewrite_tac [GSYM th]) >>
  irule (cj 5 mcopy_operand_ghost_frame) >> simp[eval_operand_def]
QED

Resume reason_tuple_copy_path_ptr[coverage]:
  rpt strip_tac >>
  `ptr_covers G4 tn4 p s4 k` by (gvs[ptr_covers_def] >> metis_tac[]) >>
  simp[ptr_covers_inst_idx] >> unabbrev_all_tac >>
  `n = w2n (n2w n : bytes32)` by simp[] >>
  qpat_x_assum `n = w2n _` (fn th => once_rewrite_tac [th]) >>
  irule reason_mcopy_live_covers >> simp[eval_operand_def]
QED

Resume reason_tuple_copy_path_ptr[variables]:
  `Gf = G4` by
    (unabbrev_all_tac >>
     `n = w2n (n2w n : bytes32)` by simp[] >>
     qpat_x_assum `n = w2n _` (fn th => once_rewrite_tac [th]) >>
     irule (cj 1 mcopy_operand_ghost_frame) >> simp[eval_operand_def]) >>
  `tnf.t_var = tn4.t_var` by
    (unabbrev_all_tac >>
     `n = w2n (n2w n : bytes32)` by simp[] >>
     qpat_x_assum `n = w2n _` (fn th => once_rewrite_tac [th]) >>
     irule (cj 2 mcopy_operand_ghost_frame) >> simp[eval_operand_def]) >>
  simp[Abbr `t`, mcopy_def, write_memory_with_expansion_def, lookup_var_def] >>
  rpt strip_tac >>
  qpat_x_assum `!p. p <> v1 /\ p <> v2 /\ p <> v3 /\ p <> v4 ==> _`
    (qspec_then `p` mp_tac) >> simp[op_taint_def, lookup_var_def]
QED

Finalise reason_tuple_copy_path_ptr

(* Public resource corollary of the exact memory/taint postconditions above.
   It is type-generic so other checked encoders can reuse the same boundary. *)
Theorem reason_tuple_copy_resources_ptr:
  ptr_mem_ok cx ty v op G tn s /\
  evaluate_type (get_tenv cx) ty = SOME tv /\
  eval_operand op s = SOME a /\ val_wf tv v /\
  val_store_size tv v <= n /\
  sf.vs_memory = (mcopy (w2n b) (w2n a) n s).vs_memory /\
  tnf.t_mem = (tn.t_mem DIFF {i | w2n b <= i /\ i < w2n b + n}) UNION
    {w2n b + i | i < n /\ w2n a + i IN tn.t_mem} ==>
  !mem. mem_agree_outside tnf.t_mem sf.vs_memory mem ==>
    val_in_memory tv v (w2n b) mem
Proof
  strip_tac >>
  `val_footprint tv v <= n` by
    metis_tac[val_footprint_le_store_size, LESS_EQ_TRANS] >>
  `!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
    val_in_memory tv v (w2n a) mem` by fs[ptr_mem_ok_def] >>
  rpt strip_tac >> irule robust_val_in_memory_copy_transport >>
  conj_tac >- simp[] >>
  qexistsl_tac [`s.vs_memory`, `sf.vs_memory`, `n`, `w2n a`,
    `tn.t_mem`, `tnf.t_mem`] >>
  simp[mcopy_mem_bytes_at_same, IN_DIFF, IN_UNION, GSPECIFICATION]
QED
