Theory extRetBytesCopyCountedPtr
Ancestors
  extRetScalarCopyCountedPtr extRetCopyCountedPtr typedCopyPtr
  fragGasSeqPtr fragGasPathPtr fragExec fragExecPtr
  venomExecSemantics venomInstProofs venomInst venomState
  ptrSafeRun ptrDiscipline bodyPtrDefs finite_map context compileEnv emitHelper
  arithmetic exprSimBufferStore wordLoadStorePtr
(* An emitted, nonterminating, non-GAS instruction is one zero-count edge.
   The semantic and pointer premises are discharged for each concrete opcode
   below; this is not a conversion from a fixed-run fragment. *)
Theorem emitted_step_counted_ptr:
  fn_has_code sa sb fn /\
  sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_current_insts = sa.cs_current_insts ++ [inst] /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  inst.inst_opcode <> INVOKE /\ inst.inst_opcode <> GAS /\
  ~is_terminator inst.inst_opcode /\
  ptr_inst_ok D lo 0 ctx fn G tn inst s /\
  step_inst_base inst s = OK t ==>
  gas_path_ptr D lo ctx fn PG G tn s 0
    (step_prov PG G inst t) (step_taint inst s t tn)
    (OK (t with vs_inst_idx := SUC s.vs_inst_idx))
Proof
  strip_tac >> drule_all fn_has_code_same_block >> strip_tac >>
  `get_instruction bb s.vs_inst_idx = SOME inst` by
    (qpat_x_assum `!i. _` (qspec_then `0` mp_tac) >> simp[]) >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` by simp[] >>
  drule_all straight_line_ptr_edge >> simp[] >>
  disch_then (qspec_then `PG` assume_tac) >>
  drule (cj 2 gas_path_ptr_rules) >>
  disch_then (qspec_then `0` mp_tac) >> simp[] >>
  disch_then irule >> irule (cj 1 gas_path_ptr_rules) >>
  simp[] >> metis_tac[step_preserves_halted, step_inst_non_invoke]
QED

Theorem emit_copy_len_binop_ambient_counted_ptr:
  (opc = ADD /\ f = word_add \/ opc = AND /\ f = word_and) /\
  emit_op opc [left;right] sa = (Var out,sb) /\
  fn_has_code sa sb fn /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\
  eval_operand left s = SOME a /\ eval_operand right s = SOME b /\
  op_taint tn left = {} /\ op_taint tn right = {} ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    lookup_var out sf = SOME (f a b) /\ op_taint tnf (Var out) = {} /\
    sf.vs_allocas = s.vs_allocas /\ sf.vs_alloca_next = s.vs_alloca_next /\
    sf.vs_fmp = s.vs_fmp /\
    sf.vs_memory = s.vs_memory /\ tnf.t_mem = tn.t_mem /\
    tnf.t_imm = tn.t_imm /\ sf.vs_accounts = s.vs_accounts /\
    sf.vs_transient = s.vs_transient /\ sf.vs_call_ctx = s.vs_call_ctx /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!p. not_fresh_at sa p ==>
      lookup_var p sf = lookup_var p s /\
      FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++
     [mk_inst sa.cs_next_id opc [left;right] [out]] /\
   (!p. not_fresh_at sa p ==> p <> out)` by
    (gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
         fresh_id_def, emit_def, comp_return_def, not_fresh_at_def] >>
     metis_tac[LESS_EQ_REFL]) >>
  `opc <> GAS /\ opc <> INVOKE /\ ~is_terminator opc` by
    gvs[is_terminator_def] >>
  qabbrev_tac `t = update_var out (f a b) s` >>
  qabbrev_tac `Gf = step_prov PG G
    (mk_inst sa.cs_next_id opc [left;right] [out]) t` >>
  qabbrev_tac `tnf = step_taint
    (mk_inst sa.cs_next_id opc [left;right] [out]) s t tn` >>
  qexistsl_tac [`Gf`, `tnf`, `t with vs_inst_idx := SUC s.vs_inst_idx`] >>
  conj_tac >-
    (qunabbrev_tac `Gf` >> qunabbrev_tac `tnf` >>
     irule emitted_step_counted_ptr >>
     simp[mk_inst_def, is_terminator_def] >>
     conj_tac >-
       (gvs[] >> pure_once_rewrite_tac[step_inst_base_def] >>
        simp_tac (srw_ss()) [mk_inst_def] >>
        simp[exec_pure2_def, Abbr `t`]) >>
     conj_tac >- (qexistsl_tac [`sa`, `sb`] >> simp[mk_inst_def]) >>
     irule (SRULE [mk_inst_def] ptr_inst_ok_copy_len_binop) >> metis_tac[]) >>
  `tnf.t_imm = tn.t_imm` by
    (gvs[] >> simp[Abbr `tnf`, step_taint_def, imm_taint_def, mk_inst_def]) >>
  gvs[] >> simp[Abbr `t`, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  simp[Abbr `tnf`, Abbr `Gf`,
       copy_len_binop_ghost_frame |> SPEC_ALL |> Q.INST [`opc` |-> `ADD`] |> SRULE [],
       copy_len_binop_ghost_frame |> SPEC_ALL |> Q.INST [`opc` |-> `AND`] |> SRULE []] >>
  rpt strip_tac >> `p <> out` by metis_tac[] >>
  simp[copy_len_binop_ghost_frame, lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED

Theorem emit_copy_len_binop_counted_ptr:
  (opc = ADD /\ f = word_add \/ opc = AND /\ f = word_and) /\
  emit_op opc [left;right] sa = (Var out,sb) /\
  fn_has_code sa sb fn /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\
  eval_operand left s = SOME a /\ eval_operand right s = SOME b /\
  op_taint tn left = {} /\ op_taint tn right = {} ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    lookup_var out sf = SOME (f a b) /\ op_taint tnf (Var out) = {} /\
    sf.vs_allocas = s.vs_allocas /\ sf.vs_alloca_next = s.vs_alloca_next /\
    sf.vs_fmp = s.vs_fmp /\
    sf.vs_memory = s.vs_memory /\ tnf.t_mem = tn.t_mem /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!p. not_fresh_at sa p ==>
      lookup_var p sf = lookup_var p s /\
      FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all emit_copy_len_binop_ambient_counted_ptr >>
  disch_then (qspecl_then [`PG`, `G`, `D`] strip_assume_tac) >>
  qexistsl_tac [`Gf`, `tnf`, `sf`] >> simp[]
QED

Theorem emit_mload_clean_ambient_counted_ptr:
  emit_op MLOAD [Var src] sa = (Var out,sb) /\
  fn_has_code sa sb fn /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\
  ptr_covers G tn src s 32 /\ lookup_var src s = SOME a /\
  (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem) ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    lookup_var out sf = SOME (mload (w2n a) s) /\ op_taint tnf (Var out) = {} /\
    op_prov Gf (Var out) = NONE /\
    sf.vs_allocas = s.vs_allocas /\ sf.vs_alloca_next = s.vs_alloca_next /\
    sf.vs_fmp = s.vs_fmp /\
    sf.vs_memory = s.vs_memory /\ tnf.t_mem = tn.t_mem /\
    tnf.t_imm = tn.t_imm /\ sf.vs_accounts = s.vs_accounts /\
    sf.vs_transient = s.vs_transient /\ sf.vs_call_ctx = s.vs_call_ctx /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!p. not_fresh_at sa p ==>
      lookup_var p sf = lookup_var p s /\
      FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++
     [mk_inst sa.cs_next_id MLOAD [Var src] [out]] /\
   (!p. not_fresh_at sa p ==> p <> out)` by
    (gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
         fresh_id_def, emit_def, comp_return_def, not_fresh_at_def] >>
     metis_tac[LESS_EQ_REFL]) >>
  qabbrev_tac `t = update_var out (mload (w2n a) s) s` >>
  qabbrev_tac `Gf = step_prov PG G
    (mk_inst sa.cs_next_id MLOAD [Var src] [out]) t` >>
  qabbrev_tac `tnf = step_taint
    (mk_inst sa.cs_next_id MLOAD [Var src] [out]) s t tn` >>
  qexistsl_tac [`Gf`, `tnf`, `t with vs_inst_idx := SUC s.vs_inst_idx`] >>
  conj_tac >-
    (qunabbrev_tac `Gf` >> qunabbrev_tac `tnf` >>
     irule emitted_step_counted_ptr >> simp[mk_inst_def, is_terminator_def] >>
     conj_tac >-
       (pure_once_rewrite_tac[step_inst_base_def] >>
        simp[mk_inst_def, exec_read1_def, eval_operand_def, Abbr `t`]) >>
     conj_tac >- (qexistsl_tac [`sa`, `sb`] >> simp[mk_inst_def]) >>
     irule (SRULE [mk_inst_def] ptr_inst_ok_mload) >> simp[]) >>
  `op_taint tnf (Var out) = {} /\ tnf.t_mem = tn.t_mem /\
   tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans` by
    (simp[Abbr `tnf`, Abbr `t`] >> irule mload_ghost_clean >>
     simp[eval_operand_def]) >>
  `tnf.t_imm = tn.t_imm` by
    simp[Abbr `tnf`, step_taint_def, imm_taint_def, mk_inst_def] >>
  simp[Abbr `t`, update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  conj_tac >-
    simp[Abbr `Gf`, op_prov_def, step_prov_def, set_prov_def,
         out_prov_def, mk_inst_def, FLOOKUP_DRESTRICT] >>
  rpt strip_tac >> `p <> out` by metis_tac[] >>
  simp[Abbr `Gf`, Abbr `tnf`, step_prov_def, set_prov_def,
       out_prov_def, step_taint_def, set_var_taint_def, mk_inst_def,
       op_taint_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE]
QED

Theorem emit_mload_clean_counted_ptr:
  emit_op MLOAD [Var src] sa = (Var out,sb) /\
  fn_has_code sa sb fn /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\
  ptr_covers G tn src s 32 /\ lookup_var src s = SOME a /\
  (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem) ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    lookup_var out sf = SOME (mload (w2n a) s) /\ op_taint tnf (Var out) = {} /\
    op_prov Gf (Var out) = NONE /\
    sf.vs_allocas = s.vs_allocas /\ sf.vs_alloca_next = s.vs_alloca_next /\
    sf.vs_fmp = s.vs_fmp /\
    sf.vs_memory = s.vs_memory /\ tnf.t_mem = tn.t_mem /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!p. not_fresh_at sa p ==>
      lookup_var p sf = lookup_var p s /\
      FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >> drule_all emit_mload_clean_ambient_counted_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`Gf`, `tnf`, `sf`] >> simp[]
QED

Theorem compile_bytestring_copy_len_counted_ptr:
  compile_bytestring_copy_len (Var src) sa = (count_op,sb) /\
  fn_has_code sa sb fn /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\
  ptr_covers G tn src s 32 /\ lookup_var src s = SOME a /\
  (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem) ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    eval_operand count_op sf = SOME ((mload (w2n a) s + 31w && i2w (-32)) + 32w) /\
    op_taint tnf count_op = {} /\
    sf.vs_allocas = s.vs_allocas /\ sf.vs_alloca_next = s.vs_alloca_next /\
    sf.vs_fmp = s.vs_fmp /\
    sf.vs_memory = s.vs_memory /\ tnf.t_mem = tn.t_mem /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!p. not_fresh_at sa p ==>
      lookup_var p sf = lookup_var p s /\
      FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  qpat_x_assum `compile_bytestring_copy_len _ _ = _` mp_tac >>
  simp[compile_bytestring_copy_len_def, comp_bind_def] >>
  ntac 3 (pairarg_tac >> simp[LET_THM, pairTheory.pair_case_def]) >>
  strip_tac >>
  `?v1. src_len = Var v1` by
    gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
        fresh_id_def, emit_def, comp_return_def] >>
  `?v2. padded_len = Var v2` by
    gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
        fresh_id_def, emit_def, comp_return_def] >>
  `?v3. rounded = Var v3` by
    gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
        fresh_id_def, emit_def, comp_return_def] >>
  `?v4. count_op = Var v4` by
    gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
        fresh_id_def, emit_def, comp_return_def] >>
  gvs[] >>
  rename1 `emit_op MLOAD [Var src] sa = (Var v1,sc1)` >>
  rename1 `emit_op ADD [Var v1; Lit 31w] sc1 = (Var v2,sc2)` >>
  rename1 `emit_op AND [Var v2; Lit (i2w (-32))] sc2 = (Var v3,sc3)` >>
  `cs_extends sa sc1 /\ cs_extends sc1 sc2 /\
   cs_extends sc2 sc3 /\ cs_extends sc3 sb` by
    (imp_res_tac exprLoweringPropsTheory.emit_op_extends >>
     fs[cs_extends_def, exprLoweringPropsTheory.same_blocks_def] >>
     rpt conj_tac >> qexists_tac `[]` >> simp[]) >>
  `fn_has_code sa sc1 fn /\ fn_has_code sc1 sc2 fn /\
   fn_has_code sc2 sc3 fn /\ fn_has_code sc3 sb fn` by
    metis_tac[fn_has_code_split, cs_extends_trans] >>
  drule_all emit_mload_clean_ambient_counted_ptr >>
  disch_then (qspecl_then [`PG`, `D`] (qx_choose_then `G1` (qx_choose_then `tn1` (qx_choose_then `s1` strip_assume_tac)))) >>
  `eval_operand (Var v1) s1 = SOME (mload (w2n a) s) /\
   eval_operand (Lit 31w) s1 = SOME 31w /\ op_taint tn1 (Lit 31w) = {}` by
    simp[eval_operand_def, op_taint_def] >>
  drule_all (SRULE [] (Q.INST [`opc` |-> `ADD`, `f` |-> `word_add`] emit_copy_len_binop_counted_ptr)) >>
  disch_then (qspecl_then [`PG`, `G1`, `D`] (qx_choose_then `G2` (qx_choose_then `tn2` (qx_choose_then `s2` strip_assume_tac)))) >>
  `eval_operand (Var v2) s2 = SOME (mload (w2n a) s + 31w) /\
   eval_operand (Lit (i2w (-32))) s2 = SOME (i2w (-32)) /\
   op_taint tn2 (Lit (i2w (-32))) = {}` by simp[eval_operand_def, op_taint_def] >>
  drule_all (SRULE [] (Q.INST [`opc` |-> `AND`, `f` |-> `word_and`] emit_copy_len_binop_counted_ptr)) >>
  disch_then (qspecl_then [`PG`, `G2`, `D`] (qx_choose_then `G3` (qx_choose_then `tn3` (qx_choose_then `s3` strip_assume_tac)))) >>
  `eval_operand (Var v3) s3 = SOME (mload (w2n a) s + 31w && i2w (-32)) /\
   eval_operand (Lit 32w) s3 = SOME 32w /\ op_taint tn3 (Lit 32w) = {}` by
    simp[eval_operand_def, op_taint_def] >>
  drule_all (SRULE [] (Q.INST [`opc` |-> `ADD`, `f` |-> `word_add`] emit_copy_len_binop_counted_ptr)) >>
  disch_then (qspecl_then [`PG`, `G3`, `D`] (qx_choose_then `G4` (qx_choose_then `tn4` (qx_choose_then `s4` strip_assume_tac)))) >>
  qexistsl_tac [`G4`, `tn4`, `s4`] >>
  conj_tac >-
    (irule (SRULE [] (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_path_ptr_then)) >>
     qexistsl_tac [`G1`, `s1`, `tn1`] >> simp[] >>
     irule (SRULE [] (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_path_ptr_then)) >>
     qexistsl_tac [`G2`, `s2`, `tn2`] >> simp[] >>
     irule (SRULE [] (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_path_ptr_then)) >>
     qexistsl_tac [`G3`, `s3`, `tn3`] >> simp[]) >>
  `!p. not_fresh_at sa p ==> not_fresh_at sc1 p /\
       not_fresh_at sc2 p /\ not_fresh_at sc3 p` by
    (gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
         fresh_id_def, emit_def, comp_return_def, not_fresh_at_def] >>
     rpt strip_tac >> decide_tac) >>
  simp[eval_operand_def] >> gen_tac >> strip_tac >>
  `not_fresh_at sc1 p /\ not_fresh_at sc2 p /\ not_fresh_at sc3 p` by metis_tac[] >>
  qpat_x_assum `!p. not_fresh_at sa p ==> _` (qspec_then `p` mp_tac) >>
  qpat_x_assum `!p. not_fresh_at sc1 p ==> _` (qspec_then `p` mp_tac) >>
  qpat_x_assum `!p. not_fresh_at sc2 p ==> _` (qspec_then `p` mp_tac) >>
  qpat_x_assum `!p. not_fresh_at sc3 p ==> _` (qspec_then `p` mp_tac) >> simp[]
QED

Theorem emit_mcopy_ambient_counted_ptr:
  emit_void MCOPY [Var dst;Var src;count_op] sa = ((),sb) /\
  fn_has_code sa sb fn /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  eval_operand count_op s = SOME n /\ op_taint tn count_op = {} /\
  ptr_covers G tn src s (w2n n) /\ ptr_covers G tn dst s (w2n n) ==>
  ?tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    sf.vs_allocas = s.vs_allocas /\ sf.vs_alloca_next = s.vs_alloca_next /\
    sf.vs_fmp = s.vs_fmp /\
    sf.vs_memory = (mcopy (w2n b) (w2n a) (w2n n) s).vs_memory /\
    tnf.t_mem = (tn.t_mem DIFF {i | w2n b <= i /\ i < w2n b + w2n n}) UNION
      {w2n b + i | i < w2n n /\ w2n a + i IN tn.t_mem} /\
    tnf.t_imm = tn.t_imm /\ sf.vs_accounts = s.vs_accounts /\
    sf.vs_transient = s.vs_transient /\ sf.vs_call_ctx = s.vs_call_ctx /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!p. lookup_var p sf = lookup_var p s /\
         op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++
     [mk_inst sa.cs_next_id MCOPY [Var dst;Var src;count_op] []]` by
    gvs[emit_void_def, comp_bind_def, comp_ignore_bind_def,
        fresh_id_def, emit_def, comp_return_def] >>
  qabbrev_tac `inst = mk_inst sa.cs_next_id MCOPY [Var dst;Var src;count_op] []` >>
  qabbrev_tac `t = mcopy (w2n b) (w2n a) (w2n n) s` >>
  qabbrev_tac `tnf = step_taint inst s t tn` >>
  `step_prov PG G inst t = G /\ tnf.t_var = tn.t_var /\
   tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
   tnf.t_mem = (tn.t_mem DIFF {i | w2n b <= i /\ i < w2n b + w2n n}) UNION
      {w2n b + i | i < w2n n /\ w2n a + i IN tn.t_mem}` by
    (qunabbrev_tac `tnf` >> qunabbrev_tac `inst` >> qunabbrev_tac `t` >>
     match_mp_tac mcopy_operand_ghost_frame >> simp[eval_operand_def]) >>
  qexistsl_tac [`tnf`, `t with vs_inst_idx := SUC s.vs_inst_idx`] >>
  conj_tac >-
    (`gas_path_ptr D 0 ctx fn PG G tn s 0 (step_prov PG G inst t) tnf
        (OK (t with vs_inst_idx := SUC s.vs_inst_idx))` suffices_by simp[] >>
     qunabbrev_tac `tnf` >> irule emitted_step_counted_ptr >>
     simp[Abbr `inst`, mk_inst_def, is_terminator_def] >>
     conj_tac >-
       (pure_once_rewrite_tac[step_inst_base_def] >>
        simp[Abbr `t`, mk_inst_def, eval_operand_def]) >>
     conj_tac >- (qexistsl_tac [`sa`, `sb`] >> simp[mk_inst_def]) >>
     irule (SRULE [mk_inst_def] ptr_inst_ok_mcopy_operand) >> simp[eval_operand_def]) >>
  simp[Abbr `t`, mcopy_def, write_memory_with_expansion_def,
       Abbr `tnf`, Abbr `inst`, step_taint_def, imm_taint_def, mk_inst_def,
       lookup_var_def, op_taint_def]
QED

Theorem emit_mcopy_counted_ptr:
  emit_void MCOPY [Var dst;Var src;count_op] sa = ((),sb) /\
  fn_has_code sa sb fn /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  eval_operand count_op s = SOME n /\ op_taint tn count_op = {} /\
  ptr_covers G tn src s (w2n n) /\ ptr_covers G tn dst s (w2n n) ==>
  ?tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 G tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    sf.vs_allocas = s.vs_allocas /\ sf.vs_alloca_next = s.vs_alloca_next /\
    sf.vs_fmp = s.vs_fmp /\
    sf.vs_memory = (mcopy (w2n b) (w2n a) (w2n n) s).vs_memory /\
    tnf.t_mem = (tn.t_mem DIFF {i | w2n b <= i /\ i < w2n b + w2n n}) UNION
      {w2n b + i | i < w2n n /\ w2n a + i IN tn.t_mem} /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!p. lookup_var p sf = lookup_var p s /\
         op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >> drule_all emit_mcopy_ambient_counted_ptr >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  qexistsl_tac [`tnf`, `sf`] >> simp[]
QED

Theorem compile_store_bytestring_counted_ptr:
  compile_store_bytestring (Var src) (Var dst) sa = ((),sb) /\
  fn_has_code sa sb fn /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ not_fresh_at sa src /\ not_fresh_at sa dst /\
  lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
  n = 32 + 32 * ((len + 31) DIV 32) /\
  len + 31 < dimword(:256) /\ n < dimword(:256) /\
  mload (w2n a) s = n2w len /\
  ptr_covers G tn src s n /\ ptr_covers G tn dst s n /\
  (!i. w2n a <= i /\ i < w2n a + 32 ==> i NOTIN tn.t_mem) ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    sf.vs_memory = (mcopy (w2n b) (w2n a) n s).vs_memory /\
    (!i. ~(w2n b <= i /\ i < w2n b + n) ==>
      mem_bytes_at i 1 sf.vs_memory = mem_bytes_at i 1 s.vs_memory) /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    (!i. i < n ==> (w2n b + i IN tnf.t_mem <=> w2n a + i IN tn.t_mem)) /\
    (!i. ~(w2n b <= i /\ i < w2n b + n) ==>
      (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
    (!p. not_fresh_at sa p ==>
      lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
      op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  strip_tac >>
  qpat_x_assum `compile_store_bytestring _ _ _ = _` mp_tac >>
  simp[compile_store_bytestring_def, comp_bind_def] >>
  pairarg_tac >> simp[LET_THM, pairTheory.pair_case_def] >> strip_tac >>
  rename1 `compile_bytestring_copy_len (Var src) sa = (count_op,sc)` >>
  `cs_extends sa sc /\ cs_extends sc sb` by
    (qpat_x_assum `compile_bytestring_copy_len _ _ = _` mp_tac >>
     qpat_x_assum `emit_void _ _ _ = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[compile_bytestring_copy_len_def, emit_op_def,
          emit_void_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
          fresh_id_def, emit_def, comp_return_def, LET_THM, pairTheory.pair_case_def] >>
     rpt strip_tac >> gvs[] >> rewrite_tac[cs_extends_def] >>
     qexists_tac `[]` >> simp[] >>
     pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC] >>
     simp[rich_listTheory.IS_PREFIX_APPEND]) >>
  `fn_has_code sa sc fn /\ fn_has_code sc sb fn` by
    metis_tac[fn_has_code_split] >>
  `ptr_covers G tn src s 32` by
    (fs[ptr_covers_def] >> metis_tac[LESS_EQ_TRANS, LESS_EQ_ADD]) >>
  drule_all compile_bytestring_copy_len_counted_ptr >>
  disch_then (qspecl_then [`PG`, `D`]
    (qx_choose_then `G1` (qx_choose_then `tn1` (qx_choose_then `s1` strip_assume_tac)))) >>
  `eval_operand count_op s1 = SOME (n2w n)` by
    (fs[] >> qspec_then `len` mp_tac buffer_round_size >>
     simp[vfmConstantsTheory.word_size_def]) >>
  `lookup_var src s1 = SOME a /\ lookup_var dst s1 = SOME b /\
   ptr_covers G1 tn1 src s1 n /\ ptr_covers G1 tn1 dst s1 n` by
    (qpat_assum `!p. not_fresh_at sa p ==> _` (qspec_then `src` strip_assume_tac) >>
     qpat_assum `!p. not_fresh_at sa p ==> _` (qspec_then `dst` strip_assume_tac) >>
     gvs[ptr_covers_def] >> metis_tac[]) >>
  `ptr_covers G1 tn1 src s1 (w2n (n2w n : bytes32)) /\
   ptr_covers G1 tn1 dst s1 (w2n (n2w n : bytes32))` by
    (gvs[wordsTheory.w2n_n2w, LESS_MOD]) >>
  drule_all emit_mcopy_counted_ptr >>
  disch_then (qspecl_then [`PG`, `D`]
    (qx_choose_then `tn2` (qx_choose_then `s2` strip_assume_tac))) >>
  qexistsl_tac [`G1`, `tn2`, `s2`] >>
  conj_tac >-
    (irule (SRULE [] (Q.INST [`n` |-> `0`, `m` |-> `0`] gas_path_ptr_then)) >>
     qexistsl_tac [`G1`, `s1`, `tn1`] >> simp[]) >>
  gvs[wordsTheory.w2n_n2w, LESS_MOD] >>
  conj_tac >-
    simp[mcopy_def, read_memory_def, write_memory_with_expansion_def, write_memory_def] >>
  conj_tac >-
    (gen_tac >> disch_tac >>
     `mem_bytes_at i 1 (mcopy (w2n b) (w2n a) (32 * ((len + 31) DIV 32) + 32) s1).vs_memory =
      mem_bytes_at i 1 s1.vs_memory` by
       (irule buffer_mcopy_exterior >> decide_tac) >> gvs[]) >>
  simp[] >> rpt strip_tac >> eq_tac >> strip_tac >> gvs[] >> decide_tac
QED
