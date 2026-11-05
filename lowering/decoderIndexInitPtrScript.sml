Theory decoderIndexInitPtr
Ancestors
  abiDecoderIndexInit abiDecoderAllocation allocationPtr typedCopyPtr fragExecPtr
  bodyPtrDefs ptrDiscipline ptrSafeRun compileEnv context emitHelper emitHelperProps
  loweringHalt localPtrsProps exprLoweringProps venomExecSemantics venomMemProps venomState venomInst finite_map
  words list rich_list arithmetic pred_set instIdxIndep

Theorem budget_alloca_observations[local]:
  abi_decoder_budget first last b cap s /\ id IN abi_decoder_ids first last /\
  step_inst_base (mk_inst id ALLOCA [Lit 32w] [out]) s = OK t ==>
  ?p. lookup_var out t = SOME (n2w p) /\ b <= p /\ p + 32 <= b + cap /\
    p + 32 < dimword (:256) /\
    t.vs_current_bb = s.vs_current_bb /\ t.vs_halted = s.vs_halted /\
    ptr_covers (step_prov PG G (mk_inst id ALLOCA [Lit 32w] [out]) t)
      (step_taint (mk_inst id ALLOCA [Lit 32w] [out]) s t tn) out t 32 /\
    (step_taint (mk_inst id ALLOCA [Lit 32w] [out]) s t tn).t_stor = tn.t_stor /\
    (step_taint (mk_inst id ALLOCA [Lit 32w] [out]) s t tn).t_trans = tn.t_trans /\
    (!x. x <> out ==> lookup_var x t = lookup_var x s /\
      FLOOKUP (step_prov PG G (mk_inst id ALLOCA [Lit 32w] [out]) t) x = FLOOKUP G x /\
      op_taint (step_taint (mk_inst id ALLOCA [Lit 32w] [out]) s t tn) (Var x) =
        op_taint tn (Var x))
Proof
  strip_tac >>
  `exec_alloca (mk_inst id ALLOCA [Lit 32w] [out]) s (32w:bytes32) = OK t` by
    (qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
     simp[Once step_inst_base_def, mk_inst_def, eval_operand_def]) >>
  drule abi_decoder_alloca32 >>
  disch_then (qspecl_then [`out`, `mk_inst id ALLOCA [Lit 32w] [out]`] mp_tac) >>
  simp[mk_inst_def] >> strip_tac >> gvs[] >>
  `p + 32 < dimword (:256)` by
    (drule abi_decoder_budget_word_bound >> decide_tac) >>
  qexists_tac `p` >> simp[] >>
  Cases_on `FLOOKUP s.vs_allocas id`
  >- (`s.vs_alloca_next + 32 < dimword (:256)` by
        (drule_all abi_decoder_missing_credit >> strip_tac >>
         qpat_x_assum `abi_decoder_budget first last b cap s` mp_tac >>
         simp_tac bool_ss [abi_decoder_budget_def] >> strip_tac >> decide_tac) >>
      `32 < dimword (:256)` by simp[] >>
      drule_all fresh_alloca_ptr_covers >>
      disch_then (qspecl_then [`PG`,`G`,`tn`,`out`,`32`] strip_assume_tac) >>
      drule_all fresh_alloca_ghost >>
      disch_then (qspecl_then [`PG`,`G`,`tn`] strip_assume_tac) >>
      drule step_alloca_fresh >> disch_then (qspec_then `32` mp_tac) >>
      simp[] >> disch_then (qspec_then `out` mp_tac) >>
      strip_tac >> gvs[mk_inst_def] >>
      gvs[update_var_def, lookup_var_def, FLOOKUP_UPDATE, op_taint_def]) >>
  rename1 `FLOOKUP s.vs_allocas id = SOME site` >> PairCases_on `site` >>
  `site1 = 32 /\ site0 + 32 < dimword (:256)` by
    (qpat_x_assum `abi_decoder_budget first last b cap s` mp_tac >>
     simp_tac bool_ss [abi_decoder_budget_def] >> strip_tac >>
     qpat_x_assum `!id off sz. _ ==> sz = 32 /\ _` drule >> disch_then drule >> strip_tac >> decide_tac) >>
  gvs[] >> drule reused_alloca_step >> disch_then (qspec_then `out` mp_tac) >>
  strip_tac >> gvs[] >>
  drule_all reused_alloca_ptr_covers >>
  disch_then (qspecl_then [`out`,`PG`,`G`,`tn`,`out`,`32`] strip_assume_tac) >>
  drule reused_alloca_ghost >>
  disch_then (qspecl_then [`out`,`PG`,`G`,`tn`] strip_assume_tac) >>
  gvs[mk_inst_def] >>
  gvs[update_var_def, lookup_var_def, FLOOKUP_UPDATE, op_taint_def]
QED

Theorem budget_alloca_mem_difference[local]:
  abi_decoder_budget first last b cap s /\ id IN abi_decoder_ids first last /\
  step_inst_base (mk_inst id ALLOCA [Lit 32w] [out]) s = OK t /\
  lookup_var out t = SOME (n2w p) /\ p + 32 < dimword (:256) ==>
  (step_taint (mk_inst id ALLOCA [Lit 32w] [out]) s t tn).t_mem DIFF
    {a | p <= a /\ a < p + 32} = tn.t_mem DIFF {a | p <= a /\ a < p + 32}
Proof
  strip_tac >>
  `32 < dimword (:256)` by simp[] >>
  Cases_on `FLOOKUP s.vs_allocas id`
  >- (`s.vs_alloca_next + 32 < dimword (:256)` by
        (drule_all abi_decoder_missing_credit >> strip_tac >>
         qpat_x_assum `abi_decoder_budget first last b cap s` mp_tac >>
         simp_tac bool_ss [abi_decoder_budget_def] >> strip_tac >> decide_tac) >>
      drule_all fresh_alloca_ghost >>
      disch_then (qspecl_then [`ARB`,`FEMPTY`,`tn`] strip_assume_tac) >>
      drule step_alloca_fresh >> disch_then (qspec_then `32` mp_tac) >>
      simp[] >> disch_then (qspec_then `out` mp_tac) >> strip_tac >>
      gvs[lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
      `s.vs_alloca_next < dimword (:256)` by decide_tac >>
      simp[] >> SET_TAC[]) >>
  rename1 `FLOOKUP s.vs_allocas id = SOME site` >> PairCases_on `site` >>
  `site1 = 32` by
    (qpat_x_assum `abi_decoder_budget first last b cap s` mp_tac >>
     simp_tac bool_ss [abi_decoder_budget_def] >> metis_tac[]) >>
  gvs[] >> drule reused_alloca_step >> disch_then (qspec_then `out` mp_tac) >>
  strip_tac >> gvs[] >> drule reused_alloca_ghost >>
  disch_then (qspecl_then [`out`,`ARB`,`FEMPTY`,`tn`] strip_assume_tac) >>
  gvs[]
QED

Theorem budget_alloca_endpoint_exact_ptr[local]:
  emit_op ALLOCA [Lit 32w] sa = (ip,sb) /\
  abi_decoder_budget first last b cap s /\ sa.cs_next_id IN abi_decoder_ids first last /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  ?H u q p. ip = Var q /\ lookup_var q t = SOME (n2w p) /\
    b <= p /\ p + 32 <= b + cap /\ p + 32 < dimword (:256) /\
    ptr_covers H u q (t with vs_inst_idx := SUC s.vs_inst_idx) 32 /\
    frag_exec_ptr cx ctx PG sa sb
      (\g z v. g = G /\ z = tn /\ v = s)
      (\g z v. g = H /\ z = u /\ v = (t with vs_inst_idx := SUC s.vs_inst_idx)) R /\
    u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\
    u.t_mem DIFF {a | p <= a /\ a < p + 32} =
      tn.t_mem DIFF {a | p <= a /\ a < p + 32} /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> drule emitted_insts_emit_op >> strip_tac >>
  qpat_x_assum `run_inst_seq _ _ = _` mp_tac >>
  simp[run_inst_seq_def, AllCaseEqs()] >> strip_tac >>
  `sb.cs_next_id = sa.cs_next_id + 1 /\ sb.cs_current_bb = sa.cs_current_bb` by
    (qpat_x_assum `emit_op _ _ _ = _` mp_tac >>
     simp[emit_op_def, fresh_var_def, fresh_id_def, emit_def, comp_bind_def,
       comp_ignore_bind_def, comp_return_def] >> strip_tac >> gvs[]) >>
  drule_all budget_alloca_observations >>
  disch_then (qspecl_then [`tn`,`PG`,`G`] strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `ptr_covers H u q t 32` >>
  `u.t_mem DIFF {a | p <= a /\ a < p + 32} =
   tn.t_mem DIFF {a | p <= a /\ a < p + 32}` by
    (simp[Abbr `u`] >> irule budget_alloca_mem_difference >>
     metis_tac[]) >>
  qexistsl_tac [`H`,`u`,`p`] >> simp[] >>
  conj_tac >- fs[ptr_covers_def, eval_op_inst_idx, eval_operand_def, lookup_var_def] >>
  conj_tac
  >- (irule ptr_fragment_step >> simp[mk_inst_def, is_terminator_def] >>
      rpt strip_tac >> gvs[] >> qexists_tac `t` >> simp[] >>
      simp[Abbr `H`, Abbr `u`] >>
      gvs[GSYM mk_inst_def] >> metis_tac[ptr_inst_ok_alloca]) >>
  rpt strip_tac >>
  `x <> q` by (fs[not_fresh_at_def, Abbr `q`] >> metis_tac[LESS_EQ_REFL]) >>
  first_x_assum drule >> simp[]
QED

Theorem budget_alloca_endpoint_ptr[local]:
  emit_op ALLOCA [Lit 32w] sa = (ip,sb) /\
  abi_decoder_budget first last b cap s /\ sa.cs_next_id IN abi_decoder_ids first last /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  ?H u q p. ip = Var q /\ lookup_var q t = SOME (n2w p) /\
    b <= p /\ p + 32 <= b + cap /\ p + 32 < dimword (:256) /\
    ptr_covers H u q (t with vs_inst_idx := SUC s.vs_inst_idx) 32 /\
    frag_exec_ptr cx ctx PG sa sb
      (\g z v. g = G /\ z = tn /\ v = s)
      (\g z v. g = H /\ z = u /\ v = (t with vs_inst_idx := SUC s.vs_inst_idx)) R /\
    u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> drule_all budget_alloca_endpoint_exact_ptr >>
  disch_then (qspecl_then [`tn`,`cx`,`ctx`,`R`,`PG`,`G`] strip_assume_tac) >>
  qexistsl_tac [`H`,`u`,`q`,`p`] >> simp[]
QED

Theorem abi_decode_index_init_endpoint_exact_ptr:
  abi_decode_index_init sa = (ip,sb) /\
  abi_decoder_budget first last b cap s /\
  sa.cs_next_id IN abi_decoder_ids first last /\ ~s.vs_halted /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  ?H u q p. ip = Var q /\ eval_operand ip t = SOME (n2w p) /\
    b <= p /\ p + 32 <= b + cap /\ mload p t = 0w /\
    ptr_covers H u q (t with vs_inst_idx := LENGTH (emitted_insts sa sb) + s.vs_inst_idx) 32 /\
    frag_exec_ptr cx ctx PG sa sb
      (\g z v. g = G /\ z = tn /\ v = s)
      (\g z v. g = H /\ z = u /\ v = (t with vs_inst_idx := LENGTH (emitted_insts sa sb) + s.vs_inst_idx)) R /\
    u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\
    u.t_mem = tn.t_mem DIFF {a | p <= a /\ a < p + 32} /\
    (!a. p <= a /\ a < p + 32 ==> a NOTIN u.t_mem) /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> drule abi_decode_index_init_trace >> strip_tac >>
  `emit_op ALLOCA [Lit 32w] sa = (ip,allocation_st)` by
    (Cases_on `emit_op ALLOCA [Lit 32w] sa` >>
     gvs[compile_alloc_buffer_def, comp_bind_def, comp_return_def]) >>
  drule emitted_insts_emit_op >> strip_tac >>
  drule emitted_insts_emit_void >> strip_tac >>
  `emitted_insts sa sb = emitted_insts sa allocation_st ++ emitted_insts allocation_st sb` by
    (simp[emitted_insts_def] >>
     pure_rewrite_tac[GSYM APPEND_ASSOC] >> simp[DROP_LENGTH_APPEND]) >>
  `?v. run_inst_seq (emitted_insts sa allocation_st) s = OK v /\
       run_inst_seq (emitted_insts allocation_st sb) v = OK t` by
    (qpat_x_assum `run_inst_seq (emitted_insts sa sb) s = OK t` mp_tac >>
     simp[run_inst_seq_def, AllCaseEqs()] >> metis_tac[]) >>
  drule_all budget_alloca_endpoint_exact_ptr >>
  disch_then (qspecl_then [`tn`,`cx`,`ctx`,`R`,`PG`,`G`] strip_assume_tac) >>
  `t = mstore p 0w v` by
    (qpat_x_assum `run_inst_seq (emitted_insts allocation_st sb) v = OK t` mp_tac >>
     simp[run_inst_seq_def, Once step_inst_base_def, mk_inst_def,
          exec_write2_def, eval_operand_def, w2n_n2w] >>
     gvs[eval_operand_def] >> simp[w2n_n2w]) >>
  `sb.cs_current_bb = allocation_st.cs_current_bb` by
    (qpat_x_assum `emit_void _ _ _ = _` mp_tac >>
     simp[emit_void_def, fresh_id_def, emit_def, comp_bind_def,
          comp_ignore_bind_def, comp_return_def] >> strip_tac >> gvs[]) >>
  qabbrev_tac `v1 = v with vs_inst_idx := SUC s.vs_inst_idx` >>
  qabbrev_tac `ins = mk_inst allocation_st.cs_next_id MSTORE [Var q; Lit 0w] []` >>
  qabbrev_tac `u1 = step_taint ins v1 (mstore p 0w v1) u` >>
  `step_prov PG H ins (mstore p 0w v1) = H /\
   u1.t_var = u.t_var /\ u1.t_stor = u.t_stor /\ u1.t_trans = u.t_trans /\
   u1.t_mem = u.t_mem DIFF {a | p <= a /\ a < p + 32}` by
    (mp_tac mstore_ghost_frame >>
     disch_then (qspecl_then [`PG`,`H`,`u`,`v1`,`allocation_st.cs_next_id`,
       `q`,`Lit 0w`,`n2w p`,`0w`] mp_tac) >>
     simp[Abbr `ins`, Abbr `u1`, Abbr `v1`, lookup_var_def,
          eval_operand_def, op_taint_def, w2n_n2w] >> gvs[lookup_var_def]) >>
  qexistsl_tac [`H`,`u1`,`q`,`p`] >>
  gvs[eval_operand_def] >>
  conj_tac >- simp[mload_mstore_same] >>
  conj_tac >- (fs[ptr_covers_def, Abbr `v1`, eval_operand_def, lookup_var_def] >>
               gvs[ptr_covers_def, eval_operand_def, lookup_var_def, op_taint_def]) >>
  reverse conj_tac >- (rpt strip_tac >> fs[op_taint_def]) >>
  irule frag_exec_ptr_seq >>
  qexistsl_tac [`\g z v. g = H /\ z = u /\ v = v1`, `allocation_st`] >>
  simp[] >> conj_tac >-
    (drule emit_op_extends >> simp[same_blocks_def] >> strip_tac >>
     irule cs_extends_same_block >> simp[IS_PREFIX_APPEND]) >>
  conj_tac >-
    (drule emit_void_extends >> simp[same_blocks_def] >> strip_tac >>
     irule cs_extends_same_block >> simp[IS_PREFIX_APPEND]) >>
  irule mstore_frag_ptr >> simp[] >>
  qexistsl_tac [`STRING #"%" (toString sa.cs_next_var)`, `sa.cs_next_id + 1`, `Lit 0w`] >>
  simp[Abbr `ins`, op_taint_def] >> qexistsl_tac [`n2w p`,`0w`] >>
  simp[Abbr `v1`, lookup_var_def, eval_operand_def, w2n_n2w] >>
  gvs[lookup_var_def, mstore_def, ADD1, ADD_ASSOC]
QED

Theorem abi_decode_index_init_endpoint_ptr:
  abi_decode_index_init sa = (ip,sb) /\
  abi_decoder_budget first last b cap s /\
  sa.cs_next_id IN abi_decoder_ids first last /\ ~s.vs_halted /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  ?H u q p. ip = Var q /\ eval_operand ip t = SOME (n2w p) /\
    b <= p /\ p + 32 <= b + cap /\ mload p t = 0w /\
    ptr_covers H u q (t with vs_inst_idx := LENGTH (emitted_insts sa sb) + s.vs_inst_idx) 32 /\
    frag_exec_ptr cx ctx PG sa sb
      (\g z v. g = G /\ z = tn /\ v = s)
      (\g z v. g = H /\ z = u /\ v = (t with vs_inst_idx := LENGTH (emitted_insts sa sb) + s.vs_inst_idx)) R /\
    u.t_stor = tn.t_stor /\ u.t_trans = tn.t_trans /\
    (!a. p <= a /\ a < p + 32 ==> a NOTIN u.t_mem) /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s /\
      FLOOKUP H x = FLOOKUP G x /\ op_taint u (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> drule_all abi_decode_index_init_endpoint_exact_ptr >>
  disch_then (qspecl_then [`tn`,`cx`,`ctx`,`R`,`PG`,`G`] strip_assume_tac) >>
  qexistsl_tac [`H`,`u`,`q`,`p`] >> simp[]
QED
