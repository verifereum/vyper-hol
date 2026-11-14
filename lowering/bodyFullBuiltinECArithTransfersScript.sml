Theory bodyFullBuiltinECArithTransfers
Ancestors
  bodyMemEcArithTransfers exprSimPtrLiteralOps wordLoadStorePtr
  fragGasSeqPtr bodyFullAllocGeneric exprPtrUnwrapScalarEdges loweringStateRelDefs
  bodyPtrEnvBuiltinsEdges ptrCoverage allocationPtr
  venomExecSemantics venomInst venomState finite_map words bodyPtrDefs
  ptrSafetyTransport ptrDiscipline fragExecPtr ghostPcTransportPtr instIdxIndep

Theorem ec_scalar_store_origin_ptr_path:
  (do dst <- emit_op ADD [Var bp; Lit (n2w pd)];
      emit_void MSTORE [dst; scalar] od) sa = ((),sb) /\
  lookup_var bp s = SOME bw /\ eval_operand scalar s = SOME sw /\
  ptr_covers G tn bp s nd /\ op_taint tn scalar = {} /\
  not_fresh_at sa bp /\
  (!x. scalar = Var x ==> not_fresh_at sa x) /\
  pd + 32 <= nd /\ w2n bw + nd < dimword (:256) /\
  w2n bw + nd <= s.vs_alloca_next /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?t G' tn'.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) [] (OK t,G',tn')) /\
    t.vs_memory = (mstore (w2n bw + pd) sw s).vs_memory /\
    tn'.t_mem = tn.t_mem DIFF {i | w2n bw + pd <= i /\ i < w2n bw + pd + 32} /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x)) /\
    t.vs_inst_idx = s.vs_inst_idx + LENGTH (emitted_insts sa sb) /\
    t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
             vs_inst_idx := s.vs_inst_idx|> = s
Proof
  strip_tac >>
  `eval_operand (Var bp) s = SOME bw` by simp[eval_operand_def] >>
  `!x. MEM (Var x) [Var bp;scalar] ==> not_fresh_at sa x` by
    (simp[] >> metis_tac[]) >>
  drule_all ec_scalar_store_run >> strip_tac >>
  drule ec_scalar_store_shape >> strip_tac >>
  `w2n (bw + n2w pd) = w2n bw + pd` by
    (`pd < dimword (:256) /\ w2n bw + pd < dimword (:256)` by decide_tac >>
     simp[wordsTheory.w2n_add_2, wordsTheory.w2n_n2w]) >>
  `w2n (bw + n2w pd) + 32 <= s.vs_alloca_next` by decide_tac >>
  drule_all ec_scalar_store_mem_ok >> strip_tac >>
  qabbrev_tac `q = STRING #"%" (toString sa.cs_next_var)` >>
  `!x. not_fresh_at sa x ==> x <> q` by
    (rpt strip_tac >> fs[not_fresh_at_def] >>
     first_x_assum (qspec_then `sa.cs_next_var` mp_tac) >> simp[Abbr `q`]) >>
  qpat_assum `ptr_covers G tn bp s nd` (strip_assume_tac o REWRITE_RULE [ptr_covers_def]) >>
  `FLOOKUP G bp = SOME (b,sz')` by metis_tac[] >>
  qabbrev_tac `i1 = mk_inst sa.cs_next_id ADD [Var bp; Lit (n2w pd)] [q]` >>
  qabbrev_tac `i2 = mk_inst (sa.cs_next_id+1) MSTORE [Var q;scalar] []` >>
  qabbrev_tac `u = update_var q (bw + n2w pd) s` >>
  qabbrev_tac `Gu = G |+ (q,(b,sz'))` >>
  qabbrev_tac `tu = tn with t_var := tn.t_var |+ (q,{})` >>
  `step_inst_base i1 s = OK u` by
    simp[Abbr `i1`, Abbr `u`, step_inst_base_opcode_eqs, exec_pure2_def,
         bind_outputs_def, eval_operand_def] >>
  `step_prov PG G i1 u = Gu /\ step_taint i1 s u tn = tu` by
    (simp[Abbr `i1`, Abbr `u`, Abbr `Gu`, Abbr `tu`] >>
     irule literal_add_ghost >> simp[]) >>
  `ptr_covers Gu tu q u 32` by
    (qpat_x_assum `step_prov _ _ _ _ = _` (SUBST1_TAC o SYM) >>
     qpat_x_assum `step_taint _ _ _ _ = _` (SUBST1_TAC o SYM) >>
     `bw + n2w pd = n2w (w2n bw + pd)` by metis_tac[wordsTheory.n2w_w2n] >>
     qunabbrev_tac `i1` >> qunabbrev_tac `u` >>
     pure_asm_rewrite_tac[] >> irule literal_add_ptr_covers >>
     gvs[]) >>
  `lookup_var q u = SOME (bw + n2w pd) /\
   eval_operand scalar u = SOME sw /\ op_taint tu scalar = {}` by
    (Cases_on `scalar` >>
     gvs[Abbr `u`, Abbr `tu`, eval_operand_def, update_var_def,
         lookup_var_def, op_taint_def, FLOOKUP_UPDATE] >>
     `q <> s'` by metis_tac[] >> simp[]) >>
  qabbrev_tac `v = mstore (w2n bw + pd) sw u` >>
  qabbrev_tac `tv = step_taint i2 u v tu` >>
  `step_inst_base i2 u = OK v` by
    simp[Abbr `i2`, Abbr `v`, step_inst_base_opcode_eqs, exec_write2_def,
         eval_operand_def] >>
  `step_prov PG Gu i2 v = Gu /\ tv.t_var = tu.t_var /\
   tv.t_stor = tu.t_stor /\ tv.t_trans = tu.t_trans /\
   tv.t_mem = tu.t_mem DIFF {i | w2n bw + pd <= i /\ i < w2n bw + pd + 32}` by
    (simp[Abbr `tv`, Abbr `v`, Abbr `i2`] >>
     drule_all mstore_ghost_frame >> simp[]) >>
  `!D. ptr_inst_ok D lo 0 ctx func G tn i1 s` by
    (gen_tac >> irule ptr_inst_ok_lower_bound_transport >>
     conj_tac >- simp[] >> qexists_tac `0` >>
     simp[Abbr `i1`, literal_add_ptr_inst_ok]) >>
  `!D. ptr_inst_ok D lo 0 ctx func Gu tu i2
     (u with vs_inst_idx := SUC s.vs_inst_idx)` by
    (gen_tac >> irule ptr_inst_ok_lower_bound_transport >>
     conj_tac >- (gvs[Abbr `u`, allocas_from_def, update_var_def] >> metis_tac[]) >>
     qexists_tac `0` >> simp[Abbr `i2`] >> irule ptr_inst_ok_mstore >>
     gvs[ptr_covers_def, lookup_var_def]) >>
  `step_inst_base i2 (u with vs_inst_idx := SUC s.vs_inst_idx) =
     OK (v with vs_inst_idx := SUC s.vs_inst_idx)` by
    simp[Abbr `i2`, Abbr `v`, step_inst_base_opcode_eqs,
         exec_write2_def, eval_operand_def, lookup_var_def, mstore_def] >>
  `!D. inst_seq_ptr D lo ctx func PG G tn [i1;i2] s Gu tv` by
    (gen_tac >> simp[inst_seq_ptr_def, Abbr `tv`]) >>
  qexistsl_tac [`t with vs_inst_idx := s.vs_inst_idx + 2`, `Gu`, `tv`] >>
  conj_tac
  >- (gen_tac >>
      `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
        (emitted_insts sa sb)` by simp[Abbr `i1`, Abbr `i2`, mk_inst_def, is_terminator_def] >>
      `inst_seq_ptr D lo ctx func PG G tn (emitted_insts sa sb) s Gu tv` by simp[] >>
      drule_all run_inst_seq_gas_origin_ptr_path >>
      simp[Abbr `i1`, Abbr `i2`, mk_inst_def]) >>
  simp[Abbr `tu`] >>
  conj_tac
  >- simp[Abbr `tv`, Abbr `i2`, step_taint_def, imm_taint_def, mk_inst_def] >>
  conj_tac
  >- (rpt strip_tac >> `x <> q` by metis_tac[] >>
      gvs[Abbr `Gu`, op_taint_def, FLOOKUP_UPDATE, lookup_var_def]) >>
  `t.vs_inst_idx = s.vs_inst_idx` by
    (qpat_x_assum `t with <|vs_vars := _; vs_memory := _|> = s`
       (mp_tac o Q.AP_TERM `\z. z.vs_inst_idx`) >> simp[]) >>
  qpat_x_assum `t with <|vs_vars := _; vs_memory := _|> = s`
    (mp_tac o Q.AP_TERM `\z. z with vs_inst_idx := s.vs_inst_idx`) >> simp[]
QED
