Theory bodyPopLengthTestMods
Ancestors
  bodyPtrSignedConvertBool exprSimPop fragGasCopySeqLiftProps fragGasSeqPtr
  fragExec fragExecMem instMemFrontier memSafeRun ptrDiscipline venomState
  venomInst venomExecSemantics exprLoweringProps instIdxIndep finite_map rich_list

Theorem pop_length_test_raw[local]:
  lookup_var x0 s = SOME n ==>
  ?q. run_inst_seq [mk_inst id ISZERO [Var x0] [x1];
                    mk_inst (id+1) ISZERO [Var x1] [x2]] s = OK q /\
      lookup_var x2 q = SOME (bool_to_word (n <> 0w))
Proof
  strip_tac >>
  simp[run_inst_seq_def, pop_step_ISZERO, lookup_var_def, update_var_def,
       FLOOKUP_UPDATE] >>
  Cases_on `n = 0w` >> simp[bool_to_word_def, lookup_var_def, update_var_def,
                              FLOOKUP_UPDATE]
QED

Theorem pop_length_test_uniform[local]:
  op_taint tn (Var x0) = {} /\ allocas_from lo s /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  code = [mk_inst id ISZERO [Var x0] [x1];
          mk_inst (id+1) ISZERO [Var x1] [x2]] /\
  run_inst_seq code s = OK q ==>
  ?G' tn'.
    (!D j. inst_seq_ptr D lo ctx func PG G tn code
             (s with vs_inst_idx := j) G' tn') /\
    op_prov G' (Var x2) = NONE /\ op_taint tn' (Var x2) = {} /\
    (!x. x <> x1 /\ x <> x2 ==>
         FLOOKUP G' x = FLOOKUP G x /\
         op_taint tn' (Var x) = op_taint tn (Var x)) /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm
Proof
  strip_tac >>
  qexistsl_tac [`DRESTRICT (DRESTRICT G (COMPL {x1})) (COMPL {x2})`,
                `tn with t_var := tn.t_var |+ (x1,{}) |+ (x2,{})`] >>
  conj_tac
  >- (rpt gen_tac >>
      `run_inst_seq code (s with vs_inst_idx := j) =
       OK (q with vs_inst_idx := j)` by
        simp[run_inst_seq_inst_idx, mk_inst_def, is_terminator_def,
             exec_result_map_def] >>
      `(ctx_has_dalloca ctx ==> allocas_below_fmp (s with vs_inst_idx := j))` by
        (qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp s` mp_tac >>
         rewrite_tac[allocas_below_fmp_def, venom_state_accfupds]) >>
      `allocas_from lo (s with vs_inst_idx := j)` by
        (qpat_assum `allocas_from lo s` mp_tac >>
         rewrite_tac[allocas_from_def, venom_state_accfupds]) >>
      `EVERY (\i. i.inst_opcode <> INVOKE /\ i.inst_opcode <> ALLOCA) code` by
        simp[mk_inst_def] >>
      irule inst_seq_ptr_lower_bound_transport >> simp[] >>
      qexists_tac `0` >> simp[] >>
      qpat_x_assum `run_inst_seq code s = OK q` kall_tac >>
      qpat_x_assum `code = _` SUBST_ALL_TAC >>
      drule_all iszero_pair_certificate >>
      disch_then (qspecl_then [`func`, `PG`, `G`, `D`] strip_assume_tac) >>
      gvs[]) >>
  simp[op_prov_def, op_taint_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE] >>
  rpt strip_tac >> simp[]
QED

Theorem pop_length_test_origin[local]:
  ~s.vs_halted /\ lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX code (DROP s.vs_inst_idx bb.bb_instructions) /\
  code = [mk_inst id ISZERO [Var x0] [x1];
          mk_inst (id+1) ISZERO [Var x1] [x2]] /\
  inst_seq_ptr D lo ctx func PG G tn code s G' tn' /\
  run_inst_seq code s = OK q ==>
  gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
    (OK (q with vs_inst_idx := s.vs_inst_idx + 2), G', tn')
Proof
  strip_tac >>
  `run_inst_seq_mem_ok code s` by
    (irule run_inst_seq_mem_ok_every >>
     simp[inst_dload_in_section_def, mk_inst_def] >> rpt conj_tac >>
     irule below_frontier_no_ranges >> simp[mk_inst_def]) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode) code` by
    simp[mk_inst_def, is_terminator_def] >>
  `EVERY (\i. i.inst_opcode <> DALLOCA) code` by simp[mk_inst_def] >>
  `(ctx_has_dalloca ctx ==> !pre i post u.
      code = pre ++ i::post /\ run_inst_seq pre s = OK u ==>
      unitTransformDefs$dalloca_no_wrap i u)` by
    (rpt strip_tac >> irule dalloca_no_wrap_non_dalloca >>
     qpat_x_assum `code = pre ++ i::post` SUBST_ALL_TAC >>
     qpat_assum `EVERY (\i. i.inst_opcode <> DALLOCA) _` mp_tac >>
     simp[NoAsms, listTheory.EVERY_APPEND]) >>
  drule_all run_inst_seq_gas_origin_ptr_path >>
  disch_then (qspec_then `explicit` mp_tac) >> simp[mk_inst_def]
QED

Theorem pop_length_test_mods:
  lookup_var x0 s1 = SOME n /\ op_prov G (Var x0) = NONE /\
  op_taint tn (Var x0) = {} /\ x0 <> x1 /\ x0 <> x2 /\ x1 <> x2 /\
  allocas_from lo s1 /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s1) /\
  ~s1.vs_halted /\ s1.vs_inst_idx = k+1 /\
  lookup_block s1.vs_current_bb func.fn_blocks = SOME bb /\
  code = [mk_inst id ISZERO [Var x0] [x1];
          mk_inst (id+1) ISZERO [Var x1] [x2]] /\
  isPREFIX code (DROP (k+1) bb.bb_instructions) ==>
  ?q s3 G' tn'.
    run_inst_seq code s1 = OK q /\ s3 = q with vs_inst_idx := k+3 /\
    (!D j. inst_seq_ptr D lo ctx func PG G tn code
             (s1 with vs_inst_idx := j) G' tn') /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s1,G,tn) []
           (OK s3,G',tn')) /\
    (s3 with <| vs_vars := s1.vs_vars; vs_inst_idx := s1.vs_inst_idx |>) = s1 /\
    ~s3.vs_halted /\ s3.vs_current_bb = s1.vs_current_bb /\
    allocas_from lo s3 /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s3) /\
    lookup_var x0 s3 = SOME n /\
    op_prov G' (Var x0) = NONE /\ op_taint tn' (Var x0) = {} /\
    lookup_var x2 s3 = SOME (bool_to_word (n <> 0w)) /\
    op_prov G' (Var x2) = NONE /\ op_taint tn' (Var x2) = {} /\
    (!x. x <> x1 /\ x <> x2 ==>
         lookup_var x s3 = lookup_var x s1 /\ FLOOKUP G' x = FLOOKUP G x /\
         op_taint tn' (Var x) = op_taint tn (Var x)) /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm
Proof
  strip_tac >>
  drule pop_length_test_raw >>
  disch_then (qspecl_then [`x2`,`x1`,`id`] strip_assume_tac) >>
  `run_inst_seq code s1 = OK q` by simp[] >>
  drule_all pop_length_test_uniform >>
  disch_then (qspecl_then [`func`,`PG`,`G`] strip_assume_tac) >>
  `!D. inst_seq_ptr D lo ctx func PG G tn code s1 G' tn'` by
    (gen_tac >> first_x_assum (qspecl_then [`D`,`s1.vs_inst_idx`] mp_tac) >>
     simp[venom_state_component_equality]) >>
  drule iszero_pair_runtime_frame >> strip_tac >>
  qexistsl_tac [`q`,`q with vs_inst_idx := k+3`,`G'`,`tn'`] >>
  simp[] >> conj_tac
  >- (gen_tac >> qpat_assum `!D. inst_seq_ptr D lo _ _ _ _ _ _ _ _ _`
          (qspec_then `D` assume_tac) >>
      `isPREFIX code (DROP s1.vs_inst_idx bb.bb_instructions)` by
        (qpat_assum `s1.vs_inst_idx = _` (fn th => pure_rewrite_tac[th]) >>
         first_assum ACCEPT_TAC) >>
      drule_all pop_length_test_origin >>
      disch_then (qspec_then `explicit` mp_tac) >> simp[]) >>
  qpat_x_assum `(q with vs_vars := s1.vs_vars) = s1` (assume_tac o SYM) >>
  fs[venom_state_component_equality] >>
  simp[lookup_var_def, op_prov_def, allocas_from_def, allocas_below_fmp_def] >>
  fs[lookup_var_def, op_prov_def, allocas_from_def, allocas_below_fmp_def] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  disch_tac >> qpat_assum `ctx_has_dalloca ctx ==> _`
    (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC
QED
