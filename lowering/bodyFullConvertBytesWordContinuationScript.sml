(* Uniform ghost endpoints for bytes-word scalar continuations. *)
Theory bodyFullConvertBytesWordContinuation
Ancestors
  bodyPtrSignedConvertClamp bodyPtrSignedConvertBool bodyPtrSignedConvertScalarOps
  ptrDiscipline instIdxIndep fragGasSeqPtr emitHelperProps ASCIInumbers
  fragExec compileEnv exprLowering exprLoweringProps venomState venomInst
  venomExecSemantics finite_map words arithmetic list
  exprPtrUnwrapFrames[qualified,ignore_grammar]

Theorem bytes_word_continuation_uniform:
  (compile_type_convert word ConvToBool sm = (out,sb) \/
   (?b. compile_int_clamp F b word sm = (out,sb)) \/
   (out = word /\ sb = sm) \/ emit_op SHL [bits;word] sm = (out,sb)) /\
  op_prov G word = NONE /\ op_taint tn word = {} /\
  op_prov G bits = NONE /\ op_taint tn bits = {} /\ (ctx_has_dalloca ctx ==> allocas_below_fmp u) /\
  (run_inst_seq (emitted_insts sm sb) u = OK t \/
   run_inst_seq (emitted_insts sm sb) u = Abort err t) ==>
  ?H th.
    (!D q. inst_seq_ptr D 0 ctx fn PG G tn (emitted_insts sm sb)
      (u with vs_inst_idx := q) H th) /\
    (!p. not_fresh_at sm p ==> FLOOKUP H p = FLOOKUP G p /\
      op_taint th (Var p) = op_taint tn (Var p)) /\
    th.t_mem = tn.t_mem /\ th.t_stor = tn.t_stor /\
    th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm /\
    (run_inst_seq (emitted_insts sm sb) u = OK t ==>
      op_prov H out = NONE /\ op_taint th out = {})
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `_ \/ _ \/ _ \/ _` strip_assume_tac
  >- (drule convert_bool_code >> strip_tac >> gnvs[] >>
      `run_inst_seq [mk_inst sm.cs_next_id ISZERO [word] [a];
        mk_inst (sm.cs_next_id+1) ISZERO [Var a] [b]] u = OK t` by
        (qpat_x_assum `_ \/ _` strip_assume_tac >>
         qpat_x_assum `run_inst_seq _ _ = Abort _ _` mp_tac >>
         simp[run_inst_seq_def, AllCaseEqs(), scalar_iszero_no_abort]) >>
      qexistsl_tac [`DRESTRICT (DRESTRICT G (COMPL {a})) (COMPL {b})`,
        `tn with t_var := tn.t_var |+ (a,{}) |+ (b,{})`] >>
      conj_tac
      >- (rpt gen_tac >>
          `run_inst_seq [mk_inst sm.cs_next_id ISZERO [word] [a];
            mk_inst (sm.cs_next_id+1) ISZERO [Var a] [b]]
            (u with vs_inst_idx := q) = OK (t with vs_inst_idx := q)` by
            simp[run_inst_seq_inst_idx, is_terminator_def, exec_result_map_def] >>
          `ctx_has_dalloca ctx ==> allocas_below_fmp (u with vs_inst_idx := q)` by
            simp[exprPtrUnwrapFramesTheory.copy_allocas_inst_idx] >>
          drule_all iszero_pair_certificate >>
          disch_then (qspecl_then [`fn`,`PG`,`G`,`D`] strip_assume_tac) >> gvs[]) >>
      simp[op_prov_def, op_taint_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE] >>
      rpt strip_tac >> simp[] >> metis_tac[])
  >- (drule int_clamp_unsigned_code >> strip_tac >> gnvs[] >>
      `?v. run_inst_seq
        [mk_inst sm.cs_next_id GT [out; Lit (n2w (2 ** b - 1))] [a];
         mk_inst (sm.cs_next_id+1) ISZERO [Var a] [b']] u = OK v` by
        metis_tac[unsigned_clamp_success_prefix, unsigned_clamp_abort_prefix] >>
      qexistsl_tac [`DRESTRICT (DRESTRICT G (COMPL {a})) (COMPL {b'})`,
        `tn with t_var := tn.t_var |+ (a,{}) |+ (b',{})`] >>
      conj_tac
      >- (rpt gen_tac >>
          irule (PURE_REWRITE_RULE [APPEND] scalar_iszero_assert_certificate) >>
          simp[op_prov_def, op_taint_def] >>
          qexists_tac `v with vs_inst_idx := q` >>
          simp[run_inst_seq_inst_idx, is_terminator_def, exec_result_map_def]) >>
      conj_tac
      >- (rpt strip_tac >>
          simp[op_taint_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE] >> metis_tac[]) >>
      simp[] >> Cases_on `out` >>
      gvs[op_prov_def, op_taint_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE] >>
      rpt IF_CASES_TAC >> simp[])
  >- (gvs[emitted_insts_def] >> qexistsl_tac [`G`,`tn`] >>
      simp[inst_seq_ptr_def]) >>
  drule emitted_insts_emit_op >> strip_tac >>
  gnvs[] >>
  `run_inst_seq [mk_inst sm.cs_next_id SHL [bits;word]
    [STRING #"%" (toString sm.cs_next_var)]] u = OK t` by
    (qpat_x_assum `_ \/ _` strip_assume_tac >>
     qpat_x_assum `run_inst_seq _ _ = Abort _ _` mp_tac >>
     simp[run_inst_seq_def, AllCaseEqs(), convert_scalar_no_abort]) >>
  `MEM SHL [GT; SLT; SGT; AND; EQ; SIGNEXTEND; SAR; SHR; SHL; MUL; SDIV]` by simp[] >>
  drule_all scalar_clean_frame_certificate >>
  disch_then (qspecl_then [`fn`,`PG`,`ARB:dead`] strip_assume_tac) >>
  qexistsl_tac [`H`,`th`] >>
  conj_tac
  >- (rpt gen_tac >> drule_all scalar_clean_frame_certificate >>
      disch_then (qspecl_then [`fn`,`PG`,`D`] strip_assume_tac) >>
      `H = H' /\ th = th'` by
        metis_tac[inst_seq_ptr_ghost_unique] >>
      gvs[]) >>
  simp[] >> rpt strip_tac >>
  `p <> STRING #"%" (toString sm.cs_next_var)` by
    (fs[loweringStateRelDefsTheory.not_fresh_at_def]) >>
  metis_tac[]
QED
