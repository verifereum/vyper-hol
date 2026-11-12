Theory bodyPtrBopInFlagCertificate
Ancestors bodyPtrBopScalarCompile bodyPtrBopScalarSeq bodyPtrBopScalarDynamic exprLowering
  exprLoweringProps compileEnv freshWrites emitHelperProps list pred_set

Theorem membership_scalar_iszero_chain:
  comp_bind (emit_op opc ops) (\u. emit_op ISZERO [u]) st = (v,st') /\
  MEM opc [AND; ISZERO] /\ EVERY (\op. op IN A) ops /\
  (!z. z IN R ==> not_fresh_at st z) ==>
  ?B. (bop_scalar_seq R A (emitted_insts st st') B /\ A SUBSET B /\
       st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st' /\
       same_blocks st st' /\ st.cs_next_var <= st'.cs_next_var) /\ v IN B
Proof
  strip_tac >> drule bop_scalar_compile_bind_run >>
  disch_then (qspecl_then [`R`, `\v B. v IN B`, `\u B. u IN B`, `A`] mp_tac) >>
  impl_tac
  >- (conj_tac
      >- (rpt strip_tac >> BETA_TAC >> drule bop_scalar_compile_emit_op >>
          disch_then irule >> fs[MEM]) >>
      rpt strip_tac >> rule_assum_tac BETA_RULE >>
      `!z. z IN R ==> not_fresh_at m z` by metis_tac[not_fresh_at_mono] >>
      drule bop_scalar_compile_emit_op >> simp[]) >> simp[]
QED

Theorem membership_flag_scalar_certificate:
  (bop = In \/ bop = NotIn) /\
  compile_binop bop x y ty bl el st = (v,st') /\ x IN A /\ y IN A /\
  (!w. Lit w IN A) /\ (!z. z IN R ==> not_fresh_at st z) ==>
  ?B. (bop_scalar_seq R A (emitted_insts st st') B /\ A SUBSET B /\
       st'.cs_current_insts = st.cs_current_insts ++ emitted_insts st st' /\
       same_blocks st st' /\ st.cs_next_var <= st'.cs_next_var) /\ v IN B
Proof
  strip_tac >> gvs[compile_binop_def]
  >- (drule bop_scalar_compile_bind_run >>
      disch_then (qspecl_then [`R`, `\v B. v IN B`, `\u B. u IN B`, `A`] mp_tac) >>
      impl_tac
      >- (conj_tac
          >- (rpt strip_tac >> BETA_TAC >> drule bop_scalar_compile_emit_op >>
          disch_then irule >> fs[MEM]) >>
          rpt strip_tac >> rule_assum_tac BETA_RULE >>
          `!z. z IN R ==> not_fresh_at m z` by metis_tac[not_fresh_at_mono] >>
          drule membership_scalar_iszero_chain >> simp[]) >> simp[]) >>
  drule membership_scalar_iszero_chain >> simp[]
QED

Theorem membership_flag_certificate_result_path:
  (bop = In \/ bop = NotIn) /\
  compile_binop bop x y ty bl el st = (v,st') /\ x IN A /\ y IN A /\
  (!w. Lit w IN A) /\ (!z. z IN R ==> not_fresh_at st z) /\
  (!op. op IN A ==> op_prov G op = NONE /\ op_taint tn op = {}) /\
  ~ctx_has_dalloca ctx /\ run_inst_seq (emitted_insts st st') s = OK t /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts st st') (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?G' tn'. gas_path_ptr D 0 ctx fn PG G tn s 0 G' tn'
      (OK (t with vs_inst_idx := s.vs_inst_idx + LENGTH (emitted_insts st st'))) /\
    op_prov G' v = NONE /\ op_taint tn' v = {} /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!z. z IN R ==> FLOOKUP G' z = FLOOKUP G z /\
                      FLOOKUP tn'.t_var z = FLOOKUP tn.t_var z)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all membership_flag_scalar_certificate >> strip_tac >>
  irule bop_scalar_certificate_result_path >> simp[] >>
  qexists_tac `A` >> simp[] >> metis_tac[]
QED
