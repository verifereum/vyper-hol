(* Canonical, horizon-independent ghosts for unsigned AsWeiValue scaling. *)
Theory bodyFullBuiltinWordWeiSuffix
Ancestors
  bodyPtrWordBuiltinsScaling bodyPtrWordBuiltinsScalingSteps
  bodyPtrWordBuiltinsScalarSequence ptrDiscipline venomInst
  instSeqPtrLo bodyFullGhostFrame
  exprSimWordBuiltins fragGasSeqPtr fragGasEmitCtrl bodySimFull
  finite_map pred_set list

Theorem as_wei_value_canonical_ghosts:
  compile_as_wei_value_int v (denomination_multiplier dn) F sa = (op,sb) /\
  op_prov G v = NONE /\ op_taint tn v = {} /\ ~ctx_has_dalloca ctx /\
  allocas_from lo s /\ lo <= s.vs_alloca_next ==>
  ?G' tn'.
    (!D. inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sb) s G' tn') /\
    (!t. run_inst_seq (emitted_insts sa sb) s = OK t ==>
      op_prov G' op = NONE /\ op_taint tn' op = {})
Proof
  strip_tac >> Cases_on `denomination_multiplier dn = 1`
  >- (gvs[] >> drule word_scale_identity >> strip_tac >> gvs[] >>
      qexistsl_tac [`G`, `tn`] >> simp[inst_seq_ptr_def]) >>
  drule_all word_scale_emitted_shape >> strip_tac >>
  drule word_scale_emitted_dependency >> strip_tac >>
  `?G' tn'.
    inst_seq_ptr
      (<|d_stor := K (K {}); d_trans := K (K {});
         d_imm := K {}; d_ret := K {}|>) 0 ctx fn PG G tn
      (emitted_insts sa sb) s G' tn' /\
    (!t. run_inst_seq (emitted_insts sa sb) s = OK t ==>
      !x. x IN {z | v = Var z} UNION
        set (FLAT (MAP (\i. i.inst_outputs) (emitted_insts sa sb))) ==>
        FLOOKUP G' x = NONE /\ op_taint tn' (Var x) = {})` by
    (irule (word_scalar_sequence |> Q.INST
      [`P` |-> `\B H th u. !x. x IN B ==>
         FLOOKUP H x = NONE /\ op_taint th (Var x) = {}`] |> BETA_RULE) >>
     simp[] >> conj_tac
     >- (rpt gen_tac >> strip_tac >>
         `MEM i.inst_opcode [MUL; Div; EQ; ISZERO; OR; ASSERT]` by
           (fs[EVERY_MEM] >> metis_tac[]) >>
         gen_tac >> disch_tac >>
         irule (word_scale_scalar_transfer |> SIMP_RULE (srw_ss()) [IN_UNION]) >>
         (conj_tac >- fs[MEM]) >> qexists_tac `B` >> simp[]) >>
     conj_tac
     >- (rpt strip_tac >> irule word_scale_inst_ok >>
         simp[allocas_from_def] >> fs[EVERY_MEM] >>
         rpt strip_tac >> Cases_on `arg` >>
         gvs[op_taint_def, op_prov_def] >> metis_tac[]) >>
     conj_tac >- (Cases_on `v` >> gvs[op_prov_def]) >>
     fs[EVERY_MEM]) >>
  qexistsl_tac [`G'`, `tn'`] >> conj_tac
  >- (gen_tac >> irule inst_seq_ptr_zero_to_lo >> simp[] >>
      qexists_tac `<|d_stor := K (K {}); d_trans := K (K {});
         d_imm := K {}; d_ret := K {}|>` >> simp[]) >>
  rpt strip_tac >> first_x_assum drule >> strip_tac >>
  drule_all word_scale_emitted_insts >> strip_tac >>
  gvs[op_prov_def] >> first_x_assum irule >> simp[mk_inst_def]
QED
