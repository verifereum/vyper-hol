(* Joint zero-offset store link for Concat. *)
Theory bodyFullBuiltinConcatZero
Ancestors
  bodyFullUnwrapRun bodyFullGhostFrame wordLoadStorePtr exprSimPrecompiles
  fragExecPtr emitHelperProps exprLoweringProps valueEncodingProps venomMemProps
  venomInst venomExecSemantics
  ptrSafetyTransport fragGasSeqPtr allocaFootprint finite_map pred_set

Theorem concat_offset_zero_full:
  emit_void MSTORE [Var oq; Lit 0w] sc = (u,sc') /\
  fn_has_code sc sc' func /\ fn_inst_ids_distinct func /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ ptr_covers G tn oq s 64 /\
  lookup_var oq s = SOME ow /\ lo <= w2n ow /\
  w2n ow+64 < dimword (:256) /\ w2n ow+64 <= s.vs_alloca_next /\
  ~s.vs_halted /\ s.vs_current_bb = sc.cs_current_bb /\
  s.vs_inst_idx = LENGTH sc.cs_current_insts /\
  alloca_history func s /\ alloca_inv s /\ allocas_from lo s ==>
  ?t tn'.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G,tn')) /\
    t = (mstore (w2n ow) 0w s with vs_inst_idx := LENGTH sc'.cs_current_insts) /\
    t.vs_current_bb = sc'.cs_current_bb /\
    t.vs_inst_idx = LENGTH sc'.cs_current_insts /\ ~t.vs_halted /\
    alloca_history func t /\ allocas_from lo t /\
    t with <|vs_memory := s.vs_memory; vs_inst_idx := s.vs_inst_idx|> = s /\
    tn'.t_var = tn.t_var /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    mload (w2n ow) t = 0w /\
    tn'.t_mem = tn.t_mem DIFF {i | w2n ow <= i /\ i < w2n ow+32} /\
    (!p n. p+n <= w2n ow \/ w2n ow+32 <= p ==>
      mem_bytes_at p n t.vs_memory = mem_bytes_at p n s.vs_memory) /\
    (!(H:(bool # bytes32 # type_value) list # num list) cenv cx es.
      stmt_state_rel H ctx func cenv cx es s /\
      (!name b sz. local_region cenv es.scopes s name b sz ==>
        regions_disjoint (w2n ow) 64 b sz) /\
      (!src. src = cenv.ce_module \/ IS_SOME (ALOOKUP cenv.ce_modules src) ==>
        immutables_rel cenv cx.txn.target src cenv.ce_is_ctor es t) ==>
      stmt_state_rel H ctx func cenv cx es t)
Proof
  strip_tac >> Cases_on `u` >>
  drule emitted_insts_emit_void >> strip_tac >>
  drule emit_void_extends >> pure_rewrite_tac[same_blocks_def] >> strip_tac >>
  `ptr_covers G tn oq s 32` by
    (fs[bodyPtrDefsTheory.ptr_covers_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS, arithmeticTheory.ADD_MONO_LESS_EQ]) >>
  `eval_operand (Var oq) s = SOME ow /\ eval_operand (Lit 0w) s = SOME 0w` by
    simp[venomStateTheory.eval_operand_def] >>
  qabbrev_tac `raw = mstore (w2n ow) 0w s` >>
  qabbrev_tac `tn' =
    step_taint (mk_inst sc.cs_next_id MSTORE [Var oq; Lit 0w] []) s raw tn` >>
  `raw = mstore (w2n ow) 0w s` by simp[Abbr `raw`] >>
  `step_inst_base (mk_inst sc.cs_next_id MSTORE [Var oq; Lit 0w] []) s = OK raw` by
    (qpat_assum `raw = mstore _ _ _` SUBST1_TAC >>
     irule step_MSTORE >> simp[]) >>
  `run_inst_seq [mk_inst sc.cs_next_id MSTORE [Var oq; Lit 0w] []] s = OK raw` by
    (simp_tac bool_ss [Once run_inst_seq_def] >>
     asm_rewrite_tac[] >> simp_tac (srw_ss()) [Once run_inst_seq_def]) >>
  `tn'.t_var = tn.t_var /\ tn'.t_stor = tn.t_stor /\
   tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
   tn'.t_mem = tn.t_mem DIFF {k | w2n ow <= k /\ k < w2n ow + 32}` by
    (qpat_assum `Abbrev (tn' = _)`
       (SUBST1_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     qpat_assum `raw = mstore _ _ _` SUBST1_TAC >>
     simp[ifexp_materialize_mstore_ghost,
          ifexp_materialize_mstore_taint, ptrDisciplineTheory.op_taint_def]) >>
  `!D. ptr_inst_ok D lo 0 ctx func G tn
      (mk_inst sc.cs_next_id MSTORE [Var oq; Lit 0w] []) s` by
    (gen_tac >> irule ptr_inst_ok_lower_bound_transport >> simp[] >>
     qexists_tac `0` >> simp[] >>
     irule fragExecPtrTheory.ptr_inst_ok_mstore >> simp[ptrDisciplineTheory.op_taint_def]) >>
  `step_prov PG G (mk_inst sc.cs_next_id MSTORE [Var oq; Lit 0w] []) raw = G` by
    (qpat_assum `raw = mstore _ _ _` SUBST1_TAC >>
     simp_tac bool_ss [ifexp_materialize_mstore_ghost]) >>
  `tn' = step_taint (mk_inst sc.cs_next_id MSTORE [Var oq; Lit 0w] []) s raw tn` by
    (qpat_assum `Abbrev (tn' = _)` (ACCEPT_TAC o REWRITE_RULE [markerTheory.Abbrev_def])) >>
  `!D. inst_seq_ptr D lo ctx func PG G tn
      [mk_inst sc.cs_next_id MSTORE [Var oq; Lit 0w] []] s G tn'` by
    (gen_tac >> pure_rewrite_tac[inst_seq_ptr_def] >>
     asm_rewrite_tac[] >> simp_tac (srw_ss()) [Once inst_seq_ptr_def, ifexp_materialize_mstore_ghost]) >>
  `w2n ow + 32 <= s.vs_alloca_next` by decide_tac >>
  `run_inst_seq_mem_ok [mk_inst sc.cs_next_id MSTORE [Var oq; Lit 0w] []] s` by
    (drule_all emit_mstore_mem_ok >> simp[]) >>
  `(ctx_has_dalloca ctx ==>
      !pre i post u. [mk_inst sc.cs_next_id MSTORE [Var oq; Lit 0w] []] =
        pre ++ i::post /\ run_inst_seq pre s = OK u ==>
        unitTransformDefs$dalloca_no_wrap i u)` by
    (rpt strip_tac >> irule memSafeRunTheory.dalloca_no_wrap_non_dalloca >>
     qpat_x_assum `[_] = _ ++ _` (mp_tac o SYM) >>
     simp[listTheory.APPEND_EQ_SING] >> strip_tac >> simp[mk_inst_def]) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK (raw with vs_inst_idx := LENGTH sc'.cs_current_insts),G,tn')` by
    (gen_tac >> irule emitted_origin_ptr_path >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl [`[mk_inst sc.cs_next_id MSTORE [Var oq; Lit 0w] []]`, `sc`] >>
     rpt conj_tac
     >~ [`EVERY _ _`] >- simp[mk_inst_def, is_terminator_def] >>
     first_assum MATCH_ACCEPT_TAC) >>
  `alloca_history func (raw with vs_inst_idx := LENGTH sc'.cs_current_insts)` by
    (irule emitted_alloca_history >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl [`[mk_inst sc.cs_next_id MSTORE [Var oq; Lit 0w] []]`, `s`, `sc`] >>
     rpt conj_tac
     >~ [`EVERY _ _`] >- simp_tac (srw_ss()) [mk_inst_def, is_terminator_def] >>
     first_assum ACCEPT_TAC) >>
  `!p n. p+n <= w2n ow \/ w2n ow+32 <= p ==>
    mem_bytes_at p n (raw with vs_inst_idx := LENGTH sc'.cs_current_insts).vs_memory =
      mem_bytes_at p n s.vs_memory` by
    (qpat_assum `raw = mstore _ _ s` SUBST1_TAC >>
     simp[NoAsms] >> metis_tac[mstore_mem_bytes_at_disjoint, arithmeticTheory.ADD_COMM]) >>
  `!(H:(bool # bytes32 # type_value) list # num list) cenv cx es.
    stmt_state_rel H ctx func cenv cx es s /\
    (!name b sz. local_region cenv es.scopes s name b sz ==>
      regions_disjoint (w2n ow) 64 b sz) /\
    (!src. src = cenv.ce_module \/ IS_SOME (ALOOKUP cenv.ce_modules src) ==>
      immutables_rel cenv cx.txn.target src cenv.ce_is_ctor es
        (raw with vs_inst_idx := LENGTH sc'.cs_current_insts)) ==>
    stmt_state_rel H ctx func cenv cx es (raw with vs_inst_idx := LENGTH sc'.cs_current_insts)` by
    (rpt strip_tac >> rewrite_tac[stmt_state_rel_inst_idx] >>
     qpat_assum `raw = mstore _ _ s` SUBST_ALL_TAC >>
     pure_rewrite_tac[venomMemPropsTheory.mstore_eq_write_mem] >>
     irule write_memory_stmt_state_rel >> simp[] >>
     conj_tac
     >- (rpt strip_tac >> first_x_assum drule >>
         simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
     qpat_x_assum `!src. _ ==> immutables_rel _ _ _ _ _ _` mp_tac >>
     simp[venomMemPropsTheory.mstore_eq_write_mem,
          loweringStateRelDefsTheory.immutables_rel_def,
          venomStateTheory.write_memory_with_expansion_def]) >>
  `mload (w2n ow) (raw with vs_inst_idx := LENGTH sc'.cs_current_insts) = 0w` by
    (`mload (w2n ow) (raw with vs_inst_idx := LENGTH sc'.cs_current_insts) =
      mload (w2n ow) raw` by simp[NoAsms, venomStateTheory.mload_def] >>
     pop_assum SUBST1_TAC >>
     qpat_assum `raw = mstore _ _ s` SUBST1_TAC >>
     rewrite_tac[venomMemPropsTheory.mload_mstore_same]) >>
  qexistsl [`raw with vs_inst_idx := LENGTH sc'.cs_current_insts`, `tn'`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  rpt conj_tac
  >~ [`allocas_from lo (raw with vs_inst_idx := _)`] >-
    (qpat_assum `raw = mstore _ _ s` SUBST1_TAC >>
     simp[NoAsms, ptrDisciplineTheory.allocas_from_def, venomStateTheory.mstore_def] >>
     qpat_assum `allocas_from lo s`
       (ACCEPT_TAC o REWRITE_RULE [ptrDisciplineTheory.allocas_from_def]))
  >>~ [`(raw with vs_inst_idx := _).vs_current_bb = _`] >-
    (qpat_assum `raw = mstore _ _ s` SUBST1_TAC >>
     simp[NoAsms, venomStateTheory.mstore_def] >> asm_rewrite_tac[])
  >>~ [`~(raw with vs_inst_idx := _).vs_halted`] >-
    (qpat_assum `raw = mstore _ _ s` SUBST1_TAC >>
     simp[NoAsms, venomStateTheory.mstore_def] >> first_assum ACCEPT_TAC)
  >>~ [`raw with <|vs_memory := _; vs_inst_idx := _; vs_inst_idx := _|> = s`] >-
    (qpat_assum `raw = mstore _ _ s` SUBST1_TAC >>
     simp[NoAsms, venomStateTheory.mstore_def, venomStateTheory.venom_state_component_equality])
  >> FIRST [first_assum ACCEPT_TAC, PURE_ASM_REWRITE_TAC [] >> simp[NoAsms]]
QED
