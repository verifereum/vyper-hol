(* Joint zero-offset store link for Concat. *)
Theory bodyFullBuiltinConcatZero
Ancestors
  bodyFullUnwrapRun bodyFullGhostFrame wordLoadStorePtr exprSimPrecompiles
  emitHelperProps exprLoweringProps valueEncodingProps venomMemProps
  ptrSafetyTransport fragGasSeqPtr finite_map pred_set

Theorem concat_offset_zero_full:
  emit_void MSTORE [Var oq; Lit 0w] sc = (u,sc') /\
  fn_has_code sc sc' func /\ fn_inst_ids_distinct func /\
  ~ctx_has_dalloca ctx /\ ptr_covers G tn oq s 64 /\
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
      immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor es t ==>
      stmt_state_rel H ctx func cenv cx es t)
Proof
  strip_tac >> Cases_on `u` >>
  drule emitted_insts_emit_void >> strip_tac >>
  drule emit_void_extends >> pure_rewrite_tac[same_blocks_def] >> strip_tac >>
  `ptr_covers G tn oq s 32` by
    (fs[bodyPtrDefsTheory.ptr_covers_def] >> metis_tac[arithmeticTheory.LESS_EQ_TRANS, arithmeticTheory.ADD_MONO_LESS_EQ]) >>
  `eval_operand (Var oq) s = SOME ow /\ eval_operand (Lit 0w) s = SOME 0w` by
    simp[venomStateTheory.eval_operand_def] >>
  drule_all wordLoadStorePtrTheory.ifexp_copy_store_phase >>
  disch_then (qspecl_then [`sc.cs_next_id`, `func`, `PG`, `ARB`] strip_assume_tac) >>
  rename1 `run_inst_seq _ s = OK raw` >>
  `!D. inst_seq_ptr D 0 ctx func PG G tn
      [mk_inst sc.cs_next_id MSTORE [Var oq; Lit 0w] []] s G tn'` by
    (gen_tac >> drule_all wordLoadStorePtrTheory.ifexp_copy_store_phase >>
     disch_then (qspecl_then [`sc.cs_next_id`, `func`, `PG`, `D`] strip_assume_tac) >>
     gvs[inst_seq_ptr_def]) >>
  `!D. inst_seq_ptr D lo ctx func PG G tn
      [mk_inst sc.cs_next_id MSTORE [Var oq; Lit 0w] []] s G tn'` by
    (gen_tac >> gvs[inst_seq_ptr_def] >>
     irule ptr_inst_ok_lower_bound_transport >> simp[] >>
     qexists `0` >> simp[]) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK (raw with vs_inst_idx := LENGTH sc'.cs_current_insts),G,tn')` by
    (gen_tac >> irule emitted_origin_ptr_path >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl [`[mk_inst sc.cs_next_id MSTORE [Var oq; Lit 0w] []]`, `sc`] >>
     simp[venomInstTheory.is_terminator_def,
       fragExecMemTheory.run_inst_seq_mem_ok_last,
       unitTransformDefsTheory.inst_mem_below_frontier_def,
       memSafeRunTheory.inst_dload_in_section_def,
       contextCodegenRelTheory.source_memory_read_ranges_def,
       codegenRelTheory.source_memory_write_ranges_def,
       codegenRelTheory.fixed_source_write_range_def] >> decide_tac) >>
  `alloca_history func (raw with vs_inst_idx := LENGTH sc'.cs_current_insts)` by
    (irule emitted_alloca_history >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl [`[mk_inst sc.cs_next_id MSTORE [Var oq; Lit 0w] []]`, `s`, `sc`] >>
     simp[venomInstTheory.is_terminator_def]) >>
  `!p n. p+n <= w2n ow \/ w2n ow+32 <= p ==>
    mem_bytes_at p n raw.vs_memory = mem_bytes_at p n s.vs_memory` by
    (qpat_assum `raw = mstore _ _ s` SUBST1_TAC >>
     metis_tac[mstore_mem_bytes_at_disjoint]) >>
  `!(H:(bool # bytes32 # type_value) list # num list) cenv cx es.
    stmt_state_rel H ctx func cenv cx es s /\
    (!name b sz. local_region cenv es.scopes s name b sz ==>
      regions_disjoint (w2n ow) 64 b sz) /\
    immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor es
      (raw with vs_inst_idx := LENGTH sc'.cs_current_insts) ==>
    stmt_state_rel H ctx func cenv cx es (raw with vs_inst_idx := LENGTH sc'.cs_current_insts)` by
    (rpt strip_tac >> simp[stmt_state_rel_inst_idx] >>
     qpat_assum `raw = mstore _ _ s` SUBST_ALL_TAC >>
     pure_rewrite_tac[venomMemPropsTheory.mstore_eq_write_mem] >>
     irule write_memory_stmt_state_rel >> simp[] >>
     conj_tac
     >- (rpt strip_tac >> first_x_assum drule >>
         simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
     qpat_x_assum `immutables_rel _ _ _ _ _ _` mp_tac >>
     simp[venomMemPropsTheory.mstore_eq_write_mem,
          loweringStateRelDefsTheory.immutables_rel_def,
          venomStateTheory.write_memory_with_expansion_def]) >>
  `mload (w2n ow) (raw with vs_inst_idx := LENGTH sc'.cs_current_insts) = 0w` by
    (simp[venomStateTheory.mload_def] >>
     qpat_assum `raw = mstore _ _ s` SUBST1_TAC >>
     metis_tac[venomMemPropsTheory.mload_mstore_same, venomStateTheory.mload_def]) >>
  qexistsl [`raw with vs_inst_idx := LENGTH sc'.cs_current_insts`, `tn'`] >>
  simp[ptrDisciplineTheory.op_taint_def] >>
  qpat_assum `raw = mstore _ _ s` SUBST1_TAC >>
  simp[venomMemPropsTheory.mload_mstore_same] >>
  simp[venomStateTheory.mstore_def, ptrDisciplineTheory.allocas_from_def,
       venomStateTheory.venom_state_component_equality] >>
  gvs[ptrDisciplineTheory.allocas_from_def, venomStateTheory.mstore_def] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
