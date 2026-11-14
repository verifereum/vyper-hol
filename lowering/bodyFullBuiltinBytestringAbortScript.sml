(* A failing slice executes the scalar bounds prefix and its ASSERT. *)
Theory bodyFullBuiltinBytestringAbort
Ancestors
  bodyPtrBytestringBuiltinsBounds fragGasSeqPtr fragGasOriginPtr fragGasOrigin fragGasPathPtr
  instSeqPtrLo ptrSafetyTransport instMemFrontier ptrSafeRun fragExec fragExecMem
  venomExecSemantics venomExecProofs venomState venomInst instIdxIndep
  memSafeRun gasEvents gasCount exprLoweringProps emitHelperProps
  exprSimWordBuiltins stmtAppendStorageRunPtr
  compileEnv loweringStateRelDefs ptrDiscipline finite_map words list rich_list arithmetic

Theorem bytestring_slice_bounds_prefix_check[local]:
  compile_assert_slice_bounds a n limit sa = ((),sb) /\
  eval_operand a s = SOME wa /\ eval_operand n s = SOME wn /\
  eval_operand limit s = SOME wl /\
  (!op. MEM op [a;n;limit] ==>
    op_prov G op = NONE /\ op_taint tn op = {} /\
    (!z. op = Var z ==> not_fresh_at sa z)) /\
  ~ctx_has_dalloca ctx /\
  names = GENLIST (\j. STRING #"%" (toString (sa.cs_next_var+j))) 5 ==>
  inst_seq_ptr D 0 ctx func PG G tn
    (TAKE 5 (emitted_insts sa sb)) s
    (FOLDL (\g x. DRESTRICT g (COMPL {x})) G names)
    (tn with t_var := tn.t_var |++ MAP (\x. (x,{})) names)
Proof
  strip_tac >> fs[DISJ_IMP_THM, FORALL_AND_THM] >>
  `!j w ss. sa.cs_next_var <= j ==>
    eval_operand a (update_var (STRING #"%" (toString j)) w ss) = eval_operand a ss /\
    eval_operand n (update_var (STRING #"%" (toString j)) w ss) = eval_operand n ss /\
    eval_operand limit (update_var (STRING #"%" (toString j)) w ss) = eval_operand limit ss` by
    (rpt strip_tac >> irule eval_operand_update_not_fresh >>
     qexists_tac `sa` >> simp[]) >>
  `!j. sa.cs_next_var <= j ==>
    a <> Var (STRING #"%" (toString j)) /\
    n <> Var (STRING #"%" (toString j)) /\
    limit <> Var (STRING #"%" (toString j))` by
    (gvs[not_fresh_at_def] >> metis_tac[]) >>
  drule compile_assert_slice_bounds_layout >> strip_tac >>
  qpat_x_assum `emitted_insts _ _ = _` SUBST_ALL_TAC >>
  gvs[GENLIST_CONS, combinTheory.o_DEF, FOLDL, FUPDATE_LIST] >>
  irule slice_scalar_seq_cons >>
  simp[DISJ_IMP_THM, FORALL_AND_THM] >> qexists_tac `wa+wn` >>
  simp[step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def] >>
  pure_rewrite_tac[GSYM mk_inst_def] >>
  irule slice_scalar_seq_cons >>
  simp[DISJ_IMP_THM, FORALL_AND_THM, scalar_prov_restrict,
       scalar_taint_update_other] >>
  simp[op_prov_def, FLOOKUP_DRESTRICT, op_taint_def, FLOOKUP_UPDATE] >>
  qexists_tac `bool_to_word (w2n (wa+wn) < w2n wa)` >>
  simp[step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def,
       eval_op_inst_idx, eval_operand_def, lookup_var_def, lookup_var_update_var, FLOOKUP_UPDATE,
       GREATER_DEF] >>
  pure_rewrite_tac[GSYM mk_inst_def] >>
  irule slice_scalar_seq_cons >>
  simp[DISJ_IMP_THM, FORALL_AND_THM, scalar_prov_restrict,
       scalar_taint_update_other] >>
  simp[op_prov_def, FLOOKUP_DRESTRICT, op_taint_def, FLOOKUP_UPDATE] >>
  qexists_tac `bool_to_word (w2n wl < w2n (wa+wn))` >>
  simp[step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def,
       eval_op_inst_idx, eval_operand_def, lookup_var_def, lookup_var_update_var, FLOOKUP_UPDATE,
       GREATER_DEF] >>
  pure_rewrite_tac[GSYM mk_inst_def] >>
  irule slice_scalar_seq_cons >>
  simp[DISJ_IMP_THM, FORALL_AND_THM, op_prov_def, FLOOKUP_DRESTRICT,
       op_taint_def, FLOOKUP_UPDATE] >>
  qexists_tac `bool_to_word (w2n (wa+wn) < w2n wa) ||
               bool_to_word (w2n wl < w2n (wa+wn))` >>
  simp[step_inst_base_opcode_eqs, mk_inst_def, exec_pure2_def,
       eval_op_inst_idx, eval_operand_def, lookup_var_def, lookup_var_update_var, FLOOKUP_UPDATE] >>
  pure_rewrite_tac[GSYM mk_inst_def] >>
  irule slice_scalar_seq_cons >>
  simp[DISJ_IMP_THM, FORALL_AND_THM, op_prov_def, FLOOKUP_DRESTRICT,
       op_taint_def, FLOOKUP_UPDATE] >>
  qexists_tac `bool_to_word ((bool_to_word (w2n (wa+wn) < w2n wa) ||
               bool_to_word (w2n wl < w2n (wa+wn))) = 0w)` >>
  simp[step_inst_base_opcode_eqs, mk_inst_def, exec_pure1_def,
       eval_op_inst_idx, eval_operand_def, lookup_var_def, lookup_var_update_var, FLOOKUP_UPDATE] >>
  pure_rewrite_tac[GSYM mk_inst_def] >>
  simp[pred_setTheory.INTER_ASSOC, FUPDATE_COMMUTES, inst_seq_ptr_def]
QED

Theorem bytestring_slice_bounds_full_abort:
  compile_assert_slice_bounds a n limit sa = ((),sb) /\
  fn_has_code sa sb func /\
  eval_operand a s = SOME wa /\ eval_operand n s = SOME wn /\
  eval_operand limit s = SOME wl /\
  (!op. MEM op [a;n;limit] ==>
    op_prov G op = NONE /\ op_taint tn op = {} /\
    (!z. op = Var z ==> not_fresh_at sa z)) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  run_inst_seq (emitted_insts sa sb) s = Abort ab u ==>
  ab = Revert_abort /\
  ?G' tn'. !D.
    gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (Abort Revert_abort (u with vs_inst_idx := s.vs_inst_idx+5),G',tn')
Proof
  strip_tac >>
  `!op z. MEM op [a;n;limit] /\ op = Var z ==> not_fresh_at sa z` by
    metis_tac[] >>
  drule_all compile_assert_slice_bounds_reserved_prefix_run >> strip_tac >>
  `emitted_insts sa sb = TAKE 5 (emitted_insts sa sb) ++
    [EL 5 (emitted_insts sa sb)]` by
    (drule compile_assert_slice_bounds_layout >> simp[]) >>
  `step_inst_base (EL 5 (emitted_insts sa sb)) p = Abort ab u` by
    (qpat_assum `run_inst_seq _ s = OK p`
       (mp_then Any (qspec_then `[EL 5 (emitted_insts sa sb)]` mp_tac)
         run_inst_seq_append) >>
     simp[GSYM (Q.ASSUME `emitted_insts sa sb = TAKE 5 (emitted_insts sa sb) ++
       [EL 5 (emitted_insts sa sb)]`), run_inst_seq_def] >>
     Cases_on `w2n (wa+wn) < w2n wa \/ w2n wl < w2n (wa+wn)` >> simp[]) >>
  `ab = Revert_abort` by
    (Cases_on `w2n (wa+wn) < w2n wa \/ w2n wl < w2n (wa+wn)` >> gvs[]) >>
  simp[] >>
  qabbrev_tac `names = GENLIST (\j. STRING #"%" (toString (sa.cs_next_var+j))) 5` >>
  qabbrev_tac `G' = FOLDL (\g x. DRESTRICT g (COMPL {x})) G names` >>
  qabbrev_tac `tn' = tn with t_var := tn.t_var |++ MAP (\x. (x,{})) names` >>
  `!D. inst_seq_ptr D lo ctx func PG G tn
      (TAKE 5 (emitted_insts sa sb)) s G' tn'` by
    (gen_tac >> irule inst_seq_ptr_zero_to_lo >> simp[] >>
     qexists_tac `D` >> simp[] >>
     simp[Abbr `G'`, Abbr `tn'`] >>
     irule bytestring_slice_bounds_prefix_check >>
     simp[Abbr `names`] >>
     qexistsl_tac [`a`,`limit`,`n`,`wa`,`wl`,`wn`] >> simp[] >>
     qpat_assum `!op z. MEM op [a;n;limit] /\ _ ==> _` mp_tac >>
     simp[DISJ_IMP_THM, FORALL_AND_THM] >> metis_tac[]) >>
  drule_all compile_assert_slice_bounds_code >> strip_tac >>
  `sb.cs_current_bb = sa.cs_current_bb /\
   sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb` by
    (drule compile_assert_slice_bounds_layout >> simp[same_blocks_def]) >>
  `isPREFIX (TAKE 5 (emitted_insts sa sb))
      (DROP s.vs_inst_idx bb.bb_instructions)` by
    (qpat_x_assum `isPREFIX _ _` mp_tac >>
     simp[IS_PREFIX_APPEND] >> strip_tac >>
     qexists_tac `DROP 5 (emitted_insts sa sb) ++ l` >>
     qpat_assum `DROP _ _ = emitted_insts sa sb ++ l` SUBST1_TAC >>
     pure_rewrite_tac[APPEND_ASSOC, TAKE_DROP] >> REFL_TAC) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (TAKE 5 (emitted_insts sa sb)) /\
   FILTER (\i. i.inst_opcode = GAS) (TAKE 5 (emitted_insts sa sb)) = []` by
    (conj_tac
     >- (irule EVERY_TAKE >> fs[EVERY_MEM]) >>
     `EVERY (\i. i.inst_opcode <> GAS) (TAKE 5 (emitted_insts sa sb))` by
       (irule EVERY_TAKE >> fs[EVERY_MEM]) >>
     fs[FILTER_EQ_NIL, EVERY_MEM]) >>
  `run_inst_seq_mem_ok (TAKE 5 (emitted_insts sa sb)) s` by
    (irule run_inst_seq_mem_ok_every >>
     drule compile_assert_slice_bounds_layout >>
     disch_then (SUBST1_TAC o last o CONJUNCTS) >> simp[mk_inst_def] >>
     rpt conj_tac >> gen_tac >> irule below_frontier_no_ranges >>
     simp[mk_inst_def]) >>
  qabbrev_tac `v = p with vs_inst_idx := s.vs_inst_idx+5` >>
  `~v.vs_halted /\ v.vs_current_bb = s.vs_current_bb /\
   allocas_from lo v /\ v.vs_alloca_next = s.vs_alloca_next` by
    (simp[Abbr `v`] >>
     qpat_assum `p = s with vs_vars := p.vs_vars` SUBST1_TAC >>
     simp[allocas_from_def] >>
     qpat_assum `allocas_from lo s`
       (ACCEPT_TAC o REWRITE_RULE[allocas_from_def])) >>
  `lookup_block v.vs_current_bb func.fn_blocks = SOME bb /\
   get_instruction bb v.vs_inst_idx = SOME (EL 5 (emitted_insts sa sb))` by
     (drule_all fn_has_code_same_block >> strip_tac >>
      rename1 `lookup_block sa.cs_current_bb func.fn_blocks = SOME code` >>
      `code = bb` by metis_tac[optionTheory.SOME_11] >>
      pop_assum SUBST_ALL_TAC >>
     `get_instruction bb (LENGTH sa.cs_current_insts+5) =
        SOME (EL 5 (emitted_insts sa sb))` by
       (first_x_assum (qspec_then `5` mp_tac) >> gvs[]) >>
     simp[Abbr `v`]) >>
  `~is_terminator (EL 5 (emitted_insts sa sb)).inst_opcode` by
    (fs[EVERY_EL] >> metis_tac[]) >>
  `step_inst_base (EL 5 (emitted_insts sa sb)) v =
      Abort Revert_abort (u with vs_inst_idx := s.vs_inst_idx+5)` by
    simp[Abbr `v`, step_inst_inst_idx_indep, exec_result_map_def] >>
  `op_taint tn' (Var (STRING #"%" (toString (sa.cs_next_var+4)))) = {}` by
    simp[Abbr `tn'`, Abbr `names`, GENLIST_CONS, combinTheory.o_DEF,
         FUPDATE_LIST, op_taint_def, FLOOKUP_UPDATE] >>
  qexistsl_tac [`G'`,`tn'`] >> gen_tac >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK v,G',tn')` by
    (simp[Abbr `v`] >>
     qspecl_then [`TAKE 5 (emitted_insts sa sb)`, `s`, `p`, `G`, `tn`,
                  `G'`, `tn'`, `ctx`, `func`, `bb`]
       mp_tac run_inst_seq_gas_origin_ptr_path >>
     simp[]) >>
  `gas_origin_ptr_edge (D,lo,explicit,ctx,func,PG) (v,G',tn') []
      (Abort Revert_abort (u with vs_inst_idx := s.vs_inst_idx+5),G',tn')` by
    (qabbrev_tac `i = EL 5 (emitted_insts sa sb)` >>
     `i = mk_inst (sa.cs_next_id+5) ASSERT
        [Var (STRING #"%" (toString (sa.cs_next_var+4)))] []` by
       (simp[Abbr `i`] >> drule compile_assert_slice_bounds_layout >> simp[]) >>
     `ptr_inst_ok D lo 0 ctx func G' tn' i v` by
       (irule ptr_inst_ok_lower_bound_transport >> simp[] >>
        qexists_tac `0` >> simp[] >>
        irule append_assert_abort_check >> simp[] >> metis_tac[]) >>
     `step_inst 0 ctx i v =
        Abort Revert_abort (u with vs_inst_idx := s.vs_inst_idx+5)` by
       simp[step_inst_non_invoke, mk_inst_def] >>
     simp[gas_origin_ptr_edge_def, gas_origin_edge_def,
          gas_path_ptr_edge_def] >> conj_tac
      >- (qexists_tac `0` >>
         gvs[gas_events_step_def, mem_safe_step_non_invoke,
              mk_inst_def, is_terminator_def, below_frontier_no_ranges,
              inst_dload_in_section_def, exit_result_def]) >>
      qexists_tac `0` >>
     gvs[gas_count_step_def, ptr_safe_step_def, mk_inst_def,
          is_terminator_def, exit_result_def]) >>
  `gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (v,G',tn') []
      (Abort Revert_abort (u with vs_inst_idx := s.vs_inst_idx+5),G',tn')` by
    metis_tac[cj 3 gas_origin_ptr_path_rules, exit_result_def] >>
  metis_tac[gas_origin_ptr_path_append, APPEND_NIL]
QED
