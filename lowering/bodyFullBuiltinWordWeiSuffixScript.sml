(* Canonical, horizon-independent ghosts for unsigned AsWeiValue scaling. *)
Theory bodyFullBuiltinWordWeiSuffix
Ancestors
  bodyPtrWordBuiltinsScaling bodyPtrWordBuiltinsScalingSteps
  bodyPtrWordBuiltinsScalarSequence ptrDiscipline venomInst
  instSeqPtrLo bodyFullGhostFrame freshWrites
  exprSimWordBuiltins fragGasSeqPtr fragGasEmitCtrl bodySimFull
  finite_map pred_set list fragExecMem unitTransformDefs memSafeRun contextCodegenRel codegenRel

Theorem as_wei_value_step_exterior:
  compile_as_wei_value_int v (denomination_multiplier dn) F sa = (op,sb) /\
  MEM i (emitted_insts sa sb) /\ step_inst_base i s = OK t ==>
  step_taint i s t tn = tn with t_var :=
    set_var_taint tn.t_var i.inst_outputs (out_taint tn i s)
Proof
  strip_tac >> Cases_on `denomination_multiplier dn = 1`
  >- (gvs[] >> drule word_scale_identity >> strip_tac >> gvs[]) >>
  drule_all word_scale_emitted_shape >> strip_tac >>
  `MEM i.inst_opcode [MUL; Div; EQ; ISZERO; OR; ASSERT]` by
    (fs[EVERY_MEM] >> metis_tac[]) >>
  `t = s with vs_vars := t.vs_vars` by
    (`fresh_write_op i.inst_opcode` by fs[fresh_write_op_def, MEM] >>
     drule_all step_fresh_write_op >> simp[]) >>
  `new_site_bytes s t = {}` by
    (qpat_x_assum `t = s with vs_vars := _` SUBST1_TAC >>
     simp[new_site_bytes_def, FLOOKUP_DEF, EXTENSION, SF CONJ_ss]) >>
  Cases_on `MEM i.inst_opcode [Div; OR]`
  >- (drule_all word_scale_delta_ghost_step >>
      simp[word_scale_delta_out_taint]) >>
  `MEM i.inst_opcode [SUB; SLT; EQ; AND; ISZERO; ASSERT; XOR; MUL]` by fs[MEM] >>
  metis_tac[bodyPtrWordBuiltinsAbsSequenceTheory.word_abs_ghost_step]
QED

Theorem as_wei_value_canonical_ghosts:
  compile_as_wei_value_int v (denomination_multiplier dn) F sa = (op,sb) /\
  op_prov G v = NONE /\ op_taint tn v = {} /\ ~ctx_has_dalloca ctx /\
  allocas_from lo s /\ lo <= s.vs_alloca_next ==>
  ?G' tn'.
    (!D. inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sb) s G' tn') /\
    (!t. run_inst_seq (emitted_insts sa sb) s = OK t ==>
      op_prov G' op = NONE /\ op_taint tn' op = {} /\
      tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
      tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
      (!x. not_fresh_at sa x ==> FLOOKUP G' x = FLOOKUP G x /\
         op_taint tn' (Var x) = op_taint tn (Var x)))
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
      (!x. x IN {z | v = Var z} UNION
        set (FLAT (MAP (\i. i.inst_outputs) (emitted_insts sa sb))) ==>
        FLOOKUP G' x = NONE /\ op_taint tn' (Var x) = {}) /\
      tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
      tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
      (!x. not_fresh_at sa x ==> FLOOKUP G' x = FLOOKUP G x /\
         op_taint tn' (Var x) = op_taint tn (Var x)))` by
    (irule (word_scalar_sequence |> Q.INST
      [`P` |-> `\B H th u.
         (!x. x IN B ==> FLOOKUP H x = NONE /\ op_taint th (Var x) = {}) /\
         th.t_mem = tn.t_mem /\ th.t_stor = tn.t_stor /\
         th.t_trans = tn.t_trans /\ th.t_imm = tn.t_imm /\
         (!x. not_fresh_at sa x ==> FLOOKUP H x = FLOOKUP G x /\
           op_taint th (Var x) = op_taint tn (Var x))`] |> BETA_RULE) >>
     simp[] >> conj_tac
     >- (rpt gen_tac >> strip_tac >>
         `MEM i.inst_opcode [MUL; Div; EQ; ISZERO; OR; ASSERT]` by
           (fs[EVERY_MEM] >> metis_tac[]) >>
         conj_tac
         >- (gen_tac >> disch_tac >>
             irule (word_scale_scalar_transfer |> SIMP_RULE (srw_ss()) [IN_UNION]) >>
             (conj_tac >- fs[MEM]) >> qexists_tac `B` >> simp[]) >>
         drule_all as_wei_value_step_exterior >>
         disch_then (qspec_then `th` SUBST1_TAC) >> simp[] >>
         gen_tac >> strip_tac >>
         `~MEM x i.inst_outputs` by
           (drule word_scale_outputs_fresh >>
            disch_then (qspec_then `sa` mp_tac) >> simp[] >> metis_tac[]) >>
         simp[decoderGhostFramePtrTheory.step_prov_other_output] >>
         Cases_on `i.inst_outputs` >>
         gvs[op_taint_def, set_var_taint_def, FLOOKUP_DRESTRICT] >>
         Cases_on `t` >> gvs[set_var_taint_def, FLOOKUP_DRESTRICT, FLOOKUP_UPDATE]) >>
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

Theorem as_wei_value_suffix_mem_ok:
  compile_as_wei_value_int v (denomination_multiplier dn) F sa = (op,sb) ==>
  run_inst_seq_mem_ok (emitted_insts sa sb) s
Proof
  strip_tac >> Cases_on `denomination_multiplier dn = 1`
  >- (gvs[] >> drule word_scale_identity >> strip_tac >>
      gvs[run_inst_seq_mem_ok_def]) >>
  drule_all word_scale_emitted_insts >> strip_tac >>
  simp[run_inst_seq_mem_ok_def, inst_mem_below_frontier_def,
       inst_dload_in_section_def, source_memory_read_ranges_def,
       source_memory_write_ranges_def, mk_inst_def] >>
  rpt (BasicProvers.TOP_CASE_TAC >> simp[])
QED

Theorem as_wei_value_success_origin:
  compile_as_wei_value_int v (denomination_multiplier dn) F sa = (op,sb) /\
  fn_has_code sa sb fn /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  op_prov G v = NONE /\ op_taint tn v = {} /\ ~ctx_has_dalloca ctx /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  ?G' tn'.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
      (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts),G',tn')) /\
    op_prov G' op = NONE /\ op_taint tn' op = {} /\
    tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
    tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    (!x. not_fresh_at sa x ==> FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x))
Proof
  strip_tac >> drule_all as_wei_value_canonical_ghosts >>
  disch_then (qspecl_then [`fn`, `PG`] strip_assume_tac) >>
  qexistsl_tac [`G'`, `tn'`] >>
  reverse conj_tac >- metis_tac[] >> gen_tac >>
  drule_all word_scale_current_block >> strip_tac >>
  drule_all word_scale_code_prefix >> strip_tac >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
      (emitted_insts sa sb) /\
   FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = []` by
    (Cases_on `denomination_multiplier dn = 1`
     >- (gvs[] >> drule word_scale_identity >> strip_tac >> gvs[]) >>
     drule_all word_scale_emitted_shape >> simp[]) >>
  `run_inst_seq_mem_ok (emitted_insts sa sb) s` by
    metis_tac[as_wei_value_suffix_mem_ok] >>
  first_x_assum (qspec_then `D` assume_tac) >>
  drule_all run_inst_seq_gas_origin_ptr_path >>
  simp[]
QED

Theorem as_wei_value_runtime_frame:
  compile_as_wei_value_int v (denomination_multiplier dn) F sa = (op,sb) /\
  sc.cs_next_var <= sa.cs_next_var /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  t = s with vs_vars := t.vs_vars /\
  (!x. not_fresh_at sc x ==> lookup_var x t = lookup_var x s)
Proof
  strip_tac >>
  `writes_fresh sc (emitted_insts sa sb)` by
    (Cases_on `denomination_multiplier dn = 1`
     >- (gvs[] >> drule word_scale_identity >> simp[writes_fresh_def]) >>
     drule_all word_scale_emitted_shape >> strip_tac >>
     drule word_scale_outputs_fresh >>
     disch_then (qspec_then `sc` mp_tac) >> simp[] >> strip_tac >>
     simp[writes_fresh_def, EVERY_MEM] >> rpt strip_tac
     >- (fs[EVERY_MEM, fresh_write_op_def] >> metis_tac[MEM]) >>
     metis_tac[]) >>
  drule_all run_inst_seq_writes_fresh >> simp[venomStateTheory.lookup_var_def]
QED

Theorem as_wei_value_success_full:
  compile_as_wei_value_int v (denomination_multiplier dn) F sa = (op,sb) /\
  fn_has_code sa sb fn /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  op_prov G v = NONE /\ op_taint tn v = {} /\ ~ctx_has_dalloca ctx /\
  allocas_from lo s /\ lo <= s.vs_alloca_next /\
  sc.cs_next_var <= sa.cs_next_var /\ local_ptrs_reserved cenv sc /\
  (!x sz. cenv.ce_return_buf = SOME (PtrVar (Var x) sz) ==> not_fresh_at sc x) /\
  (!x sz. cenv.ce_return_pc = SOME (PtrVar (Var x) sz) ==> not_fresh_at sc x) /\
  es'.scopes = es.scopes /\
  ghost_kept_at lo cenv es0 sc G0 tn0 s0 G tn /\
  run_inst_seq (emitted_insts sa sb) s = OK t ==>
  ?G' tn'.
    op_prov G' op = NONE /\ op_taint tn' op = {} /\
    ghost_kept_at lo cenv es0 sc G0 tn0 s0 G' tn' /\
    t = s with vs_vars := t.vs_vars /\
    (!x. not_fresh_at sc x ==> lookup_var x t = lookup_var x s) /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,fn,PG) (s,G,tn) []
       (OK (t with vs_inst_idx := LENGTH sb.cs_current_insts),G',tn') /\
       (ghost_inv_at D lo d cenv cx es G tn s ==>
        ghost_inv_at D lo d cenv cx es' G' tn'
          (t with vs_inst_idx := LENGTH sb.cs_current_insts))
Proof
  strip_tac >> drule_all as_wei_value_success_origin >>
  disch_then (qspecl_then [`explicit`, `PG`] strip_assume_tac) >>
  drule_all as_wei_value_runtime_frame >> strip_tac >>
  `!x. not_fresh_at sc x ==> FLOOKUP G' x = FLOOKUP G x /\
      op_taint tn' (Var x) = op_taint tn (Var x)` by
    (gen_tac >> disch_tac >> first_x_assum irule >>
     metis_tac[not_fresh_at_mono]) >>
  qexistsl_tac [`G'`, `tn'`] >> simp[] >> conj_tac
  >- (fs[bodyPtrDefsTheory.ghost_kept_at_def] >> metis_tac[]) >>
  gen_tac >> strip_tac >> irule ghost_inv_at_exterior_frame >>
  goal_assum (drule_at Any) >> qexists_tac `sc` >> simp[] >>
  qpat_x_assum `t = s with vs_vars := _` SUBST1_TAC >>
  fs[venomStateTheory.lookup_var_def]
QED
