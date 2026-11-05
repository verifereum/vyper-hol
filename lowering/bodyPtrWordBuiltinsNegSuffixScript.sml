(* Symbolic compiler suffix: operands need not have scalar provenance. *)
Theory bodyPtrWordBuiltinsNegSuffix
Ancestors bodyPtrWordBuiltinsArithmeticSteps bodyPtrWordBuiltinsIntervalGhost
  exprLowering exprLoweringProps exprSimUnopProps compileEnv emitHelper
  venomInst list rich_list fragGasSeqPtr decoderGhostFramePtr
  venomExecSemantics venomState finite_map ptrDiscipline ptrSafeRun venomExecProofs codegenRel bodyPtrDefs

Theorem word_neg_emitted_insts:
  compile_neg v ty sa = (op,sb) ==>
  emitted_insts sa sb =
    [mk_inst sa.cs_next_id SGT [v; Lit (FST (type_bounds ty))]
       [STRING #"%" (toString sa.cs_next_var)];
     mk_inst (sa.cs_next_id + 1) ASSERT
       [Var (STRING #"%" (toString sa.cs_next_var))] [];
     mk_inst (sa.cs_next_id + 2) SUB [Lit 0w; v]
       [STRING #"%" (toString (sa.cs_next_var + 1))]] /\
  op = Var (STRING #"%" (toString (sa.cs_next_var + 1)))
Proof
  Cases_on `type_bounds ty` >>
  simp[compile_neg_def, comp_bind_def, comp_ignore_bind_def, emit_op_def,
       emit_void_def, fresh_id_def, fresh_var_def, emit_def, comp_return_def] >>
  strip_tac >> gvs[emitted_insts_def] >> simp[DROP_LENGTH_APPEND]
QED

Theorem word_neg_sgt_step:
  eval_operand v s = SOME w ==>
  step_inst_base (mk_inst id SGT [v; Lit bound] [x]) s =
    OK (update_var x (bool_to_word (w > bound)) s)
Proof
  strip_tac >> simp[step_inst_base_def, mk_inst_def, exec_pure2_def,
                    eval_operands_def, eval_operand_def]
QED

Theorem word_neg_assert_step:
  eval_operand v s = SOME w ==>
  step_inst_base (mk_inst id ASSERT [v] []) s =
    if w = 0w then Abort Revert_abort (revert_state (set_returndata [] s)) else OK s
Proof
  strip_tac >> simp[step_inst_base_def, mk_inst_def, eval_operands_def]
QED

Theorem word_neg_ghost_step:
  MEM opc [SGT; SUB; ASSERT] /\ new_site_bytes s t = {} ==>
  step_prov PG G (mk_inst id opc args outs) t =
    set_prov G outs (if opc = SUB then first_prov G args else NONE) /\ 
  step_taint (mk_inst id opc args outs) s t tn =
    tn with t_var := set_var_taint tn.t_var outs {}
Proof
  strip_tac >>
  `out_taint tn (mk_inst id opc args outs) s = {}` by
    (irule word_arithmetic_out_taint >> gvs[mk_inst_def, MEM]) >>
  Cases_on `outs` >> gvs[MEM] >>
  simp[step_prov_def, mk_inst_def, out_prov_def, set_prov_def,
       step_taint_def, mem_taint_def, store_taint_def,
       adopt_reset_def, imm_taint_def, taint_component_equality,
       step_writes_def, source_memory_write_ranges_def, range_bytes_def] >>
  namedCases_on `args` ["", "a rest"] >> simp[written_taint_def] >>
  namedCases_on `rest` ["", "b more"] >> simp[written_taint_def] >>
  namedCases_on `more` ["", "c tail"] >> simp[written_taint_def] >>
  Cases_on `tail` >> simp[written_taint_def]
QED

Theorem word_neg_inst_ok:
  MEM opc [SGT; SUB; ASSERT] /\
  (!arg. MEM arg args ==> op_taint tn arg = {}) /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx ==>
  ptr_inst_ok D lo 0 ctx fn G tn (mk_inst id opc args outs) s
Proof
  strip_tac >>
  `ptr_safe_step D lo 0 ctx fn PG G tn (mk_inst id opc args outs) s` by
    (irule word_arithmetic_ptr_safe_step >> gvs[mk_inst_def, MEM]) >>
  gvs[ptr_safe_step_def]
QED

Theorem word_neg_checked_sequence:
  eval_operand v s = SOME w /\ op_taint tn v = {} /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx ==>
  ?G' tn'. inst_seq_ptr D lo ctx fn PG G tn
    [mk_inst id SGT [v; Lit bound] [x];
     mk_inst (id + 1) ASSERT [Var x] [];
     mk_inst (id + 2) SUB [Lit 0w; v] [y]] s G' tn'
Proof
  strip_tac >>
  `ptr_inst_ok D lo 0 ctx fn G tn (mk_inst id SGT [v; Lit bound] [x]) s` by
    (irule word_neg_inst_ok >> simp[] >> rpt strip_tac >> gvs[] >>
     simp[op_taint_def]) >>
  drule word_neg_sgt_step >>
  disch_then (qspecl_then [`x`, `id`, `bound`] assume_tac) >>
  simp[Once inst_seq_ptr_def] >>
  qmatch_goalsub_abbrev_tac `inst_seq_ptr _ _ _ _ _ G1 tn1 _ s1` >>
  `op_taint tn1 (Var x) = {}` by
    (simp[Abbr `tn1`] >> irule word_arithmetic_output_clean >> simp[mk_inst_def]) >>
  `allocas_from lo s1` by
    (gvs[Abbr `s1`, allocas_from_def, update_var_def] >> metis_tac[]) >>
  `ptr_inst_ok D lo 0 ctx fn G1 tn1 (mk_inst (id + 1) ASSERT [Var x] []) s1` by
    (irule word_neg_inst_ok >> simp[]) >>
  `eval_operand (Var x) s1 = SOME (bool_to_word (w > bound))` by
    simp[Abbr `s1`, eval_operand_def, lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
  drule word_neg_assert_step >> disch_then (qspec_then `id + 1` assume_tac) >>
  simp[Once inst_seq_ptr_def] >>
  reverse (Cases_on `w > bound`) >> simp[] >>
  qmatch_goalsub_abbrev_tac `inst_seq_ptr _ _ _ _ _ G2 tn2 _ s2` >>

  `op_taint tn1 v = {}` by
    (Cases_on `v` >> simp[op_taint_def] >>
     rename1 `eval_operand (Var z) s = SOME w` >>
     Cases_on `z = x` >- gvs[op_taint_def] >>
     `op_taint tn1 (Var z) = op_taint tn (Var z)` by
       simp[Abbr `tn1`, step_taint_other_output, mk_inst_def] >>
     gvs[op_taint_def]) >>
  `op_taint tn2 v = op_taint tn1 v` by
    (Cases_on `v` >> simp[Abbr `tn2`, op_taint_def, step_taint_def,
       mk_inst_def, set_var_taint_def, DRESTRICT_UNIV] >> gvs[op_taint_def]) >>
  `ptr_inst_ok D lo 0 ctx fn G2 tn2 (mk_inst (id + 2) SUB [Lit 0w; v] [y]) s2` by
    (irule word_neg_inst_ok >> simp[Abbr `s2`, allocas_from_def] >>
     rpt strip_tac >> gvs[] >> simp[op_taint_def] >>
     gvs[allocas_from_def] >> metis_tac[]) >>
  simp[Once inst_seq_ptr_def] >>
  Cases_on `step_inst_base (mk_inst (id + 2) SUB [Lit 0w; v] [y]) s2` >>
  simp[inst_seq_ptr_def]
QED

Theorem word_neg_emitted_checked:
  compile_neg v ty sa = (op,sb) /\ eval_operand v s = SOME w /\
  op_taint tn v = {} /\ allocas_from lo s /\ ~ctx_has_dalloca ctx ==>
  ?G' tn'. inst_seq_ptr D lo ctx fn PG G tn (emitted_insts sa sb) s G' tn'
Proof
  strip_tac >> drule word_neg_emitted_insts >> strip_tac >>
  asm_rewrite_tac[] >> irule word_neg_checked_sequence >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem word_neg_emitted_shape:
  compile_neg v ty sa = (op,sb) ==>
  LENGTH (emitted_insts sa sb) = 3 /\
  FILTER (\i. i.inst_opcode = GAS) (emitted_insts sa sb) = [] /\
  EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (emitted_insts sa sb)
Proof
  strip_tac >> drule word_neg_emitted_insts >> strip_tac >>
  simp[mk_inst_def, is_terminator_def]
QED

Theorem word_neg_counted_normal:
  compile_neg v ty sa = (op,sb) /\ fresh_vars_wrt sa s /\
  eval_operand v s = SOME w /\ op_taint tn v = {} /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  w2i (FST (type_bounds ty)) < w2i w ==>
  ?t G' tn'.
    gas_path_ptr D lo ctx fn PG G tn s 0 G' tn'
      (OK (t with vs_inst_idx := s.vs_inst_idx + 3)) /\
    eval_operand op t = SOME (0w - w)
Proof
  strip_tac >> drule_all compile_neg_run >> simp[] >> strip_tac >>
  drule_all word_neg_emitted_checked >>
  disch_then (qspecl_then [`fn`, `PG`, `G`, `D`] strip_assume_tac) >>
  drule word_neg_emitted_shape >> strip_tac >>
  drule_all run_inst_seq_gas_path_ptr >> simp[] >>
  metis_tac[]
QED

Theorem word_neg_counted_abort:
  compile_neg v ty sa = (op,sb) /\ fresh_vars_wrt sa s /\
  eval_operand v s = SOME w /\ op_taint tn v = {} /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
  lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  ~(w2i (FST (type_bounds ty)) < w2i w) ==>
  ?t G' tn' n. gas_path_ptr D lo ctx fn PG G tn s n G' tn'
    (Abort Revert_abort t)
Proof
  strip_tac >> drule_all compile_neg_run >> simp[] >> strip_tac >>
  drule_all word_neg_emitted_checked >>
  disch_then (qspecl_then [`fn`, `PG`, `G`, `D`] strip_assume_tac) >>
  drule word_neg_emitted_shape >> strip_tac >>
  drule_all run_inst_seq_abort_gas_path_ptr >> metis_tac[]
QED

Theorem word_neg_current_block:
  compile_neg v ty sa = (op,sb) ==>
  sb.cs_current_bb = sa.cs_current_bb /\
  sb.cs_current_insts = sa.cs_current_insts ++ emitted_insts sa sb
Proof
  Cases_on `type_bounds ty` >>
  simp[compile_neg_def, comp_bind_def, comp_ignore_bind_def, emit_op_def,
       emit_void_def, fresh_id_def, fresh_var_def, emit_def, comp_return_def] >>
  strip_tac >> gvs[emitted_insts_def] >> simp[DROP_LENGTH_APPEND]
QED

Theorem word_neg_code_prefix:
  compile_neg v ty sa = (op,sb) /\ fn_has_code sa sb fn /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?bb. lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
       isPREFIX (emitted_insts sa sb) (DROP s.vs_inst_idx bb.bb_instructions)
Proof
  strip_tac >> drule word_neg_current_block >> strip_tac >>
  gvs[fragExecTheory.fn_has_code_def, IS_PREFIX_APPEND] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, DROP_LENGTH_APPEND] >> simp[]
QED

(* SUB may propagate the input provenance; a temporary's provenance is
   irrelevant to the frame as long as the frame does not observe it. *)
Theorem word_neg_temp_ghost_inv:
  ghost_inv d cenv cx es G tn s /\
  (!n p sz. FLOOKUP cenv.ce_vars n = SOME (PtrVar (Var p) sz) ==> p <> x) /\
  (!p sz. d <> NONE /\ cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> p <> x) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> p <> x) ==>
  ghost_inv d cenv cx es (set_prov G [x] site)
    (tn with t_var := set_var_taint tn.t_var [x] {}) (update_var x w s)
Proof
  strip_tac >> Cases_on `site`
  >- (simp[set_prov_def] >> irule word_interval_ghost_inv_temp >> simp[] >> metis_tac[]) >>
  fs[bodyPtrDefsTheory.ghost_inv_def] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `p <> x` by metis_tac[] >>
      qpat_x_assum `!name entry p sz. _`
        (qspecl_then [`name`, `entry`, `p`, `sz`] mp_tac) >>
      simp[ptr_covers_def, set_prov_def, FLOOKUP_UPDATE, update_var_def,
           lookup_var_def, op_taint_def, set_var_taint_def]) >>
  conj_tac
  >- (namedCases_on `d` ["", "buf"] >> fs[return_buf_ptr_def] >>
      PairCases_on `buf` >> fs[return_buf_ptr_def] >>
      rename1 `cenv.ce_return_buf = SOME (PtrVar (Var rp) slot)` >>
      `rp <> x` by metis_tac[] >>
      gvs[ptr_covers_def, set_prov_def, FLOOKUP_UPDATE, update_var_def,
          lookup_var_def, op_taint_def, set_var_taint_def] >> metis_tac[]) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> `x' <> x` by metis_tac[] >>
      gvs[op_taint_def, set_var_taint_def, FLOOKUP_UPDATE] >> metis_tac[]) >>
  fs[bodyPtrDefsTheory.stor_taint_ok_def, update_var_def]
QED

Theorem word_neg_temp_ghost_kept:
  ghost_kept cenv es sa G0 tn0 s0 G tn /\
  (!p. not_fresh_at sa p ==> p <> x) ==>
  ghost_kept cenv es sa G0 tn0 s0 (set_prov G [x] site)
    (tn with t_var := set_var_taint tn.t_var [x] {})
Proof
  strip_tac >> Cases_on `site`
  >- (simp[set_prov_def] >> irule word_interval_ghost_kept_temp >> simp[] >> metis_tac[]) >>
  fs[bodyPtrDefsTheory.ghost_kept_def] >>
  conj_tac
  >- (rpt strip_tac >> rename1 `not_fresh_at sa p` >>
      `p <> x` by metis_tac[] >>
      gvs[set_prov_def, FLOOKUP_UPDATE, op_taint_def, set_var_taint_def] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem word_neg_output_ghost_inv:
  MEM opc [SGT; SUB] /\ ghost_inv d cenv cx es G tn s /\
  (!n p sz. FLOOKUP cenv.ce_vars n = SOME (PtrVar (Var p) sz) ==> p <> x) /\
  (!p sz. d <> NONE /\ cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> p <> x) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> p <> x) ==>
  ghost_inv d cenv cx es
    (step_prov PG G (mk_inst id opc args [x]) (update_var x w s))
    (step_taint (mk_inst id opc args [x]) s (update_var x w s) tn)
    (update_var x w s)
Proof
  strip_tac >>
  `new_site_bytes s (update_var x w s) = {}` by
    simp[new_site_bytes_def, update_var_def, FLOOKUP_DEF,
         pred_setTheory.EXTENSION, SF CONJ_ss] >>
  `MEM opc [SGT; SUB; ASSERT]` by gvs[MEM] >>
  simp[word_neg_ghost_step, step_prov_def] >>
  irule word_neg_temp_ghost_inv >> simp[] >> metis_tac[]
QED

Theorem word_neg_output_ghost_kept:
  MEM opc [SGT; SUB] /\ ghost_kept cenv es sa G0 tn0 s0 G tn /\
  (!p. not_fresh_at sa p ==> p <> x) ==>
  ghost_kept cenv es sa G0 tn0 s0
    (step_prov PG G (mk_inst id opc args [x]) (update_var x w s))
    (step_taint (mk_inst id opc args [x]) s (update_var x w s) tn)
Proof
  strip_tac >>
  `new_site_bytes s (update_var x w s) = {}` by
    simp[new_site_bytes_def, update_var_def, FLOOKUP_DEF,
         pred_setTheory.EXTENSION, SF CONJ_ss] >>
  `MEM opc [SGT; SUB; ASSERT]` by gvs[MEM] >>
  simp[word_neg_ghost_step, step_prov_def] >>
  irule word_neg_temp_ghost_kept >> simp[] >> metis_tac[]
QED

Theorem word_neg_assert_ghost_identity:
  step_prov PG G (mk_inst id ASSERT [v] []) s = G /\
  step_taint (mk_inst id ASSERT [v] []) s s tn = tn
Proof
  `new_site_bytes s s = {}` by
    simp[new_site_bytes_def, FLOOKUP_DEF, pred_setTheory.EXTENSION, SF CONJ_ss] >>
  simp[word_neg_ghost_step, step_prov_def, mk_inst_def, set_prov_def,
       set_var_taint_def, DRESTRICT_UNIV]
QED

Theorem word_neg_sub_step:
  eval_operand v s = SOME w ==>
  step_inst_base (mk_inst id SUB [Lit 0w; v] [y]) s =
    OK (update_var y (0w - w) s)
Proof
  strip_tac >> simp[step_inst_base_def, mk_inst_def, exec_pure2_def,
                    eval_operands_def, eval_operand_def]
QED
