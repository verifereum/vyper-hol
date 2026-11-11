Theory bodyPtrPrecompileBuiltinsSuffixFrame
Ancestors bodyPtrPrecompileBuiltinsSuffixGhost bodyPtrPrecompileBuiltinsSuffixReady
          bodyPtrPrecompileBuiltinsRuntime bodyPtrPrecompileBuiltinsContinuationFrame
          exprSimPrecompiles exprLoweringProps exprSimHash ptrDiscipline
          decoderGhostFramePtr venomExecSemantics venomInstProofs venomState
          venomInst venomCallOracleDefs compileEnv loweringStateRelDefs finite_map pred_set valueCopy
          bodyPtrPrecompileBuiltinsFreshFrame localPtrsProps loweringPosts list rich_list
          bodyPtrDefs stmtFragPtr

Theorem suffix_same_endpoint_effects:
  gi = mk_inst id GAS [] [gv] /\
  ci = mk_inst (id+1) STATICCALL
    [Var gv; Lit addr; Var src; Lit an; Var dst; Lit rn] [cv] /\
  ai = mk_inst (id+2) ASSERT [Var cv] [] /\
  src <> gv /\ dst <> gv /\
  eval_operand (Var src) s = SOME wi /\ eval_operand (Var dst) s = SOME wo /\
  computed_precompile (venom_call_request s addr 0w wi an T) /\
  step_inst_base gi s = OK u /\ step_inst_base ci u = OK v /\
  run_inst_seq [gi;ci;ai] s = OK q /\
  G2 = step_prov PG (step_prov PG G gi u) ci v /\
  tn2 = step_taint ci u v (step_taint gi s u tn) ==>
  q.vs_call_ctx = s.vs_call_ctx /\ q.vs_accounts = s.vs_accounts /\
  q.vs_transient = s.vs_transient /\
  tn2.t_stor = tn.t_stor /\ tn2.t_trans = tn.t_trans /\ tn2.t_imm = tn.t_imm /\
  tn2.t_mem = tn.t_mem DIFF
    {i | w2n wo <= i /\ i < w2n wo + MIN (w2n rn) (LENGTH v.vs_returndata)} /\
  (!x. x <> gv /\ x <> cv ==> FLOOKUP G2 x = FLOOKUP G x /\
    op_taint tn2 (Var x) = op_taint tn (Var x))
Proof
  strip_tac >>
  `u = update_var gv (HD (s.vs_gas_readings ++ [0w]))
    (s with vs_gas_readings := DROP 1 s.vs_gas_readings)` by gvs[step_GAS] >>
  `eval_operand (Var gv) u = SOME (HD (s.vs_gas_readings ++ [0w])) /\
   eval_operand (Var src) u = SOME wi /\ eval_operand (Var dst) u = SOME wo` by
    gvs[update_var_def, eval_operand_def, lookup_var_def, FLOOKUP_UPDATE] >>
  `computed_precompile (venom_call_request u addr 0w wi an T)` by
    (gvs[update_var_def, venom_call_request_def, read_memory_def]) >>
  drule_all computed_call_step_frame >> strip_tac >>
  `q = v` by
    (gvs[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def, AllCaseEqs()]) >>
  `exec_ext_call ci u (HD (s.vs_gas_readings ++ [0w])) addr 0w wi an wo rn T = OK v` by
    (gvs[step_inst_base_opcode_eqs, mk_inst_def, eval_operand_def,
         update_var_def, lookup_var_def, FLOOKUP_UPDATE]) >>
  `ci.inst_outputs = [cv] /\ gi.inst_outputs = [gv]` by simp[mk_inst_def] >>
  drule_all computed_static_state_frame >> strip_tac >>
  drule_all suffix_memory_taint >> strip_tac >>
  `tn2.t_stor = tn.t_stor /\ tn2.t_trans = tn.t_trans /\ tn2.t_imm = tn.t_imm` by
    (gvs[] >> simp[step_taint_nonmemory_frame, mk_inst_def]) >>
  simp[] >> rpt strip_tac >>
  gvs[] >> simp[step_prov_other_output, step_taint_other_output, mk_inst_def]
QED

Theorem computed_suffix_frame_effects:
  (do gas <- emit_op GAS [];
      success <- emit_op STATICCALL
        [gas; Lit target; Var src; Lit insz; Var dst; Lit 32w];
      emit_void ASSERT [success]; return (Var dst) od) sm = (Var dst,sl) /\
  not_fresh_at sm src /\ not_fresh_at sm dst /\
  eval_operand (Var src) s = SOME wi /\ eval_operand (Var dst) s = SOME wo /\
  computed_precompile (venom_call_request s target 0w wi insz T) /\
  precompile_result (venom_call_request s target 0w wi insz T).cr_target
    (venom_call_request s target 0w wi insz T).cr_data = SOME (SOME data) /\
  step_inst_base (EL 0 (emitted_insts sm sl)) s = OK u /\
  step_inst_base (EL 1 (emitted_insts sm sl)) u = OK v /\
  run_inst_seq (emitted_insts sm sl) s = OK q /\
  G2 = step_prov PG (step_prov PG G (EL 0 (emitted_insts sm sl)) u)
    (EL 1 (emitted_insts sm sl)) v /\
  tn2 = step_taint (EL 1 (emitted_insts sm sl)) u v
    (step_taint (EL 0 (emitted_insts sm sl)) s u tn) ==>
  q.vs_call_ctx = s.vs_call_ctx /\ q.vs_accounts = s.vs_accounts /\
  q.vs_transient = s.vs_transient /\
  tn2.t_stor = tn.t_stor /\ tn2.t_trans = tn.t_trans /\ tn2.t_imm = tn.t_imm /\
  tn2.t_mem SUBSET tn.t_mem /\
  (!i. ~(w2n wo <= i /\ i < w2n wo + 32) ==>
    (i IN tn2.t_mem <=> i IN tn.t_mem)) /\
  (!i. ~(w2n wo <= i /\ i < w2n wo + 32) ==>
    mem_bytes_at i 1 q.vs_memory = mem_bytes_at i 1 s.vs_memory) /\
  (!x. not_fresh_at sm x ==> FLOOKUP G2 x = FLOOKUP G x /\
    op_taint tn2 (Var x) = op_taint tn (Var x) /\ lookup_var x q = lookup_var x s)
Proof
  strip_tac >>
  `q.vs_memory = (write_memory_with_expansion (w2n wo) (TAKE 32 data) s).vs_memory /\
   (!x. not_fresh_at sm x ==> lookup_var x q = lookup_var x s)` by
    (qpat_assum `_ sm = (Var dst,sl)`
       (mp_then Any mp_tac computed_suffix_output) >>
     disch_then (drule_all o SRULE [wordsTheory.dimword_def]) >> simp[]) >>
  drule computed_suffix_shape >> strip_tac >>
  `src <> STRING #"%" (toString sm.cs_next_var) /\
   dst <> STRING #"%" (toString sm.cs_next_var)` by
    (gvs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_REFL]) >>
  fs[] >> drule_all (SRULE [] (GEN_ALL suffix_same_endpoint_effects)) >>
  suspend "apply_effects"
QED

Resume computed_suffix_frame_effects[apply_effects]:
  disch_then (qspecl_then [`tn`,`PG`,`G`] strip_assume_tac) >>
  gvs[wordsTheory.dimword_def] >>
  conj_tac
  >- (rpt strip_tac >>
      `MIN 32 (LENGTH v.vs_returndata) <= 32` by simp[] >>
      `~(w2n wo <= i /\ i < w2n wo + MIN 32 (LENGTH v.vs_returndata))` by
        decide_tac >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >> irule mem_bytes_at_write_disjoint >>
      `LENGTH (TAKE 32 data) <= 32` by simp[LENGTH_TAKE_EQ] >> decide_tac) >>
  rpt strip_tac >>
  `x <> STRING #"%" (toString sm.cs_next_var) /\
   x <> STRING #"%" (toString (sm.cs_next_var+1))` by
    (gvs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_REFL,
       arithmeticTheory.LESS_EQ_SUC_REFL]) >> metis_tac[]
QED

Finalise computed_suffix_frame_effects

Theorem computed_suffix_ghost_frame:
  (do gas <- emit_op GAS [];
      success <- emit_op STATICCALL
        [gas; Lit target; Var src; Lit insz; Var dst; Lit 32w];
      emit_void ASSERT [success]; return (Var dst) od) sm = (Var dst,sl) /\
  not_fresh_at sm src /\ not_fresh_at sm dst /\
  eval_operand (Var src) s = SOME wi /\ eval_operand (Var dst) s = SOME wo /\
  computed_precompile (venom_call_request s target 0w wi insz T) /\
  precompile_result (venom_call_request s target 0w wi insz T).cr_target
    (venom_call_request s target 0w wi insz T).cr_data = SOME (SOME data) /\
  step_inst_base (EL 0 (emitted_insts sm sl)) s = OK u /\
  step_inst_base (EL 1 (emitted_insts sm sl)) u = OK v /\
  run_inst_seq (emitted_insts sm sl) s = OK q /\
  G2 = step_prov PG (step_prov PG G (EL 0 (emitted_insts sm sl)) u)
    (EL 1 (emitted_insts sm sl)) v /\
  tn2 = step_taint (EL 1 (emitted_insts sm sl)) u v
    (step_taint (EL 0 (emitted_insts sm sl)) s u tn) /\
  ghost_inv d cenv cx es G tn s /\ local_ptrs_rel fn cenv es.scopes s /\
  local_ptrs_reserved cenv sm /\ sf.cs_next_var <= sm.cs_next_var /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
  (!name b sz. local_region cenv es.scopes s name b sz ==>
     regions_disjoint (w2n wo) 32 b sz) ==>
  ghost_inv d cenv cx (es with outcomes := SOME (DROP 1 s.vs_outcomes)) G2 tn2 q /\
  ghost_kept cenv es sf G tn s G2 tn2
Proof
  strip_tac >> drule_all computed_suffix_frame_effects >> strip_tac >>
  `!p sz. ((?name. FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz)) \/
     cenv.ce_return_buf = SOME (PtrVar (Var p) sz) \/
     cenv.ce_return_pc = SOME (PtrVar (Var p) sz)) ==>
     FLOOKUP G2 p = FLOOKUP G p /\ op_taint tn2 (Var p) = op_taint tn (Var p) /\
     lookup_var p q = lookup_var p s` by
    (rpt strip_tac >> `not_fresh_at sm p` by
      (gvs[local_ptrs_reserved_def] >> metis_tac[]) >> metis_tac[]) >>
  conj_tac
  >- (`ghost_inv d cenv cx es G2 tn2 q` suffices_by (simp[NoAsms, ghost_inv_def] >> strip_tac >> first_assum ACCEPT_TAC) >>
      irule fresh_scratch_ghost_frame >>
      goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
      qexists `fn` >> simp[] >> first_assum ACCEPT_TAC) >>
  irule ghost_kept_memory_subset >> simp[] >> rpt strip_tac >>
  `not_fresh_at sm x` by (irule not_fresh_at_mono >> goal_assum drule >> simp[]) >>
  gvs[] >> metis_tac[]
QED
