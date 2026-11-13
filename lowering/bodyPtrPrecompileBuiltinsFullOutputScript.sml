Theory bodyPtrPrecompileBuiltinsFullOutput
Ancestors bodyPtrPrecompileBuiltinsSuffixFrame bodyPtrPrecompileBuiltinsSuffixReady
          bodyPtrPrecompileBuiltinsSuffixGhost bodyPtrPrecompileBuiltinsSuffixPaths
          bodyPtrPrecompileBuiltinsFreshFrame bodyPtrPrecompileBuiltinsRuntime
          exprSimPrecompiles exprSimHash exprLoweringProps compileEnv loweringStateRelDefs freshWrites
          venomExecSemantics venomInst venomState ptrDiscipline bodyPtrDefs
          finite_map pred_set list rich_list valueCopy

(* Full overwrite is different from recovery's initialized partial-output
   contract: no cleanliness of the old output buffer is required here. *)
Theorem computed_suffix_full_output:
  (do gas <- emit_op GAS [];
      success <- emit_op STATICCALL
        [gas; Lit target; Var src; Lit insz; Var dst; Lit outsz];
      emit_void ASSERT [success]; return (Var dst) od) sm = (Var dst,sl) /\
  not_fresh_at sm src /\ not_fresh_at sm dst /\
  eval_operand (Var src) s = SOME wi /\ eval_operand (Var dst) s = SOME wo /\
  computed_precompile (venom_call_request s target 0w wi insz T) /\
  precompile_result (venom_call_request s target 0w wi insz T).cr_target
    (venom_call_request s target 0w wi insz T).cr_data = SOME (SOME data) /\
  s.vs_outcomes = co::rest /\ co.co_success /\
  w2n outsz <= LENGTH data /\
  step_inst_base (EL 0 (emitted_insts sm sl)) s = OK u /\
  step_inst_base (EL 1 (emitted_insts sm sl)) u = OK v /\
  run_inst_seq (emitted_insts sm sl) s = OK q /\
  G2 = step_prov PG (step_prov PG G (EL 0 (emitted_insts sm sl)) u)
    (EL 1 (emitted_insts sm sl)) v /\
  tn2 = step_taint (EL 1 (emitted_insts sm sl)) u v
    (step_taint (EL 0 (emitted_insts sm sl)) s u tn) /\
  ptr_covers G tn dst s (w2n outsz) /\
  ghost_inv d cenv cx es G tn s /\ local_ptrs_rel fn cenv es.scopes s /\
  local_ptrs_reserved cenv sm /\ sf.cs_next_var <= sm.cs_next_var /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
  (!name b sz. local_region cenv es.scopes s name b sz ==>
     regions_disjoint (w2n wo) (w2n outsz) b sz) ==>
  eval_operand (Var dst) q = SOME wo /\
  q.vs_memory = (write_memory_with_expansion (w2n wo) (TAKE (w2n outsz) data) s).vs_memory /\
  ptr_covers G2 tn2 dst q (w2n outsz) /\
  (!i. w2n wo <= i /\ i < w2n wo + w2n outsz ==> i NOTIN tn2.t_mem) /\
  ghost_inv d cenv cx (es with outcomes := SOME (DROP 1 s.vs_outcomes)) G2 tn2 q /\
  ghost_kept cenv es sf G tn s G2 tn2
Proof
  strip_tac >>
  `q.vs_memory = (write_memory_with_expansion (w2n wo) (TAKE (w2n outsz) data) s).vs_memory /\
   q.vs_allocas = s.vs_allocas /\ eval_operand (Var dst) q = SOME wo /\
   (!x. not_fresh_at sm x ==> lookup_var x q = lookup_var x s)` by
    (qpat_assum `_ sm = (Var dst,sl)` (mp_then Any mp_tac computed_suffix_output) >>
     disch_then (drule_all o SRULE []) >> simp[]) >>
  `q.vs_returndata = data` by
    (qpat_assum `_ sm = (Var dst,sl)` (mp_then Any mp_tac computed_suffix_success) >>
     disch_then (qspecl_then [`wo`,`wi`,`s`,`data`] mp_tac o SRULE []) >> simp[] >>
     disch_then (fn th => qpat_x_assum `run_inst_seq _ s = OK q` mp_tac >>
       rewrite_tac[th]) >> simp[update_var_def]) >>
  drule computed_suffix_shape >> strip_tac >>
  `src <> STRING #"%" (toString sm.cs_next_var) /\
   dst <> STRING #"%" (toString sm.cs_next_var) /\
   dst <> STRING #"%" (toString (sm.cs_next_var+1))` by
    (gvs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_REFL,
       arithmeticTheory.LESS_EQ_SUC_REFL]) >>
  `q = v` by
    gvs[run_inst_seq_def, step_inst_base_opcode_eqs, mk_inst_def, AllCaseEqs()] >>
  fs[] >> drule_all (SRULE [] (GEN_ALL suffix_same_endpoint_effects)) >>
  disch_then (qspecl_then [`tn`,`PG`,`G`] strip_assume_tac) >>
  qpat_x_assum `G2 = _` (fn eg => qpat_x_assum `tn2 = _` (fn et =>
    pure_rewrite_tac [GSYM eg, GSYM et] >>
    rule_assum_tac (REWRITE_RULE [GSYM eg, GSYM et]))) >>
  suspend "full_write"
QED

Resume computed_suffix_full_output[full_write]:
  `tn2.t_mem = tn.t_mem DIFF
    {i | w2n wo <= i /\ i < w2n wo + w2n outsz}` by
    (`MIN (w2n outsz) (LENGTH data) = w2n outsz` by
       (simp[arithmeticTheory.MIN_DEF] >> IF_CASES_TAC >> decide_tac) >> fs[]) >>
  `tn2.t_mem SUBSET tn.t_mem /\
   (!i. w2n wo <= i /\ i < w2n wo + w2n outsz ==> i NOTIN tn2.t_mem)` by
    (simp[SUBSET_DEF, IN_DIFF] >> metis_tac[]) >>
  `!x. not_fresh_at sm x ==> FLOOKUP G2 x = FLOOKUP G x /\
    op_taint tn2 (Var x) = op_taint tn (Var x) /\ lookup_var x v = lookup_var x s` by
    (rpt strip_tac >>
     `x <> STRING #"%" (toString sm.cs_next_var) /\
      x <> STRING #"%" (toString (sm.cs_next_var+1))` by
       (gvs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_REFL,
         arithmeticTheory.LESS_EQ_SUC_REFL]) >> metis_tac[]) >>
  `ptr_covers G2 tn2 dst v (w2n outsz)` by
    (gvs[ptr_covers_def] >> metis_tac[]) >>
  `!i. ~(w2n wo <= i /\ i < w2n wo + w2n outsz) ==>
    mem_bytes_at i 1 v.vs_memory = mem_bytes_at i 1 s.vs_memory` by
    (rpt strip_tac >> simp[] >> irule mem_bytes_at_write_disjoint >>
     `LENGTH (TAKE (w2n outsz) data) <= w2n outsz` by simp[LENGTH_TAKE_EQ] >>
     decide_tac) >>
  suspend "frame"
QED

Resume computed_suffix_full_output[frame]:
  `!p sz. ((?name. FLOOKUP cenv.ce_vars name = SOME (PtrVar (Var p) sz)) \/
     cenv.ce_return_buf = SOME (PtrVar (Var p) sz) \/
     cenv.ce_return_pc = SOME (PtrVar (Var p) sz)) ==>
     FLOOKUP G2 p = FLOOKUP G p /\ op_taint tn2 (Var p) = op_taint tn (Var p) /\
     lookup_var p v = lookup_var p s` by
    (rpt strip_tac >> `not_fresh_at sm p` by
      (gvs[local_ptrs_reserved_def] >> metis_tac[]) >> metis_tac[]) >>
  `ghost_inv d cenv cx es G2 tn2 v` by
    (irule fresh_scratch_ghost_frame >>
     goal_assum (drule_at Any) >> goal_assum (drule_at Any) >>
     qexists `fn` >> simp[IN_DIFF] >> first_assum ACCEPT_TAC) >>
  `ghost_kept cenv es sf G tn s G2 tn2` by
    (irule ghost_kept_memory_subset >> simp[] >> rpt strip_tac >>
     `not_fresh_at sm x` by
       (irule not_fresh_at_mono >> goal_assum drule >> simp[]) >> metis_tac[]) >>
  `ghost_inv d cenv cx (es with outcomes := SOME (DROP 1 s.vs_outcomes)) G2 tn2 v` by
    (`ghost_inv d cenv cx es G2 tn2 v` suffices_by
       (simp[NoAsms, ghost_inv_def] >> strip_tac >> first_assum ACCEPT_TAC) >>
     first_assum ACCEPT_TAC) >>
  gvs[] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED
Finalise computed_suffix_full_output

Theorem computed_full_output_paths:
  (do gas <- emit_op GAS [];
      success <- emit_op STATICCALL
        [gas; Lit target; Var src; Lit insz; Var dst; Lit outsz];
      emit_void ASSERT [success]; return (Var dst) od) sm = (Var dst,sl) /\
  not_fresh_at sm src /\ not_fresh_at sm dst /\
  eval_operand (Var src) s = SOME wi /\ eval_operand (Var dst) s = SOME wo /\
  computed_precompile (venom_call_request s target 0w wi insz T) /\
  ptr_covers G tn src s (w2n insz) /\ ptr_covers G tn dst s (w2n outsz) /\
  (!i. w2n wi <= i /\ i < w2n wi + w2n insz ==> i NOTIN tn.t_mem) /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  tn.t_stor SUBSET D.d_stor s.vs_call_ctx.cc_address
    (s.vs_accounts s.vs_call_ctx.cc_address).storage /\
  tn.t_trans SUBSET D.d_trans s.vs_call_ctx.cc_address
    (s.vs_transient s.vs_call_ctx.cc_address) /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sm sl) (DROP s.vs_inst_idx bb.bb_instructions) /\
  ghost_inv d cenv cx es G tn s /\ local_ptrs_rel fn cenv es.scopes s /\
  local_ptrs_reserved cenv sm /\ sf.cs_next_var <= sm.cs_next_var /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
  (!name b sz. local_region cenv es.scopes s name b sz ==>
     regions_disjoint (w2n wo) (w2n outsz) b sz) ==>
  ?G2 tn2.
    (!data. precompile_result (venom_call_request s target 0w wi insz T).cr_target
        (venom_call_request s target 0w wi insz T).cr_data = SOME (SOME data) /\
      (?co rest. s.vs_outcomes = co::rest /\ co.co_success) /\
      w2n outsz <= LENGTH data ==>
      ?q. run_inst_seq (emitted_insts sm sl) s = OK q /\
        gas_path_ptr D lo ctx fn PG G tn s 1 G2 tn2
          (OK (q with vs_inst_idx := s.vs_inst_idx + 3)) /\
        eval_operand (Var dst) q = SOME wo /\
        q.vs_memory = (write_memory_with_expansion (w2n wo) (TAKE (w2n outsz) data) s).vs_memory /\
        ptr_covers G2 tn2 dst q (w2n outsz) /\
        (!i. w2n wo <= i /\ i < w2n wo + w2n outsz ==> i NOTIN tn2.t_mem) /\
        ghost_inv d cenv cx (es with outcomes := SOME (DROP 1 s.vs_outcomes)) G2 tn2 q /\
        ghost_kept cenv es sf G tn s G2 tn2) /\
    ((precompile_result (venom_call_request s target 0w wi insz T).cr_target
        (venom_call_request s target 0w wi insz T).cr_data = SOME NONE \/
      s.vs_outcomes = [] \/ ?co rest. s.vs_outcomes = co::rest /\ ~co.co_success) ==>
      ?q n j. run_inst_seq (emitted_insts sm sl) s = Abort Revert_abort q /\
        gas_path_ptr D lo ctx fn PG G tn s n G2 tn2
          (Abort Revert_abort (q with vs_inst_idx := j)))
Proof
  strip_tac >> drule_all computed_emitted_suffix_paths >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  qexistsl [`G'`,`tn'`] >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `?q. run_inst_seq (emitted_insts sm sl) s = OK q` by
        (qpat_assum `_ sm = (Var dst,sl)` (mp_then Any mp_tac computed_suffix_success) >>
         disch_then (qspecl_then [`wo`,`wi`,`s`,`data`] mp_tac o SRULE []) >>
         simp[] >> metis_tac[]) >>
      drule_all computed_suffix_full_output >> strip_tac >>
      qexists `q` >> simp[]) >>
  suspend "failure"
QED

Resume computed_full_output_paths[failure]:
  disch_then (DISJ_CASES_THEN assume_tac)
  >- (`?q. run_inst_seq (emitted_insts sm sl) s = Abort Revert_abort q` by
        (qpat_assum `_ sm = (Var dst,sl)` (mp_then Any mp_tac computed_suffix_failure) >>
         disch_then (drule_all o SRULE []) >> simp[]) >> metis_tac[]) >>
  `?q. run_inst_seq (emitted_insts sm sl) s = Abort Revert_abort q` by
    (qpat_assum `_ sm = (Var dst,sl)` (mp_then Any mp_tac computed_suffix_oracle_failure) >>
     disch_then (mp_tac o SRULE []) >> metis_tac[]) >>
  metis_tac[]
QED
Finalise computed_full_output_paths
