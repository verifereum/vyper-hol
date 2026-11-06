Theory bodyPtrPrecompileBuiltinsContinuationFrame
Ancestors bodyPtrPrecompileBuiltinsRecoveryContinuation
          bodyPtrPrecompileBuiltinsFreshFrame exprSimWordArgs
          exprSimPrecompiles exprLoweringProps compileEnv venomState finite_map

Theorem fresh_read_ordinary_frame:
  stmt_state_rel ctx fn cenv cx es' q /\ wb_frame cenv es sf s q /\
  local_ptrs_reserved cenv sm /\ sm.cs_next_var <= n /\
  sf.cs_next_var <= n ==>
  stmt_state_rel ctx fn cenv cx es'
    (update_var (STRING #"%" (toString n)) w q) /\
  wb_frame cenv es sf s
    (update_var (STRING #"%" (toString n)) w q)
Proof
  strip_tac >> conj_tac
  >- (irule stmt_state_rel_update_var >> simp[] >>
      irule local_ptrs_reserved_fresh >> metis_tac[]) >>
  irule wb_frame_readonly_tail >> goal_assum (drule_at Any) >>
  qexists `sf` >> simp[update_var_def, lookup_var_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> gvs[not_fresh_at_def] >> metis_tac[arithmeticTheory.LESS_EQ_REFL]
QED

Theorem computed_load_suffix_ordinary_frame:
  (do gas <- emit_op GAS [];
      success <- emit_op STATICCALL
        [gas; Lit target; Var src; Lit insz; Var dst; Lit 32w];
      emit_void ASSERT [success]; return (Var dst) od) sm = (Var dst,sl) /\
  emit_op MLOAD [Var dst] sl = (res,sb) /\ res = Var y /\
  t = update_var y w q /\
  not_fresh_at sm src /\ not_fresh_at sm dst /\
  eval_operand (Var src) s = SOME wi /\ eval_operand (Var dst) s = SOME wo /\
  precompile_result (venom_call_request s target 0w wi insz T).cr_target
    (venom_call_request s target 0w wi insz T).cr_data = SOME (SOME data) /\
  run_inst_seq (emitted_insts sm sl) s = OK q /\
  stmt_state_rel ctx fn cenv cx es s /\ local_ptrs_reserved cenv sm /\
  sf.cs_next_var <= sm.cs_next_var /\ sf.cs_next_id <= sm.cs_next_id /\
  (!name b sz. local_region cenv es.scopes s name b sz ==>
     regions_disjoint (w2n wo) 32 b sz) /\
  (!aid b sz. aid < sf.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,sz) ==>
     regions_disjoint (w2n wo) 32 b sz) /\
  (cenv.ce_is_ctor ==> !name tv iv off.
     FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
     FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
       | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (tv,iv) ==>
     regions_disjoint (w2n wo) 32 off (type_memory_size tv)) ==>
  stmt_state_rel ctx fn cenv cx
    (es with outcomes := SOME (DROP 1 s.vs_outcomes)) t /\ wb_frame cenv es sf s t
Proof
  strip_tac >>
  `stmt_state_rel ctx fn cenv cx
     (es with outcomes := SOME (DROP 1 s.vs_outcomes)) q /\ wb_frame cenv es sf s q` by
    (qpat_assum `_ sm = (Var dst,sl)`
       (mp_then Any mp_tac computed_suffix_preserves) >>
     disch_then (drule_all o SRULE [wordsTheory.dimword_def]) >> simp[]) >>
  drule computed_suffix_shape >> strip_tac >>
  drule emitted_insts_emit_op_local >> strip_tac >> gvs[] >>
  irule fresh_read_ordinary_frame >> goal_assum (drule_at Any) >> simp[] >>
  qexists `sm` >> simp[]
QED
