Theory bodyPtrPrecompileBuiltinsContinuationFrame
Ancestors bodyPtrPrecompileBuiltinsRecoveryContinuation
          bodyPtrPrecompileBuiltinsFreshFrame bodyPtrPrecompileBuiltinsSuffixGhost exprSimWordArgs
          exprSimPrecompiles exprLoweringProps compileEnv loweringStateRelDefs venomState finite_map
          ptrDiscipline decoderGhostFramePtr bodyPtrDefs pred_set stmtFragPtr venomInst
          ptrSafeRun codegenRel

Theorem fresh_read_ordinary_frame:
  stmt_state_rel ctx fn cenv cx es' q /\ wb_frame cenv es es' sf s q /\
  local_ptrs_reserved cenv sm /\ sm.cs_next_var <= n /\
  sf.cs_next_var <= n ==>
  stmt_state_rel ctx fn cenv cx es'
    (update_var (STRING #"%" (toString n)) w q) /\
  wb_frame cenv es es' sf s
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
    (es with outcomes := SOME (DROP 1 s.vs_outcomes)) t /\
  wb_frame cenv es (es with outcomes := SOME (DROP 1 s.vs_outcomes)) sf s t
Proof
  strip_tac >>
  `stmt_state_rel ctx fn cenv cx
     (es with outcomes := SOME (DROP 1 s.vs_outcomes)) q /\
     wb_frame cenv es (es with outcomes := SOME (DROP 1 s.vs_outcomes)) sf s q` by
    (qpat_assum `_ sm = (Var dst,sl)`
       (mp_then Any mp_tac computed_suffix_preserves) >>
     disch_then (drule_all o SRULE [wordsTheory.dimword_def]) >> simp[]) >>
  drule computed_suffix_shape >> strip_tac >>
  drule emitted_insts_emit_op_local >> strip_tac >> gvs[] >>
  irule fresh_read_ordinary_frame >> goal_assum (drule_at Any) >> simp[] >>
  qexists `sm` >> simp[]
QED

Theorem return_pointer_reservation_mono:
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sa p) /\
  sa.cs_next_var <= sm.cs_next_var ==>
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p)
Proof
  metis_tac[not_fresh_at_mono]
QED

(* Both expression pointer judgments explicitly quantify over entry runs with
   these two reservations (bodyPtrDefs).  The prefix uses the same cenv; this
   monotone boundary transports those actual premises to the suffix start. *)
Theorem fresh_read_taint_fields:
  t = update_var y w q /\
  tn' = step_taint (mk_inst id MLOAD [src] [y])
    (q with vs_inst_idx := k) (t with vs_inst_idx := k) tn ==>
  tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
  tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm
Proof
  simp[step_taint_def, mk_inst_def, mem_taint_def, new_site_bytes_def,
       step_writes_def, written_taint_def, source_memory_write_ranges_def,
       range_bytes_def, update_var_def, store_taint_def, adopt_reset_def,
       imm_taint_def, FLOOKUP_DEF, EXTENSION] >> metis_tac[]
QED

Theorem ghost_inv_readonly_old_frame:
  ghost_inv d cenv cx es G tn s /\ local_ptrs_reserved cenv sm /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
  (!p. not_fresh_at sm p ==> FLOOKUP G' p = FLOOKUP G p /\
     op_taint tn' (Var p) = op_taint tn (Var p) /\ lookup_var p t = lookup_var p s) /\
  es'.scopes = es.scopes /\ t.vs_memory = s.vs_memory /\
  tn'.t_mem = tn.t_mem /\ tn'.t_stor = tn.t_stor /\
  tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
  t.vs_call_ctx = s.vs_call_ctx /\ t.vs_accounts = s.vs_accounts /\
  t.vs_transient = s.vs_transient ==>
  ghost_inv d cenv cx es' G' tn' t
Proof
  strip_tac >> fs[ghost_inv_def] >> conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at sm p` by (gvs[local_ptrs_reserved_def] >> metis_tac[]) >>
      first_x_assum drule >> strip_tac >>
      gvs[ptr_covers_def] >> metis_tac[]) >>
  reverse conj_tac >- gvs[stor_taint_ok_def] >>
  Cases_on `d` >> gvs[return_buf_ptr_def] >> PairCases_on `x` >>
  gvs[return_buf_ptr_def, ptr_covers_def] >> metis_tac[]
QED

Theorem fresh_read_ghost_frame:
  ghost_inv d cenv cx es G tn q /\ local_ptrs_reserved cenv sm /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
  sm.cs_next_var <= n /\ sf.cs_next_var <= sm.cs_next_var /\
  y = STRING #"%" (toString n) /\ t = update_var y w q /\
  G' = step_prov PG G (mk_inst id MLOAD [src] [y]) (t with vs_inst_idx := k) /\
  tn' = step_taint (mk_inst id MLOAD [src] [y])
    (q with vs_inst_idx := k) (t with vs_inst_idx := k) tn ==>
  ghost_inv d cenv cx es G' tn' t /\ ghost_kept cenv es sf G tn q G' tn'
Proof
  strip_tac >> drule_all fresh_read_taint_fields >> strip_tac >>
  `!p. not_fresh_at sm p ==> FLOOKUP G' p = FLOOKUP G p /\
     op_taint tn' (Var p) = op_taint tn (Var p) /\ lookup_var p t = lookup_var p q` by
    (rpt strip_tac >> `p <> y` by
       (gvs[not_fresh_at_def] >> metis_tac[]) >>
     gvs[] >> simp[step_prov_other_output, step_taint_other_output,
          mk_inst_def, update_var_def, lookup_var_def, FLOOKUP_UPDATE]) >>
  conj_tac
  >- (irule ghost_inv_readonly_old_frame >> goal_assum (drule_at Any) >>
      qexists `es` >> simp[update_var_def]) >>
  irule ghost_kept_memory_subset >> simp[] >> rpt strip_tac >>
  `not_fresh_at sm x` by (irule not_fresh_at_mono >> goal_assum drule >> simp[]) >>
  gvs[] >> metis_tac[]
QED

Theorem ghost_kept_same_memory_trans:
  ghost_kept cenv es sf G0 tn0 s0 G1 tn1 /\
  ghost_kept cenv es1 sf G1 tn1 s1 G2 tn2 /\ tn2.t_mem = tn1.t_mem ==>
  ghost_kept cenv es sf G0 tn0 s0 G2 tn2
Proof
  simp[ghost_kept_def] >> rpt strip_tac >> metis_tac[]
QED
