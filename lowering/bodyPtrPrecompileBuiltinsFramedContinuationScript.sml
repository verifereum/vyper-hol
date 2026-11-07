Theory bodyPtrPrecompileBuiltinsFramedContinuation
Ancestors bodyPtrPrecompileBuiltinsRecoveryContinuation
          bodyPtrPrecompileBuiltinsContinuationFrame bodyPtrPrecompileBuiltinsSuffixFrame
          bodyPtrPrecompileBuiltinsSuffixGhost exprSimPrecompiles exprLoweringProps
          exprSimProps bodyPtrDefs compileEnv emitHelper venomInst venomState list

Theorem computed_load_suffix_framed_path:
  comp_bind
    (do gas <- emit_op GAS [];
        success <- emit_op STATICCALL
          [gas; Lit target; Var src; Lit insz; Var dst; Lit 32w];
        emit_void ASSERT [success]; return (Var dst) od)
    (\out. emit_op MLOAD [out]) sm = (res,sb) /\
  not_fresh_at sm src /\ not_fresh_at sm dst /\
  eval_operand (Var src) s = SOME wi /\ eval_operand (Var dst) s = SOME wo /\
  computed_precompile (venom_call_request s target 0w wi insz T) /\
  ptr_covers G tn src s (w2n insz) /\ ptr_covers G tn dst s 32 /\
  (!i. w2n wi <= i /\ i < w2n wi + w2n insz ==> i NOTIN tn.t_mem) /\
  (!i. w2n wo <= i /\ i < w2n wo + 32 ==> i NOTIN tn.t_mem) /\
  allocas_from lo s /\ ~ctx_has_dalloca ctx /\
  tn.t_stor SUBSET D.d_stor s.vs_call_ctx.cc_address
    (s.vs_accounts s.vs_call_ctx.cc_address).storage /\
  tn.t_trans SUBSET D.d_trans s.vs_call_ctx.cc_address
    (s.vs_transient s.vs_call_ctx.cc_address) /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (emitted_insts sm sb) (DROP s.vs_inst_idx bb.bb_instructions) /\
  precompile_result (venom_call_request s target 0w wi insz T).cr_target
    (venom_call_request s target 0w wi insz T).cr_data = SOME (SOME data) /\
  (?co rest. s.vs_outcomes = co::rest /\ co.co_success) /\
  stmt_state_rel ctx fn cenv cx es s /\ ghost_inv d cenv cx es G tn s /\
  local_ptrs_reserved cenv sm /\
  sf.cs_next_var <= sm.cs_next_var /\ sf.cs_next_id <= sm.cs_next_id /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
  (!name b sz. local_region cenv es.scopes s name b sz ==>
     regions_disjoint (w2n wo) 32 b sz) /\
  (!aid b sz. aid < sf.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,sz) ==>
     regions_disjoint (w2n wo) 32 b sz) /\
  (cenv.ce_is_ctor ==> !name tv iv off.
     FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
     FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
       | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (tv,iv) ==>
     regions_disjoint (w2n wo) 32 off (type_memory_size tv)) ==>
  ?t G' tn'.
    run_inst_seq (emitted_insts sm sb) s = OK t /\
    gas_path_ptr D lo ctx fn PG G tn s 1 G' tn'
      (OK (t with vs_inst_idx := s.vs_inst_idx + 4)) /\
    t.vs_current_bb = s.vs_current_bb /\ t.vs_inst_idx = s.vs_inst_idx /\
    op_prov G' res = NONE /\ op_taint tn' res = {} /\
    eval_operand res t = SOME (mem_word_at (w2n wo)
      (write_memory_with_expansion (w2n wo) (TAKE 32 data) s).vs_memory) /\
    (?sl q u v G1 tn1 y.
      (do gas <- emit_op GAS [];
          success <- emit_op STATICCALL
            [gas; Lit target; Var src; Lit insz; Var dst; Lit 32w];
          emit_void ASSERT [success]; return (Var dst) od) sm = (Var dst,sl) /\
      emit_op MLOAD [Var dst] sl = (res,sb) /\ res = Var y /\
      run_inst_seq (emitted_insts sm sl) s = OK q /\
      step_inst_base (EL 0 (emitted_insts sm sl)) s = OK u /\
      step_inst_base (EL 1 (emitted_insts sm sl)) u = OK v /\
      G1 = step_prov PG (step_prov PG G (EL 0 (emitted_insts sm sl)) u)
        (EL 1 (emitted_insts sm sl)) v /\
      tn1 = step_taint (EL 1 (emitted_insts sm sl)) u v
        (step_taint (EL 0 (emitted_insts sm sl)) s u tn) /\
      t = update_var y (mload (w2n wo) q) q /\
      G' = step_prov PG G1 (mk_inst sl.cs_next_id MLOAD [Var dst] [y])
        (t with vs_inst_idx := s.vs_inst_idx + 3) /\
      tn' = step_taint (mk_inst sl.cs_next_id MLOAD [Var dst] [y])
        (q with vs_inst_idx := s.vs_inst_idx + 3)
        (t with vs_inst_idx := s.vs_inst_idx + 3) tn1) /\
    stmt_state_rel ctx fn cenv cx
      (es with outcomes := SOME (DROP 1 s.vs_outcomes)) t /\
    wb_frame cenv es sf s t /\
    ghost_inv d cenv cx (es with outcomes := SOME (DROP 1 s.vs_outcomes)) G' tn' t /\
    ghost_kept cenv es sf G tn s G' tn'
Proof
  strip_tac >>
  Q.SUBGOAL_THEN `?co rest. s.vs_outcomes = co::rest /\ co.co_success` assume_tac
  >- metis_tac[] >>
  drule_all computed_load_suffix_clean_path >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  drule_all computed_load_suffix_ordinary_frame >> strip_tac >>
  `local_ptrs_rel fn cenv es.scopes s` by
    fs[stmt_state_rel_def, state_rel_def] >>
  drule_all computed_suffix_ghost_frame >> strip_tac >>
  suspend "load_frame"
QED

Resume computed_load_suffix_framed_path[load_frame]:
  drule computed_suffix_shape >> strip_tac >>
  drule emitted_insts_emit_op_local >> strip_tac >>
  `y = STRING #"%" (toString sl.cs_next_var)` by gvs[] >>
  `sm.cs_next_var <= sl.cs_next_var` by simp[] >>
  drule_all fresh_read_ghost_frame >> strip_tac >>
  drule_all fresh_read_taint_fields >> strip_tac >>
  drule_all ghost_kept_same_memory_trans >> strip_tac >>
  suspend "pack"
QED

Resume computed_load_suffix_framed_path[pack]:
  qexistsl [`t`,`G'`,`tn'`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (qexistsl [`sl`,`q`,`u`,`v`,`G1`,`tn1`,`y`] >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Finalise computed_load_suffix_framed_path
