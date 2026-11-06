Theory bodyPtrPrecompileBuiltinsFullOutputFrame
Ancestors bodyPtrPrecompileBuiltinsFullOutput exprSimPrecompiles

(* computed_suffix_preserves already supplies the general ordinary frame:
   its extent is w2n outsz, not 32.  Reuse it rather than duplicate it. *)
Theorem computed_full_output_framed_paths:
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
  stmt_state_rel ctx fn cenv cx es s /\
  local_ptrs_reserved cenv sm /\ sf.cs_next_var <= sm.cs_next_var /\
  sf.cs_next_id <= sm.cs_next_id /\
  (!p sz. cenv.ce_return_buf = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
  (!p sz. cenv.ce_return_pc = SOME (PtrVar (Var p) sz) ==> not_fresh_at sm p) /\
  (!name b sz. local_region cenv es.scopes s name b sz ==>
     regions_disjoint (w2n wo) (w2n outsz) b sz) /\
  (!aid b sz. aid < sf.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,sz) ==>
     regions_disjoint (w2n wo) (w2n outsz) b sz) /\
  (cenv.ce_is_ctor ==> !name tv iv off.
     FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc off) /\
     FLOOKUP (case ALOOKUP es.immutables cx.txn.target of NONE => FEMPTY
       | SOME imms => get_source_immutables cenv.ce_module imms) name = SOME (tv,iv) ==>
     regions_disjoint (w2n wo) (w2n outsz) off (type_memory_size tv)) ==>
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
        ghost_kept cenv es sf G tn s G2 tn2 /\
        stmt_state_rel ctx fn cenv cx (es with outcomes := SOME (DROP 1 s.vs_outcomes)) q /\
        wb_frame cenv es sf s q) /\
    ((precompile_result (venom_call_request s target 0w wi insz T).cr_target
        (venom_call_request s target 0w wi insz T).cr_data = SOME NONE \/
      s.vs_outcomes = [] \/ ?co rest. s.vs_outcomes = co::rest /\ ~co.co_success) ==>
      ?q n j. run_inst_seq (emitted_insts sm sl) s = Abort Revert_abort q /\
        gas_path_ptr D lo ctx fn PG G tn s n G2 tn2
          (Abort Revert_abort (q with vs_inst_idx := j)))
Proof
  strip_tac >> drule_all computed_full_output_paths >>
  disch_then (qspec_then `PG` strip_assume_tac) >>
  qexistsl [`G2`,`tn2`] >> reverse conj_tac
  >- first_assum ACCEPT_TAC >>
  gen_tac >> strip_tac >>
  qpat_x_assum `!data. _` (qspec_then `data` mp_tac) >> simp[] >> strip_tac >>
  qexists `q` >> simp[] >>
  qpat_assum `_ sm = (Var dst,sl)` (mp_then Any mp_tac computed_suffix_preserves) >>
  disch_then (drule_all o SRULE []) >> simp[]
QED
