(* One checked execution for the reason encoder's four-instruction head. *)
Theory bodyFullRaiseReasonHead
Ancestors
  stmtReasonMemory revertReasonPrefixBoundaryPtr revertReasonPrefixCodePtr
  revertReasonLayout revertReasonPrefixPtr
  fragGasSeqPtr instSeqPtrLo fragGasOriginPtrLoop
  venomInst venomState list rich_list arithmetic

Theorem reason_head_origin_ptr_path:
  MEM (mk_inst id ALLOCA [Lit (n2w (64 + M))] ["%" ++ toString v])
    (fn_insts func) /\
  MEM (mk_inst (id + 3) ALLOCA [Lit (n2w M)] ["%" ++ toString (v + 2)])
    (fn_insts func) /\
  64 + M < dimword (:256) /\
  alloca_room ctx func s /\ alloca_next_valid s /\
  (!x. FLOOKUP s.vs_allocas id = SOME x ==> SND x = 64 + M) /\
  (!x. FLOOKUP s.vs_allocas (id + 3) = SOME x ==> SND x = M) /\
  stmt_state_rel H0 ctx func cenv cx es s /\ ~ctx_has_dalloca ctx /\
  ~s.vs_halted /\
  lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
  isPREFIX (reason_head id v M) (DROP s.vs_inst_idx bb.bb_instructions) /\
  allocas_from lo s /\ lo <= s.vs_alloca_next ==>
  ?t Gf tnf B TP.
    run_inst_seq (reason_head id v M) s = OK t /\
    run_inst_seq_mem_ok (reason_head id v M) s /\
    (!D. inst_seq_ptr D lo ctx func PG G tn (reason_head id v M) s Gf tnf /\
      gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
        (OK (t with vs_inst_idx := s.vs_inst_idx + 4),Gf,tnf)) /\
    lookup_var ("%" ++ toString v) t = SOME (n2w B) /\
    lookup_var ("%" ++ toString (v + 1)) t = SOME (n2w (B + 32)) /\
    lookup_var ("%" ++ toString (v + 2)) t = SOME (n2w TP) /\
    (!x. x <> "%" ++ toString v /\ x <> "%" ++ toString (v + 1) /\
         x <> "%" ++ toString (v + 2) ==> lookup_var x t = lookup_var x s) /\
    FLOOKUP t.vs_allocas id = SOME (B,64 + M) /\
    FLOOKUP t.vs_allocas (id + 3) = SOME (TP,M) /\
    (!a. a <> id /\ a <> id + 3 ==>
      FLOOKUP t.vs_allocas a = FLOOKUP s.vs_allocas a) /\
    (FLOOKUP s.vs_allocas id = NONE ==> B = s.vs_alloca_next) /\
    (FLOOKUP s.vs_allocas (id + 3) = NONE ==> s.vs_alloca_next <= TP) /\
    B + 64 + M <= t.vs_alloca_next /\ TP + M <= t.vs_alloca_next /\
    s.vs_alloca_next <= t.vs_alloca_next /\ alloca_room ctx func t /\
    (!a. a + 32 <= B \/ B + 32 <= a ==> mload a t = mload a s) /\
    t.vs_current_bb = s.vs_current_bb /\ t.vs_inst_idx = s.vs_inst_idx /\
    t.vs_halted = s.vs_halted /\
    (!x. FLOOKUP s.vs_allocas id = SOME x ==> B = FST x) /\
    (!x. FLOOKUP s.vs_allocas (id + 3) = SOME x ==> TP = FST x) /\
    (fn_inst_ids_distinct func /\
     (!k. k < 2 ==> not_local_ptr cenv es.scopes ("%" ++ toString (v+k))) ==>
     ptr_covers Gf tnf ("%" ++ toString v) t (64+M) /\
     ptr_covers Gf tnf ("%" ++ toString (v+1)) t (32+M) /\
     ptr_covers Gf tnf ("%" ++ toString (v+2)) t M)
Proof
  strip_tac >>
  drule_all reason_head_run_mem >>
  disch_then (qx_choosel_then [`B`,`TP`] strip_assume_tac) >>
  rename1 `run_inst_seq (reason_head id v M) s = OK t` >>
  `reason_head id v M = revert_reason_prefix id v M` by
    simp[reason_head_def, revert_reason_prefix_def] >>
  fs[] >>
  `?Gf tnf. inst_seq_ptr ARB 0 ctx func PG G tn
     (reason_head id v M) s Gf tnf` by
    (drule_at (Pat `run_inst_seq _ _ = _`) revert_reason_prefix_checked_path >>
     simp[] >> metis_tac[]) >>
  `!D. inst_seq_ptr D 0 ctx func PG G tn (reason_head id v M) s Gf tnf` by
    (gen_tac >>
     drule_at (Pat `run_inst_seq _ _ = _`) revert_reason_prefix_checked_path >>
     simp[] >> metis_tac[inst_seq_ptr_ghost_unique]) >>
  `!D. inst_seq_ptr D lo ctx func PG G tn (reason_head id v M) s Gf tnf` by
    (gen_tac >> irule inst_seq_ptr_zero_to_lo >> simp[] >>
     qexists_tac `D` >> simp[]) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) []
      (OK (t with vs_inst_idx := s.vs_inst_idx+4),Gf,tnf)` by
    (gen_tac >>
     `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
        (reason_head id v M)` by
       simp[reason_head_def, revert_reason_prefix_def, mk_inst_def, is_terminator_def] >>
     qpat_assum `reason_head _ _ _ = _`
       (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
     first_assum (qspec_then `D` assume_tac) >>
     drule_all run_inst_seq_gas_origin_ptr_path >>
     simp[revert_reason_prefix_def, mk_inst_def]) >>
  qexistsl_tac [`Gf`,`tnf`] >>
  qpat_assum `reason_head _ _ _ = _`
    (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
  simp[] >> conj_tac >- first_assum ACCEPT_TAC >>
  strip_tac >>
  drule_at (Pat `run_inst_seq _ _ = _`) revert_reason_prefix_covers >>
  simp[ADD_COMM] >> metis_tac[]
QED
