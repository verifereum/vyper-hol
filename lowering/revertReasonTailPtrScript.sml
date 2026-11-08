(* Compose ordinary witnesses and checked execution at the ABI suffix boundary. *)
Theory revertReasonTailPtr
Ancestors
  revertReasonSuffixPathPtr revertReasonSuffixRuns revertReasonCopyPtr
  revertReasonRuns revertReasonLayout fragGasPathPtr normalizerAllocationFrame
  stmtSimReason allocaSiteResource entrySinkExtraction reasonCopySourcePtr
  exprLoweringProps localPtrsProps venomInst venomState words arithmetic finite_map list rich_list

Theorem revert_reason_suffix_resources_path_ptr:
  lookup_var b s = SOME B /\ lookup_var p s = SOME P /\ lookup_var q s = SOME Q /\
  ptr_covers G tn b s (64+ms) /\
  ptr_covers G tn p s (32+ms) /\ ptr_covers G tn q s ms /\
  mload (w2n Q) s = n2w L /\
  (!j. w2n Q <= j /\ j < w2n Q+32 ==> j NOTIN tn.t_mem) /\
  32 + contractABI$ceil32 L <= ms /\ L+63 < dimword(:256) /\
  64+ms < dimword(:256) /\ w2n B+64+ms < dimword(:256) /\
  w2n P+32+ms < dimword(:256) /\
  (!k. 4 <= k /\ k <= 20 ==>
    b <> STRING #"%" (toString ((v:num)+k)) /\
    p <> STRING #"%" (toString (v+k)) /\ q <> STRING #"%" (toString (v+k))) /\
  ~ctx_has_dalloca ctx /\ alloca_inv s /\ alloca_room ctx fn s /\
  MEM (mk_inst (id+5) ALLOCA [Lit 32w]
    [STRING #"%" (toString (v+4))]) (fn_insts fn) /\
  (!a sz. FLOOKUP s.vs_allocas (id+5) = SOME (a,sz) ==> sz = 32) /\
  FLOOKUP s.vs_allocas parent = SOME (w2n Q,ms) /\ parent <> id+5 /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (revert_reason_suffix id v (Var b) (Var p) (Var q))
    (DROP s.vs_inst_idx bb.bb_instructions) ==>
  ?z Gf tnf j.
    run_inst_seq (revert_reason_suffix id v (Var b) (Var p) (Var q)) s =
      Abort Revert_abort z /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf
      (Abort Revert_abort (z with vs_inst_idx := j))
Proof
  strip_tac >> `32 <= ms` by decide_tac >>
  `reason_operand [b;p;q] (Var b) /\ reason_operand [b;p;q] (Var p) /\
   reason_operand [b;p;q] (Var q) /\ reason_known [b;p;q] s` by
    (simp[reason_operand_def, reason_known_def] >> metis_tac[]) >>
  drule_at (Pat `reason_known _ _`) revert_reason_suffix_run >>
  disch_then (qspecl_then [`v`,`Var q`,`Var p`,`id`,`Var b`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  drule_all revert_reason_size_cell_allocate >> strip_tac >>
  drule_at (Pat `run_inst_seq _ _ = Abort _ _`) revert_reason_suffix_path_ptr >>
  disch_then (drule_at (Pat `ptr_covers _ _ _ _ (64+_)`)) >>
  disch_then (drule_at (Pat `mload _ _ = _`)) >>
  disch_then (drule_at (Pat `step_inst_base _ _ = _`)) >>
  disch_then (drule_at (Pat `run_inst_seq _ _ = OK _`)) >>
  disch_then (drule_at (Pat `lookup_block _ _ = _`)) >>
  disch_then (drule_at (Pat `lookup_var _ _ = SOME _`)) >>
  disch_then (drule_at (Pat `ptr_covers _ _ _ _ (32+_)`)) >>
  disch_then (drule_at (Pat `FLOOKUP _ _ = SOME (_,32)`)) >>
  disch_then (drule_at (Pat `lookup_var b _ = SOME _`)) >>
  disch_then (drule_at (Pat `lookup_var p _ = SOME _`)) >>
  disch_then (qspecl_then [`ctx`,`PG`,`D`] mp_tac) >>
  (impl_tac >- (asm_rewrite_tac[])) >> strip_tac >>
  qexistsl [`z`,`Gf`,`tnf`,`j`] >> simp[]
QED

Theorem revert_reason_tail_resources_path_ptr:
  lookup_var b s = SOME B /\ lookup_var p s = SOME P /\
  lookup_var q s = SOME Q /\ lookup_var src s = SOME A /\
  ptr_covers G tn b s (64+ms) /\ ptr_covers G tn p s (32+ms) /\
  ptr_covers G tn q s ms /\
  ptr_covers G tn src s (32+contractABI$ceil32 L) /\
  mload (w2n A) s = n2w L /\
  (!j. w2n A <= j /\ j < w2n A+32 ==> j NOTIN tn.t_mem) /\
  32+contractABI$ceil32 L <= ms /\ L+63 < dimword(:256) /\
  64+ms < dimword(:256) /\ w2n B+64+ms < dimword(:256) /\
  w2n P+32+ms < dimword(:256) /\
  (!k. k <= 20 ==>
    b <> STRING #"%" (toString ((v:num)+k)) /\
    p <> STRING #"%" (toString (v+k)) /\
    q <> STRING #"%" (toString (v+k)) /\
    src <> STRING #"%" (toString (v+k))) /\
  ~ctx_has_dalloca ctx /\ alloca_inv s /\ alloca_room ctx fn s /\
  MEM (mk_inst (id+5) ALLOCA [Lit 32w]
    [STRING #"%" (toString (v+4))]) (fn_insts fn) /\
  (!a sz. FLOOKUP s.vs_allocas (id+5) = SOME (a,sz) ==> sz = 32) /\
  FLOOKUP s.vs_allocas parent = SOME (w2n Q,ms) /\ parent <> id+5 /\
  ~s.vs_halted /\ lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
  isPREFIX (revert_reason_copy id v (Var q) (Var src))
    (DROP s.vs_inst_idx bb.bb_instructions) /\
  isPREFIX (revert_reason_suffix id v (Var b) (Var p) (Var q))
    (DROP (s.vs_inst_idx+5) bb.bb_instructions) ==>
  ?t z Gf tnf j.
    run_inst_seq (revert_reason_copy id v (Var q) (Var src)) s = OK t /\
    run_inst_seq (revert_reason_suffix id v (Var b) (Var p) (Var q))
      (t with vs_inst_idx := s.vs_inst_idx+5) = Abort Revert_abort z /\
    gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf
      (Abort Revert_abort (z with vs_inst_idx := j))
Proof
  strip_tac >>
  `!k. k < 4 ==> src <> STRING #"%" (toString (v+k)) /\
                    q <> STRING #"%" (toString (v+k))` by simp[] >>
  drule_all revert_reason_copy_run >> disch_then (qspec_then `id` strip_assume_tac) >>
  `ptr_covers G tn q s (32+contractABI$ceil32 L)` by
    metis_tac[ptr_covers_mono] >>
  drule_all revert_reason_copy_boundary_ptr >>
  disch_then (qspecl_then [`PG`,`D`] strip_assume_tac) >>
  `EVERY (\i. i.inst_opcode <> INVOKE /\ ~is_terminator i.inst_opcode)
    (revert_reason_copy id v (Var q) (Var src))` by
    simp[NoAsms, revert_reason_copy_def, mk_inst_def, is_terminator_def] >>
  drule_all run_inst_seq_preserves_entry_control >> strip_tac >>
  `alloca_inv (t with vs_inst_idx := s.vs_inst_idx+5) /\
   alloca_room ctx fn (t with vs_inst_idx := s.vs_inst_idx+5)` by
    (conj_tac >- (irule alloca_inv_fields >> qexists_tac `s` >> simp[]) >>
     irule alloca_room_fields >> qexists_tac `s` >> simp[]) >>
  `lookup_var b (t with vs_inst_idx := s.vs_inst_idx+5) = SOME B /\
   ptr_covers Gf tnf b (t with vs_inst_idx := s.vs_inst_idx+5) (64+ms)` by
    (first_x_assum (qspecl_then [`b`,`64+ms`] mp_tac) >>
     asm_rewrite_tac[] >>
     (impl_tac >- (rpt strip_tac >> qpat_x_assum `!k. k <= 20 ==> _`
       (qspec_then `k` mp_tac) >> asm_rewrite_tac[] >> decide_tac)) >>
     strip_tac >> asm_rewrite_tac[]) >>
  `lookup_var p (t with vs_inst_idx := s.vs_inst_idx+5) = SOME P /\
   ptr_covers Gf tnf p (t with vs_inst_idx := s.vs_inst_idx+5) (32+ms)` by
    (qpat_x_assum `!x C. _ /\ ptr_covers _ _ x _ C ==> _` (qspecl_then [`p`,`32+ms`] mp_tac) >>
     asm_rewrite_tac[] >>
     (impl_tac >- (rpt strip_tac >> qpat_x_assum `!k. k <= 20 ==> _`
       (qspec_then `k` mp_tac) >> asm_rewrite_tac[] >> decide_tac)) >>
     strip_tac >> asm_rewrite_tac[]) >>
  `lookup_var q (t with vs_inst_idx := s.vs_inst_idx+5) = SOME Q /\
   ptr_covers Gf tnf q (t with vs_inst_idx := s.vs_inst_idx+5) ms` by
    (qpat_x_assum `!x C. _ /\ ptr_covers _ _ x _ C ==> _` (qspecl_then [`q`,`ms`] mp_tac) >>
     asm_rewrite_tac[] >>
     (impl_tac >- (rpt strip_tac >> qpat_x_assum `!k. k <= 20 ==> _`
       (qspec_then `k` mp_tac) >> asm_rewrite_tac[] >> decide_tac)) >>
     strip_tac >> asm_rewrite_tac[]) >>
  `?z G2 tn2 j.
    run_inst_seq (revert_reason_suffix id v (Var b) (Var p) (Var q))
      (t with vs_inst_idx := s.vs_inst_idx+5) = Abort Revert_abort z /\
    gas_path_ptr D 0 ctx fn PG Gf tnf (t with vs_inst_idx := s.vs_inst_idx+5)
      0 G2 tn2 (Abort Revert_abort (z with vs_inst_idx := j))` by
    (irule revert_reason_suffix_resources_path_ptr >>
     asm_rewrite_tac[venom_state_accfupds, combinTheory.K_THM] >>
     conj_tac >- (rpt strip_tac >> qpat_x_assum `!k. k <= 20 ==> _`
       (qspec_then `k` mp_tac) >> asm_rewrite_tac[] >> simp[NoAsms]) >>
     conj_tac >- (qexists_tac `bb` >> asm_rewrite_tac[]) >>
     qexistsl_tac [`B`,`L`,`P`,`Q`,`ms`,`parent`] >> asm_rewrite_tac[]) >>
  qexistsl_tac [`t`,`z`,`G2`,`tn2`,`j`] >> asm_rewrite_tac[] >>
  drule_all gas_path_ptr_then >> simp[]
QED
