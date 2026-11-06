(* Compose ordinary witnesses and checked execution at the ABI suffix boundary. *)
Theory revertReasonTailPtr
Ancestors
  revertReasonSuffixPathPtr revertReasonSuffixRuns revertReasonCopyPtr
  revertReasonRuns revertReasonLayout fragGasPathPtr normalizerAllocationFrame
  stmtSimReason allocaSiteResource venomInst venomState words arithmetic finite_map list rich_list

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
