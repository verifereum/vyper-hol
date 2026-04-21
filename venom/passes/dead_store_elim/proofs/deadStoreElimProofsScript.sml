(*
 * Dead Store Elimination — Proofs
 *
 * Corrected theorems with complete precondition sets:
 *   - alloca_inv s: alloca regions are non-overlapping (runtime invariant)
 *   - bp_ptrs_bounded bp fn s: analysis-identified alloca accesses
 *     stay within their allocation bounds (analysis-to-runtime bridge)
 *   - bp_ptr_sound bp s: analysis-computed addresses match runtime (Thm2)
 *
 * This matches the MCE pattern (alloca_inv + bp_ptrs_bounded +
 * bp_ptr_sound). The three together ensure that if may_overlap says
 * two alloca-backed accesses don't alias (different allocations),
 * they genuinely don't overlap at runtime.
 *
 * The ORIGINAL frozen theorems are FALSE: formal counterexamples
 * (_FALSE theorems below) show that pointer arithmetic (ADD) across
 * adjacent ALLOCA regions can cause bp_analyze to miss aliasing.
 * The original Thm1 lacked bp_ptrs_bounded entirely; Thm2 had a
 * vacuously-quantified bp (FEMPTY trivially satisfies bp_ptr_sound/
 * bp_ptrs_bounded).
 *
 * Neither alloca_inv nor alloca_safe_access can replace
 * bp_ptrs_bounded: the counterexample satisfies both (ptr1_adj=32
 * falls within Allocation 1's bounds), but bp_ptrs_bounded correctly
 * fails because the analysis says ptr1_adj is in Allocation 0 (offset
 * 32 exceeds Allocation 0's size of 32).
 *)

Theory deadStoreElimProofs
Ancestors
  deadStoreElimDefs passSimulationProps basePtrProps passSharedProps While
  venomMemProps memAliasDefs passSharedField cfgAnalysisProps
  stateEquiv stateEquivProps venomState venomInst
  passSimulationDefs passSharedDefs execEquivParamDefs
  vfmTypes byte fcp memLocDefs
  dfIterateDefs finite_map basePtrDefs
  venomExecSemantics

(* ===== dse_equiv / dse_all_equiv properties ===== *)

Triviality dse_equiv_refl:
  !space s. dse_equiv space s s
Proof
  simp[dse_equiv_def]
QED

Triviality dse_equiv_trans:
  !space s1 s2 s3.
    dse_equiv space s1 s2 /\ dse_equiv space s2 s3 ==>
    dse_equiv space s1 s3
Proof
  simp[dse_equiv_def] >> metis_tac[]
QED

Triviality dse_equiv_implies_all:
  !space s1 s2. dse_equiv space s1 s2 ==> dse_all_equiv s1 s2
Proof
  simp[dse_equiv_def, dse_all_equiv_def]
QED

Triviality dse_all_equiv_refl:
  !s. dse_all_equiv s s
Proof
  simp[dse_all_equiv_def]
QED

Triviality dse_all_equiv_trans:
  !s1 s2 s3.
    dse_all_equiv s1 s2 /\ dse_all_equiv s2 s3 ==>
    dse_all_equiv s1 s3
Proof
  simp[dse_all_equiv_def] >> metis_tac[]
QED

(* ===== Bridge lemmas ===== *)

Triviality state_equiv_empty_implies_dse_equiv:
  !space s1 s2. state_equiv {} s1 s2 ==> dse_equiv space s1 s2
Proof
  simp[state_equiv_def, execution_equiv_def, dse_equiv_def,
       lookup_var_def] >>
  rpt strip_tac >>
  `FLOOKUP s1.vs_vars v = FLOOKUP s2.vs_vars v`
    by metis_tac[pred_setTheory.NOT_IN_EMPTY] >> gvs[]
QED

Triviality execution_equiv_empty_implies_dse_equiv:
  !space s1 s2. execution_equiv {} s1 s2 ==> dse_equiv space s1 s2
Proof
  simp[execution_equiv_def, dse_equiv_def, lookup_var_def] >>
  rpt strip_tac >>
  first_x_assum (qspec_then `v` mp_tac) >> simp[]
QED

(* ===== lift_result composition lemmas ===== *)

Triviality lift_result_dse_equiv_trans:
  !space r1 r2 r3.
    lift_result (dse_equiv space) (dse_equiv space) (dse_equiv space) r1 r2 /\
    lift_result (dse_equiv space) (dse_equiv space) (dse_equiv space) r2 r3 ==>
    lift_result (dse_equiv space) (dse_equiv space) (dse_equiv space) r1 r3
Proof
  Cases_on `r1` >> Cases_on `r2` >> Cases_on `r3` >>
  simp[lift_result_def] >> metis_tac[dse_equiv_trans]
QED

Triviality lift_result_dse_all_equiv_trans:
  !r1 r2 r3.
    lift_result dse_all_equiv dse_all_equiv dse_all_equiv r1 r2 /\
    lift_result dse_all_equiv dse_all_equiv dse_all_equiv r2 r3 ==>
    lift_result dse_all_equiv dse_all_equiv dse_all_equiv r1 r3
Proof
  Cases_on `r1` >> Cases_on `r2` >> Cases_on `r3` >>
  simp[lift_result_def] >> metis_tac[dse_all_equiv_trans]
QED

Triviality lift_result_dse_equiv_to_all:
  !space r1 r2.
    lift_result (dse_equiv space) (dse_equiv space) (dse_equiv space) r1 r2 ==>
    lift_result dse_all_equiv dse_all_equiv dse_all_equiv r1 r2
Proof
  Cases_on `r1` >> Cases_on `r2` >>
  simp[lift_result_def] >> metis_tac[dse_equiv_implies_all]
QED

(* Compose error-or-lift_result chains: if r1=Error, done.
   Otherwise lift_result R r1 r2, then r2 can't be Error either,
   so lift_result R r2 r3, and transitivity gives lift_result R r1 r3. *)
Triviality lift_result_or_error_trans:
  !R (r1:exec_result) r2 r3.
    ((?e. r1 = Error e) \/ lift_result R R R r1 r2) /\
    ((?e. r2 = Error e) \/ lift_result R R R r2 r3) /\
    (!s1 s2 s3. R s1 s2 /\ R s2 s3 ==> R s1 s3) ==>
    (?e. r1 = Error e) \/ lift_result R R R r1 r3
Proof
  Cases_on `r1` >> Cases_on `r2` >> Cases_on `r3` >>
  simp[lift_result_def] >> metis_tac[]
QED

(* Bridge: error-or-lift_result with dse_equiv to dse_all_equiv *)
Triviality lift_result_or_error_equiv_to_all:
  !space (r1:exec_result) r2.
    ((?e. r1 = Error e) \/ lift_result (dse_equiv space) (dse_equiv space) (dse_equiv space) r1 r2) ==>
    (?e. r1 = Error e) \/ lift_result dse_all_equiv dse_all_equiv dse_all_equiv r1 r2
Proof
  rpt strip_tac >> gvs[] >>
  disj2_tac >> irule lift_result_dse_equiv_to_all >> qexists `space` >> simp[]
QED

(* ===== Single-pass correctness helpers ===== *)


(* H1: get_instruction in transformed block *)
Triviality get_instruction_block_map_transform:
  !f bb idx.
    get_instruction (block_map_transform f bb) idx =
    case get_instruction bb idx of NONE => NONE | SOME i => SOME (f i)
Proof
  simp[get_instruction_def, block_map_transform_def] >>
  rw[] >> simp[listTheory.EL_MAP]
QED

(* H2: block_map_transform preserves label *)
Triviality block_map_transform_label:
  !f bb. (block_map_transform f bb).bb_label = bb.bb_label
Proof
  simp[block_map_transform_def]
QED

(* H3: lookup_block in dse_single_pass *)
Triviality lookup_block_dse_single_pass:
  !lbl fn dead_ids space.
    lookup_block lbl (dse_single_pass dead_ids space fn).fn_blocks =
    OPTION_MAP (block_map_transform (dse_inst dead_ids space))
      (lookup_block lbl fn.fn_blocks)
Proof
  simp[dse_single_pass_def, function_map_transform_def] >>
  rpt gen_tac >> irule lookup_block_map >> simp[block_map_transform_label]
QED

(* H4: memory_def_opcode is not a terminator *)
Triviality memory_def_opcode_not_terminator:
  !space op. is_memory_def_opcode space op ==> ~is_terminator op
Proof
  Cases_on `space` >> simp[is_memory_def_opcode_def] >>
  strip_tac >> Cases_on `op` >>
  gvs[is_terminator_def] >> EVAL_TAC
QED

(* H5: dse_inst preserves is_terminator *)
Triviality dse_inst_is_terminator:
  !dead_ids space inst.
    is_terminator (dse_inst dead_ids space inst).inst_opcode =
    is_terminator inst.inst_opcode
Proof
  rw[dse_inst_def] >>
  simp[mk_nop_inst_def, is_terminator_def] >>
  metis_tac[memory_def_opcode_not_terminator]
QED

(* H6: NOP semantics *)
Triviality step_inst_base_nop:
  !inst s. step_inst_base (mk_nop_inst inst) s = OK s
Proof
  simp[step_inst_base_def, mk_nop_inst_def]
QED

(* H7: step_inst for NOP (non-INVOKE) *)
Triviality step_inst_nop:
  !fuel ctx inst s. step_inst fuel ctx (mk_nop_inst inst) s = OK s
Proof
  rpt gen_tac >>
  `(mk_nop_inst inst).inst_opcode <> INVOKE` by simp[mk_nop_inst_def] >>
  simp[step_inst_non_invoke, step_inst_base_nop]
QED

(* H8: run_blocks never returns OK *)
Triviality run_blocks_never_ok:
  !fuel ctx fn s s'. run_blocks fuel ctx fn s <> OK s'
Proof
  completeInduct_on `fuel` >> rw[Once run_blocks_def] >>
  rpt (CASE_TAC >> fs[])
QED

(* ================================================================== *)
(* CORRECTNESS PROOF HELPERS                                          *)
(* ================================================================== *)


(* --- Entry label preservation --- *)

Triviality fmt_preserves_entry_label:
  !bt fn. (!bb. (bt bb).bb_label = bb.bb_label) ==>
    fn_entry_label (function_map_transform bt fn) = fn_entry_label fn
Proof
  rw[fn_entry_label_def, entry_block_def, function_map_transform_def] >>
  Cases_on `fn.fn_blocks` >> simp[]
QED

Triviality clear_nops_preserves_entry_label:
  !fn. fn_entry_label (clear_nops_function fn) = fn_entry_label fn
Proof
  rw[fn_entry_label_def, entry_block_def, clear_nops_function_def] >>
  Cases_on `fn.fn_blocks` >> simp[clear_nops_block_def]
QED

Triviality dse_single_pass_preserves_entry_label:
  !dead_ids space fn.
    fn_entry_label (dse_single_pass dead_ids space fn) = fn_entry_label fn
Proof
  rw[dse_single_pass_def] >> irule fmt_preserves_entry_label >>
  simp[block_map_transform_label]
QED

Triviality dse_iterate_preserves_entry_label:
  !analysis_fn space fn fn'.
    dse_iterate analysis_fn space fn = SOME fn' ==>
    fn_entry_label fn' = fn_entry_label fn
Proof
  rpt strip_tac >> gvs[dse_iterate_def] >>
  qpat_x_assum `OWHILE _ _ _ = _` mp_tac >>
  MAP_EVERY qid_spec_tac [`fn'`, `fn`] >>
  ho_match_mp_tac OWHILE_IND >> rw[] >>
  gvs[dse_single_pass_preserves_entry_label]
QED

Triviality dse_function_space_preserves_entry_label:
  !analysis_fn space fn.
    fn_entry_label (dse_function_space analysis_fn space fn) = fn_entry_label fn
Proof
  rw[dse_function_space_def] >>
  Cases_on `dse_iterate (analysis_fn space) space fn` >>
  simp[clear_nops_preserves_entry_label] >>
  imp_res_tac dse_iterate_preserves_entry_label
QED



(* ================================================================== *)
(* COUNTEREXAMPLE: Both theorems are FALSE as stated                  *)
(*                                                                    *)
(* Root cause: bp_analyze assigns different Allocation IDs to adjacent *)
(* ALLOCAs and concludes they don't alias. But pointer arithmetic     *)
(* (ADD) from one allocation reaches into the adjacent one. The       *)
(* preconditions don't prevent this because:                          *)
(* - Theorem 1: no bp_ptr_sound/bp_ptrs_bounded at all               *)
(* - Theorem 2: bp is universally quantified, unrelated to bp_analyze *)
(* ================================================================== *)


Triviality dimindex_256:
  dimindex(:256) = 256
Proof
  simp[index_bit0, finite_bit0, index_one, finite_one]
QED

Triviality w2n_32_256:
  w2n (32w:256 word) = 32
Proof
  simp[wordsTheory.w2n_n2w, wordsTheory.dimword_def, dimindex_256]
QED

Triviality w2n_1_256:
  w2n (1w:256 word) = 1
Proof
  simp[wordsTheory.w2n_n2w, wordsTheory.dimword_def, dimindex_256]
QED
(*
 * COUNTEREXAMPLE FUNCTION
 *
 *   Block A: ALLOCA 32 → ptr1 (id=0), ALLOCA 32 → ptr2 (id=1),
 *            ADD(ptr1, 32w) → ptr1_adj (id=2), JMP B (id=3)
 *   Block B: MSTORE [ptr1_adj, 42w] (id=4), MLOAD [ptr2] → result (id=5),
 *            STOP (id=6)
 *
 * bp_analyze: ptr1 → Allocation 0, ptr2 → Allocation 1,
 *             ptr1_adj → Allocation 0 offset 32.
 * may_overlap(Alloc 0 off 32, Alloc 1 off 0) = F (different allocations)
 * → MSTORE at id=4 classified as dead.
 *
 * At runtime (via run_function, starting at entry "A"):
 *   ptr1 = next_alloca_offset(s) = MAX 0 0 = 0
 *   ptr2 = MAX 32 0 = 32
 *   ptr1_adj = ptr1 + 32 = 0 + 32 = 32 = ptr2  ← ALIASED!
 *
 * Original: MSTORE writes 42w at ptr1_adj=32, MLOAD reads at ptr2=32 → 42w
 * Transformed: MSTORE NOP'd, MLOAD reads at ptr2=32 → 0w
 * 42w ≠ 0w → dse_equiv violated.
 *)

Definition cex_fn_def:
  cex_fn = <| fn_name := "test"; fn_blocks :=
    [<| bb_label := "A"; bb_instructions :=
        [<| inst_id := 0; inst_opcode := ALLOCA;
            inst_operands := [Lit 32w]; inst_outputs := ["ptr1"] |>;
         <| inst_id := 1; inst_opcode := ALLOCA;
            inst_operands := [Lit 32w]; inst_outputs := ["ptr2"] |>;
         <| inst_id := 2; inst_opcode := ADD;
            inst_operands := [Var "ptr1"; Lit 32w]; inst_outputs := ["ptr1_adj"] |>;
         <| inst_id := 3; inst_opcode := JMP;
            inst_operands := [Label "B"]; inst_outputs := [] |>] |>;
     <| bb_label := "B"; bb_instructions :=
        [<| inst_id := 4; inst_opcode := MSTORE;
            inst_operands := [Var "ptr1_adj"; Lit 42w]; inst_outputs := [] |>;
         <| inst_id := 5; inst_opcode := MLOAD;
            inst_operands := [Var "ptr2"]; inst_outputs := ["result"] |>;
         <| inst_id := 6; inst_opcode := STOP;
            inst_operands := []; inst_outputs := [] |>] |>] |>
End

Definition cex_analysis_fn_def:
  cex_analysis_fn (sp:addr_space) (fn':ir_function) =
    if sp = AddrSp_Memory /\ fn' = cex_fn then {4:num} else {}
End

(* Initial state: empty, run_function will set current_bb *)
Definition cex_state_def:
  cex_state = <|
    vs_memory := [];
    vs_transient := K (K 0w);
    vs_vars := FEMPTY;
    vs_prev_bb := NONE; vs_current_bb := ""; vs_inst_idx := 0;
    vs_returndata := []; vs_halted := F;
    vs_accounts := K ARB; vs_call_ctx := ARB;
    vs_tx_ctx := ARB; vs_block_ctx := ARB;
    vs_logs := []; vs_immutables := FEMPTY; vs_data_section := [];
    vs_labels := FEMPTY |+ ("A", 0w:256 word) |+ ("B", 0w);
    vs_code := []; vs_params := [];
    vs_prev_hashes := []; vs_allocas := FEMPTY; vs_alloca_next := 0
  |>
End

(* --- bp_analyze computes the expected base pointer map --- *)


Definition cex_bp_def:
  cex_bp = FEMPTY |+ ("ptr1_adj", [Ptr (Allocation 0) (SOME 32)])
                  |+ ("ptr2", [Ptr (Allocation 1) (SOME 0)])
                  |+ ("ptr1", [Ptr (Allocation 0) (SOME 0)])
End

Triviality cex_bp_analyze:
  bp_analyze (cfg_analyze cex_fn) cex_fn = cex_bp
Proof
  simp[bp_analyze_def, df_iterate_def] >>
  `(cfg_analyze cex_fn).cfg_dfs_pre = ["A"; "B"]` by EVAL_TAC >>
  simp[] >>
  `SND (bp_one_pass cex_fn ["A"; "B"] FEMPTY) = cex_bp`
    by (EVAL_TAC >> simp[FUPDATE_COMMUTES, cex_bp_def, w2n_32_256]) >>
  `SND (bp_one_pass cex_fn ["A"; "B"] cex_bp) = cex_bp`
    by (EVAL_TAC >> simp[FUPDATE_EQ, FUPDATE_COMMUTES, cex_bp_def,
                         w2n_32_256]) >>
  once_rewrite_tac[WHILE] >> simp[] >>
  `cex_bp <> FEMPTY` by simp[cex_bp_def] >>
  simp[] >>
  once_rewrite_tac[WHILE] >> simp[]
QED

(* --- all_dead_stores holds for the counterexample --- *)

Triviality cex_all_dead_stores:
  all_dead_stores {4} (cfg_analyze cex_fn) FEMPTY cex_bp AddrSp_Memory cex_fn
Proof
  simp[all_dead_stores_def] >>
  qexists `EL 1 cex_fn.fn_blocks` >> qexists `0:num` >>
  rpt conj_tac
  >- EVAL_TAC >- EVAL_TAC >- EVAL_TAC >- EVAL_TAC
  >- (EVAL_TAC >> simp[w2n_32_256])
  >- (EVAL_TAC >> simp[w2n_32_256])
  >- EVAL_TAC >- EVAL_TAC >>
  (* ¬dse_mem_def_live *)
  rw[dse_mem_def_live_def]
  >- ((* same-block: j∈{1,2} → reads_alias=F *)
      spose_not_then assume_tac >> gvs[] >>
      `LENGTH (EL 1 cex_fn.fn_blocks).bb_instructions = 3`
        by EVAL_TAC >>
      `j = 1 \/ j = 2` by decide_tac >>
      gvs[] >>
      qpat_x_assum `dse_inst_reads_alias _ _ _ _ _` mp_tac >>
      EVAL_TAC >> simp[w2n_32_256])
  >- ((* successor: cfg_succs_of "B" = [] *)
      disj2_tac >> disj1_tac >>
      EVAL_TAC)
QED

(* --- The full precondition holds (for all fn') --- *)

Triviality cex_precondition:
  !sp fn'. all_dead_stores (cex_analysis_fn sp fn')
             (cfg_analyze fn') FEMPTY (bp_analyze (cfg_analyze fn') fn')
             sp fn'
Proof
  rpt gen_tac >> simp[cex_analysis_fn_def] >>
  IF_CASES_TAC
  >- (gvs[cex_bp_analyze, cex_all_dead_stores])
  >- simp[all_dead_stores_def]
QED

(* --- dse_function_space transforms as expected --- *)

Triviality cex_single_pass:
  dse_single_pass {4} AddrSp_Memory cex_fn =
  <| fn_name := "test"; fn_blocks :=
    [<| bb_label := "A"; bb_instructions :=
        [<| inst_id := 0; inst_opcode := ALLOCA;
            inst_operands := [Lit 32w]; inst_outputs := ["ptr1"] |>;
         <| inst_id := 1; inst_opcode := ALLOCA;
            inst_operands := [Lit 32w]; inst_outputs := ["ptr2"] |>;
         <| inst_id := 2; inst_opcode := ADD;
            inst_operands := [Var "ptr1"; Lit 32w]; inst_outputs := ["ptr1_adj"] |>;
         <| inst_id := 3; inst_opcode := JMP;
            inst_operands := [Label "B"]; inst_outputs := [] |>] |>;
     <| bb_label := "B"; bb_instructions :=
        [<| inst_id := 4; inst_opcode := NOP;
            inst_operands := []; inst_outputs := [] |>;
         <| inst_id := 5; inst_opcode := MLOAD;
            inst_operands := [Var "ptr2"]; inst_outputs := ["result"] |>;
         <| inst_id := 6; inst_opcode := STOP;
            inst_operands := []; inst_outputs := [] |>] |>] |>
Proof
  EVAL_TAC
QED

Triviality cex_analysis_fn_after_nop:
  cex_analysis_fn AddrSp_Memory (dse_single_pass {4} AddrSp_Memory cex_fn) = {}
Proof
  simp[cex_analysis_fn_def] >>
  rewrite_tac[cex_single_pass] >> EVAL_TAC
QED

Definition cex_fn_transformed_def:
  cex_fn_transformed = <| fn_name := "test"; fn_blocks :=
    [<| bb_label := "A"; bb_instructions :=
        [<| inst_id := 0; inst_opcode := ALLOCA;
            inst_operands := [Lit 32w]; inst_outputs := ["ptr1"] |>;
         <| inst_id := 1; inst_opcode := ALLOCA;
            inst_operands := [Lit 32w]; inst_outputs := ["ptr2"] |>;
         <| inst_id := 2; inst_opcode := ADD;
            inst_operands := [Var "ptr1"; Lit 32w]; inst_outputs := ["ptr1_adj"] |>;
         <| inst_id := 3; inst_opcode := JMP;
            inst_operands := [Label "B"]; inst_outputs := [] |>] |>;
     <| bb_label := "B"; bb_instructions :=
        [<| inst_id := 5; inst_opcode := MLOAD;
            inst_operands := [Var "ptr2"]; inst_outputs := ["result"] |>;
         <| inst_id := 6; inst_opcode := STOP;
            inst_operands := []; inst_outputs := [] |>] |>] |>
End

Triviality cex_iterate:
  dse_iterate (cex_analysis_fn AddrSp_Memory) AddrSp_Memory cex_fn =
  SOME (dse_single_pass {4} AddrSp_Memory cex_fn)
Proof
  simp[dse_iterate_def] >>
  once_rewrite_tac[OWHILE_THM] >>
  simp[cex_analysis_fn_def] >>
  rewrite_tac[cex_single_pass] >> EVAL_TAC >>
  once_rewrite_tac[OWHILE_THM] >>
  simp[cex_analysis_fn_def]
QED

Triviality cex_clear_nops:
  clear_nops_function (dse_single_pass {4} AddrSp_Memory cex_fn) =
  cex_fn_transformed
Proof
  rewrite_tac[cex_single_pass, cex_fn_transformed_def] >> EVAL_TAC
QED

Triviality cex_function_space:
  dse_function_space cex_analysis_fn AddrSp_Memory cex_fn = cex_fn_transformed
Proof
  simp[dse_function_space_def, cex_iterate, cex_clear_nops]
QED

Triviality OWHILE_FALSE:
  !G f s. ~G s ==> OWHILE G f s = SOME s
Proof
  rpt strip_tac >> once_rewrite_tac[OWHILE_THM] >> simp[]
QED

Triviality cex_iterate_identity:
  !sp. dse_iterate (cex_analysis_fn sp) sp cex_fn_transformed =
       SOME cex_fn_transformed
Proof
  gen_tac >> simp[dse_iterate_def] >>
  irule OWHILE_FALSE >> simp[cex_analysis_fn_def] >> EVAL_TAC
QED

Triviality cex_function_space_identity:
  !sp. dse_function_space cex_analysis_fn sp cex_fn_transformed =
       cex_fn_transformed
Proof
  simp[dse_function_space_def, cex_iterate_identity] >> EVAL_TAC
QED

(* dse_function composes three passes; only Memory changes cex_fn *)
Triviality cex_dse_function:
  dse_function cex_analysis_fn cex_fn = cex_fn_transformed
Proof
  simp[dse_function_def, cex_function_space, cex_function_space_identity]
QED

(* --- Execution divergence (run_function version) ---
   Both executions start at entry block A, execute identical ALLOCAs,
   then jump to block B. At block B:
   - Original: MSTORE writes 42w at ptr1_adj=32, then MLOAD reads at ptr2=32 → 42w
   - Transformed: NOP'd MSTORE, MLOAD reads at ptr2=32 from zero-init memory → 0w

   We prove: after block A, ptr1_adj = ptr2 = 32w (the pointers alias).
   This is the key runtime fact that bp_analyze misses. *)

(* After executing block A from entry state *)
Triviality cex_after_block_A:
  exec_block 0 ARB (EL 0 cex_fn.fn_blocks)
    (cex_state with <| vs_current_bb := "A"; vs_inst_idx := 0 |>) =
  OK <| vs_memory := []; vs_transient := K (K 0w);
        vs_vars := FEMPTY |+ ("ptr1", 0w:256 word)
                          |+ ("ptr2", n2w (w2n (32w:256 word)))
                          |+ ("ptr1_adj", 0w + 32w);
        vs_prev_bb := SOME "A"; vs_current_bb := "B"; vs_inst_idx := 0;
        vs_returndata := []; vs_halted := F;
        vs_accounts := K ARB; vs_call_ctx := ARB;
        vs_tx_ctx := ARB; vs_block_ctx := ARB;
        vs_logs := []; vs_immutables := FEMPTY; vs_data_section := [];
        vs_labels := FEMPTY |+ ("A", 0w) |+ ("B", 0w);
        vs_code := []; vs_params := [];
        vs_prev_hashes := [];
        vs_allocas := FEMPTY |+ (0, (0, w2n (32w:256 word)))
                             |+ (1, (w2n (32w:256 word), w2n (32w:256 word)));
        vs_alloca_next := w2n (32w:256 word) + w2n (32w:256 word) |>
Proof
  EVAL_TAC
QED

(* The key aliasing fact: ptr1_adj = ptr2 at runtime *)
Triviality cex_ptrs_alias:
  (0w:256 word) + 32w = n2w (w2n (32w:256 word))
Proof
  simp[w2n_32_256]
QED

(* 42w ≠ 0w at 256 bits *)
Triviality w42_neq_0:
  (42w:256 word) <> 0w
Proof
  simp[wordsTheory.dimword_def, dimindex_256]
QED

(* bp_ptrs_bounded FEMPTY is vacuously true (no alloca-based locations) *)
Triviality bp_ptrs_bounded_FEMPTY:
  !fn s. bp_ptrs_bounded FEMPTY fn s
Proof
  simp[bp_ptrs_bounded_def] >> rpt strip_tac >>
  Cases_on `ops.iao_ofst` >>
  gvs[bp_segment_from_ops_def, LET_THM, bp_ptr_from_op_def,
      bp_get_ptrs_def, FLOOKUP_DEF, ml_undefined_def]
QED

(* ===== End-to-end negation: both frozen theorems are FALSE ===== *)
(*
 * The frozen statements use run_blocks with universally-quantified s.
 * We use cex_state with vs_current_bb := "A" (entry block) as the state.
 *)

(* Byte-level helpers for showing result divergence *)

Triviality get_byte_0w:
  !a be. get_byte a (0w:'a word) be = 0w
Proof
  simp[byteTheory.get_byte_def, wordsTheory.ZERO_SHIFT, wordsTheory.w2w_0]
QED

Triviality word_to_bytes_aux_0w:
  !n be. word_to_bytes_aux n (0w:'a word) be = REPLICATE n (0w:8 word)
Proof
  Induct_on `n` >>
  simp[byteTheory.word_to_bytes_aux_def, get_byte_0w,
       GSYM listTheory.SNOC_APPEND, rich_listTheory.SNOC_REPLICATE]
QED

Triviality word_of_bytes_zero:
  word_of_bytes T (0w:256 word) (REPLICATE 32 (0w:8 word)) = 0w
Proof
  `REPLICATE 32 (0w:8 word) = word_to_bytes (0w:256 word) T`
    by simp[byteTheory.word_to_bytes_def, dimindex_256, word_to_bytes_aux_0w] >>
  simp[vfmTypesTheory.word_to_bytes_word_of_bytes_256]
QED

Triviality w2n_0w_plus_32w:
  w2n (0w + 32w : 256 word) = 32
Proof
  simp[wordsTheory.WORD_ADD_0, w2n_32_256]
QED

Triviality w2n_n2w_w2n_32:
  w2n (n2w (w2n (32w : 256 word)) : 256 word) = 32
Proof
  simp[w2n_32_256, wordsTheory.w2n_n2w, wordsTheory.dimword_def, dimindex_256]
QED

Triviality dimindex_256_div_8:
  dimindex(:256) DIV 8 = 32
Proof
  simp[dimindex_256]
QED

(* List algebra helpers for mstore/mload roundtrip at offset 32 *)

Triviality drop_replicate_32:
  !x rest. DROP 32 (REPLICATE 32 (x:'a) ++ rest) = rest
Proof
  rpt gen_tac >>
  `LENGTH (REPLICATE 32 (x:'a)) = 32` by simp[] >>
  metis_tac[rich_listTheory.DROP_LENGTH_APPEND]
QED

Triviality wta_32_is_word_to_bytes:
  !w be. word_to_bytes_aux 32 (w:256 word) be = word_to_bytes w be
Proof
  simp[byteTheory.word_to_bytes_def, dimindex_256]
QED

Triviality take_word_to_bytes_32:
  !w be rest. TAKE 32 (word_to_bytes (w:256 word) be ++ rest) =
              word_to_bytes w be
Proof
  rpt gen_tac >>
  `LENGTH (word_to_bytes (w:256 word) be) = 32`
    by simp[byteTheory.LENGTH_word_to_bytes, dimindex_256] >>
  metis_tac[rich_listTheory.TAKE_LENGTH_APPEND]
QED

Triviality take_replicate_64_32:
  TAKE 32 (REPLICATE 64 (0w:8 word)) = REPLICATE 32 0w
Proof
  EVAL_TAC
QED

(* Abbreviation for the counterexample state *)
Definition cex_entry_state_def:
  cex_entry_state = cex_state with vs_current_bb := "A"
End

(* Shared: evaluate run_blocks, excluding stuck 256-bit word ops *)
val cex_eval_conv =
  computeLib.RESTR_EVAL_CONV [``word_of_bytes``, ``word_to_bytes_aux``];

(* Original: run_blocks produces Halt with result = 42w *)
Triviality cex_orig_is_halt:
  ?s. run_blocks 2 ARB cex_fn cex_entry_state = Halt s
Proof
  simp[cex_entry_state_def] >>
  CONV_TAC (DEPTH_CONV (fn t =>
    if can (match_term ``run_blocks n ctx fn st``) t
    then cex_eval_conv t else raise UNCHANGED)) >>
  simp[SF SFY_ss]
QED

Triviality cex_run_orig:
  FLOOKUP (let s = (case run_blocks 2 ARB cex_fn cex_entry_state
                     of Halt s => s | _ => ARB) in s.vs_vars)
    "result" = SOME (42w:256 word)
Proof
  simp[cex_entry_state_def] >>
  computeLib.RESTR_EVAL_TAC [``word_of_bytes``, ``word_to_bytes_aux``] >>
  simp[w2n_0w_plus_32w, w2n_n2w_w2n_32, dimindex_256_div_8,
       wta_32_is_word_to_bytes, take_replicate_64_32,
       drop_replicate_32, take_word_to_bytes_32,
       vfmTypesTheory.word_to_bytes_word_of_bytes_256]
QED

(* Transformed: run_blocks produces Halt with result = 0w *)
Triviality cex_trans_is_halt:
  ?s. run_blocks 2 ARB cex_fn_transformed cex_entry_state = Halt s
Proof
  simp[cex_entry_state_def] >>
  CONV_TAC (DEPTH_CONV (fn t =>
    if can (match_term ``run_blocks n ctx fn st``) t
    then cex_eval_conv t else raise UNCHANGED)) >>
  simp[SF SFY_ss]
QED

Triviality cex_run_trans:
  FLOOKUP (let s = (case run_blocks 2 ARB cex_fn_transformed cex_entry_state
                     of Halt s => s | _ => ARB) in s.vs_vars)
    "result" = SOME (0w:256 word)
Proof
  simp[cex_entry_state_def] >>
  computeLib.RESTR_EVAL_TAC [``word_of_bytes``] >>
  simp[w2n_n2w_w2n_32] >>
  once_rewrite_tac[GSYM $ EVAL ``REPLICATE 32 (0w:8 word)``] >>
  simp[word_of_bytes_zero]
QED

(* --- Shared counterexample tactic for both frozen theorem negations --- *)
(* Both proofs follow the same pattern:
   1. Instantiate with cex_analysis_fn, cex_fn, cex_entry_state
   2. Simplify the transform (cex_function_space / cex_dse_function)
   3. Both calls produce Halt → extract "result" variable
   4. Original has 42w, transformed has 0w → contradiction *)


(* Per-space DSE preserves dse_equiv: eliminating dead stores for one address
   space preserves all observable state except possibly the target space's
   memory/storage/transient.

   Precondition chain:
   alloca_inv s: alloca regions are non-overlapping → different allocas
                  don't share bytes at runtime
   bp_ptrs_bounded: alloca-backed accesses stay within their
                     analysis-identified allocation → if may_overlap
                     says two accesses are in different allocations, they
                     genuinely don't overlap at runtime *)
Theorem dse_function_space_correct_proof:
  !analysis_fn space fuel ctx fn s.
    alloca_inv s /\
    bp_ptrs_bounded (bp_analyze (cfg_analyze fn) fn) fn s /\
    (!fn'. all_dead_stores (analysis_fn space fn')
             (cfg_analyze fn') FEMPTY (bp_analyze (cfg_analyze fn') fn')
             space fn') ==>
    lift_result (dse_equiv space) (dse_equiv space) (dse_equiv space)
      (run_blocks fuel ctx fn s)
      (run_blocks fuel ctx (dse_function_space analysis_fn space fn) s)
Proof
  cheat
QED

(* ORIGINAL Theorem 1 is FALSE: cross-allocation pointer arithmetic via
   ADD lets a pointer escape its allocation bounds. bp_analyze assigns
   different Allocation IDs and concludes may_overlap = F, but at runtime
   the aliased MSTORE affects a subsequent MLOAD. *)
Theorem dse_function_space_correct_proof_FALSE:
  ~(!analysis_fn cfg aliases bp space fuel ctx fn s.
      (!fn'. all_dead_stores (analysis_fn space fn')
               (cfg_analyze fn') aliases (bp_analyze (cfg_analyze fn') fn')
               space fn') ==>
      lift_result (dse_equiv space) (dse_equiv space) (dse_equiv space)
        (run_blocks fuel ctx fn s)
        (run_blocks fuel ctx (dse_function_space analysis_fn space fn) s))
Proof
  simp[] >>
  qexistsl [`cex_analysis_fn`, `FEMPTY`,
            `AddrSp_Memory`, `2`, `ARB`, `cex_fn`, `cex_entry_state`] >>
  conj_tac >- simp[cex_precondition] >>
  simp[cex_function_space] >>
  strip_assume_tac cex_orig_is_halt >>
  strip_assume_tac cex_trans_is_halt >>
  simp[] >> fs[lift_result_def, dse_equiv_def] >>
  rpt strip_tac >>
  qexists `"result"` >> simp[lookup_var_def] >>
  mp_tac cex_run_orig >> mp_tac cex_run_trans >>
  qpat_x_assum `Halt s = _` (assume_tac o GSYM) >>
  qpat_x_assum `Halt s' = _` (assume_tac o GSYM) >>
  simp[w42_neq_0]
QED

(* Full DSE (all three spaces) preserves dse_all_equiv: sequentially
   eliminating dead stores for Memory, Storage, and Transient preserves
   all variables, logs, return data, and control flow.

   Precondition chain (matches MCE pattern):
   alloca_inv s: alloca regions are non-overlapping
   bp_ptr_sound bp s: analysis-computed addresses match runtime
   bp_ptrs_bounded bp fn s: alloca-backed accesses stay within
                            their analysis-identified allocation
   Together: if may_overlap says two accesses in different allocations
   don't alias, they genuinely don't overlap at runtime. *)
Theorem dse_function_correct_proof:
  !analysis_fn fuel ctx fn s.
    alloca_inv s /\
    bp_ptr_sound (bp_analyze (cfg_analyze fn) fn) s /\
    bp_ptrs_bounded (bp_analyze (cfg_analyze fn) fn) fn s /\
    (!space fn'.
      all_dead_stores (analysis_fn space fn')
        (cfg_analyze fn') FEMPTY (bp_analyze (cfg_analyze fn') fn')
        space fn') ==>
    lift_result dse_all_equiv dse_all_equiv dse_all_equiv
      (run_blocks fuel ctx fn s)
      (run_blocks fuel ctx (dse_function analysis_fn fn) s)
Proof
  cheat
QED

(* ORIGINAL Theorem 2 is FALSE: bp is universally quantified and
   unconstrained, so bp = FEMPTY satisfies bp_ptr_sound/bp_ptrs_bounded
   vacuously. Same cross-allocation aliasing counterexample applies. *)
Theorem dse_function_correct_proof_FALSE:
  ~(!analysis_fn aliases fuel ctx fn s bp.
      bp_ptr_sound bp s /\ bp_ptrs_bounded bp fn s /\
      (!space fn'.
        all_dead_stores (analysis_fn space fn')
          (cfg_analyze fn') aliases (bp_analyze (cfg_analyze fn') fn')
          space fn') ==>
      lift_result dse_all_equiv dse_all_equiv dse_all_equiv
        (run_blocks fuel ctx fn s)
        (run_blocks fuel ctx (dse_function analysis_fn fn) s))
Proof
  simp[] >>
  qexistsl [`cex_analysis_fn`, `FEMPTY`, `2`, `ARB`,
            `cex_fn`, `cex_entry_state`, `FEMPTY`] >>
  simp[bp_ptr_sound_init, bp_ptrs_bounded_FEMPTY, cex_precondition] >>
  simp[cex_dse_function] >>
  strip_assume_tac cex_orig_is_halt >>
  strip_assume_tac cex_trans_is_halt >>
  simp[] >> fs[lift_result_def, dse_all_equiv_def] >>
  rpt strip_tac >>
  qexists `"result"` >> simp[lookup_var_def] >>
  mp_tac cex_run_orig >> mp_tac cex_run_trans >>
  qpat_x_assum `Halt s = _` (assume_tac o GSYM) >>
  qpat_x_assum `Halt s' = _` (assume_tac o GSYM) >>
  simp[w42_neq_0]
QED
