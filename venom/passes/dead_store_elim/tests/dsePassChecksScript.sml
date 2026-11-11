(* Concrete checks for Dead Store Elimination (DSE) definitions and pass execution:
   - bp_segment_from_ops uses exact iao_size (CALL max outsize stays non-fixed)
   - bp_get_read_location treats DRET/RETFMP (vyper#5297) and key-space
     SELFDESTRUCT as ml_undefined barriers
   - all_dead_stores rejects zero-size writes (ml_size = SOME 0)
   - dse_checked_analysis finds the overwritten stores of dse_overwrite_fn
   - non-vacuity of dse_function_correct and dse_checked_function_correct:
     their premises hold for dse_overwrite_fn, and dse_term_equiv fixes the
     transformed run's variables, storage and transient storage *)
Theory dsePassChecks
Ancestors
  deadStoreElimDefs deadStoreElimEquiv passSimulationDefs basePtrDefs
  memLocDefs venomInst venomExecSemantics venomState cfgDefs vfmTypes
  byte While combin finite_map list rich_list pred_set words
  deadStoreElimFrame deadStoreElimCheckerDefs deadStoreElimChecker
  deadStoreElimCorrectness venomWf venomMemDefs venomMemProps
  venomExecProps venomExecProofs stateEquiv
Libs
  deadStoreElimFrameLib

Triviality w2n_32_256[local]:
  w2n (32w:256 word) = 32
Proof
  simp[wordsTheory.w2n_n2w, wordsTheory.dimword_def] >>
  CONV_TAC (DEPTH_CONV fcpLib.INDEX_CONV) >> EVAL_TAC
QED

Triviality w2n_0_256[local]:
  w2n (0w:256 word) = 0
Proof
  simp[wordsTheory.w2n_n2w, wordsTheory.dimword_def] >>
  CONV_TAC (DEPTH_CONV fcpLib.INDEX_CONV) >> EVAL_TAC
QED

Triviality mod_dimword_32_256[local]:
  32 MOD dimword (:256) = 32
Proof
  simp[wordsTheory.dimword_def] >>
  CONV_TAC (DEPTH_CONV fcpLib.INDEX_CONV) >> EVAL_TAC
QED

Triviality wta_32_is_word_to_bytes[local]:
  !w be. word_to_bytes_aux 32 (w:256 word) be = word_to_bytes w be
Proof
  simp[byteTheory.word_to_bytes_def] >>
  CONV_TAC (DEPTH_CONV fcpLib.INDEX_CONV) >> simp[]
QED

Triviality take_word_to_bytes_32[local]:
  !w be rest.
    TAKE 32 (word_to_bytes (w:256 word) be ++ rest) = word_to_bytes w be
Proof
  rpt gen_tac >>
  `LENGTH (word_to_bytes (w:256 word) be) = 32` by
    (simp[byteTheory.LENGTH_word_to_bytes] >>
     CONV_TAC (DEPTH_CONV fcpLib.INDEX_CONV) >> simp[]) >>
  metis_tac[rich_listTheory.TAKE_LENGTH_APPEND]
QED

Triviality drop_word_to_bytes_32[local]:
  !w be. DROP 32 (word_to_bytes (w:256 word) be) = []
Proof
  rpt gen_tac >>
  `LENGTH (word_to_bytes (w:256 word) be) = 32` by
    (simp[byteTheory.LENGTH_word_to_bytes] >>
     CONV_TAC (DEPTH_CONV fcpLib.INDEX_CONV) >> simp[]) >>
  simp[listTheory.DROP_LENGTH_TOO_LONG]
QED

Definition dse_test_call_inst_def:
  dse_test_call_inst =
    <|inst_id := 0; inst_opcode := CALL;
      inst_operands := [Lit 100w; Lit 0w; Lit 0w; Lit 0w; Lit 0w; Lit 64w; Lit 32w];
      inst_outputs := ["ok"]|>
End

Definition dse_test_mstore_inst_def:
  dse_test_mstore_inst =
    <|inst_id := 1; inst_opcode := MSTORE;
      inst_operands := [Lit 64w; Lit 42w];
      inst_outputs := []|>
End

Theorem call_write_location_not_fixed:
  (bp_get_write_location FEMPTY dse_test_call_inst AddrSp_Memory).ml_size = NONE /\
  ~ml_is_fixed (bp_get_write_location FEMPTY dse_test_call_inst AddrSp_Memory) /\
  (bp_get_write_location FEMPTY dse_test_mstore_inst AddrSp_Memory).ml_size = SOME 32 /\
  ml_is_fixed (bp_get_write_location FEMPTY dse_test_mstore_inst AddrSp_Memory)
Proof
  EVAL_TAC >> simp[w2n_32_256]
QED

Theorem dret_retfmp_selfdestruct_read_barriers:
  bp_get_read_location FEMPTY (mk_inst 0 DRET [Lit 0w] []) AddrSp_Memory = ml_undefined /\
  bp_get_read_location FEMPTY (mk_inst 0 DRET [Lit 0w] []) AddrSp_Storage = ml_undefined /\
  bp_get_read_location FEMPTY (mk_inst 0 DRET [Lit 0w] []) AddrSp_Transient = ml_undefined /\
  bp_get_read_location FEMPTY (mk_inst 0 RETFMP [Lit 0w] []) AddrSp_Memory = ml_undefined /\
  bp_get_read_location FEMPTY (mk_inst 0 RETFMP [Lit 0w] []) AddrSp_Storage = ml_undefined /\
  bp_get_read_location FEMPTY (mk_inst 0 RETFMP [Lit 0w] []) AddrSp_Transient = ml_undefined /\
  bp_get_read_location FEMPTY (mk_inst 0 SELFDESTRUCT [Lit 0w] []) AddrSp_Storage = ml_undefined /\
  bp_get_read_location FEMPTY (mk_inst 0 SELFDESTRUCT [Lit 0w] []) AddrSp_Transient = ml_undefined
Proof
  EVAL_TAC
QED

Definition dse_zero_copy_fn_def:
  dse_zero_copy_fn =
    mk_raw_function "zero_copy"
      [<|bb_label := "entry";
         bb_instructions :=
           [<|inst_id := 0; inst_opcode := CODECOPY;
              inst_operands := [Lit 0w; Lit 0w; Lit 0w]; inst_outputs := []|>;
            <|inst_id := 1; inst_opcode := STOP;
              inst_operands := []; inst_outputs := []|>]|>]
End

Theorem zero_size_write_not_dead_store:
  (bp_get_write_location FEMPTY
     (EL 0 (HD dse_zero_copy_fn.fn_blocks).bb_instructions)
     AddrSp_Memory).ml_size = SOME 0 /\
  ~all_dead_stores {0} (cfg_analyze dse_zero_copy_fn) FEMPTY FEMPTY
     AddrSp_Memory dse_zero_copy_fn
Proof
  `(bp_get_write_location FEMPTY
     (EL 0 (HD dse_zero_copy_fn.fn_blocks).bb_instructions)
     AddrSp_Memory).ml_size = SOME 0` by (EVAL_TAC >> simp[w2n_0_256]) >>
  simp[] >> strip_tac >> fs[all_dead_stores_def] >>
  qpat_x_assum `MEM bb _` mp_tac >>
  qpat_x_assum `inst_idx < _` mp_tac >>
  qpat_x_assum `(EL inst_idx _).inst_id = 0` mp_tac >>
  simp[dse_zero_copy_fn_def, mk_raw_function_def] >>
  rpt strip_tac >> gvs[] >>
  Cases_on `inst_idx` >> gvs[dse_zero_copy_fn_def, mk_raw_function_def] >>
  Cases_on `n` >> gvs[]
QED

Definition dse_overwrite_fn_def:
  dse_overwrite_fn =
    mk_raw_function "overwrite"
      [<|bb_label := "entry";
         bb_instructions :=
           [<|inst_id := 0; inst_opcode := MSTORE;
              inst_operands := [Lit 0w; Lit 10w]; inst_outputs := []|>;
            <|inst_id := 1; inst_opcode := MSTORE;
              inst_operands := [Lit 0w; Lit 20w]; inst_outputs := []|>;
            <|inst_id := 2; inst_opcode := SSTORE;
              inst_operands := [Lit 0w; Lit 30w]; inst_outputs := []|>;
            <|inst_id := 3; inst_opcode := SSTORE;
              inst_operands := [Lit 0w; Lit 40w]; inst_outputs := []|>;
            <|inst_id := 4; inst_opcode := TSTORE;
              inst_operands := [Lit 0w; Lit 1w]; inst_outputs := []|>;
            <|inst_id := 5; inst_opcode := TSTORE;
              inst_operands := [Lit 0w; Lit 2w]; inst_outputs := []|>;
            <|inst_id := 6; inst_opcode := MLOAD;
              inst_operands := [Lit 0w]; inst_outputs := ["mres"]|>;
            <|inst_id := 7; inst_opcode := SLOAD;
              inst_operands := [Lit 0w]; inst_outputs := ["sres"]|>;
            <|inst_id := 8; inst_opcode := TLOAD;
              inst_operands := [Lit 0w]; inst_outputs := ["tres"]|>;
            <|inst_id := 9; inst_opcode := STOP;
              inst_operands := []; inst_outputs := []|>]|>]
End

(* Every instruction id is a candidate; dse_checked_analysis keeps the ones
   its check accepts. *)
Definition dse_all_ids_def:
  dse_all_ids (space : addr_space) fn = MAP (\i. i.inst_id) (fn_insts fn)
End

(* What the checker accepts on each iterate of the pass: the overwritten
   MSTORE, SSTORE and TSTORE (ids 0, 2, 4) and nothing else. *)
Theorem dse_overwrite_mem_round[local]:
  dse_checked_analysis dse_all_ids AddrSp_Memory dse_overwrite_fn = {0} /\
  dse_checked_analysis dse_all_ids AddrSp_Memory
    (dse_single_pass {0} AddrSp_Memory dse_overwrite_fn) = {}
Proof
  conj_tac >> EVAL_TAC >> simp[w2n_32_256, w2n_0_256, mod_dimword_32_256]
QED

Theorem dse_overwrite_storage_round[local]:
  dse_checked_analysis dse_all_ids AddrSp_Storage
    (clear_nops_function (dse_single_pass {0} AddrSp_Memory dse_overwrite_fn)) =
    {2} /\
  dse_checked_analysis dse_all_ids AddrSp_Storage
    (dse_single_pass {2} AddrSp_Storage
      (clear_nops_function
        (dse_single_pass {0} AddrSp_Memory dse_overwrite_fn))) = {}
Proof
  conj_tac >> EVAL_TAC >> simp[w2n_32_256, w2n_0_256, mod_dimword_32_256]
QED

Theorem dse_overwrite_transient_round[local]:
  dse_checked_analysis dse_all_ids AddrSp_Transient
    (clear_nops_function (dse_single_pass {2} AddrSp_Storage
      (clear_nops_function
        (dse_single_pass {0} AddrSp_Memory dse_overwrite_fn)))) = {4} /\
  dse_checked_analysis dse_all_ids AddrSp_Transient
    (dse_single_pass {4} AddrSp_Transient
      (clear_nops_function (dse_single_pass {2} AddrSp_Storage
        (clear_nops_function
          (dse_single_pass {0} AddrSp_Memory dse_overwrite_fn))))) = {}
Proof
  conj_tac >> EVAL_TAC >> simp[w2n_32_256, w2n_0_256, mod_dimword_32_256]
QED

(* One round of dse_iterate removes what the checker accepted; the next
   round's check accepts nothing. *)
Theorem dse_function_space_one_round[local]:
  dse_checked_analysis cand sp fn = s /\ s <> {} /\
  dse_checked_analysis cand sp (dse_single_pass s sp fn) = {} ==>
  dse_function_space (dse_checked_analysis cand) sp fn =
    clear_nops_function (dse_single_pass s sp fn)
Proof
  strip_tac >>
  simp[dse_function_space_def, dse_iterate_def] >>
  once_rewrite_tac[WhileTheory.OWHILE_THM] >> simp[] >>
  once_rewrite_tac[WhileTheory.OWHILE_THM] >> simp[]
QED

Theorem dse_overwrite_checked_pass:
  MAP (\i. i.inst_id)
    (HD (dse_function (dse_checked_analysis dse_all_ids)
           dse_overwrite_fn).fn_blocks).bb_instructions =
    [1; 3; 5; 6; 7; 8; 9]
Proof
  qabbrev_tac `fn1 = clear_nops_function
                       (dse_single_pass {0} AddrSp_Memory dse_overwrite_fn)` >>
  qabbrev_tac `fn2 = clear_nops_function
                       (dse_single_pass {2} AddrSp_Storage fn1)` >>
  `dse_function_space (dse_checked_analysis dse_all_ids) AddrSp_Memory
     dse_overwrite_fn = fn1` by
    (simp[Abbr `fn1`] >> irule dse_function_space_one_round >>
     simp[dse_overwrite_mem_round]) >>
  `dse_function_space (dse_checked_analysis dse_all_ids) AddrSp_Storage fn1 =
   fn2` by
    (simp[Abbr `fn2`] >> irule dse_function_space_one_round >>
     simp[Abbr `fn1`, dse_overwrite_storage_round]) >>
  `dse_function_space (dse_checked_analysis dse_all_ids) AddrSp_Transient fn2 =
   clear_nops_function (dse_single_pass {4} AddrSp_Transient fn2)` by
    (irule dse_function_space_one_round >>
     simp[Abbr `fn1`, Abbr `fn2`, dse_overwrite_transient_round]) >>
  simp[dse_function_def] >>
  simp[Abbr `fn1`, Abbr `fn2`] >>
  CONV_TAC (DEPTH_CONV (fn t =>
    if can (match_term ``clear_nops_function x``) t
    then EVAL t else raise UNCHANGED)) >>
  EVAL_TAC
QED

(* ===== Non-vacuity of the correctness theorems ===== *)

Theorem dse_overwrite_bp[local]:
  bp_analyze (cfg_analyze dse_overwrite_fn) dse_overwrite_fn = FEMPTY
Proof
  EVAL_TAC
QED

Theorem dse_overwrite_step_allocas[local]:
  lookup_block lbl dse_overwrite_fn.fn_blocks = SOME bb /\
  get_instruction bb idx = SOME inst /\
  step_inst fuel ctx inst s0 = OK s1 ==> s1.vs_allocas = s0.vs_allocas
Proof
  strip_tac >>
  `MEM inst bb.bb_instructions` by
    (fs[get_instruction_def, AllCaseEqs()] >> metis_tac[MEM_EL]) >>
  `MEM bb dse_overwrite_fn.fn_blocks` by metis_tac[lookup_block_MEM] >>
  `~is_alloca_op inst.inst_opcode /\ inst.inst_opcode <> INVOKE` by
    (qpat_x_assum `MEM inst _` mp_tac >> qpat_x_assum `MEM bb _` mp_tac >>
     rpt (pop_assum kall_tac) >>
     simp[dse_overwrite_fn_def, mk_raw_function_def] >>
     rpt strip_tac >> gvs[is_alloca_op_def]) >>
  metis_tac[step_inst_non_alloca_preserves_allocas]
QED

Theorem dse_overwrite_ptrs_bounded[local]:
  bp_ptrs_bounded bp dse_overwrite_fn s
Proof
  simp[bp_ptrs_bounded_def, dse_overwrite_fn_def, mk_raw_function_def] >>
  rpt strip_tac >> gvs[] >>
  gvs[mem_write_ops_def, mem_read_ops_def, bp_segment_from_ops_def]
QED

(* Every premise of dse_checked_function_correct holds for dse_overwrite_fn
   from the initial state, with no allocations as the state invariant. *)
Theorem dse_overwrite_premises[local]:
  wf_function dse_overwrite_fn /\ ssa_form dse_overwrite_fn /\
  (init_venom_state "entry").vs_inst_idx = 0 /\
  ~(init_venom_state "entry").vs_call_ctx.cc_static /\
  ~(init_venom_state "entry").vs_halted /\
  (init_venom_state "entry").vs_allocas = FEMPTY /\
  (!bb s0 s1.
     lookup_block s0.vs_current_bb dse_overwrite_fn.fn_blocks = SOME bb /\
     s0.vs_inst_idx = 0 /\ s0.vs_allocas = FEMPTY /\
     eval_phis s0 bb.bb_instructions = OK s1 ==>
     s1.vs_allocas = FEMPTY) /\
  (!bb inst fuel' ctx s0 s1.
     lookup_block s0.vs_current_bb dse_overwrite_fn.fn_blocks = SOME bb /\
     get_instruction bb s0.vs_inst_idx = SOME inst /\ s0.vs_allocas = FEMPTY /\
     step_inst fuel' ctx inst s0 = OK s1 ==>
     s1.vs_allocas = FEMPTY) /\
  (!s0. s0.vs_allocas = FEMPTY ==>
     alloca_inv s0 /\
     (!aid base sz. FLOOKUP s0.vs_allocas aid = SOME (base, sz) ==>
                    base + sz < dimword (:256)) /\
     bp_ptr_sound (bp_analyze (cfg_analyze dse_overwrite_fn) dse_overwrite_fn) s0 /\
     bp_ptrs_bounded (bp_analyze (cfg_analyze dse_overwrite_fn) dse_overwrite_fn)
       dse_overwrite_fn s0 /\
     (!inst. bp_accesses_in_own_alloca
               (bp_analyze (cfg_analyze dse_overwrite_fn) dse_overwrite_fn) inst s0))
Proof
  rpt conj_tac
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >- EVAL_TAC
  >- (rpt strip_tac >> drule eval_phis_only_updates_vs_vars >>
      disch_then SUBST1_TAC >> simp[])
  >- metis_tac[dse_overwrite_step_allocas]
  >> rpt strip_tac
  >- metis_tac[alloca_inv_empty]
  >- gvs[]
  >- simp[dse_overwrite_bp, bp_ptr_sound_def, bp_get_ptrs_def]
  >- simp[dse_overwrite_ptrs_bounded]
  >> simp[bp_accesses_in_own_alloca_def]
QED

(* The untransformed run halts with these values. *)
Theorem dse_overwrite_run[local]:
  ?s. run_blocks 1 ARB dse_overwrite_fn (init_venom_state "entry") = Halt s /\
      lookup_var "mres" s = SOME 20w /\ lookup_var "sres" s = SOME 40w /\
      lookup_var "tres" s = SOME 2w /\ sload 0w s = 40w /\ tload 0w s = 2w
Proof
  CONV_TAC (DEPTH_CONV (fn t =>
    if can (match_term ``run_blocks 1 ARB dse_overwrite_fn s``) t
    then EVAL t else raise UNCHANGED)) >>
  simp_tac bool_ss [exec_result_11] >> EVAL_TAC >>
  simp[combinTheory.UPDATE_EQ, wta_32_is_word_to_bytes, drop_word_to_bytes_32,
       take_word_to_bytes_32, vfmTypesTheory.word_to_bytes_word_of_bytes_256]
QED

(* The terminal relation fixes every variable, storage and transient
   storage of the transformed run. *)
Theorem dse_term_equiv_observations[local]:
  dse_term_equiv s t ==>
  (!v. lookup_var v t = lookup_var v s) /\ (!k. sload k t = sload k s) /\
  (!k. tload k t = tload k s)
Proof
  simp_tac (srw_ss() ++ deadStoreElimFrameLib.frame_ss)
    [dse_equiv_def, sload_def, tload_def, contract_storage_def,
     contract_transient_def]
QED

(* Non-vacuity witness for dse_function_correct and
   dse_checked_function_correct: all their premises hold for dse_overwrite_fn,
   and the terminal relation transfers the untransformed run's final
   variables, storage and transient storage to the transformed run. *)
Theorem dse_overwrite_correctness_witness:
  lift_result dse_all_equiv dse_term_equiv dse_all_equiv
    (run_blocks 1 ARB dse_overwrite_fn (init_venom_state "entry"))
    (run_blocks 1 ARB (dse_function (dse_checked_analysis dse_all_ids)
                         dse_overwrite_fn) (init_venom_state "entry")) /\
  ?t. run_blocks 1 ARB (dse_function (dse_checked_analysis dse_all_ids)
                          dse_overwrite_fn) (init_venom_state "entry") = Halt t /\
      lookup_var "mres" t = SOME 20w /\ lookup_var "sres" t = SOME 40w /\
      lookup_var "tres" t = SOME 2w /\ sload 0w t = 40w /\ tload 0w t = 2w
Proof
  strip_assume_tac dse_overwrite_run >>
  strip_assume_tac dse_overwrite_premises >>
  `(?e. run_blocks 1 ARB dse_overwrite_fn (init_venom_state "entry") = Error e) \/
   lift_result dse_all_equiv dse_term_equiv dse_all_equiv
     (run_blocks 1 ARB dse_overwrite_fn (init_venom_state "entry"))
     (run_blocks 1 ARB (dse_function (dse_checked_analysis dse_all_ids)
                          dse_overwrite_fn) (init_venom_state "entry"))` by
    (irule dse_function_correct >>
     simp[dse_checked_analysis_dead_stores] >>
     qexists_tac `\s0. s0.vs_allocas = FEMPTY` >> rw[] >> metis_tac[]) >>
  `(?e. run_blocks 1 ARB dse_overwrite_fn (init_venom_state "entry") = Error e) \/
   lift_result dse_all_equiv dse_term_equiv dse_all_equiv
     (run_blocks 1 ARB dse_overwrite_fn (init_venom_state "entry"))
     (run_blocks 1 ARB (dse_function (dse_checked_analysis dse_all_ids)
                          dse_overwrite_fn) (init_venom_state "entry"))` by
    (irule dse_checked_function_correct >> simp[] >>
     qexists_tac `\s0. s0.vs_allocas = FEMPTY` >> rw[] >> metis_tac[]) >>
  gvs[] >>
  qpat_x_assum `lift_result _ _ _ _ _` mp_tac >>
  qpat_x_assum `Halt s = _` (SUBST1_TAC o GSYM) >>
  Cases_on `run_blocks 1 ARB (dse_function (dse_checked_analysis dse_all_ids)
                                dse_overwrite_fn) (init_venom_state "entry")` >>
  simp[lift_result_def] >> strip_tac >>
  drule dse_term_equiv_observations >> simp[]
QED
