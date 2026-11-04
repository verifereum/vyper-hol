Theory loadElimEscapingPointerProbe
Ancestors
  loadElimPhiProbes memoryCopyElisionSound venomMemDefs
  finite_map basePtrDefs dfIterateDefs dfgCorrectnessProof While venomInst venomExecSemantics venomState memLocDefs

(* This candidate is tested against the universal step premise first. *)
Definition escape_probe_fn_def:
  escape_probe_fn = mk_raw_function "escape"
    [<| bb_label := "e"; bb_instructions :=
      [probe_inst 0 ALLOCA [Lit 32w] ["a"];
       probe_inst 1 ALLOCA [Lit 32w] ["b"];
       probe_inst 2 CALLDATALOAD [Lit 0w] ["d"];
       probe_inst 3 ADD [Var "a"; Var "d"] ["q"];
       probe_inst 4 MLOAD [Var "q"] ["x"];
       probe_inst 5 MSTORE [Var "b"; Lit 1w] [];
       probe_inst 6 MLOAD [Var "q"] ["y"];
       probe_inst 7 STOP [] []] |>]
End

Definition escape_bp_def:
  escape_bp = FEMPTY |++ [("a", [Ptr (Allocation 0) (SOME 0)]);
                ("b", [Ptr (Allocation 1) (SOME 0)]);
                ("q", [Ptr (Allocation 0) NONE])]
End

Theorem escape_probe_order:
  (cfg_analyze escape_probe_fn).cfg_dfs_pre = ["e"]
Proof
  EVAL_TAC
QED

Theorem escape_probe_first:
  SND (bp_one_pass escape_probe_fn ["e"] FEMPTY) = escape_bp
Proof
  EVAL_TAC
QED

Theorem escape_probe_stable:
  SND (bp_one_pass escape_probe_fn ["e"] escape_bp) = escape_bp
Proof
  EVAL_TAC >> simp[fmap_EXT, FLOOKUP_DEF, FAPPLY_FUPDATE_THM] >> pred_setLib.SET_TAC[]
QED

Theorem escape_probe_bp:
  bp_analyze (cfg_analyze escape_probe_fn) escape_probe_fn =
    FEMPTY |++ [("a", [Ptr (Allocation 0) (SOME 0)]);
                ("b", [Ptr (Allocation 1) (SOME 0)]);
                ("q", [Ptr (Allocation 0) NONE])]
Proof
  rewrite_tac[bp_analyze_def, escape_probe_order, LET_THM] >>
  BETA_TAC >> rewrite_tac[df_iterate_def] >>
  once_rewrite_tac[WhileTheory.WHILE] >>
  simp[escape_probe_first] >>
  once_rewrite_tac[WhileTheory.WHILE] >>
  simp[escape_probe_stable, escape_bp_def, FUPDATE_LIST_THM]
QED

Definition escape_counterstate_def:
  escape_counterstate = (ARB : venom_state) with
    <| vs_vars := FEMPTY; vs_allocas := FEMPTY |+ (1, (0,32));
       vs_alloca_next := 0; vs_inst_idx := 0 |>
End

Theorem escape_counterstate_pre:
  dfg_assigns_sound (dfg_build_function escape_probe_fn) escape_counterstate /\
  bp_ptr_sound (bp_analyze (cfg_analyze escape_probe_fn) escape_probe_fn)
    escape_counterstate /\
  allocas_non_overlapping escape_counterstate /\
  allocas_in_word escape_counterstate /\
  bp_ptrs_bounded (bp_analyze (cfg_analyze escape_probe_fn) escape_probe_fn)
    escape_probe_fn escape_counterstate
Proof
  rewrite_tac[escape_probe_bp] >> rpt conj_tac
  >- (EVAL_TAC >> rpt strip_tac >> gvs[AllCaseEqs()])
  >- (EVAL_TAC >> simp[])
  >- (EVAL_TAC >> rpt strip_tac >> gvs[AllCaseEqs()])
  >- (EVAL_TAC >> rpt strip_tac >> gvs[AllCaseEqs()] >> simp[wordsTheory.dimword_def])
  >> simp[bp_ptrs_bounded_def, escape_probe_fn_def,
          mk_raw_function_def, listTheory.MEM, DISJ_IMP_THM, FORALL_AND_THM] >>
     rpt strip_tac >> gvs[probe_inst_def, mem_write_ops_def, mem_read_ops_def] >>
     EVAL_TAC >> simp[wordsTheory.word_0_n2w, wordsTheory.w2n_n2w,
                          wordsTheory.dimword_def]
QED

Definition escape_poststate_def:
  escape_poststate = update_var "a" 0w
    (escape_counterstate with
      <| vs_allocas := escape_counterstate.vs_allocas |+ (0,(0,32));
         vs_alloca_next := 32 |> )
End

Theorem escape_alloca_step:
  !fuel ctx.
    step_inst fuel ctx (probe_inst 0 ALLOCA [Lit 32w] ["a"])
      escape_counterstate = OK escape_poststate
Proof
  simp[step_inst_def, probe_inst_def, step_inst_base_def,
       exec_alloca_def, escape_counterstate_def, escape_poststate_def, FLOOKUP_UPDATE, FLOOKUP_EMPTY,
       wordsTheory.word_0_n2w, wordsTheory.w2n_n2w, wordsTheory.dimword_def]
QED

Theorem escape_poststate_overlap:
  ~allocas_non_overlapping (escape_poststate with vs_inst_idx := 0)
Proof
  simp[allocas_non_overlapping_def, escape_poststate_def,
       escape_counterstate_def, update_var_def] >>
  qexistsl_tac [`0`, `1`, `0`, `32`, `0`, `32`] >>
  simp[FLOOKUP_UPDATE, FLOOKUP_EMPTY]
QED

(* A concrete falsifying instance of the frozen universal step premise.
   This REJECTS the candidate; it is not a counterexample to correctness. *)
Theorem escape_universal_premise_counterinstance:
  ?bb inst s0 s1.
    MEM bb escape_probe_fn.fn_blocks /\ MEM inst bb.bb_instructions /\
    inst_wf inst /\
    dfg_assigns_sound (dfg_build_function escape_probe_fn) (s0 with vs_inst_idx := 0) /\
    bp_ptr_sound (bp_analyze (cfg_analyze escape_probe_fn) escape_probe_fn)
      (s0 with vs_inst_idx := 0) /\
    allocas_non_overlapping (s0 with vs_inst_idx := 0) /\
    allocas_in_word (s0 with vs_inst_idx := 0) /\
    bp_ptrs_bounded (bp_analyze (cfg_analyze escape_probe_fn) escape_probe_fn)
      escape_probe_fn (s0 with vs_inst_idx := 0) /\
    step_inst 0 ARB inst s0 = OK s1 /\
    ~allocas_non_overlapping (s1 with vs_inst_idx := 0)
Proof
  qexistsl_tac [`HD escape_probe_fn.fn_blocks`,
    `probe_inst 0 ALLOCA [Lit 32w] ["a"]`,
    `escape_counterstate`, `escape_poststate`] >>
  `escape_counterstate with vs_inst_idx := 0 = escape_counterstate` by
    simp[escape_counterstate_def] >>
  simp[escape_counterstate_pre, escape_alloca_step, escape_poststate_overlap] >>
  EVAL_TAC
QED
