(* Bounded countermodel to preserving an arbitrary post at the first PC hit.
   FirstHit already names an existing theory, so use Countermodel here.
   These definitions name only finite fixture data, not a new judgment. *)
Theory bodyPtrWordBuiltinsFirstHitCountermodel
Ancestors fragGasPathPtr gasSummaryComposePtr ptrSafeRun ptrDiscipline
  venomInst venomState venomExecSemantics gasCount words arithmetic
Libs finite_mapLib intReduce wordsLib

val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset intReduce.add_int_compset

Definition word_hit_fn_def:
  word_hit_fn = mk_raw_function "hit"
    [<| bb_label := "start";
        bb_instructions := [mk_inst 0 JMP [Label "end"] []] |>;
     <| bb_label := "end";
        bb_instructions := [mk_inst 1 ADD [Lit 0w; Lit 1w] ["x"];
                            mk_inst 2 JMP [Label "end"] []] |>]
End

Definition word_hit_s0_def:
  word_hit_s0 = update_var "x" 0w (init_venom_state "start")
End
Definition word_hit_u_def:
  word_hit_u = jump_to "end" word_hit_s0
End
Definition word_hit_v_def:
  word_hit_v = next_inst (update_var "x" 1w word_hit_u)
End
Definition word_hit_t_def:
  word_hit_t = jump_to "end" word_hit_v
End

Theorem word_hit_first_edge:
  gas_path_ptr_edge D 0 ctx word_hit_fn [] FEMPTY entry_taint word_hit_s0
    0 FEMPTY entry_taint (OK word_hit_u)
Proof
  rewrite_tac[gas_path_ptr_edge_def] >>
  conj_tac >- EVAL_TAC >>
  qexistsl [`0`, `HD word_hit_fn.fn_blocks`,
            `mk_inst 0 JMP [Label "end"] []`, `OK word_hit_u`] >>
  rpt conj_tac >- EVAL_TAC >- EVAL_TAC >- (EVAL_TAC >> simp[WORD_ADD_0]) >- EVAL_TAC
  >- (EVAL_TAC >> simp[] >> Cases >> simp[]) >>
  disj2_tac >> disj2_tac >> disj2_tac >>
  disj1_tac >> qexists `"end"` >> EVAL_TAC
QED

Definition word_hit_tn_def:
  word_hit_tn = entry_taint with t_var := FEMPTY |+ ("x", {})
End

Theorem word_hit_write_edge:
  gas_path_ptr_edge D 0 ctx word_hit_fn [] FEMPTY entry_taint word_hit_u
    0 FEMPTY word_hit_tn (OK word_hit_v)
Proof
  rewrite_tac[gas_path_ptr_edge_def] >>
  conj_tac >- EVAL_TAC >>
  qexistsl [`0`, `EL 1 word_hit_fn.fn_blocks`,
            `mk_inst 1 ADD [Lit 0w; Lit 1w] ["x"]`,
            `OK (update_var "x" 1w word_hit_u)`] >>
  rpt conj_tac >- EVAL_TAC >- EVAL_TAC >- (EVAL_TAC >> simp[WORD_ADD_0]) >- EVAL_TAC
  >- (EVAL_TAC >> simp[] >> Cases >> simp[]) >>
  disj1_tac >> qexists `update_var "x" 1w word_hit_u` >>
  EVAL_TAC >> simp[]
QED

Theorem word_hit_return_edge:
  gas_path_ptr_edge D 0 ctx word_hit_fn [] FEMPTY word_hit_tn word_hit_v
    0 FEMPTY word_hit_tn (OK word_hit_t)
Proof
  rewrite_tac[gas_path_ptr_edge_def] >>
  conj_tac >- EVAL_TAC >>
  qexistsl [`0`, `EL 1 word_hit_fn.fn_blocks`,
            `mk_inst 2 JMP [Label "end"] []`, `OK word_hit_t`] >>
  rpt conj_tac >- EVAL_TAC >- EVAL_TAC >- (EVAL_TAC >> simp[WORD_ADD_0]) >- EVAL_TAC
  >- (EVAL_TAC >> simp[] >> Cases >> simp[]) >>
  disj2_tac >> disj2_tac >> disj2_tac >>
  disj1_tac >> qexists `"end"` >> EVAL_TAC
QED

Theorem word_hit_prefix_path:
  gas_path_ptr D 0 ctx word_hit_fn [] FEMPTY entry_taint word_hit_s0
    0 FEMPTY entry_taint (OK word_hit_u)
Proof
  mp_tac word_hit_first_edge >>
  `~word_hit_u.vs_halted` by EVAL_TAC >>
  metis_tac[gas_path_ptr_rules, ADD_0]
QED

Theorem word_hit_suffix_path:
  gas_path_ptr D 0 ctx word_hit_fn [] FEMPTY entry_taint word_hit_u
    0 FEMPTY word_hit_tn (OK word_hit_t)
Proof
  mp_tac word_hit_write_edge >> mp_tac word_hit_return_edge >>
  `~word_hit_t.vs_halted` by EVAL_TAC >>
  metis_tac[gas_path_ptr_rules, ADD_0]
QED

Theorem word_hit_full_path:
  gas_path_ptr D 0 ctx word_hit_fn [] FEMPTY entry_taint word_hit_s0
    0 FEMPTY word_hit_tn (OK word_hit_t)
Proof
  mp_tac word_hit_prefix_path >> mp_tac word_hit_suffix_path >>
  metis_tac[gas_path_ptr_then, ADD_0]
QED

Theorem word_hit_pc_and_value:
  word_hit_s0.vs_current_bb <> "end" /\
  word_hit_u.vs_current_bb = "end" /\ word_hit_u.vs_inst_idx = 0 /\
  word_hit_v.vs_current_bb = "end" /\ word_hit_v.vs_inst_idx = 1 /\
  word_hit_t.vs_current_bb = "end" /\ word_hit_t.vs_inst_idx = 0 /\
  lookup_var "x" word_hit_u = SOME 0w /\
  lookup_var "x" word_hit_t = SOME 1w
Proof
  EVAL_TAC
QED

(* Both marked witnesses have exactly the same source result/state and marks.
   Only their target state and final taint differ. No source gas is read. *)
Theorem word_hit_marked_prefix:
  gas_marked_exec_ptr D (ctx,word_hit_fn) [] (return ())
    (es,word_hit_s0,FEMPTY,entry_taint) []
    (INL ()) es FEMPTY entry_taint (OK word_hit_u)
Proof
  simp[gas_marked_exec_ptr_def, vyperStateTheory.return_def,
       word_hit_prefix_path]
QED

Theorem word_hit_marked_full:
  gas_marked_exec_ptr D (ctx,word_hit_fn) [] (return ())
    (es,word_hit_s0,FEMPTY,entry_taint) []
    (INL ()) es FEMPTY word_hit_tn (OK word_hit_t)
Proof
  simp[gas_marked_exec_ptr_def, vyperStateTheory.return_def,
       word_hit_full_path]
QED

(* The full marked trace satisfies this inline Q; its first-hit prefix does not.
   This is NOT a counterexample to expr_post or to the frozen task theorem. *)
Theorem word_hit_post_not_retained:
  (lookup_var "x" word_hit_t = SOME 1w /\
   word_hit_t.vs_current_bb = "end" /\ word_hit_t.vs_inst_idx = 0) /\
  ~(lookup_var "x" word_hit_u = SOME 1w /\
    word_hit_u.vs_current_bb = "end" /\ word_hit_u.vs_inst_idx = 0)
Proof
  EVAL_TAC >> WORD_DECIDE_TAC
QED
