Theory fnAliasInvAvailability
Ancestors
  fnAliasInvLiveness venomWf rich_list list

(* All entry paths have encountered a definition, counting only the strict
   instruction prefix in the final block. Unreachable labels are vacuous. *)
Definition alias_path_available_def:
  alias_path_available fn l i v <=>
    !path. is_fn_path fn path /\ path <> [] /\
      (?entry. fn_entry_label fn = SOME entry /\ HD path = entry) /\
      LAST path = l ==>
      (?k bb inst. k < LENGTH path - 1 /\
        lookup_block (EL k path) fn.fn_blocks = SOME bb /\
        MEM inst bb.bb_instructions /\ MEM v (inst_defs inst)) \/
      (?bb j. lookup_block l fn.fn_blocks = SOME bb /\
        j < i /\ j < LENGTH bb.bb_instructions /\
        MEM v (inst_defs (EL j bb.bb_instructions)))
End

Definition alias_pending_phi_def:
  alias_pending_phi fn l i v <=>
    ?bb inst. lookup_block l fn.fn_blocks = SOME bb /\
      MEM inst (DROP i (collect_phis bb.bb_instructions)) /\
      MEM v (inst_uses inst)
End

Theorem alias_pending_phi_past_prefix:
  LENGTH (collect_phis bb.bb_instructions) <= i /\
  lookup_block l fn.fn_blocks = SOME bb ==>
  ~alias_pending_phi fn l i v
Proof
  strip_tac >>
  `DROP i (collect_phis bb.bb_instructions) = []` by
    (simp[GSYM LENGTH_NIL, LENGTH_DROP]) >>
  simp[alias_pending_phi_def]
QED

Definition alias_phi_loop_fn_def:
  alias_phi_loop_fn = mk_raw_function "phi_loop"
    [<| bb_label := "entry"; bb_instructions :=
       [mk_inst 0 PARAM [] ["seed"];
        mk_inst 1 JMP [Label "header"] []] |>;
     <| bb_label := "header"; bb_instructions :=
       [mk_inst 2 PHI [Label "entry"; Var "seed";
                       Label "body"; Var "next"] ["p"];
        mk_inst 3 ISZERO [Var "p"] ["z"];
        mk_inst 4 JMP [Label "body"] []] |>;
     <| bb_label := "body"; bb_instructions :=
       [mk_inst 5 ADD [Var "p"; Lit 1w] ["next"];
        mk_inst 6 JMP [Label "header"] []] |>]
End

Theorem alias_phi_loop_liveness:
  MEM "next" (live_vars_at (liveness_analyze alias_phi_loop_fn) "header" 0) /\
  MEM "seed" (input_vars_from "entry"
    (EL 1 alias_phi_loop_fn.fn_blocks).bb_instructions
    (live_vars_at (liveness_analyze alias_phi_loop_fn) "header" 0)) /\
  ~MEM "next" (input_vars_from "entry"
    (EL 1 alias_phi_loop_fn.fn_blocks).bb_instructions
    (live_vars_at (liveness_analyze alias_phi_loop_fn) "header" 0)) /\
  alias_pending_phi alias_phi_loop_fn "header" 0 "next" /\
  (!v. ~alias_pending_phi alias_phi_loop_fn "header" 1 v)
Proof
  EVAL_TAC >> simp[livenessDefsTheory.collect_phis_def] >> EVAL_TAC
QED

Theorem alias_phi_loop_not_available:
  ~alias_path_available alias_phi_loop_fn "header" 0 "next"
Proof
  simp[alias_path_available_def] >>
  qexists_tac `["entry"; "header"]` >>
  EVAL_TAC >> simp[SF DNF_ss] >> EVAL_TAC >>
  rpt strip_tac >> CCONTR_TAC >> gvs[]
QED
