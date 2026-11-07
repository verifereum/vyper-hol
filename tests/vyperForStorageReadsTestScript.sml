(* Iterating a storage or transient array reads element i from its slots at
   the start of iteration i; the length is read once, at loop entry.  Each loop
   body makes an external call whose outcome rewrites the array (a re-entrant
   write), so later iterations see the new elements, and the loop runs to the
   length read at entry whether the array shrinks or grows.  Copying the array
   at loop entry would give the unchanged sums. *)
Theory vyperForStorageReadsTest
Ancestors
  vyperSmallStep[ignore_grammar] vyperExtCallCpsCVTest
  vyperCallOutcome[ignore_grammar] vfmState[ignore_grammar]
  vfmExecution[ignore_grammar]
  vyperState vyperContext vyperAST vyperValue
  list option pair finite_map words
Libs cv_transLib wordsLib

Definition fsr_context_def:
  fsr_context = empty_evaluation_context with
    <| sources := [(0w, [(NONE,
         [VariableDecl Private Storage "items"
           (ArrayT (BaseT (UintT 256)) (Dynamic 3)) (SOME 4)])])];
       layouts := [(0w, ([((NONE,"items"),4)], [((NONE,"items"),4)]))] |>
End
val () = cv_auto_trans fsr_context_def;

(* items = [1, mid, 3][:len], at slots 4 (length), 5, 6, 7 *)
Definition fsr_accounts_def:
  fsr_accounts len mid = update_account 0w (empty_account_state with storage :=
    update_storage 4w (n2w len) (update_storage 5w 1w
      (update_storage 6w mid (update_storage 7w 3w empty_storage)))) empty_accounts
End
val () = cv_auto_trans fsr_accounts_def;

Definition fsr_outcome_def:
  fsr_outcome len mid =
    <|co_created := 0w; co_success := T; co_returnData := REPLICATE 31 0w ++ [42w];
      co_accounts := fsr_accounts len mid;
      co_tStorage := empty_transient_storage; co_logs := []; co_toDelete := []|>
End
val () = cv_auto_trans fsr_outcome_def;

(* acc: uint256 = 0
   for x: uint256 in self.items:
       acc = acc + x
       extcall f(9) *)
Definition fsr_body_def:
  fsr_body =
    [AnnAssign "acc" (BaseT (UintT 256)) (Literal (BaseT (UintT 256)) (IntL 0));
     For "x" (BaseT (UintT 256))
       (Array (TopLevelName (ArrayT (BaseT (UintT 256)) (Dynamic 3)) (NONE,"items"))) 3
       [Assign (BaseTarget (NameTarget "acc"))
          (Builtin (BaseT (UintT 256)) (Bop Add)
             [Name (BaseT (UintT 256)) "acc"; Name (BaseT (UintT 256)) "x"]);
        Expr (cpscv_call F 9w (BaseT (UintT 256)) NONE)]]
End
val () = cv_auto_trans fsr_body_def;

(* Runs body in cx from the given storage and transient storage, with the
   given call outcomes, and returns the final value of acc. *)
Definition fsr_run_def:
  fsr_run cx body accts ts os =
    case vyperSmallStep$fromk (vyperSmallStep$cont
           (vyperSmallStep$eval_stmts_cps cx body
              (empty_state with <|accounts := accts; tStorage := ts;
                                  scopes := [FEMPTY]; outcomes := SOME os|>)
              vyperSmallStep$DoneK)) of
    | (INL (), st) =>
        (case st.scopes of
         | sc::_ => OPTION_MAP (λv. v.value) (FLOOKUP sc "acc")
         | [] => NONE)
    | _ => NONE
End
val () = cv_auto_trans fsr_run_def;

Definition fsr_acc_def:
  fsr_acc len os =
    fsr_run fsr_context fsr_body (fsr_accounts len 2w) empty_transient_storage os
End
val () = cv_auto_trans fsr_acc_def;

(* The calls leave the array as it was: 1 + 2 + 3. *)
Theorem for_storage_unchanged:
  fsr_acc 3 (REPLICATE 3 (fsr_outcome 3 2w)) = SOME (IntV 6)
Proof
  CONV_TAC cv_eval
QED

(* The first call sets items[1] := 20 and shrinks the array to length 1.
   Iteration 1 reads the new items[1]; iteration 2 still runs, reading slot 7. *)
Theorem for_storage_reads_each_iteration:
  fsr_acc 3 (REPLICATE 3 (fsr_outcome 1 20w)) = SOME (IntV 24)
Proof
  CONV_TAC cv_eval
QED

(* The array starts as [1, 2]; the first call grows it to [1, 2, 3].  The loop
   still runs twice, the length read at entry: 1 + 2. *)
Theorem for_storage_growth_not_iterated:
  fsr_acc 2 (REPLICATE 2 (fsr_outcome 3 2w)) = SOME (IntV 3)
Proof
  CONV_TAC cv_eval
QED

(* pairs: transient(uint256[2][3]) at transient slot 0: element i is the two
   slots 2i and 2i + 1. *)
Definition fsr_tcontext_def:
  fsr_tcontext = empty_evaluation_context with
    <| sources := [(0w, [(NONE,
         [VariableDecl Private Transient "pairs"
           (ArrayT (ArrayT (BaseT (UintT 256)) (Fixed 2)) (Fixed 3)) (SOME 0)])])];
       layouts := [(0w, ([], [((NONE,"pairs"),0)]))] |>
End
val () = cv_auto_trans fsr_tcontext_def;

(* pairs = [[1, 2], [3, mid], [5, 6]] *)
Definition fsr_tstorage_def:
  fsr_tstorage mid = update_transient_storage 0w
    (update_storage 0w 1w (update_storage 1w 2w (update_storage 2w 3w
      (update_storage 3w mid (update_storage 4w 5w
        (update_storage 5w 6w empty_storage)))))) empty_transient_storage
End
val () = cv_auto_trans fsr_tstorage_def;

Definition fsr_toutcome_def:
  fsr_toutcome mid =
    <|co_created := 0w; co_success := T; co_returnData := REPLICATE 31 0w ++ [42w];
      co_accounts := empty_accounts; co_tStorage := fsr_tstorage mid;
      co_logs := []; co_toDelete := []|>
End
val () = cv_auto_trans fsr_toutcome_def;

(* acc: uint256 = 0
   for p: uint256[2] in self.pairs:
       acc = acc + p[1]
       extcall f(9) *)
Definition fsr_tbody_def:
  fsr_tbody =
    [AnnAssign "acc" (BaseT (UintT 256)) (Literal (BaseT (UintT 256)) (IntL 0));
     For "p" (ArrayT (BaseT (UintT 256)) (Fixed 2))
       (Array (TopLevelName
          (ArrayT (ArrayT (BaseT (UintT 256)) (Fixed 2)) (Fixed 3)) (NONE,"pairs"))) 3
       [Assign (BaseTarget (NameTarget "acc"))
          (Builtin (BaseT (UintT 256)) (Bop Add)
             [Name (BaseT (UintT 256)) "acc";
              Subscript (BaseT (UintT 256))
                (Name (ArrayT (BaseT (UintT 256)) (Fixed 2)) "p")
                (Literal (BaseT (UintT 256)) (IntL 1))]);
        Expr (cpscv_call F 9w (BaseT (UintT 256)) NONE)]]
End
val () = cv_auto_trans fsr_tbody_def;

Definition fsr_tacc_def:
  fsr_tacc os = fsr_run fsr_tcontext fsr_tbody empty_accounts (fsr_tstorage 4w) os
End
val () = cv_auto_trans fsr_tacc_def;

(* The calls leave the array as it was: 2 + 4 + 6. *)
Theorem for_transient_unchanged:
  fsr_tacc (REPLICATE 3 (fsr_toutcome 4w)) = SOME (IntV 12)
Proof
  CONV_TAC cv_eval
QED

(* The first call sets pairs[1][1] := 40, read in iteration 1: 2 + 40 + 6. *)
Theorem for_transient_reads_each_iteration:
  fsr_tacc (REPLICATE 3 (fsr_toutcome 40w)) = SOME (IntV 48)
Proof
  CONV_TAC cv_eval
QED
