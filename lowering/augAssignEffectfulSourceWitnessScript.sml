(* Concrete source-only witness; no compiler or invariant admission claim. *)
Theory augAssignEffectfulSourceWitness
Ancestors
  augAssignEffectfulContinuationProbe augAssignEffectfulContractProbe
  vyperInterpreter vyperState vyperContext vyperCallOutcome vyperABI vfmState finite_map

Definition effaug_array_ty_def:
  effaug_array_ty = ArrayT (ArrayT (BaseT (UintT 8)) (Fixed 1)) (Dynamic 1)
End

Definition effaug_tops_def:
  effaug_tops = [VariableDecl Private Storage "a" effaug_array_ty (SOME 0)]
End

Definition effaug_cx_def:
  effaug_cx = empty_evaluation_context with
    <|sources := [(0w, [(NONE, effaug_tops)])];
      layouts := [(0w, ([((NONE,"a"),0)], []))]|>
End

Definition effaug_accounts_def:
  effaug_accounts payload =
    (20w =+ (empty_account_state with code := [0w]))
      ((0w =+ (empty_account_state with storage := payload)) empty_accounts)
End

Definition effaug_outcome_def:
  effaug_outcome =
    <|co_created := 0w; co_toDelete := []; co_success := T;
      co_returnData := REPLICATE 32 0w;
      co_accounts := effaug_accounts (update_storage 1w 256w (\k. 0w));
      co_tStorage := empty_transient_storage; co_logs := []|>
End

Definition effaug_es_def:
  effaug_es = empty_state with
    <|accounts := effaug_accounts (update_storage 0w 1w (\k. 0w));
      outcomes := SOME [effaug_outcome]|>
End

Definition effaug_index_def:
  effaug_index = Call (BaseT (UintT 256))
    (ExtCall F F ("f", [], BaseT (UintT 256)) [])
    [Literal (BaseT AddressT) (BytesL (REPLICATE 19 0w ++ [20w]))] NONE
End

Definition effaug_stmt_def:
  effaug_stmt = AugAssign (BaseT (UintT 8))
    (SubscriptTarget
      (SubscriptTarget (TopLevelNameTarget (NONE,"a"))
        (Literal (BaseT (UintT 256)) (IntL 0))) effaug_index)
    Add (Literal (BaseT (UintT 8)) (IntL 1))
End

Theorem effaug_abi_zero:
  evaluate_abi_decode_return FEMPTY (BaseT (UintT 256)) (REPLICATE 32 0w) =
    INL (IntV 0)
Proof
  EVAL_TAC >> simp[]
QED

Theorem effaug_global_place:
  eval_base_place effaug_cx (TopLevelNameTarget (NONE,"a"))
    (effaug_es with gas_obs := obs) =
    (INL (PlaceR (StoragePlace F 0w
      (ArrayTV (ArrayTV (BaseTV (UintT 8)) (Fixed 1)) (Dynamic 1)))),
     effaug_es with gas_obs := obs)
Proof
  simp[Once evaluate_def] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``effaug_es``]) >>
  simp[vyperValueTheory.type_slot_size_def, SF wordsLib.SIZES_ss,
       return_def]
QED
