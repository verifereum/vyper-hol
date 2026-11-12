Theory vyperCodeSliceTest
Ancestors
  vyperInterpreter vyperSmallStep vyperState vyperContext
  vyperValueOperation finite_map words vfmState

Definition code_slice_order_expr_def:
  code_slice_order_expr =
    Builtin (BaseT (BytesT (Dynamic 1))) (Slice 1)
      [Builtin (BaseT (BytesT (Dynamic 24576))) (Acc Code)
        [Subscript (BaseT AddressT)
          (Name (ArrayT (BaseT AddressT) (Dynamic 1)) "addrs")
          (Literal (BaseT (UintT 256)) (IntL 0))];
       TypeBuiltin (BaseT (UintT 256)) Convert (BaseT (UintT 256))
         [Pop (BaseT AddressT) (NameTarget "addrs")];
       Literal (BaseT (UintT 256)) (IntL 1)]
End

Definition code_slice_order_state_def:
  code_slice_order_state = empty_state with
    <| scopes := [FEMPTY |+ ("addrs",
         <|assignable := T;
           type := ArrayTV (BaseTV AddressT) (Dynamic 1);
           value := ArrayV (DynArrayV [BytesV (REPLICATE 20 0w)]); popped := []|>)];
       accounts := (\a. empty_account_state with code := [0w]) |>
End

(* The length operand empties addrs before the code address is indexed. *)
Theorem code_slice_start_before_address:
  FST (eval_expr empty_evaluation_context code_slice_order_expr
    code_slice_order_state) =
  INR (Error (RuntimeError "evaluate_subscripts array_index"))
Proof
  EVAL_TAC >>
  simp[lookup_scopes_def, FLOOKUP_UPDATE, FLOOKUP_EMPTY,
       subscript_type_def, return_def, integerTheory.INT_LE_REFL] >>
  EVAL_TAC >> simp[return_def, integerTheory.INT_LE_REFL] >> EVAL_TAC >>
  simp[return_def, integerTheory.INT_LE_REFL] >> EVAL_TAC >>
  simp[wordsTheory.word_0_n2w, wordsTheory.w2n_n2w] >> EVAL_TAC >>
  simp[integerTheory.INT_LT_REFL, integerTheory.INT_NOT_LT, return_def]
QED

Theorem code_slice_cps_start_before_address:
  FST (fromtvk (cont (eval_expr_cps empty_evaluation_context
    code_slice_order_expr code_slice_order_state DoneK))) =
  INR (Error (RuntimeError "evaluate_subscripts array_index"))
Proof
  simp[GSYM eval_expr_eq_cont_cps, code_slice_start_before_address]
QED

Definition self_code_slice_expr_def:
  self_code_slice_expr =
    Builtin (BaseT (BytesT (Dynamic 2))) (Slice 2)
      [Builtin (BaseT (BytesT (Dynamic 24576))) (Acc Code)
        [Builtin (BaseT AddressT) (Env SelfAddr) []];
       Literal (BaseT (UintT 256)) (IntL 1);
       Literal (BaseT (UintT 256)) (IntL 2)]
End

(* During deployment (installed account code = []), slice(self.code, 1, 2)
   reads the active frame's cx.txn.code. *)
Theorem self_code_slice_reads_txn_code:
  FST (eval_expr
    (empty_evaluation_context with
       txn := empty_call_txn with code := [0x11w; 0x22w; 0x33w])
    self_code_slice_expr empty_state) =
  INL (Value (BytesV [0x22w; 0x33w]))
Proof
  EVAL_TAC >> simp[return_def] >> EVAL_TAC
QED

Theorem self_code_slice_cps_reads_txn_code:
  FST (fromtvk (cont (eval_expr_cps
    (empty_evaluation_context with
       txn := empty_call_txn with code := [0x11w; 0x22w; 0x33w])
    self_code_slice_expr empty_state DoneK))) =
  INL (Value (BytesV [0x22w; 0x33w]))
Proof
  simp[GSYM eval_expr_eq_cont_cps, self_code_slice_reads_txn_code]
QED
