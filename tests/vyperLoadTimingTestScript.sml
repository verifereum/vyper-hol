(* Source-derived witnesses distinguish capture time from load time. *)
Theory vyperLoadTimingTest
Ancestors
  vyperSmallStep vyperState vyperMisc jsonToVyper finite_map While pair
  vyperTypeContract vyperInterpreter vyperAbiOperand
Libs
  jsonASTLib cv_transLib finite_mapLib wordsLib vyperCheckContractLib

fun holbuild_extra_deps (_ : string list) = ()
val () = holbuild_extra_deps ["fixtures/load_timing"]
val () = computeLib.upd_compset add_finite_map_compset

fun load_fixture name = let
  val path = "fixtures/load_timing/oracle/" ^ name ^ ".json"
  val ast = JSONDecode.decodeFile jsonASTLib.annotated_ast path
  val layout = JSONDecode.decodeFile jsonASTLib.storage_layout path
  val translation = optionSyntax.dest_some
    (rhs (concl (EVAL ``translate_annotated_ast ^ast``)))
  val (sources, rest) = pairSyntax.dest_pair translation
  val (_, imports) = pairSyntax.dest_pair rest
  val modules = rhs (concl (EVAL ``annotate_sources_slots ^layout ^sources``))
  val slots = rhs (concl (EVAL ``extract_storage_layout ^imports ^layout``))
  val program = optionSyntax.dest_some
    (rhs (concl (EVAL ``ALOOKUP ^modules NONE``)))
in
  (program, ``empty_evaluation_context with
    <|sources := [(0w, ^modules)]; layouts := [(0w, ^slots)]|>``)
end;

val (pop_program, pop_context) = load_fixture "pop_refill";
val (conditional_program, conditional_context) = load_fixture "conditional_snapshot";
val (memory_view_program, memory_view_context) = load_fixture "conditional_memory_view";
val (nested_pop_program, nested_pop_context) = load_fixture "nested_retained_pop";
val (call_storage_program, call_storage_context) = load_fixture "call_storage_read";
val (call_memory_program, call_memory_context) = load_fixture "call_memory_pop";
val (builtin_eager_program, builtin_eager_context) = load_fixture "builtin_eager_read";

Definition pop_refill_program_def:
  pop_refill_program = ^pop_program
End
val () = cv_auto_trans pop_refill_program_def;

Definition pop_refill_context_def:
  pop_refill_context = ^pop_context
End
val () = cv_auto_trans pop_refill_context_def;

Definition conditional_snapshot_program_def:
  conditional_snapshot_program = ^conditional_program
End
val () = cv_auto_trans conditional_snapshot_program_def;

Definition conditional_snapshot_context_def:
  conditional_snapshot_context = ^conditional_context
End
val () = cv_auto_trans conditional_snapshot_context_def;

Definition conditional_memory_view_program_def:
  conditional_memory_view_program = ^memory_view_program
End
val () = cv_auto_trans conditional_memory_view_program_def;

Definition conditional_memory_view_context_def:
  conditional_memory_view_context = ^memory_view_context
End
val () = cv_auto_trans conditional_memory_view_context_def;

Definition nested_retained_pop_program_def:
  nested_retained_pop_program = ^nested_pop_program
End
val () = cv_auto_trans nested_retained_pop_program_def;

Definition nested_retained_pop_context_def:
  nested_retained_pop_context = ^nested_pop_context
End
val () = cv_auto_trans nested_retained_pop_context_def;

Definition call_storage_read_program_def:
  call_storage_read_program = ^call_storage_program
End
val () = cv_auto_trans call_storage_read_program_def;

Definition call_storage_read_context_def:
  call_storage_read_context = ^call_storage_context
End
val () = cv_auto_trans call_storage_read_context_def;

Definition call_memory_pop_program_def:
  call_memory_pop_program = ^call_memory_program
End
val () = cv_auto_trans call_memory_pop_program_def;

Definition call_memory_pop_context_def:
  call_memory_pop_context = ^call_memory_context
End
val () = cv_auto_trans call_memory_pop_context_def;

Definition builtin_eager_read_program_def:
  builtin_eager_read_program = ^builtin_eager_program
End
val () = cv_auto_trans builtin_eager_read_program_def;

Definition builtin_eager_read_context_def:
  builtin_eager_read_context = ^builtin_eager_context
End
val () = cv_auto_trans builtin_eager_read_context_def;

Theorem load_timing_cont_pre[cv_pre]:
  cont_pre (eval_stmts_cps cx ss st DoneK)
Proof
  rw[cont_pre_IS_SOME_cont] >>
  qspecl_then [`cx`,`ss`,`st`,`DoneK`] mp_tac (cj 2 eval_cps_eq) >>
  rw[cont_def] >> CASE_TAC >> CASE_TAC >> gvs[] >>
  rw[Once OWHILE_THM]
QED

(* Bind the exported entry's actual parameter declarations, then observe its
   return value. The body and all internal callees come from the source AST. *)
Definition load_timing_run_def:
  load_timing_run cx program args = do
    (mut,nr,params,dflts,ret,ss) <- lift_option_type
      (lookup_function NONE "f" External program) "load timing entry";
    env <- lift_option_type (bind_arguments (get_tenv cx) params args)
             "load timing arguments";
    set_scopes [env];
    try (do eval_stmts cx ss; return NoneV od) handle_function
  od
End
val () = load_timing_run_def
  |> SRULE [FUN_EQ_THM, bind_def, ignore_bind_def, try_def,
            LET_RATOR, UNCURRY, prod_CASE_rator, sum_CASE_rator,
            eval_stmts_eq_cont_cps]
  |> cv_auto_trans;

Theorem popped_storage_result_reads_after_target_refill:
  FST (load_timing_run pop_refill_context pop_refill_program [] empty_state) =
    INL (IntV 9)
Proof
  CONV_TAC cv_eval
QED

Theorem conditional_storage_result_snapshots_before_target_change:
  FST (load_timing_run conditional_snapshot_context
    conditional_snapshot_program [BoolV T] empty_state) = INL (IntV 5) /\
  FST (load_timing_run conditional_snapshot_context
    conditional_snapshot_program [BoolV F] empty_state) = INL (IntV 5)
Proof
  CONV_TAC cv_eval
QED

Theorem conditional_memory_result_observes_target_pop:
  FST (load_timing_run conditional_memory_view_context
    conditional_memory_view_program [BoolV T] empty_state) = INL (IntV 1) /\
  FST (load_timing_run conditional_memory_view_context
    conditional_memory_view_program [BoolV F] empty_state) = INL (IntV 1)
Proof
  CONV_TAC cv_eval
QED

Theorem nested_pop_uses_retained_inner_location:
  FST (load_timing_run nested_retained_pop_context
    nested_retained_pop_program [] empty_state) = INL (IntV 5)
Proof
  CONV_TAC cv_eval
QED

(* ABI-wrap the source-derived nested-pop expression, retaining its exact
   declaration and index AST. This is f() -> Bytes[32] with return
   abi_encode(d[0][d.pop()[0][0]].pop()). No index is reconstructed. *)
val nested_abi_program = rhs (concl (EVAL
  ``case nested_retained_pop_program of
    [FunctionDecl vis mut nr raw id params dflts ret
      [decl; Return (SOME e)]] =>
      [FunctionDecl vis mut nr raw id params dflts
        (BaseT (BytesT (Dynamic 32)))
        [decl; Return (SOME (TypeBuiltin (BaseT (BytesT (Dynamic 32)))
          (AbiEncode T NONE) (TupleT [expr_type e]) [e]))]]
    | _ => []``));

Definition nested_retained_abi_program_def:
  nested_retained_abi_program = ^nested_abi_program
End
val () = cv_auto_trans nested_retained_abi_program_def;

Theorem nested_retained_abi_program_checked:
  IS_SOME (check_contract F [] (0w : address)
    [(NONE, nested_retained_abi_program)])
Proof
  simp[nested_retained_abi_program_def] >>
  CONV_TAC (RAND_CONV vyperCheckContractLib.check_contract_conv) >> simp[]
QED

Theorem abi_encode_nested_pop_uses_retained_inner_location:
  FST (load_timing_run nested_retained_pop_context
    nested_retained_abi_program [] empty_state) =
    INL (BytesV (REPLICATE 31 0w ++ [5w]))
Proof
  CONV_TAC cv_eval
QED

(* Exercise the CPS entry explicitly as well as the direct evaluator. *)
Definition load_timing_run_cps_def:
  load_timing_run_cps cx program args = do
    (mut,nr,params,dflts,ret,ss) <- lift_option_type
      (lookup_function NONE "f" External program) "load timing entry";
    env <- lift_option_type (bind_arguments (get_tenv cx) params args)
             "load timing arguments";
    set_scopes [env];
    try (do (λst. fromk (cont (eval_stmts_cps cx ss st DoneK))); return NoneV od)
      handle_function
  od
End

Theorem load_timing_run_cps_eq:
  load_timing_run_cps = load_timing_run
Proof
  simp_tac bool_ss [FUN_EQ_THM, load_timing_run_cps_def, load_timing_run_def,
    GSYM eval_stmts_eq_cont_cps] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >> simp_tac bool_ss []
QED

Theorem abi_encode_nested_pop_cps_exact:
  FST (load_timing_run_cps nested_retained_pop_context
    nested_retained_abi_program [] empty_state) =
    INL (BytesV (REPLICATE 31 0w ++ [5w]))
Proof
  simp[load_timing_run_cps_eq, abi_encode_nested_pop_uses_retained_inner_location]
QED

(* A fresh capture must keep the root-relative alias, not put the retained
   child in an unrelated snapshot/root. Later writes update the same cells. *)
Definition retained_abi_state_def:
  retained_abi_state = empty_state with scopes :=
    [FEMPTY |+ ("d", <| assignable := T;
      type := ArrayTV (ArrayTV (ArrayTV (BaseTV (UintT 256)) (Dynamic 2))
                (Dynamic 2)) (Dynamic 2);
      value := ArrayV (DynArrayV []);
      popped := [([ValueSubscript (IntV 0)],
        ArrayV (DynArrayV [ArrayV (DynArrayV [IntV 0; IntV 5])]))] |>)]
End

Theorem retained_abi_capture_later_pop_aliases:
  FST ((do
    arg <- abi_place_operand empty_evaluation_context
      (MemoryPlace "d" [ValueSubscript (IntV 0); ValueSubscript (IntV 0)]);
    pop_place empty_evaluation_context
      (MemoryPlace "d" [ValueSubscript (IntV 0); ValueSubscript (IntV 0)]);
    read_abi_operand empty_evaluation_context arg
  od) retained_abi_state) = INL (ArrayV (DynArrayV [IntV 0]))
Proof
  EVAL_TAC
QED

Theorem call_storage_argument_reads_after_later_argument:
  FST (load_timing_run call_storage_read_context
    call_storage_read_program [] empty_state) = INL (IntV 10)
Proof
  CONV_TAC cv_eval
QED

Theorem call_memory_argument_reads_after_later_pop:
  FST (load_timing_run call_memory_pop_context
    call_memory_pop_program [] empty_state) = INL (IntV 1)
Proof
  CONV_TAC cv_eval
QED

Theorem builtin_storage_argument_reads_before_later_argument:
  FST (load_timing_run builtin_eager_read_context
    builtin_eager_read_program [] empty_state) = INL (IntV 0)
Proof
  CONV_TAC cv_eval
QED
