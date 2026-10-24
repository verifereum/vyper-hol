(* Source-derived witnesses distinguish capture time from load time. *)
Theory vyperLoadTimingTest
Ancestors
  vyperSmallStep vyperState vyperMisc jsonToVyper finite_map While pair
Libs
  jsonASTLib cv_transLib finite_mapLib wordsLib

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
