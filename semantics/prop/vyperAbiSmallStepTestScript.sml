(* Direct CPS/CV execution and big-step transport of the pinned ABI regression.
   The general equivalence theorem is unrestricted: no typing/purity premises.
   cv_eval tests below run CPS frames, not the big-step equivalence rewrite. *)
Theory vyperAbiSmallStepTest
Ancestors
  vyperSmallStep vyperAbiAliasTest vyperInterpreter vyperContext vyperState
  vyperAST vyperValue vyperAbiOperand list While finite_map
Libs
  cv_transLib wordsLib monadsyntax

val () = List.app cv_auto_trans
  [alias_array_type_def, alias_array_tv_def, alias_state_def, alias_expr_def,
   indexed_alias_state_def, conditional_alias_state_def];

Definition abi_cps_run_def:
  abi_cps_run e st = fromtvk (cont
    (eval_expr_cps empty_evaluation_context e st DoneK))
End
(* Keep the endpoint-validity rule explicit at this translation boundary. *)
val () = cv_memLib.cv_pre_add cont_pre_eval_expr_cps;
val () = cv_auto_trans abi_cps_run_def;

Theorem successful_values_cont:
  FST run = INL vs ⇒
  ∃rt. SOME (AK cx (ApplyVals vs) rt DoneK) =
       cont (liftk cx ApplyVals run DoneK)
Proof
  Cases_on `run` >> rename1 `FST (res,rt)` >> Cases_on `res` >>
  simp[liftk_def, cont_def, Once OWHILE_THM]
QED

Theorem smallstep_alias_matches_pinned:
  FST (fromtvk (cont
    (eval_expr_cps empty_evaluation_context alias_expr alias_state DoneK))) =
  INL (Value (BytesV
    (REPLICATE 31 0w ++ [64w] ++ REPLICATE 32 0w ++
     REPLICATE 31 0w ++ [1w] ++ REPLICATE 31 0w ++ [1w])))
Proof
  CONV_TAC cv_eval
QED

Theorem smallstep_alias_releases_tokens:
  (SND (fromtvk (cont
    (eval_expr_cps empty_evaluation_context alias_expr alias_state DoneK)))).abi_memory = []
Proof
  CONV_TAC cv_eval
QED

(* Whole result/state connection, independently of the direct execution below. *)
Theorem smallstep_alias_whole_result_eq_bigstep:
  abi_cps_run alias_expr alias_state =
  eval_expr empty_evaluation_context alias_expr alias_state
Proof
  simp[abi_cps_run_def, GSYM eval_expr_eq_cont_cps]
QED

Theorem smallstep_captures_effectful_index_once:
  ∃rt. cont (eval_abi_exprs_cps empty_evaluation_context
    [Subscript alias_array_type
       (Name (ArrayT alias_array_type (Dynamic 2)) "a")
       (Pop (BaseT (UintT 256)) (NameTarget "i"));
     Pop (BaseT BoolT)
       (SubscriptTarget (NameTarget "a") (Literal (BaseT (UintT 256)) (IntL 1)))]
    indexed_alias_state (AbiStageK DoneK)) =
    SOME (AK empty_evaluation_context
      (ApplyVals [ArrayV (DynArrayV [BoolV F]); BoolV T]) rt DoneK)
Proof
  simp[eval_abi_exprs_stage_cps_eq] >> irule successful_values_cont >>
  ACCEPT_TAC index_is_evaluated_once_before_later_effect
QED

Theorem smallstep_captures_effectful_condition_once:
  ∃rt. cont (eval_abi_exprs_cps empty_evaluation_context
    [IfExp alias_array_type (Pop (BaseT BoolT) (NameTarget "cond"))
       (Name alias_array_type "a") (Name alias_array_type "missing");
     Pop (BaseT BoolT) (NameTarget "a")]
    conditional_alias_state (AbiStageK DoneK)) =
    SOME (AK empty_evaluation_context
      (ApplyVals [ArrayV (DynArrayV [BoolV T]); BoolV F]) rt DoneK)
Proof
  simp[eval_abi_exprs_stage_cps_eq] >> irule successful_values_cont >>
  ACCEPT_TAC condition_is_evaluated_once_and_keeps_memory_alias
QED

Theorem smallstep_complex_pop_keeps_backing_cells:
  ∃rt. cont (eval_abi_exprs_cps empty_evaluation_context
    [Subscript alias_array_type
       (Name (ArrayT alias_array_type (Dynamic 2)) "a")
       (Literal (BaseT (UintT 256)) (IntL 1));
     Pop alias_array_type (NameTarget "a")]
    indexed_alias_state (AbiStageK DoneK)) =
    SOME (AK empty_evaluation_context
      (ApplyVals [ArrayV (DynArrayV [BoolV F; BoolV T]);
                  ArrayV (DynArrayV [BoolV F; BoolV T])]) rt DoneK)
Proof
  simp[eval_abi_exprs_stage_cps_eq] >> irule successful_values_cont >>
  ACCEPT_TAC complex_pop_retains_backing_cells
QED

(* Actual TypeBuiltin execution: the index/condition pops must not be replayed
   and the aliased complex value must not be snapshotted before the later pop. *)
Definition abi_index_expr_def:
  abi_index_expr = TypeBuiltin (BaseT (BytesT (Dynamic 160))) (AbiEncode F NONE)
    (TupleT [alias_array_type; BaseT BoolT])
    [Subscript alias_array_type
       (Name (ArrayT alias_array_type (Dynamic 2)) "a")
       (Pop (BaseT (UintT 256)) (NameTarget "i"));
     Pop (BaseT BoolT)
       (SubscriptTarget (NameTarget "a") (Literal (BaseT (UintT 256)) (IntL 1)))]
End
val () = cv_auto_trans abi_index_expr_def;

Definition abi_condition_expr_def:
  abi_condition_expr = TypeBuiltin (BaseT (BytesT (Dynamic 160))) (AbiEncode F NONE)
    (TupleT [alias_array_type; BaseT BoolT])
    [IfExp alias_array_type (Pop (BaseT BoolT) (NameTarget "cond"))
       (Name alias_array_type "a") (Name alias_array_type "missing");
     Pop (BaseT BoolT) (NameTarget "a")]
End
val () = cv_auto_trans abi_condition_expr_def;

Theorem smallstep_index_executes_once:
  let run = abi_cps_run abi_index_expr indexed_alias_state in
    FST run = INL (Value (BytesV
      (REPLICATE 31 0w ++ [64w] ++ REPLICATE 31 0w ++ [1w] ++
       REPLICATE 31 0w ++ [1w] ++ REPLICATE 32 0w))) ∧
    (SND run).abi_memory = [] ∧
    lookup_scopes_val "i" (SND run).scopes = SOME (ArrayV (DynArrayV []))
Proof
  CONV_TAC cv_eval
QED

Theorem smallstep_condition_executes_once:
  let run = abi_cps_run abi_condition_expr conditional_alias_state in
    FST run = INL (Value (BytesV
      (REPLICATE 31 0w ++ [64w] ++ REPLICATE 32 0w ++
       REPLICATE 31 0w ++ [1w] ++ REPLICATE 31 0w ++ [1w]))) ∧
    (SND run).abi_memory = [] ∧
    lookup_scopes_val "cond" (SND run).scopes = SOME (ArrayV (DynArrayV []))
Proof
  CONV_TAC cv_eval
QED

(* Begin inside an outer capture.  Exceptional inner cleanup must retain that
   token AND its updated backing cells, not merely reset abi_memory to []. *)
Definition abi_outer_state_def:
  abi_outer_state = SND (capture_abi_memory empty_evaluation_context "a"
    alias_array_tv (ArrayV (DynArrayV [BoolV T; BoolV F])) alias_state)
End
val () = cv_auto_trans abi_outer_state_def;

Definition abi_error_expr_def:
  abi_error_expr = TypeBuiltin (BaseT (BytesT (Dynamic 160))) (AbiEncode F NONE)
    (TupleT [alias_array_type; BaseT BoolT; alias_array_type])
    [Name alias_array_type "a"; Pop (BaseT BoolT) (NameTarget "a");
     Name alias_array_type "missing"]
End
val () = cv_auto_trans abi_error_expr_def;

Theorem smallstep_error_preserves_older_alias_write:
  let run = abi_cps_run abi_error_expr abi_outer_state in
    FST run = INR (Error (TypeError "Name not in scope")) ∧
    LENGTH (SND run).abi_memory = 1 ∧
    FST (read_abi_operand empty_evaluation_context
      (AbiMemory 0 0 alias_array_tv) (SND run)) =
      INL (ArrayV (DynArrayV [BoolV T])) ∧
    lookup_scopes_val "a" (SND run).scopes =
      SOME (ArrayV (DynArrayV [BoolV T]))
Proof
  CONV_TAC cv_eval
QED

Definition abi_projection_error_expr_def:
  abi_projection_error_expr = TypeBuiltin (BaseT (BytesT (Dynamic 160)))
    (AbiEncode F NONE) (TupleT [alias_array_type; BaseT BoolT])
    [Name alias_array_type "a";
     Subscript (BaseT BoolT) (Name alias_array_type "a")
       (Literal (BaseT (UintT 256)) (IntL 2))]
End
val () = cv_auto_trans abi_projection_error_expr_def;

Theorem smallstep_bad_index_cleans_captures:
  let run = abi_cps_run abi_projection_error_expr alias_state in
    FST run = INR (Error (RuntimeError "ABI subscript bounds")) ∧
    (SND run).abi_memory = [] ∧
    lookup_scopes_val "a" (SND run).scopes =
      SOME (ArrayV (DynArrayV [BoolV T; BoolV F]))
Proof
  CONV_TAC cv_eval
QED

Definition abi_condition_error_expr_def:
  abi_condition_error_expr = TypeBuiltin (BaseT (BytesT (Dynamic 160)))
    (AbiEncode F NONE) (TupleT [alias_array_type; alias_array_type])
    [Name alias_array_type "a";
     IfExp alias_array_type (Literal (BaseT (UintT 256)) (IntL 0))
       (Name alias_array_type "a") (Name alias_array_type "missing")]
End
val () = cv_auto_trans abi_condition_error_expr_def;

Theorem smallstep_bad_condition_cleans_captures:
  let run = abi_cps_run abi_condition_error_expr alias_state in
    FST run = INR (Error (TypeError "not BoolV")) ∧
    (SND run).abi_memory = [] ∧
    lookup_scopes_val "a" (SND run).scopes =
      SOME (ArrayV (DynArrayV [BoolV T; BoolV F]))
Proof
  CONV_TAC cv_eval
QED

(* Verify the connection/translation exports and every regression are closed.
   DISK_THM is the standard saved-theorem tag, not an admission oracle. *)
fun check_abi_closed (thy,n) = let
  val th = DB.fetch thy n
  val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  val _ = if null (Thm.hyp th) andalso null axioms andalso
      List.all (fn s => s = "DISK_THM") oracles then ()
    else raise Fail (thy ^ "." ^ n ^ ": not kernel-closed/unadmitted")
  in print ("ABI_SMALLSTEP_KERNEL_CLOSED " ^ thy ^ "." ^ n ^ "\n") end;

val () = List.app check_abi_closed
  [("vyperSmallStep", "eval_cps_eq"),
   ("vyperSmallStep", "eval_abi_expr_cps_eq"),
   ("vyperSmallStep", "eval_abi_exprs_cps_eq"),
   ("vyperSmallStep", "eval_abi_exprs_stage_cps_eq"),
   ("vyperSmallStep", "eval_expr_eq_cont_cps"),
   ("vyperSmallStep", "abi_release_step"),
   ("vyperSmallStep", "cv_eval_expr_cps_thm"),
   ("vyperSmallStep", "cv_cont_thm")];

Theorem smallstep_error_releases_tokens:
  (SND (fromtvk (cont (eval_expr_cps empty_evaluation_context
    (TypeBuiltin (BaseT (BytesT (Dynamic 160))) (AbiEncode F NONE)
      (TupleT [alias_array_type; alias_array_type])
      [Name alias_array_type "a"; Name alias_array_type "missing"])
    alias_state DoneK)))).abi_memory = []
Proof
  CONV_TAC cv_eval
QED

val () = List.app (fn (n,_) =>
  check_abi_closed ("vyperAbiSmallStepTest",n))
  (DB.thms "vyperAbiSmallStepTest");
