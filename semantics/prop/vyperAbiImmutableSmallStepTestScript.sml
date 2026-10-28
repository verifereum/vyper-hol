(* Pin cd74ce4f: constructor projected assignment runs in BOTH backends.
   Execute actual CPS statement frames, then ABI-encode the immutable child.
   This is not a rewrite of the computation through big-step equivalence. *)
Theory vyperAbiImmutableSmallStepTest
Ancestors
  vyperSmallStep vyperAbiImmutableProjectionTest vyperAbiAliasTest
  vyperContext vyperState vyperInterpreter vyperAST vyperValue
  vyperAbiOperand list rich_list finite_map alist While arithmetic combin
Libs
  cv_transLib wordsLib

val () = List.app cv_auto_trans
  [alias_array_type_def, alias_array_tv_def, immutable_nested_type_def,
   immutable_projection_context_def, immutable_projection_state_def,
   immutable_projection_expr_def];

Theorem cont_pre_eval_stmts_cps[cv_pre]:
  cont_pre (eval_stmts_cps cx ss st DoneK)
Proof
  rw[cont_pre_IS_SOME_cont] >>
  qspecl_then [`cx`,`ss`,`st`,`DoneK`] mp_tac (cj 2 eval_cps_eq) >>
  rw[cont_def] >> Cases_on `eval_stmts cx ss st` >>
  rename1 `eval_stmts cx ss st = (res,rt)` >>
  Cases_on `res` >> gvs[] >> rw[Once WhileTheory.OWHILE_THM]
QED
val () = cv_memLib.cv_pre_add cont_pre_eval_stmts_cps;

Definition immutable_assignment_cps_program_def:
  immutable_assignment_cps_program =
    [Assign (BaseTarget (SubscriptTarget
       (SubscriptTarget (TopLevelNameTarget (NONE,"a"))
         (Pop (BaseT (UintT 256)) (NameTarget "indices")))
       (Literal (BaseT (UintT 256)) (IntL 0))))
       (Literal (BaseT BoolT) (BoolL F));
     Return (SOME (TypeBuiltin (BaseT (BytesT (Dynamic 128)))
       (AbiEncode T NONE) (TupleT [alias_array_type])
       [immutable_projection_expr]))]
End
val () = cv_auto_trans immutable_assignment_cps_program_def;

(* A concrete step bound avoids the generic cont precondition at this
   statement-test translation boundary. DoneK is checked below, not assumed. *)
Definition immutable_assignment_cps_machine_def:
  immutable_assignment_cps_machine = FUNPOW stepk 23
    (eval_stmts_cps immutable_projection_context immutable_assignment_cps_program
      immutable_projection_state DoneK)
End
Definition immutable_assignment_cps_result_def:
  immutable_assignment_cps_result = fromtvk (SOME immutable_assignment_cps_machine)
End

Definition immutable_pure_encode_def:
  immutable_pure_encode = TypeBuiltin (BaseT (BytesT (Dynamic 128)))
    (AbiEncode T NONE) (TupleT [alias_array_type]) [immutable_projection_expr]
End
val () = cv_auto_trans immutable_pure_encode_def;

Definition immutable_pure_cps_result_def:
  immutable_pure_cps_result = fromtvk (cont
    (eval_expr_cps immutable_projection_context immutable_pure_encode
      immutable_projection_state DoneK))
End
val () = cv_memLib.cv_pre_add cont_pre_eval_expr_cps;
val () = cv_auto_trans immutable_pure_cps_result_def;

Theorem immutable_smallstep_pure_read_restores_exact_state:
  FST immutable_pure_cps_result = INL (Value (BytesV
    (REPLICATE 31 0w ++ [32w] ++ REPLICATE 31 0w ++ [2w] ++
     REPLICATE 31 0w ++ [1w] ++ REPLICATE 32 0w))) /\
  SND immutable_pure_cps_result = immutable_projection_state
Proof
  CONV_TAC cv_eval
QED

Theorem cont_bounded[local]:
  !n ak.
    (!i. i < n ==> nextk (FUNPOW stepk i ak) <> DoneK) /\
    nextk (FUNPOW stepk n ak) = DoneK ==>
    cont ak = SOME (FUNPOW stepk n ak)
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- (gvs[] >> simp[Once cont_tr]) >>
  `nextk ak <> DoneK` by
    (qpat_x_assum `!i. _` (qspec_then `0` mp_tac) >> simp[]) >>
  ONCE_REWRITE_TAC [cont_tr] >> simp[Once FUNPOW] >>
  first_x_assum irule >> conj_tac
  >- (rpt strip_tac >> qpat_x_assum `!i. _`
        (qspec_then `SUC i` mp_tac) >> simp[FUNPOW]) >>
  gvs[FUNPOW]
QED

Definition continuation_live_def:
  continuation_live k = (case k of DoneK => F | _ => T)
End
val () = cv_auto_trans continuation_live_def;

Theorem continuation_live_eq[local]:
  continuation_live k <=> k <> DoneK
Proof
  Cases_on `k` >> simp[continuation_live_def]
QED

Definition immutable_assignment_step_live_def:
  immutable_assignment_step_live i = continuation_live (nextk (FUNPOW stepk i
    (eval_stmts_cps immutable_projection_context immutable_assignment_cps_program
      immutable_projection_state DoneK)))
End
val () = cv_auto_trans immutable_assignment_step_live_def;

Definition immutable_assignment_live_prefix_def:
  immutable_assignment_live_prefix =
    EVERY immutable_assignment_step_live (COUNT_LIST 23)
End
val () = cv_auto_trans immutable_assignment_live_prefix_def;

Theorem immutable_smallstep_assignment_reaches_cont_endpoint:
  cont (eval_stmts_cps immutable_projection_context immutable_assignment_cps_program
    immutable_projection_state DoneK) = SOME immutable_assignment_cps_machine
Proof
  simp_tac bool_ss [immutable_assignment_cps_machine_def] >>
  irule cont_bounded >> conj_tac
  >- (`immutable_assignment_live_prefix` by CONV_TAC cv_eval >>
      gvs[immutable_assignment_live_prefix_def, immutable_assignment_step_live_def,
        continuation_live_eq, EVERY_MEM, MEM_COUNT_LIST]) >>
  CONV_TAC (LAND_CONV cv_eval) >> REFL_TAC
QED

val IMM_ASSIGN_CV_TAC =
  simp_tac bool_ss [immutable_assignment_cps_result_def,
    immutable_assignment_cps_machine_def] >>
  CONV_TAC (BINOP_CONV cv_eval) >> REFL_TAC;

(* Pinned ABI words: offset 32, length 2, false, false. The index pop runs
   exactly once and constructor assignment survives representation cleanup. *)
Theorem immutable_smallstep_assignment_projection_pinned_bytes:
  nextk immutable_assignment_cps_machine = DoneK /\
  FST immutable_assignment_cps_result =
    INR (ReturnException (BytesV
      (REPLICATE 31 0w ++ [32w] ++ REPLICATE 31 0w ++ [2w] ++
       REPLICATE 64 0w))) /\
  lookup_scopes_val "indices" (SND immutable_assignment_cps_result).scopes =
    SOME (ArrayV (DynArrayV [])) /\
  (SND immutable_assignment_cps_result).abi_memory = [] /\
  (SND immutable_assignment_cps_result).abi_immutables = [] /\
  FST (lookup_global immutable_projection_context NONE "a"
    (SND immutable_assignment_cps_result)) =
    INL (Value (ArrayV (DynArrayV [ArrayV (DynArrayV [BoolV F; BoolV F])])) )
Proof
  rpt conj_tac
  >- IMM_ASSIGN_CV_TAC
  >- IMM_ASSIGN_CV_TAC
  >- IMM_ASSIGN_CV_TAC
  >- IMM_ASSIGN_CV_TAC
  >- IMM_ASSIGN_CV_TAC
  >> IMM_ASSIGN_CV_TAC
QED

Definition immutable_error_cps_result_def:
  immutable_error_cps_result = fromtvk (cont
    (eval_expr_cps immutable_projection_context
      (TypeBuiltin (BaseT (BytesT (Dynamic 128))) (AbiEncode F NONE)
        (TupleT [alias_array_type; BaseT BoolT; alias_array_type])
        [immutable_projection_expr;
         Pop (BaseT BoolT) immutable_projection_target;
         Name alias_array_type "missing"])
      immutable_projection_state DoneK))
End
val () = cv_auto_trans immutable_projection_target_def;
val () = cv_auto_trans immutable_error_cps_result_def;

(* Legacy-validated mutation followed by an evaluator error: release tokens,
   not logical effects. This missing-name error is not a checked source program;
   Venom projected pop itself panics at compilation. *)
Theorem immutable_smallstep_error_retains_mutation_not_fresh_captures:
  FST immutable_error_cps_result =
    INR (Error (TypeError "Name not in scope")) /\
  (SND immutable_error_cps_result).abi_memory = [] /\
  (SND immutable_error_cps_result).abi_immutables = [] /\
  FST (lookup_global immutable_projection_context NONE "a"
    (SND immutable_error_cps_result)) =
    INL (Value (ArrayV (DynArrayV [ArrayV (DynArrayV [BoolV T])])) )
Proof
  rpt conj_tac
  >- CONV_TAC cv_eval
  >- CONV_TAC cv_eval
  >- CONV_TAC cv_eval
  >> CONV_TAC cv_eval
QED

val () = List.app (fn (name,th) => let
  val (oracles,axioms) = Tag.dest_tag (Thm.tag th)
  in if null (Thm.hyp th) andalso null axioms andalso
      List.all (fn s => s = "DISK_THM") oracles then
      print ("IMMUTABLE_SMALLSTEP_KERNEL_CLOSED " ^ name ^ "\n")
    else raise Fail (name ^ ": not kernel-closed") end)
  (DB.thms "vyperAbiImmutableSmallStepTest");
