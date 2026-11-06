(* Execute generated deep-DUP assembly at both restore-strategy boundaries.
   Check the physical stack, pre-existing memory, and the external state frame. *)
Theory deepDupChecks
Ancestors stackPlanOps stackPlanTypes stackModel planExec asmSem words list byte
Libs wordsLib

val () = computeLib.upd_compset (computeLib.add_thms [set_byte_def])

(* Reduce one actual interpreter step, leaving its recursive continuation
   opaque. Bounded groups keep each proof fragment within the normal timeout. *)
val asm_runner = ``run_asm_aux``;
fun DEEP_DUP_STEP_CONV tm =
  let val (head,args) = strip_comb tm
  in if same_const head asm_runner andalso length args = 5 then
       let val unfolded = ONCE_REWRITE_CONV [run_asm_aux_def] tm
       in TRANS unfolded (computeLib.RESTR_EVAL_CONV [asm_runner]
            (rhs (concl unfolded))) end
     else raise mk_HOL_ERR "deepDupChecks" "DEEP_DUP_STEP_CONV"
       "not an applied assembly interpreter"
  end;
fun DEEP_DUP_CASE_CONV tm =
  let val (_,args) = strip_comb tm
  in (funpow (length args - 1) RATOR_CONV
        (RAND_CONV DEEP_DUP_STEP_CONV)) tm end;
val DEEP_DUP_STEP_TAC =
  TRY (CONV_TAC (BINDER_CONV DEEP_DUP_CASE_CONV));

Definition deep_dup_input_stack_def:
  deep_dup_input_stack = GENLIST (\n. n2w n : bytes32) 40
End

Definition deep_dup_input_memory_def:
  deep_dup_input_memory = GENLIST (\n. n2w n : byte) 64
End

Definition deep_dup_probe_def:
  deep_dup_probe dist seed <=>
    let ps = (init_plan_state 64) with ps_stack := MAP Lit deep_dup_input_stack in
    let (ops,ps') = do_dup dist ps in
    let initial = seed with <| as_pc := 0;
      as_stack := REVERSE deep_dup_input_stack;
      as_memory := deep_dup_input_memory |> in
    case run_asm 500 (execute_plan 0 ops) initial of
      AsmHalt result =>
        result.as_stack = EL dist (REVERSE deep_dup_input_stack) ::
          REVERSE deep_dup_input_stack /\
        TAKE 64 result.as_memory = deep_dup_input_memory /\
        result with <| as_pc := seed.as_pc; as_stack := seed.as_stack;
                       as_memory := seed.as_memory |> = seed
    | _ => F
End

Theorem deep_dup_first_inaccessible:
  !seed. deep_dup_probe 16 seed
Proof
  CONV_TAC (computeLib.RESTR_EVAL_CONV [asm_runner]) >>
  DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >>
  EVAL_TAC >> simp[]
QED

Theorem deep_dup_two_spills:
  !seed. deep_dup_probe 17 seed
Proof
  CONV_TAC (computeLib.RESTR_EVAL_CONV [asm_runner]) >>
  DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >>
  EVAL_TAC >> simp[]
QED

Theorem deep_dup_last_single_swap:
  !seed. deep_dup_probe 31 seed
Proof
  CONV_TAC (computeLib.RESTR_EVAL_CONV [asm_runner]) >>
  DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >>
  DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >>
  DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >>
  DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >>
  DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >>
  DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >>
  EVAL_TAC >> simp[]
QED

Theorem deep_dup_multiple_restore_swaps:
  !seed. deep_dup_probe 32 seed
Proof
  CONV_TAC (computeLib.RESTR_EVAL_CONV [asm_runner]) >>
  DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >>
  DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >>
  DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >>
  DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >>
  DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >>
  DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >>
  DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >>
  DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >> DEEP_DUP_STEP_TAC >>
  EVAL_TAC >> simp[]
QED
