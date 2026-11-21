(*
 * Join reorder through spills: a witness
 *
 * A diamond E -> {A, B} -> J where 19 values are live across the branch,
 * so the planner spills some of them before the JMPs into J.  The JMP's
 * join reorder must restore every spilled live-in of J before reordering
 * (as Python's _stack_reorder does), or the two predecessors enter J with
 * different stacks and one path reads the wrong values.  This theory
 * compiles the function with the context codegen, runs the assembly on
 * both paths, and checks each against the Venom interpreter.
 *)
Theory joinSpillWitness
Ancestors
  stackPlanGen planExec asmSem venomExecSemantics venomState venomInst fnPlanLineageReplay
Libs finite_mapLib sortingLib wordsLib

val () = computeLib.upd_compset add_finite_map_compset;
val () = computeLib.upd_compset sortingLib.add_sorting_compset;
val () = computeLib.upd_compset
  (computeLib.add_thms [alistTheory.fmap_to_alist_FEMPTY,
     finite_mapTheory.DRESTRICT_FUPDATE, finite_mapTheory.DRESTRICT_FEMPTY,
     pred_setTheory.IN_APP,
     REWRITE_RULE [pred_setTheory.IN_APP] pred_setTheory.IN_COMPL,
     REWRITE_RULE [pred_setTheory.IN_APP] pred_setTheory.IN_SING,
     byteTheory.set_byte_bit_field_insert]);

Definition jp_vars_def:
  jp_vars = ["x0"; "x1"; "x2"; "x3"; "x4"; "x5"; "x6"; "x7";
    "x8"; "x9"; "x10"; "x11"; "x12"; "x13"; "x14"; "x15"; "x16"]
End

(* J stores each x_i in its own memory word i, so every live-in of the
   join is observed.  fn_eom := SOME 544 makes the context place spills
   above those 17 words. *)
Definition jp_fn_def:
  jp_fn = (mk_raw_function "diamond_spill"
    [<| bb_label := "E"; bb_instructions :=
        MAPi (\i v. mk_inst i PARAM [Lit (n2w i)] [v])
          (["z"] ++ jp_vars ++ ["c"]) ++
        [mk_inst 19 JNZ [Var "c"; Label "A"; Label "B"] []] |>;
     <| bb_label := "A"; bb_instructions :=
        [mk_inst 20 MSTORE [Lit 0w; Var "z"] [];
         mk_inst 21 JMP [Label "J"] []] |>;
     <| bb_label := "B"; bb_instructions :=
        [mk_inst 22 JMP [Label "J"] []] |>;
     <| bb_label := "J"; bb_instructions :=
        MAPi (\i v. mk_inst (23+i) MSTORE [Lit (n2w (32*i)); Var v] []) jp_vars ++
        [mk_inst 40 STOP [] []] |>]) with fn_eom := SOME 544
End

Definition jp_ctx_def:
  jp_ctx = mk_venom_context [jp_fn] (SOME "diamond_spill")
End

(* params: z = 100, x_i = i + 1, c *)
Definition jp_params_def:
  jp_params (c:bytes32) =
    [100w:bytes32] ++ GENLIST (\i. n2w (i + 1)) 17 ++ [c]
End

Definition jp_asm_init_def:
  jp_asm_init below c =
    <| as_stack := REVERSE (jp_params c) ++ below; as_memory := [];
       as_accounts := empty_accounts;
       as_transient := empty_transient_storage; as_returndata := [];
       as_logs := []; as_pc := 0; as_call_ctx := empty_call_context;
       as_tx_ctx := empty_tx_context; as_block_ctx := empty_block_context;
       as_code := []; as_prev_hashes := []; as_outcomes := [];
       as_requests := []; as_pending_deletions := []; as_gas_readings := [] |>
End

(* memory words 0..16 *)
Definition jp_words_def:
  jp_words (m : byte list) =
    GENLIST (\i. w2n (word_of_bytes T (0w:bytes32)
                       (TAKE 32 (DROP (32*i) m ++ REPLICATE 32 0w)))) 17
End

Definition jp_run_def:
  jp_run asm below c =
    case run_asm 1000 asm (jp_asm_init below c) of
      AsmHalt s => ("halt", jp_words s.as_memory, MAP w2n s.as_stack)
    | AsmOK s => ("ok", jp_words s.as_memory, MAP w2n s.as_stack)
    | AsmRevert s => ("revert", jp_words s.as_memory, MAP w2n s.as_stack)
    | AsmFault s => ("fault", jp_words s.as_memory, MAP w2n s.as_stack)
    | AsmError e => ("error: " ++ e, [], [])
End

Definition jp_venom_result_def:
  jp_venom_result c =
    case run_function 10 jp_ctx jp_fn
           ((init_venom_state "E") with vs_params := jp_params c) of
      Halt s => ("halt", jp_words s.vs_memory)
    | OK s => ("ok", jp_words s.vs_memory)
    | Abort _ s => ("abort", jp_words s.vs_memory)
    | IntRet _ s => ("intret", jp_words s.vs_memory)
    | Error e => ("error: " ++ e, [])
End

Theorem jp_release_live = fnPlanLineageReplayTheory.release_dead_spills_live_domain

val pr = fn th => print ("\n" ^ thm_to_string th ^ "\n");
fun timed name f x =
  let val t = Timer.startRealTimer ()
      val r = f x
  in print ("\n[" ^ name ^ ": " ^
       Real.toString (Time.toReal (Timer.checkRealTimer t)) ^ "s]\n"); r end;

(* Spill release now scans the allocator's occupied offset range, so
   kernel evaluation can execute it along with the rest of the planner. *)
val plan_eval =
  computeLib.CBV_CONV
    (computeLib.set_skip (computeLib.the_compset ()) boolSyntax.conditional (SOME 1));

val plan_th = timed "plan" plan_eval ``OPTION_MAP (\cp. (cp.cp_initial_fmp,
                       context_plan_ops cp)) (generate_context_plan jp_ctx)``;
val () = pr plan_th;
val () = if not (optionSyntax.is_some (rhs (concl plan_th)))
         then raise Fail "plan did not evaluate to a concrete SOME" else ();

val asm_th = timed "asm" EVAL ``OPTION_MAP (\(fmp,ops). execute_plan fmp ops)
                    ^(rhs (concl plan_th))``;
val () = pr asm_th;
val asm_tm = rand (rhs (concl asm_th));

(* Each path halts with x_i = i + 1 in memory word i, as the Venom
   interpreter does. *)
fun check name tm expected =
  let val th = timed name EVAL tm
  in pr th;
     if aconv (rhs (concl th)) expected then th
     else raise Fail (name ^ ": unexpected result")
  end;

val expected = ``("halt", GENLIST (\i. i + 1) 17)``;
val expected_th = EVAL expected;
val expected_tm = rhs (concl expected_th);
Theorem jp_venom_c1 = check "venom c=1" ``jp_venom_result 1w`` expected_tm;
Theorem jp_venom_c0 = check "venom c=0" ``jp_venom_result 0w`` expected_tm;

(* the assembly's status and memory words, without its final stack *)
fun asm_check below c =
  check "asm" ``(\r. (FST r, FST (SND r))) (jp_run ^asm_tm ^below ^c)``
    expected_tm;

Theorem jp_asm_c1 = asm_check ``[] : bytes32 list`` ``1w : bytes32``;
Theorem jp_asm_c0 = asm_check ``[] : bytes32 list`` ``0w : bytes32``;
(* with two caller-frame words below the params *)
Theorem jp_asm_c1_frame = asm_check ``[111w; 222w] : bytes32 list`` ``1w : bytes32``;
Theorem jp_asm_c0_frame = asm_check ``[111w; 222w] : bytes32 list`` ``0w : bytes32``;
