Theory bodySimAugPlaceComputationProbe
Ancestors
  vyperTypeSystem vyperTyping vyperInterpreter vyperState vyperStorage vyperValue vyperAST
  finite_map words compileEnv vyperCompiler stmtLowering venomExecSemantics venomState vfmState
Libs
  wordsLib intLib

Definition aug_place_compute_inner_ty_def:
  aug_place_compute_inner_ty = ArrayT (ArrayT (BaseT (UintT 256)) (Fixed 1)) (Dynamic 1)
End
Definition aug_place_compute_ty_def:
  aug_place_compute_ty = ArrayT aug_place_compute_inner_ty (Dynamic 1)
End
Definition aug_place_compute_rhs_def:
  aug_place_compute_rhs = Builtin aug_place_compute_ty
    (MakeArray (SOME aug_place_compute_inner_ty) (Dynamic 1))
    [Builtin aug_place_compute_inner_ty
      (MakeArray (SOME (ArrayT (BaseT (UintT 256)) (Fixed 1))) (Dynamic 1)) []]
End
Definition aug_place_compute_body_def:
  aug_place_compute_body =
    [Assign (BaseTarget (TopLevelNameTarget (NONE,"outer"))) aug_place_compute_rhs;
     Return (SOME (Literal (BaseT (UintT 256)) (IntL 0)))]
End
Definition aug_place_compute_tops_def:
  aug_place_compute_tops =
    [VariableDecl Private Storage "outer" aug_place_compute_ty (SOME 0);
     FunctionDecl Internal Nonpayable F F "key" [] [] (BaseT (UintT 256))
       aug_place_compute_body]
End
Definition aug_place_compute_env_def:
  aug_place_compute_env = <|
    current_src := NONE; var_types := FEMPTY; var_assignable := FEMPTY;
    bare_globals := FEMPTY; bare_global_assignable := FEMPTY;
    toplevel_vtypes := FEMPTY |+ ((NONE,"outer"),Type aug_place_compute_ty);
    type_defs := type_env aug_place_compute_tops;
    fn_sigs := FEMPTY |+ ((NONE,"key"),
      <|param_types := []; num_defaults := 0; ret_ty := BaseT (UintT 256)|>);
    flag_members := FEMPTY |>
End
Theorem aug_place_compute_typed:
  IS_SOME (type_stmts aug_place_compute_env (BaseT (UintT 256)) aug_place_compute_body)
Proof
  EVAL_TAC >> simp[wordsTheory.dimword_def, type_slot_size_def]
QED

Definition aug_place_compute_cenv_def:
  aug_place_compute_cenv = <|
    ce_target := all_capabilities;
    ce_vars := FEMPTY;
    ce_module_vars := FEMPTY |+ ((NONE,"outer"),StorageLoc 0w);
    ce_storage_layout := FEMPTY; ce_module := NONE;
    ce_struct_fields := FEMPTY;
    ce_dynarray_capacity := K 0;
    ce_module_dynarray_capacity := (\n. if n = (NONE,"outer") then 1 else 0);
    ce_method_id := (\n ts. 0); ce_flag_member_id := (\n m. 0);
    ce_flag_n_members := K 0; ce_var_type := K NONE;
    ce_module_var_type := (\n. if n = (NONE,"outer") then SOME aug_place_compute_ty else NONE);
    ce_hashmap_info := K NONE; ce_event_info := K NONE;
    ce_type_env := type_env aug_place_compute_tops;
    ce_returns_count := 1; ce_return_buf := NONE; ce_return_pc := NONE;
    ce_ctor_exit_label := NONE; ce_is_external := F;
    ce_ret_enc_info := AbiPrimWord; ce_ret_dec_info := DecPrimWord NoClamp;
    ce_max_return_size := 32; ce_is_ctor := F; ce_imm_alloca := NONE;
    ce_func_info := K (0,0,[]); ce_func_param_types := K [];
    ce_func_ids := K 0; ce_nonreentrant := (F,0,F,F);
    ce_raw_return := F; ce_alloca_locals := T |>
End
Definition aug_place_compute_lowered_def:
  aug_place_compute_lowered = SND (compile_stmt aug_place_compute_cenv NoLoop
    (BaseT (UintT 256)) (HD aug_place_compute_body) (initial_compile_state "entry"))
End
Theorem aug_place_compute_copy_selected:
  MAP (\i. i.inst_opcode)
    (EL 1 aug_place_compute_lowered.cs_blocks).bb_instructions =
    [MUL; ADD; MLOAD; ADD; SSTORE; ADD; ASSIGN; JMP] /\
  MAP (\i. i.inst_opcode)
    (EL 5 aug_place_compute_lowered.cs_blocks).bb_instructions =
    [ALLOCA; MSTORE; ALLOCA; MSTORE; ADD; MCOPY; MLOAD; ASSIGN; JMP]
Proof
  EVAL_TAC
QED

Definition aug_place_compute_cx_def:
  aug_place_compute_cx = empty_evaluation_context with
    <| stk := [(NONE,"caller")];
       sources := [(0w,[(NONE,aug_place_compute_tops)])];
       layouts := [(0w,([((NONE,"outer"),0)],[]))] |>
End
Definition aug_place_compute_initial_def:
  aug_place_compute_initial = empty_state with accounts :=
    (0w =+ (empty_account_state with storage :=
       (0w =+ 1w) ((1w =+ 1w) ((2w =+ 7w) (K 0w))))) empty_accounts
End
Definition aug_place_compute_target_def:
  aug_place_compute_target = SubscriptTarget
    (SubscriptTarget
      (SubscriptTarget (TopLevelNameTarget (NONE,"outer"))
        (Literal (BaseT (UintT 256)) (IntL 0)))
      (Literal (BaseT (UintT 256)) (IntL 0)))
    (Call (BaseT (UintT 256)) (IntCall (NONE,"key")) [] NONE)
End
Theorem aug_place_compute_source_capture:
  let (r,s) = eval_target_place aug_place_compute_cx aug_place_compute_target
                aug_place_compute_initial in
    r = INL (StoragePlace F 2w (BaseTV (UintT 256))) /\
    get_storage aug_place_compute_cx s F 0w = 1w /\
    get_storage aug_place_compute_cx s F 1w = 0w /\
    read_place aug_place_compute_cx (StoragePlace F 2w (BaseTV (UintT 256))) s =
      (INL (IntV 7),s)
Proof
  EVAL_TAC >> simp[wordsTheory.dimword_def, type_slot_size_def] >>
  EVAL_TAC >> simp[] >> EVAL_TAC >> simp[] >> EVAL_TAC >>
  simp[wordsTheory.dimword_def, wordsTheory.WORD_ADD_0, return_def] >>
  EVAL_TAC >> simp[wordsTheory.dimword_def, return_def] >> EVAL_TAC >>
  simp[wordsTheory.dimword_def] >> EVAL_TAC >>
  simp[wordsTheory.word_add_n2w, wordsTheory.dimword_def]
QED

Definition aug_place_compute_fn_def:
  aug_place_compute_fn = mk_raw_function "probe"
    (<| bb_label := aug_place_compute_lowered.cs_current_bb;
        bb_instructions := aug_place_compute_lowered.cs_current_insts ++
          [<|inst_id := 34; inst_opcode := STOP; inst_operands := []; inst_outputs := []|>] |>
      :: aug_place_compute_lowered.cs_blocks)
End
Definition aug_place_compute_backend_def:
  aug_place_compute_backend = (ARB:venom_state) with
    <| vs_memory := []; vs_vars := FEMPTY; vs_allocas := FEMPTY;
       vs_alloca_next := 0; vs_current_bb := "entry"; vs_inst_idx := 0;
       vs_halted := F; vs_prev_bb := NONE;
       vs_accounts := aug_place_compute_initial.accounts;
       vs_call_ctx := (ARB:call_context) with cc_address := 0w |>
End
Theorem aug_place_compute_backend_copy:
  case run_blocks 20 ARB aug_place_compute_fn aug_place_compute_backend of
    Halt s => sload 0w s = 1w /\ sload 1w s = 0w /\ sload 2w s = 0w
  | _ => F
Proof
  EVAL_TAC >> simp[wordsTheory.dimword_def] >> EVAL_TAC >> simp[]
QED

(* PREMISE/OBSERVATION AUDIT (body_augassign_place, C1.2.6.4).
   This ledger is a bounded interface diagnostic, NOT a counterexample.
   Abbreviations used only in this comment:
     C = aug_place_compute_cx, T = aug_place_compute_target,
     S = aug_place_compute_initial, P = aug_place_compute_tops,
     E = aug_place_compute_env, CE = aug_place_compute_cenv,
     U = BaseT (UintT 256), Z = Literal U (IntL 0),
     K = Call U (IntCall (NONE,"key")) [] NONE,
     B = SubscriptTarget (SubscriptTarget
           (TopLevelNameTarget (NONE,"outer")) Z) Z,
     A = AugAssign U T bop e.
   bop and e have NOT yet been fixed by the arithmetic probe.

   Checked computations already in THIS theory:
     aug_place_compute_typed: type_stmts of the callee body is SOME.
     aug_place_compute_source_capture: T succeeds and its captured word
       reads IntV 7 after the key call; outer/inner lengths are 1/0.
     aug_place_compute_backend_copy: the compiled replacement assignment,
       executed as a raw function, leaves words 0/1/2 equal to 1/0/0.
   None of these is a statement or expression simulation judgment.

   Frozen premise ledger (all unmarked propositions are RESIDUAL):
   1. !s'' p t' s3 cur t'' s4 ptv t3.
        eval_target_place C T s'' = (INL p,t') /\
        read_place C p s3 = (INL cur,t'') /\
        place_type_value C p s4 = (INL ptv,t3) ==> body_expr_ok C e.
      Its states are independently quantified, not a sequencing invariant.
      Source_capture supplies target/read successes but does not prove
      body_expr_ok C e. A success of place_type_value is still needed to
      use this implication at the concrete state.
   2. body_base_target_ok C T. By body_base_target_ok_def this is exactly
        ((?s pv s1. eval_base_place C
            (TopLevelNameTarget (NONE,"outer")) s = (INL pv,s1)) ==>
           body_expr_ok C Z) /\
        ((?s pv s1. eval_base_place C
            (SubscriptTarget (TopLevelNameTarget (NONE,"outer")) Z) s =
            (INL pv,s1)) ==> body_expr_ok C Z) /\
        ((?s pv s1. eval_base_place C B s = (INL pv,s1)) ==>
           body_expr_ok C K).
      Crucially the last clause is SEMANTIC, not syntactic support.
      Each body_expr_ok C q means (bodySimScript.sml:159-164)
        !tops ctx func cenv env ty es.
          body_inv tops ctx cenv C /\ expr_body_pre cenv C env q es ==>
          expr_sim ctx func cenv C ty q es /\
          expr_vv_sim ctx func cenv C ty q es.
      Thus arbitrary functions and types, not just the explicit raw probe
      function, are quantified. expr_body_pre (exprSimHyps:406-415) asks
      expr_sim_inv, well_typed_expr, byte_widths_expr, alloc_limits_expr,
      call_evaluation_safe, no EVM-run expression, and EVERY internal call
      to be in module NONE of a supported program visible in C.
      No exclusion or satisfaction of this universal predicate is proved.
   3. body_inv P ctx cenv C. Exact remaining code/environment boundary:
        supported_program P /\
        (?rpolicy unit. lower_vyper_runtime_unit P rpolicy = SOME unit /\
          ctx = unit.cu_context /\ cenv.ce_target = rpolicy.rpol_target) /\
        get_module_code C NONE = SOME P /\
        cenv.ce_func_ids = build_func_ids 0 P /\
        cenv.ce_func_param_types = build_func_param_types P /\
        cenv.ce_event_info = build_event_info (type_env P) P (K NONE) /\
        ~cenv.ce_is_ctor /\ cenv.ce_alloca_locals /\
        ALL_DISTINCT (FLAT (MAP (toplevel_vtype_keys_toplevel NONE) P)) /\
        cenv.ce_hashmap_info = build_hashmap_info P /\
        cenv.ce_module_dynarray_capacity =
          build_dynarray_capacity (collect_module_vars P) /\
        (!id. cenv.ce_module_var_type (NONE,id) =
          build_var_type_map P (NONE,id)).
      CE is an explicit record, not a verified build_compile_env instance.
      Its function key id 0 is not by itself an exclusion: build_func_ids
      counts FUNCTION declarations, and key is the first function in P.
      No runtime unit, policy, or context equality has been supplied.
   4. supported_stmt P bindings A. RESIDUAL for this nested fixture.
      The older aug_place_probe_supported theorem in StorageProbe concerns
      a DIFFERENT, one-level-smaller program; it cannot discharge this.
   5. expr_sim_inv cenv C env S. RESIDUAL: includes env_consistent,
      state/accounts/context/functions typing, outcomes SOME and typed,
      storage well-formedness, layout safety, oracle_storage_ok, and map/
      pointer metadata agreements (exprSimHypsScript.sml:289 onwards).
      aug_place_compute_typed proves only callee type_stmts, NOT this.
   6. ce_locals_declared cenv env. For CE, ce_vars = FEMPTY makes this
      definition trivially true, but no complete related instance exists.
   7. locals_alloc_ok cenv env. For E, var_types = FEMPTY makes this
      definition trivially true; this does not establish expr_sim_inv.
   8. type_stmt env ret_ty A = SOME env'. RESIDUAL; the checked typing
      theorem is about the callee body, not this augmented statement.
   9. stmt_exprs_ok cenv A. RESIDUAL: all keys AND RHS need byte widths/
      allocation bounds, together with alloc_limits_stmt.
   10. call_evaluation_safe C (int_calls_stmt A). RESIDUAL; its exact
       interface (vyperTypeCallStackSoundnessScript.sml:302-310) is
         ?edges owner ancestors.
           C.stk = owner::ancestors /\
           call_stack_follows (call_edge_rel edges) C.stk /\
           irreflexive (TC (call_edge_rel edges)) /\
           functions_follow_call_graph edges C /\
           calls_follow_call_graph edges owner (int_calls_stmt A).
       C.stk = [(NONE,"caller")]; no checked graph witness is provided.
   11. frame_ret_ok ctx func C RetQ cenv ret_ty. RESIDUAL universal
       return-statement simulation over same_frame environments. The
       target statement has no return, but this premise is NOT omitted.
   12. eval_stmt C A S = (res,es'). RESIDUAL until bop/e are selected.
       Successful target/read alone do not fix binop/store or res.
   13. (?bt fld. T = AttributeTarget bt fld) \/
       (?bt k. T = SubscriptTarget bt k). Holds by T's definition.

   Required observation (stmtSimScript.sml:191-215): to refute stmt_frag
   one must exhibit sa,sb,s0,cenv' with stmt_env execution, fn_has_code,
   distinct instruction ids, local_ptrs_reserved, ret_pc_ok, nonterminated
   sa, stmt_res_ok, stmt_state_rel, nonhalted s0 and matching entry PC.
   Then BOTH of the following alternatives must be impossible:
     (i) some nonhalted s landing at sb (normal result), or the loop
         control label (break/continue), with cenv_top_ext, final
         stmt_state_rel, old-variable/alloca preservation, and the
         run_from suffix-to-prefix property;
     (ii) some fuel,r with run_from fuel ctx func s0 = r,
          exit_result r and stmt_exit RetQ es' res r.
   For res = INR (Error (RuntimeError m)), stmt_lands is false (no
   normal/break/continue outcome), and stmt_exit permits ANY Abort a s,
   not only a particular revert payload (exprSimScript.sml:102-107).
   For res = INL (), stmt_exit is false, but alternative (i) still needs
   to be ruled out. A dead-only word mismatch does not rule it out.
   In particular run_blocks of aug_place_compute_fn proves neither
   run_from in a body_inv runtime context nor a complete target-call
   prefix, and its STOP is a diagnostic harness, not a compiled A exit.

   Classification: no definition-backed exclusion established; no full
   premise satisfiability or negation of stmt_frag established. The next
   arithmetic probe may test an observable discrepancy, but must retain
   these semantic/universal/runtime-unit residuals explicitly.
*)

(* Bounded arithmetic observation, not a full simulation counterexample. *)
Theorem aug_place_compute_add_overflows:
  evaluate_binop (Unsigned 256) (BaseTV (UintT 256)) Add
    (IntV 7) (IntV (&(2 ** 256) - 1)) =
    INR (RuntimeError "bounded_int_op bound") /\
  evaluate_binop (Unsigned 256) (BaseTV (UintT 256)) Add
    (IntV 0) (IntV (&(2 ** 256) - 1)) =
    INL (IntV (&(2 ** 256) - 1))
Proof
  EVAL_TAC
QED

Definition aug_place_compute_max_rhs_def:
  aug_place_compute_max_rhs =
    Literal (BaseT (UintT 256)) (IntL (&(2 ** 256) - 1))
End

Theorem aug_place_compute_source_aug_overflow:
  FST (eval_stmt aug_place_compute_cx
    (AugAssign (BaseT (UintT 256)) aug_place_compute_target Add
      aug_place_compute_max_rhs) aug_place_compute_initial) =
    INR (Error (RuntimeError "bounded_int_op bound"))
Proof
  EVAL_TAC >> simp[wordsTheory.dimword_def, type_slot_size_def] >>
  EVAL_TAC >> simp[] >> EVAL_TAC >> simp[] >> EVAL_TAC >>
  simp[wordsTheory.dimword_def, wordsTheory.WORD_ADD_0, return_def] >>
  EVAL_TAC >> simp[wordsTheory.dimword_def, return_def] >> EVAL_TAC >>
  simp[wordsTheory.dimword_def] >> EVAL_TAC >>
  simp[wordsTheory.word_add_n2w, wordsTheory.dimword_def]
QED

Definition aug_place_compute_suffix_lowered_def:
  aug_place_compute_suffix_lowered = SND
    (compile_stmt aug_place_compute_cenv NoLoop (BaseT (UintT 256))
      (AugAssign (BaseT (UintT 256))
        (TopLevelNameTarget (NONE,"outer")) Add aug_place_compute_max_rhs)
      (initial_compile_state "entry"))
End

(* This isolates the SAME emitted load/add/store sequence at storage slot
   zero; the captured-place prefix is deliberately not claimed here. *)
Definition aug_place_compute_suffix_fn_def:
  aug_place_compute_suffix_fn = mk_raw_function "suffix"
    (<|bb_label := aug_place_compute_suffix_lowered.cs_current_bb;
       bb_instructions := aug_place_compute_suffix_lowered.cs_current_insts ++
         [<|inst_id := 100; inst_opcode := STOP; inst_operands := []; inst_outputs := []|>] |>
     :: aug_place_compute_suffix_lowered.cs_blocks)
End

Theorem aug_place_compute_suffix_zero:
  case run_blocks 5 ARB aug_place_compute_suffix_fn
    (aug_place_compute_backend with vs_accounts :=
      (0w =+ empty_account_state) empty_accounts) of
    Halt s => sload 0w s = n2w (2 ** 256 - 1)
  | _ => F
Proof
  EVAL_TAC >> simp[wordsTheory.dimword_def] >> EVAL_TAC >> simp[]
QED

Theorem aug_place_compute_suffix_seven:
  case run_blocks 5 ARB aug_place_compute_suffix_fn
    (aug_place_compute_backend with vs_accounts :=
      (0w =+ (empty_account_state with storage :=
        (0w =+ 7w) (K 0w))) empty_accounts) of
    Abort a s => a = Revert_abort
  | _ => F
Proof
  EVAL_TAC >> simp[wordsTheory.dimword_def] >> EVAL_TAC >> simp[]
QED

Theorem aug_place_compute_suffix_opcodes:
  MAP (\i. i.inst_opcode) aug_place_compute_suffix_lowered.cs_current_insts =
    [SLOAD; ADD; LT; ISZERO; ASSERT; SSTORE] /\
  aug_place_compute_suffix_lowered.cs_blocks = []
Proof
  EVAL_TAC
QED

(* Observation boundary: source_aug_overflow checks the entire SOURCE
   AugAssign, including its effectful target evaluation. suffix_zero and
   suffix_seven check emitted backend load/add/store at a supplied slot;
   the raw function's final STOP witnesses continuation after the store.
   The root's declared array type is not a claim of source well-typedness
   for this suffix-only harness. stmtLowering uses the AugAssign U annotation
   for arithmetic and the root only for its pointer/location here.

   The source result is RuntimeError, for which stmt_lands is false and
   stmt_exit accepts any Abort. The zero-word suffix Halts instead of
   Aborting; the seven-word suffix Aborts with Revert_abort as expected.
   This is an observable diagnostic stronger than dead-word inequality,
   but NOT a counterexample to the frozen theorem: there is no checked
   whole compiled effectful target prefix linked to this suffix, no actual
   body_inv runtime-unit/context, no complete entry stmt_state_rel, and
   no discharge of the universal key body_expr_ok, frame_ret_ok or other
   ledger residuals above. In particular finite run_blocks followed by
   an artificial STOP does not yet exclude every run_from Abort outcome
   of the whole statement in the required runtime context.
*)
