(* Concrete generated-code diagnostic. No stand-in instruction stream. *)
Theory bodyPtrMakeArrayConcreteReturn
Ancestors
  bodyPtrMakeArrayForwardLayoutProbe compileVyper moduleLowering vyperCompiler
  ptrSafeRun integer_word bodyPtrMakeArrayTaintNormalize ptrDiscipline
Libs finite_mapLib wordsLib intLib

val () = computeLib.upd_compset add_finite_map_compset
val B32 = ``BaseT (BytesT (Dynamic 32))``
val B64 = ``BaseT (BytesT (Dynamic 64))``
val N = ``TupleT [^B32; ^B32]``
val W = ``TupleT [^B64; ^B32]``
val emptyN = ``Builtin ^N (MakeArray NONE (Fixed 2))
  [Literal ^B32 (BytesL []); Literal ^B32 (BytesL [])]``
val callW = ``Call ^W (IntCall (NONE,"empty_narrow")) [] NONE``
val tops = ``[
  FunctionDecl Internal Pure F F "empty_narrow" [] ([] : expr list) ^N
    [Return (SOME ^emptyN)];
  FunctionDecl External Pure F F "read_empty" [] ([] : expr list) ^W
    [Return (SOME ^callW)]]``
val ipkg = ``package_internal_fn ^tops F (assign_nkeys ^tops 0) F 0
  (Pure,F,F,"empty_narrow",[],([] : expr list),^N,
   [Return (SOME ^emptyN)])``

val cs = ``SND (compile_internal_fn_bodies [^ipkg]
    (initial_compile_state "__entry"))``

Theorem concrete_internal_opcodes:
  MAP (\i. i.inst_opcode) (^cs).cs_current_insts =
  [PARAM; RETPC_PARAM; ALLOCA; ALLOCA; MSTORE; ADD; MLOAD; ADD;
   AND; ADD; MCOPY; ALLOCA; MSTORE; ADD; MLOAD; ADD; AND; ADD;
   MCOPY; MCOPY; RET]
Proof
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``function_selector``])
QED

Theorem concrete_internal_label:
  (^cs).cs_current_bb = "internal 0 empty_narrow()_runtime"
Proof
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``function_selector``])
QED

val extracted = ``extract_context_with_internals "__entry" [^ipkg] ^cs``
val ctx = ``FST (THE ^extracted)``
val callee = ``THE (lookup_function "internal 0 empty_narrow()_runtime"
  (^ctx).ctx_functions)``

Theorem concrete_internal_selected:
  IS_SOME ^extracted /\
  IS_SOME (lookup_function "internal 0 empty_narrow()_runtime"
    (^ctx).ctx_functions) /\
  LENGTH (^callee).fn_blocks = 1 /\
  LENGTH (HD (^callee).fn_blocks).bb_instructions = 21
Proof
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``function_selector``])
QED

val caller = ``(init_venom_state "__entry") with vs_fmp := 1024w``
val start = ``THE (setup_callee ^callee [256w; 7w] ^caller)``

Theorem concrete_internal_setup:
  IS_SOME (setup_callee ^callee [256w; 7w] ^caller) /\
  (^start).vs_fmp = 1024w /\ (^start).vs_return_pc_token = 7w
Proof
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``function_selector``])
QED

Theorem concrete_internal_run:
  ?s. run_blocks 30 ^ctx ^callee ^start =
    IntRet <| iret_values := []; iret_adopt_fmp := NONE |> s /\
    TAKE 128 (DROP 256 s.vs_memory) = REPLICATE 128 0w
Proof
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``function_selector``, ``run_blocks``]) >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``function_selector``]) >>
  simp_tac bool_ss [] >> EVAL_TAC
QED

(* Ghost header replay is not yet proved. The attempted symbolic-taint
   replay expands repeated new_site_bytes quantifiers; see C1.10 evidence.
   This run does not establish body_inv, ghost_inv, gas_path_ptr, or the
   full lowered runtime context (only the generated internal segment and
   its packaging). It is not a target counterexample or proof. *)

(* A bounded replay retaining mem_taint and new_site_bytes opaque still
   duplicates entire operational states through nested taint records before
   normalization can act. This measurement remains inconclusive; no header
   cleanliness claim follows from the successful operational return. *)
