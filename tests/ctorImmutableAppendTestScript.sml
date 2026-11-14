(* DynArray append on a constructor immutable reads and writes the length,
   and stores the element, through the immutables buffer (ce_imm_alloca). *)
Theory ctorImmutableAppendTest
Ancestors
  exprLowering exprLoweringProps vyperCompiler venomCallOracleDefs
  venomExecSemantics venomState compileEnv context words list
Libs
  wordsLib

(* The array sits at immutable offset 64, the immutables buffer at memory
   256, and a non-primitive element is staged in memory from 0. *)
Definition ctor_imm_append_run_def:
  ctor_imm_append_run is_prim elem_size len staged =
    let cenv = (ARB:compile_env) with
      <|ce_is_ctor := T; ce_imm_alloca := SOME (Lit 256w)|> in
    let val_op = if is_prim then Lit (HD staged) else Lit 0w in
    let cs = initial_compile_state "entry" in
    let compiled = SND (compile_dynarray_append cenv (Lit 64w) val_op 32
                          elem_size ARB ARB 2 is_prim LocCode cs) in
    let s0 = (init_venom_state "entry") with
      <|vs_memory := REPLICATE 1024 0w|> in
    let s1 = mstore 320 (n2w len) s0 in
    let s2 = FOLDL (\s (i,w). mstore (32 * i) w s) s1
               (ZIP (GENLIST I (LENGTH staged), staged)) in
    run_inst_seq (emitted_insts cs compiled) s2
End

(* A primitive word, a one-word composite (uint256[1]) and a two-word
   element: the element lands at buffer + 64 + 32 + len * elem_size and the
   length word at buffer + 64 is incremented. *)
Theorem ctor_immutable_append_buffer:
  (case ctor_imm_append_run T 32 1 [9w] of
     OK s => mload 320 s = 2w /\ mload 384 s = 9w
   | _ => F) /\
  (case ctor_imm_append_run F 32 1 [5w] of
     OK s => mload 320 s = 2w /\ mload 384 s = 5w
   | _ => F) /\
  (case ctor_imm_append_run F 64 0 [5w; 6w] of
     OK s => mload 320 s = 1w /\ mload 352 s = 5w /\ mload 384 s = 6w
   | _ => F)
Proof
  EVAL_TAC
QED
