(* Bounded reentry probe: literal endpoint calculation. This does not assert
   that a containing function or its continuation is pointer-safe. *)
Theory bodyPtrWordBuiltinsReentryProbe
Ancestors exprLowering moduleLowering compileEnv vyperCompiler venomInst gasCount list bodyPtrWordBuiltinsFirstHit
Libs finite_mapLib intReduce

val () = computeLib.upd_compset add_finite_map_compset
val () = computeLib.upd_compset intReduce.add_int_compset

Theorem word_literal_completion:
  lower_value compile_expr cenv ty (Literal ety (IntL n)) sa =
    (Lit (i2w n), sa)
Proof
  simp[lower_value_def, Once compile_expr_def, compile_literal_vv_def,
       unwrap_value_def, comp_bind_def, comp_return_def]
QED

(* Concrete abbreviations keep finite compilation and path tests readable. *)
Definition word_reentry_body_def:
  word_reentry_body =
    [For "i" (BaseT (UintT 256))
      (Range (Literal (BaseT (UintT 256)) (IntL 0))
             (Literal (BaseT (UintT 256)) (IntL 2))) 2
      [Expr (Literal (BaseT (UintT 256)) (IntL 7))]]
End

Definition word_reentry_env_def:
  word_reentry_env = build_compile_env [] External Nonpayable "foo" [] NoneT
    word_reentry_body F
End

Definition word_reentry_final_def:
  word_reentry_final = SND
    (compile_external_function_body word_reentry_env [] F 0 F F
      word_reentry_body NONE (initial_compile_state "entry"))
End

Theorem word_reentry_compiled_opcodes:
  MAP (\i. i.inst_opcode)
    (FLAT (MAP (\b. b.bb_instructions) word_reentry_final.cs_blocks)) =
  [ADD; ASSIGN; JMP; MSTORE; JMP; EQ; JNZ; ASSIGN; ADD; JMP; ALLOCA; JMP]
Proof
  EVAL_TAC
QED

Theorem word_reentry_non_gas:
  !inst. MEM inst
    (FLAT (MAP (\b. b.bb_instructions) word_reentry_final.cs_blocks)) ==>
    inst.inst_opcode <> GAS /\ inst.inst_opcode <> INVOKE
Proof
  rpt strip_tac >>
  `MEM inst.inst_opcode
    [ADD; ASSIGN; JMP; MSTORE; JMP; EQ; JNZ; ASSIGN; ADD; JMP; ALLOCA; JMP]` by
    (rewrite_tac[GSYM word_reentry_compiled_opcodes] >>
     simp[MEM_MAP] >> metis_tac[]) >> gvs[]
QED

(* The path index counts GAS observations, not instruction transitions. *)
Theorem word_reentry_zero_counts:
  MEM inst (FLAT (MAP (\b. b.bb_instructions) word_reentry_final.cs_blocks)) ==>
  gas_count_step fuel ctx inst s = 0
Proof
  strip_tac >> drule word_reentry_non_gas >>
  simp[gas_count_step_def]
QED
