Theory bodyPtrBytestringBuiltinsTerminalPairProbe
Ancestors bodyPtrBytestringBuiltinsPlaceFrontierProbe
          bodyPtrBytestringBuiltinsImageFrontier

(* Proof-only fixtures for the actual place-retaining operand compiler. *)
Definition terminal_probe_expr_def:
  terminal_probe_expr = Attribute (BaseT (BytesT (Dynamic 1))) place_probe_base "second"
End
Definition terminal_probe_empty_def:
  terminal_probe_empty = TypeBuiltin (BaseT (BytesT (Dynamic 1))) Empty
    (BaseT (BytesT (Dynamic 1))) []
End
Definition terminal_probe_final_def:
  terminal_probe_final = (initial_compile_state "") with
    <|cs_next_var := 3; cs_next_id := 4;
      cs_current_insts := [mk_inst 0 ALLOCA [Lit 32w] ["%0"];
        mk_inst 1 ADD [Var "%0"; Lit 32w] ["%1"];
        mk_inst 2 ALLOCA [Lit 64w] ["%2"];
        mk_inst 3 MSTORE [Var "%2"; Lit 0w] []]|>
End

Theorem terminal_probe_supported:
  supported_program place_probe_tops /\
  supported_pure_exprs place_probe_tops [terminal_probe_expr; terminal_probe_empty]
Proof
  EVAL_TAC
QED

Theorem terminal_probe_compile:
  compile_multi_vvs compile_expr place_probe_env
    [terminal_probe_expr; terminal_probe_empty] (initial_compile_state "") =
  ([LocatedValue (BaseT (BytesT (Dynamic 1))) (mk_ptr (Var "%1") LocMemory);
    LocatedValue (BaseT (BytesT (Dynamic 1)))
      (base_ptr <|buf_operand := Var "%2"; buf_size := 64|>)],
    terminal_probe_final)
Proof
  EVAL_TAC
QED

Theorem terminal_probe_collision:
  image_bad terminal_probe_final.cs_current_insts
Proof
  simp[terminal_probe_final_def, image_bad_def] >>
  qexistsl [`0`, `1`, `2`, `3`, `32w`, `"%0"`, `"%1"`, `"%2"`, `[]`, `[]`] >> simp[]
QED

(* The support grammar does not enforce call arity/type correctness.  Use an
   actual internal-call expression to test the child-list seam, not a hand
   concatenation of fragments.  This is still not an installed-unit witness. *)
Definition terminal_probe_tops_def:
  terminal_probe_tops = place_probe_tops ++
    [FunctionDecl Internal Nonpayable F F "sink" [] [] NoneT []]
End
Definition terminal_probe_call_def:
  terminal_probe_call = Call NoneT (IntCall (NONE,"sink"))
    [terminal_probe_expr; terminal_probe_empty] NONE
End
Definition terminal_probe_env_def:
  terminal_probe_env = place_probe_env with
    <|ce_func_ids := (\s. 0); ce_func_param_types := (\s. []);
      ce_is_ctor := F; ce_func_info := (\s. (0,0,[]));
      ce_func_return_type := (\s. NoneT)|>
End

Theorem terminal_probe_call_supported:
  supported_program terminal_probe_tops /\
  supported_effect_expr terminal_probe_tops terminal_probe_call
Proof
  EVAL_TAC
QED

Theorem terminal_probe_call_prefix:
  TAKE 4 (SND (compile_expr terminal_probe_env NoneT terminal_probe_call
    (initial_compile_state ""))).cs_current_insts =
  terminal_probe_final.cs_current_insts
Proof
  EVAL_TAC
QED
