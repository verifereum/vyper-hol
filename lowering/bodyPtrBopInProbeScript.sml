(* Finite diagnostics for memory-valued membership.  These facts alone do
   not refute the body judgment: its frame and operand premises also matter. *)
Theory bodyPtrBopInProbe
Ancestors
  exprLoweringProps exprLowering vyperTypeSystem vyperValueOperation venomExecSemantics
  venomState venomInst venomMemProps compileEnv context emitHelper words

Theorem string_membership_typing_probe:
  well_typed_binop (BaseT BoolT) In (BaseT (StringT 1))
    (ArrayT (BaseT (StringT 1)) (Fixed 1))
Proof
  simp[well_typed_binop_def]
QED

Theorem string_membership_source_probe:
  evaluate_binop (Unsigned 256) (ArrayTV (BaseTV (StringT 1)) (Fixed 1))
    In (StringV "a") (ArrayV (DynArrayV [StringV "a"])) =
    INL (BoolV T)
Proof
  EVAL_TAC >> simp[w2n_n2w, dimword_def, dimindex_256]
QED

Theorem singleton_membership_codegen_probe:
  compile_list_membership_in needle [elem] st =
    emit_op EQ [needle; elem] st
Proof
  simp[compile_list_membership_in_def]
QED

Theorem distinct_buffers_eq_probe:
  step_inst_base (mk_inst 8 EQ [Lit 64w; Lit 128w] ["result"])
    (init_venom_state "entry") =
  OK (update_var "result" 0w (init_venom_state "entry"))
Proof
  EVAL_TAC >> simp[dimword_def, dimindex_256, bool_to_word_def]
QED

Theorem distinct_allocations_probe:
  exec_alloca (mk_inst 0 ALLOCA [Lit 64w] ["first"])
    ((init_venom_state "entry") with vs_alloca_next := 64) (64w:bytes32) =
  OK (update_var "first" 64w
    ((init_venom_state "entry") with
      <| vs_alloca_next := 128; vs_allocas := FEMPTY |+ (0,(64,64)) |>))
Proof
  EVAL_TAC >> simp[w2n_n2w, dimword_def, dimindex_256]
QED

Theorem string_literal_emission_probe:
  MAP (\i. i.inst_opcode)
    (SND (compile_literal_vv (BaseT (StringT 1)) (StringL "a")
      <| cs_next_var := 0; cs_next_label := 0; cs_next_id := 0;
         cs_current_bb := "entry"; cs_current_insts := [];
         cs_blocks := []; cs_data_sections := [] |>)).cs_current_insts =
  [ALLOCA; MSTORE; ADD; MSTORE]
Proof
  EVAL_TAC >> simp[w2n_n2w, n2w_11, dimword_def, dimindex_256,
                   bool_to_word_def]
QED

Theorem compiled_string_membership_probe:
  (case compile_expr cenv (BaseT BoolT)
     (Builtin (BaseT BoolT) (Bop In)
       [Literal (BaseT (StringT 1)) (StringL "a");
        Builtin (ArrayT (BaseT (StringT 1)) (Fixed 1))
          (MakeArray (SOME (BaseT (StringT 1))) (Fixed 1))
          [Literal (BaseT (StringT 1)) (StringL "a")]])
     <| cs_next_var := 0; cs_next_label := 0; cs_next_id := 0;
        cs_current_bb := "entry"; cs_current_insts := [];
        cs_blocks := []; cs_data_sections := [] |> of
   (vv, st) =>
     case run_inst_seq st.cs_current_insts
        ((init_venom_state "entry") with vs_alloca_next := 64) of
       OK s => eval_operand (vv_operand vv) s = SOME 0w
     | _ => F)
Proof
  EVAL_TAC >> simp[w2n_n2w, n2w_11, dimword_def, dimindex_256,
                   bool_to_word_def]
QED

Theorem string_membership_expression_typing_probe:
  well_typed_expr env
     (Builtin (BaseT BoolT) (Bop In)
       [Literal (BaseT (StringT 1)) (StringL "a");
        Builtin (ArrayT (BaseT (StringT 1)) (Fixed 1))
          (MakeArray (SOME (BaseT (StringT 1))) (Fixed 1))
          [Literal (BaseT (StringT 1)) (StringL "a")]])
Proof
  simp[well_typed_expr_def, well_typed_builtin_app_def,
       well_typed_binop_def] >>
  EVAL_TAC >> simp[dimword_def, dimindex_256] >> EVAL_TAC
QED
