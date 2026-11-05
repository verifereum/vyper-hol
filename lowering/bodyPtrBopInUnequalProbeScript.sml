(* Local pointer-only candidate diagnostics, not a target counterexample. *)
Theory bodyPtrBopInUnequalProbe
Ancestors
  bodyPtrBopInProbe bodyPtrBopInCompareBoundary ptrDiscipline
  exprLoweringProps exprLowering vyperTypeSystem vyperValueOperation
  venomExecSemantics venomState venomInst venomMemProps compileEnv
  context emitHelper words finite_map

Theorem unequal_string_membership_source:
  evaluate_binop (Unsigned 256) (ArrayTV (BaseTV (StringT 1)) (Fixed 1))
    In (StringV "a") (ArrayV (DynArrayV [StringV "b"])) =
    INL (BoolV F)
Proof
  EVAL_TAC >> simp[w2n_n2w, dimword_def, dimindex_256]
QED

Theorem unequal_string_membership_typed:
  well_typed_expr env
    (Builtin (BaseT BoolT) (Bop In)
      [Literal (BaseT (StringT 1)) (StringL "a");
       Builtin (ArrayT (BaseT (StringT 1)) (Fixed 1))
         (MakeArray (SOME (BaseT (StringT 1))) (Fixed 1))
         [Literal (BaseT (StringT 1)) (StringL "b")]])
Proof
  simp[well_typed_expr_def, well_typed_builtin_app_def,
       well_typed_binop_def] >>
  EVAL_TAC >> simp[dimword_def, dimindex_256] >> EVAL_TAC
QED

Theorem unequal_string_membership_compiled:
  (case compile_expr cenv (BaseT BoolT)
    (Builtin (BaseT BoolT) (Bop In)
      [Literal (BaseT (StringT 1)) (StringL "a");
       Builtin (ArrayT (BaseT (StringT 1)) (Fixed 1))
         (MakeArray (SOME (BaseT (StringT 1))) (Fixed 1))
         [Literal (BaseT (StringT 1)) (StringL "b")]])
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

Theorem unequal_string_membership_eq_sites:
  (case compile_expr cenv (BaseT BoolT)
    (Builtin (BaseT BoolT) (Bop In)
      [Literal (BaseT (StringT 1)) (StringL "a");
       Builtin (ArrayT (BaseT (StringT 1)) (Fixed 1))
         (MakeArray (SOME (BaseT (StringT 1))) (Fixed 1))
         [Literal (BaseT (StringT 1)) (StringL "b")]])
    <| cs_next_var := 0; cs_next_label := 0; cs_next_id := 0;
       cs_current_bb := "entry"; cs_current_insts := [];
       cs_blocks := []; cs_data_sections := [] |> of
   (vv, st) =>
     case FOLDL (\(s,G) i.
         case step_inst_base i s of
           OK t => (t, step_prov [] G i t)
         | _ => (s,G))
       (((init_venom_state "entry") with vs_alloca_next := 64), FEMPTY)
       (FRONT st.cs_current_insts) of
     (s,G) =>
       ?u w. (LAST st.cs_current_insts).inst_opcode = EQ /\
         (LAST st.cs_current_insts).inst_operands = [Var u; Var w] /\
         FLOOKUP G u = SOME (64,64) /\
         FLOOKUP G w = SOME (128,64) /\
         FLOOKUP s.vs_allocas 0 = SOME (64,64) /\
         FLOOKUP s.vs_allocas 4 = SOME (128,64) /\
         ~access_ok 0 G fn (LAST st.cs_current_insts) s)
Proof
  EVAL_TAC >> simp[w2n_n2w, n2w_11, dimword_def, dimindex_256,
                   bool_to_word_def, FLOOKUP_UPDATE, FLOOKUP_DRESTRICT]
QED
