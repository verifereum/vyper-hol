Theory bodyPtrBopInLocalSuffix
Ancestors
  exprLowering bodyPtrBopInCompareBoundary finite_map

(* Concrete fixtures keep exact state equations readable; no semantic change. *)
Definition equality_fixture_def:
  equality_fixture = Builtin (BaseT BoolT) (Bop Eq)
    [Literal (BaseT (UintT 256)) (StringL "a");
     Literal (BaseT (UintT 256)) (StringL "b")]
End

Definition local_membership_fixture_def:
  local_membership_fixture = Builtin (BaseT BoolT) (Bop In)
    [Name (BaseT (StringT 1)) "x";
     Builtin (ArrayT (BaseT (StringT 1)) (Fixed 1))
       (MakeArray (SOME (BaseT (StringT 1))) (Fixed 1))
       [Name (BaseT (StringT 1)) "y"]]
End

Definition empty_compile_fixture_def:
  empty_compile_fixture =
    <| cs_next_var := 0; cs_next_label := 0; cs_next_id := 0;
       cs_current_bb := "entry"; cs_current_insts := [];
       cs_blocks := []; cs_data_sections := [] |>
End

Theorem equality_fixture_boundary:
  (case compile_expr cenv (BaseT BoolT) equality_fixture empty_compile_fixture of
   (vv,st) => vv = StackValue (BaseT BoolT) (Var "%6") /\
     st.cs_next_var = 7 /\ st.cs_next_id = 11 /\
     LAST st.cs_current_insts =
       <| inst_id := 10; inst_opcode := EQ;
          inst_operands := [Var "%2"; Var "%5"];
          inst_outputs := ["%6"] |>)
Proof
  EVAL_TAC
QED

Theorem local_membership_exact_suffix:
  (case compile_expr cenv (BaseT BoolT) equality_fixture empty_compile_fixture of
   (vv,st) =>
     compile_expr (cenv with ce_vars := FEMPTY |+
       ("x",PtrVar (Var "%2") 64) |+ ("y",PtrVar (Var "%5") 64))
       (BaseT BoolT) local_membership_fixture
       (st with <| cs_next_var := 6; cs_next_id := 10;
                    cs_current_insts := FRONT st.cs_current_insts |>) = (vv,st))
Proof
  EVAL_TAC
QED

Theorem local_suffix_comparison_rejected:
  FLOOKUP G "%2" = SOME (64,64) /\
  FLOOKUP G "%5" = SOME (128,64) ==>
  (case compile_expr cenv (BaseT BoolT) equality_fixture empty_compile_fixture of
   (vv,st) => ~access_ok lo G fn (LAST st.cs_current_insts) s)
Proof
  strip_tac >>
  mp_tac equality_fixture_boundary >>
  Cases_on `compile_expr cenv (BaseT BoolT) equality_fixture empty_compile_fixture` >>
  simp[] >> strip_tac >>
  irule different_sites_comparison_access_rejected >>
  simp[] >> metis_tac[]
QED
