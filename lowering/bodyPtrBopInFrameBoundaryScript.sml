Theory bodyPtrBopInFrameBoundary
Ancestors
  bodyPtrBopInLocalSuffix bodyPtrBopInBoundary venomWf fragExec

(* This fixture only packages the computed list in one containing block.
   It deliberately asserts no membership in any lowered context. *)
Definition equality_containing_function_def:
  equality_containing_function cenv fn = fn with fn_blocks :=
    [<| bb_label := "entry";
        bb_instructions :=
          (SND (compile_expr cenv (BaseT BoolT) equality_fixture
                  empty_compile_fixture)).cs_current_insts |>]
End

Theorem equality_containing_function_has_code:
  (case compile_expr cenv (BaseT BoolT) equality_fixture empty_compile_fixture of
   (vv,st) =>
     fn_has_code
       (st with <| cs_next_var := 6; cs_next_id := 10;
                    cs_current_insts := FRONT st.cs_current_insts |>)
       st (equality_containing_function cenv fn))
Proof
  `(SND (compile_expr cenv (BaseT BoolT) equality_fixture
     empty_compile_fixture)).cs_current_bb = "entry" /\
   (SND (compile_expr cenv (BaseT BoolT) equality_fixture
     empty_compile_fixture)).cs_blocks = []` by EVAL_TAC >>
  Cases_on `compile_expr cenv (BaseT BoolT) equality_fixture empty_compile_fixture` >>
  gvs[equality_containing_function_def, fn_has_code_def,
      emitted_blocks_def, venomInstTheory.lookup_block_def, listTheory.FIND_def, listTheory.INDEX_FIND_def]
QED

Theorem equality_containing_function_distinct_ids:
  fn_inst_ids_distinct (equality_containing_function cenv fn)
Proof
  EVAL_TAC >> simp[]
QED
