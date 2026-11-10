(* Bounded actual-edit test of routed return cuts.  Definitions here are
   proof examples, not alternate executable semantics or input contracts. *)
Theory functionInlinerReturnCuts
Ancestors
  functionInlinerCuts functionInlinerReturnTransport functionInlinerDefs
  callLayoutDefs venomExecSemantics venomState venomInst list finite_map

Definition return_cut_inner_def:
  return_cut_inner fmp = mk_raw_function "inner"
    [<|bb_label := "inner"; bb_instructions :=
      [mk_inst 10 PARAM [Lit 0w] ["arg"]] ++
      (if fmp then [mk_inst 11 FMP_PARAM [Lit 1w] ["fp"]] else []) ++
      [mk_inst 12 RETPC_PARAM [Lit (if fmp then 2w else 1w)] ["pc"];
       mk_inst 13 (if fmp then RETFMP else RET)
         [Var "arg"; Var "pc"] []] |>]
End

Definition return_cut_middle_def:
  return_cut_middle fmp = mk_raw_function "middle"
    [<|bb_label := "middle"; bb_instructions :=
      [mk_inst 20 RETPC_PARAM [Lit 0w] ["mpc"]] ++
      (if fmp then [mk_inst 21 GETFMP [] ["mf"]] else []) ++
      [mk_inst 22 INVOKE
         (if fmp then [Label "inner"; Lit 41w; Var "mf"]
          else [Label "inner"; Lit 41w]) ["answer"];
       mk_inst 23 RET [Var "answer"; Var "mpc"] []] |>]
End

Definition return_cut_outer_def:
  return_cut_outer = mk_raw_function "outer"
    [<|bb_label := "outer"; bb_instructions :=
      [mk_inst 30 INVOKE [Label "middle"] ["result"];
       mk_inst 31 STOP [] []] |>]
End

Definition return_cut_produced_def:
  return_cut_produced fmp =
    let p0 = inline_prefix 0;
        r0 = return_block_label p0 0;
        p1 = inline_prefix 1;
        r1 = return_block_label p1 1;
        mid = renumber_fn_inst_ids (inline_call_site p0 r0
          (return_cut_middle fmp) (return_cut_inner fmp) "middle"
          (if fmp then 2 else 1))
    in renumber_fn_inst_ids
         (inline_call_site p1 r1 return_cut_outer mid "outer" 0)
End

Theorem return_cut_layout:
  !fmp. ?bb.
    lookup_block "inl1_inl0_inner" (return_cut_produced fmp).fn_blocks = SOME bb /\
    get_instruction bb (if fmp then 3 else 2) = SOME
      (mk_inst (if fmp then 10 else 8) ASSIGN
         [Var "inl1_inl0_arg"] ["inl1_answer"]) /\
    get_instruction bb (if fmp then 4 else 3) = SOME
      (mk_inst (if fmp then 11 else 9) JMP
        [Label "inl1_inl0_inline_return0"] []) /\
    LENGTH bb.bb_instructions = (if fmp then 5 else 4)
Proof
  Cases >> EVAL_TAC >> simp[mk_inst_def]
QED
