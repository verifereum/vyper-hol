(* Checked rejection of the proposed DALLOCA/FMP counterexample.
   The source contract explicitly excludes DALLOCA. *)
Theory lowerDloadPtrFmpCounterexample
Ancestors
  o1PassContract ptrDiscipline

Theorem dalloca_candidate_excluded:
  !D vs.
  ~o1_src_inv D
    (mk_venom_context
      [mk_raw_function "main"
        [<|bb_label := "main"; bb_instructions :=
          [mk_inst 0 DALLOCA [Lit 0w] ["p"];
           mk_inst 1 DLOAD [Lit 0w] ["x"];
           mk_inst 2 STOP [] []]|>]] (SOME "main")) vs
Proof
  rpt gen_tac >> simp[o1_src_inv_def] >> EVAL_TAC
QED
