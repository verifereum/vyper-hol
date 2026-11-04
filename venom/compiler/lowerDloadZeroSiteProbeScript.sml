(* Checked probes for allocation-site aliasing across DLOAD expansion. *)
Theory lowerDloadZeroSiteProbe
Ancestors
  o1ContractLowerDload ptrDiscipline unitMemInv lowerDloadDefs
  venomExecSemantics irSupply list venomInst venomState
  contextCodegenRel unitTransformDefs memLocDefs codegenRel
  venomWf unitShapeDefs

Theorem zero_site_prefix_comparison:
  let ins = [mk_inst 0 ALLOCA [Lit 0w] ["p"];
             mk_inst 1 DLOAD [Lit 0w] ["x"];
             mk_inst 2 ALLOCA [Lit 0w] ["q"];
             mk_inst 3 EQ [Var "p"; Var "q"] ["e"]] in
  let s = (init_venom_state "entry") with
            vs_labels := FEMPTY |+ ("code_end",0w) in
  let supply = <| irs_next_inst := 4; irs_next_var := 0;
                  irs_next_label := 0; irs_used_inst_ids := [0;1;2;3];
                  irs_used_vars := ["p";"x";"q";"e"];
                  irs_used_labels := ["entry";"code_end"] |> in
  let run = \xs. FOLDL (\r i. case r of OK st => step_inst_base i st
                                             | _ => r) (OK s) xs in
  (case run ins of OK st =>
      (lookup_var "p" st, lookup_var "q" st, lookup_var "e" st)
    | _ => (NONE,NONE,NONE)) = (SOME 0w,SOME 0w,SOME 1w) /\
  (case run (FST (lower_dload_insts_supply supply ins)) of OK st =>
      (lookup_var "p" st, lookup_var "q" st, lookup_var "e" st)
    | _ => (NONE,NONE,NONE)) = (SOME 0w,SOME 32w,SOME 0w)
Proof
  `dimindex (:256) = 256` by CONV_TAC fcpLib.INDEX_CONV >>
  EVAL_TAC >> simp[bool_to_word_def, wordsTheory.dimword_def]
QED

Theorem zero_site_comparison_admissible:
  let eqi = mk_inst 3 EQ [Var "p"; Var "q"] ["e"] in
  let G = FEMPTY |+ ("p",(0,0)) |+ ("q",(0,0)) in
  let s = update_var "q" 0w (update_var "p" 0w
            (init_venom_state "entry")) in
  access_ok 0 G fn eqi s /\ ptr_use_ok P {"p";"q"} eqi /\
  raw_mem_ok ctx fn eqi s
Proof
  simp[access_ok_def, ptr_use_ok_def, raw_mem_ok_def,
       mk_inst_def, update_var_def, init_venom_state_def,
       eval_operand_def, lookup_var_def, source_memory_read_ranges_def,
       source_memory_write_ranges_def, inst_mem_ok_in_fn_def,
       mem_read_ops_def, mem_write_ops_def, inst_mem_below_frontier_def,
       wordsTheory.dimword_def] >>
  EVAL_TAC >> simp[]
QED

Theorem zero_site_prefix_syntax:
  EVERY (\i. inst_wf i /\ inst_shape_ok i /\
             ptr_use_ok P {"p";"q"} i)
    [mk_inst 0 ALLOCA [Lit 0w] ["p"];
     mk_inst 1 DLOAD [Lit 0w] ["x"];
     mk_inst 2 ALLOCA [Lit 0w] ["q"];
     mk_inst 3 EQ [Var "p"; Var "q"] ["e"]]
Proof
  EVAL_TAC >> simp[ptr_use_ok_def, inst_wf_def, inst_shape_ok_def,
                  label_positions_ok_def, is_read0_opcode_def]
QED

Theorem zero_site_alloca_provenance:
  let p = mk_inst 0 ALLOCA [Lit 0w] ["p"] in
  let q = mk_inst 2 ALLOCA [Lit 0w] ["q"] in
  let s = init_venom_state "entry" in
  case exec_alloca p s 0w of OK s1 =>
    (case exec_alloca q s1 0w of OK s2 =>
       FLOOKUP (step_prov [] (step_prov [] FEMPTY p s1) q s2) "p" = SOME (0,0) /\
       FLOOKUP (step_prov [] (step_prov [] FEMPTY p s1) q s2) "q" = SOME (0,0)
     | _ => F)
  | _ => F
Proof
  EVAL_TAC >> simp[]
QED

Theorem zero_site_initial_layout:
  code_layout_valid ((init_venom_state "entry") with
                       vs_labels := FEMPTY |+ ("code_end",0w))
Proof
  simp[code_layout_valid_def, init_venom_state_def,
       wordsTheory.dimword_def] >>
  `dimindex (:256) = 256` by CONV_TAC fcpLib.INDEX_CONV >>
  simp[finite_mapTheory.FLOOKUP_UPDATE]
QED
