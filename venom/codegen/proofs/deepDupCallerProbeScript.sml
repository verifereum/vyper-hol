(* Checked caller-interface probe for deep DUP.  This does not refute the
   mandated algorithm: it exposes an over-strong symbolic-map alignment
   contract when a literal in the spill map is subsequently pushed. *)
Theory deepDupCallerProbe
Ancestors doSwapSim planSpillBounds stackPlanGen stackPlanTypes stackModel
          mixedPrefixSim finite_map list rich_list words
Libs BasicProvers

Theorem bump_two_input_overlap_probe:
  !lo.
    let ps = (init_plan_state 0) with <|
          ps_stack := [Var "deep"; Var "a"; Var "b"; Var "c";
                       Var "d"; Var "e"; Var "f"; Var "g";
                       Var "h"; Var "i"; Var "j"; Var "k";
                       Var "l"; Var "m"; Var "n"; Var "o"];
          ps_spilled := FEMPTY |+ (Lit 42w, 0);
          ps_alloc := (init_spill_alloc 0) with sa_next_offset := 32 |>;
        h = Lit 42w;
        h' = Var "deep";
        result = emit_input_plan BUMP [h;h'] ["deep"] ps;
        input_ops = FST result;
        ps1 = SND result
    in
      (* Exactly generated_plan_state_wf 0 ps, expanded to avoid depending
         on the currently broken genBlockSim theory. *)
      plan_slots_bounded 0 ps /\
      spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
      ALL_DISTINCT ps.ps_stack /\
      DISJOINT (set ps.ps_stack) (FDOM ps.ps_spilled) /\
      (!op. MEM op [h;h'] /\ is_var_operand op ==>
        (?d. stack_get_depth op ps.ps_stack = SOME d /\ d <= 15) \/
        IS_SOME (FLOOKUP ps.ps_spilled op)) /\
      (!l. MEM (Label l) [h;h'] ==> IS_SOME (FLOOKUP lo l)) /\
      prefix_spill_wf initial_fmp lo input_ops ps /\
      (apply_prefix_ops initial_fmp lo input_ops ps).ps_spilled <> ps1.ps_spilled
Proof
  gen_tac >> CONV_TAC (computeLib.RESTR_EVAL_CONV [``spill_lookup``]) >>
  simp[FLOOKUP_UPDATE, DOMSUB_FUPDATE_THM, FLOOKUP_DEF] >>
  simp[spill_lookup_def, FLOOKUP_UPDATE, wordsTheory.dimword_def,
       fcpLib.INDEX_CONV ``dimindex(:256)``] >>
  rpt strip_tac >> gvs[is_var_operand_def] >> CONV_TAC EVAL
QED
