Theory fnPlanLineageRelationalTail
Ancestors fnPlanLineageSetup stackPlanGen stackPlanOps list

(* Preparation and deletion confinement are inputs. Shielding is required
   only at the actual enabled optimistic observation, with arbitrary spills. *)
Theorem native_regular_conditional_shared_core_replay:
  !liveness dfg cfg fn inst nl halting term lbl ps prefixP prefixQ
   preops r pops t.
    inst.inst_opcode <> JMP /\
    lineage_regular_prepare dfg inst nl
      (ps with ps_stack := prefixP ++ ps.ps_stack) =
      (preops,r with ps_stack := prefixP ++ r.ps_stack) /\
    lineage_regular_prepare dfg inst nl
      (ps with ps_stack := prefixQ ++ ps.ps_stack) =
      (preops,r with ps_stack := prefixQ ++ r.ps_stack) /\
    (if inst.inst_outputs <> [] /\ (~halting \/ LENGTH inst.inst_outputs > 1)
     then popmany_plan (MAP Var (FILTER (\v. ~MEM v nl) inst.inst_outputs))
       (r with ps_stack := prefixP ++ r.ps_stack)
     else ([],r with ps_stack := prefixP ++ r.ps_stack)) =
       (pops,t with ps_stack := prefixP ++ t.ps_stack) /\
    (if inst.inst_outputs <> [] /\ (~halting \/ LENGTH inst.inst_outputs > 1)
     then popmany_plan (MAP Var (FILTER (\v. ~MEM v nl) inst.inst_outputs))
       (r with ps_stack := prefixQ ++ r.ps_stack)
     else ([],r with ps_stack := prefixQ ++ r.ps_stack)) =
       (pops,t with ps_stack := prefixQ ++ t.ps_stack) /\
    (inst.inst_outputs <> [] /\ FILTER (\v. MEM v nl) inst.inst_outputs <> [] ==>
      nl = [] \/ MEM (Var (LAST nl)) t.ps_stack \/
      (~MEM (Var (LAST nl)) prefixP /\ ~MEM (Var (LAST nl)) prefixQ)) ==>
    ?ops u.
      generate_regular_inst_plan liveness dfg cfg fn inst nl halting term lbl
        (ps with ps_stack := prefixP ++ ps.ps_stack) =
        (ops,u with ps_stack := prefixP ++ u.ps_stack) /\
      generate_regular_inst_plan liveness dfg cfg fn inst nl halting term lbl
        (ps with ps_stack := prefixQ ++ ps.ps_stack) =
        (ops,u with ps_stack := prefixQ ++ u.ps_stack)
Proof
  rpt gen_tac >> strip_tac >>
  Cases_on `inst.inst_outputs = []`
  >- (qexistsl [`preops`, `release_dead_spills nl r`] >>
      simp[lineage_regular_prepare_decompose, release_dead_spills_stack_update,
        fnPlanLineageInventoryTheory.release_dead_spills_stack]) >>
  Cases_on `FILTER (\v. MEM v nl) inst.inst_outputs = []`
  >- (qexistsl [`preops ++ pops`, `release_dead_spills nl t`] >>
      gvs[] >>
      simp[lineage_regular_prepare_decompose, release_dead_spills_stack_update,
        fnPlanLineageInventoryTheory.release_dead_spills_stack]) >>
  namedCases_on `optimistic_swap_plan dfg inst nl term t` ["opts v"] >>
  `optimistic_swap_plan dfg inst nl term
    (t with ps_stack := prefixP ++ t.ps_stack) =
      (opts,v with ps_stack := prefixP ++ v.ps_stack)` by
    (irule optimistic_swap_plan_shielded_bottom_frame >> simp[] >> metis_tac[]) >>
  `optimistic_swap_plan dfg inst nl term
    (t with ps_stack := prefixQ ++ t.ps_stack) =
      (opts,v with ps_stack := prefixQ ++ v.ps_stack)` by
    (irule optimistic_swap_plan_shielded_bottom_frame >> simp[] >> metis_tac[]) >>
  qexistsl [`preops ++ pops ++ opts`, `release_dead_spills nl v`] >>
  gvs[] >>
  simp[lineage_regular_prepare_decompose, release_dead_spills_stack_update,
    fnPlanLineageInventoryTheory.release_dead_spills_stack]
QED
