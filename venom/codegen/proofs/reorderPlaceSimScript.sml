(* Physical placement of one prepared operand.
   TOP-LEVEL: reorder_place_checked_sim.
   Helpers: planner aliases at equal-valued physical stack positions. *)
Theory reorderPlaceSim
Ancestors
  doSwapCorrect doSwapSim operandInventory instSimHelpers
  stackPlanOps stackPlanTypes stackModel codegenRel asmSem planExec stackOpSim
  dfgDefs list rich_list finite_map arithmetic

Theorem stack_poke_length[local,simp]:
  LENGTH (stack_poke dist op stk) = LENGTH stk
Proof
  simp[stack_poke_def, LENGTH_LUPDATE]
QED

Theorem venom_asm_rel_stack_value:
  !lo ps vs st dist.
    venom_asm_rel lo ps vs st /\ dist < LENGTH ps.ps_stack /\
    stack_peek dist ps.ps_stack <> dead_stack_marker ==>
    operand_val vs lo (stack_peek dist ps.ps_stack) = SOME (EL dist st.as_stack)
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.SPECL [`lo`,`vs`,`ps.ps_stack`,`st.as_stack`,`dist`]
    plan_stack_rel_el) >>
  (impl_tac >- fs[venom_asm_rel_def]) >>
  asm_simp_tac (srw_ss()) [GSYM stack_peek_eq_EL_REVERSE_inventory]
QED

Theorem venom_asm_rel_alias_swap:
  !lo ps vs st dist final_dist op.
    venom_asm_rel lo ps vs st /\
    dist < LENGTH ps.ps_stack /\ final_dist < LENGTH ps.ps_stack /\
    stack_peek dist ps.ps_stack = op /\ op <> dead_stack_marker /\
    stack_peek final_dist ps.ps_stack <> dead_stack_marker /\
    operand_val vs lo op = operand_val vs lo (stack_peek final_dist ps.ps_stack) ==>
    venom_asm_rel lo
      (ps with ps_stack := stack_poke final_dist op
        (stack_poke dist (stack_peek final_dist ps.ps_stack) ps.ps_stack)) vs st
Proof
  rpt gen_tac >> strip_tac >>
  `operand_val vs lo op = SOME (EL dist st.as_stack)` by
    (mp_tac (Q.SPECL [`lo`,`ps`,`vs`,`st`,`dist`] venom_asm_rel_stack_value) >>
     (impl_tac >- asm_simp_tac (srw_ss()) []) >> asm_simp_tac (srw_ss()) []) >>
  `operand_val vs lo (stack_peek final_dist ps.ps_stack) =
     SOME (EL final_dist st.as_stack)` by
    (mp_tac (Q.SPECL [`lo`,`ps`,`vs`,`st`,`final_dist`]
       venom_asm_rel_stack_value) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> simp_tac bool_ss []) >>
  fs[venom_asm_rel_def] >> irule plan_stack_rel_poke_swap >>
  asm_simp_tac (srw_ss()) []
QED

Theorem reorder_place_checked_sim:
  !dfg op dist final_dist ps ops post initial_fmp lo o2pc prog vs st.
    dist < LENGTH ps.ps_stack /\ stack_peek dist ps.ps_stack = op /\
    final_dist < LENGTH ps.ps_stack /\
    spill_alloc_layout_wf ps.ps_alloc ps.ps_spilled /\
    op <> dead_stack_marker /\
    (!at. operand_equiv dfg op at ==> at <> dead_stack_marker) /\
    (!op1 at. operand_equiv dfg op1 at ==>
       operand_val vs lo op1 = operand_val vs lo at) /\
    (if dist = final_dist then ([],ps)
     else if operand_equiv dfg op (stack_peek final_dist ps.ps_stack) then
       ([],ps with ps_stack := stack_poke final_dist op
         (stack_poke dist (stack_peek final_dist ps.ps_stack) ps.ps_stack))
     else
       let (ops1,mid) = do_swap dist ps;
           (ops2,last) = do_swap final_dist mid
       in (ops1 ++ ops2,last)) = (ops,post) /\
    (!bytes. MEM (AsmPush bytes) prog ==> LENGTH bytes <= 32) /\
    venom_asm_rel lo ps vs st /\
    asm_block_at prog st.as_pc (execute_plan initial_fmp ops) ==>
    ?st'. asm_steps lo o2pc prog (LENGTH (execute_plan initial_fmp ops)) st =
      AsmOK st' /\ venom_asm_rel lo post vs st' /\
      st'.as_pc = st.as_pc + LENGTH (execute_plan initial_fmp ops) /\
      spill_alloc_layout_wf post.ps_alloc post.ps_spilled /\
      LENGTH post.ps_stack = LENGTH ps.ps_stack
Proof
  rpt gen_tac >> strip_tac >> Cases_on `dist = final_dist`
  >- (gvs[] >> qexists_tac `st` >> simp[execute_plan_def, asm_steps_def]) >>
  Cases_on `operand_equiv dfg op (stack_peek final_dist ps.ps_stack)`
  >- (gvs[] >>
      `stack_peek final_dist ps.ps_stack <> dead_stack_marker` by
        (CCONTR_TAC >> gvs[]) >>
      `operand_val vs lo (stack_peek dist ps.ps_stack) =
       operand_val vs lo (stack_peek final_dist ps.ps_stack)` by
        (qpat_assum `!op1 at. operand_equiv dfg op1 at ==> _`
           (qspecl_then [`stack_peek dist ps.ps_stack`,
             `stack_peek final_dist ps.ps_stack`] mp_tac) >> simp[]) >>
      qexists_tac `st` >> simp[execute_plan_def, asm_steps_def] >>
      irule venom_asm_rel_alias_swap >> asm_simp_tac (srw_ss()) []) >>
  Cases_on `do_swap dist ps` >> rename1 `do_swap dist ps = (ops1,mid)` >>
  Cases_on `do_swap final_dist mid` >>
  rename1 `do_swap final_dist mid = (ops2,last)` >> gvs[] >>
  mp_tac (Q.SPECL [`dist`,`final_dist`,`ps`,`ops1`,`mid`,`ops2`,`last`,
    `initial_fmp`,`lo`,`o2pc`,`prog`,`vs`,`st`] two_swaps_checked_sim) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  simp_tac std_ss [ADD_COMM]
QED
