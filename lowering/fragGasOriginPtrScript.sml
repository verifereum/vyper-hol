(* One path carries GAS provenance, memory checks and pointer ghosts. *)
Theory fragGasOriginPtr
Ancestors
  fragGasOrigin fragGasPathPtr fragGasFocus ptrSafeRun ptrDiscipline
  venomExecSemantics venomInst venomState finite_map list arithmetic

Definition gas_origin_ptr_edge_def:
  gas_origin_ptr_edge (D, lo, explicit, ctx, func, PG)
      (s, G, tn) marks (r, G', tn') <=>
    gas_origin_edge T explicit ctx func s marks r /\
    gas_path_ptr_edge D lo ctx func PG G tn s
      (LENGTH marks) G' tn' r
End

Inductive gas_origin_ptr_path:
  (!D lo explicit ctx func PG s G tn.
     ~s.vs_halted ==>
     gas_origin_ptr_path (D, lo, explicit, ctx, func, PG)
       (s, G, tn) [] (OK s, G, tn)) /\
  (!D lo explicit ctx func PG s G tn left mid G1 tn1 right r G' tn'.
     gas_origin_ptr_edge (D, lo, explicit, ctx, func, PG)
       (s, G, tn) left (OK mid, G1, tn1) /\
     gas_origin_ptr_path (D, lo, explicit, ctx, func, PG)
       (mid, G1, tn1) right (r, G', tn') ==>
     gas_origin_ptr_path (D, lo, explicit, ctx, func, PG)
       (s, G, tn) (left ++ right) (r, G', tn')) /\
  (!D lo explicit ctx func PG s G tn marks r G' tn'.
     gas_origin_ptr_edge (D, lo, explicit, ctx, func, PG)
       (s, G, tn) marks (r, G', tn') /\ exit_result r ==>
     gas_origin_ptr_path (D, lo, explicit, ctx, func, PG)
       (s, G, tn) marks (r, G', tn'))
End

(* A focused call enters its child without claiming anything about the
   child's unexecuted suffix. Completed calls use the checked path edge. *)
Inductive gas_origin_ptr_focus:
  (!D lo explicit ctx func PG s G tn marks finish G' tn'.
     gas_origin_ptr_path (D, lo, explicit, ctx, func, PG)
       (s, G, tn) marks (OK finish, G', tn') ==>
     gas_origin_ptr_focus (D, lo, explicit, ctx, func, PG)
       (s, G, tn) marks (func, PG, G', tn', finish)) /\
  (!D lo explicit ctx func PG s G tn left mid G1 tn1 right leaf leaf_pg leaf_g leaf_tn finish.
     gas_origin_ptr_path (D, lo, explicit, ctx, func, PG)
       (s, G, tn) left (OK mid, G1, tn1) /\
     gas_origin_ptr_focus (D, lo, explicit, ctx, func, PG)
       (mid, G1, tn1) right (leaf, leaf_pg, leaf_g, leaf_tn, finish) ==>
     gas_origin_ptr_focus (D, lo, explicit, ctx, func, PG)
       (s, G, tn) (left ++ right) (leaf, leaf_pg, leaf_g, leaf_tn, finish)) /\
  (!D lo explicit ctx func PG s G tn bb inst name ops callee entered
    marks leaf leaf_pg leaf_g leaf_tn finish.
     lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
     get_instruction bb s.vs_inst_idx = SOME inst /\
     inst.inst_opcode = INVOKE /\
     decode_invoke inst = SOME (name, ops) /\
     gas_invoke_entry (ctx, func) s callee entered /\
     ptr_inst_ok D lo 0 ctx func G tn inst s /\
     gas_origin_ptr_focus
       (D, lo, explicit, ctx, callee, MAP (op_prov G) ops)
       (entered, FEMPTY, tn with t_var := FEMPTY)
       marks (leaf, leaf_pg, leaf_g, leaf_tn, finish) ==>
     gas_origin_ptr_focus (D, lo, explicit, ctx, func, PG)
       (s, G, tn) marks (leaf, leaf_pg, leaf_g, leaf_tn, finish))
End

Theorem gas_origin_ptr_path_projections:
  !D lo explicit ctx func PG s G tn marks r G' tn'.
    gas_origin_ptr_path (D, lo, explicit, ctx, func, PG)
      (s, G, tn) marks (r, G', tn') ==>
    gas_origin_path T explicit ctx func s marks r /\
    gas_path_ptr D lo ctx func PG G tn s (LENGTH marks) G' tn' r
Proof
  qsuff_tac
    `!cx st marks out.
       gas_origin_ptr_path cx st marks out ==>
       case (cx, st, out) of
         ((D, lo, explicit, ctx, func, PG), (s, G, tn), (r, G', tn')) =>
           gas_origin_path T explicit ctx func s marks r /\
           gas_path_ptr D lo ctx func PG G tn s (LENGTH marks) G' tn' r`
  >- (rpt strip_tac >>
      qpat_x_assum `!cx st marks out. _`
        (qspecl_then [`(D, lo, explicit, ctx, func, PG)`, `(s, G, tn)`,
                      `marks`, `(r, G', tn')`] mp_tac) >> simp[]) >>
  ho_match_mp_tac gas_origin_ptr_path_ind >> rpt conj_tac >>
  rpt gen_tac >> simp[gas_origin_ptr_edge_def, LENGTH_APPEND] >>
  metis_tac[gas_origin_path_rules, gas_path_ptr_rules]
QED

(* A joint edge has a single instruction fuel for its recorded sites,
   memory check and pointer ghost, even though the components hide fuel. *)
Theorem gas_origin_ptr_edge_common_fuel:
  gas_origin_ptr_edge (D, lo, explicit, ctx, func, PG)
    (s, G, tn) marks (r, G', tn') ==>
  ~s.vs_halted /\
  ?fuel bb inst middle.
    lookup_block s.vs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME inst /\
    step_inst fuel ctx inst s = middle /\
    marks = MAP (\key. key IN explicit)
      (gas_events_step fuel ctx func.fn_name inst s) /\
    (revert_forward_at bb s.vs_inst_idx \/ mem_safe_step fuel ctx inst s) /\
    ptr_safe_step D lo fuel ctx func PG G tn inst s /\
    ((?t. middle = OK t /\ ~is_terminator inst.inst_opcode /\
          ~t.vs_halted /\
          r = OK (t with vs_inst_idx := SUC s.vs_inst_idx) /\
          (G', tn') = ghost_step fuel ctx PG G tn inst s) \/
     (?t. middle = OK t /\ is_terminator inst.inst_opcode /\
          t.vs_halted /\ r = Halt t /\ G' = G /\ tn' = tn) \/
     (?t target entered.
        middle = OK t /\ is_terminator inst.inst_opcode /\ ~t.vs_halted /\
        lookup_block t.vs_current_bb func.fn_blocks = SOME target /\
        eval_phis t target.bb_instructions = OK entered /\ ~entered.vs_halted /\
        r = OK (entered with vs_inst_idx :=
                  phi_prefix_length target.bb_instructions) /\
        G' = entry_prov func t G /\ tn' = entry_taint_vars func t tn) \/
     (?lbl. is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
            middle = OK (jump_to lbl s) /\ r = middle /\
            G' = G /\ tn' = tn) \/
     (exit_result middle /\ r = middle /\ G' = G /\ tn' = tn))
Proof
  rewrite_tac[gas_origin_ptr_edge_def] >>
  disch_then (CONJUNCTS_THEN2 mp_tac assume_tac) >>
  rewrite_tac[gas_origin_edge_def] >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (qx_choose_then `a` (qx_choose_then `bb` (qx_choose_then `inst`
      (qx_choose_then `ma` (REPEAT_TCL CONJUNCTS_THEN assume_tac)))))) >>
  qpat_x_assum `gas_path_ptr_edge _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  rewrite_tac[gas_path_ptr_edge_def] >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (qx_choose_then `b` (qx_choose_then `bb2` (qx_choose_then `inst2`
      (qx_choose_then `mb` (REPEAT_TCL CONJUNCTS_THEN assume_tac)))))) >>
  gnvs[] >>
  `!e. step_inst a ctx inst s <> Error e` by
    (metis_tac[fragExecTheory.exit_result_not_error, venomExecSemanticsTheory.exec_result_distinct]) >>
  `!e. step_inst b ctx inst s <> Error e` by
    (metis_tac[fragExecTheory.exit_result_not_error, venomExecSemanticsTheory.exec_result_distinct]) >>
  `step_inst a ctx inst s = step_inst b ctx inst s` by
    (Cases_on `a <= b` >>
     metis_tac[CONJUNCT1 venomExecProofsTheory.fuel_mono, arithmeticTheory.NOT_LESS_EQUAL, arithmeticTheory.LESS_IMP_LESS_OR_EQ]) >>
  `ghost_step a ctx PG G tn inst s = ghost_step b ctx PG G tn inst s` by
    (Cases_on `a <= b` >>
     metis_tac[CONJUNCT1 ghost_fuel_mono_up, arithmeticTheory.NOT_LESS_EQUAL, arithmeticTheory.LESS_IMP_LESS_OR_EQ]) >>
  `ptr_safe_step D lo a ctx func PG G tn inst s` by
    (Cases_on `a <= b` >>
     metis_tac[CONJUNCT1 ptr_safe_fuel_mono_down,
               CONJUNCT1 ptr_safe_fuel_mono_up,
               arithmeticTheory.NOT_LESS_EQUAL, arithmeticTheory.LESS_IMP_LESS_OR_EQ]) >>
  qexists_tac `a` >> simp[]
QED

Theorem gas_origin_ptr_focus_origin:
  !D lo explicit ctx func PG s G tn marks leaf leaf_pg leaf_g leaf_tn stop_state.
    gas_origin_ptr_focus (D, lo, explicit, ctx, func, PG)
      (s, G, tn) marks (leaf, leaf_pg, leaf_g, leaf_tn, stop_state) ==>
    gas_origin_focus T explicit (ctx, func) s marks (leaf, stop_state)
Proof
  qsuff_tac
    `!cx st marks out.
       gas_origin_ptr_focus cx st marks out ==>
       case (cx, st, out) of
         ((D, lo, explicit, ctx, func, PG), (s, G, tn),
          (leaf, leaf_pg, leaf_g, leaf_tn, end_state)) =>
           gas_origin_focus T explicit (ctx, func) s marks (leaf, end_state)`
  >- (rpt strip_tac >>
      first_x_assum
        (qspecl_then [`(D, lo, explicit, ctx, func, PG)`, `(s, G, tn)`,
                      `marks`, `(leaf, leaf_pg, leaf_g, leaf_tn, stop_state)`]
                     mp_tac) >> simp[]) >>
  ho_match_mp_tac gas_origin_ptr_focus_ind >> rpt conj_tac >>
  rpt gen_tac >> simp[] >> strip_tac >>
  metis_tac[gas_origin_ptr_path_projections, gas_origin_focus_rules]
QED
