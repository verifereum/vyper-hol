(* Supply expansion: structural and semantic segment interfaces. *)
Theory singleUseExpansionSupplySim
Ancestors
  singleUseExpansionSupplyProofs singleUseExpansionDefs irSupply
  stateFrame stateEquiv venomExecProps venomExecProofs
  venomExecSemantics venomWf venomInst venomState

(* Control indices are related separately by segment alignment. *)
Definition sue_state_rel_def:
  sue_state_rel protected st tt <=>
    execution_frame st = execution_frame tt /\
    st.vs_current_bb = tt.vs_current_bb /\
    st.vs_prev_bb = tt.vs_prev_bb /\
    (!v. v IN protected ==> FLOOKUP st.vs_vars v = FLOOKUP tt.vs_vars v)
End

Theorem sue_state_rel_refl[simp]:
  sue_state_rel protected st st
Proof
  simp[sue_state_rel_def]
QED

Theorem sue_state_rel_trans:
  sue_state_rel protected st tt /\ sue_state_rel protected tt uu ==>
  sue_state_rel protected st uu
Proof
  simp[sue_state_rel_def] >> metis_tac[]
QED

Theorem sue_state_rel_fresh_write:
  sue_state_rel protected st tt /\ ~(v IN protected) ==>
  sue_state_rel protected st (tt with vs_vars := tt.vs_vars |+ (v,w))
Proof
  simp[sue_state_rel_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  metis_tac[]
QED

(* Shape plus the exact supply delta records allocation order without
   identifying it with the order in which the prefix executes. *)
Theorem sue_expand_ops_supply_prefix:
  !dfg inst s ops k assigns new_ops s'.
    ir_supply_inst_ok s /\
    sue_expand_ops_supply dfg inst s ops k = (assigns,new_ops,s') ==>
    EVERY (\a. a.inst_opcode = ASSIGN /\ LENGTH a.inst_outputs = 1) assigns /\
    s'.irs_used_vars = FLAT (MAP (\a. a.inst_outputs) assigns) ++
                       s.irs_used_vars /\
    ALL_DISTINCT (FLAT (MAP (\a. a.inst_outputs) assigns)) /\
    EVERY (\v. ~MEM v s.irs_used_vars)
          (FLAT (MAP (\a. a.inst_outputs) assigns))
Proof
  Induct_on `ops`
  >- (rpt strip_tac >> gvs[sue_expand_ops_supply_def]) >>
  rpt gen_tac >> strip_tac >>
  Cases_on `sue_expand_ops_supply dfg inst s ops (k + 1)` >>
  PairCases_on `r` >>
  rename1 `sue_expand_ops_supply dfg inst s ops (k + 1) =
           (more_assigns,more_ops,s1)` >>
  `sue_supply_extends s s1` by
    metis_tac[sue_expand_ops_supply_extends] >>
  `ir_supply_inst_ok s1` by gvs[sue_supply_extends_def] >>
  first_x_assum drule_all >> strip_tac >>
  Cases_on `~sue_needs_assign dfg inst k`
  >- gvs[sue_expand_ops_supply_def] >>
  Cases_on `h`
  >- (Cases_on `sue_alloc_assign_supply s1 (Lit c)` >>
      PairCases_on `r` >>
      drule_all sue_alloc_assign_supply_contract >> strip_tac >>
      drule sue_alloc_assign_supply_shape >> strip_tac >>
      gvs[Once sue_expand_ops_supply_def] >>
      metis_tac[listTheory.MEM_REVERSE, listTheory.MEM_APPEND])
  >- (Cases_on `LENGTH (dfg_get_uses dfg s'') = 1 /\
                 sue_count_remaining (Var s'') ops = 0`
      >- gvs[sue_expand_ops_supply_def] >>
      Cases_on `sue_alloc_assign_supply s1 (Var s'')` >>
      PairCases_on `r` >>
      drule_all sue_alloc_assign_supply_contract >> strip_tac >>
      drule sue_alloc_assign_supply_shape >> strip_tac >>
      gvs[Once sue_expand_ops_supply_def] >>
      metis_tac[listTheory.MEM_REVERSE, listTheory.MEM_APPEND]) >>
  gvs[sue_expand_ops_supply_def]
QED

Theorem sue_expand_inst_supply_skip:
  sue_should_skip inst.inst_opcode ==>
  sue_expand_inst_supply dfg s inst = ([inst],s)
Proof
  simp[sue_expand_inst_supply_def]
QED

Theorem sue_expand_inst_supply_segment:
  ir_supply_inst_ok s /\
  sue_expand_inst_supply dfg s inst = (out,s') ==>
  ?assigns new_ops.
    out = assigns ++ [inst with inst_operands := new_ops] /\
    EVERY (\a. a.inst_opcode = ASSIGN /\ LENGTH a.inst_outputs = 1) assigns /\
    s'.irs_used_vars = FLAT (MAP (\a. a.inst_outputs) assigns) ++ s.irs_used_vars /\
    ALL_DISTINCT (FLAT (MAP (\a. a.inst_outputs) assigns)) /\
    EVERY (\v. ~MEM v s.irs_used_vars)
          (FLAT (MAP (\a. a.inst_outputs) assigns))
Proof
  strip_tac >> Cases_on `sue_should_skip inst.inst_opcode`
  >- (gvs[sue_expand_inst_supply_def] >>
      qexists_tac `inst.inst_operands` >> simp[]) >>
  Cases_on `sue_expand_ops_supply dfg inst s inst.inst_operands 0` >>
  PairCases_on `r` >>
  gvs[sue_expand_inst_supply_def] >>
  drule_all sue_expand_ops_supply_prefix >> strip_tac >>
  qexists_tac `r0` >> simp[]
QED

Theorem sue_expand_inst_supply_nonempty:
  sue_expand_inst_supply dfg s inst = (out,s') ==> out <> []
Proof
  strip_tac >> Cases_on `sue_should_skip inst.inst_opcode`
  >- gvs[sue_expand_inst_supply_def] >>
  Cases_on `sue_expand_ops_supply dfg inst s inst.inst_operands 0` >>
  PairCases_on `r` >> gvs[sue_expand_inst_supply_def]
QED

Theorem sue_expand_inst_supply_last:
  sue_expand_inst_supply dfg s inst = (out,s') ==>
  (LAST out).inst_opcode = inst.inst_opcode /\
  (LAST out).inst_outputs = inst.inst_outputs /\
  (LAST out).inst_id = inst.inst_id
Proof
  strip_tac >> Cases_on `sue_should_skip inst.inst_opcode`
  >- gvs[sue_expand_inst_supply_def] >>
  Cases_on `sue_expand_ops_supply dfg inst s inst.inst_operands 0` >>
  PairCases_on `r` >> gvs[sue_expand_inst_supply_def]
QED

(* This interface is independent of the tail and of supply well-formedness. *)
Theorem sue_expand_ops_supply_preserved_head:
  ~sue_needs_assign dfg inst k /\
  sue_expand_ops_supply dfg inst s (op::ops) k = (assigns,new_ops,s') ==>
  ?rest. new_ops = op::rest /\
    sue_expand_ops_supply dfg inst s ops (k + 1) = (assigns,rest,s')
Proof
  strip_tac >>
  Cases_on `sue_expand_ops_supply dfg inst s ops (k + 1)` >>
  PairCases_on `r` >> gvs[sue_expand_ops_supply_def]
QED

Theorem sue_expand_ops_supply_structural_head:
  (inst.inst_opcode = LOG \/ inst.inst_opcode = DRET) /\
  inst.inst_operands = op::ops /\
  sue_expand_ops_supply dfg inst s inst.inst_operands 0 =
    (assigns,new_ops,s') ==>
  ?rest. new_ops = op::rest /\
    sue_expand_ops_supply dfg inst s ops 1 = (assigns,rest,s')
Proof
  strip_tac >>
  `~sue_needs_assign dfg inst 0` by simp[sue_needs_assign_def] >>
  gvs[] >> drule_all sue_expand_ops_supply_preserved_head >> simp[]
QED

Theorem sue_expand_inst_supply_labels:
  sue_expand_inst_supply dfg s inst = (out,s') ==>
  MAP sue_operand_label (LAST out).inst_operands =
  MAP sue_operand_label inst.inst_operands
Proof
  strip_tac >> Cases_on `sue_should_skip inst.inst_opcode`
  >- gvs[sue_expand_inst_supply_def] >>
  Cases_on `sue_expand_ops_supply dfg inst s inst.inst_operands 0` >>
  PairCases_on `r` >> gvs[sue_expand_inst_supply_def] >>
  metis_tac[sue_expand_ops_supply_operand_labels]
QED

(* Checked examples intentionally include no supply distinctness assumption. *)
Theorem sue_supply_two_literals_probe[local]:
  MAP (\i. i.inst_operands)
    (FST (sue_expand_inst_supply dfg
      <| irs_next_inst := 10; irs_next_var := 0; irs_next_label := 0;
         irs_used_inst_ids := []; irs_used_vars := []; irs_used_labels := [] |>
      <| inst_id := 1; inst_opcode := ADD;
         inst_operands := [Lit 3w; Lit 4w]; inst_outputs := ["out"] |>)) =
    [[Lit 3w]; [Lit 4w]; [Var "formal_var_1"; Var "formal_var_0"]]
Proof
  EVAL_TAC
QED

Theorem sue_supply_phi_probe[local]:
  sue_expand_inst_supply dfg s
    <| inst_id := 1; inst_opcode := PHI;
       inst_operands := [Label "pred"; Var "x"]; inst_outputs := ["y"] |> =
  ([<| inst_id := 1; inst_opcode := PHI;
       inst_operands := [Label "pred"; Var "x"]; inst_outputs := ["y"] |>],s)
Proof
  simp[sue_expand_inst_supply_def, sue_should_skip_def]
QED

Theorem sue_supply_ignored_operand_probe[local]:
  MAP (\i. i.inst_operands)
    (FST (sue_expand_inst_supply
      (dfg_empty with dfg_uses := FEMPTY |+ ("x",
        [<| inst_id := 1; inst_opcode := CALLER;
            inst_operands := [Var "x"]; inst_outputs := ["y"] |>;
         <| inst_id := 2; inst_opcode := CALLER;
            inst_operands := [Var "x"]; inst_outputs := ["z"] |>]))
      <| irs_next_inst := 10; irs_next_var := 0; irs_next_label := 0;
         irs_used_inst_ids := [1;2]; irs_used_vars := ["x";"y";"z"];
         irs_used_labels := [] |>
      <| inst_id := 1; inst_opcode := CALLER;
         inst_operands := [Var "x"]; inst_outputs := ["y"] |>)) =
    [[Var "x"]; [Var "formal_var_0"]]
Proof
  EVAL_TAC
QED

Theorem sue_supply_repeated_variable_probe[local]:
  MAP (\i. i.inst_operands)
    (FST (sue_expand_inst_supply
      (dfg_empty with dfg_uses := FEMPTY |+ ("x",
        [<| inst_id := 1; inst_opcode := ADD;
            inst_operands := [Var "x"; Var "x"]; inst_outputs := ["y"] |>;
         <| inst_id := 2; inst_opcode := STOP;
            inst_operands := [Var "x"]; inst_outputs := [] |>]))
      <| irs_next_inst := 10; irs_next_var := 0; irs_next_label := 0;
         irs_used_inst_ids := [1;2]; irs_used_vars := ["x";"y"];
         irs_used_labels := [] |>
      <| inst_id := 1; inst_opcode := ADD;
         inst_operands := [Var "x"; Var "x"]; inst_outputs := ["y"] |>)) =
    [[Var "x"]; [Var "x"]; [Var "formal_var_1"; Var "formal_var_0"]]
Proof
  EVAL_TAC
QED

Theorem sue_expand_inst_supply_structural_head:
  (inst.inst_opcode = LOG \/ inst.inst_opcode = DRET) /\
  inst.inst_operands = op::ops /\
  sue_expand_inst_supply dfg s inst = (out,s') ==>
  ?rest. (LAST out).inst_operands = op::rest
Proof
  strip_tac >> Cases_on `sue_should_skip inst.inst_opcode`
  >- gvs[sue_expand_inst_supply_def] >>
  Cases_on `sue_expand_ops_supply dfg inst s inst.inst_operands 0` >>
  PairCases_on `r` >> gvs[sue_expand_inst_supply_def] >>
  `~sue_needs_assign dfg inst 0` by simp[sue_needs_assign_def] >>
  drule_all sue_expand_ops_supply_preserved_head >>
  strip_tac >> simp[]
QED

(* Retain segment boundaries rather than recovering them from transformed IR. *)
Definition sue_segments_supply_def:
  sue_segments_supply dfg s [] = ([],s) /\
  sue_segments_supply dfg s (inst::insts) =
    case sue_expand_inst_supply dfg s inst of (out,s1) =>
    case sue_segments_supply dfg s1 insts of (segs,s2) =>
      (out::segs,s2)
End

Definition sue_segment_offset_def:
  sue_segment_offset segs i = LENGTH (FLAT (TAKE i segs))
End

Theorem sue_segments_supply_flat:
  !insts dfg s segs s'.
    sue_segments_supply dfg s insts = (segs,s') ==>
    sue_expand_insts_supply dfg s insts = (FLAT segs,s')
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- gvs[sue_segments_supply_def, sue_expand_insts_supply_def] >>
  Cases_on `sue_expand_inst_supply dfg s h` >>
  Cases_on `sue_segments_supply dfg r insts` >>
  gvs[sue_segments_supply_def, sue_expand_insts_supply_def] >>
  first_x_assum drule >> simp[]
QED

Theorem sue_segments_supply_length:
  !insts dfg s segs s'.
    sue_segments_supply dfg s insts = (segs,s') ==>
    LENGTH segs = LENGTH insts
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- gvs[sue_segments_supply_def] >>
  Cases_on `sue_expand_inst_supply dfg s h` >>
  Cases_on `sue_segments_supply dfg r insts` >>
  gvs[sue_segments_supply_def] >> metis_tac[]
QED

Theorem sue_segments_supply_nonempty:
  !insts dfg s segs s'.
    sue_segments_supply dfg s insts = (segs,s') ==>
    EVERY (\seg. seg <> []) segs
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- gvs[sue_segments_supply_def] >>
  Cases_on `sue_expand_inst_supply dfg s h` >>
  Cases_on `sue_segments_supply dfg r insts` >>
  gvs[sue_segments_supply_def] >>
  metis_tac[sue_expand_inst_supply_nonempty]
QED

Theorem sue_segments_supply_index:
  !insts dfg s segs s' i.
    sue_segments_supply dfg s insts = (segs,s') /\ i < LENGTH insts ==>
    ?si sj. sue_expand_inst_supply dfg si (EL i insts) = (EL i segs,sj) /\
            (ir_supply_inst_ok s ==> sue_supply_extends s si)
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- gvs[sue_segments_supply_def] >>
  Cases_on `sue_expand_inst_supply dfg s h` >>
  Cases_on `sue_segments_supply dfg r insts` >>
  gvs[sue_segments_supply_def] >>
  Cases_on `i`
  >- (gvs[] >> qexistsl [`s`,`r`] >>
      simp[sue_supply_extends_refl]) >>
  gvs[] >> first_x_assum drule_all >> strip_tac >>
  qexistsl [`si`,`sj`] >> simp[] >> strip_tac >>
  `sue_supply_extends s r` by metis_tac[sue_expand_inst_supply_extends] >>
  `ir_supply_inst_ok r` by gvs[sue_supply_extends_def] >>
  metis_tac[sue_supply_extends_trans]
QED

Theorem sue_segment_offset_zero[simp]:
  sue_segment_offset segs 0 = 0
Proof
  simp[sue_segment_offset_def]
QED

Theorem sue_segment_offset_cons[simp]:
  sue_segment_offset (seg::segs) (SUC i) =
    LENGTH seg + sue_segment_offset segs i
Proof
  simp[sue_segment_offset_def]
QED

Theorem sue_segment_offset_end[simp]:
  sue_segment_offset segs (LENGTH segs) = LENGTH (FLAT segs)
Proof
  simp[sue_segment_offset_def]
QED

Theorem sue_segment_offset_suc:
  !segs i. i < LENGTH segs ==>
    sue_segment_offset segs (SUC i) =
      sue_segment_offset segs i + LENGTH (EL i segs)
Proof
  Induct >> Cases_on `i` >> simp[]
QED

Theorem sue_segment_offset_el:
  !segs i j. i < LENGTH segs /\ j < LENGTH (EL i segs) ==>
    EL (sue_segment_offset segs i + j) (FLAT segs) = EL j (EL i segs)
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- gvs[] >>
  Cases_on `i` >> gvs[listTheory.EL_APPEND_EQN]
QED

Theorem sue_segment_offset_bound:
  !segs i. i <= LENGTH segs ==>
    sue_segment_offset segs i <= LENGTH (FLAT segs)
Proof
  Induct >> Cases_on `i` >> simp[]
QED

Theorem sue_segment_interior:
  !segs k. k < LENGTH (FLAT segs) ==>
    ?i j. i < LENGTH segs /\ j < LENGTH (EL i segs) /\
          k = sue_segment_offset segs i + j
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- gvs[] >>
  gvs[] >> Cases_on `k < LENGTH h`
  >- (qexistsl [`0`,`k`] >> simp[]) >>
  first_x_assum (qspec_then `k - LENGTH h` mp_tac) >>
  simp[] >> strip_tac >>
  qexistsl [`SUC i`,`j`] >> simp[]
QED

Theorem sue_segment_offset_strict:
  !segs i j. EVERY (\seg. seg <> []) segs /\
    i < j /\ j <= LENGTH segs ==>
    sue_segment_offset segs i < sue_segment_offset segs j
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- gvs[] >>
  Cases_on `i` >> Cases_on `j` >> gvs[] >>
  Cases_on `h` >> gvs[]
QED

Theorem sue_segment_offset_mono:
  !segs i j. i <= j /\ j <= LENGTH segs ==>
    sue_segment_offset segs i <= sue_segment_offset segs j
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- gvs[] >>
  Cases_on `i` >> Cases_on `j` >> gvs[]
QED

Theorem sue_segment_interior_unique:
  i < LENGTH segs /\ i' < LENGTH segs /\
  j < LENGTH (EL i segs) /\ j' < LENGTH (EL i' segs) /\
  sue_segment_offset segs i + j = sue_segment_offset segs i' + j' ==>
  i = i' /\ j = j'
Proof
  strip_tac >>
  Cases_on `i = i'` >- gvs[] >>
  `sue_segment_offset segs (SUC i) =
   sue_segment_offset segs i + LENGTH (EL i segs)` by
    simp[sue_segment_offset_suc] >>
  `sue_segment_offset segs (SUC i') =
   sue_segment_offset segs i' + LENGTH (EL i' segs)` by
    simp[sue_segment_offset_suc] >>
  Cases_on `i < i'`
  >- (`sue_segment_offset segs (SUC i) <= sue_segment_offset segs i'` by
        (irule sue_segment_offset_mono >> simp[]) >> gvs[]) >>
  `sue_segment_offset segs (SUC i') <= sue_segment_offset segs i` by
    (irule sue_segment_offset_mono >> simp[]) >> gvs[]
QED

Theorem sue_expand_block_supply_label:
  sue_expand_block_supply dfg s bb = (bb',s') ==>
  bb'.bb_label = bb.bb_label
Proof
  Cases_on `sue_expand_insts_supply dfg s bb.bb_instructions` >>
  simp[sue_expand_block_supply_def] >> strip_tac >> gvs[]
QED

Theorem sue_expand_blocks_supply_labels:
  !bbs dfg s bbs' s'.
    sue_expand_blocks_supply dfg s bbs = (bbs',s') ==>
    MAP (\bb. bb.bb_label) bbs' = MAP (\bb. bb.bb_label) bbs
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- gvs[sue_expand_blocks_supply_def] >>
  Cases_on `sue_expand_block_supply dfg s h` >>
  Cases_on `sue_expand_blocks_supply dfg r bbs` >>
  gvs[sue_expand_blocks_supply_def] >>
  metis_tac[sue_expand_block_supply_label]
QED

Theorem sue_expand_blocks_supply_lookup:
  !bbs dfg s bbs' s' lbl bb.
    sue_expand_blocks_supply dfg s bbs = (bbs',s') /\
    lookup_block lbl bbs = SOME bb ==>
    ?bb' si sj. lookup_block lbl bbs' = SOME bb' /\
                sue_expand_block_supply dfg si bb = (bb',sj) /\
                (ir_supply_inst_ok s ==> sue_supply_extends s si)
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- gvs[lookup_block_def, listTheory.FIND_thm] >>
  Cases_on `sue_expand_block_supply dfg s h` >>
  Cases_on `sue_expand_blocks_supply dfg r bbs` >>
  gvs[sue_expand_blocks_supply_def] >>
  drule sue_expand_block_supply_label >> strip_tac >>
  `ir_supply_inst_ok s ==> sue_supply_extends s r /\ ir_supply_inst_ok r` by
    (strip_tac >> drule_all sue_expand_block_supply_extends >>
     simp[sue_supply_extends_def] >> metis_tac[]) >>
  Cases_on `h.bb_label = lbl`
  >- (gvs[lookup_block_def, listTheory.FIND_thm] >>
      metis_tac[sue_supply_extends_refl]) >>
  gvs[lookup_block_def, listTheory.FIND_thm] >>
  first_x_assum drule_all >> strip_tac >>
  metis_tac[sue_supply_extends_trans]
QED

Theorem sue_expand_inst_supply_nonphi:
  ir_supply_inst_ok s /\ inst.inst_opcode <> PHI /\
  sue_expand_inst_supply dfg s inst = (out,s') ==>
  EVERY (\i. i.inst_opcode <> PHI) out
Proof
  strip_tac >> drule_all sue_expand_inst_supply_segment >> strip_tac >>
  gvs[listTheory.EVERY_APPEND, listTheory.EVERY_MEM] >> metis_tac[]
QED

Theorem sue_nonphi_prefix:
  EVERY (\i. i.inst_opcode <> PHI) out /\ out <> [] ==>
  phi_prefix_length (out ++ tail) = 0 /\
  eval_phis st (out ++ tail) = OK st
Proof
  Cases_on `out` >> simp[phi_prefix_length_def, eval_phis_def] >>
  strip_tac >> simp[phi_prefix_length_def, eval_phis_def]
QED

Theorem sue_expand_insts_supply_phis:
  !insts dfg s out s' st.
    ir_supply_inst_ok s /\
    sue_expand_insts_supply dfg s insts = (out,s') ==>
    phi_prefix_length out = phi_prefix_length insts /\
    eval_phis st out = eval_phis st insts
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- gvs[sue_expand_insts_supply_def] >>
  Cases_on `sue_expand_inst_supply dfg s h` >>
  rename1 `sue_expand_inst_supply dfg s h = (head_out,s1)` >>
  Cases_on `sue_expand_insts_supply dfg s1 insts` >>
  rename1 `sue_expand_insts_supply dfg s1 insts = (tail_out,s2)` >>
  gvs[sue_expand_insts_supply_def] >>
  `sue_supply_extends s s1` by metis_tac[sue_expand_inst_supply_extends] >>
  `ir_supply_inst_ok s1` by gvs[sue_supply_extends_def] >>
  Cases_on `h.inst_opcode = PHI`
  >- (`sue_should_skip h.inst_opcode` by simp[sue_should_skip_def] >>
      drule_all sue_expand_inst_supply_skip >> strip_tac >>
      gvs[] >> first_x_assum drule_all >>
      disch_then (qspec_then `st` assume_tac) >>
      simp[phi_prefix_length_def, eval_phis_def]) >>
  `EVERY (\i. i.inst_opcode <> PHI) head_out` by
    metis_tac[sue_expand_inst_supply_nonphi] >>
  `head_out <> []` by metis_tac[sue_expand_inst_supply_nonempty] >>
  drule_all sue_nonphi_prefix >> simp[phi_prefix_length_def, eval_phis_def]
QED

Theorem sue_expand_function_supply_identity:
  sue_expand_function_supply s fn = (fn',s') ==>
  fn'.fn_name = fn.fn_name /\ fn_entry_label fn' = fn_entry_label fn
Proof
  strip_tac >>
  Cases_on `sue_expand_blocks_supply (dfg_build_function fn) s fn.fn_blocks` >>
  gvs[sue_expand_function_supply_def] >>
  drule sue_expand_blocks_supply_labels >> strip_tac >>
  Cases_on `fn.fn_blocks` >> Cases_on `q` >>
  gvs[fn_entry_label_def, entry_block_def]
QED

Theorem sue_expand_function_supply_lookup:
  sue_expand_function_supply s fn = (fn',s') /\
  lookup_block lbl fn.fn_blocks = SOME bb ==>
  ?bb' si sj. lookup_block lbl fn'.fn_blocks = SOME bb' /\
              sue_expand_block_supply (dfg_build_function fn) si bb = (bb',sj) /\
              (ir_supply_inst_ok s ==> sue_supply_extends s si)
Proof
  strip_tac >>
  Cases_on `sue_expand_blocks_supply (dfg_build_function fn) s fn.fn_blocks` >>
  gvs[sue_expand_function_supply_def] >>
  drule_all sue_expand_blocks_supply_lookup >> simp[]
QED

Theorem sue_expand_block_supply_segments:
  sue_expand_block_supply dfg s bb = (bb',s') ==>
  ?segs. sue_segments_supply dfg s bb.bb_instructions = (segs,s') /\
         bb' = bb with bb_instructions := FLAT segs
Proof
  strip_tac >>
  Cases_on `sue_segments_supply dfg s bb.bb_instructions` >>
  drule sue_segments_supply_flat >> strip_tac >>
  gvs[sue_expand_block_supply_def]
QED

(* At PHI entry the two indices agree; later segment positions need not. *)
Theorem sue_state_rel_entry_equiv:
  sue_state_rel protected st tt /\ st.vs_inst_idx = tt.vs_inst_idx <=>
  state_equiv (COMPL protected) st tt
Proof
  simp[sue_state_rel_def, state_equiv_def, execution_equiv_def,
       lookup_var_def] >> metis_tac[]
QED

Theorem sue_eval_phis_entry:
  sue_state_rel protected st tt /\ st.vs_inst_idx = tt.vs_inst_idx /\
  EVERY (\inst. inst.inst_opcode = PHI ==>
    !v. MEM (Var v) inst.inst_operands ==> v IN protected) insts /\
  eval_phis st insts = OK st' ==>
  ?tt'. eval_phis tt insts = OK tt' /\
    sue_state_rel protected st' tt' /\ st'.vs_inst_idx = tt'.vs_inst_idx
Proof
  strip_tac >>
  `state_equiv (COMPL protected) st tt` by
    simp[GSYM sue_state_rel_entry_equiv] >>
  drule eval_phis_state_equiv >>
  disch_then (qspec_then `insts` mp_tac) >>
  simp[] >> strip_tac >>
  qexists_tac `s2'` >> simp[sue_state_rel_entry_equiv]
QED

Theorem sue_expand_blocks_supply_lookup_back:
  !bbs dfg s bbs' s' lbl bb'.
    sue_expand_blocks_supply dfg s bbs = (bbs',s') /\
    lookup_block lbl bbs' = SOME bb' ==>
    ?bb si sj. lookup_block lbl bbs = SOME bb /\
               sue_expand_block_supply dfg si bb = (bb',sj) /\
                (ir_supply_inst_ok s ==> sue_supply_extends s si)
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- gvs[sue_expand_blocks_supply_def, lookup_block_def, listTheory.FIND_thm] >>
  Cases_on `sue_expand_block_supply dfg s h` >>
  Cases_on `sue_expand_blocks_supply dfg r bbs` >>
  gvs[sue_expand_blocks_supply_def] >>
  drule sue_expand_block_supply_label >> strip_tac >>
  `ir_supply_inst_ok s ==> sue_supply_extends s r /\ ir_supply_inst_ok r` by
    (strip_tac >> drule_all sue_expand_block_supply_extends >>
     simp[sue_supply_extends_def] >> metis_tac[]) >>
  Cases_on `h.bb_label = lbl`
  >- (gvs[lookup_block_def, listTheory.FIND_thm] >>
      metis_tac[sue_supply_extends_refl]) >>
  gvs[lookup_block_def, listTheory.FIND_thm] >>
  first_x_assum drule_all >> strip_tac >>
  metis_tac[sue_supply_extends_trans]
QED

Theorem sue_operand_label_get_label:
  sue_operand_label = get_label
Proof
  simp[FUN_EQ_THM] >> Cases >>
  simp[sue_operand_label_def, get_label_def]
QED

Theorem sue_expand_inst_supply_successors:
  sue_expand_inst_supply dfg s inst = (out,s') ==>
  get_successors (LAST out) = get_successors inst
Proof
  strip_tac >>
  drule sue_expand_inst_supply_last >> strip_tac >>
  drule sue_expand_inst_supply_labels >>
  simp[sue_operand_label_get_label, get_successors_def]
QED


Theorem sue_segment_last_index:
  i < LENGTH segs /\ SUC i = LENGTH segs /\ EL i segs <> [] ==>
  LAST (FLAT segs) = LAST (EL i segs)
Proof
  strip_tac >>
  `0 < LENGTH (EL i segs)` by (Cases_on `EL i segs` >> gvs[]) >>
  `sue_segment_offset segs i + LENGTH (EL i segs) = LENGTH (FLAT segs)` by
    (drule sue_segment_offset_suc >> simp[]) >>
  `0 < LENGTH (FLAT segs)` by decide_tac >>
  `sue_segment_offset segs i + (LENGTH (EL i segs) - 1) =
   LENGTH (FLAT segs) - 1` by decide_tac >>
  `LENGTH (EL i segs) - 1 < LENGTH (EL i segs)` by decide_tac >>
  `EL (LENGTH (FLAT segs) - 1) (FLAT segs) =
   EL (LENGTH (EL i segs) - 1) (EL i segs)` by
    metis_tac[sue_segment_offset_el] >>
  `FLAT segs <> []` by (strip_tac >> gvs[]) >>
  simp[listTheory.LAST_EL, arithmeticTheory.PRE_SUB1]
QED

Theorem sue_expand_block_supply_successors:
  sue_expand_block_supply dfg s bb = (bb',s') /\
  bb.bb_instructions <> [] ==>
  get_successors (LAST bb'.bb_instructions) =
  get_successors (LAST bb.bb_instructions)
Proof
  strip_tac >> drule sue_expand_block_supply_segments >> strip_tac >>
  `LENGTH segs = LENGTH bb.bb_instructions` by
    metis_tac[sue_segments_supply_length] >>
  `0 < LENGTH bb.bb_instructions` by
    (Cases_on `bb.bb_instructions` >> gvs[]) >>
  drule sue_segments_supply_index >>
  disch_then (qspec_then `LENGTH bb.bb_instructions - 1` mp_tac) >>
  simp[] >> strip_tac >>
  `EVERY (\seg. seg <> []) segs` by
    metis_tac[sue_segments_supply_nonempty] >>
  `EL (LENGTH bb.bb_instructions - 1) segs <> []` by
    gvs[listTheory.EVERY_EL] >>
  `LAST (FLAT segs) = LAST (EL (LENGTH bb.bb_instructions - 1) segs)` by
    (irule sue_segment_last_index >> simp[]) >>
  drule sue_expand_inst_supply_successors >>
  gvs[listTheory.LAST_EL, arithmeticTheory.PRE_SUB1]
QED
