(* Supply expansion: structural and semantic segment interfaces. *)
Theory singleUseExpansionSupplySim
Ancestors
  singleUseExpansionSupplyProofs singleUseExpansionDefs irSupply
  stateFrame stateEquiv venomExecProps venomExecProofs
  venomExecSemantics venomWf venomInst venomState sccpCorrectnessProofs
  analysisSimDefs instIdxIndep execEquivParamProofs passSharedSubst

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
  qexistsl_tac [`bb''`, `si`, `sj`] >> simp[] >>
  strip_tac >> irule sue_supply_extends_trans >>
  qexists_tac `r` >> simp[]
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
  qexistsl_tac [`bb`, `si`, `sj`] >> simp[] >>
  strip_tac >> irule sue_supply_extends_trans >>
  qexists_tac `r` >> simp[]
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

(* The execution invariant at a source instruction boundary.  PHIs have
   already executed; idx is independent of the state's control index so
   this same interface applies to partial exec_block calls. *)
Definition sue_boundary_defined_def:
  sue_boundary_defined f bb idx st <=>
    strict_dom_vars_defined f st /\
    (!j v. j < idx /\ MEM v (EL j bb.bb_instructions).inst_outputs ==>
           v IN FDOM st.vs_vars)
End

Theorem sue_boundary_operand_defined:
  wf_ssa f /\ wf_function f /\ fn_inst_wf f /\
  MEM bb f.fn_blocks /\ bb.bb_label = st.vs_current_bb /\
  idx < LENGTH bb.bb_instructions /\
  (EL idx bb.bb_instructions).inst_opcode <> PHI /\
  sue_boundary_defined f bb idx st /\
  MEM (Var v) (EL idx bb.bb_instructions).inst_operands ==>
  v IN FDOM st.vs_vars
Proof
  simp[sue_boundary_defined_def] >> metis_tac[operand_vars_in_fdom]
QED

Theorem sue_boundary_defined_phis:
  strict_dom_vars_defined f st /\
  eval_phis st bb.bb_instructions = OK st_phi ==>
  sue_boundary_defined f bb (phi_prefix_length bb.bb_instructions)
    (st_phi with vs_inst_idx := phi_prefix_length bb.bb_instructions)
Proof
  strip_tac >> simp[sue_boundary_defined_def] >> conj_tac
  >- (drule eval_phis_preserves_current_bb >> strip_tac >>
      drule eval_phis_vars_grow >> strip_tac >>
      gvs[strict_dom_vars_defined_def] >> metis_tac[pred_setTheory.SUBSET_DEF]) >>
  metis_tac[eval_phis_outputs_in_fdom_idx]
QED

Theorem sue_boundary_defined_step:
  sue_boundary_defined f bb idx st /\
  idx < LENGTH bb.bb_instructions /\
  inst = EL idx bb.bb_instructions /\ inst_wf inst /\
  inst.inst_opcode <> PHI /\ ~is_terminator inst.inst_opcode /\
  step_inst fuel ctx inst st = OK st' ==>
  sue_boundary_defined f bb (SUC idx)
    (st' with vs_inst_idx := SUC idx)
Proof
  strip_tac >>
  `FDOM st'.vs_vars = FDOM st.vs_vars UNION set inst.inst_outputs` by
    metis_tac[step_inst_fdom] >>
  `st'.vs_current_bb = st.vs_current_bb` by
    metis_tac[venomInstPropsTheory.step_preserves_control_flow] >>
  gvs[sue_boundary_defined_def, strict_dom_vars_defined_def] >>
  conj_tac
  >- metis_tac[pred_setTheory.IN_UNION] >>
  rpt strip_tac >> Cases_on `j = idx` >> gvs[] >>
  `j < idx` by decide_tac >> metis_tac[pred_setTheory.IN_UNION]
QED

Theorem sue_boundary_defined_exit:
  wf_function f /\ MEM bb f.fn_blocks /\ bb_well_formed bb /\
  EVERY inst_wf bb.bb_instructions /\
  bb.bb_label = st.vs_current_bb /\ idx < LENGTH bb.bb_instructions /\
  is_terminator (EL idx bb.bb_instructions).inst_opcode /\
  sue_boundary_defined f bb idx st /\
  fn_reachable f st.vs_current_bb /\
  fn_cfg_edge f st.vs_current_bb st'.vs_current_bb /\
  FDOM st.vs_vars SUBSET FDOM st'.vs_vars ==>
  strict_dom_vars_defined f st'
Proof
  strip_tac >>
  `idx = PRE (LENGTH bb.bb_instructions)` by
    metis_tac[bb_well_formed_def] >>
  fs[sue_boundary_defined_def] >>
  rw[strict_dom_vars_defined_def] >>
  Cases_on `d_bb.bb_label = bb.bb_label`
  >- (`d_bb = bb` by metis_tac[same_label_same_block] >> gvs[] >>
      `?j. j < LENGTH bb.bb_instructions /\
           EL j bb.bb_instructions = d_inst` by metis_tac[listTheory.MEM_EL] >>
      `inst_wf d_inst` by metis_tac[listTheory.EVERY_MEM] >>
      `~is_terminator d_inst.inst_opcode` by
        metis_tac[terminator_no_outputs, listTheory.MEM] >>
      `j < PRE (LENGTH bb.bb_instructions)` by
        (Cases_on `j = PRE (LENGTH bb.bb_instructions)` >> gvs[] >> decide_tac) >>
      `v IN FDOM st.vs_vars` by metis_tac[] >>
      metis_tac[pred_setTheory.SUBSET_DEF]) >>
  `fn_dominates f d_bb.bb_label st.vs_current_bb` by
    metis_tac[fn_dominates_predecessor] >>
  fs[strict_dom_vars_defined_def] >>
  `v IN FDOM st.vs_vars` by metis_tac[] >>
  metis_tac[pred_setTheory.SUBSET_DEF]
QED

Theorem sue_phi_prefix_boundary_nonphi:
  !insts. phi_prefix_length insts < LENGTH insts ==>
    (EL (phi_prefix_length insts) insts).inst_opcode <> PHI
Proof
  Induct >- simp[phi_prefix_length_def] >>
  gen_tac >> Cases_on `h.inst_opcode = PHI` >>
  simp[phi_prefix_length_def]
QED

Theorem sue_phi_suffix_nonphi:
  bb_well_formed bb /\ phi_prefix_length bb.bb_instructions <= idx /\
  idx < LENGTH bb.bb_instructions ==>
  (EL idx bb.bb_instructions).inst_opcode <> PHI
Proof
  strip_tac >>
  `phi_prefix_length bb.bb_instructions < LENGTH bb.bb_instructions` by
    decide_tac >>
  drule sue_phi_prefix_boundary_nonphi >> strip_tac >>
  spose_not_then assume_tac >>
  drule_all phi_before_non_phi >> decide_tac
QED

Theorem sue_terminator_cfg_edge:
  MEM bb f.fn_blocks /\ bb.bb_label = st.vs_current_bb /\
  bb_well_formed bb /\ EVERY inst_wf bb.bb_instructions /\
  idx < LENGTH bb.bb_instructions /\ inst = EL idx bb.bb_instructions /\
  is_terminator inst.inst_opcode /\
  step_inst fuel ctx inst st = OK st' /\ ~st'.vs_halted ==>
  fn_cfg_edge f st.vs_current_bb st'.vs_current_bb
Proof
  strip_tac >>
  `inst.inst_opcode <> INVOKE` by (strip_tac >> gvs[is_terminator_def]) >>
  `step_inst_base inst st = OK st'` by
    gvs[Once step_inst_def] >>
  `inst_wf inst` by metis_tac[listTheory.EVERY_EL] >>
  `MEM st'.vs_current_bb (get_successors inst)` by
    metis_tac[step_inst_base_term_succs] >>
  `idx = PRE (LENGTH bb.bb_instructions)` by
    metis_tac[bb_well_formed_def] >>
  `LAST bb.bb_instructions = inst` by
    (gvs[bb_well_formed_def] >> simp[listTheory.LAST_EL]) >>
  simp[fn_cfg_edge_def] >> qexists_tac `bb` >>
  Cases_on `bb.bb_instructions` >>
  gvs[venomInstTheory.bb_succs_def, listTheory.MEM_nub]
QED

Theorem sue_terminator_domain_mono:
  step_inst fuel ctx inst st = OK st' /\ is_terminator inst.inst_opcode ==>
  FDOM st.vs_vars SUBSET FDOM st'.vs_vars
Proof
  strip_tac >> simp[pred_setTheory.SUBSET_DEF] >>
  metis_tac[lookup_var_fdom, step_terminator_preserves_vars]
QED

Theorem sue_state_rel_eval_operand:
  sue_state_rel protected st tt /\
  (!v. op = Var v ==> v IN protected) ==>
  eval_operand op tt = eval_operand op st
Proof
  Cases_on `op` >>
  simp[sue_state_rel_def, eval_operand_def, lookup_var_def] >>
  rpt strip_tac >>
  `st.vs_labels = tt.vs_labels` by
    (irule execution_frame_projection >> simp[execution_frame_def]) >> simp[]
QED

Theorem sue_assign_step:
  inst.inst_opcode = ASSIGN /\ inst.inst_operands = [op] /\
  inst.inst_outputs = [v] /\ eval_operand op st = SOME w ==>
  step_inst fuel ctx inst st = OK (st with vs_vars := st.vs_vars |+ (v,w))
Proof
  simp[Once step_inst_def] >>
  simp[Once step_inst_base_def, update_var_def]
QED

Theorem sue_assign_prefix_success:
  !assigns protected st tt fuel ctx.
    sue_state_rel protected st tt /\
    EVERY (\a. ?op dst.
      a.inst_opcode = ASSIGN /\ a.inst_operands = [op] /\
      a.inst_outputs = [dst] /\ ~(dst IN protected) /\
      (!v. op = Var v ==> v IN protected) /\
      IS_SOME (eval_operand op st)) assigns ==>
    ?tt'. run_insts fuel ctx assigns tt = OK tt' /\
          sue_state_rel protected st tt' /\ tt'.vs_inst_idx = tt.vs_inst_idx
Proof
  Induct >> rpt gen_tac
  >- simp[analysisSimDefsTheory.run_insts_def] >>
  strip_tac >> fs[listTheory.EVERY_DEF] >>
  `eval_operand op tt = eval_operand op st` by
    metis_tac[sue_state_rel_eval_operand] >>
  Cases_on `eval_operand op st` >> gvs[] >>
  `step_inst fuel ctx h tt = OK (tt with vs_vars := tt.vs_vars |+ (dst,x))` by
    metis_tac[sue_assign_step] >>
  `sue_state_rel protected st (tt with vs_vars := tt.vs_vars |+ (dst,x))` by
    metis_tac[sue_state_rel_fresh_write] >>
  first_x_assum drule >> disch_then drule >>
  disch_then (qspecl_then [`fuel`, `ctx`] strip_assume_tac) >>
  qexists_tac `tt'` >> simp[analysisSimDefsTheory.run_insts_def] >>
  metis_tac[]
QED

Theorem sue_alloc_assign_supply_shape:
  sue_alloc_assign_supply s op = (a,newop,s') ==>
  a.inst_opcode = ASSIGN /\ a.inst_operands = [op]
Proof
  simp[sue_alloc_assign_supply_def, AllCaseEqs()] >> rpt strip_tac >> gvs[]
QED

Theorem sue_expand_ops_supply_copy_sources:
  !ops dfg inst s k assigns new_ops s'.
    sue_expand_ops_supply dfg inst s ops k = (assigns,new_ops,s') ==>
    EVERY (\a. ?op. MEM op ops /\ (!l. op <> Label l) /\
                       a.inst_opcode = ASSIGN /\ a.inst_operands = [op]) assigns
Proof
  Induct >> rpt gen_tac
  >- simp[sue_expand_ops_supply_def] >>
  strip_tac >>
  Cases_on `sue_expand_ops_supply dfg inst s ops (k + 1)` >>
  PairCases_on `r` >>
  first_x_assum drule >> strip_tac >>
  gvs[sue_expand_ops_supply_def] >>
  Cases_on `sue_needs_assign dfg inst k` >> gvs[]
  >- (Cases_on `h` >> gvs[AllCaseEqs()] >>
      imp_res_tac sue_alloc_assign_supply_shape >>
      gvs[listTheory.EVERY_MEM] >> metis_tac[]) >>
  gvs[listTheory.EVERY_MEM] >> metis_tac[]
QED

Theorem sue_expand_ops_supply_copies_ready:
  ir_supply_inst_ok s /\
  sue_expand_ops_supply dfg inst s ops k = (assigns,new_ops,s') /\
  protected SUBSET set s.irs_used_vars /\
  (!v. MEM (Var v) ops ==> v IN protected) /\
  (!a v. MEM a assigns /\ a.inst_operands = [Var v] ==>
         v IN FDOM st.vs_vars) ==>
  EVERY (\a. ?op dst.
    a.inst_opcode = ASSIGN /\ a.inst_operands = [op] /\
    a.inst_outputs = [dst] /\ ~(dst IN protected) /\
    (!v. op = Var v ==> v IN protected) /\
    IS_SOME (eval_operand op st)) assigns
Proof
  strip_tac >>
  drule_all sue_expand_ops_supply_prefix >> strip_tac >>
  drule sue_expand_ops_supply_copy_sources >> strip_tac >>
  fs[listTheory.EVERY_MEM] >> rpt strip_tac >>
  rename1 `MEM a assigns` >>
  `?op. MEM op ops /\ (!l. op <> Label l) /\
        a.inst_opcode = ASSIGN /\ a.inst_operands = [op]` by metis_tac[] >>
  `LENGTH a.inst_outputs = 1` by metis_tac[] >>
  `?dst. a.inst_outputs = [dst]` by
    (Cases_on `a.inst_outputs` >> gvs[] >>
     rename1 `LENGTH tail = 0` >> Cases_on `tail` >> gvs[]) >>
  `~(dst IN protected)` by
    (fs[pred_setTheory.SUBSET_DEF, listTheory.MEM_FLAT, listTheory.MEM_MAP] >>
     metis_tac[listTheory.MEM]) >>
  qexistsl_tac [`op`, `dst`] >> simp[] >> conj_tac
  >- metis_tac[] >>
  Cases_on `op` >> gvs[eval_operand_def, lookup_var_def] >>
  rename1 `a.inst_operands = [Var v]` >>
  `v IN FDOM st.vs_vars` by metis_tac[] >>
  simp[finite_mapTheory.FLOOKUP_DEF]
QED

Theorem sue_expand_ops_supply_prefix_success:
  ir_supply_inst_ok s /\
  sue_expand_ops_supply dfg inst s ops k = (assigns,new_ops,s') /\
  protected SUBSET set s.irs_used_vars /\
  (!v. MEM (Var v) ops ==> v IN protected) /\
  (!a v. MEM a assigns /\ a.inst_operands = [Var v] ==>
         v IN FDOM st.vs_vars) /\ sue_state_rel protected st tt ==>
  ?tt'. run_insts fuel ctx (TAKE n assigns) tt = OK tt' /\
        sue_state_rel protected st tt' /\ tt'.vs_inst_idx = tt.vs_inst_idx
Proof
  strip_tac >> irule sue_assign_prefix_success >> simp[] >>
  irule rich_listTheory.EVERY_TAKE >>
  irule sue_expand_ops_supply_copies_ready >> metis_tac[]
QED

Theorem sue_run_insts_preserves_lookup:
  !insts fuel ctx st tt v.
    EVERY (\a. ~MEM v a.inst_outputs /\ ~is_terminator a.inst_opcode) insts /\
    run_insts fuel ctx insts st = OK tt ==>
    lookup_var v tt = lookup_var v st
Proof
  Induct >> rpt gen_tac
  >- simp[analysisSimDefsTheory.run_insts_def] >>
  strip_tac >> fs[listTheory.EVERY_DEF, analysisSimDefsTheory.run_insts_def] >>
  Cases_on `step_inst fuel ctx h st` >> gvs[] >>
  metis_tac[venomInstPropsTheory.step_preserves_non_output_vars]
QED

Theorem sue_assign_prefix_rel:
  !assigns fuel ctx st tt uu protected.
    EVERY (\a. a.inst_opcode = ASSIGN /\
               EVERY (\v. ~(v IN protected)) a.inst_outputs) assigns /\
    sue_state_rel protected st tt /\
    run_insts fuel ctx assigns tt = OK uu ==>
    sue_state_rel protected st uu
Proof
  Induct >> rpt gen_tac
  >- (simp[analysisSimDefsTheory.run_insts_def] >> metis_tac[]) >>
  strip_tac >> fs[listTheory.EVERY_DEF, analysisSimDefsTheory.run_insts_def] >>
  Cases_on `step_inst fuel ctx h tt` >> gvs[] >>
  gvs[Once step_inst_def, Once step_inst_base_def, AllCaseEqs(), update_var_def] >>
  metis_tac[sue_state_rel_fresh_write]
QED

(* Shared branch tactics keep the operand induction direct, without sharing
   suspension labels between distinct sequents. *)
local
val unchanged_operand_tac =
  `sue_state_rel protected st uu` by
    (irule sue_assign_prefix_rel >> goal_assum (drule_at Any) >>
     simp[] >> drule_all sue_expand_ops_supply_prefix >>
     strip_tac >> gvs[listTheory.EVERY_MEM] >>
     fs[pred_setTheory.SUBSET_DEF, listTheory.MEM_FLAT, listTheory.MEM_MAP] >>
     metis_tac[]) >>
  simp[] >> conj_tac
  >- (irule sue_state_rel_eval_operand >> qexists_tac `protected` >> simp[] >> metis_tac[]) >>
  `!v. MEM (Var v) ops ==> v IN protected` by metis_tac[] >>
  qpat_x_assum `!dfg inst s k assigns new_ops s' protected st tt uu fuel ctx. _`
    drule_all >> simp[];

val copied_operand_tac =
  drule_all sue_alloc_assign_supply_contract >> strip_tac >>
  drule sue_alloc_assign_supply_shape >> strip_tac >>
  gvs[analysisSimDefsTheory.run_insts_def, AllCaseEqs()] >> (
  rename1 `assign_inst.inst_outputs = [dst]` >>
  `~(dst IN protected)` by
    (fs[sue_supply_extends_def, pred_setTheory.SUBSET_DEF] >> metis_tac[listTheory.MEM_APPEND]) >>
  `EVERY (\a. ~MEM dst a.inst_outputs /\ ~is_terminator a.inst_opcode) tail_as` by
    (drule_all sue_expand_ops_supply_prefix >> strip_tac >>
     fs[listTheory.EVERY_MEM, listTheory.MEM_FLAT, listTheory.MEM_MAP] >>
     metis_tac[is_terminator_def]) >>
  drule_all sue_run_insts_preserves_lookup >> strip_tac >>
  gvs[Once step_inst_def, Once step_inst_base_def, AllCaseEqs(), update_var_def] >>
  rename1 `run_insts fuel ctx tail_as (tt with vs_vars := tt.vs_vars |+ (dst,value)) = OK uu` >>
  conj_tac
  >- (fs[eval_operand_def, lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE,
         sue_state_rel_def] >> metis_tac[]) >>
  `sue_state_rel protected st (tt with vs_vars := tt.vs_vars |+ (dst,value))` by
    (irule sue_state_rel_fresh_write >> simp[]) >>
  `!v. MEM (Var v) ops ==> v IN protected` by metis_tac[] >>
  qpat_x_assum `!dfg inst s k assigns new_ops s' protected st tt uu fuel ctx. _`
    drule_all >> simp[]);
in

Theorem sue_expand_ops_supply_eval:
  !ops dfg inst s k assigns new_ops s' protected st tt uu fuel ctx.
    ir_supply_inst_ok s /\
    sue_expand_ops_supply dfg inst s ops k = (assigns,new_ops,s') /\
    protected SUBSET set s.irs_used_vars /\
    (!v. MEM (Var v) ops ==> v IN protected) /\
    sue_state_rel protected st tt /\
    run_insts fuel ctx assigns tt = OK uu ==>
    LIST_REL (\op newop. eval_operand newop uu = eval_operand op st) ops new_ops
Proof
  Induct >> rpt gen_tac
  >- simp[sue_expand_ops_supply_def] >>
  strip_tac >>
  Cases_on `sue_expand_ops_supply dfg inst s ops (k + 1)` >>
  PairCases_on `r` >>
  rename1 `sue_expand_ops_supply dfg inst s ops (k + 1) = (tail_as,tail_ops,s1)` >>
  `sue_supply_extends s s1` by metis_tac[sue_expand_ops_supply_extends] >>
  `ir_supply_inst_ok s1` by gvs[sue_supply_extends_def] >>
  `!v. MEM (Var v) ops ==> v IN protected` by metis_tac[listTheory.MEM] >>
  `!v. h = Var v ==> v IN protected` by metis_tac[listTheory.MEM] >>
  Cases_on `sue_needs_assign dfg inst k`
  >- (Cases_on `h`
      >- (gvs[Once sue_expand_ops_supply_def, AllCaseEqs()] >> copied_operand_tac)
      >- (rename1 `Var v` >>
          Cases_on `LENGTH (dfg_get_uses dfg v) = 1 /\ sue_count_remaining (Var v) ops = 0`
          >- (gvs[Once sue_expand_ops_supply_def] >> unchanged_operand_tac) >>
          gvs[Once sue_expand_ops_supply_def, AllCaseEqs()] >> copied_operand_tac) >>
      gvs[Once sue_expand_ops_supply_def] >> unchanged_operand_tac) >>
  gvs[Once sue_expand_ops_supply_def] >> unchanged_operand_tac
QED

end

Theorem sue_expand_ops_supply_sim:
  ir_supply_inst_ok s /\
  sue_expand_ops_supply dfg inst s ops k = (assigns,new_ops,s') /\
  protected SUBSET set s.irs_used_vars /\
  (!v. MEM (Var v) ops ==> v IN protected) /\
  (!a v. MEM a assigns /\ a.inst_operands = [Var v] ==>
         v IN FDOM st.vs_vars) /\ sue_state_rel protected st tt ==>
  ?uu. run_insts fuel ctx assigns tt = OK uu /\
       sue_state_rel protected st uu /\ uu.vs_inst_idx = tt.vs_inst_idx /\
       LIST_REL (\op newop. eval_operand newop uu = eval_operand op st) ops new_ops
Proof
  strip_tac >> drule_all sue_expand_ops_supply_prefix_success >>
  disch_then (qspecl_then [`LENGTH assigns`, `fuel`, `ctx`] strip_assume_tac) >>
  gvs[] >>
  drule_all sue_expand_ops_supply_eval >> simp[]
QED

Definition sue_term_rel_def:
  sue_term_rel protected st tt <=>
    execution_frame st = execution_frame tt /\
    (!v. v IN protected ==> FLOOKUP st.vs_vars v = FLOOKUP tt.vs_vars v)
End

Definition sue_result_rel_def:
  sue_result_rel protected r r' <=>
    lift_result (sue_state_rel protected) (sue_term_rel protected)
                (sue_term_rel protected) r r'
End

Theorem sue_term_rel_execution_equiv:
  sue_term_rel protected st tt <=> execution_equiv (COMPL protected) st tt
Proof
  simp[sue_term_rel_def, execution_equiv_def, lookup_var_def] >> metis_tac[]
QED

Theorem sue_state_rel_idx[simp]:
  sue_state_rel protected (st with vs_inst_idx := n) (tt with vs_inst_idx := m) <=>
  sue_state_rel protected st tt
Proof
  simp[sue_state_rel_def]
QED

Theorem sue_term_rel_idx[simp]:
  sue_term_rel protected (st with vs_inst_idx := n) (tt with vs_inst_idx := m) <=>
  sue_term_rel protected st tt
Proof
  simp[sue_term_rel_def]
QED

Theorem sue_state_rel_state_equiv:
  sue_state_rel protected st tt <=>
  state_equiv (COMPL protected) (st with vs_inst_idx := 0) (tt with vs_inst_idx := 0)
Proof
  simp[state_equiv_def, execution_equiv_def, sue_state_rel_def, lookup_var_def] >>
  metis_tac[]
QED

Theorem sue_result_rel_idx[simp]:
  sue_result_rel protected
    (exec_result_map (\u. u with vs_inst_idx := n) r)
    (exec_result_map (\u. u with vs_inst_idx := m) r') <=>
  sue_result_rel protected r r'
Proof
  Cases_on `r` >> Cases_on `r'` >>
  simp[sue_result_rel_def, lift_result_def, exec_result_map_def]
QED

Theorem sue_setup_callee_idx[local]:
  setup_callee fn args (s with vs_inst_idx := n) = setup_callee fn args s
Proof
  simp[setup_callee_def]
QED

Theorem sue_fold_updates_idx[local]:
  !xs s. FOLDL (\st (v,w). update_var v w st)
    (s with vs_inst_idx := n) xs =
    (FOLDL (\st (v,w). update_var v w st) s xs) with vs_inst_idx := n
Proof
  Induct >> simp[] >> Cases_on `h` >> gen_tac >>
  `update_var q r (s with vs_inst_idx := n) =
   (update_var q r s) with vs_inst_idx := n` by simp[update_var_def] >>
  simp[]
QED

Theorem sue_bind_outputs_idx[local]:
  bind_outputs outs vals (s with vs_inst_idx := n) =
  OPTION_MAP (\st. st with vs_inst_idx := n) (bind_outputs outs vals s)
Proof
  Cases_on `LENGTH outs = LENGTH vals` >>
  simp[bind_outputs_def, sue_fold_updates_idx]
QED

Theorem sue_merge_callee_idx[local]:
  merge_callee_state (s with vs_inst_idx := n) t =
  (merge_callee_state s t) with vs_inst_idx := n
Proof
  simp[merge_callee_state_def]
QED

Theorem sue_adopt_return_idx[local]:
  adopt_return_fmp ret (s with vs_inst_idx := n) =
  (adopt_return_fmp ret s) with vs_inst_idx := n
Proof
  Cases_on `ret.iret_adopt_fmp` >> simp[adopt_return_fmp_def]
QED

Theorem sue_step_inst_idx_norm:
  !fuel ctx inst s n.
  exec_result_map (\u. u with vs_inst_idx := 0)
    (step_inst fuel ctx inst (s with vs_inst_idx := n)) =
  exec_result_map (\u. u with vs_inst_idx := 0)
    (step_inst fuel ctx inst s)
Proof
  rpt gen_tac >> Cases_on `inst.inst_opcode = INVOKE`
  >- (simp[Once step_inst_def] >>
      simp[Once step_inst_def, eval_ops_inst_idx, sue_setup_callee_idx,
           sue_merge_callee_idx, sue_adopt_return_idx, sue_bind_outputs_idx] >>
      Cases_on `decode_invoke inst` >> simp[] >>
      rename1 `SOME p` >> PairCases_on `p` >> simp[] >>
      Cases_on `lookup_function p0 ctx.ctx_functions` >> simp[] >>
      Cases_on `eval_operands p1 s` >> simp[] >>
      rename1 `setup_callee fn args s` >>
      Cases_on `setup_callee fn args s` >> simp[] >>
      rename1 `run_blocks fuel ctx fn callee` >>
      Cases_on `run_blocks fuel ctx fn callee` >> simp[exec_result_map_def] >>
      rename1 `bind_outputs inst.inst_outputs ret.iret_values st` >>
      Cases_on `bind_outputs inst.inst_outputs ret.iret_values st` >>
      simp[exec_result_map_def]) >>
  simp[step_inst_non_invoke] >>
  Cases_on `is_terminator inst.inst_opcode`
  >- metis_tac[terminator_step_inst_base_idx_norm0] >>
  simp[step_inst_inst_idx_indep] >>
  Cases_on `step_inst_base inst s` >> simp[exec_result_map_def]
QED

Theorem sue_lift_result_state_equiv[local]:
  lift_result (state_equiv (COMPL P)) (execution_equiv (COMPL P))
    (execution_equiv (COMPL P)) r r' ==>
  sue_result_rel P r r'
Proof
  Cases_on `r` >> Cases_on `r'` >>
  simp[lift_result_def, sue_result_rel_def, sue_term_rel_execution_equiv] >>
  simp[state_equiv_def, execution_equiv_def, sue_state_rel_def, lookup_var_def] >>
  metis_tac[]
QED

Theorem sue_step_inst_preserves:
  sue_state_rel P s t /\
  (!x. MEM (Var x) inst.inst_operands ==> x IN P) ==>
  sue_result_rel P (step_inst fuel ctx inst s) (step_inst fuel ctx inst t)
Proof
  rpt strip_tac >>
  `state_equiv (COMPL P) (s with vs_inst_idx := 0)
                         (t with vs_inst_idx := 0)` by
    simp[GSYM sue_state_rel_state_equiv] >>
  `!x. MEM (Var x) inst.inst_operands ==>
       lookup_var x (s with vs_inst_idx := 0) =
       lookup_var x (t with vs_inst_idx := 0)` by
    (gvs[sue_state_rel_def, lookup_var_def] >> metis_tac[]) >>
  `sue_result_rel P (step_inst fuel ctx inst (s with vs_inst_idx := 0))
                    (step_inst fuel ctx inst (t with vs_inst_idx := 0))` by
    (irule sue_lift_result_state_equiv >>
     irule step_inst_preserves_R_proof >>
     simp[state_equiv_execution_equiv_valid_state_rel_proof]) >>
  `sue_result_rel P
     (exec_result_map (\u. u with vs_inst_idx := 0)
       (step_inst fuel ctx inst (s with vs_inst_idx := 0)))
     (exec_result_map (\u. u with vs_inst_idx := 0)
       (step_inst fuel ctx inst (t with vs_inst_idx := 0)))` by simp[] >>
  qpat_x_assum `sue_result_rel _ (exec_result_map _ _) _` mp_tac >>
  pure_rewrite_tac[sue_step_inst_idx_norm] >> simp[]
QED

Theorem sue_step_inst_rewritten:
  sue_state_rel P s t /\
  (!x. MEM (Var x) inst.inst_operands ==> x IN P) /\
  inst_wf inst /\ ~is_alloca_op inst.inst_opcode /\
  inst.inst_opcode <> PARAM /\ inst.inst_opcode <> FMP_PARAM /\
  inst.inst_opcode <> RETPC_PARAM /\ inst.inst_opcode <> PHI /\
  LENGTH ops = LENGTH inst.inst_operands /\
  (inst.inst_opcode = DRET ==>
    parse_dret_shape (inst with inst_operands := ops) = parse_dret_shape inst) /\
  (!i. i < LENGTH inst.inst_operands ==>
    eval_operand (EL i ops) t = eval_operand (EL i inst.inst_operands) t) /\
  (!i. i < LENGTH inst.inst_operands ==>
    !lbl. EL i inst.inst_operands = Label lbl ==> EL i ops = Label lbl) /\
  (inst.inst_opcode = LOG ==> HD ops = HD inst.inst_operands) ==>
  sue_result_rel P (step_inst fuel ctx inst s)
    (step_inst fuel ctx (inst with inst_operands := ops) t)
Proof
  strip_tac >> drule_all step_inst_operands_equiv >>
  disch_then (qspecl_then [`fuel`, `ctx`] assume_tac) >>
  simp[] >> irule sue_step_inst_preserves >> simp[]
QED

Theorem sue_expand_ops_supply_structure:
  sue_expand_ops_supply dfg inst s inst.inst_operands 0 = (assigns,ops,s') ==>
  LENGTH ops = LENGTH inst.inst_operands /\
  (!i. i < LENGTH inst.inst_operands ==>
    !lbl. EL i inst.inst_operands = Label lbl ==> EL i ops = Label lbl) /\
  (inst.inst_opcode = LOG ==> HD ops = HD inst.inst_operands) /\
  (inst.inst_opcode = DRET ==>
    parse_dret_shape (inst with inst_operands := ops) = parse_dret_shape inst)
Proof
  strip_tac >>
  drule sue_expand_ops_supply_operand_labels >> strip_tac >>
  `LENGTH ops = LENGTH inst.inst_operands` by
    metis_tac[listTheory.LENGTH_MAP] >> simp[] >>
  conj_tac
  >- (rpt strip_tac >>
      `EL i (MAP sue_operand_label ops) =
       EL i (MAP sue_operand_label inst.inst_operands)` by simp[] >>
      gvs[listTheory.EL_MAP, sue_operand_label_def] >>
      Cases_on `EL i ops` >> gvs[sue_operand_label_def]) >>
  `inst.inst_opcode = LOG \/ inst.inst_opcode = DRET ==>
   HD ops = HD inst.inst_operands` by
    (disch_tac >> Cases_on `inst.inst_operands`
     >- gvs[sue_expand_ops_supply_def] >>
     `?rest. ops = h::rest` by metis_tac[sue_expand_ops_supply_structural_head] >>
     simp[]) >>
  simp[] >> strip_tac >>
  Cases_on `inst.inst_operands`
  >- gvs[sue_expand_ops_supply_def, dretShapeDefsTheory.parse_dret_shape_def] >>
  `?rest. ops = h::rest` by metis_tac[sue_expand_ops_supply_structural_head] >>
  gvs[dretShapeDefsTheory.parse_dret_shape_def]
QED

Theorem sue_expand_ops_supply_step_sim:
  ir_supply_inst_ok supply /\
  sue_expand_ops_supply dfg inst supply inst.inst_operands 0 = (assigns,ops,supply') /\
  P SUBSET set supply.irs_used_vars /\
  (!v. MEM (Var v) inst.inst_operands ==> v IN P) /\
  (!a v. MEM a assigns /\ a.inst_operands = [Var v] ==> v IN FDOM s.vs_vars) /\
  sue_state_rel P s t /\ inst_wf inst /\
  ~is_alloca_op inst.inst_opcode /\ ~sue_should_skip inst.inst_opcode ==>
  ?u. run_insts fuel ctx assigns t = OK u /\ sue_state_rel P s u /\
      u.vs_inst_idx = t.vs_inst_idx /\
      sue_result_rel P (step_inst fuel ctx inst s)
        (step_inst fuel ctx (inst with inst_operands := ops) u)
Proof
  strip_tac >> drule_all sue_expand_ops_supply_sim >>
  disch_then (qspecl_then [`fuel`, `ctx`] strip_assume_tac) >>
  qexists_tac `uu` >> simp[] >>
  drule sue_expand_ops_supply_structure >> strip_tac >>
  gvs[sue_should_skip_def, is_param_opcode_iff] >>
  irule sue_step_inst_rewritten >> simp[] >>
  rpt strip_tac >>
  `eval_operand (EL i ops) uu = eval_operand (EL i inst.inst_operands) s` by
    (fs[listTheory.LIST_REL_EL_EQN] >> metis_tac[]) >>
  `eval_operand (EL i inst.inst_operands) s =
   eval_operand (EL i inst.inst_operands) uu` by
    (sym_tac >> irule sue_state_rel_eval_operand >> qexists_tac `P` >> simp[] >>
     rpt strip_tac >> first_x_assum irule >>
     simp[listTheory.MEM_EL] >> qexists_tac `i` >> simp[]) >> simp[]
QED

Theorem sue_run_blocks_never_ok:
  !fuel ctx fn s st. run_blocks fuel ctx fn s <> OK st
Proof
  Induct >- simp[Once run_blocks_def] >>
  simp[Once run_blocks_unfold] >> rpt gen_tac >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >> simp[] >>
  rename1 `run_block fuel ctx bb s` >>
  Cases_on `run_block fuel ctx bb s` >> simp[] >>
  IF_CASES_TAC >> simp[]
QED
