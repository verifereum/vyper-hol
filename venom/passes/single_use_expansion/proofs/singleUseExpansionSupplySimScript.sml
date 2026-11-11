(* Supply expansion: structural and semantic segment interfaces. *)
Theory singleUseExpansionSupplySim
Ancestors
  singleUseExpansionSupplyProofs singleUseExpansionDefs irSupply
  stateFrame stateEquiv venomExecProps venomExecProofs
  venomExecSemantics venomWf venomInst venomState
  analysisSimDefs instIdxIndep execEquivParamProofs passSharedSubst
  venomFnScheduleRunner ctxLookupAgreeHelpers cfgWf contextCodegenRelProps
  venomWfProps

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
  rpt strip_tac >> drule sue_expand_ops_supply_copies >>
  rw[listTheory.EVERY_MEM] >> first_x_assum drule >> rw[] >>
  first_assum (irule_at Any) >> simp[]
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

Theorem sue_segments_supply_index_ready:
  sue_segments_supply dfg supply insts = (segs,supply') /\
  ir_supply_inst_ok supply /\ P SUBSET set supply.irs_used_vars /\ i < LENGTH insts ==>
  ?si sj. sue_expand_inst_supply dfg si (EL i insts) = (EL i segs,sj) /\
          ir_supply_inst_ok si /\ P SUBSET set si.irs_used_vars
Proof
  strip_tac >> drule_all sue_segments_supply_index >> strip_tac >>
  qexistsl [`si`, `sj`] >> simp[] >>
  gvs[sue_supply_extends_def] >>
  fs[pred_setTheory.SUBSET_DEF] >> metis_tac[listTheory.MEM_APPEND]
QED

Theorem sue_function_lookup_ready:
  sue_expand_function_supply supply fn = (fn',supply') /\
  ir_supply_inst_ok supply /\ ir_supply_covers_fn supply fn /\
  lookup_block lbl fn.fn_blocks = SOME bb ==>
  ?bb' si sj segs. lookup_block lbl fn'.fn_blocks = SOME bb' /\
    sue_segments_supply (dfg_build_function fn) si bb.bb_instructions = (segs,sj) /\
    bb' = bb with bb_instructions := FLAT segs /\
    ir_supply_inst_ok si /\ set (fn_ir_vars fn) SUBSET set si.irs_used_vars
Proof
  strip_tac >> drule_all sue_expand_function_supply_lookup >> strip_tac >>
  drule sue_expand_block_supply_segments >> strip_tac >>
  qexistsl [`bb'`, `si`, `sj`, `segs`] >> simp[] >>
  gvs[sue_supply_extends_def, ir_supply_covers_fn_def,
      list_subset_def, listTheory.EVERY_MEM,
      pred_setTheory.SUBSET_DEF] >>
  metis_tac[listTheory.MEM_APPEND]
QED

Theorem sue_segment_offset_drop:
  !segs i. i < LENGTH segs ==>
  DROP (sue_segment_offset segs i) (FLAT segs) =
    EL i segs ++ FLAT (DROP (SUC i) segs)
Proof
  Induct >> Cases_on `i` >> simp[sue_segment_offset_cons,
    listTheory.DROP_APPEND, listTheory.DROP_LENGTH_TOO_LONG] >>
  rpt strip_tac >> first_x_assum irule >> simp[]
QED

Theorem sue_assign_step_idx[local]:
  a.inst_opcode = ASSIGN ==>
  step_inst fuel ctx a (t with vs_inst_idx := k) =
  exec_result_map (\u. u with vs_inst_idx := k) (step_inst fuel ctx a t)
Proof
  strip_tac >> simp[Once step_inst_def] >>
  simp[Once step_inst_def] >>
  irule step_inst_inst_idx_indep >> simp[is_terminator_def]
QED

Theorem sue_drop_cons_index[local]:
  !xs k. DROP k xs = h::tail ==>
    k < LENGTH xs /\ EL k xs = h /\ DROP (SUC k) xs = tail
Proof
  Induct >> Cases_on `k` >> simp[] >> metis_tac[]
QED

Theorem sue_exec_block_assign_prefix:
  !assigns k bb tail t u.
  EVERY (\a. a.inst_opcode = ASSIGN) assigns /\
  DROP k bb.bb_instructions = assigns ++ tail /\
  run_insts fuel ctx assigns t = OK u ==>
  exec_block fuel ctx bb (t with vs_inst_idx := k) =
  exec_block fuel ctx bb (u with vs_inst_idx := k + LENGTH assigns)
Proof
  Induct >> rpt gen_tac
  >- simp[run_insts_def] >>
  strip_tac >> fs[] >>
  `k < LENGTH bb.bb_instructions /\ EL k bb.bb_instructions = h` by
    metis_tac[sue_drop_cons_index] >>
  `DROP (SUC k) bb.bb_instructions = assigns ++ tail` by
    metis_tac[sue_drop_cons_index] >>
  Cases_on `step_inst fuel ctx h t` >>
  gvs[run_insts_def] >>
  simp[Once exec_block_def, get_instruction_def, sue_assign_step_idx,
       is_terminator_def, exec_result_map_def] >>
  first_x_assum (qspec_then `SUC k` mp_tac) >>
  pure_rewrite_tac[arithmeticTheory.ADD_CLAUSES] >>
  disch_then irule >> simp[]
QED

Theorem sue_segments_phi_offset:
  !insts dfg supply segs supply'.
    ir_supply_inst_ok supply /\
    sue_segments_supply dfg supply insts = (segs,supply') ==>
    sue_segment_offset segs (phi_prefix_length insts) = phi_prefix_length insts
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- gvs[sue_segments_supply_def, phi_prefix_length_def] >>
  Cases_on `sue_expand_inst_supply dfg supply h` >>
  Cases_on `sue_segments_supply dfg r insts` >>
  gvs[sue_segments_supply_def] >>
  Cases_on `h.inst_opcode = PHI`
  >- (`sue_should_skip h.inst_opcode` by simp[sue_should_skip_def] >>
      drule_all sue_expand_inst_supply_skip >> strip_tac >> gvs[] >>
      first_x_assum drule_all >> simp[phi_prefix_length_def]) >>
  simp[phi_prefix_length_def]
QED

Theorem sue_eval_phis_idx[local]:
  !insts s n.
    eval_phis (s with vs_inst_idx := n) insts =
    exec_result_map (\u. u with vs_inst_idx := n) (eval_phis s insts)
Proof
  Induct >> rpt gen_tac >> simp[eval_phis_def, exec_result_map_def] >>
  `!op. eval_operand op (s with vs_inst_idx := n) = eval_operand op s` by
    (Cases >> simp[eval_operand_def, lookup_var_def]) >>
  `eval_one_phi (s with vs_inst_idx := n) h = eval_one_phi s h` by
    simp[eval_one_phi_def] >>
  simp[] >> Cases_on `h.inst_opcode = PHI` >> simp[] >>
  Cases_on `eval_one_phi s h` >> simp[exec_result_map_def] >>
  PairCases_on `x` >> simp[] >>
  Cases_on `eval_phis s insts` >>
  simp[exec_result_map_def, update_var_def]
QED

Theorem sue_eval_phis_shape[local]:
  !insts s. (?u. eval_phis s insts = OK u) \/
    eval_phis s insts = Error "phi evaluation failed"
Proof
  Induct >> simp[eval_phis_def] >> rpt gen_tac >>
  Cases_on `h.inst_opcode = PHI` >> simp[] >>
  Cases_on `eval_one_phi s h` >> simp[] >> PairCases_on `x` >>
  first_x_assum (qspec_then `s` strip_assume_tac) >> simp[]
QED

Theorem sue_eval_phis_rel_normalized[local]:
  sue_state_rel P s t /\ s.vs_inst_idx = t.vs_inst_idx /\
  EVERY (\inst. inst.inst_opcode = PHI ==>
    !v. MEM (Var v) inst.inst_operands ==> v IN P) insts ==>
  sue_result_rel P (eval_phis s insts) (eval_phis t insts)
Proof
  strip_tac >>
  qspecl_then [`insts`,`s`] strip_assume_tac sue_eval_phis_shape
  >- (drule_all sue_eval_phis_entry >> strip_tac >>
      simp[sue_result_rel_def, lift_result_def]) >>
  qspecl_then [`insts`,`t`] strip_assume_tac sue_eval_phis_shape
  >- (`sue_state_rel P t s` by
        (gvs[sue_state_rel_def] >> metis_tac[]) >>
      `t.vs_inst_idx = s.vs_inst_idx` by simp[] >>
      drule_all sue_eval_phis_entry >> strip_tac >> gvs[]) >>
  simp[sue_result_rel_def, lift_result_def]
QED

Theorem sue_expanded_phi_entry:
  ir_supply_inst_ok supply /\
  sue_segments_supply dfg supply bb.bb_instructions = (segs,supply') /\
  EVERY (\inst. inst.inst_opcode = PHI ==>
    !v. MEM (Var v) inst.inst_operands ==> v IN P) bb.bb_instructions /\
  sue_state_rel P s t ==>
  sue_result_rel P (eval_phis s bb.bb_instructions) (eval_phis t (FLAT segs))
Proof
  strip_tac >> drule sue_segments_supply_flat >> strip_tac >>
  drule_all sue_expand_insts_supply_phis >>
  disch_then (qspec_then `t` strip_assume_tac) >> simp[] >>
  `sue_result_rel P
     (eval_phis (s with vs_inst_idx := 0) bb.bb_instructions)
     (eval_phis (t with vs_inst_idx := 0) bb.bb_instructions)` by
    (irule sue_eval_phis_rel_normalized >> simp[]) >>
  gvs[sue_eval_phis_idx]
QED

Theorem sue_expanded_phi_entry_ok:
  ir_supply_inst_ok supply /\
  sue_segments_supply dfg supply bb.bb_instructions = (segs,supply') /\
  EVERY (\inst. inst.inst_opcode = PHI ==>
    !v. MEM (Var v) inst.inst_operands ==> v IN P) bb.bb_instructions /\
  sue_state_rel P s t /\
  eval_phis s bb.bb_instructions = OK u /\
  eval_phis t (FLAT segs) = OK v ==>
  sue_state_rel P
    (u with vs_inst_idx := phi_prefix_length bb.bb_instructions)
    (v with vs_inst_idx := sue_segment_offset segs (phi_prefix_length bb.bb_instructions))
Proof
  strip_tac >> drule_all sue_expanded_phi_entry >>
  simp[sue_result_rel_def, lift_result_def]
QED

Theorem sue_exec_block_defined_exit:
  !i st u.
  wf_ssa fn /\ fn_inst_wf fn /\ wf_function fn /\
  MEM bb fn.fn_blocks /\ bb.bb_label = st.vs_current_bb /\
  fn_reachable fn st.vs_current_bb /\
  phi_prefix_length bb.bb_instructions <= i /\ i <= LENGTH bb.bb_instructions /\
  st.vs_inst_idx = i /\ sue_boundary_defined fn bb i st /\
  exec_block fuel ctx bb st = OK u /\ ~u.vs_halted ==>
  fn_reachable fn u.vs_current_bb /\ strict_dom_vars_defined fn u
Proof
  measureInduct_on `LENGTH bb.bb_instructions - i` >> rpt gen_tac >> strip_tac >>
  `bb_well_formed bb` by metis_tac[wf_function_def] >>
  `EVERY inst_wf bb.bb_instructions` by
    (fs[fn_inst_wf_def, listTheory.EVERY_MEM] >> metis_tac[]) >>
  qpat_x_assum `exec_block _ _ _ _ = _` mp_tac >>
  simp[Once exec_block_def, get_instruction_def] >>
  Cases_on `i < LENGTH bb.bb_instructions` >> simp[] >>
  Cases_on `step_inst fuel ctx (EL i bb.bb_instructions) st` >> simp[] >>
  rename1 `step_inst fuel ctx (EL i bb.bb_instructions) st = OK next` >>
  Cases_on `is_terminator (EL i bb.bb_instructions).inst_opcode` >> simp[]
  >- (Cases_on `next.vs_halted` >> simp[] >> strip_tac >> gvs[] >>
      `fn_cfg_edge fn st.vs_current_bb next.vs_current_bb` by
        metis_tac[sue_terminator_cfg_edge] >>
      conj_tac >- metis_tac[fn_reachable_step] >>
      irule sue_boundary_defined_exit >>
      metis_tac[sue_terminator_domain_mono]) >>
  strip_tac >>
  `sue_boundary_defined fn bb (SUC i) (next with vs_inst_idx := SUC i)` by
    (irule sue_boundary_defined_step >>
     metis_tac[sue_phi_suffix_nonphi, listTheory.EVERY_EL]) >>
  `next.vs_current_bb = st.vs_current_bb` by
    metis_tac[venomInstPropsTheory.step_preserves_control_flow] >>
  first_x_assum (qspec_then `SUC i` mp_tac) >> simp[] >>
  disch_then (qspecl_then [`next with vs_inst_idx := SUC i`, `u`] mp_tac) >>
  simp[]
QED

Theorem sue_result_step_indices[local]:
  sue_result_rel P (step_inst fuel ctx inst s)
    (step_inst fuel ctx inst' (t with vs_inst_idx := k)) <=>
  sue_result_rel P (step_inst fuel ctx inst s) (step_inst fuel ctx inst' t)
Proof
  once_rewrite_tac[GSYM (Q.INST [`n` |-> `0`, `m` |-> `0`] sue_result_rel_idx)] >>
  pure_rewrite_tac[sue_step_inst_idx_norm] >> simp[]
QED

Theorem sue_drop_prefix_index[local]:
  !prefix xs k inst tail. DROP k xs = prefix ++ inst::tail ==>
    k + LENGTH prefix < LENGTH xs /\ EL (k + LENGTH prefix) xs = inst
Proof
  Induct >> rpt gen_tac >> simp[]
  >- metis_tac[sue_drop_cons_index] >>
  strip_tac >> drule sue_drop_cons_index >> strip_tac >>
  RULE_ASSUM_TAC (PURE_REWRITE_RULE [GSYM listTheory.APPEND_ASSOC, listTheory.APPEND]) >>
  first_x_assum (qspecl_then [`xs`, `SUC k`, `inst`, `tail`] mp_tac) >>
  simp[arithmeticTheory.ADD_CLAUSES]
QED

Theorem sue_segment_indexed_step:
  ir_supply_inst_ok supply /\ P SUBSET set supply.irs_used_vars /\
  sue_segments_supply dfg supply bb.bb_instructions = (segs,supply') /\
  i < LENGTH bb.bb_instructions /\ bb' = bb with bb_instructions := FLAT segs /\
  inst = EL i bb.bb_instructions /\ inst_wf inst /\ ~is_alloca_op inst.inst_opcode /\
  (!v. MEM (Var v) inst.inst_operands ==> v IN P) /\
  (~sue_should_skip inst.inst_opcode ==>
    !v. MEM (Var v) inst.inst_operands ==> v IN FDOM s.vs_vars) /\
  sue_state_rel P s t /\ t.vs_inst_idx = sue_segment_offset segs i ==>
  ?k u inst'.
    exec_block fuel ctx bb' t = exec_block fuel ctx bb' u /\
    u.vs_inst_idx = k /\ k < LENGTH bb'.bb_instructions /\
    EL k bb'.bb_instructions = inst' /\ inst'.inst_opcode = inst.inst_opcode /\
    SUC k = sue_segment_offset segs (SUC i) /\
    sue_result_rel P (step_inst fuel ctx inst s) (step_inst fuel ctx inst' u)
Proof
  strip_tac >> drule_all sue_segments_supply_index_ready >> strip_tac >>
  `i < LENGTH segs` by metis_tac[sue_segments_supply_length] >>
  drule sue_segment_offset_drop >> strip_tac >>
  drule sue_segment_offset_suc >> strip_tac >>
  Cases_on `sue_should_skip inst.inst_opcode`
  >- suspend "skip" >>
  Cases_on `sue_expand_ops_supply dfg inst si inst.inst_operands 0` >>
  PairCases_on `r` >>
  rename1 `sue_expand_ops_supply dfg inst si inst.inst_operands 0 = (assigns,ops,sj')` >>
  `EL i segs = assigns ++ [inst with inst_operands := ops]` by
    gvs[sue_expand_inst_supply_def] >>
  `!a v. MEM a assigns /\ a.inst_operands = [Var v] ==> v IN FDOM s.vs_vars` by
    (drule sue_expand_ops_supply_copy_sources >>
     simp[listTheory.EVERY_MEM] >> metis_tac[listTheory.CONS_11]) >>
  drule_all sue_expand_ops_supply_step_sim >>
  disch_then (qspecl_then [`fuel`, `ctx`] strip_assume_tac) >>
  suspend "expanded"
QED

Resume sue_segment_indexed_step[skip]:
  `EL i segs = [inst]` by metis_tac[sue_expand_inst_supply_skip, pairTheory.PAIR_EQ] >>
  `sue_segment_offset segs i < LENGTH (FLAT segs) /\
   EL (sue_segment_offset segs i) (FLAT segs) = inst` by
    (fs[] >> metis_tac[sue_drop_cons_index]) >>
  qexistsl [`sue_segment_offset segs i`, `t`, `inst`] >>
  simp[] >> irule sue_step_inst_preserves >> simp[]
QED

Resume sue_segment_indexed_step[expanded]:
  `EVERY (\a. a.inst_opcode = ASSIGN) assigns` by
    (drule_all sue_expand_ops_supply_prefix >>
     simp[listTheory.EVERY_MEM] >> metis_tac[]) >>
  `DROP (sue_segment_offset segs i) bb'.bb_instructions =
    assigns ++ (inst with inst_operands := ops)::FLAT (DROP (SUC i) segs)` by
    (simp[] >> pure_asm_rewrite_tac[GSYM listTheory.APPEND_ASSOC, listTheory.APPEND]) >>
  `t with vs_inst_idx := sue_segment_offset segs i = t` by
    (qpat_x_assum `t.vs_inst_idx = _` (SUBST1_TAC o SYM) >> simp[]) >>
  drule_all sue_exec_block_assign_prefix >> strip_tac >>
  `sue_segment_offset segs i + LENGTH assigns < LENGTH bb'.bb_instructions /\
    EL (sue_segment_offset segs i + LENGTH assigns) bb'.bb_instructions =
      inst with inst_operands := ops` by
    metis_tac[sue_drop_prefix_index] >>
  qexistsl [`sue_segment_offset segs i + LENGTH assigns`,
    `u with vs_inst_idx := sue_segment_offset segs i + LENGTH assigns`,
    `inst with inst_operands := ops`] >>
  simp[] >> conj_tac
  >- metis_tac[arithmeticTheory.ADD_COMM] >>
  gvs[sue_result_step_indices]
QED

Finalise sue_segment_indexed_step

Theorem sue_original_operand_covered:
  MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
  MEM (Var v) inst.inst_operands ==> v IN set (fn_ir_vars fn)
Proof
  strip_tac >>
  `!ops. MEM (Var v) ops ==> MEM v (venomInst$operand_vars ops)` by
    (Induct >> simp[venomInstTheory.operand_vars_def] >> Cases_on `h` >>
     simp[venomInstTheory.operand_vars_def, venomInstTheory.operand_var_def] >> metis_tac[]) >>
  simp[fn_ir_vars_def, block_ir_vars_def, listTheory.MEM_FLAT,
       listTheory.MEM_MAP] >>
  qexists_tac `block_ir_vars bb` >> conj_tac
  >- (qexists_tac `bb` >> simp[block_ir_vars_def]) >>
  simp[block_ir_vars_def, listTheory.MEM_FLAT, listTheory.MEM_MAP] >>
  qexists_tac `inst_ir_vars inst` >> conj_tac
  >- metis_tac[] >>
  simp[inst_ir_vars_def, venomInstTheory.inst_uses_def] >> metis_tac[]
QED

Theorem sue_exec_block_supply_sim:
  !i s t.
  wf_ssa fn /\ fn_inst_wf fn /\ wf_function fn /\ MEM bb fn.fn_blocks /\
  bb.bb_label = s.vs_current_bb /\ fn_reachable fn s.vs_current_bb /\
  EVERY (\inst. inst.inst_opcode <> ALLOCA) (fn_insts fn) /\
  ir_supply_inst_ok supply /\ set (fn_ir_vars fn) SUBSET set supply.irs_used_vars /\
  sue_segments_supply (dfg_build_function fn) supply bb.bb_instructions = (segs,supply') /\
  bb' = bb with bb_instructions := FLAT segs /\
  phi_prefix_length bb.bb_instructions <= i /\ i <= LENGTH bb.bb_instructions /\
  s.vs_inst_idx = i /\ t.vs_inst_idx = sue_segment_offset segs i /\
  sue_boundary_defined fn bb i s /\ sue_state_rel (set (fn_ir_vars fn)) s t ==>
  sue_result_rel (set (fn_ir_vars fn))
    (exec_block fuel ctx bb s) (exec_block fuel ctx bb' t)
Proof
  measureInduct_on `LENGTH bb.bb_instructions - i` >> rpt gen_tac >> strip_tac >>
  Cases_on `i = LENGTH bb.bb_instructions`
  >- (`LENGTH segs = LENGTH bb.bb_instructions` by metis_tac[sue_segments_supply_length] >>
      `sue_segment_offset segs i = LENGTH (FLAT segs)` by metis_tac[sue_segment_offset_end] >>
      gvs[] >> simp[Once exec_block_def, get_instruction_def] >>
      simp[Once exec_block_def, get_instruction_def, sue_result_rel_def, lift_result_def]) >>
  `i < LENGTH bb.bb_instructions` by decide_tac >>
  `bb_well_formed bb` by metis_tac[wf_function_def] >>
  `EVERY inst_wf bb.bb_instructions` by
    (fs[fn_inst_wf_def, listTheory.EVERY_MEM] >> metis_tac[]) >>
  `inst_wf (EL i bb.bb_instructions)` by metis_tac[listTheory.EVERY_EL] >>
  `!v. MEM (Var v) (EL i bb.bb_instructions).inst_operands ==>
       v IN set (fn_ir_vars fn)` by metis_tac[sue_original_operand_covered, listTheory.MEM_EL] >>
  `(EL i bb.bb_instructions).inst_opcode <> PHI` by metis_tac[sue_phi_suffix_nonphi] >>
  `!v. MEM (Var v) (EL i bb.bb_instructions).inst_operands ==> v IN FDOM s.vs_vars` by
    metis_tac[sue_boundary_operand_defined] >>
  `MEM (EL i bb.bb_instructions) (fn_insts fn)` by
    (`!bbs. MEM bb bbs ==> MEM (EL i bb.bb_instructions) (fn_insts_blocks bbs)` by
       (Induct >> simp[fn_insts_blocks_def] >> metis_tac[listTheory.MEM_EL]) >>
     simp[fn_insts_def]) >>
  `(EL i bb.bb_instructions).inst_opcode <> ALLOCA` by
    (qpat_x_assum `EVERY (\inst. inst.inst_opcode <> ALLOCA) _` mp_tac >>
     simp[listTheory.EVERY_MEM] >> disch_then drule >> simp[]) >>
  `~is_alloca_op (EL i bb.bb_instructions).inst_opcode` by
    (qpat_x_assum `(EL i bb.bb_instructions).inst_opcode <> ALLOCA` mp_tac >>
     Cases_on `(EL i bb.bb_instructions).inst_opcode` >> simp[is_alloca_op_def]) >>
  `?k u inst'.
    exec_block fuel ctx bb' t = exec_block fuel ctx bb' u /\
    u.vs_inst_idx = k /\ k < LENGTH bb'.bb_instructions /\
    EL k bb'.bb_instructions = inst' /\
    inst'.inst_opcode = (EL i bb.bb_instructions).inst_opcode /\
    SUC k = sue_segment_offset segs (SUC i) /\
    sue_result_rel (set (fn_ir_vars fn))
      (step_inst fuel ctx (EL i bb.bb_instructions) s) (step_inst fuel ctx inst' u)` by
    (irule sue_segment_indexed_step >> simp[] >> metis_tac[]) >>
  qpat_x_assum `exec_block fuel ctx bb' t = _` SUBST1_TAC >>
  `get_instruction bb s.vs_inst_idx = SOME (EL i bb.bb_instructions)` by
    simp[get_instruction_def] >>
  `get_instruction bb' u.vs_inst_idx = SOME inst'` by
    gvs[get_instruction_def] >>
  pure_once_rewrite_tac[exec_block_def] >>
  qpat_x_assum `get_instruction bb _ = _` (fn th => rewrite_tac[th]) >>
  qpat_x_assum `get_instruction bb' _ = _` (fn th => rewrite_tac[th]) >>
  Cases_on `step_inst fuel ctx (EL i bb.bb_instructions) s` >>
  Cases_on `step_inst fuel ctx inst' u` >>
  fs[sue_result_rel_def, lift_result_def] >>
  rename1 `sue_state_rel (set (fn_ir_vars fn)) v v'` >>
  Cases_on `is_terminator (EL i bb.bb_instructions).inst_opcode`
  >- (`v.vs_halted = v'.vs_halted` by
        (fs[sue_state_rel_def] >>
         qpat_x_assum `execution_frame v = _` mp_tac >>
         simp[execution_frame_def, venom_state_component_equality]) >>
      Cases_on `v'.vs_halted` >>
      fs[lift_result_def, sue_term_rel_def, sue_state_rel_def]) >>
  simp[] >>
  `v.vs_current_bb = s.vs_current_bb` by
    metis_tac[venomInstPropsTheory.step_preserves_control_flow] >>
  `sue_boundary_defined fn bb (SUC i) (v with vs_inst_idx := SUC i)` by
    (irule sue_boundary_defined_step >> simp[] >> metis_tac[]) >>
  first_x_assum (qspec_then `SUC i` mp_tac) >>
  impl_tac >- decide_tac >>
  disch_then (qspecl_then [`v with vs_inst_idx := SUC i`,
    `v' with vs_inst_idx := sue_segment_offset segs (SUC i)`] mp_tac) >>
  simp[]
QED

Theorem sue_run_blocks_supply_sim:
  !fuel st tt.
  wf_ssa fn /\ fn_inst_wf fn /\ wf_function fn /\
  EVERY (\inst. inst.inst_opcode <> ALLOCA) (fn_insts fn) /\
  ir_supply_covers_fn supply fn /\ ir_supply_inst_ok supply /\
  sue_expand_function_supply supply fn = (fn',supply') /\
  fn_reachable fn st.vs_current_bb /\ strict_dom_vars_defined fn st /\
  sue_state_rel (set (fn_ir_vars fn)) st tt ==>
  sue_result_rel (set (fn_ir_vars fn)) (run_blocks fuel ctx fn st)
    (run_blocks fuel ctx fn' tt)
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- (pure_once_rewrite_tac[run_blocks_def] >>
      simp[sue_result_rel_def, lift_result_def]) >>
  `tt.vs_current_bb = st.vs_current_bb` by fs[sue_state_rel_def] >>
  Cases_on `lookup_block st.vs_current_bb fn.fn_blocks`
  >- suspend "missing" >>
  rename1 `lookup_block st.vs_current_bb fn.fn_blocks = SOME bb` >>
  drule_all sue_function_lookup_ready >> strip_tac >>
  `MEM bb fn.fn_blocks /\ bb.bb_label = st.vs_current_bb` by
    metis_tac[lookup_block_MEM, lookup_block_label] >>
  `EVERY (\inst. inst.inst_opcode = PHI ==>
      !v. MEM (Var v) inst.inst_operands ==> v IN set (fn_ir_vars fn)) bb.bb_instructions` by
    (simp[listTheory.EVERY_MEM] >> metis_tac[sue_original_operand_covered]) >>
  `sue_result_rel (set (fn_ir_vars fn))
     (eval_phis st bb.bb_instructions) (eval_phis tt (FLAT segs))` by
    (irule sue_expanded_phi_entry >> simp[] >> metis_tac[]) >>
  suspend "phis"
QED

Resume sue_run_blocks_supply_sim[missing]:
  `lookup_block st.vs_current_bb fn'.fn_blocks = NONE` by
    (Cases_on `sue_expand_blocks_supply (dfg_build_function fn) supply fn.fn_blocks` >>
     gvs[sue_expand_function_supply_def] >>
     Cases_on `lookup_block st.vs_current_bb q` >> simp[] >>
     drule_all sue_expand_blocks_supply_lookup_back >> simp[]) >>
  pure_once_rewrite_tac[run_blocks_def] >>
  simp[sue_result_rel_def, lift_result_def]
QED

Resume sue_run_blocks_supply_sim[phis]:
  `phi_prefix_length (FLAT segs) = phi_prefix_length bb.bb_instructions` by
    (drule sue_segments_supply_flat >> strip_tac >>
     drule_all sue_expand_insts_supply_phis >> simp[]) >>
  `sue_segment_offset segs (phi_prefix_length bb.bb_instructions) =
    phi_prefix_length bb.bb_instructions` by metis_tac[sue_segments_phi_offset] >>
  pure_once_rewrite_tac[run_blocks_def] >> simp[] >>
  qspecl_then [`bb.bb_instructions`, `st`] strip_assume_tac sue_eval_phis_shape >>
  Cases_on `eval_phis tt (FLAT segs)` >>
  gvs[sue_result_rel_def, lift_result_def] >>
  suspend "block"

QED

Resume sue_run_blocks_supply_sim[block]:
  `sue_boundary_defined fn bb (phi_prefix_length bb.bb_instructions)
    (u with vs_inst_idx := phi_prefix_length bb.bb_instructions)` by
    metis_tac[sue_boundary_defined_phis] >>
  `u.vs_current_bb = st.vs_current_bb` by
    metis_tac[eval_phis_preserves_current_bb] >>
  `sue_result_rel (set (fn_ir_vars fn))
    (exec_block fuel ctx bb (u with vs_inst_idx := phi_prefix_length bb.bb_instructions))
    (exec_block fuel ctx (bb with bb_instructions := FLAT segs)
      (v with vs_inst_idx := phi_prefix_length bb.bb_instructions))` by
    (irule sue_exec_block_supply_sim >> simp[phi_prefix_length_le] >> metis_tac[]) >>
  Cases_on `exec_block fuel ctx bb
    (u with vs_inst_idx := phi_prefix_length bb.bb_instructions)` >>
  Cases_on `exec_block fuel ctx (bb with bb_instructions := FLAT segs)
    (v with vs_inst_idx := phi_prefix_length bb.bb_instructions)` >>
  gvs[sue_result_rel_def, lift_result_def] >>
  suspend "exit"
QED

Resume sue_run_blocks_supply_sim[exit]:
  `v'.vs_halted = v''.vs_halted` by
    (fs[sue_state_rel_def] >>
     qpat_x_assum `execution_frame v' = _` mp_tac >>
     simp[execution_frame_def, venom_state_component_equality]) >>
  Cases_on `v'.vs_halted`
  >- fs[lift_result_def, sue_term_rel_def, sue_state_rel_def] >>
  fs[] >> first_x_assum irule >> simp[] >>
  irule sue_exec_block_defined_exit >> simp[] >>
  qexistsl [`bb`, `ctx`, `fuel`,
    `u with vs_inst_idx := phi_prefix_length bb.bb_instructions`] >>
  simp[phi_prefix_length_le]
QED

Finalise sue_run_blocks_supply_sim


Definition sue_idx0_def:
  sue_idx0 st = st with vs_inst_idx := 0
End

Theorem sue_idx0_update[simp]:
  sue_idx0 (st with vs_inst_idx := k) = sue_idx0 st
Proof
  simp[sue_idx0_def]
QED

Theorem sue_assign_step_fuel:
  a.inst_opcode = ASSIGN ==>
  step_inst fuel ctx a t = step_inst 0 ctx a t
Proof
  strip_tac >> simp[Once step_inst_def] >>
  simp[Once step_inst_def] >> simp[step_inst_base_def]
QED

Theorem sue_assign_step_normalized:
  a.inst_opcode = ASSIGN /\ step_inst fuel ctx a t = OK v ==>
  step_inst 0 ctx a (sue_idx0 t) = OK (sue_idx0 v)
Proof
  strip_tac >> simp[sue_idx0_def, sue_assign_step_idx] >>
  drule sue_assign_step_fuel >> disch_then (qspecl_then [`t`, `fuel`, `ctx`] assume_tac) >>
  gvs[exec_result_map_def]
QED

Theorem sue_assign_prefix_advance:
  EVERY (\a. a.inst_opcode = ASSIGN) assigns /\ j < LENGTH assigns /\
  b.vs_inst_idx = 0 /\
  run_insts 0 ctx (TAKE j assigns) b = OK (sue_idx0 t) /\
  step_inst fuel ctx (EL j assigns) t = OK v ==>
  run_insts 0 ctx (TAKE (SUC j) assigns) b =
    OK (sue_idx0 (v with vs_inst_idx := SUC t.vs_inst_idx))
Proof
  strip_tac >>
  ` (EL j assigns).inst_opcode = ASSIGN` by
    fs[listTheory.EVERY_EL] >>
  drule_all sue_assign_step_normalized >> strip_tac >>
  simp[rich_listTheory.TAKE_SUC_BY_TAKE, listTheory.SNOC_APPEND,
       analysisSimProofsBaseTheory.run_insts_append,
       analysisSimProofsBaseTheory.run_insts_singleton]
QED

Theorem sue_assign_prefix_empty:
  b.vs_inst_idx = 0 ==>
  run_insts 0 ctx (TAKE 0 assigns) b = OK (sue_idx0 b)
Proof
  simp[run_insts_def, sue_idx0_def, venom_state_component_equality]
QED

Theorem sue_assign_prefix_complete:
  run_insts 0 ctx (TAKE (LENGTH assigns) assigns) b = OK (sue_idx0 t) <=>
  run_insts 0 ctx assigns b = OK (sue_idx0 t)
Proof
  simp[]
QED

Theorem sue_state_rel_idx0[simp]:
  sue_state_rel protected st (sue_idx0 tt) <=> sue_state_rel protected st tt
Proof
  simp[sue_idx0_def, sue_state_rel_def, execution_frame_def]
QED

Theorem sue_eval_operand_idx0[simp]:
  eval_operand op (sue_idx0 t) = eval_operand op t
Proof
  Cases_on `op` >> simp[sue_idx0_def, eval_operand_def, lookup_var_def]
QED

Theorem sue_assign_prefix_normalized_rel:
  EVERY (\a. a.inst_opcode = ASSIGN /\
             EVERY (\v. ~(v IN protected)) a.inst_outputs) assigns /\
  sue_state_rel protected st b /\
  run_insts 0 ctx (TAKE j assigns) b = OK (sue_idx0 t) ==>
  sue_state_rel protected st t
Proof
  strip_tac >>
  `sue_state_rel protected st (sue_idx0 t)` suffices_by simp[] >>
  irule sue_assign_prefix_rel >> goal_assum (drule_at Any) >>
  simp[] >> irule rich_listTheory.EVERY_TAKE >> simp[]
QED

Theorem sue_expand_ops_supply_normalized_eval:
  ir_supply_inst_ok s /\
  sue_expand_ops_supply dfg inst s ops k = (assigns,new_ops,s') /\
  protected SUBSET set s.irs_used_vars /\
  (!v. MEM (Var v) ops ==> v IN protected) /\
  sue_state_rel protected st b /\
  run_insts 0 ctx assigns b = OK (sue_idx0 t) ==>
  LIST_REL (\op newop. eval_operand newop t = eval_operand op st) ops new_ops
Proof
  strip_tac >> drule_all sue_expand_ops_supply_eval >> simp[]
QED

Theorem sue_function_lookup_ready_back:
  sue_expand_function_supply supply fn = (fn',supply') /\
  ir_supply_inst_ok supply /\ ir_supply_covers_fn supply fn /\
  lookup_block lbl fn'.fn_blocks = SOME bb' ==>
  ?bb si sj segs. lookup_block lbl fn.fn_blocks = SOME bb /\
    sue_segments_supply (dfg_build_function fn) si bb.bb_instructions = (segs,sj) /\
    bb' = bb with bb_instructions := FLAT segs /\
    ir_supply_inst_ok si /\ set (fn_ir_vars fn) SUBSET set si.irs_used_vars
Proof
  strip_tac >>
  `?bb. lookup_block lbl fn.fn_blocks = SOME bb` by
    (Cases_on `sue_expand_blocks_supply (dfg_build_function fn) supply fn.fn_blocks` >>
     gvs[sue_expand_function_supply_def] >>
     drule_all sue_expand_blocks_supply_lookup_back >> metis_tac[]) >>
  drule_all sue_function_lookup_ready >> strip_tac >>
  gvs[] >> metis_tac[]
QED

(* A successful completed copy prefix is enough for final-step simulation;
   no separate operand-definedness premise is needed here. *)
Theorem sue_expand_inst_supply_final_step:
  ir_supply_inst_ok supply /\
  sue_expand_inst_supply dfg supply inst = (segment,supply') /\
  P SUBSET set supply.irs_used_vars /\
  (!x. MEM (Var x) inst.inst_operands ==> x IN P) /\
  inst_wf inst /\ ~is_alloca_op inst.inst_opcode /\
  sue_state_rel P s b /\
  run_insts 0 ctx (BUTLAST segment) b = OK (sue_idx0 t) ==>
  sue_result_rel P (step_inst fuel ctx inst s)
    (step_inst fuel ctx (LAST segment) t)
Proof
  strip_tac >> Cases_on `sue_should_skip inst.inst_opcode`
  >- (drule_all sue_expand_inst_supply_skip >> strip_tac >>
      gvs[analysisSimDefsTheory.run_insts_def] >>
      irule sue_step_inst_preserves >> fs[]) >>
  Cases_on `sue_expand_ops_supply dfg inst supply inst.inst_operands 0` >>
  PairCases_on `r` >>
  `segment = q ++ [inst with inst_operands := r0] /\ supply' = r1` by
    fs[sue_expand_inst_supply_def] >>
  `run_insts 0 ctx q b = OK (sue_idx0 t)` by
    fs[rich_listTheory.FRONT_APPEND_NOT_NIL] >>
  drule_all sue_expand_ops_supply_normalized_eval >> strip_tac >>
  `sue_state_rel P s t` by
    (irule sue_assign_prefix_normalized_rel >>
     qexistsl [`q`, `b`, `ctx`, `LENGTH q`] >> simp[] >>
     drule sue_expand_ops_supply_prefix >>
     fs[listTheory.EVERY_MEM, listTheory.MEM_FLAT,
        listTheory.MEM_MAP, pred_setTheory.SUBSET_DEF] >> metis_tac[]) >>
  drule sue_expand_ops_supply_structure >> strip_tac >>
  simp[] >> irule sue_step_inst_rewritten >>
  fs[sue_should_skip_def, is_param_opcode_iff] >>
  rpt strip_tac >>
  `eval_operand (EL i r0) t = eval_operand (EL i inst.inst_operands) s` by
    fs[listTheory.LIST_REL_EL_EQN] >>
  `eval_operand (EL i inst.inst_operands) s =
   eval_operand (EL i inst.inst_operands) t` by
    (sym_tac >> irule sue_state_rel_eval_operand >> qexists_tac `P` >> simp[] >>
     rpt strip_tac >> first_x_assum irule >>
     simp[listTheory.MEM_EL] >> qexists_tac `i` >> simp[]) >> simp[]
QED

Theorem sue_expand_ops_supply_copies_wf:
  sue_expand_ops_supply dfg inst s ops k = (assigns,new_ops,s') ==>
  EVERY inst_wf assigns
Proof
  strip_tac >> drule sue_expand_ops_supply_copies >>
  simp[listTheory.EVERY_MEM] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >> simp[inst_wf_def]
QED

Theorem sue_supply_skip_opcodes[local]:
  sue_should_skip PHI /\ sue_should_skip PARAM /\
  sue_should_skip FMP_PARAM /\ sue_should_skip RETPC_PARAM
Proof
  EVAL_TAC
QED

(* Unlike parser-significant counts, ALLOCA's literal is copied.  Consumers
   must retain their no-ALLOCA premise. *)
Theorem sue_supply_alloca_literal_probe[local]:
  MAP (\i. i.inst_operands)
    (FST (sue_expand_inst_supply dfg
      <| irs_next_inst := 10; irs_next_var := 0; irs_next_label := 0;
         irs_used_inst_ids := []; irs_used_vars := []; irs_used_labels := [] |>
      <| inst_id := 1; inst_opcode := ALLOCA;
         inst_operands := [Lit 32w]; inst_outputs := ["out"] |>)) =
    [[Lit 32w]; [Var "formal_var_0"]]
Proof
  EVAL_TAC
QED

Theorem sue_expand_ops_supply_inst_wf:
  inst_wf inst /\ inst.inst_opcode <> ALLOCA /\
  inst.inst_opcode <> DRET /\ ~sue_should_skip inst.inst_opcode /\
  sue_expand_ops_supply dfg inst s inst.inst_operands 0 = (assigns,new_ops,s') ==>
  inst_wf (inst with inst_operands := new_ops)
Proof
  strip_tac >>
  drule sue_expand_ops_supply_length >> strip_tac >>
  drule sue_expand_ops_supply_operand_labels >> strip_tac >>
  fs[sue_should_skip_def, is_param_opcode_def] >>
  qpat_x_assum `inst_wf inst` mp_tac >>
  simp[inst_wf_def] >>
  Cases_on `inst.inst_opcode` >>
  simp[] >> rpt strip_tac >> gvs[is_param_opcode_def]
  >- (Cases_on `x0` >> gvs[sue_operand_label_def])
  >- (Cases_on `new_ops` >> gvs[] >>
      rename1 `MAP sue_operand_label tail = [_; _]` >>
      Cases_on `tail` >> gvs[] >>
      rename1 `sue_operand_label op1 = sue_operand_label (Label l1)` >>
      Cases_on `op1` >> gvs[sue_operand_label_def] >>
      gvs[AllCaseEqs()])
  >- (Cases_on `new_ops` >> gvs[] >>
      gvs[GSYM sue_operand_label_get_label] >>
      `EVERY IS_SOME (MAP sue_operand_label label_ops)` by
        gvs[listTheory.EVERY_MAP, combinTheory.o_DEF] >>
      metis_tac[listTheory.EVERY_MAP, combinTheory.o_DEF])
  >- (Cases_on `new_ops` >> gvs[] >>
      rename1 `sue_operand_label op = sue_operand_label (Label lbl)` >>
      Cases_on `op` >> gvs[sue_operand_label_def]) >>
  `?rest'. new_ops = Lit tc::rest'` by
    metis_tac[sue_expand_ops_supply_structural_head] >>
  gvs[]
QED

Theorem sue_expand_inst_supply_inst_wf:
  inst_wf inst /\ inst.inst_opcode <> ALLOCA /\
  inst.inst_opcode <> DRET /\
  sue_expand_inst_supply dfg s inst = (out,s') ==>
  EVERY inst_wf out
Proof
  strip_tac >> Cases_on `sue_should_skip inst.inst_opcode`
  >- gvs[sue_expand_inst_supply_def] >>
  Cases_on `sue_expand_ops_supply dfg inst s inst.inst_operands 0` >>
  PairCases_on `r` >> gvs[sue_expand_inst_supply_def] >>
  drule sue_expand_ops_supply_copies_wf >> strip_tac >>
  simp[] >> irule sue_expand_ops_supply_inst_wf >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem sue_expand_insts_supply_inst_wf:
  !insts s outs s'.
    EVERY (\i. inst_wf i /\ i.inst_opcode <> ALLOCA /\
               i.inst_opcode <> DRET) insts /\
    sue_expand_insts_supply dfg s insts = (outs,s') ==>
    EVERY inst_wf outs
Proof
  Induct_on `insts` >> rpt strip_tac
  >- gvs[sue_expand_insts_supply_def] >>
  Cases_on `sue_expand_inst_supply dfg s h` >>
  Cases_on `sue_expand_insts_supply dfg r insts` >>
  gvs[sue_expand_insts_supply_def] >>
  metis_tac[sue_expand_inst_supply_inst_wf]
QED

Theorem sue_expand_blocks_supply_inst_wf:
  !bbs s bbs' s'.
    EVERY (\bb. EVERY (\i. inst_wf i /\ i.inst_opcode <> ALLOCA /\
                          i.inst_opcode <> DRET) bb.bb_instructions) bbs /\
    sue_expand_blocks_supply dfg s bbs = (bbs',s') ==>
    EVERY (\bb. EVERY inst_wf bb.bb_instructions) bbs'
Proof
  Induct_on `bbs` >> rpt strip_tac
  >- gvs[sue_expand_blocks_supply_def] >>
  Cases_on `sue_expand_block_supply dfg s h` >>
  Cases_on `sue_expand_blocks_supply dfg r bbs` >>
  gvs[sue_expand_blocks_supply_def] >> conj_tac
  >- (Cases_on `sue_expand_insts_supply dfg s h.bb_instructions` >>
      gvs[sue_expand_block_supply_def] >>
      metis_tac[sue_expand_insts_supply_inst_wf]) >>
  metis_tac[]
QED

Theorem sue_expand_inst_supply_opcodes:
  P ASSIGN /\ P inst.inst_opcode /\
  sue_expand_inst_supply dfg s inst = (out,s') ==>
  EVERY (\i. P i.inst_opcode) out
Proof
  strip_tac >> Cases_on `sue_should_skip inst.inst_opcode`
  >- gvs[sue_expand_inst_supply_def] >>
  Cases_on `sue_expand_ops_supply dfg inst s inst.inst_operands 0` >>
  PairCases_on `r` >> gvs[sue_expand_inst_supply_def] >>
  drule sue_expand_ops_supply_copies >>
  simp[listTheory.EVERY_MEM] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >> gvs[]
QED

Theorem sue_expand_insts_supply_opcodes:
  !insts s outs s'.
    P ASSIGN /\ EVERY (\i. P i.inst_opcode) insts /\
    sue_expand_insts_supply dfg s insts = (outs,s') ==>
    EVERY (\i. P i.inst_opcode) outs
Proof
  Induct_on `insts` >> rpt strip_tac
  >- gvs[sue_expand_insts_supply_def] >>
  Cases_on `sue_expand_inst_supply dfg s h` >>
  Cases_on `sue_expand_insts_supply dfg r insts` >>
  gvs[sue_expand_insts_supply_def] >>
  metis_tac[sue_expand_inst_supply_opcodes]
QED

Theorem sue_expand_block_supply_opcodes:
  P ASSIGN /\ EVERY (\i. P i.inst_opcode) bb.bb_instructions /\
  sue_expand_block_supply dfg s bb = (bb',s') ==>
  EVERY (\i. P i.inst_opcode) bb'.bb_instructions
Proof
  strip_tac >>
  Cases_on `sue_expand_insts_supply dfg s bb.bb_instructions` >>
  gvs[sue_expand_block_supply_def] >>
  metis_tac[sue_expand_insts_supply_opcodes]
QED

Theorem sue_expand_blocks_supply_opcodes:
  !bbs s bbs' s'.
    P ASSIGN /\
    EVERY (\bb. EVERY (\i. P i.inst_opcode) bb.bb_instructions) bbs /\
    sue_expand_blocks_supply dfg s bbs = (bbs',s') ==>
    EVERY (\bb. EVERY (\i. P i.inst_opcode) bb.bb_instructions) bbs'
Proof
  Induct_on `bbs` >> rpt strip_tac
  >- gvs[sue_expand_blocks_supply_def] >>
  Cases_on `sue_expand_block_supply dfg s h` >>
  Cases_on `sue_expand_blocks_supply dfg r bbs` >>
  gvs[sue_expand_blocks_supply_def] >>
  metis_tac[sue_expand_block_supply_opcodes]
QED

Theorem sue_expand_function_supply_opcodes:
  P ASSIGN /\ EVERY (\i. P i.inst_opcode) (fn_insts fn) /\
  sue_expand_function_supply s fn = (fn',s') ==>
  EVERY (\i. P i.inst_opcode) (fn_insts fn')
Proof
  strip_tac >>
  Cases_on `sue_expand_blocks_supply (dfg_build_function fn) s fn.fn_blocks` >>
  gvs[sue_expand_function_supply_def, fn_insts_def, fn_insts_blocks_def,
      fn_insts_EVERY_block] >>
  drule_all sue_expand_blocks_supply_opcodes >> simp[]
QED

Theorem sue_expand_function_supply_inst_wf:
  fn_inst_wf fn /\
  EVERY (\i. i.inst_opcode <> ALLOCA /\ i.inst_opcode <> DRET) (fn_insts fn) /\
  sue_expand_function_supply s fn = (fn',s') ==>
  fn_inst_wf fn'
Proof
  strip_tac >>
  Cases_on `sue_expand_blocks_supply (dfg_build_function fn) s fn.fn_blocks` >>
  gvs[sue_expand_function_supply_def, fn_inst_wf_def,
      fn_insts_def, fn_insts_blocks_def,
      fn_insts_EVERY_block] >>
  `EVERY (\bb. EVERY inst_wf bb.bb_instructions) q` suffices_by
    (simp[listTheory.EVERY_MEM] >> metis_tac[]) >>
  irule sue_expand_blocks_supply_inst_wf >>
  goal_assum (drule_at Any) >> simp[] >>
  gvs[listTheory.EVERY_MEM] >> metis_tac[]
QED

Theorem sue_bb_well_formed_cons[local]:
  bb_well_formed (bb with bb_instructions := h::t) <=>
  if t = [] then is_terminator h.inst_opcode
  else ~is_terminator h.inst_opcode /\
       bb_well_formed (bb with bb_instructions := t) /\
       (h.inst_opcode = PHI \/ EVERY (\i. i.inst_opcode <> PHI) t)
Proof
  Cases_on `t = []` >- gvs[bb_well_formed_def] >>
  `LAST (h::t) = LAST t` by (Cases_on `t` >> gvs[]) >>
  simp[bb_well_formed_def] >>
  eq_tac
  >- (rpt disch_tac >> gvs[] >> rpt conj_tac
      >- (rpt strip_tac >>
          qpat_x_assum `!i. _ /\ is_terminator _ ==> _`
            (qspec_then `0` mp_tac) >> simp[] >>
          Cases_on `t` >> gvs[])
      >- (rpt strip_tac >>
          qpat_x_assum `!i. _ /\ is_terminator _ ==> _`
            (qspec_then `SUC i` mp_tac) >> simp[] >> decide_tac)
      >- (rpt strip_tac >>
          first_x_assum (qspecl_then [`SUC i`, `SUC j`] mp_tac) >> simp[])
      >> Cases_on `h.inst_opcode = PHI` >> simp[] >>
      simp[listTheory.EVERY_EL] >> rpt strip_tac >>
      first_x_assum (qspecl_then [`0`, `SUC n`] mp_tac) >> simp[])
  >> rpt disch_tac >> gvs[] >>
  (conj_tac >- (Cases >> simp[] >> metis_tac[])) >>
     qx_gen_tac `a` >> qx_gen_tac `b` >>
     Cases_on `b` >> simp[] >> Cases_on `a` >> simp[] >>
     fs[listTheory.EVERY_EL] >> metis_tac[]
QED

Theorem sue_bb_nonphi_head[local]:
  bb_well_formed (bb with bb_instructions := h::t) /\
  h.inst_opcode <> PHI ==>
  EVERY (\i. i.inst_opcode <> PHI) (h::t)
Proof
  Cases_on `t = []` >> simp[sue_bb_well_formed_cons] >> metis_tac[]
QED

Theorem sue_bb_assign_prefix[local]:
  !assigns. EVERY (\a. a.inst_opcode = ASSIGN) assigns /\
    bb_well_formed (bb with bb_instructions := h::t) /\
    h.inst_opcode <> PHI ==>
    bb_well_formed (bb with bb_instructions := assigns ++ h::t)
Proof
  Induct >> simp[] >> rpt strip_tac >>
  `bb_well_formed (bb with bb_instructions := assigns ++ h::t)` by metis_tac[] >>
  `EVERY (\i. i.inst_opcode <> PHI) (assigns ++ h::t)` by
    (simp[listTheory.EVERY_APPEND] >> conj_tac
     >- (gvs[listTheory.EVERY_MEM] >> metis_tac[]) >>
     drule_all sue_bb_nonphi_head >> simp[]) >>
  simp[sue_bb_well_formed_cons, is_terminator_def]
QED

Theorem sue_expand_insts_supply_nonempty:
  sue_expand_insts_supply dfg s insts = (outs,s') ==>
  (outs = [] <=> insts = [])
Proof
  Cases_on `insts` >> simp[sue_expand_insts_supply_def] >>
  Cases_on `sue_expand_inst_supply dfg s h` >>
  Cases_on `sue_expand_insts_supply dfg r t` >>
  strip_tac >> gvs[] >>
  drule sue_expand_inst_supply_nonempty >> simp[]
QED

Theorem sue_expand_insts_supply_bb_well_formed:
  !insts s outs s'.
    bb_well_formed (bb with bb_instructions := insts) /\
    ir_supply_inst_ok s /\
    sue_expand_insts_supply dfg s insts = (outs,s') ==>
    bb_well_formed (bb with bb_instructions := outs)
Proof
  Induct_on `insts`
  >- simp[bb_well_formed_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `sue_expand_inst_supply dfg s h` >>
  Cases_on `sue_expand_insts_supply dfg r insts` >>
  gvs[sue_expand_insts_supply_def] >>
  `ir_supply_inst_ok r` by
    metis_tac[sue_expand_inst_supply_extends, sue_supply_extends_def] >>
  Cases_on `h.inst_opcode = PHI`
  >- (gvs[sue_expand_inst_supply_def, sue_should_skip_def] >>
      `insts <> []` by
        (strip_tac >> gvs[sue_bb_well_formed_cons, is_terminator_def]) >>
      `bb_well_formed (bb with bb_instructions := insts)` by
        gvs[sue_bb_well_formed_cons] >>
      `bb_well_formed (bb with bb_instructions := q')` by metis_tac[] >>
      `q' <> []` by metis_tac[sue_expand_insts_supply_nonempty] >>
      simp[sue_bb_well_formed_cons, is_terminator_def]) >>
  drule_all sue_expand_inst_supply_segment >> strip_tac >> gvs[] >>
  `EVERY (\a. a.inst_opcode = ASSIGN) assigns` by
    gvs[listTheory.EVERY_MEM] >>
  pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC, listTheory.APPEND] >>
  irule sue_bb_assign_prefix >> simp[] >>
  Cases_on `insts = []`
  >- (gvs[sue_expand_insts_supply_def, sue_bb_well_formed_cons]) >>
  `bb_well_formed (bb with bb_instructions := insts)` by
    gvs[sue_bb_well_formed_cons] >>
  `bb_well_formed (bb with bb_instructions := q')` by metis_tac[] >>
  `q' <> []` by metis_tac[sue_expand_insts_supply_nonempty] >>
  `EVERY (\i. i.inst_opcode <> PHI) insts` by
    gvs[sue_bb_well_formed_cons] >>
  `EVERY (\i. i.inst_opcode <> PHI) q'` by
    (ho_match_mp_tac sue_expand_insts_supply_opcodes >>
     goal_assum (drule_at Any) >> simp[] >> metis_tac[]) >>
  gvs[sue_bb_well_formed_cons]
QED

Theorem sue_expand_block_supply_bb_well_formed:
  bb_well_formed bb /\ ir_supply_inst_ok s /\
  sue_expand_block_supply dfg s bb = (bb',s') ==>
  bb_well_formed bb'
Proof
  strip_tac >>
  Cases_on `sue_expand_insts_supply dfg s bb.bb_instructions` >>
  gvs[sue_expand_block_supply_def] >>
  irule sue_expand_insts_supply_bb_well_formed >>
  goal_assum (drule_at Any) >> simp[]
QED

Theorem sue_expand_blocks_supply_bb_well_formed:
  !bbs s bbs' s'.
    EVERY bb_well_formed bbs /\ ir_supply_inst_ok s /\
    sue_expand_blocks_supply dfg s bbs = (bbs',s') ==>
    EVERY bb_well_formed bbs'
Proof
  Induct_on `bbs` >> rpt strip_tac
  >- gvs[sue_expand_blocks_supply_def] >>
  Cases_on `sue_expand_block_supply dfg s h` >>
  Cases_on `sue_expand_blocks_supply dfg r bbs` >>
  gvs[sue_expand_blocks_supply_def] >>
  `ir_supply_inst_ok r` by
    metis_tac[sue_expand_block_supply_extends, sue_supply_extends_def] >>
  conj_tac >- metis_tac[sue_expand_block_supply_bb_well_formed] >>
  metis_tac[]
QED

Theorem sue_expand_blocks_supply_member:
  !bbs s bbs' s' bb'.
    sue_expand_blocks_supply dfg s bbs = (bbs',s') /\ MEM bb' bbs' ==>
    ?bb si sj. MEM bb bbs /\ sue_expand_block_supply dfg si bb = (bb',sj)
Proof
  Induct_on `bbs` >> rpt strip_tac
  >- gvs[sue_expand_blocks_supply_def] >>
  Cases_on `sue_expand_block_supply dfg s h` >>
  Cases_on `sue_expand_blocks_supply dfg r bbs` >>
  gvs[sue_expand_blocks_supply_def] >> metis_tac[]
QED

Theorem sue_expand_block_supply_bb_succs:
  sue_expand_block_supply dfg s bb = (bb',s') ==>
  bb_succs bb' = bb_succs bb
Proof
  strip_tac >> Cases_on `bb.bb_instructions = []`
  >- gvs[sue_expand_block_supply_def, sue_expand_insts_supply_def, bb_succs_def] >>
  drule_all sue_expand_block_supply_successors >> strip_tac >>
  `bb'.bb_instructions <> []` by
    (Cases_on `sue_expand_insts_supply dfg s bb.bb_instructions` >>
     gvs[sue_expand_block_supply_def] >>
     metis_tac[sue_expand_insts_supply_nonempty]) >>
  Cases_on `bb.bb_instructions` >> Cases_on `bb'.bb_instructions` >>
  gvs[bb_succs_def]
QED

Theorem sue_expand_function_supply_wf_function:
  wf_function fn /\ ir_supply_covers_fn s fn /\ ir_supply_inst_ok s /\
  sue_expand_function_supply s fn = (fn',s') ==>
  wf_function fn'
Proof
  strip_tac >>
  `ALL_DISTINCT (fn_ir_inst_ids fn)` by
    gvs[wf_function_def, fn_inst_ids_distinct_def, fn_ir_inst_ids_def,
        lambdify block_ir_inst_ids_def] >>
  `EVERY (\id. MEM id s.irs_used_inst_ids) (fn_ir_inst_ids fn)` by
    gvs[ir_supply_covers_fn_def, list_subset_def] >>
  drule_all sue_expand_function_supply_ids_ok >>
  simp[sue_ids_supply_ok_def] >> strip_tac >>
  Cases_on `sue_expand_blocks_supply (dfg_build_function fn) s fn.fn_blocks` >>
  gvs[sue_expand_function_supply_def] >>
  drule sue_expand_blocks_supply_labels >> strip_tac >>
  `EVERY bb_well_formed q` by
    (irule sue_expand_blocks_supply_bb_well_formed >>
     goal_assum (drule_at Any) >>
     gvs[wf_function_def, listTheory.EVERY_MEM]) >>
  simp[wf_function_def] >> rpt conj_tac
  >- gvs[wf_function_def, fn_labels_def]
  >- (gvs[wf_function_def, fn_has_entry_def] >>
      Cases_on `q` >> gvs[] >> Cases_on `fn.fn_blocks` >> gvs[])
  >- gvs[listTheory.EVERY_MEM]
  >- (simp[fn_succs_closed_def] >> rpt strip_tac >>
      drule_all sue_expand_blocks_supply_member >> strip_tac >>
      drule sue_expand_block_supply_bb_succs >> strip_tac >>
      gvs[wf_function_def, fn_succs_closed_def, fn_labels_def] >>
      metis_tac[]) >>
  gvs[fn_inst_ids_distinct_def, fn_ir_inst_ids_def, lambdify block_ir_inst_ids_def]
QED

Theorem sue_expand_blocks_supply_head:
  bbs <> [] /\ sue_expand_blocks_supply dfg s bbs = (bbs',s') ==>
  bbs' <> [] /\
  ?si. sue_expand_block_supply dfg s (HD bbs) = (HD bbs',si)
Proof
  Cases_on `bbs` >> simp[sue_expand_blocks_supply_def] >>
  Cases_on `sue_expand_block_supply dfg s h` >>
  Cases_on `sue_expand_blocks_supply dfg r t` >> simp[] >>
  rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem sue_copies_origins:
  !assigns.
    EVERY (\a. ?op v. P op /\ a.inst_opcode = ASSIGN /\
      a.inst_operands = [op] /\ a.inst_outputs = [v]) assigns ==>
    ?cs. MAP FST cs = FLAT (MAP (\a. a.inst_outputs) assigns) /\
      (!v op. MEM (v,op) cs ==> P op) /\
      (!a. MEM a assigns ==>
        ?v op. MEM (v,op) cs /\ a.inst_opcode = ASSIGN /\
               a.inst_operands = [op] /\ a.inst_outputs = [v])
Proof
  Induct >> simp[] >>
  rpt strip_tac >> first_x_assum drule >> strip_tac >>
  qexists_tac `(v,op)::cs` >> simp[] >> metis_tac[]
QED

Theorem sue_expand_ops_supply_origins:
  ir_supply_inst_ok s /\
  sue_expand_ops_supply dfg inst s ops k = (assigns,new_ops,s') ==>
  ?cs. ALL_DISTINCT (MAP FST cs) /\
    s'.irs_used_vars = MAP FST cs ++ s.irs_used_vars /\
    (!v op. MEM (v,op) cs ==> ~MEM v s.irs_used_vars /\ MEM op ops /\
      ((?w. op = Var w) \/ (?c. op = Lit c))) /\
    (!a. MEM a assigns ==>
      ?v op. MEM (v,op) cs /\ a.inst_opcode = ASSIGN /\
             a.inst_operands = [op] /\ a.inst_outputs = [v]) /\
    LIST_REL (\op nop. nop = op \/ ?v. MEM (v,op) cs /\ nop = Var v)
      ops new_ops
Proof
  strip_tac >> drule_all sue_expand_ops_supply_prefix >> strip_tac >>
  drule sue_expand_ops_supply_copies >> strip_tac >>
  `EVERY (\a. ?op v. (MEM op ops /\ ((?w. op = Var w) \/ (?c. op = Lit c))) /\
    a.inst_opcode = ASSIGN /\ a.inst_operands = [op] /\ a.inst_outputs = [v]) assigns` by
    (gvs[listTheory.EVERY_MEM] >> metis_tac[]) >>
  drule (sue_copies_origins |>
    Q.INST [`P` |-> `\op. MEM op ops /\ ((?w. op = Var w) \/ (?c. op = Lit c))`] |>
    BETA_RULE) >> strip_tac >>
  qexists_tac `cs` >> simp[] >> conj_tac
  >- (rpt strip_tac >>
      `MEM v (MAP FST cs)` by (simp[listTheory.MEM_MAP] >> metis_tac[pairTheory.FST]) >>
      gvs[listTheory.EVERY_MEM] >> metis_tac[]) >>
  drule sue_expand_ops_supply_provenance >> strip_tac >>
  irule listTheory.LIST_REL_mono >> goal_assum (drule_at Any) >>
  rpt strip_tac >> gvs[] >>
  `?v' op'. MEM (v',op') cs /\ a.inst_opcode = ASSIGN /\
     a.inst_operands = [op'] /\ a.inst_outputs = [v']` by metis_tac[] >>
  gvs[] >> metis_tac[]
QED

Theorem sue_expand_inst_supply_origins:
  ir_supply_inst_ok s /\
  sue_expand_inst_supply dfg s i = (out,s') ==>
  ?cs. ALL_DISTINCT (MAP FST cs) /\
    s'.irs_used_vars = MAP FST cs ++ s.irs_used_vars /\
    (!v op. MEM (v,op) cs ==> ~MEM v s.irs_used_vars /\ MEM op i.inst_operands /\
      ((?w. op = Var w) \/ (?c. op = Lit c))) /\
    (!j. MEM j out ==>
      (?v op. MEM (v,op) cs /\ j.inst_opcode = ASSIGN /\
        j.inst_outputs = [v] /\ j.inst_operands = [op]) \/
      (j.inst_opcode = i.inst_opcode /\ j.inst_outputs = i.inst_outputs /\
       LIST_REL (\op nop. nop = op \/ ?v. MEM (v,op) cs /\ nop = Var v)
         i.inst_operands j.inst_operands))
Proof
  strip_tac >> Cases_on `sue_should_skip i.inst_opcode`
  >- (gvs[sue_expand_inst_supply_def] >>
      `!xs : operand list. LIST_REL (\op nop. nop = op) xs xs` by
        (Induct >> simp[]) >> simp[]) >>
  Cases_on `sue_expand_ops_supply dfg i s i.inst_operands 0` >>
  PairCases_on `r` >> gvs[sue_expand_inst_supply_def] >>
  drule_all sue_expand_ops_supply_origins >> strip_tac >>
  qexists_tac `cs` >> simp[] >> rpt strip_tac >> gvs[] >> metis_tac[]
QED

Theorem sue_origin_rel_mono:
  LIST_REL (\op nop. nop = op \/ ?v. MEM (v,op) cs /\ nop = Var v) ops nops /\
  (!p. MEM p cs ==> MEM p ds) ==>
  LIST_REL (\op nop. nop = op \/ ?v. MEM (v,op) ds /\ nop = Var v) ops nops
Proof
  strip_tac >> irule listTheory.LIST_REL_mono >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem sue_expand_insts_supply_origins:
  !insts s out s'.
  ir_supply_inst_ok s /\
  (!w. MEM w protected ==> MEM w s.irs_used_vars) /\
  (!i w. MEM i insts /\ MEM (Var w) i.inst_operands ==> MEM w protected) /\
  sue_expand_insts_supply dfg s insts = (out,s') ==>
  ?cs. ALL_DISTINCT (MAP FST cs) /\
    s'.irs_used_vars = MAP FST cs ++ s.irs_used_vars /\
    (!v op. MEM (v,op) cs ==> ~MEM v s.irs_used_vars /\
      ((?w. op = Var w /\ MEM w protected) \/ (?c. op = Lit c))) /\
    (!j. MEM j out ==>
      (?v op. MEM (v,op) cs /\ j.inst_opcode = ASSIGN /\
        j.inst_outputs = [v] /\ j.inst_operands = [op]) \/
      (?i. MEM i insts /\ j.inst_opcode = i.inst_opcode /\
       j.inst_outputs = i.inst_outputs /\
       LIST_REL (\op nop. nop = op \/ ?v. MEM (v,op) cs /\ nop = Var v)
         i.inst_operands j.inst_operands))
Proof
  Induct >> rpt strip_tac
  >- gvs[sue_expand_insts_supply_def] >>
  Cases_on `sue_expand_inst_supply dfg s h` >>
  Cases_on `sue_expand_insts_supply dfg r insts` >>
  gvs[sue_expand_insts_supply_def] >>
  drule_all sue_expand_inst_supply_origins >> strip_tac >>
  `ir_supply_inst_ok r` by
    metis_tac[sue_expand_inst_supply_extends, sue_supply_extends_def] >>
  `!w. MEM w protected ==> MEM w r.irs_used_vars` by simp[] >>
  `!i w. MEM i insts /\ MEM (Var w) i.inst_operands ==> MEM w protected` by
    metis_tac[] >>
  first_x_assum drule_all >> strip_tac >>
  qexists_tac `cs' ++ cs` >>
  simp[listTheory.MAP_APPEND, listTheory.ALL_DISTINCT_APPEND] >>
  conj_tac
  >- (gvs[listTheory.MEM_MAP, pairTheory.EXISTS_PROD] >> metis_tac[]) >>
  conj_tac >- (rpt strip_tac >> gvs[] >> metis_tac[]) >>
  `!ops nops. LIST_REL (\op nop. nop = op \/ ?v. MEM (v,op) cs /\ nop = Var v) ops nops ==>
    LIST_REL (\op nop. nop = op \/ ?v. MEM (v,op) (cs' ++ cs) /\ nop = Var v) ops nops` by
    (rpt strip_tac >> irule sue_origin_rel_mono >> goal_assum (drule_at Any) >> simp[]) >>
  `!ops nops. LIST_REL (\op nop. nop = op \/ ?v. MEM (v,op) cs' /\ nop = Var v) ops nops ==>
    LIST_REL (\op nop. nop = op \/ ?v. MEM (v,op) (cs' ++ cs) /\ nop = Var v) ops nops` by
    (rpt strip_tac >> irule sue_origin_rel_mono >> goal_assum (drule_at Any) >> simp[]) >>
  fs[] >> metis_tac[]
QED

Theorem sue_expand_insts_supply_append:
  !xs s ys.
  sue_expand_insts_supply dfg s (xs ++ ys) =
    case sue_expand_insts_supply dfg s xs of (xs',s1) =>
    case sue_expand_insts_supply dfg s1 ys of (ys',s2) => (xs' ++ ys',s2)
Proof
  Induct
  >- (rpt gen_tac >> simp[sue_expand_insts_supply_def] >>
      Cases_on `sue_expand_insts_supply dfg s ys` >> simp[]) >>
  rpt gen_tac >> simp[sue_expand_insts_supply_def] >>
  Cases_on `sue_expand_inst_supply dfg s h` >>
  Cases_on `sue_expand_insts_supply dfg r xs` >> simp[] >>
  Cases_on `sue_expand_insts_supply dfg r'' ys` >> simp[]
QED

Theorem sue_expand_blocks_supply_flat:
  !bbs s bbs' s'.
  sue_expand_blocks_supply dfg s bbs = (bbs',s') ==>
  sue_expand_insts_supply dfg s (FLAT (MAP (\bb. bb.bb_instructions) bbs)) =
    (FLAT (MAP (\bb. bb.bb_instructions) bbs'),s')
Proof
  Induct >> rpt strip_tac
  >- gvs[sue_expand_blocks_supply_def, sue_expand_insts_supply_def] >>
  Cases_on `sue_expand_insts_supply dfg s h.bb_instructions` >>
  Cases_on `sue_expand_blocks_supply dfg r bbs` >>
  gvs[sue_expand_blocks_supply_def, sue_expand_block_supply_def,
      sue_expand_insts_supply_append] >>
  first_x_assum drule >> simp[]
QED

Theorem sue_expand_function_supply_origins:
  ir_supply_inst_ok s /\ ir_supply_covers_fn s fn /\
  sue_expand_function_supply s fn = (fn',s') ==>
  ?cs. ALL_DISTINCT (MAP FST cs) /\
    s'.irs_used_vars = MAP FST cs ++ s.irs_used_vars /\
    (!v op. MEM (v,op) cs ==> ~MEM v s.irs_used_vars /\
      ((?w. op = Var w /\ MEM w s.irs_used_vars) \/ (?c. op = Lit c))) /\
    (!j. MEM j (fn_insts fn') ==>
      (?v op. MEM (v,op) cs /\ j.inst_opcode = ASSIGN /\
        j.inst_outputs = [v] /\ j.inst_operands = [op]) \/
      (?i. MEM i (fn_insts fn) /\ j.inst_opcode = i.inst_opcode /\
       j.inst_outputs = i.inst_outputs /\
       LIST_REL (\op nop. nop = op \/ ?v. MEM (v,op) cs /\ nop = Var v)
         i.inst_operands j.inst_operands))
Proof
  strip_tac >>
  Cases_on `sue_expand_blocks_supply (dfg_build_function fn) s fn.fn_blocks` >>
  gvs[sue_expand_function_supply_def] >>
  drule sue_expand_blocks_supply_flat >> strip_tac >>
  `!i w. MEM i (FLAT (MAP (\bb. bb.bb_instructions) fn.fn_blocks)) /\
      MEM (Var w) i.inst_operands ==> MEM w s.irs_used_vars` by
    (rpt strip_tac >>
     gvs[listTheory.MEM_FLAT, listTheory.MEM_MAP] >>
     drule_all sue_original_operand_covered >>
     gvs[ir_supply_covers_fn_def, list_subset_def, listTheory.EVERY_MEM]) >>
  drule_at (Pat `sue_expand_insts_supply _ _ _ = _`)
    (sue_expand_insts_supply_origins |> Q.INST [`protected` |-> `s.irs_used_vars`]) >>
  disch_then (qspec_then `s` mp_tac) >>
  (impl_tac >- metis_tac[]) >>
  strip_tac >> qexists_tac `cs` >> simp[] >>
  `!bbs. fn_insts_blocks bbs = FLAT (MAP (\bb. bb.bb_instructions) bbs)` by
    (Induct >> simp[fn_insts_blocks_def]) >>
  gvs[fn_insts_def] >> metis_tac[]
QED

Theorem sue_origins_projection_exists:
  !cs. ALL_DISTINCT (MAP FST cs) /\
    (!v op. MEM (v,op) cs ==> ~(v IN P)) ==>
  ?rho. (!v. v IN P ==> rho v = Var v) /\
    (!v op. MEM (v,op) cs ==> rho v = op)
Proof
  Induct
  >- (simp[] >> qexists_tac `Var` >> simp[]) >>
  gen_tac >> PairCases_on `h` >> simp[] >> rpt strip_tac >>
  `!v op. MEM (v,op) cs ==> ~(v IN P)` by metis_tac[] >>
  first_x_assum drule_all >> strip_tac >>
  qexists_tac `\v. if v = h0 then h1 else rho' v` >> simp[] >>
  conj_tac >- metis_tac[] >>
  rpt strip_tac >> gvs[] >>
  `MEM v (MAP FST cs)` by (simp[listTheory.MEM_MAP] >> metis_tac[pairTheory.FST]) >>
  metis_tac[]
QED

Theorem sue_origin_rel_projection:
  !ops nops.
  LIST_REL (\op nop. nop = op \/ ?v. MEM (v,op) cs /\ nop = Var v) ops nops /\
  (!v op. MEM (v,op) cs ==> project v = op) /\
  (!v. MEM (Var v) ops ==> project v = Var v) ==>
  MAP (\op. case op of Var v => project v | other => other) nops = ops
Proof
  Induct
  >- (Cases_on `nops` >> simp[]) >>
  gen_tac >> Cases_on `nops`
  >- simp[] >>
  rewrite_tac[listTheory.LIST_REL_def, listTheory.MAP, listTheory.CONS_11] >>
  strip_tac >>
  (conj_tac
  >- (gvs[] >> Cases_on `h` >> gvs[] >> metis_tac[]) >>
  first_x_assum irule >> gvs[] >> metis_tac[])
QED

Theorem sue_expand_function_supply_projection:
  ir_supply_inst_ok s /\ ir_supply_covers_fn s fn /\
  sue_expand_function_supply s fn = (fn',s') ==>
  ?project.
    (!j. MEM j (fn_insts fn') ==>
      (j.inst_opcode = ASSIGN /\ ?v. j.inst_outputs = [v] /\
        MAP (\op. case op of Var w => project w | other => other)
          j.inst_operands = [project v]) \/
      (?i. MEM i (fn_insts fn) /\ j.inst_opcode = i.inst_opcode /\
        j.inst_outputs = i.inst_outputs /\
        (!v. MEM v i.inst_outputs ==> project v = Var v) /\
        MAP (\op. case op of Var w => project w | other => other)
          j.inst_operands = i.inst_operands))
Proof
  strip_tac >> drule_all sue_expand_function_supply_origins >> strip_tac >>
  drule_at (Pat `ALL_DISTINCT _`) sue_origins_projection_exists >>
  disch_then (qspec_then `set s.irs_used_vars` mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac >>
  rename1 `!v. MEM v s.irs_used_vars ==> project v = Var v` >>
  `!i v. MEM i (fn_insts fn) /\
    (MEM v i.inst_outputs \/ MEM (Var v) i.inst_operands) ==>
    project v = Var v` by
    (rpt strip_tac >>
     `!bbs. fn_insts_blocks bbs = FLAT (MAP (\bb. bb.bb_instructions) bbs)` by
       (Induct >> simp[fn_insts_blocks_def]) >>
     gvs[fn_insts_def, listTheory.MEM_FLAT, listTheory.MEM_MAP]
     >- (`MEM v (fn_ir_vars fn)` by
       (simp[fn_ir_vars_def, listTheory.MEM_FLAT, listTheory.MEM_MAP] >>
        qexists_tac `block_ir_vars bb` >> conj_tac >- metis_tac[] >>
        simp[block_ir_vars_def, listTheory.MEM_FLAT, listTheory.MEM_MAP] >>
        qexists_tac `inst_ir_vars i` >> simp[inst_ir_vars_def] >> metis_tac[]) >>
         gvs[ir_supply_covers_fn_def, list_subset_def, listTheory.EVERY_MEM]) >>
     drule_all sue_original_operand_covered >>
     gvs[ir_supply_covers_fn_def, list_subset_def, listTheory.EVERY_MEM]) >>
  qexists_tac `project` >> rpt strip_tac >>
  qpat_x_assum `!j. MEM j (fn_insts fn') ==> _` drule >> strip_tac
  >- (disj1_tac >> simp[] >>
      `((?w. op = Var w /\ MEM w s.irs_used_vars) \/ (?c. op = Lit c))` by metis_tac[] >>
      gvs[] >> metis_tac[]) >>
  disj2_tac >> qexists_tac `i` >> simp[] >> conj_tac
  >- metis_tac[] >>
  irule sue_origin_rel_projection >> conj_tac >- metis_tac[] >>
  qexists_tac `cs` >> metis_tac[]
QED

Theorem sue_origin_rel_label_projection:
  !xs ys.
  (!v op. MEM (v,op) cs ==> get_label op = NONE) /\
  LIST_REL (\op nop. nop = op \/ ?v. MEM (v,op) cs /\ nop = Var v) xs ys ==>
  MAP get_label ys = MAP get_label xs
Proof
  Induct_on `xs` >> Cases_on `ys` >>
  simp[] >> rpt strip_tac >> gvs[] >>
  simp[venomStateTheory.get_label_def] >> metis_tac[]
QED

Theorem sue_expand_function_supply_label_projection:
  ir_supply_inst_ok s /\ ir_supply_covers_fn s fn /\
  sue_expand_function_supply s fn = (fn',s') ==>
  !j. MEM j (fn_insts fn') ==>
    (j.inst_opcode = ASSIGN /\ ?op v. j.inst_operands = [op] /\
      j.inst_outputs = [v] /\ get_label op = NONE) \/
    (?i. MEM i (fn_insts fn) /\ j.inst_opcode = i.inst_opcode /\
      j.inst_outputs = i.inst_outputs /\
      MAP get_label j.inst_operands = MAP get_label i.inst_operands)
Proof
  strip_tac >> drule_all sue_expand_function_supply_origins >> strip_tac >>
  `!v op. MEM (v,op) cs ==> get_label op = NONE` by
    (rpt strip_tac >> first_x_assum drule >>
     strip_tac >> gvs[venomStateTheory.get_label_def]) >>
  rpt strip_tac >> qpat_x_assum `!j. MEM j (fn_insts fn') ==> _` drule >>
  strip_tac
  >- (disj1_tac >> simp[] >> metis_tac[]) >>
  disj2_tac >> qexists_tac `i` >> simp[] >>
  irule sue_origin_rel_label_projection >> goal_assum (drule_at Any) >>
  metis_tac[]
QED

Theorem sue_expand_insts_supply_last:
  !insts s outs s'.
  insts <> [] /\ sue_expand_insts_supply dfg s insts = (outs,s') ==>
  outs <> [] /\
  (LAST outs).inst_opcode = (LAST insts).inst_opcode /\
  MAP get_label (LAST outs).inst_operands =
    MAP get_label (LAST insts).inst_operands
Proof
  Induct_on `insts` >> rpt gen_tac >> strip_tac
  >- gvs[] >>
  Cases_on `sue_expand_inst_supply dfg s h` >>
  Cases_on `sue_expand_insts_supply dfg r insts` >>
  gvs[sue_expand_insts_supply_def] >>
  drule sue_expand_inst_supply_nonempty >> strip_tac >>
  Cases_on `insts = []`
  >- (gvs[sue_expand_insts_supply_def] >>
      drule sue_expand_inst_supply_last >>
      drule sue_expand_inst_supply_labels >>
      simp[sue_operand_label_get_label]) >>
  first_x_assum drule_all >> strip_tac >>
  Cases_on `q'` >> gvs[] >>
  pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC, listTheory.APPEND,
    listTheory.LAST_APPEND_CONS] >>
  simp[listTheory.LAST_DEF]
QED

Theorem sue_expand_block_supply_last:
  bb.bb_instructions <> [] /\
  sue_expand_block_supply dfg s bb = (bb',s') ==>
  bb'.bb_instructions <> [] /\
  (LAST bb'.bb_instructions).inst_opcode = (LAST bb.bb_instructions).inst_opcode /\
  MAP get_label (LAST bb'.bb_instructions).inst_operands =
    MAP get_label (LAST bb.bb_instructions).inst_operands
Proof
  strip_tac >>
  Cases_on `sue_expand_insts_supply dfg s bb.bb_instructions` >>
  gvs[sue_expand_block_supply_def] >>
  metis_tac[sue_expand_insts_supply_last]
QED

Theorem sue_expand_blocks_supply_member_forward:
  !bbs s bbs' s' bb.
  sue_expand_blocks_supply dfg s bbs = (bbs',s') /\ MEM bb bbs ==>
  ?bb' si sj. MEM bb' bbs' /\ sue_expand_block_supply dfg si bb = (bb',sj)
Proof
  Induct_on `bbs` >> rpt gen_tac >> strip_tac
  >- gvs[] >>
  Cases_on `sue_expand_block_supply dfg s h` >>
  Cases_on `sue_expand_blocks_supply dfg r bbs` >>
  gvs[sue_expand_blocks_supply_def] >> metis_tac[]
QED

(* Replaying allocation with a repaired used instruction-ID set. *)
Theorem sue_expand_function_supply_used_inst_ids:
  FST (sue_expand_function_supply (s with irs_used_inst_ids := ids) fn) =
  FST (sue_expand_function_supply s fn)
Proof
  simp[sue_expand_function_supply_def] >>
  Cases_on `sue_expand_blocks_supply (dfg_build_function fn) s fn.fn_blocks` >>
  drule sue_expand_blocks_supply_used_inst_ids >>
  disch_then (qspec_then `ids` strip_assume_tac) >>
  simp[]
QED

Theorem sue_supply_replay:
  ir_supply_covers_fn s fn /\
  sue_expand_function_supply s fn = (fn',s') ==>
  ?t t'. ir_supply_covers_fn t fn /\ ir_supply_inst_ok t /\
    sue_expand_function_supply t fn = (fn',t')
Proof
  strip_tac >>
  qexists_tac `s with irs_used_inst_ids := fn_ir_inst_ids fn` >>
  mp_tac (Q.INST [`ids` |-> `fn_ir_inst_ids fn`]
    sue_expand_function_supply_used_inst_ids) >>
  Cases_on `sue_expand_function_supply
    (s with irs_used_inst_ids := fn_ir_inst_ids fn) fn` >>
  gvs[ir_supply_covers_fn_def, list_subset_def, ir_supply_inst_ok_def,
      listTheory.EVERY_MEM]
QED

Theorem sue_expand_ops_supply_use_origin:
  sue_expand_ops_supply dfg inst s ops idx = (assigns,new_ops,s') /\
  MEM (Var v) new_ops ==>
  MEM (Var v) ops \/ ?a. MEM a assigns /\ MEM v a.inst_outputs
Proof
  strip_tac >> drule sue_expand_ops_supply_provenance >>
  simp[listTheory.LIST_REL_EL_EQN] >> strip_tac >>
  qpat_x_assum `MEM (Var v) new_ops` mp_tac >>
  simp[Once listTheory.MEM_EL] >> strip_tac >>
  first_x_assum (qspec_then `n` mp_tac) >>
  simp[] >> strip_tac >> gvs[]
  >- (disj1_tac >> simp[listTheory.MEM_EL] >>
      qexists_tac `n` >> simp[]) >>
  disj2_tac >> qexists_tac `a` >> simp[]
QED

Theorem sue_expand_inst_supply_use_origin:
  sue_expand_inst_supply dfg s inst = (out,s') /\
  k < LENGTH out /\ MEM (Var v) (EL k out).inst_operands ==>
  MEM (Var v) inst.inst_operands \/
  ?h. h < k /\ MEM v (EL h out).inst_outputs
Proof
  strip_tac >> Cases_on `sue_should_skip inst.inst_opcode`
  >- (gvs[sue_expand_inst_supply_def] >>
      `k = 0` by decide_tac >> gvs[]) >>
  Cases_on `sue_expand_ops_supply dfg inst s inst.inst_operands 0` >>
  PairCases_on `r` >>
  gvs[sue_expand_inst_supply_def] >>
  rename1 `sue_expand_ops_supply dfg inst s inst.inst_operands 0 =
    (assigns,new_ops,s')` >>
  Cases_on `k < LENGTH assigns`
  >- (gvs[listTheory.EL_APPEND_EQN] >>
      drule sue_expand_ops_supply_copies >>
      simp[listTheory.EVERY_MEM] >> strip_tac >>
      `MEM (EL k assigns) assigns` by metis_tac[listTheory.MEM_EL] >>
      first_x_assum drule >> strip_tac >> gvs[] >> metis_tac[]) >>
  `k = LENGTH assigns` by decide_tac >>
  gvs[listTheory.EL_APPEND_EQN] >>
  drule_all sue_expand_ops_supply_use_origin >> strip_tac
  >- simp[] >>
  disj2_tac >>
  qpat_x_assum `MEM a assigns` mp_tac >>
  simp[Once listTheory.MEM_EL] >>
  disch_then (qx_choose_then `h` strip_assume_tac) >>
  qexists_tac `h` >> gvs[listTheory.EL_APPEND_EQN]
QED

Theorem sue_expand_inst_supply_phi:
  sue_expand_inst_supply dfg s inst = (out,s') /\
  MEM a out /\ a.inst_opcode = PHI ==>
  out = [inst] /\ a = inst /\ inst.inst_opcode = PHI
Proof
  strip_tac >> Cases_on `sue_should_skip inst.inst_opcode`
  >- gvs[sue_expand_inst_supply_def] >>
  Cases_on `sue_expand_ops_supply dfg inst s inst.inst_operands 0` >>
  PairCases_on `r` >> gvs[sue_expand_inst_supply_def] >>
  drule sue_expand_ops_supply_copies >>
  simp[listTheory.EVERY_MEM] >> strip_tac >>
  gvs[listTheory.MEM_APPEND, listTheory.MEM]
  >- (first_x_assum drule >> simp[]) >>
  gvs[sue_should_skip_def]
QED

Theorem sue_expand_inst_supply_outputs_distinct:
  ir_supply_inst_ok s /\ ALL_DISTINCT inst.inst_outputs /\
  EVERY (\v. MEM v s.irs_used_vars) inst.inst_outputs /\
  sue_expand_inst_supply dfg s inst = (out,s') ==>
  ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) out)) /\
  !v. MEM v (FLAT (MAP (\i. i.inst_outputs) out)) /\
      MEM v s.irs_used_vars ==> MEM v inst.inst_outputs
Proof
  strip_tac >> drule_all sue_expand_inst_supply_segment >> strip_tac >>
  gvs[listTheory.MAP_APPEND, listTheory.FLAT_APPEND,
      listTheory.ALL_DISTINCT_APPEND, listTheory.EVERY_MEM] >>
  metis_tac[]
QED

Theorem sue_expand_inst_supply_outputs_covered:
  ir_supply_inst_ok s /\
  EVERY (\v. MEM v s.irs_used_vars) inst.inst_outputs /\
  sue_expand_inst_supply dfg s inst = (out,s') ==>
  EVERY (\v. MEM v s'.irs_used_vars)
    (FLAT (MAP (\i. i.inst_outputs) out))
Proof
  strip_tac >> drule_all sue_expand_inst_supply_segment >> strip_tac >>
  gvs[listTheory.MAP_APPEND, listTheory.FLAT_APPEND,
      listTheory.EVERY_MEM] >> metis_tac[]
QED

Theorem sue_expand_insts_supply_outputs_distinct:
  !insts dfg s out s'.
  ir_supply_inst_ok s /\
  ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) insts)) /\
  EVERY (\v. MEM v s.irs_used_vars)
    (FLAT (MAP (\i. i.inst_outputs) insts)) /\
  sue_expand_insts_supply dfg s insts = (out,s') ==>
  ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) out)) /\
  !v. MEM v (FLAT (MAP (\i. i.inst_outputs) out)) /\
      MEM v s.irs_used_vars ==>
      MEM v (FLAT (MAP (\i. i.inst_outputs) insts))
Proof
  Induct >> simp[sue_expand_insts_supply_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `sue_expand_inst_supply dfg s h` >>
  rename1 `sue_expand_inst_supply dfg s h = (head_out,s1)` >>
  Cases_on `sue_expand_insts_supply dfg s1 insts` >>
  rename1 `sue_expand_insts_supply dfg s1 insts = (tail_out,s2)` >>
  gvs[sue_expand_insts_supply_def, listTheory.ALL_DISTINCT_APPEND,
      listTheory.EVERY_APPEND] >>
  `sue_supply_extends s s1` by
    metis_tac[sue_expand_inst_supply_extends] >>
  `ir_supply_inst_ok s1` by gvs[sue_supply_extends_def] >>
  `!v. MEM v s.irs_used_vars ==> MEM v s1.irs_used_vars` by
    metis_tac[sue_supply_extends_members] >>
  `EVERY (\v. MEM v s1.irs_used_vars)
     (FLAT (MAP (\i. i.inst_outputs) insts))` by
    (gvs[listTheory.EVERY_MEM] >> metis_tac[]) >>
  drule_all sue_expand_inst_supply_outputs_distinct >> strip_tac >>
  drule_all sue_expand_inst_supply_outputs_covered >> strip_tac >>
  first_x_assum (qspecl_then [`dfg`,`s1`,`tail_out`,`s'`] mp_tac) >>
  simp[] >> strip_tac >>
  gvs[listTheory.MAP_APPEND, listTheory.FLAT_APPEND,
      listTheory.ALL_DISTINCT_APPEND, listTheory.EVERY_MEM] >>
  metis_tac[]
QED

Theorem sue_expand_insts_supply_outputs_covered:
  !insts dfg s out s'.
  ir_supply_inst_ok s /\
  EVERY (\v. MEM v s.irs_used_vars)
    (FLAT (MAP (\i. i.inst_outputs) insts)) /\
  sue_expand_insts_supply dfg s insts = (out,s') ==>
  EVERY (\v. MEM v s'.irs_used_vars)
    (FLAT (MAP (\i. i.inst_outputs) out))
Proof
  Induct >> simp[sue_expand_insts_supply_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `sue_expand_inst_supply dfg s h` >>
  rename1 `sue_expand_inst_supply dfg s h = (head_out,s1)` >>
  Cases_on `sue_expand_insts_supply dfg s1 insts` >>
  rename1 `sue_expand_insts_supply dfg s1 insts = (tail_out,s2)` >>
  gvs[sue_expand_insts_supply_def, listTheory.EVERY_APPEND] >>
  `sue_supply_extends s s1` by
    metis_tac[sue_expand_inst_supply_extends] >>
  `ir_supply_inst_ok s1` by gvs[sue_supply_extends_def] >>
  `!v. MEM v s.irs_used_vars ==> MEM v s1.irs_used_vars` by
    metis_tac[sue_supply_extends_members] >>
  `EVERY (\v. MEM v s1.irs_used_vars)
     (FLAT (MAP (\i. i.inst_outputs) insts))` by
    (gvs[listTheory.EVERY_MEM] >> metis_tac[]) >>
  drule_all sue_expand_inst_supply_outputs_covered >> strip_tac >>
  first_x_assum (qspecl_then [`dfg`,`s1`,`tail_out`,`s'`] mp_tac) >>
  simp[] >> strip_tac >>
  `sue_supply_extends s1 s'` by
    metis_tac[sue_expand_insts_supply_extends] >>
  drule sue_supply_extends_members >> strip_tac >>
  gvs[listTheory.MAP_APPEND, listTheory.FLAT_APPEND,
      listTheory.EVERY_MEM] >> metis_tac[]
QED

Theorem sue_expand_block_supply_outputs_distinct:
  ir_supply_inst_ok s /\
  ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions)) /\
  EVERY (\v. MEM v s.irs_used_vars)
    (FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions)) /\
  sue_expand_block_supply dfg s bb = (out,s') ==>
  ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) out.bb_instructions)) /\
  (!v. MEM v (FLAT (MAP (\i. i.inst_outputs) out.bb_instructions)) /\
       MEM v s.irs_used_vars ==>
       MEM v (FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions))) /\
  EVERY (\v. MEM v s'.irs_used_vars)
    (FLAT (MAP (\i. i.inst_outputs) out.bb_instructions))
Proof
  strip_tac >>
  Cases_on `sue_expand_insts_supply dfg s bb.bb_instructions` >>
  gvs[sue_expand_block_supply_def] >>
  metis_tac[sue_expand_insts_supply_outputs_distinct,
            sue_expand_insts_supply_outputs_covered]
QED

Theorem sue_expand_blocks_supply_outputs_distinct:
  !bbs dfg s out s'.
  ir_supply_inst_ok s /\
  ALL_DISTINCT (FLAT (MAP (\bb.
    FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions)) bbs)) /\
  EVERY (\v. MEM v s.irs_used_vars) (FLAT (MAP (\bb.
    FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions)) bbs)) /\
  sue_expand_blocks_supply dfg s bbs = (out,s') ==>
  ALL_DISTINCT (FLAT (MAP (\bb.
    FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions)) out)) /\
  !v. MEM v (FLAT (MAP (\bb.
        FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions)) out)) /\
      MEM v s.irs_used_vars ==>
      MEM v (FLAT (MAP (\bb.
        FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions)) bbs))
Proof
  Induct >> simp[sue_expand_blocks_supply_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `sue_expand_block_supply dfg s h` >>
  rename1 `sue_expand_block_supply dfg s h = (head_out,s1)` >>
  Cases_on `sue_expand_blocks_supply dfg s1 bbs` >>
  rename1 `sue_expand_blocks_supply dfg s1 bbs = (tail_out,s2)` >>
  gvs[sue_expand_blocks_supply_def, listTheory.ALL_DISTINCT_APPEND,
      listTheory.EVERY_APPEND] >>
  `sue_supply_extends s s1` by
    metis_tac[sue_expand_block_supply_extends] >>
  `ir_supply_inst_ok s1` by gvs[sue_supply_extends_def] >>
  `!v. MEM v s.irs_used_vars ==> MEM v s1.irs_used_vars` by
    metis_tac[sue_supply_extends_members] >>
  `EVERY (\v. MEM v s1.irs_used_vars) (FLAT (MAP (\bb.
     FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions)) bbs))` by
    (gvs[listTheory.EVERY_MEM] >> metis_tac[]) >>
  drule_all sue_expand_block_supply_outputs_distinct >> strip_tac >>
  first_x_assum (qspecl_then [`dfg`,`s1`,`tail_out`,`s'`] mp_tac) >>
  simp[] >> strip_tac >>
  gvs[listTheory.ALL_DISTINCT_APPEND, listTheory.EVERY_MEM] >>
  metis_tac[]
QED

Theorem sue_expand_function_supply_ssa_form:
  ir_supply_inst_ok s /\ ir_supply_covers_fn s fn /\ ssa_form fn /\
  sue_expand_function_supply s fn = (fn',s') ==> ssa_form fn'
Proof
  strip_tac >>
  `!bbs. fn_insts_blocks bbs = FLAT (MAP (\bb. bb.bb_instructions) bbs)` by
    (Induct >> simp[fn_insts_blocks_def]) >>
  `EVERY (\v. MEM v s.irs_used_vars)
     (FLAT (MAP (\i. i.inst_outputs) (fn_insts fn)))` by
    (gvs[ir_supply_covers_fn_def, list_subset_def, fn_ir_vars_def,
         block_ir_vars_def, inst_ir_vars_def, fn_insts_def,
         listTheory.EVERY_MEM, listTheory.MEM_FLAT,
         listTheory.MEM_MAP] >>
     metis_tac[inst_ir_vars_def, listTheory.MEM_FLAT,
               listTheory.MEM_MAP, listTheory.MEM_APPEND]) >>
  Cases_on `sue_expand_blocks_supply (dfg_build_function fn) s fn.fn_blocks` >>
  gvs[sue_expand_function_supply_def, ssa_form_def, fn_insts_def] >>
  drule sue_expand_blocks_supply_flat >> strip_tac >>
  drule_all sue_expand_insts_supply_outputs_distinct >> simp[]
QED

Theorem sue_expand_function_supply_cfg_edge:
  sue_expand_function_supply s fn = (fn',s') ==>
  !a b. fn_cfg_edge fn' a b <=> fn_cfg_edge fn a b
Proof
  strip_tac >>
  Cases_on `sue_expand_blocks_supply (dfg_build_function fn) s fn.fn_blocks` >>
  gvs[sue_expand_function_supply_def] >>
  rpt gen_tac >> simp[fn_cfg_edge_def] >> eq_tac >> strip_tac
  >- (drule_all sue_expand_blocks_supply_member >> strip_tac >>
      drule sue_expand_block_supply_bb_succs >> strip_tac >>
      drule sue_expand_block_supply_label >> strip_tac >>
      qexists_tac `bb'` >> gvs[]) >>
  drule_all sue_expand_blocks_supply_member_forward >> strip_tac >>
  drule sue_expand_block_supply_bb_succs >> strip_tac >>
  drule sue_expand_block_supply_label >> strip_tac >>
  qexists_tac `bb'` >> gvs[]
QED

Theorem sue_expand_function_supply_entry_label:
  sue_expand_function_supply s fn = (fn',s') ==>
  fn_entry_label fn' = fn_entry_label fn
Proof
  strip_tac >>
  Cases_on `sue_expand_blocks_supply (dfg_build_function fn) s fn.fn_blocks` >>
  gvs[sue_expand_function_supply_def] >>
  drule sue_expand_blocks_supply_labels >> strip_tac >>
  Cases_on `fn.fn_blocks` >> Cases_on `q` >>
  gvs[fn_entry_label_def, entry_block_def]
QED

Theorem sue_expand_function_supply_reachable:
  sue_expand_function_supply s fn = (fn',s') ==>
  !lbl. fn_reachable fn' lbl <=> fn_reachable fn lbl
Proof
  strip_tac >>
  drule sue_expand_function_supply_cfg_edge >> strip_tac >>
  drule sue_expand_function_supply_entry_label >> strip_tac >>
  `fn_cfg_edge fn' = fn_cfg_edge fn` by simp[FUN_EQ_THM] >>
  simp[fn_reachable_def]
QED

Theorem sue_expand_function_supply_path:
  sue_expand_function_supply s fn = (fn',s') ==>
  !path. is_fn_path fn' path <=> is_fn_path fn path
Proof
  strip_tac >> drule sue_expand_function_supply_cfg_edge >> strip_tac >>
  Induct >> simp[is_fn_path_def] >>
  Cases_on `path` >> gvs[is_fn_path_def]
QED

Theorem sue_expand_function_supply_dominates:
  sue_expand_function_supply s fn = (fn',s') ==>
  !d n. fn_dominates fn' d n <=> fn_dominates fn d n
Proof
  strip_tac >>
  drule sue_expand_function_supply_reachable >> strip_tac >>
  drule sue_expand_function_supply_entry_label >> strip_tac >>
  drule sue_expand_function_supply_path >> strip_tac >>
  simp[fn_dominates_def]
QED

Theorem sue_expand_function_supply_all_reachable:
  all_reachable fn /\ sue_expand_function_supply s fn = (fn',s') ==>
  all_reachable fn'
Proof
  strip_tac >> drule sue_expand_function_supply_reachable >> strip_tac >>
  Cases_on `sue_expand_blocks_supply (dfg_build_function fn) s fn.fn_blocks` >>
  gvs[sue_expand_function_supply_def, all_reachable_def] >>
  rpt strip_tac >>
  drule_all sue_expand_blocks_supply_member >> strip_tac >>
  drule sue_expand_block_supply_label >> strip_tac >> metis_tac[]
QED

Theorem sue_reachable_self_dominates:
  fn_reachable fn lbl ==> fn_dominates fn lbl lbl
Proof
  simp[fn_dominates_def] >> rpt strip_tac >>
  Cases_on `path` >> gvs[rich_listTheory.MEM_LAST]
QED

Theorem sue_segment_position_bound:
  i < LENGTH segs /\ j < LENGTH (EL i segs) ==>
  sue_segment_offset segs i + j < LENGTH (FLAT segs)
Proof
  strip_tac >>
  `sue_segment_offset segs (SUC i) <= LENGTH (FLAT segs)` by
    (irule sue_segment_offset_bound >> simp[]) >>
  drule sue_segment_offset_suc >> simp[]
QED

Theorem sue_segment_positions_ordered:
  i < j /\ j < LENGTH segs /\
  h < LENGTH (EL i segs) ==>
  sue_segment_offset segs i + h < sue_segment_offset segs j + k
Proof
  strip_tac >>
  `sue_segment_offset segs (SUC i) <= sue_segment_offset segs j` by
    (irule sue_segment_offset_mono >> simp[]) >>
  `i < LENGTH segs` by decide_tac >>
  drule sue_segment_offset_suc >> simp[]
QED

Theorem sue_segments_supply_last_outputs:
  sue_segments_supply dfg s insts = (segs,s') /\ i < LENGTH insts ==>
  sue_segment_offset segs i + (LENGTH (EL i segs) - 1) < LENGTH (FLAT segs) /\
  (EL (sue_segment_offset segs i + (LENGTH (EL i segs) - 1))
      (FLAT segs)).inst_outputs = (EL i insts).inst_outputs
Proof
  strip_tac >>
  drule sue_segments_supply_length >> strip_tac >>
  drule_all sue_segments_supply_index >> strip_tac >>
  drule sue_expand_inst_supply_nonempty >> strip_tac >>
  `LENGTH (EL i segs) - 1 < LENGTH (EL i segs)` by
    (Cases_on `EL i segs` >> gvs[]) >>
  conj_tac
  >- (irule sue_segment_position_bound >> simp[]) >>
  simp[sue_segment_offset_el] >>
  drule sue_expand_inst_supply_last >> strip_tac >>
  gvs[listTheory.LAST_EL, arithmeticTheory.PRE_SUB1]
QED

Theorem sue_segments_supply_use_origin:
  sue_segments_supply dfg s insts = (segs,s') /\
  k < LENGTH (FLAT segs) /\
  MEM (Var v) (EL k (FLAT segs)).inst_operands ==>
  (?i j. i < LENGTH insts /\ j < LENGTH (EL i segs) /\
     k = sue_segment_offset segs i + j /\
     MEM (Var v) (EL i insts).inst_operands) \/
  ?h. h < k /\ MEM v (EL h (FLAT segs)).inst_outputs
Proof
  strip_tac >> drule_all sue_segment_interior >> strip_tac >>
  drule sue_segments_supply_length >> strip_tac >>
  `i < LENGTH insts` by decide_tac >>
  drule_all sue_segments_supply_index >> strip_tac >>
  `EL k (FLAT segs) = EL j (EL i segs)` by
    metis_tac[sue_segment_offset_el] >>
  qpat_x_assum `MEM (Var v) (EL k (FLAT segs)).inst_operands` mp_tac >>
  asm_rewrite_tac[] >> strip_tac >>
  drule_all sue_expand_inst_supply_use_origin >> strip_tac
  >- (disj1_tac >> qexistsl [`i`,`j`] >> simp[]) >>
  disj2_tac >> qexists_tac `sue_segment_offset segs i + h` >>
  `h < LENGTH (EL i segs)` by decide_tac >>
  simp[sue_segment_offset_el]
QED

Theorem sue_segments_supply_definition_before:
  sue_segments_supply dfg s insts = (segs,s') /\
  i < j /\ j < LENGTH insts /\ k < LENGTH (EL j segs) ==>
  ?h. h < sue_segment_offset segs j + k /\
      h < LENGTH (FLAT segs) /\
      (EL h (FLAT segs)).inst_outputs = (EL i insts).inst_outputs
Proof
  strip_tac >>
  drule sue_segments_supply_length >> strip_tac >>
  `i < LENGTH insts` by decide_tac >>
  drule_all sue_segments_supply_last_outputs >> strip_tac >>
  qexists_tac `sue_segment_offset segs i + (LENGTH (EL i segs) - 1)` >>
  `LENGTH (EL i segs) - 1 < LENGTH (EL i segs)` by
    (drule_all sue_segments_supply_index >> strip_tac >>
     drule sue_expand_inst_supply_nonempty >>
     Cases_on `EL i segs` >> simp[]) >>
  metis_tac[sue_segment_positions_ordered]
QED

Theorem sue_segments_supply_endpoint_outputs:
  sue_segments_supply dfg s insts = (segs,s') /\
  MEM inst insts /\ MEM v inst.inst_outputs ==>
  ?h. h < LENGTH (FLAT segs) /\ MEM v (EL h (FLAT segs)).inst_outputs
Proof
  strip_tac >>
  qpat_x_assum `MEM inst insts` mp_tac >> simp[Once listTheory.MEM_EL] >>
  disch_then (qx_choose_then `i` strip_assume_tac) >>
  drule_all sue_segments_supply_last_outputs >> strip_tac >>
  qexists_tac `sue_segment_offset segs i + (LENGTH (EL i segs) - 1)` >>
  gvs[]
QED

Theorem sue_segments_supply_phi:
  sue_segments_supply dfg s insts = (segs,s') /\
  k < LENGTH (FLAT segs) /\ (EL k (FLAT segs)).inst_opcode = PHI ==>
  ?i. i < LENGTH insts /\ EL k (FLAT segs) = EL i insts /\
      EL i segs = [EL i insts]
Proof
  strip_tac >> drule_all sue_segment_interior >> strip_tac >>
  drule sue_segments_supply_length >> strip_tac >>
  `i < LENGTH insts` by decide_tac >>
  drule_all sue_segments_supply_index >> strip_tac >>
  `EL k (FLAT segs) = EL j (EL i segs)` by
    metis_tac[sue_segment_offset_el] >>
  `MEM (EL k (FLAT segs)) (EL i segs)` by
    metis_tac[listTheory.MEM_EL] >>
  drule_all sue_expand_inst_supply_phi >> strip_tac >>
  qexists_tac `i` >> simp[]
QED

Theorem sue_expand_block_supply_output_member:
  sue_expand_block_supply dfg s bb = (bb',s') /\
  MEM inst bb.bb_instructions /\ MEM v inst.inst_outputs ==>
  ?inst'. MEM inst' bb'.bb_instructions /\ MEM v inst'.inst_outputs
Proof
  strip_tac >> Cases_on `sue_segments_supply dfg s bb.bb_instructions` >>
  drule sue_segments_supply_flat >> strip_tac >>
  gvs[sue_expand_block_supply_def] >>
  drule_all sue_segments_supply_endpoint_outputs >> strip_tac >>
  qexists_tac `EL h (FLAT q)` >> simp[] >>
  metis_tac[listTheory.MEM_EL]
QED

Theorem sue_expand_function_supply_available_endpoint:
  sue_expand_function_supply s fn = (fn',s') /\
  target'.bb_label = target.bb_label /\
  def_available_at fn target NONE v ==>
  def_available_at fn' target' NONE v
Proof
  strip_tac >>
  drule sue_expand_function_supply_dominates >> strip_tac >>
  qpat_x_assum `def_available_at fn target NONE v` mp_tac >>
  simp[def_available_at_def] >> strip_tac >>
  Cases_on `sue_expand_blocks_supply (dfg_build_function fn) s fn.fn_blocks` >>
  gvs[sue_expand_function_supply_def] >>
  drule_all sue_expand_blocks_supply_member_forward >> strip_tac >>
  drule_all sue_expand_block_supply_output_member >> strip_tac >>
  drule sue_expand_block_supply_label >> strip_tac >>
  simp[def_available_at_def] >>
  qexistsl [`bb'`,`inst'`] >> simp[]
QED

Theorem sue_available_local:
  MEM bb fn.fn_blocks /\ fn_reachable fn bb.bb_label /\
  h < k /\ k < LENGTH bb.bb_instructions /\
  MEM v (EL h bb.bb_instructions).inst_outputs ==>
  def_available_at fn bb (SOME (EL k bb.bb_instructions)) v
Proof
  strip_tac >> drule sue_reachable_self_dominates >> strip_tac >>
  simp[def_available_at_def] >>
  qexistsl [`bb`,`EL h bb.bb_instructions`] >> simp[] >>
  conj_tac >- metis_tac[listTheory.MEM_EL, arithmeticTheory.LESS_TRANS] >>
  qexistsl [`h`,`k`] >> simp[]
QED

Theorem sue_expand_function_supply_phi_edge_uses:
  sue_expand_function_supply s fn = (fn',s') /\
  bb'.bb_label = bb.bb_label /\ phi_edge_uses_wf fn bb inst ==>
  phi_edge_uses_wf fn' bb' inst
Proof
  strip_tac >>
  drule sue_expand_function_supply_cfg_edge >> strip_tac >>
  `!pred_bb. MEM pred_bb fn.fn_blocks ==>
    ?pred_bb'. MEM pred_bb' fn'.fn_blocks /\
      pred_bb'.bb_label = pred_bb.bb_label` by
    (rpt strip_tac >>
     Cases_on `sue_expand_blocks_supply (dfg_build_function fn) s fn.fn_blocks` >>
     gvs[sue_expand_function_supply_def] >>
     drule_all sue_expand_blocks_supply_member_forward >> strip_tac >>
     drule sue_expand_block_supply_label >> strip_tac >> metis_tac[]) >>
  gvs[phi_edge_uses_wf_def] >> rpt strip_tac >>
  qpat_x_assum `!pred v. _` drule >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  drule_all sue_expand_function_supply_available_endpoint >> strip_tac >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem sue_expand_function_supply_available_ordinary:
  sue_expand_function_supply s fn = (fn',s') /\ wf_function fn /\
  MEM bb fn.fn_blocks /\ MEM bb' fn'.fn_blocks /\
  bb'.bb_label = bb.bb_label /\
  sue_segments_supply (dfg_build_function fn) si bb.bb_instructions = (segs,sj) /\
  bb'.bb_instructions = FLAT segs /\
  j < LENGTH bb.bb_instructions /\ k < LENGTH (EL j segs) /\
  def_available_at fn bb (SOME (EL j bb.bb_instructions)) v ==>
  def_available_at fn' bb'
    (SOME (EL (sue_segment_offset segs j + k) bb'.bb_instructions)) v
Proof
  strip_tac >>
  `!a b. MEM a fn.fn_blocks /\ MEM b fn.fn_blocks /\
     a.bb_label = b.bb_label ==> a = b` by
    metis_tac[venomExecProofsTheory.same_label_same_block] >>
  `fn_inst_ids_distinct fn` by gvs[wf_function_def] >>
  drule sue_expand_function_supply_dominates >> strip_tac >>
  qpat_x_assum `def_available_at fn bb _ v` mp_tac >>
  simp[def_available_at_def] >> strip_tac >>
  Cases_on `def_bb = bb`
  >- (gvs[] >>
      `j' = j` by metis_tac[venomExecProofsTheory.inst_ids_el_eq] >> gvs[] >>
      drule_all sue_segments_supply_definition_before >> strip_tac >>
      simp[def_available_at_def] >>
      qexistsl [`bb'`,`EL h (FLAT segs)`] >> simp[] >>
      conj_tac >- metis_tac[listTheory.MEM_EL] >>
      qexistsl [`h`,`sue_segment_offset segs j + k`] >>
      simp[] >>
      once_rewrite_tac[arithmeticTheory.ADD_COMM] >>
      irule sue_segment_position_bound >>
      drule sue_segments_supply_length >> simp[]) >>
  Cases_on `sue_expand_blocks_supply (dfg_build_function fn) s fn.fn_blocks` >>
  gvs[sue_expand_function_supply_def] >>
  drule_all sue_expand_blocks_supply_member_forward >> strip_tac >>
  drule_all sue_expand_block_supply_output_member >> strip_tac >>
  drule sue_expand_block_supply_label >> strip_tac >>
  simp[def_available_at_def] >>
  qexistsl [`bb''`,`inst'`] >> simp[] >> metis_tac[]
QED

Theorem sue_expand_function_supply_def_dominates_uses:
  wf_function fn /\ all_reachable fn /\ def_dominates_uses fn /\
  sue_expand_function_supply s fn = (fn',s') ==>
  def_dominates_uses fn'
Proof
  strip_tac >>
  `all_reachable fn'` by metis_tac[sue_expand_function_supply_all_reachable] >>
  simp[def_dominates_uses_def] >> rpt gen_tac >> strip_tac >>
  rename1 `MEM bb' fn'.fn_blocks` >>
  `?bb si sj. MEM bb fn.fn_blocks /\
     sue_expand_block_supply (dfg_build_function fn) si bb = (bb',sj)` by
    (Cases_on `sue_expand_blocks_supply (dfg_build_function fn) s fn.fn_blocks` >>
     gvs[sue_expand_function_supply_def] >>
     metis_tac[sue_expand_blocks_supply_member]) >>
  drule sue_expand_block_supply_label >> strip_tac >>
  Cases_on `sue_segments_supply (dfg_build_function fn) si bb.bb_instructions` >>
  rename1 `sue_segments_supply _ _ _ = (segs,t)` >>
  drule sue_segments_supply_flat >> strip_tac >>
  `bb'.bb_instructions = FLAT segs` by gvs[sue_expand_block_supply_def] >>
  qpat_x_assum `MEM inst bb'.bb_instructions` mp_tac >>
  simp[Once listTheory.MEM_EL] >>
  disch_then (qx_choose_then `k` strip_assume_tac) >> gvs[] >>
  Cases_on `(EL k (FLAT segs)).inst_opcode = PHI`
  >- (simp[] >> drule_all sue_segments_supply_phi >> strip_tac >>
      `phi_edge_uses_wf fn bb (EL i bb.bb_instructions)` by
        (qpat_x_assum `def_dominates_uses fn` mp_tac >>
         simp[def_dominates_uses_def] >>
         metis_tac[listTheory.MEM_EL]) >>
      metis_tac[sue_expand_function_supply_phi_edge_uses]) >>
  simp[] >> rpt strip_tac >>
  drule_all sue_segments_supply_use_origin >> strip_tac
  >- (`(EL i bb.bb_instructions).inst_opcode <> PHI` by
        (strip_tac >> drule sue_segments_supply_length >> strip_tac >>
         drule_all sue_segments_supply_index >> strip_tac >>
         `EL i segs = [EL i bb.bb_instructions]` by
           gvs[sue_expand_inst_supply_def, sue_should_skip_def] >>
         `EL k (FLAT segs) = EL j (EL i segs)` by
           metis_tac[sue_segment_offset_el] >>
         gvs[]) >>
      `def_available_at fn bb (SOME (EL i bb.bb_instructions)) v` by
        (qpat_x_assum `def_dominates_uses fn` mp_tac >>
         simp[def_dominates_uses_def] >> metis_tac[listTheory.MEM_EL]) >>
      drule_all sue_expand_function_supply_available_ordinary >>
      simp[]) >>
  `fn_reachable fn' bb'.bb_label` by metis_tac[all_reachable_def] >>
  `k < LENGTH bb'.bb_instructions /\
   MEM v (EL h bb'.bb_instructions).inst_outputs` by simp[] >>
  drule_all sue_available_local >> simp[]
QED

(* Counterexample: expansion creates variable uses in an unreachable block. *)
Definition sue_ce_fn_def:
  sue_ce_fn = mk_raw_function "ce"
    [<| bb_label := "e"; bb_instructions := [mk_inst 0 STOP [] []] |>;
     <| bb_label := "u"; bb_instructions :=
       [mk_inst 1 ADD [Lit 0w; Lit 1w] ["x"]; mk_inst 2 STOP [] []] |>]
End

Definition sue_ce_supply_def:
  sue_ce_supply = <| irs_next_inst := 3; irs_next_var := 0;
    irs_next_label := 0; irs_used_inst_ids := [0;1;2];
    irs_used_vars := ["x"]; irs_used_labels := ["ce";"e";"u"] |>
End

Definition sue_ce_out_def:
  sue_ce_out = mk_raw_function "ce"
    [<| bb_label := "e"; bb_instructions := [mk_inst 0 STOP [] []] |>;
     <| bb_label := "u"; bb_instructions :=
       [mk_inst 4 ASSIGN [Lit 0w] ["formal_var_1"];
        mk_inst 3 ASSIGN [Lit 1w] ["formal_var_0"];
        mk_inst 1 ADD [Var "formal_var_1"; Var "formal_var_0"] ["x"];
        mk_inst 2 STOP [] []] |>]
End

Theorem sue_ce_input:
  wf_ssa sue_ce_fn /\ fn_inst_wf sue_ce_fn /\
  wf_function sue_ce_fn /\ ir_supply_covers_fn sue_ce_supply sue_ce_fn
Proof
  simp[wf_ssa_def, ssa_form_def, def_dominates_uses_def,
       fn_inst_wf_def, wf_function_def, sue_ce_fn_def, mk_raw_function_def,
       mk_inst_def, fn_succs_closed_def, fn_inst_ids_distinct_def,
       listTheory.MEM, GSYM AND_IMP_INTRO, DISJ_IMP_THM, FORALL_AND_THM] >>
  EVAL_TAC >> simp[]
QED

Theorem sue_ce_expansion:
  sue_expand_function_supply sue_ce_supply sue_ce_fn =
    (sue_ce_out, sue_ce_supply with <| irs_next_inst := 5;
      irs_next_var := 2; irs_used_inst_ids := [4;3;0;1;2];
      irs_used_vars := ["formal_var_1";"formal_var_0";"x"] |>)
Proof
  EVAL_TAC
QED

Theorem sue_ce_no_edges:
  !a b. ~fn_cfg_edge sue_ce_out a b
Proof
  rewrite_tac[fn_cfg_edge_def] >> rpt strip_tac >>
  gvs[sue_ce_out_def, mk_raw_function_def, listTheory.MEM] >>
  pop_assum mp_tac >> EVAL_TAC
QED

Theorem sue_ce_unreachable:
  ~fn_reachable sue_ce_out "u"
Proof
  simp[fn_reachable_def, Once relationTheory.RTC_CASES1,
       sue_ce_no_edges] >> EVAL_TAC
QED

Theorem sue_ce_not_ssa:
  ~wf_ssa sue_ce_out
Proof
  `!bb use v. bb.bb_label = "u" ==>
     ~def_available_at sue_ce_out bb use v` by
    metis_tac[def_available_at_def, fn_dominates_def, sue_ce_unreachable] >>
  strip_tac >> fs[wf_ssa_def, def_dominates_uses_def] >>
  qpat_x_assum `!bb inst. _` (qspecl_then
    [`EL 1 sue_ce_out.fn_blocks`,
     `mk_inst 1 ADD [Var "formal_var_1"; Var "formal_var_0"] ["x"]`] mp_tac) >>
  impl_tac >- EVAL_TAC >>
  simp[mk_inst_def] >>
  qexists_tac `"formal_var_1"` >> simp[] >>
  `((EL 1 sue_ce_out.fn_blocks).bb_label = "u")` by EVAL_TAC >>
  metis_tac[]
QED

Theorem sue_expand_function_supply_wf_ssa_counterexample:
  ?s'. wf_ssa sue_ce_fn /\ fn_inst_wf sue_ce_fn /\
    wf_function sue_ce_fn /\ ir_supply_covers_fn sue_ce_supply sue_ce_fn /\
    sue_expand_function_supply sue_ce_supply sue_ce_fn = (sue_ce_out,s') /\
    ~wf_ssa sue_ce_out
Proof
  metis_tac[sue_ce_input, sue_ce_expansion, sue_ce_not_ssa]
QED

(* The counterexample above shows why reachability is needed: inserted
   copies in unreachable blocks cannot have dominating definitions. *)
(* The inserted copies define fresh variables, each right before the one
   instruction that reads it, and read what that instruction read there. *)
Theorem sue_expand_function_supply_wf_ssa:
  wf_ssa fn /\ fn_inst_wf fn /\ wf_function fn /\ all_reachable fn /\
  ir_supply_covers_fn s fn /\
  sue_expand_function_supply s fn = (fn',s') ==>
  wf_ssa fn'
Proof
  strip_tac >> drule_all sue_supply_replay >> strip_tac >>
  gvs[wf_ssa_def] >> conj_tac
  >- metis_tac[sue_expand_function_supply_ssa_form] >>
  metis_tac[sue_expand_function_supply_def_dominates_uses]
QED

Theorem sue_expand_inst_supply_operand_copies:
  sue_expand_inst_supply dfg s i = (out,s') ==>
  ?j. MEM j out /\ j.inst_opcode = i.inst_opcode /\
    j.inst_outputs = i.inst_outputs /\
    (sue_should_skip i.inst_opcode ==> j = i) /\
    LIST_REL (\op nop. nop = op \/
      ?a v. MEM a out /\ a.inst_opcode = ASSIGN /\
        a.inst_operands = [op] /\ a.inst_outputs = [v] /\ nop = Var v)
      i.inst_operands j.inst_operands
Proof
  strip_tac >> Cases_on `sue_should_skip i.inst_opcode`
  >- (gvs[sue_expand_inst_supply_def] >>
      `!xs : operand list. LIST_REL (\op nop. nop = op) xs xs` by
        (Induct >> simp[]) >>
      irule listTheory.LIST_REL_mono >>
      qexists_tac `\op nop. nop = op` >> simp[]) >>
  Cases_on `sue_expand_ops_supply dfg i s i.inst_operands 0` >>
  PairCases_on `r` >> gvs[sue_expand_inst_supply_def] >>
  qexists_tac `i with inst_operands := r0` >> simp[] >>
  drule sue_expand_ops_supply_provenance >> strip_tac >>
  irule listTheory.LIST_REL_mono >> goal_assum (drule_at Any) >>
  simp[] >> metis_tac[]
QED

Theorem sue_expand_insts_supply_skip_member:
  !insts s out s' i.
  sue_expand_insts_supply dfg s insts = (out,s') /\
  MEM i insts /\ sue_should_skip i.inst_opcode ==> MEM i out
Proof
  Induct >> rpt strip_tac
  >- gvs[] >>
  Cases_on `sue_expand_inst_supply dfg s h` >>
  Cases_on `sue_expand_insts_supply dfg r insts` >>
  gvs[sue_expand_insts_supply_def]
  >- gvs[sue_expand_inst_supply_def] >>
  disj2_tac >> first_x_assum irule >> metis_tac[]
QED

Theorem sue_expand_block_supply_skip_member:
  sue_expand_block_supply dfg s bb = (bb',s') /\
  MEM i bb.bb_instructions /\ sue_should_skip i.inst_opcode ==>
  MEM i bb'.bb_instructions
Proof
  Cases_on `sue_expand_insts_supply dfg s bb.bb_instructions` >>
  simp[sue_expand_block_supply_def] >> strip_tac >> gvs[] >>
  irule sue_expand_insts_supply_skip_member >> metis_tac[]
QED

Theorem sue_expand_insts_supply_operand_copies:
  !insts s out s' i.
  sue_expand_insts_supply dfg s insts = (out,s') /\ MEM i insts ==>
  ?j. MEM j out /\ j.inst_opcode = i.inst_opcode /\
    j.inst_outputs = i.inst_outputs /\
    (sue_should_skip i.inst_opcode ==> j = i) /\
    LIST_REL (\op nop. nop = op \/
      ?a v. MEM a out /\ a.inst_opcode = ASSIGN /\
        a.inst_operands = [op] /\ a.inst_outputs = [v] /\ nop = Var v)
      i.inst_operands j.inst_operands
Proof
  Induct >> rpt strip_tac
  >- gvs[] >>
  Cases_on `sue_expand_inst_supply dfg s h` >>
  Cases_on `sue_expand_insts_supply dfg r insts` >>
  gvs[sue_expand_insts_supply_def]
  >- (drule sue_expand_inst_supply_operand_copies >> strip_tac >>
      qexists_tac `j` >> simp[] >>
      irule listTheory.LIST_REL_mono >> goal_assum (drule_at Any) >>
      simp[] >> metis_tac[]) >>
  first_x_assum drule_all >> strip_tac >>
  qexists_tac `j` >> simp[] >>
  irule listTheory.LIST_REL_mono >> goal_assum (drule_at Any) >>
  simp[] >> metis_tac[]
QED

Theorem sue_expand_block_supply_operand_copies:
  sue_expand_block_supply dfg s bb = (bb',s') /\
  MEM i bb.bb_instructions ==>
  ?j. MEM j bb'.bb_instructions /\ j.inst_opcode = i.inst_opcode /\
    j.inst_outputs = i.inst_outputs /\
    (sue_should_skip i.inst_opcode ==> j = i) /\
    LIST_REL (\op nop. nop = op \/
      ?a v. MEM a bb'.bb_instructions /\ a.inst_opcode = ASSIGN /\
        a.inst_operands = [op] /\ a.inst_outputs = [v] /\ nop = Var v)
      i.inst_operands j.inst_operands
Proof
  Cases_on `sue_expand_insts_supply dfg s bb.bb_instructions` >>
  simp[sue_expand_block_supply_def] >> strip_tac >> gvs[] >>
  drule_all sue_expand_insts_supply_operand_copies >> simp[]
QED

Theorem sue_expand_inst_supply_old_output:
  ir_supply_inst_ok s /\ sue_expand_inst_supply dfg s i = (out,s') /\
  MEM j out /\ MEM v j.inst_outputs /\ MEM v s.irs_used_vars ==>
  ?ops. j = i with inst_operands := ops /\
    (sue_should_skip i.inst_opcode ==> j = i)
Proof
  strip_tac >> Cases_on `sue_should_skip i.inst_opcode`
  >- (gvs[sue_expand_inst_supply_def] >>
      qexists_tac `i.inst_operands` >> simp[]) >>
  drule_all sue_expand_inst_supply_segment >> strip_tac >>
  gvs[listTheory.MEM_APPEND, listTheory.MEM] >>
  gvs[listTheory.EVERY_MEM, listTheory.MEM_FLAT, listTheory.MEM_MAP] >>
  metis_tac[]
QED

Theorem sue_distinct_outputs_unique[local]:
  !xs i j v. ALL_DISTINCT (FLAT (MAP (\a. a.inst_outputs) xs)) /\
    MEM i xs /\ MEM j xs /\ MEM v i.inst_outputs /\ MEM v j.inst_outputs ==>
    i = j
Proof
  Induct >> simp[] >> rpt strip_tac >>
  gvs[listTheory.ALL_DISTINCT_APPEND, listTheory.MEM_FLAT,
      listTheory.MEM_MAP] >> metis_tac[]
QED

Theorem sue_expand_inst_supply_fresh_unique:
  ir_supply_inst_ok s /\
  EVERY (\v. MEM v s.irs_used_vars) inst.inst_outputs /\
  sue_expand_inst_supply dfg s inst = (out,s') /\
  ~MEM v s.irs_used_vars /\ MEM i out /\ MEM j out /\
  MEM v i.inst_outputs /\ MEM v j.inst_outputs ==> i = j
Proof
  strip_tac >> drule_all sue_expand_inst_supply_segment >> strip_tac >>
  gvs[listTheory.EVERY_MEM] >>
  `MEM i assigns /\ MEM j assigns` by (gvs[] >> metis_tac[]) >>
  irule sue_distinct_outputs_unique >> metis_tac[]
QED

Theorem sue_expand_insts_supply_old_output:
  !insts s out s' j v.
  ir_supply_inst_ok s /\
  sue_expand_insts_supply dfg s insts = (out,s') /\
  MEM j out /\ MEM v j.inst_outputs /\ MEM v s.irs_used_vars ==>
  ?i. MEM i insts /\ MEM v i.inst_outputs
Proof
  Induct >> rpt strip_tac
  >- gvs[sue_expand_insts_supply_def] >>
  Cases_on `sue_expand_inst_supply dfg s h` >>
  Cases_on `sue_expand_insts_supply dfg r insts` >>
  gvs[sue_expand_insts_supply_def]
  >- (drule_all sue_expand_inst_supply_old_output >> strip_tac >>
      qexists_tac `h` >> gvs[]) >>
  `sue_supply_extends s r` by metis_tac[sue_expand_inst_supply_extends] >>
  `ir_supply_inst_ok r /\ MEM v r.irs_used_vars` by
    metis_tac[sue_supply_extends_def, sue_supply_extends_members] >>
  first_x_assum drule_all >> strip_tac >>
  qexists_tac `i` >> simp[]
QED

Theorem sue_expand_insts_supply_fresh_unique:
  !insts s out s' i j v.
  ir_supply_inst_ok s /\
  EVERY (\v. MEM v s.irs_used_vars)
    (FLAT (MAP (\a. a.inst_outputs) insts)) /\
  sue_expand_insts_supply dfg s insts = (out,s') /\
  ~MEM v s.irs_used_vars /\ MEM i out /\ MEM j out /\
  MEM v i.inst_outputs /\ MEM v j.inst_outputs ==> i = j
Proof
  Induct >> rpt strip_tac
  >- gvs[sue_expand_insts_supply_def] >>
  Cases_on `sue_expand_inst_supply dfg s h` >>
  Cases_on `sue_expand_insts_supply dfg r insts` >>
  gvs[sue_expand_insts_supply_def, listTheory.EVERY_APPEND] >>
  `sue_supply_extends s r` by metis_tac[sue_expand_inst_supply_extends] >>
  `ir_supply_inst_ok r` by gvs[sue_supply_extends_def] >>
  `!w. MEM w s.irs_used_vars ==> MEM w r.irs_used_vars` by
    metis_tac[sue_supply_extends_members] >>
  `EVERY (\w. MEM w r.irs_used_vars)
    (FLAT (MAP (\a. a.inst_outputs) insts))` by
    (gvs[listTheory.EVERY_MEM] >> metis_tac[]) >>
  `EVERY (\w. MEM w r.irs_used_vars)
    (FLAT (MAP (\a. a.inst_outputs) q))` by
    metis_tac[sue_expand_inst_supply_outputs_covered] >>
  `!a w. MEM a insts /\ MEM w a.inst_outputs ==> MEM w s.irs_used_vars` by
    (gvs[listTheory.EVERY_MEM, listTheory.MEM_FLAT, listTheory.MEM_MAP] >>
     metis_tac[]) >>
  `!a. MEM a q' /\ MEM v a.inst_outputs /\ MEM v r.irs_used_vars ==>
    MEM v s.irs_used_vars` by
    (rpt strip_tac >> drule_all sue_expand_insts_supply_old_output >>
     strip_tac >> metis_tac[]) 
  >~ [`i = j`, `sue_expand_inst_supply dfg s h = (head_out,mid)`,
       `MEM i head_out`, `MEM j head_out`, `MEM v i.inst_outputs`]
  >- (irule sue_expand_inst_supply_fresh_unique >>
      qexistsl_tac [`dfg`,`h`,`head_out`,`s`,`mid`,`v`] >> simp[])
  >~ [`i = j`, `sue_expand_insts_supply dfg mid insts = (tail_out,last_supply)`,
       `MEM i tail_out`, `MEM j tail_out`, `MEM v i.inst_outputs`]
  >- (Cases_on `MEM v mid.irs_used_vars`
      >- (first_x_assum (qspec_then `i` mp_tac) >> simp[]) >>
      first_x_assum irule >> metis_tac[]) >>
  gvs[listTheory.EVERY_MEM, listTheory.MEM_FLAT, listTheory.MEM_MAP] >>
  metis_tac[]
QED

Theorem sue_expand_function_supply_fresh_unique:
  ir_supply_inst_ok s /\ ir_supply_covers_fn s fn /\
  sue_expand_function_supply s fn = (fn',s') /\
  ~MEM v s.irs_used_vars /\ MEM i (fn_insts fn') /\ MEM j (fn_insts fn') /\
  MEM v i.inst_outputs /\ MEM v j.inst_outputs ==> i = j
Proof
  strip_tac >>
  `!bbs. fn_insts_blocks bbs = FLAT (MAP (\bb. bb.bb_instructions) bbs)` by
    (Induct >> simp[fn_insts_blocks_def]) >>
  `EVERY (\v. MEM v s.irs_used_vars)
     (FLAT (MAP (\i. i.inst_outputs) (fn_insts fn)))` by
    (gvs[ir_supply_covers_fn_def, list_subset_def, fn_ir_vars_def,
         block_ir_vars_def, inst_ir_vars_def, fn_insts_def,
         listTheory.EVERY_MEM, listTheory.MEM_FLAT,
         listTheory.MEM_MAP] >>
     metis_tac[inst_ir_vars_def, listTheory.MEM_FLAT,
               listTheory.MEM_MAP, listTheory.MEM_APPEND]) >>
  Cases_on `sue_expand_blocks_supply (dfg_build_function fn) s fn.fn_blocks` >>
  gvs[sue_expand_function_supply_def, fn_insts_def] >>
  drule sue_expand_blocks_supply_flat >> strip_tac >>
  irule sue_expand_insts_supply_fresh_unique >>
  goal_assum (drule_at Any) >> metis_tac[]
QED

Theorem sue_expand_insts_supply_old_skip:
  !insts s out s' j v.
  ir_supply_inst_ok s /\
  sue_expand_insts_supply dfg s insts = (out,s') /\
  MEM j out /\ MEM v j.inst_outputs /\ MEM v s.irs_used_vars /\
  sue_should_skip j.inst_opcode ==> MEM j insts
Proof
  Induct >> rpt strip_tac
  >- gvs[sue_expand_insts_supply_def] >>
  Cases_on `sue_expand_inst_supply dfg s h` >>
  Cases_on `sue_expand_insts_supply dfg r insts` >>
  gvs[sue_expand_insts_supply_def]
  >- (drule_all sue_expand_inst_supply_old_output >> strip_tac >>
      gvs[] >> metis_tac[]) >>
  `sue_supply_extends s r` by metis_tac[sue_expand_inst_supply_extends] >>
  `ir_supply_inst_ok r /\ MEM v r.irs_used_vars` by
    metis_tac[sue_supply_extends_def, sue_supply_extends_members] >>
  disj2_tac >> first_x_assum irule >> metis_tac[]
QED

Theorem sue_expand_function_supply_skip_member:
  sue_expand_function_supply s fn = (fn',s') /\
  MEM i (fn_insts fn) /\ sue_should_skip i.inst_opcode ==>
  MEM i (fn_insts fn')
Proof
  strip_tac >>
  `!bbs. fn_insts_blocks bbs = FLAT (MAP (\bb. bb.bb_instructions) bbs)` by
    (Induct >> simp[fn_insts_blocks_def]) >>
  Cases_on `sue_expand_blocks_supply (dfg_build_function fn) s fn.fn_blocks` >>
  gvs[sue_expand_function_supply_def, fn_insts_def] >>
  drule sue_expand_blocks_supply_flat >> strip_tac >>
  irule sue_expand_insts_supply_skip_member >> metis_tac[]
QED

Theorem sue_expand_function_supply_old_skip:
  ir_supply_inst_ok s /\ sue_expand_function_supply s fn = (fn',s') /\
  MEM j (fn_insts fn') /\ MEM v j.inst_outputs /\ MEM v s.irs_used_vars /\
  sue_should_skip j.inst_opcode ==> MEM j (fn_insts fn)
Proof
  strip_tac >>
  `!bbs. fn_insts_blocks bbs = FLAT (MAP (\bb. bb.bb_instructions) bbs)` by
    (Induct >> simp[fn_insts_blocks_def]) >>
  Cases_on `sue_expand_blocks_supply (dfg_build_function fn) s fn.fn_blocks` >>
  gvs[sue_expand_function_supply_def, fn_insts_def] >>
  drule sue_expand_blocks_supply_flat >> strip_tac >>
  irule sue_expand_insts_supply_old_skip >> metis_tac[]
QED

Theorem sue_supply_operand_covered:
  ir_supply_covers_fn s fn /\ MEM i (fn_insts fn) /\
  MEM (Var v) i.inst_operands ==> MEM v s.irs_used_vars
Proof
  strip_tac >>
  `!bbs. fn_insts_blocks bbs = FLAT (MAP (\bb. bb.bb_instructions) bbs)` by
    (Induct >> simp[fn_insts_blocks_def]) >>
  gvs[fn_insts_def, listTheory.MEM_FLAT, listTheory.MEM_MAP] >>
  drule_all sue_original_operand_covered >>
  gvs[ir_supply_covers_fn_def, list_subset_def, listTheory.EVERY_MEM]
QED

Theorem sue_expand_block_supply_old_skip:
  ir_supply_inst_ok s /\ sue_expand_block_supply dfg s bb = (bb',s') /\
  MEM j bb'.bb_instructions /\ MEM v j.inst_outputs /\ MEM v s.irs_used_vars /\
  sue_should_skip j.inst_opcode ==> MEM j bb.bb_instructions
Proof
  Cases_on `sue_expand_insts_supply dfg s bb.bb_instructions` >>
  simp[sue_expand_block_supply_def] >> strip_tac >> gvs[] >>
  irule sue_expand_insts_supply_old_skip >> metis_tac[]
QED

Theorem sue_expand_blocks_supply_member_extends:
  !bbs s bbs' s' bb'.
  ir_supply_inst_ok s /\
  sue_expand_blocks_supply dfg s bbs = (bbs',s') /\ MEM bb' bbs' ==>
  ?bb si sj. MEM bb bbs /\ sue_expand_block_supply dfg si bb = (bb',sj) /\
    sue_supply_extends s si
Proof
  Induct >> rpt strip_tac
  >- gvs[sue_expand_blocks_supply_def] >>
  Cases_on `sue_expand_block_supply dfg s h` >>
  Cases_on `sue_expand_blocks_supply dfg r bbs` >>
  gvs[sue_expand_blocks_supply_def]
  >- (qexistsl_tac [`h`,`s`,`r`] >> simp[sue_supply_extends_refl]) >>
  `sue_supply_extends s r` by metis_tac[sue_expand_block_supply_extends] >>
  `ir_supply_inst_ok r` by gvs[sue_supply_extends_def] >>
  first_x_assum drule_all >> strip_tac >>
  qexistsl_tac [`bb`,`si`,`sj`] >> simp[] >>
  irule sue_supply_extends_trans >> metis_tac[]
QED

Theorem sue_expand_inst_supply_operand_copies_back:
  ir_supply_inst_ok s /\
  sue_expand_inst_supply dfg s i = (out,s') /\
  MEM j out /\ j.inst_opcode <> ASSIGN ==>
  j.inst_opcode = i.inst_opcode /\ j.inst_outputs = i.inst_outputs /\
  (sue_should_skip i.inst_opcode ==> j = i) /\
  LIST_REL (\op nop. nop = op \/
    ?a v. MEM a out /\ a.inst_opcode = ASSIGN /\
      a.inst_operands = [op] /\ a.inst_outputs = [v] /\ nop = Var v)
    i.inst_operands j.inst_operands
Proof
  strip_tac >>
  drule_all sue_expand_inst_supply_segment >> strip_tac >>
  `j = i with inst_operands := new_ops` by
    (gvs[listTheory.MEM_APPEND, listTheory.MEM, listTheory.EVERY_MEM] >> metis_tac[]) >>
  drule sue_expand_inst_supply_operand_copies >> strip_tac >>
  `j' = j` by
    (gvs[listTheory.MEM_APPEND, listTheory.MEM, listTheory.EVERY_MEM] >> metis_tac[]) >>
  gvs[]
QED

Theorem sue_expand_insts_supply_operand_copies_back:
  !insts s out s' j.
  ir_supply_inst_ok s /\ sue_expand_insts_supply dfg s insts = (out,s') /\
  MEM j out /\ j.inst_opcode <> ASSIGN ==>
  ?i. MEM i insts /\ j.inst_opcode = i.inst_opcode /\
    j.inst_outputs = i.inst_outputs /\
    (sue_should_skip i.inst_opcode ==> j = i) /\
    LIST_REL (\op nop. nop = op \/
      ?a v. MEM a out /\ a.inst_opcode = ASSIGN /\
        a.inst_operands = [op] /\ a.inst_outputs = [v] /\ nop = Var v)
      i.inst_operands j.inst_operands
Proof
  Induct >> rpt strip_tac >- gvs[sue_expand_insts_supply_def] >>
  Cases_on `sue_expand_inst_supply dfg s h` >>
  Cases_on `sue_expand_insts_supply dfg r insts` >>
  gvs[sue_expand_insts_supply_def]
  >- (drule_all sue_expand_inst_supply_operand_copies_back >> strip_tac >>
      qexists_tac `h` >> simp[] >>
      irule listTheory.LIST_REL_mono >> goal_assum (drule_at Any) >>
      simp[] >> metis_tac[]) >>
  `sue_supply_extends s r` by metis_tac[sue_expand_inst_supply_extends] >>
  `ir_supply_inst_ok r` by gvs[sue_supply_extends_def] >>
  first_x_assum drule_all >> strip_tac >>
  qexists_tac `i` >> simp[] >>
  irule listTheory.LIST_REL_mono >> goal_assum (drule_at Any) >>
  simp[] >> metis_tac[]
QED

Theorem sue_expand_block_supply_operand_copies_back:
  ir_supply_inst_ok s /\ sue_expand_block_supply dfg s bb = (bb',s') /\
  MEM j bb'.bb_instructions /\ j.inst_opcode <> ASSIGN ==>
  ?i. MEM i bb.bb_instructions /\ j.inst_opcode = i.inst_opcode /\
    j.inst_outputs = i.inst_outputs /\
    (sue_should_skip i.inst_opcode ==> j = i) /\
    LIST_REL (\op nop. nop = op \/
      ?a v. MEM a bb'.bb_instructions /\ a.inst_opcode = ASSIGN /\
        a.inst_operands = [op] /\ a.inst_outputs = [v] /\ nop = Var v)
      i.inst_operands j.inst_operands
Proof
  Cases_on `sue_expand_insts_supply dfg s bb.bb_instructions` >>
  simp[sue_expand_block_supply_def] >> strip_tac >> gvs[] >>
  drule_all sue_expand_insts_supply_operand_copies_back >> simp[]
QED

Theorem sue_supply_output_covered:
  ir_supply_covers_fn s fn /\ MEM i (fn_insts fn) /\
  MEM v i.inst_outputs ==> MEM v s.irs_used_vars
Proof
  strip_tac >>
  `!bbs. fn_insts_blocks bbs = FLAT (MAP (\bb. bb.bb_instructions) bbs)` by
    (Induct >> simp[fn_insts_blocks_def]) >>
  gvs[ir_supply_covers_fn_def, list_subset_def, fn_ir_vars_def,
      block_ir_vars_def, inst_ir_vars_def, fn_insts_def,
      listTheory.EVERY_MEM, listTheory.MEM_FLAT, listTheory.MEM_MAP] >>
  metis_tac[inst_ir_vars_def, listTheory.MEM_FLAT,
            listTheory.MEM_MAP, listTheory.MEM_APPEND]
QED

(* Syntactic inverse of the fresh operand-copy prefix. *)
Theorem sue_expand_ops_supply_copy_shape:
  ir_supply_inst_ok s /\
  sue_expand_ops_supply dfg inst s ops k = (assigns,new_ops,s') ==>
  EVERY (\a. a.inst_opcode = ASSIGN /\ LENGTH a.inst_outputs = 1 /\
              LENGTH a.inst_operands = 1) assigns
Proof
  strip_tac >> drule_all sue_expand_ops_supply_prefix >> strip_tac >>
  drule sue_expand_ops_supply_copy_sources >> strip_tac >>
  fs[listTheory.EVERY_MEM] >> rpt strip_tac >>
  res_tac >> gvs[]
QED

Theorem sue_expand_ops_supply_resolve_protected:
  ir_supply_inst_ok s /\
  sue_expand_ops_supply dfg inst s ops k = (assigns,new_ops,s') /\
  (!v. op = Var v ==> MEM v s.irs_used_vars) ==>
  resolve_block_assigns (REVERSE assigns) op = op
Proof
  strip_tac >> drule_all sue_expand_ops_supply_prefix >> strip_tac >>
  irule resolve_block_assigns_no_write >>
  Cases_on `op` >> simp[listTheory.EVERY_MEM] >>
  rpt strip_tac >>
  fs[listTheory.EVERY_MEM, listTheory.MEM_FLAT, listTheory.MEM_MAP] >>
  metis_tac[listTheory.MEM_REVERSE]
QED

Theorem sue_expand_ops_supply_resolve:
  !ops dfg inst s k assigns new_ops s'.
  ir_supply_inst_ok s /\
  (!v. MEM (Var v) ops ==> MEM v s.irs_used_vars) /\
  sue_expand_ops_supply dfg inst s ops k = (assigns,new_ops,s') ==>
  LIST_REL (\op op'. resolve_block_assigns (REVERSE assigns) op' = op)
           ops new_ops
Proof
  Induct_on `ops` >- simp[sue_expand_ops_supply_def] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `sue_expand_ops_supply dfg inst s ops (k + 1)` >>
  PairCases_on `r` >>
  rename1 `sue_expand_ops_supply dfg inst s ops (k + 1) =
            (more_assigns,more_ops,s1)` >>
  `sue_supply_extends s s1` by metis_tac[sue_expand_ops_supply_extends] >>
  `ir_supply_inst_ok s1` by gvs[sue_supply_extends_def] >>
  `LIST_REL (\op op'. resolve_block_assigns (REVERSE more_assigns) op' = op)
            ops more_ops` by (first_x_assum irule >> metis_tac[listTheory.MEM]) >>
  Cases_on `~sue_needs_assign dfg inst k`
  >- (gvs[Once sue_expand_ops_supply_def] >>
      drule_at (Pat `sue_expand_ops_supply _ _ _ _ _ = _`)
        sue_expand_ops_supply_resolve_protected >>
      simp[] >> disch_then irule >> metis_tac[listTheory.MEM]) >>
  Cases_on `h`
  >- suspend "allocated"
  >- (Cases_on `LENGTH (dfg_get_uses dfg s'') = 1 /\
                 sue_count_remaining (Var s'') ops = 0`
      >- (gvs[Once sue_expand_ops_supply_def] >>
          drule_at (Pat `sue_expand_ops_supply _ _ _ _ _ = _`)
            sue_expand_ops_supply_resolve_protected >>
          simp[] >> disch_then irule >> metis_tac[listTheory.MEM]) >>
      suspend "allocated") >>
  gvs[Once sue_expand_ops_supply_def, resolve_block_assigns_nonvar]
QED

Resume sue_expand_ops_supply_resolve[allocated]:
  markerLib.RESUME_TAC >> (qmatch_goalsub_abbrev_tac `LIST_REL _ (source::ops) new_ops` >>
  Cases_on `sue_alloc_assign_supply s1 source` >> PairCases_on `r` >>
  drule_all sue_alloc_assign_supply_contract >> strip_tac >>
  drule sue_alloc_assign_supply_shape >> strip_tac >>
  drule_all sue_expand_ops_supply_copy_shape >> strip_tac >>
  drule_all sue_expand_ops_supply_prefix >> strip_tac >>
  gvs[Abbr `source`, Once sue_expand_ops_supply_def] >>
  simp[resolve_block_assigns_copy_append, listTheory.EVERY_MEM, listTheory.MEM_REVERSE] >>
  conj_tac
  >- (`resolve_block_assigns (REVERSE more_assigns) (Var v) = Var v` by
        (irule resolve_block_assigns_no_write >>
         gvs[listTheory.EVERY_MEM, listTheory.MEM_FLAT, listTheory.MEM_MAP] >>
         metis_tac[listTheory.MEM_REVERSE]) >>
      simp[contextCodegenRelTheory.resolve_block_assigns_def]) >>
  fs[listTheory.LIST_REL_EL_EQN] >> rpt strip_tac >> simp[] >>
  `MEM (EL n ops) ops` by (simp[listTheory.MEM_EL] >> metis_tac[]) >>
  Cases_on `EL n ops` >> simp[contextCodegenRelTheory.resolve_block_assigns_def] >>
  `~(s' = v)` by metis_tac[] >> simp[])
QED

Finalise sue_expand_ops_supply_resolve

Theorem sue_expand_inst_supply_resolve:
  ir_supply_inst_ok s /\
  (!v. MEM (Var v) inst.inst_operands ==> MEM v s.irs_used_vars) /\
  sue_expand_inst_supply dfg s inst = (out,s') ==>
  EVERY (\a. a.inst_opcode = ASSIGN /\ LENGTH a.inst_outputs = 1 /\
              LENGTH a.inst_operands = 1) (BUTLAST out) /\
  LIST_REL (\op op'. resolve_block_assigns (REVERSE (BUTLAST out)) op' = op)
           inst.inst_operands (LAST out).inst_operands /\
  (!op. (!v. op = Var v ==> MEM v s.irs_used_vars) ==>
        resolve_block_assigns (REVERSE (BUTLAST out)) op = op)
Proof
  strip_tac >> Cases_on `sue_should_skip inst.inst_opcode`
  >- (gvs[sue_expand_inst_supply_def,
          contextCodegenRelTheory.resolve_block_assigns_def,
          listTheory.LIST_REL_EL_EQN]) >>
  Cases_on `sue_expand_ops_supply dfg inst s inst.inst_operands 0` >>
  PairCases_on `r` >> gvs[sue_expand_inst_supply_def] >>
  drule_all sue_expand_ops_supply_resolve >> strip_tac >>
  drule_all sue_expand_ops_supply_copy_shape >> strip_tac >>
  simp[rich_listTheory.FRONT_APPEND_NOT_NIL] >> rpt strip_tac >>
  drule_at (Pat `sue_expand_ops_supply _ _ _ _ _ = _`)
    sue_expand_ops_supply_resolve_protected >>
  simp[]
QED

Theorem sue_expand_inst_supply_step_back:
  sue_expand_inst_supply dfg s inst = (out,s') ==>
  step_back_assign (LAST out) op = step_back_assign inst op
Proof
  strip_tac >> Cases_on `sue_should_skip inst.inst_opcode`
  >- gvs[sue_expand_inst_supply_def] >>
  drule sue_expand_inst_supply_last >> strip_tac >>
  `inst.inst_opcode <> ASSIGN` by gvs[sue_should_skip_def] >>
  Cases_on `op` >> simp[contextCodegenRelTheory.step_back_assign_def]
QED

Theorem sue_segments_supply_append:
  !xs dfg s ys segs s'.
  sue_segments_supply dfg s (xs ++ ys) = (segs,s') ==>
  ?sx sy sm. sue_segments_supply dfg s xs = (sx,sm) /\
             sue_segments_supply dfg sm ys = (sy,s') /\ segs = sx ++ sy
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- (gvs[sue_segments_supply_def] >> metis_tac[]) >>
  Cases_on `sue_expand_inst_supply dfg s h` >>
  Cases_on `sue_segments_supply dfg r (xs ++ ys)` >>
  gvs[sue_segments_supply_def] >>
  first_x_assum drule >> strip_tac >>
  qexistsl [`q::sx`, `sy`, `sm`] >> simp[sue_segments_supply_def]
QED

Theorem sue_segments_supply_same_after_assigns:
  !insts dfg s segs s' P p q.
  sue_segments_supply dfg s insts = (segs,s') /\ ir_supply_inst_ok s /\
  P SUBSET set s.irs_used_vars /\
  (!inst v. MEM inst insts /\ MEM (Var v) inst.inst_operands ==> v IN P) /\
  (!v. p = Var v ==> v IN P) /\ (!v. q = Var v ==> v IN P) /\
  same_after_assigns (REVERSE insts) p q ==>
  same_after_assigns (REVERSE (FLAT segs)) p q
Proof
  Induct using listTheory.SNOC_INDUCT
  >- simp[sue_segments_supply_def,
          contextCodegenRelTheory.same_after_assigns_def] >>
  rpt gen_tac >> strip_tac >> Cases_on `p = q` >- simp[] >>
  fs[listTheory.SNOC_APPEND] >>
  drule sue_segments_supply_append >> strip_tac >>
  gvs[sue_segments_supply_def, AllCaseEqs()] >>
  rename1 `sue_expand_inst_supply dfg sm x = (out,s')` >>
  `ir_supply_inst_ok sm /\ P SUBSET set sm.irs_used_vars` by
    (drule sue_segments_supply_flat >> strip_tac >>
     drule_all sue_expand_insts_supply_extends >> strip_tac >>
     gvs[sue_supply_extends_def, pred_setTheory.SUBSET_DEF] >> metis_tac[]) >>
  `!v. MEM (Var v) x.inst_operands ==> v IN P` by metis_tac[listTheory.MEM_APPEND, listTheory.MEM] >>
  `!v. MEM (Var v) x.inst_operands ==> MEM v sm.irs_used_vars` by
    metis_tac[pred_setTheory.SUBSET_DEF, listTheory.MEM] >>
  drule_all sue_expand_inst_supply_resolve >> strip_tac >>
  `!op. step_back_assign (LAST out) op = step_back_assign x op` by
    metis_tac[sue_expand_inst_supply_step_back] >>
  drule_all sue_expand_inst_supply_segment >> strip_tac >>
  gvs[rich_listTheory.FRONT_APPEND_NOT_NIL] >>
  gvs[listTheory.REVERSE_APPEND, listTheory.APPEND_ASSOC,
      contextCodegenRelTheory.same_after_assigns_def, AllCaseEqs()] >>
  Cases_on `step_back_assign x p` >- gvs[] >>
  Cases_on `step_back_assign x q` >- gvs[] >> gvs[] >>
  rename1 `step_back_assign x p = SOME p1` >>
  rename1 `step_back_assign x q = SOME q1` >>
  `(!v. p1 = Var v ==> v IN P) /\ (!v. q1 = Var v ==> v IN P)` by
    (qpat_x_assum `!dfg s segs s' P p q. _` kall_tac >>
     metis_tac[step_back_assign_preserves_vars]) >>
  irule same_after_assigns_copy_prefix >>
  simp[listTheory.EVERY_MEM, listTheory.MEM_REVERSE] >>
  `resolve_block_assigns (REVERSE assigns) p1 = p1 /\
   resolve_block_assigns (REVERSE assigns) q1 = q1` by
    (conj_tac >> first_x_assum irule >> metis_tac[pred_setTheory.SUBSET_DEF]) >>
  simp[] >> first_x_assum irule >>
  goal_assum (drule_at Any) >> qexists_tac `P` >> simp[] >> metis_tac[]
QED

Theorem sue_segments_supply_take:
  sue_segments_supply dfg s insts = (segs,s') /\ i <= LENGTH insts ==>
  ?sm. sue_segments_supply dfg s (TAKE i insts) = (TAKE i segs,sm)
Proof
  strip_tac >>
  `sue_segments_supply dfg s (TAKE i insts ++ DROP i insts) = (segs,s')` by simp[] >>
  drule sue_segments_supply_append >> strip_tac >>
  qpat_assum `sue_segments_supply _ _ (TAKE _ _) = _`
    (mp_then Any assume_tac sue_segments_supply_length) >>
  qexists_tac `sm` >> gvs[] >>
  simp[listTheory.TAKE_APPEND1]
QED

Theorem sue_segments_supply_same_after_assigns_take:
  sue_segments_supply dfg s insts = (segs,s') /\ ir_supply_inst_ok s /\
  i <= LENGTH insts /\ P SUBSET set s.irs_used_vars /\
  (!inst v. MEM inst insts /\ MEM (Var v) inst.inst_operands ==> v IN P) /\
  (!v. p = Var v ==> v IN P) /\ (!v. q = Var v ==> v IN P) /\
  same_after_assigns (REVERSE (TAKE i insts)) p q ==>
  same_after_assigns
    (REVERSE (TAKE (sue_segment_offset segs i) (FLAT segs))) p q
Proof
  strip_tac >> drule_all sue_segments_supply_take >> strip_tac >>
  `TAKE (sue_segment_offset segs i) (FLAT segs) = FLAT (TAKE i segs)` by
    (simp[sue_segment_offset_def] >>
     `FLAT segs = FLAT (TAKE i segs) ++ FLAT (DROP i segs)` by
       metis_tac[listTheory.TAKE_DROP, listTheory.FLAT_APPEND] >>
     pop_assum SUBST1_TAC >> simp[listTheory.TAKE_APPEND1]) >>
  simp[] >> irule sue_segments_supply_same_after_assigns >>
  goal_assum (drule_at Any) >> qexists_tac `P` >> simp[] >>
  metis_tac[listTheory.MEM_APPEND, listTheory.TAKE_DROP]
QED

Theorem sue_segments_supply_assigns:
  !insts dfg s segs s'.
  EVERY (\inst. inst.inst_opcode = ASSIGN) insts /\
  sue_segments_supply dfg s insts = (segs,s') ==>
  segs = MAP (\inst. [inst]) insts /\ s' = s
Proof
  Induct >> rpt gen_tac >> strip_tac
  >- gvs[sue_segments_supply_def] >>
  `sue_should_skip h.inst_opcode` by gvs[sue_should_skip_def] >>
  gvs[sue_segments_supply_def, sue_expand_inst_supply_skip, AllCaseEqs()] >>
  first_x_assum drule_all >> simp[]
QED

Theorem sue_segments_supply_endpoint_lookup:
  sue_segments_supply dfg s bb.bb_instructions = (segs,s') /\
  i < LENGTH bb.bb_instructions ==>
  get_instruction (bb with bb_instructions := FLAT segs)
    (sue_segment_offset segs i + LENGTH (EL i segs) - 1) =
  SOME (LAST (EL i segs))
Proof
  strip_tac >> drule sue_segments_supply_length >> strip_tac >>
  drule sue_segments_supply_nonempty >> strip_tac >>
  `i < LENGTH segs /\ EL i segs <> []` by
    (fs[listTheory.EVERY_EL] >> metis_tac[]) >>
  `LENGTH (EL i segs) > 0` by (Cases_on `EL i segs` >> gvs[]) >>
  `sue_segment_offset segs i + LENGTH (EL i segs) - 1 =
   sue_segment_offset segs i + (LENGTH (EL i segs) - 1)` by decide_tac >>
  `sue_segment_offset segs (SUC i) <= LENGTH (FLAT segs)` by
    (irule sue_segment_offset_bound >> simp[]) >>
  `sue_segment_offset segs (SUC i) =
   sue_segment_offset segs i + LENGTH (EL i segs)` by
    (irule sue_segment_offset_suc >> simp[]) >>
  `sue_segment_offset segs i + (LENGTH (EL i segs) - 1) < LENGTH (FLAT segs)` by decide_tac >>
  `EL (sue_segment_offset segs i + (LENGTH (EL i segs) - 1)) (FLAT segs) =
   EL (LENGTH (EL i segs) - 1) (EL i segs)` by
    (irule sue_segment_offset_el >> simp[]) >>
  simp[get_instruction_def, listTheory.LAST_EL, arithmeticTheory.PRE_SUB1] >>
  metis_tac[arithmeticTheory.ADD_COMM]
QED

Theorem sue_segment_endpoint_prefix:
  !segs i. i < LENGTH segs /\ EL i segs <> [] ==>
  TAKE (sue_segment_offset segs i + LENGTH (EL i segs) - 1) (FLAT segs) =
  FLAT (TAKE i segs) ++ BUTLAST (EL i segs)
Proof
  Induct >> simp[] >> gen_tac >> Cases_on `i` >> simp[]
  >- simp[rich_listTheory.FRONT_BY_TAKE, arithmeticTheory.PRE_SUB1, listTheory.TAKE_APPEND1] >>
  strip_tac >>
  `LENGTH (EL n segs) > 0` by (Cases_on `EL n segs` >> gvs[]) >>
  `LENGTH h <= LENGTH h + sue_segment_offset segs n + LENGTH (EL n segs) - 1` by decide_tac >>
  simp[rich_listTheory.TAKE_APPEND2] >>
  first_x_assum (qspec_then `n` mp_tac) >> simp[] >>
  disch_then SUBST1_TAC >> simp[listTheory.APPEND_ASSOC]
QED

Theorem sue_segment_endpoint_gap:
  !segs k j. k <= j /\ j < LENGTH segs /\ EL j segs <> [] ==>
  TAKE ((sue_segment_offset segs j + LENGTH (EL j segs) - 1) -
        sue_segment_offset segs k)
    (DROP (sue_segment_offset segs k) (FLAT segs)) =
  FLAT (TAKE (j-k) (DROP k segs)) ++ BUTLAST (EL j segs)
Proof
  Induct >> simp[] >> rpt gen_tac >> Cases_on `k`
  >- (strip_tac >> mp_tac (Q.SPECL [`h::segs`, `j`] sue_segment_endpoint_prefix) >>
      pure_rewrite_tac[listTheory.LENGTH, sue_segment_offset_zero,
        listTheory.DROP_0, listTheory.FLAT, arithmeticTheory.SUB_0,
        arithmeticTheory.ADD_CLAUSES] >> metis_tac[arithmeticTheory.ADD_COMM]) >>
  Cases_on `j` >> simp[] >> strip_tac >>
  `LENGTH (EL n' segs) > 0` by (Cases_on `EL n' segs` >> gvs[]) >>
  `LENGTH h + sue_segment_offset segs n' + LENGTH (EL n' segs) - 1 -
      (LENGTH h + sue_segment_offset segs n) =
   sue_segment_offset segs n' + LENGTH (EL n' segs) - 1 -
      sue_segment_offset segs n` by decide_tac >>
  simp[listTheory.DROP_APPEND, listTheory.DROP_LENGTH_TOO_LONG] >>
  first_x_assum (qspecl_then [`n`, `n'`] mp_tac) >>
  simp[NoAsms] >> metis_tac[]
QED

Theorem sue_segments_supply_assign_interval:
  sue_segments_supply dfg s insts = (segs,s') /\
  k <= LENGTH insts /\ n <= LENGTH (DROP k insts) /\
  EVERY (\inst. inst.inst_opcode = ASSIGN) (TAKE n (DROP k insts)) ==>
  FLAT (TAKE n (DROP k segs)) = TAKE n (DROP k insts)
Proof
  strip_tac >>
  `sue_segments_supply dfg s (TAKE k insts ++ DROP k insts) = (segs,s')` by simp[] >>
  drule sue_segments_supply_append >> strip_tac >>
  qpat_assum `sue_segments_supply _ _ (TAKE _ _) = _`
    (mp_then Any assume_tac sue_segments_supply_length) >>
  `DROP k segs = sy` by (gvs[] >> simp[listTheory.DROP_APPEND]) >>
  `?sm'. sue_segments_supply dfg sm (TAKE n (DROP k insts)) = (TAKE n sy,sm')` by
    (irule sue_segments_supply_take >> goal_assum (drule_at Any) >> simp[]) >>
  drule_all sue_segments_supply_assigns >> strip_tac >>
  gvs[] >> qmatch_goalsub_abbrev_tac `FLAT (MAP f xs)` >>
  `FLAT (MAP (\inst. [inst]) xs) = xs` by (rpt (pop_assum kall_tac) >> Induct_on `xs` >> simp[]) >>
  gvs[Abbr `f`]
QED

Theorem sue_segments_supply_endpoint_resolve:
  sue_segments_supply dfg s insts = (segs,s') /\ ir_supply_inst_ok s /\
  P SUBSET set s.irs_used_vars /\ i < LENGTH insts /\
  (!inst v. MEM inst insts /\ MEM (Var v) inst.inst_operands ==> v IN P) ==>
  EVERY (\a. a.inst_opcode = ASSIGN /\ LENGTH a.inst_outputs = 1 /\
              LENGTH a.inst_operands = 1) (BUTLAST (EL i segs)) /\
  LIST_REL (\op op'. resolve_block_assigns (REVERSE (BUTLAST (EL i segs))) op' = op)
    (EL i insts).inst_operands (LAST (EL i segs)).inst_operands /\
  (!op. (!v. op = Var v ==> v IN P) ==>
        resolve_block_assigns (REVERSE (BUTLAST (EL i segs))) op = op)
Proof
  strip_tac >> drule_all sue_segments_supply_index_ready >> strip_tac >>
  `!v. MEM (Var v) (EL i insts).inst_operands ==> MEM v si.irs_used_vars` by
    metis_tac[listTheory.EL_MEM, pred_setTheory.SUBSET_DEF, listTheory.MEM] >>
  drule_all sue_expand_inst_supply_resolve >> strip_tac >> simp[] >>
  rpt strip_tac >> first_x_assum irule >>
  metis_tac[pred_setTheory.SUBSET_DEF, listTheory.MEM]
QED

Theorem sue_segments_supply_pair_layout:
  sue_segments_supply dfg s insts = (segs,s') /\
  i < j /\ j < LENGTH insts /\
  EVERY (\inst. inst.inst_opcode = ASSIGN) (TAKE (j-SUC i) (DROP (SUC i) insts)) ==>
  sue_segment_offset segs i + LENGTH (EL i segs) - 1 <
    sue_segment_offset segs j + LENGTH (EL j segs) - 1 /\
  TAKE ((sue_segment_offset segs j + LENGTH (EL j segs) - 1) -
        SUC (sue_segment_offset segs i + LENGTH (EL i segs) - 1))
    (DROP (SUC (sue_segment_offset segs i + LENGTH (EL i segs) - 1)) (FLAT segs)) =
  TAKE (j-SUC i) (DROP (SUC i) insts) ++ BUTLAST (EL j segs)
Proof
  strip_tac >> drule sue_segments_supply_length >> strip_tac >>
  drule sue_segments_supply_nonempty >> strip_tac >>
  `i < LENGTH segs /\ j < LENGTH segs /\ EL i segs <> [] /\ EL j segs <> []` by
    (gvs[listTheory.EVERY_EL] >> metis_tac[]) >>
  `LENGTH (EL i segs) > 0 /\ LENGTH (EL j segs) > 0` by
    (Cases_on `EL i segs` >> Cases_on `EL j segs` >> gvs[]) >>
  `sue_segment_offset segs (SUC i) = sue_segment_offset segs i + LENGTH (EL i segs)` by
    (irule sue_segment_offset_suc >> simp[]) >>
  `sue_segment_offset segs (SUC i) <= sue_segment_offset segs j` by
    (irule sue_segment_offset_mono >> simp[]) >>
  `SUC (sue_segment_offset segs i + LENGTH (EL i segs) - 1) =
   sue_segment_offset segs (SUC i)` by decide_tac >>
  conj_tac >- decide_tac >>
  `FLAT (TAKE (j-SUC i) (DROP (SUC i) segs)) =
   TAKE (j-SUC i) (DROP (SUC i) insts)` by
    (irule sue_segments_supply_assign_interval >>
     simp[] >> qexistsl [`dfg`, `s`, `s'`] >> simp[]) >>
  qspecl_then [`segs : instruction list list`, `SUC i`, `j`] mp_tac sue_segment_endpoint_gap >> simp[]
QED

Theorem sue_segments_supply_endpoint_compare:
  sue_segments_supply dfg s insts = (segs,s') /\ ir_supply_inst_ok s /\
  P SUBSET set s.irs_used_vars /\ i < LENGTH insts /\
  (!inst v. MEM inst insts /\ MEM (Var v) inst.inst_operands ==> v IN P) /\
  (!v. p = Var v ==> v IN P) /\ (!v. q = Var v ==> v IN P) /\
  resolve_block_assigns (REVERSE (BUTLAST (EL i segs))) p' = p /\
  same_after_assigns (REVERSE (TAKE i insts)) p q ==>
  same_after_assigns
    (REVERSE (TAKE (sue_segment_offset segs i + LENGTH (EL i segs) - 1) (FLAT segs))) p' q
Proof
  strip_tac >> drule_all sue_segments_supply_endpoint_resolve >> strip_tac >>
  drule sue_segments_supply_length >> strip_tac >>
  drule sue_segments_supply_nonempty >> strip_tac >>
  `i < LENGTH segs /\ EL i segs <> []` by
    (gvs[listTheory.EVERY_EL] >> metis_tac[]) >>
  qspecl_then [`segs : instruction list list`, `i`] mp_tac sue_segment_endpoint_prefix >>
  simp[] >> disch_then SUBST1_TAC >> simp[listTheory.REVERSE_APPEND] >>
  irule same_after_assigns_copy_prefix >>
  simp[listTheory.EVERY_MEM, listTheory.MEM_REVERSE] >>
  `resolve_block_assigns (REVERSE (BUTLAST (EL i segs))) q = q` by metis_tac[] >>
  simp[] >>
  `?sm. sue_segments_supply dfg s (TAKE i insts) = (TAKE i segs,sm)` by
    (irule sue_segments_supply_take >> simp[] >> qexists_tac `s'` >> simp[]) >>
  irule sue_segments_supply_same_after_assigns >>
  qexists_tac `P` >> goal_assum (drule_at Any) >> simp[] >>
  metis_tac[listTheory.MEM_APPEND, listTheory.TAKE_DROP]
QED

Theorem sue_segments_supply_endpoint_operands_two:
  sue_segments_supply dfg s insts = (segs,s') /\ ir_supply_inst_ok s /\
  P SUBSET set s.irs_used_vars /\ i < LENGTH insts /\
  (!inst v. MEM inst insts /\ MEM (Var v) inst.inst_operands ==> v IN P) /\
  (EL i insts).inst_operands = [a;b] ==>
  ?a' b'. (LAST (EL i segs)).inst_operands = [a';b'] /\
    resolve_block_assigns (REVERSE (BUTLAST (EL i segs))) a' = a /\
    resolve_block_assigns (REVERSE (BUTLAST (EL i segs))) b' = b
Proof
  strip_tac >> drule_all sue_segments_supply_endpoint_resolve >>
  simp[listTheory.LIST_REL_CONS1] >> metis_tac[]
QED

Theorem sue_segments_supply_endpoint_operands_three:
  sue_segments_supply dfg s insts = (segs,s') /\ ir_supply_inst_ok s /\
  P SUBSET set s.irs_used_vars /\ i < LENGTH insts /\
  (!inst v. MEM inst insts /\ MEM (Var v) inst.inst_operands ==> v IN P) /\
  (EL i insts).inst_operands = [a;b;c] ==>
  ?a' b' c'. (LAST (EL i segs)).inst_operands = [a';b';c'] /\
    resolve_block_assigns (REVERSE (BUTLAST (EL i segs))) a' = a /\
    resolve_block_assigns (REVERSE (BUTLAST (EL i segs))) b' = b /\
    resolve_block_assigns (REVERSE (BUTLAST (EL i segs))) c' = c
Proof
  strip_tac >> drule_all sue_segments_supply_endpoint_resolve >>
  simp[listTheory.LIST_REL_CONS1] >> metis_tac[]
QED

Theorem sue_segments_supply_revert_forward_pair:
  sue_segments_supply dfg s bb.bb_instructions = (segs,s') /\
  ir_supply_inst_ok s /\ P SUBSET set s.irs_used_vars /\
  (!inst v. MEM inst bb.bb_instructions /\ MEM (Var v) inst.inst_operands ==> v IN P) /\
  revert_forward_pair bb i j ==>
  revert_forward_pair (bb with bb_instructions := FLAT segs)
    (sue_segment_offset segs i + LENGTH (EL i segs) - 1)
    (sue_segment_offset segs j + LENGTH (EL j segs) - 1)
Proof
  strip_tac >>
  qpat_x_assum `revert_forward_pair bb i j`
    (strip_assume_tac o SIMP_RULE (srw_ss())
      [contextCodegenRelTheory.revert_forward_pair_def, get_instruction_def]) >>
  `EVERY (\inst. inst.inst_opcode = ASSIGN)
     (TAKE (j-SUC i) (DROP (SUC i) bb.bb_instructions))` by
    (simp[listTheory.EVERY_EL, listTheory.EL_TAKE, listTheory.EL_DROP] >>
     rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  drule_all sue_segments_supply_endpoint_operands_three >> strip_tac >>
  drule_all sue_segments_supply_endpoint_operands_two >> strip_tac >>
  drule_all sue_segments_supply_pair_layout >> strip_tac >>
  qmatch_goalsub_abbrev_tac `revert_forward_pair _ ii jj` >>
  qmatch_asmsub_abbrev_tac `EVERY _ gap` >>
  rename1 `(LAST (EL i segs)).inst_operands = [pa;sa;ra]` >>
  rename1 `(LAST (EL j segs)).inst_operands = [pb;rb]` >>
  qpat_x_assum `!k. _` kall_tac >>
  `get_instruction (bb with bb_instructions := FLAT segs) ii = SOME (LAST (EL i segs)) /\
   get_instruction (bb with bb_instructions := FLAT segs) jj = SOME (LAST (EL j segs))` by
    (simp[Abbr `ii`, Abbr `jj`] >>
     metis_tac[sue_segments_supply_endpoint_lookup, arithmeticTheory.ADD_COMM]) >>
  `(LAST (EL i segs)).inst_opcode = RETURNDATACOPY /\
   (LAST (EL j segs)).inst_opcode = REVERT` by
    metis_tac[sue_segments_supply_index, sue_expand_inst_supply_last] >>
  pure_rewrite_tac[contextCodegenRelTheory.revert_forward_pair_def] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- suspend "gap_assigns" >>
  qexistsl [`LAST (EL i segs)`, `LAST (EL j segs)`, `pa`, `sa`, `ra`, `pb`, `rb`] >>
  asm_rewrite_tac[] >>
  suspend "comparisons"
QED

Resume sue_segments_supply_revert_forward_pair[comparisons]:
  qpat_x_assum `get_instruction _ ii = _` kall_tac >>
  qpat_x_assum `get_instruction _ jj = _` kall_tac >>
  qpat_x_assum `(LAST (EL i segs)).inst_opcode = _` kall_tac >>
  qpat_x_assum `(LAST (EL j segs)).inst_opcode = _` kall_tac >>
  `EVERY (\a. a.inst_opcode = ASSIGN /\ LENGTH a.inst_outputs = 1 /\
              LENGTH a.inst_operands = 1) (BUTLAST (EL j segs))` by
    (mp_tac (Q.INST [`i` |-> `j`, `insts` |-> `bb.bb_instructions`]
       sue_segments_supply_endpoint_resolve) >> simp[] >> metis_tac[]) >>
  asm_rewrite_tac[basic_block_accessors, listTheory.REVERSE_APPEND] >>
  `!op. resolve_block_assigns
     (REVERSE (BUTLAST (EL j segs)) ++ REVERSE gap) op =
     resolve_block_assigns (REVERSE gap)
       (resolve_block_assigns (REVERSE (BUTLAST (EL j segs))) op)` by
    (irule resolve_block_assigns_copy_append >>
     gvs[listTheory.EVERY_MEM, listTheory.MEM_REVERSE]) >>
  simp_tac (srw_ss()) [] >>
  simp[listTheory.REVERSE_APPEND] >>
  `!op v. MEM op [p;src;rds;p';rds'] /\ op = Var v ==> v IN P` by
    (rpt strip_tac >>
     `MEM (EL i bb.bb_instructions) bb.bb_instructions /\
      MEM (EL j bb.bb_instructions) bb.bb_instructions` by
       metis_tac[listTheory.EL_MEM] >>
     metis_tac[listTheory.MEM]) >>
  `EVERY (\inst. !v. MEM (Var v) inst.inst_operands ==> v IN P) (REVERSE gap)` by
    (simp[listTheory.EVERY_MEM, listTheory.MEM_REVERSE, Abbr `gap`] >>
     metis_tac[listTheory.MEM_APPEND, listTheory.TAKE_DROP]) >>
  `(!v. resolve_block_assigns (REVERSE gap) p' = Var v ==> v IN P) /\
   (!v. resolve_block_assigns (REVERSE gap) rds' = Var v ==> v IN P)` by
    (metis_tac[resolve_block_assigns_preserves_vars, listTheory.MEM]) >>
  rpt conj_tac >>
  simp[Abbr `ii`] >>
  metis_tac[sue_segments_supply_endpoint_compare, arithmeticTheory.ADD_COMM,
            listTheory.MEM, operand_distinct]
QED

Resume sue_segments_supply_revert_forward_pair[gap_assigns]:
  `EVERY (\a. a.inst_opcode = ASSIGN /\ LENGTH a.inst_outputs = 1 /\
              LENGTH a.inst_operands = 1) (BUTLAST (EL j segs))` by
    (mp_tac (Q.INST [`i` |-> `j`, `insts` |-> `bb.bb_instructions`]
       sue_segments_supply_endpoint_resolve) >> simp[] >> metis_tac[]) >>
  `EVERY (\inst. inst.inst_opcode = ASSIGN)
    (TAKE (jj-SUC ii) (DROP (SUC ii) (FLAT segs)))` by
    (asm_rewrite_tac[listTheory.EVERY_APPEND] >>
     gvs[listTheory.EVERY_MEM]) >>
  qpat_x_assum `TAKE _ _ = _` kall_tac >>
  rpt strip_tac >>
  gvs[get_instruction_def] >>
  qpat_x_assum `EVERY _ (TAKE _ _)` mp_tac >>
  simp[listTheory.EVERY_EL, listTheory.EL_TAKE, listTheory.EL_DROP] >>
  disch_then (qspec_then `k-SUC ii` mp_tac) >> simp[] >>
  `SUC ii + (k-SUC ii) = k /\ k-SUC ii < jj-SUC ii /\
   k-SUC ii < LENGTH (FLAT segs) - SUC ii` by decide_tac >> simp[]
QED

Finalise sue_segments_supply_revert_forward_pair

(* end pair transport *)
