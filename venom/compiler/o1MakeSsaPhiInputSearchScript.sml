Theory o1MakeSsaPhiInputSearch
Ancestors
  o1SourceUnitCheck o1PassContract o1MakeSsaShapeProbe o1MakeSsaReachable
  o1MakeSsaCfg makeSsaCurrentProps
  makeSsaCurrentDefs irSupply unitShapeDefs venomInst list rich_list

(* Computed saturation may be used in either direction only after this
   positive-rule check and copy_phi_closed's negative-rule check. *)
Theorem phi_search_fires_sound[local]:
  MEM inst (fn_insts fn) /\ copy_phi_fires origin seen inst /\
  (!y. MEM y seen ==> copy_phi_var origin fn y) /\
  MEM x inst.inst_outputs ==> copy_phi_var origin fn x
Proof
  simp[copy_phi_fires_def, EXISTS_MEM, AllCaseEqs()] >>
  rpt strip_tac
  >- metis_tac[copy_phi_var_seed]
  >- (Cases_on `inst.inst_operands` >> gvs[] >>
      Cases_on `h` >> gvs[] >> Cases_on `t` >> gvs[] >>
      metis_tac[copy_phi_var_assign])
  >> Cases_on `op` >> gvs[] >> metis_tac[copy_phi_var_phi]
QED

Theorem phi_search_step_sound[local]:
  (!y. MEM y seen ==> copy_phi_var origin fn y) ==>
  !x. MEM x (copy_phi_step origin fn seen) ==> copy_phi_var origin fn x
Proof
  simp[copy_phi_step_def, MEM_FLAT, MEM_MAP, MEM_FILTER] >>
  rpt strip_tac >> gvs[AllCaseEqs(), MEM_FILTER] >>
  irule phi_search_fires_sound >> metis_tac[]
QED

Theorem phi_search_iter_sound[local]:
  !n seen. (!y. MEM y seen ==> copy_phi_var origin fn y) ==>
  !x. MEM x (copy_phi_iter origin fn n seen) ==> copy_phi_var origin fn x
Proof
  Induct >- simp[Once copy_phi_iter_def] >>
  rpt strip_tac >>
  qpat_x_assum `MEM x (copy_phi_iter _ _ _ _)` mp_tac >>
  simp[Once copy_phi_iter_def] >> IF_CASES_TAC >> simp[] >>
  drule phi_search_step_sound >> disch_tac >>
  qpat_x_assum `!seen. _` (qspec_then `copy_phi_step origin fn seen` mp_tac) >> simp[]
QED

Theorem phi_search_vars_exact:
  copy_phi_closed origin fn (copy_phi_vars origin fn) ==>
  !x. (copy_phi_var origin fn x <=> MEM x (copy_phi_vars origin fn))
Proof
  strip_tac >> gen_tac >> eq_tac
  >- metis_tac[copy_phi_closed_sound] >>
  mp_tac (Q.SPECL [`SUC (LENGTH (fn_insts fn))`, `[]`] phi_search_iter_sound) >>
  simp[copy_phi_vars_def]
QED

(* First enumerated product: two seed arms, nine ordered PHI-input pairs,
   three return spellings, and PHI-versus-ASSIGN for the second writer.
   The q/t pair can be cyclic, with or without an external r escape. *)
Definition phi_search_diamond_def:
  phi_search_diamond seed_right a b ret second_phi =
  mk_raw_function "entry" [
    <| bb_label := "entry"; bb_instructions := [
       mk_inst 0 JNZ [Lit 1w;Label "left";Label "right"] []] |>;
    <| bb_label := "left"; bb_instructions :=
       (if seed_right then [] else [mk_inst 1 RETPC_PARAM [Lit 0w] ["r"]]) ++
       [mk_inst 2 JMP [Label "join"] []] |>;
    <| bb_label := "right"; bb_instructions :=
       (if seed_right then [mk_inst 1 RETPC_PARAM [Lit 0w] ["r"]] else []) ++
       [mk_inst 3 JMP [Label "join"] []] |>;
    <| bb_label := "join"; bb_instructions := [
       mk_inst 4 PHI [Label "left";Var a;Label "right";Var b] ["q"];
       (if second_phi then mk_inst 5 PHI [Label "left";Var "q";Label "right";Var "q"] ["t"]
        else mk_inst 5 ASSIGN [Var "q"] ["t"]);
       mk_inst 6 RET [Var ret] []] |>]
End

Definition phi_search_supply_def:
  phi_search_supply = probe_supply with <| irs_next_inst := 7;
    irs_used_inst_ids := [0;1;2;3;4;5;6]; irs_used_vars := ["r";"q";"t"];
    irs_used_labels := ["entry";"left";"right";"join"] |>
End

Definition phi_search_diamonds_def:
  phi_search_diamonds = FLAT (MAP (\seed_right.
    FLAT (MAP (\a. FLAT (MAP (\b.
      FLAT (MAP (\ret. MAP (\second_phi.
        let fn = phi_search_diamond seed_right a b ret second_phi in
        (mk_venom_context [fn] NONE, fn, phi_search_supply)) [T;F])
        ["r";"q";"t"])) ["r";"q";"t"])) ["r";"q";"t"])) [T;F])
End

Theorem phi_search_diamonds_count:
  LENGTH phi_search_diamonds = 108
Proof
  EVAL_TAC
QED

Theorem phi_search_supply_ok:
  ir_supply_inst_ok phi_search_supply
Proof
  EVAL_TAC
QED

Theorem phi_search_diamonds_wf:
  EVERY (\(ctx,fn,s). wf_function fn /\ fn_inst_wf fn /\
    blocks_have_leading_phi fn.fn_blocks /\ ir_supply_inst_ok s)
    phi_search_diamonds
Proof
  EVAL_TAC
QED

(* This checker is valid only after reachable_fn fn = fn has been proved;
   it must not be used for the dead-predecessor family. *)
Definition phi_search_retpc_check_def:
  phi_search_retpc_check fn <=>
    let seen = copy_phi_vars RETPC_PARAM fn in
    copy_phi_closed RETPC_PARAM fn seen /\
    EVERY (\i.
      (MEM i.inst_opcode [RET;RETFMP;DRET] ==>
        i.inst_operands <> [] /\
        case LAST i.inst_operands of Var x => MEM x seen | _ => F) /\
      (i.inst_opcode = PHI ==>
        (!x y. MEM (Var x) i.inst_operands /\ MEM (Var y) i.inst_operands /\
               MEM x seen ==> MEM y seen)) /\
      (!x. MEM x i.inst_outputs /\ MEM x seen ==>
        i.inst_opcode = RETPC_PARAM \/
        (i.inst_opcode = ASSIGN /\ ?y. i.inst_operands = [Var y] /\ MEM y seen) \/
        (i.inst_opcode = PHI /\
         (?y. MEM (Var y) i.inst_operands /\ MEM y seen) /\
         (!y. MEM (Var y) i.inst_operands ==> MEM y seen)))) (fn_insts fn) /\
    (!i j x. MEM i (fn_insts fn) /\ MEM j (fn_insts fn) /\
      MEM x i.inst_outputs /\ MEM x j.inst_outputs /\ MEM x seen ==> i = j)
End

Theorem phi_search_retpc_check_sound:
  reachable_fn fn = fn /\ phi_search_retpc_check fn ==> retpc_shape_ok fn
Proof
  simp[phi_search_retpc_check_def, LET_THM, EVERY_MEM] >> strip_tac >>
  drule phi_search_vars_exact >> strip_tac >>
  simp[retpc_shape_ok_def, retpc_var_def] >> conj_tac
  >- (rpt strip_tac >> qpat_x_assum `!i. MEM i _ ==> _` (qspec_then `inst` mp_tac) >> simp[] >> strip_tac >>
      Cases_on `LAST inst.inst_operands` >> gvs[] >>
      qexistsl_tac [`FRONT inst.inst_operands`, `s`] >> metis_tac[APPEND_FRONT_LAST]) >>
  metis_tac[]
QED

Theorem phi_search_diamond_edges[local]:
  fn_cfg_edge (phi_search_diamond sr a b ret sp) "entry" "left" /\
  fn_cfg_edge (phi_search_diamond sr a b ret sp) "entry" "right" /\
  fn_cfg_edge (phi_search_diamond sr a b ret sp) "left" "join"
Proof
  Cases_on `sr` >> Cases_on `sp` >>
  simp[venomWfTheory.fn_cfg_edge_def, phi_search_diamond_def,
       mk_raw_function_def, GSYM AND_IMP_INTRO, DISJ_IMP_THM,
       LEFT_AND_OVER_OR, RIGHT_AND_OVER_OR, EXISTS_OR_THM] >> EVAL_TAC
QED

Theorem phi_search_diamond_labels_reachable:
  !l. MEM l ["entry";"left";"right";"join"] ==>
      fn_reachable (phi_search_diamond sr a b ret sp) l
Proof
  rpt strip_tac >> simp[venomWfTheory.fn_reachable_def] >>
  qexists_tac `"entry"` >> (conj_tac >- EVAL_TAC) >>
  gvs[] >> metis_tac[relationTheory.RTC_RULES, phi_search_diamond_edges]
QED

Theorem phi_search_diamond_reachable:
  reachable_fn (phi_search_diamond sr a b ret sp) =
  phi_search_diamond sr a b ret sp
Proof
  assume_tac phi_search_diamond_labels_reachable >>
  `!bb. MEM bb (phi_search_diamond sr a b ret sp).fn_blocks ==>
        fn_reachable (phi_search_diamond sr a b ret sp) bb.bb_label` by
    (gen_tac >> strip_tac >> first_x_assum irule >>
     qpat_x_assum `MEM bb _` mp_tac >>
     simp[phi_search_diamond_def, mk_raw_function_def] >> rpt strip_tac >> gvs[]) >>
  drule reachable_preds_all_reachable >> disch_tac >>
  `reachable_preds (phi_search_diamond sr a b ret sp) "join" = ["left";"right"]` by
    (asm_rewrite_tac[] >> Cases_on `sr` >> Cases_on `sp` >>
     simp[NoAsms, venomWfTheory.fn_cfg_edge_def, phi_search_diamond_def,
          mk_raw_function_def, GSYM AND_IMP_INTRO, DISJ_IMP_THM,
          LEFT_AND_OVER_OR, RIGHT_AND_OVER_OR, EXISTS_OR_THM] >> EVAL_TAC) >>
  qpat_x_assum `!lbl. reachable_preds _ lbl = _` kall_tac >>
  irule reachable_fn_fixed >> simp[] >>
  Cases_on `sr` >> Cases_on `sp` >>
  simp[phi_search_diamond_def, mk_raw_function_def, mk_inst_def,
       GSYM AND_IMP_INTRO, DISJ_IMP_THM, FORALL_AND_THM] >>
  qpat_x_assum `reachable_preds _ "join" = _` mp_tac >>
  simp[phi_search_diamond_def, mk_raw_function_def, mk_inst_def] >> strip_tac >>
  simp[reachable_inst_def, mk_inst_def, simplifyCfgDefsTheory.filter_phi_ops_def]
QED

Theorem phi_search_diamond_opaque:
  opaque_use_ok (phi_search_diamond sr a b ret sp)
Proof
  Cases_on `sr` >> Cases_on `sp` >>
  simp[opaque_use_ok_def, phi_search_diamond_def, mk_raw_function_def,
       fn_insts_def, fn_insts_blocks_def, mk_inst_def, retpc_use_ok_def,
       GSYM AND_IMP_INTRO, DISJ_IMP_THM, FORALL_AND_THM, APPEND_EQ_CONS]
QED

Theorem phi_search_diamond_shape:
  phi_search_retpc_check (phi_search_diamond sr a b ret sp) ==>
  o1_fn_shape (mk_venom_context [phi_search_diamond sr a b ret sp] NONE)
    (phi_search_diamond sr a b ret sp)
Proof
  strip_tac >>
  `retpc_shape_ok (phi_search_diamond sr a b ret sp)` by
    (irule phi_search_retpc_check_sound >> simp[phi_search_diamond_reachable]) >>
  rewrite_tac[o1_fn_shape_def, fn_shape_ok_def, phi_search_diamond_opaque] >>
  asm_rewrite_tac[] >> Cases_on `sr` >> Cases_on `sp` >> EVAL_TAC >>
  simp[GSYM AND_IMP_INTRO, DISJ_IMP_THM, FORALL_AND_THM]
QED

Definition phi_search_retained_def:
  phi_search_retained = FILTER (\(ctx,fn,s). phi_search_retpc_check fn)
    phi_search_diamonds
End


Definition phi_search_operand_seen_def:
  phi_search_operand_seen seen op =
    case op of Var x => MEM x seen | _ => F
End

Definition phi_search_operand_safe_def:
  phi_search_operand_safe seen op =
    case op of Var x => MEM x seen | _ => T
End

Definition phi_search_inst_check_def:
  phi_search_inst_check seen i <=>
    (MEM i.inst_opcode [RET;RETFMP;DRET] ==>
      i.inst_operands <> [] /\ phi_search_operand_seen seen (LAST i.inst_operands)) /\
    (i.inst_opcode = PHI /\ EXISTS (phi_search_operand_seen seen) i.inst_operands ==>
      EVERY (phi_search_operand_safe seen) i.inst_operands) /\
    EVERY (\x. MEM x seen ==>
      i.inst_opcode = RETPC_PARAM \/
      (i.inst_opcode = ASSIGN /\
        case i.inst_operands of [Var y] => MEM y seen | _ => F) \/
      (i.inst_opcode = PHI /\
        EXISTS (phi_search_operand_seen seen) i.inst_operands /\
        EVERY (phi_search_operand_safe seen) i.inst_operands)) i.inst_outputs
End

Definition phi_search_exec_check_def:
  phi_search_exec_check fn <=>
    let seen = copy_phi_vars RETPC_PARAM fn in
    copy_phi_closed RETPC_PARAM fn seen /\
    EVERY (phi_search_inst_check seen) (fn_insts fn) /\
    EVERY (\i. EVERY (\j.
      EVERY (\x. MEM x j.inst_outputs /\ MEM x seen ==> i = j) i.inst_outputs)
      (fn_insts fn)) (fn_insts fn)
End

Theorem phi_search_operand_seen_exists[local]:
  EXISTS (phi_search_operand_seen seen) ops <=>
  ?y. MEM (Var y) ops /\ MEM y seen
Proof
  simp[EXISTS_MEM, phi_search_operand_seen_def] >> eq_tac >> rpt strip_tac
  >- (Cases_on `e` >> gvs[] >> metis_tac[]) >>
  qexists_tac `Var y` >> simp[]
QED

Theorem phi_search_operand_safe_every[local]:
  EVERY (phi_search_operand_safe seen) ops <=>
  !y. MEM (Var y) ops ==> MEM y seen
Proof
  simp[EVERY_MEM, phi_search_operand_safe_def] >> eq_tac >> rpt strip_tac
  >- (first_x_assum (qspec_then `Var y` mp_tac) >> simp[]) >>
  Cases_on `e` >> gvs[]
QED

Theorem phi_search_exec_check_sound:
  phi_search_exec_check fn ==> phi_search_retpc_check fn
Proof
  simp[phi_search_exec_check_def, phi_search_retpc_check_def,
       phi_search_inst_check_def, LET_THM, EVERY_MEM,
       phi_search_operand_seen_exists, phi_search_operand_safe_every] >>
  strip_tac >> conj_tac
  >- (rpt strip_tac >> qpat_x_assum `!e. MEM e _ ==> (_ /\ _)` (qspec_then `i` mp_tac) >>
      simp[] >> strip_tac >>
      gvs[phi_search_operand_seen_def, AllCaseEqs()]
      >- (qpat_x_assum `(?z. _) ==> _` mp_tac >>
          impl_tac >- (qexists_tac `x` >> simp[]) >> simp[]) >>
      qpat_x_assum `!x. MEM x i.inst_outputs ==> _` (qspec_then `x` mp_tac) >>
      simp[] >> strip_tac >> gvs[AllCaseEqs()]
      >- (Cases_on `i.inst_operands` >> gvs[] >>
          Cases_on `h` >> gvs[] >> Cases_on `t` >> gvs[]) >>
      metis_tac[]) >>
  metis_tac[]
QED

Definition phi_search_chunk_def:
  phi_search_chunk sr a b = FLAT (MAP (\ret.
    MAP (\sp. phi_search_diamond sr a b ret sp) [T;F]) ["r";"q";"t"])
End

Definition phi_search_good_chunk_def:
  phi_search_good_chunk sr a b = FILTER phi_search_exec_check (phi_search_chunk sr a b)
End

Theorem phi_search_chunk_inputs:
  EVERY (\fn. o1_fn_shape (mk_venom_context [fn] NONE) fn /\
    ir_supply_inst_ok phi_search_supply) (phi_search_good_chunk sr a b)
Proof
  simp[phi_search_good_chunk_def, EVERY_FILTER, EVERY_MEM] >>
  rpt strip_tac >- (gvs[MEM_FILTER, phi_search_chunk_def] >>
    irule phi_search_diamond_shape >> irule phi_search_exec_check_sound >> simp[]) >>
  simp[phi_search_supply_ok]
QED

Theorem phi_search_chunk_counts:
  !sr a b. MEM sr [T;F] /\ MEM a ["r";"q";"t"] /\ MEM b ["r";"q";"t"] ==>
  LENGTH (phi_search_good_chunk sr a b) = (if a = "r" \/ b = "r" then 6 else 2)
Proof
  rpt gen_tac >> strip_tac >> gvs[] >> Cases_on `sr`
  >- EVAL_TAC >- EVAL_TAC >- EVAL_TAC >- EVAL_TAC
  >- EVAL_TAC >- EVAL_TAC >- EVAL_TAC >- EVAL_TAC
  >- EVAL_TAC >- EVAL_TAC >- EVAL_TAC >- EVAL_TAC
  >- EVAL_TAC >- EVAL_TAC >- EVAL_TAC >- EVAL_TAC
  >- EVAL_TAC >> EVAL_TAC
QED

Theorem phi_search_chunk_outputs:
  !sr a b. MEM sr [T;F] /\ MEM a ["r";"q";"t"] /\ MEM b ["r";"q";"t"] ==>
  EVERY (\fn. phi_search_exec_check
    (FST (make_ssa_current_fn phi_search_supply fn)))
    (phi_search_good_chunk sr a b)
Proof
  rpt gen_tac >> strip_tac >> gvs[] >> Cases_on `sr`
  >- EVAL_TAC >- EVAL_TAC >- EVAL_TAC >- EVAL_TAC
  >- EVAL_TAC >- EVAL_TAC >- EVAL_TAC >- EVAL_TAC
  >- EVAL_TAC >- EVAL_TAC >- EVAL_TAC >- EVAL_TAC
  >- EVAL_TAC >- EVAL_TAC >- EVAL_TAC >- EVAL_TAC
  >- EVAL_TAC >> EVAL_TAC
QED

Definition phi_search_phi_filter_def:
  phi_search_phi_filter fn <=> EVERY (\bb. EVERY (\i.
    i.inst_opcode = PHI ==> bb.bb_label = "join" /\
      simplifyCfgDefs$filter_phi_ops ["left";"right"] i.inst_operands = i.inst_operands)
    bb.bb_instructions) fn.fn_blocks
End

Theorem phi_search_chunk_outputs_filter:
  !sr a b. MEM sr [T;F] /\ MEM a ["r";"q";"t"] /\ MEM b ["r";"q";"t"] ==>
  EVERY (\fn. phi_search_phi_filter (FST (make_ssa_current_fn phi_search_supply fn)))
    (phi_search_good_chunk sr a b)
Proof
  rpt gen_tac >> strip_tac >> gvs[] >> Cases_on `sr`
  >- EVAL_TAC >- EVAL_TAC >- EVAL_TAC >- EVAL_TAC
  >- EVAL_TAC >- EVAL_TAC >- EVAL_TAC >- EVAL_TAC
  >- EVAL_TAC >- EVAL_TAC >- EVAL_TAC >- EVAL_TAC
  >- EVAL_TAC >- EVAL_TAC >- EVAL_TAC >- EVAL_TAC
  >- EVAL_TAC >> EVAL_TAC
QED

Theorem phi_search_diamond_output_reachable:
  make_ssa_current_fn s (phi_search_diamond sr a b ret sp) = (g,s') /\
  phi_search_phi_filter g ==> reachable_fn g = g
Proof
  strip_tac >>
  `ALL_DISTINCT (MAP basic_block_bb_label
    (phi_search_diamond sr a b ret sp).fn_blocks)` by
    simp[phi_search_diamond_def, mk_raw_function_def] >>
  drule_all make_ssa_current_fn_reachable >> strip_tac >>
  drule_all make_ssa_current_fn_cfg_edge >> strip_tac >>
  drule make_ssa_current_fn_labels >> strip_tac >>
  `!bb. MEM bb g.fn_blocks ==> fn_reachable g bb.bb_label` by
    (rpt strip_tac >> asm_rewrite_tac[] >>
     irule phi_search_diamond_labels_reachable >>
     `MEM bb.bb_label (MAP basic_block_bb_label g.fn_blocks)` by (simp[MEM_MAP] >> qexists_tac `bb` >> simp[]) >>
     gvs[phi_search_diamond_def, mk_raw_function_def]) >>
  drule reachable_preds_all_reachable >> strip_tac >>
  `reachable_preds g "join" = ["left";"right"]` by
    (asm_rewrite_tac[] >> Cases_on `sr` >> Cases_on `sp` >>
     simp[NoAsms, venomWfTheory.fn_cfg_edge_def, phi_search_diamond_def,
          mk_raw_function_def, GSYM AND_IMP_INTRO, DISJ_IMP_THM,
          LEFT_AND_OVER_OR, RIGHT_AND_OVER_OR, EXISTS_OR_THM] >> EVAL_TAC) >>
  irule reachable_fn_fixed >> simp[] >>
  gvs[phi_search_phi_filter_def, EVERY_MEM] >> rpt strip_tac >>
  Cases_on `i.inst_opcode = PHI` >> simp[reachable_inst_def] >>
  qpat_x_assum `!bb. MEM bb g.fn_blocks ==> !i. _`
    (qspec_then `bb` mp_tac) >> simp[] >>
  disch_then (qspec_then `i` mp_tac) >> simp[] >> strip_tac >> gvs[]
QED

Theorem phi_search_chunk_outputs_retpc:
  MEM sr [T;F] /\ MEM a ["r";"q";"t"] /\ MEM b ["r";"q";"t"] ==>
  EVERY (\fn. retpc_shape_ok (FST (make_ssa_current_fn phi_search_supply fn)))
    (phi_search_good_chunk sr a b)
Proof
  strip_tac >>
  qspecl_then [`sr`,`a`,`b`] mp_tac phi_search_chunk_outputs >>
  qspecl_then [`sr`,`a`,`b`] mp_tac phi_search_chunk_outputs_filter >>
  simp[EVERY_MEM] >> disch_tac >> disch_tac >>
  qx_gen_tac `fn` >> disch_tac >>
  `?ret sp. fn = phi_search_diamond sr a b ret sp` by
    (qpat_x_assum `MEM fn _` mp_tac >>
     pure_rewrite_tac[phi_search_good_chunk_def, MEM_FILTER] >>
     simp[phi_search_chunk_def] >> metis_tac[]) >>
  qpat_x_assum `fn = _` SUBST_ALL_TAC >>
  `phi_search_phi_filter (FST (make_ssa_current_fn phi_search_supply
      (phi_search_diamond sr a b ret sp)))` by metis_tac[] >>
  `phi_search_exec_check (FST (make_ssa_current_fn phi_search_supply
      (phi_search_diamond sr a b ret sp)))` by metis_tac[] >>
  Cases_on `make_ssa_current_fn phi_search_supply
    (phi_search_diamond sr a b ret sp)` >>
  RULE_ASSUM_TAC (REWRITE_RULE [pairTheory.FST]) >>
  irule phi_search_retpc_check_sound >> reverse conj_tac
  >- (simp[] >> irule phi_search_diamond_output_reachable >> metis_tac[]) >>
  irule phi_search_exec_check_sound >> metis_tac[]
QED

(* A computable reachable view, justified by a separate label certificate. *)
Definition phi_search_preds_def:
  phi_search_preds fn live lbl = FILTER (\l. MEM l live /\
    EXISTS (\bb. bb.bb_label = l /\ MEM lbl (bb_succs bb)) fn.fn_blocks)
    (MAP basic_block_bb_label fn.fn_blocks)
End

Definition phi_search_slice_def:
  phi_search_slice live fn = fn with fn_blocks :=
    MAP (\bb. bb with bb_instructions := MAP (\i.
      if i.inst_opcode = PHI then i with inst_operands :=
        simplifyCfgDefs$filter_phi_ops (phi_search_preds fn live bb.bb_label) i.inst_operands
      else i) bb.bb_instructions)
    (FILTER (\bb. MEM bb.bb_label live) fn.fn_blocks)
End

Theorem phi_search_slice_sound:
  (!bb. MEM bb fn.fn_blocks ==>
    (fn_reachable fn bb.bb_label <=> MEM bb.bb_label live)) ==>
  reachable_fn fn = phi_search_slice live fn
Proof
  strip_tac >>
  `!lbl. reachable_preds fn lbl = phi_search_preds fn live lbl` by
    (simp[reachable_preds_def, phi_search_preds_def] >> gen_tac >>
     simp[FILTER_EQ, EVERY_MEM, MEM_MAP, EXISTS_MEM, venomWfTheory.fn_cfg_edge_def] >>
     metis_tac[]) >>
  `FILTER (\bb. fn_reachable fn bb.bb_label) fn.fn_blocks =
   FILTER (\bb. MEM bb.bb_label live) fn.fn_blocks` by
    (simp[FILTER_EQ, EVERY_MEM]) >>
  `!lbl. reachable_inst fn lbl = (\i.
    if i.inst_opcode = PHI then i with inst_operands :=
      simplifyCfgDefs$filter_phi_ops (phi_search_preds fn live lbl) i.inst_operands
    else i)` by simp[FUN_EQ_THM, reachable_inst_def] >>
  simp[reachable_fn_def, phi_search_slice_def]
QED

Theorem phi_search_full_reachable_check_sound:
  phi_search_exec_check fn /\ phi_search_exec_check (reachable_fn fn) ==>
  retpc_shape_ok fn
Proof
  strip_tac >>
  `phi_search_retpc_check fn /\ phi_search_retpc_check (reachable_fn fn)` by
    metis_tac[phi_search_exec_check_sound] >>
  fs[phi_search_retpc_check_def, LET_THM, EVERY_MEM] >>
  `!x. copy_phi_var RETPC_PARAM fn x <=> MEM x (copy_phi_vars RETPC_PARAM fn)` by
    metis_tac[phi_search_vars_exact] >>
  `!x. copy_phi_var RETPC_PARAM (reachable_fn fn) x <=>
       MEM x (copy_phi_vars RETPC_PARAM (reachable_fn fn))` by
    metis_tac[phi_search_vars_exact] >>
  simp[retpc_shape_ok_def, retpc_var_def] >> conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!i. MEM i (fn_insts (reachable_fn fn)) ==> _`
        (qspec_then `inst` mp_tac) >> simp[] >> strip_tac >>
      Cases_on `LAST inst.inst_operands` >> gvs[] >>
      qexistsl_tac [`FRONT inst.inst_operands`, `s`] >> metis_tac[APPEND_FRONT_LAST]) >>
  metis_tac[]
QED

Definition phi_search_loop_def:
  phi_search_loop a b ret sp = mk_raw_function "entry" [
    <| bb_label := "entry"; bb_instructions := [mk_inst 0 JMP [Label "head"] []] |>;
    <| bb_label := "head"; bb_instructions := [
      mk_inst 1 PHI [Label "entry";Var a;Label "body";Var b] ["q"];
      (if sp then mk_inst 2 PHI [Label "entry";Var "q";Label "body";Var "q"] ["t"]
       else mk_inst 2 ASSIGN [Var "q"] ["t"]);
      mk_inst 3 JNZ [Lit 1w;Label "body";Label "exit"] []] |>;
    <| bb_label := "body"; bb_instructions := [
      mk_inst 4 RETPC_PARAM [Lit 0w] ["r"]; mk_inst 5 JMP [Label "head"] []] |>;
    <| bb_label := "exit"; bb_instructions := [mk_inst 6 RET [Var ret] []] |>]
End

Definition phi_search_loop_supply_def:
  phi_search_loop_supply = phi_search_supply with
    irs_used_labels := ["entry";"head";"body";"exit"]
End

Theorem phi_search_loop_reachable_labels:
  MEM l ["entry";"head";"body";"exit"] ==>
  fn_reachable (phi_search_loop a b ret sp) l
Proof
  `fn_cfg_edge (phi_search_loop a b ret sp) "entry" "head" /\
   fn_cfg_edge (phi_search_loop a b ret sp) "head" "body" /\
   fn_cfg_edge (phi_search_loop a b ret sp) "head" "exit"` by
    (Cases_on `sp` >>
     simp[NoAsms, venomWfTheory.fn_cfg_edge_def, phi_search_loop_def,
       mk_raw_function_def, GSYM AND_IMP_INTRO, DISJ_IMP_THM,
       LEFT_AND_OVER_OR, RIGHT_AND_OVER_OR, EXISTS_OR_THM] >> EVAL_TAC) >>
  strip_tac >> simp[venomWfTheory.fn_reachable_def] >>
  qexists_tac `"entry"` >> (conj_tac >- EVAL_TAC) >>
  gvs[] >> metis_tac[relationTheory.RTC_RULES]
QED

Theorem phi_search_loop_slice:
  reachable_fn (phi_search_loop a b ret sp) =
  phi_search_slice ["entry";"head";"body";"exit"] (phi_search_loop a b ret sp)
Proof
  irule phi_search_slice_sound >> rpt strip_tac >>
  `MEM bb.bb_label ["entry";"head";"body";"exit"]` by
    (qpat_x_assum `MEM bb _` mp_tac >> simp[phi_search_loop_def, mk_raw_function_def] >>
     rpt strip_tac >> gvs[]) >>
  simp[] >> irule phi_search_loop_reachable_labels >> simp[]
QED

Theorem phi_search_loop_reachable:
  reachable_fn (phi_search_loop a b ret sp) = phi_search_loop a b ret sp
Proof
  rewrite_tac[phi_search_loop_slice] >> Cases_on `sp` >> EVAL_TAC
QED

Theorem phi_search_loop_shape:
  phi_search_exec_check (phi_search_loop a b ret sp) ==>
  o1_fn_shape (mk_venom_context [phi_search_loop a b ret sp] NONE)
    (phi_search_loop a b ret sp)
Proof
  strip_tac >>
  `retpc_shape_ok (phi_search_loop a b ret sp)` by
    (irule phi_search_retpc_check_sound >> simp[phi_search_loop_reachable] >>
     irule phi_search_exec_check_sound >> simp[]) >>
  rewrite_tac[o1_fn_shape_def, fn_shape_ok_def] >>
  asm_rewrite_tac[] >> Cases_on `sp` >> EVAL_TAC >>
  simp[GSYM AND_IMP_INTRO, DISJ_IMP_THM, FORALL_AND_THM, APPEND_EQ_CONS]
QED

Theorem phi_search_loop_output_slice:
  make_ssa_current_fn s (phi_search_loop a b ret sp) = (g,s') ==>
  reachable_fn g = phi_search_slice ["entry";"head";"body";"exit"] g
Proof
  strip_tac >>
  `ALL_DISTINCT (MAP basic_block_bb_label (phi_search_loop a b ret sp).fn_blocks)` by
    simp[phi_search_loop_def, mk_raw_function_def] >>
  drule_all make_ssa_current_fn_reachable >> strip_tac >>
  drule make_ssa_current_fn_labels >> strip_tac >>
  irule phi_search_slice_sound >> rpt strip_tac >>
  `MEM bb.bb_label (MAP basic_block_bb_label g.fn_blocks)` by
    (simp[MEM_MAP] >> qexists_tac `bb` >> simp[]) >>
  `MEM bb.bb_label ["entry";"head";"body";"exit"]` by
    gvs[phi_search_loop_def, mk_raw_function_def] >>
  simp[] >> asm_rewrite_tac[] >> irule phi_search_loop_reachable_labels >> simp[]
QED

Definition phi_search_loop_chunk_def:
  phi_search_loop_chunk a b = FILTER phi_search_exec_check
    (FLAT (MAP (\ret. MAP (\sp. phi_search_loop a b ret sp) [T;F]) ["r";"q";"t"]))
End

Theorem phi_search_loop_chunk_inputs:
  EVERY (\fn. o1_fn_shape (mk_venom_context [fn] NONE) fn /\
    ir_supply_inst_ok phi_search_loop_supply) (phi_search_loop_chunk a b)
Proof
  pure_rewrite_tac[phi_search_loop_chunk_def, EVERY_MEM] >>
  gen_tac >> pure_rewrite_tac[MEM_FILTER] >> strip_tac >> BETA_TAC >> conj_tac
  >- (qpat_x_assum `MEM e _` mp_tac >> simp[] >> rpt strip_tac >> gvs[] >>
      irule phi_search_loop_shape >> simp[]) >> EVAL_TAC
QED

Theorem phi_search_loop_chunk_counts:
  !a b. MEM a ["r";"q";"t"] /\ MEM b ["r";"q";"t"] ==>
  LENGTH (phi_search_loop_chunk a b) = (if a = "r" \/ b = "r" then 6 else 2)
Proof
  rpt gen_tac >> strip_tac >> gvs[]
  >- EVAL_TAC >- EVAL_TAC >- EVAL_TAC >- EVAL_TAC
  >- EVAL_TAC >- EVAL_TAC >- EVAL_TAC >- EVAL_TAC >> EVAL_TAC
QED

Theorem phi_search_loop_chunk_outputs:
  !a b. MEM a ["r";"q";"t"] /\ MEM b ["r";"q";"t"] ==>
  EVERY (\fn. let g = FST (make_ssa_current_fn phi_search_loop_supply fn) in
    phi_search_exec_check g /\
    phi_search_exec_check (phi_search_slice ["entry";"head";"body";"exit"] g))
    (phi_search_loop_chunk a b)
Proof
  rpt gen_tac >> strip_tac >> gvs[]
  >- EVAL_TAC >- EVAL_TAC >- EVAL_TAC >- EVAL_TAC
  >- EVAL_TAC >- EVAL_TAC >- EVAL_TAC >- EVAL_TAC >> EVAL_TAC
QED

Theorem phi_search_loop_chunk_outputs_retpc:
  MEM a ["r";"q";"t"] /\ MEM b ["r";"q";"t"] ==>
  EVERY (\fn. retpc_shape_ok (FST (make_ssa_current_fn phi_search_loop_supply fn)))
    (phi_search_loop_chunk a b)
Proof
  strip_tac >> qspecl_then [`a`,`b`] mp_tac phi_search_loop_chunk_outputs >>
  simp[EVERY_MEM, LET_THM] >> disch_tac >> qx_gen_tac `fn` >> disch_tac >>
  `?ret sp. fn = phi_search_loop a b ret sp` by
    (qpat_x_assum `MEM fn _` mp_tac >>
     pure_rewrite_tac[phi_search_loop_chunk_def, MEM_FILTER] >> simp[] >> metis_tac[]) >>
  `phi_search_exec_check (FST (make_ssa_current_fn phi_search_loop_supply fn)) /\
   phi_search_exec_check (phi_search_slice ["entry";"head";"body";"exit"]
     (FST (make_ssa_current_fn phi_search_loop_supply fn)))` by metis_tac[] >>
  qpat_x_assum `fn = _` SUBST_ALL_TAC >>
  Cases_on `make_ssa_current_fn phi_search_loop_supply (phi_search_loop a b ret sp)` >>
  drule phi_search_loop_output_slice >> strip_tac >>
  irule phi_search_full_reachable_check_sound >> fs[]
QED

Definition phi_search_dead_def:
  phi_search_dead sr a b ret sp =
    let fn = phi_search_diamond sr a b ret sp in
    fn with fn_blocks :=
      (<| bb_label := "entry"; bb_instructions := [mk_inst 0 JMP [Label "left"] []] |>) ::
      TL fn.fn_blocks
End

Theorem phi_search_dead_reach:
  fn_reachable (phi_search_dead sr a b ret sp) l <=>
  MEM l ["entry";"left";"join"]
Proof
  `fn_entry_label (phi_search_dead sr a b ret sp) = SOME "entry"` by EVAL_TAC >>
  `fn_cfg_edge (phi_search_dead sr a b ret sp) "entry" "left" /\
   fn_cfg_edge (phi_search_dead sr a b ret sp) "left" "join"` by
    (Cases_on `sr` >> Cases_on `sp` >>
     simp[NoAsms, venomWfTheory.fn_cfg_edge_def, phi_search_dead_def,
          phi_search_diamond_def, mk_raw_function_def,
          GSYM AND_IMP_INTRO, DISJ_IMP_THM, LEFT_AND_OVER_OR,
          RIGHT_AND_OVER_OR, EXISTS_OR_THM] >> EVAL_TAC) >>
  eq_tac
  >- (simp[venomWfTheory.fn_reachable_def] >> strip_tac >>
      `!x y. RTC (fn_cfg_edge (phi_search_dead sr a b ret sp)) x y ==>
        MEM x ["entry";"left";"join"] ==> MEM y ["entry";"left";"join"]` suffices_by
        (disch_then (qspecl_then [`"entry"`,`l`] mp_tac) >> simp[]) >>
      ho_match_mp_tac relationTheory.RTC_INDUCT >> simp[] >> rpt strip_tac >>
      qpat_x_assum `fn_cfg_edge _ _ _` mp_tac >>
      Cases_on `sr` >> Cases_on `sp` >>
      simp[venomWfTheory.fn_cfg_edge_def, phi_search_dead_def,
        phi_search_diamond_def, mk_raw_function_def, mk_inst_def,
        GSYM AND_IMP_INTRO, DISJ_IMP_THM, LEFT_AND_OVER_OR,
        RIGHT_AND_OVER_OR, EXISTS_OR_THM] >> EVAL_TAC >> metis_tac[]) >>
  strip_tac >> simp[venomWfTheory.fn_reachable_def] >>
  gvs[] >> metis_tac[relationTheory.RTC_RULES]
QED

Theorem phi_search_dead_slice:
  reachable_fn (phi_search_dead sr a b ret sp) =
  phi_search_slice ["entry";"left";"join"] (phi_search_dead sr a b ret sp)
Proof
  irule phi_search_slice_sound >> simp[phi_search_dead_reach]
QED

Theorem phi_search_dead_shape:
  phi_search_exec_check (phi_search_dead sr a b ret sp) /\
  phi_search_exec_check (phi_search_slice ["entry";"left";"join"]
    (phi_search_dead sr a b ret sp)) ==>
  o1_fn_shape (mk_venom_context [phi_search_dead sr a b ret sp] NONE)
    (phi_search_dead sr a b ret sp)
Proof
  strip_tac >>
  `retpc_shape_ok (phi_search_dead sr a b ret sp)` by
    (irule phi_search_full_reachable_check_sound >> simp[phi_search_dead_slice]) >>
  rewrite_tac[o1_fn_shape_def, fn_shape_ok_def] >>
  asm_rewrite_tac[] >> Cases_on `sr` >> Cases_on `sp` >> EVAL_TAC >>
  simp[GSYM AND_IMP_INTRO, DISJ_IMP_THM, FORALL_AND_THM, APPEND_EQ_CONS]
QED

Theorem phi_search_dead_output_slice:
  make_ssa_current_fn s (phi_search_dead sr a b ret sp) = (g,s') ==>
  reachable_fn g = phi_search_slice ["entry";"left";"join"] g
Proof
  strip_tac >>
  `ALL_DISTINCT (MAP basic_block_bb_label (phi_search_dead sr a b ret sp).fn_blocks)` by
    simp[phi_search_dead_def, phi_search_diamond_def, mk_raw_function_def] >>
  drule_all make_ssa_current_fn_reachable >> strip_tac >>
  irule phi_search_slice_sound >> simp[phi_search_dead_reach]
QED

Definition phi_search_dead_chunk_def:
  phi_search_dead_chunk sr a b = FILTER (\fn. phi_search_exec_check fn /\
      phi_search_exec_check (phi_search_slice ["entry";"left";"join"] fn))
    (FLAT (MAP (\ret. MAP (\sp. phi_search_dead sr a b ret sp) [T;F]) ["r";"q";"t"]))
End

Theorem phi_search_dead_chunk_inputs:
  EVERY (\fn. o1_fn_shape (mk_venom_context [fn] NONE) fn /\
    ir_supply_inst_ok phi_search_supply) (phi_search_dead_chunk sr a b)
Proof
  pure_rewrite_tac[phi_search_dead_chunk_def, EVERY_MEM] >>
  gen_tac >> pure_rewrite_tac[MEM_FILTER] >> BETA_TAC >> strip_tac >> BETA_TAC >> conj_tac
  >- (qpat_x_assum `MEM e _` mp_tac >> simp[] >> rpt strip_tac >> gvs[] >>
      irule phi_search_dead_shape >> simp[]) >> simp[phi_search_supply_ok]
QED

Theorem phi_search_dead_chunk_counts:
  !sr a b. MEM sr [T;F] /\ MEM a ["r";"q";"t"] /\ MEM b ["r";"q";"t"] ==>
  LENGTH (phi_search_dead_chunk sr a b) =
    (if sr then 0 else if a = "r" then 6 else 2)
Proof
  rpt gen_tac >> strip_tac >> gvs[] >> Cases_on `sr`
  >- EVAL_TAC >- EVAL_TAC >- EVAL_TAC >- EVAL_TAC
  >- EVAL_TAC >- EVAL_TAC >- EVAL_TAC >- EVAL_TAC
  >- EVAL_TAC >- EVAL_TAC >- EVAL_TAC >- EVAL_TAC
  >- EVAL_TAC >- EVAL_TAC >- EVAL_TAC >- EVAL_TAC
  >- EVAL_TAC >> EVAL_TAC
QED

Theorem phi_search_dead_chunk_outputs:
  !sr a b. MEM sr [T;F] /\ MEM a ["r";"q";"t"] /\ MEM b ["r";"q";"t"] ==>
  EVERY (\fn. let g = FST (make_ssa_current_fn phi_search_supply fn) in
    phi_search_exec_check g /\
    phi_search_exec_check (phi_search_slice ["entry";"left";"join"] g))
    (phi_search_dead_chunk sr a b)
Proof
  rpt gen_tac >> strip_tac >> gvs[] >> Cases_on `sr`
  >- EVAL_TAC >- EVAL_TAC >- EVAL_TAC >- EVAL_TAC
  >- EVAL_TAC >- EVAL_TAC >- EVAL_TAC >- EVAL_TAC
  >- EVAL_TAC >- EVAL_TAC >- EVAL_TAC >- EVAL_TAC
  >- EVAL_TAC >- EVAL_TAC >- EVAL_TAC >- EVAL_TAC
  >- EVAL_TAC >> EVAL_TAC
QED

Theorem phi_search_dead_chunk_outputs_retpc:
  MEM sr [T;F] /\ MEM a ["r";"q";"t"] /\ MEM b ["r";"q";"t"] ==>
  EVERY (\fn. retpc_shape_ok (FST (make_ssa_current_fn phi_search_supply fn)))
    (phi_search_dead_chunk sr a b)
Proof
  strip_tac >> qspecl_then [`sr`,`a`,`b`] mp_tac phi_search_dead_chunk_outputs >>
  simp[EVERY_MEM, LET_THM] >> disch_tac >> qx_gen_tac `fn` >> disch_tac >>
  `?ret sp. fn = phi_search_dead sr a b ret sp` by
    (qpat_x_assum `MEM fn _` mp_tac >>
     pure_rewrite_tac[phi_search_dead_chunk_def, MEM_FILTER] >> simp[] >> metis_tac[]) >>
  `phi_search_exec_check (FST (make_ssa_current_fn phi_search_supply fn)) /\
   phi_search_exec_check (phi_search_slice ["entry";"left";"join"]
     (FST (make_ssa_current_fn phi_search_supply fn)))` by metis_tac[] >>
  qpat_x_assum `fn = _` SUBST_ALL_TAC >>
  Cases_on `make_ssa_current_fn phi_search_supply (phi_search_dead sr a b ret sp)` >>
  drule phi_search_dead_output_slice >> strip_tac >>
  irule phi_search_full_reachable_check_sound >> fs[]
QED

Definition phi_search_root_def:
  phi_search_root = mk_raw_function "root" [
    <| bb_label := "root"; bb_instructions := [mk_inst 99 STOP [] []] |>]
End

Definition phi_search_context_def:
  phi_search_context fn = mk_venom_context [phi_search_root;fn] (SOME "root")
End

Theorem phi_search_context_shape:
  fn.fn_name = "entry" /\
  o1_fn_shape (mk_venom_context [fn] NONE) fn ==>
  o1_ctx_shape (phi_search_context fn)
Proof
  strip_tac >>
  `o1_fn_shape (phi_search_context fn) fn` by
    (fs[o1_fn_shape_def, phi_search_context_def, mk_venom_context_def,
        fn_invoke_ok_def, ctx_fn_names_def] >> metis_tac[]) >>
  simp[o1_ctx_shape_def, phi_search_context_def, mk_venom_context_def] >>
  conj_tac
  >- (simp[venomWfTheory.ctx_wf_def, venomWfTheory.ctx_distinct_fn_names_def,
           venomWfTheory.ctx_has_entry_def, ctx_fn_names_def, phi_search_root_def,
           mk_raw_function_def, mk_venom_context_def]) >>
  conj_tac >- (
    `reachable_fn phi_search_root = phi_search_root` by
      (irule reachable_fn_single_block >> simp[phi_search_root_def, mk_raw_function_def,
         mk_inst_def]) >>
    rewrite_tac[o1_fn_shape_def, fn_shape_ok_def, retpc_shape_ok_def, opaque_use_ok_def] >>
    asm_rewrite_tac[] >> EVAL_TAC >>
    simp[GSYM AND_IMP_INTRO, DISJ_IMP_THM, FORALL_AND_THM]) >>
  fs[phi_search_context_def, mk_venom_context_def]
QED

Theorem phi_search_contexts_sound[local]:
  EVERY (\fn. o1_fn_shape (mk_venom_context [fn] NONE) fn /\ ir_supply_inst_ok s) fns /\
  EVERY (\fn. fn.fn_name = "entry") fns ==>
  EVERY (\fn. o1_ctx_shape (phi_search_context fn) /\ ir_supply_inst_ok s) fns
Proof
  simp[EVERY_MEM] >> metis_tac[phi_search_context_shape]
QED

Theorem phi_search_diamond_contexts:
  EVERY (\fn. o1_ctx_shape (phi_search_context fn) /\ ir_supply_inst_ok phi_search_supply)
    (phi_search_good_chunk sr a b)
Proof
  irule phi_search_contexts_sound >> reverse conj_tac
  >- (pure_rewrite_tac[phi_search_good_chunk_def, EVERY_MEM, MEM_FILTER] >>
      BETA_TAC >> rpt strip_tac >>
      qpat_x_assum `MEM e _` mp_tac >> simp[phi_search_chunk_def] >>
      rpt strip_tac >> gvs[] >> EVAL_TAC) >>
  irule phi_search_chunk_inputs
QED

Theorem phi_search_loop_contexts:
  EVERY (\fn. o1_ctx_shape (phi_search_context fn) /\ ir_supply_inst_ok phi_search_loop_supply)
    (phi_search_loop_chunk a b)
Proof
  irule phi_search_contexts_sound >> reverse conj_tac
  >- (pure_rewrite_tac[phi_search_loop_chunk_def, EVERY_MEM, MEM_FILTER] >>
      BETA_TAC >> rpt strip_tac >>
      qpat_x_assum `MEM e _` mp_tac >> simp[] >>
      rpt strip_tac >> gvs[] >> EVAL_TAC) >>
  irule phi_search_loop_chunk_inputs
QED

Theorem phi_search_dead_contexts:
  EVERY (\fn. o1_ctx_shape (phi_search_context fn) /\ ir_supply_inst_ok phi_search_supply)
    (phi_search_dead_chunk sr a b)
Proof
  irule phi_search_contexts_sound >> reverse conj_tac
  >- (pure_rewrite_tac[phi_search_dead_chunk_def, EVERY_MEM, MEM_FILTER] >>
      BETA_TAC >> rpt strip_tac >>
      qpat_x_assum `MEM e _` mp_tac >> simp[] >>
      rpt strip_tac >> gvs[] >> EVAL_TAC) >>
  irule phi_search_dead_chunk_inputs
QED
