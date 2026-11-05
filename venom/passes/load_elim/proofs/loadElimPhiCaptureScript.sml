Theory loadElimPhiCapture
Ancestors
  loadElimDefs loadElimOperationalHistory venomExecSemantics venomExecProofs
  venomState list pair finite_map

Theorem le_resolve_phi_pairs:
  !pairs pred v. ALL_DISTINCT (MAP FST pairs) /\ MEM (pred,v) pairs ==>
  resolve_phi pred (mk_phi_ops_from_pairs pairs) = SOME (Var v)
Proof
  Induct_on `pairs` >- simp[] >>
  gen_tac >> PairCases_on `h` >>
  simp[mk_phi_ops_from_pairs_def, resolve_phi_def] >>
  rpt strip_tac >> gvs[] >>
  Cases_on `h0 = pred` >> gvs[MEM_MAP] >> metis_tac[FST]
QED

Theorem le_generated_phi_eval:
  ALL_DISTINCT (MAP FST pairs) /\ MEM (pred,v) pairs /\
  s.vs_prev_bb = SOME pred /\ lookup_var v s = SOME w /\
  inst.inst_operands = mk_phi_ops_from_pairs pairs /\ inst.inst_outputs = [out] ==>
  eval_one_phi s inst = SOME (out,w)
Proof
  strip_tac >> drule_all le_resolve_phi_pairs >>
  simp[eval_one_phi_def, eval_operand_def]
QED

Theorem le_generated_phi_capture:
  ALL_DISTINCT (MAP FST pairs) /\ MEM (pred,v) pairs /\
  s.vs_prev_bb = SOME pred /\ lookup_var v s = SOME w /\
  inst.inst_operands = mk_phi_ops_from_pairs pairs /\ inst.inst_outputs = [out] /\
  le_phi_prefix insts = pre ++ inst::post /\
  (!j. MEM j pre ==> ~MEM out j.inst_outputs) /\
  eval_phis s insts = OK t ==>
  lookup_var out t = SOME w
Proof
  strip_tac >> drule_all le_generated_phi_eval >> strip_tac >>
  irule le_eval_phis_selected >>
  qexistsl [`inst`, `insts`, `post`, `pre`, `s`] >> simp[] >>
  metis_tac[eval_one_phi_output_mem]
QED

Theorem le_phi_prefix_append:
  !pre rest. EVERY (\i. i.inst_opcode = PHI) pre ==>
  le_phi_prefix (pre ++ rest) = pre ++ le_phi_prefix rest
Proof
  Induct_on `pre` >> simp[le_phi_prefix_def]
QED

Theorem le_phi_action_capture:
  MEM pa actions /\ pa.pa_join_lbl = lbl /\
  ALL_DISTINCT (MAP (\a. a.pa_phi_out) actions) /\
  pa.pa_phi_ops = mk_phi_ops_from_pairs pairs /\
  ALL_DISTINCT (MAP FST pairs) /\ MEM (pred,v) pairs /\
  s.vs_prev_bb = SOME pred /\ lookup_var v s = SOME w /\
  eval_phis s (phis_for_block actions lbl ++ rest) = OK t ==>
  lookup_var pa.pa_phi_out t = SOME w
Proof
  strip_tac >>
  qpat_x_assum `MEM pa actions` mp_tac >>
  simp[MEM_SPLIT] >> strip_tac >>
  qpat_x_assum `actions = _` SUBST_ALL_TAC >>
  irule le_generated_phi_capture >>
  qexistsl [`<|inst_id := pa.pa_phi_id; inst_opcode := PHI;
               inst_operands := pa.pa_phi_ops; inst_outputs := [pa.pa_phi_out]|>`,
            `phis_for_block (l1 ++ pa::l2) lbl ++ rest`, `pairs`,
            `le_phi_prefix (phis_for_block l2 lbl ++ rest)`,
            `phis_for_block l1 lbl`, `pred`, `s`, `v`] >>
  simp[phis_for_block_def, FILTER_APPEND_DISTRIB, le_phi_prefix_append,
       EVERY_MAP, EVERY_FILTER, le_phi_prefix_def] >>
  gvs[ALL_DISTINCT_APPEND, MEM_MAP, MEM_FILTER,
      phis_for_block_def, FILTER_APPEND_DISTRIB] >>
  conj_tac
  >- (rpt strip_tac >> gvs[] >> metis_tac[]) >>
  qpat_x_assum `eval_phis _ _ = OK _` mp_tac >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >> simp[]
QED

(* The original PHI writes x, but the prepended generated PHI captures old x. *)
Theorem le_phi_capture_overwritten_incoming:
  s.vs_prev_bb = SOME "p" /\ lookup_var "x" s = SOME w /\
  lookup_var "y" s = SOME z ==>
  eval_phis s
    [<|inst_id := 0; inst_opcode := PHI;
       inst_operands := mk_phi_ops_from_pairs [("p","x")];
       inst_outputs := ["$le_phi_probe"]|>;
     <|inst_id := 1; inst_opcode := PHI;
       inst_operands := [Label "p"; Var "y"];
       inst_outputs := ["x"]|>] =
  OK (update_var "$le_phi_probe" w (update_var "x" z s)) /\
  lookup_var "$le_phi_probe" (update_var "$le_phi_probe" w (update_var "x" z s)) = SOME w /\
  lookup_var "x" (update_var "$le_phi_probe" w (update_var "x" z s)) = SOME z
Proof
  strip_tac >>
  simp[eval_phis_def, eval_one_phi_def, resolve_phi_def,
       mk_phi_ops_from_pairs_def, eval_operand_def,
       lookup_var_def, update_var_def, FLOOKUP_UPDATE]
QED

Theorem le_lattice_single_var:
  lattice_single_var ll key = SOME v <=>
  FLOOKUP (unwrap_load_lattice ll) key = SOME [Var v]
Proof
  simp[lattice_single_var_def, AllCaseEqs()]
QED

Theorem le_compute_phi_action_certificate:
  compute_phi_action m cfg result key lbl inst = SOME pa ==>
  pa.pa_join_lbl = find_join_block cfg {} lbl /\
  ?pairs. pa.pa_phi_ops = mk_phi_ops_from_pairs pairs /\
    MAP FST pairs = cfg_preds_of cfg pa.pa_join_lbl /\
    EVERY (\pv. FLOOKUP
      (unwrap_load_lattice (df_boundary NONE result (FST pv))) key =
      SOME [Var (SND pv)]) pairs
Proof
  simp[compute_phi_action_def] >> strip_tac >> gvs[] >>
  qexists `MAP (\p. (p, THE (lattice_single_var
    (df_boundary NONE result p) key)))
    (cfg_preds_of cfg (find_join_block cfg {} lbl))` >>
  simp[MAP_MAP_o, combinTheory.o_DEF, EVERY_MAP] >>
  gvs[EVERY_MAP, EVERY_MEM] >> rpt strip_tac >>
  first_x_assum drule >>
  Cases_on `lattice_single_var (df_boundary NONE result p) key` >>
  simp[] >> metis_tac[le_lattice_single_var]
QED

Theorem le_compute_phi_action_selected:
  compute_phi_action m cfg result key lbl inst = SOME pa /\
  MEM pred (cfg_preds_of cfg pa.pa_join_lbl) ==>
  ?pairs v. pa.pa_phi_ops = mk_phi_ops_from_pairs pairs /\
    MAP FST pairs = cfg_preds_of cfg pa.pa_join_lbl /\
    MEM (pred,v) pairs /\
    FLOOKUP (unwrap_load_lattice (df_boundary NONE result pred)) key =
      SOME [Var v]
Proof
  strip_tac >> drule le_compute_phi_action_certificate >> strip_tac >>
  `?v. MEM (pred,v) pairs` by
    (`MEM pred (MAP FST pairs)` by metis_tac[] >>
     fs[MEM_MAP] >> metis_tac[pairTheory.PAIR]) >>
  qexistsl [`pairs`, `v`] >> simp[] >>
  gvs[EVERY_MEM] >> first_x_assum drule >> simp[]
QED

Theorem le_compute_phi_action_capture:
  compute_phi_action m cfg result key lbl inst = SOME pa /\
  MEM pa actions /\
  ALL_DISTINCT (MAP (\a. a.pa_phi_out) actions) /\
  ALL_DISTINCT (cfg_preds_of cfg pa.pa_join_lbl) /\
  MEM pred (cfg_preds_of cfg pa.pa_join_lbl) /\
  s.vs_prev_bb = SOME pred /\
  (!v. FLOOKUP (unwrap_load_lattice (df_boundary NONE result pred)) key =
       SOME [Var v] ==> lookup_var v s = SOME w) /\
  eval_phis s (phis_for_block actions pa.pa_join_lbl ++ rest) = OK t ==>
  lookup_var pa.pa_phi_out t = SOME w
Proof
  strip_tac >> drule_all le_compute_phi_action_selected >> strip_tac >>
  irule le_phi_action_capture >>
  qexistsl [`actions`, `pa.pa_join_lbl`, `pairs`, `pred`, `rest`, `s`, `v`] >>
  simp[]
QED
