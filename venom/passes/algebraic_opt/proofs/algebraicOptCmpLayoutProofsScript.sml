Theory algebraicOptCmpLayoutProofs
Ancestors
  algebraicOptCmpCoherenceProofs algebraicOptCmpChunkProofs
  algebraicOptCmpPhiProofs algebraicOptCmpScanProofs algebraicOptDefs
  venomExecSemantics venomInst list passSharedDefs irSupply dfgDefs

Theorem ao_cmp_chunk_nonempty:
  ao_cmp_flip_apply_inst fs rs ns inst <> []
Proof
  simp[ao_cmp_flip_apply_inst_def] >>
  Cases_on `ALOOKUP fs inst.inst_id` >> simp[]
  >- (Cases_on `MEM inst.inst_id rs` >> simp[] >>
      Cases_on `ALOOKUP ns inst.inst_id` >> simp[] >>
      PairCases_on `x` >> simp[]) >>
  PairCases_on `x` >> simp[]
QED

Theorem ao_cmp_expand_drop:
  !xs n C. n <= LENGTH xs ==>
    DROP (LENGTH (FLAT (MAP C (TAKE n xs)))) (FLAT (MAP C xs)) =
    FLAT (MAP C (DROP n xs))
Proof
  Induct >> Cases_on `n` >> simp[] >> rpt strip_tac >>
  simp[DROP_APPEND]
QED

Theorem ao_cmp_expand_next:
  !xs n C. n < LENGTH xs ==>
    DROP (LENGTH (FLAT (MAP C (TAKE n xs)))) (FLAT (MAP C xs)) =
    C (EL n xs) ++ FLAT (MAP C (DROP (SUC n) xs))
Proof
  Induct >> Cases_on `n` >> simp[] >> rpt strip_tac >>
  simp[DROP_APPEND]
QED

Theorem ao_cmp_phi_chunk:
  ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn)) /\
  MEM inst (fn_insts fn) /\
  ao_cmp_flip_scan (dfg_build_function fn) (fn_insts fn) = (fs,rs,ins) /\
  ir_supply_inst_ok supply /\
  ao_name_inserts_supply supply ins = (ns,supply') /\
  inst.inst_opcode = PHI ==>
  ao_cmp_flip_apply_inst fs rs ns inst = [inst]
Proof
  strip_tac >> irule ao_cmp_untouched_apply >>
  `ALOOKUP fs inst.inst_id = NONE` by
    (Cases_on `ALOOKUP fs inst.inst_id` >> simp[] >>
     drule_all ao_cmp_flip_lookup_cert >>
     simp[ao_cmp_flip_cert_def, ao_cmp_source_def, is_comparator_def]) >>
  `~MEM inst.inst_id rs` by
    (strip_tac >> drule_all ao_cmp_remove_lookup_cert >> simp[]) >>
  simp[] >> Cases_on `ALOOKUP ns inst.inst_id` >> simp[] >>
  PairCases_on `x` >> drule_all ao_cmp_insert_apply >> simp[]
QED

Theorem ao_cmp_nonphi_chunk:
  ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn)) /\
  MEM inst (fn_insts fn) /\
  ao_cmp_flip_scan (dfg_build_function fn) (fn_insts fn) = (fs,rs,ins) /\
  inst.inst_opcode <> PHI ==>
  EVERY (\j. j.inst_opcode <> PHI) (ao_cmp_flip_apply_inst fs rs ns inst)
Proof
  strip_tac >> Cases_on `ALOOKUP fs inst.inst_id`
  >- (simp[ao_cmp_flip_apply_inst_def] >>
      Cases_on `MEM inst.inst_id rs` >> simp[] >>
      Cases_on `ALOOKUP ns inst.inst_id` >> simp[] >>
      PairCases_on `x` >> simp[]) >>
  PairCases_on `x` >> drule_all ao_cmp_flip_lookup_cert >>
  simp[ao_cmp_flip_cert_def, ao_cmp_source_def] >> strip_tac >>
  gvs[ao_cmp_flip_apply_inst_def, is_comparator_def, flip_comparison_opcode_def]
QED

Theorem ao_cmp_expand_phi_prefix:
  !xs C.
    (!i. MEM i xs ==>
      C i <> [] /\
      (i.inst_opcode = PHI ==> C i = [i]) /\
      (i.inst_opcode <> PHI ==> EVERY (\j. j.inst_opcode <> PHI) (C i))) ==>
    phi_prefix_length (FLAT (MAP C xs)) = phi_prefix_length xs /\
    TAKE (phi_prefix_length xs) (FLAT (MAP C xs)) =
      TAKE (phi_prefix_length xs) xs /\
    (!s. eval_phis s (FLAT (MAP C xs)) = eval_phis s xs)
Proof
  Induct >> simp[phi_prefix_length_def, eval_phis_def] >>
  rpt gen_tac >> strip_tac >>
  `phi_prefix_length (FLAT (MAP C xs)) = phi_prefix_length xs /\
   TAKE (phi_prefix_length xs) (FLAT (MAP C xs)) =
     TAKE (phi_prefix_length xs) xs /\
   (!s. eval_phis s (FLAT (MAP C xs)) = eval_phis s xs)` by
    (first_x_assum irule >> metis_tac[MEM]) >>
  Cases_on `h.inst_opcode = PHI`
  >- (`C h = [h]` by metis_tac[MEM] >>
      simp[phi_prefix_length_def, eval_phis_def]) >>
  `C h <> [] /\ EVERY (\j. j.inst_opcode <> PHI) (C h)` by
    metis_tac[MEM] >>
  Cases_on `C h` >> gvs[] >>
  simp[phi_prefix_length_def, eval_phis_def]
QED

Theorem ao_cmp_expansion_phi_layout:
  ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn)) /\
  (!i. MEM i xs ==> MEM i (fn_insts fn)) /\
  ao_cmp_flip_scan (dfg_build_function fn) (fn_insts fn) = (fs,rs,ins) /\
  ir_supply_inst_ok supply /\
  ao_name_inserts_supply supply ins = (ns,supply') ==>
  phi_prefix_length (FLAT (MAP (ao_cmp_flip_apply_inst fs rs ns) xs)) =
    phi_prefix_length xs /\
  TAKE (phi_prefix_length xs) (FLAT (MAP (ao_cmp_flip_apply_inst fs rs ns) xs)) =
    TAKE (phi_prefix_length xs) xs /\
  (!s. eval_phis s (FLAT (MAP (ao_cmp_flip_apply_inst fs rs ns) xs)) =
    eval_phis s xs)
Proof
  strip_tac >> irule ao_cmp_expand_phi_prefix >> rpt strip_tac
  >- metis_tac[ao_cmp_chunk_nonempty]
  >- (irule ao_cmp_phi_chunk >> metis_tac[])
  >- (irule ao_cmp_nonphi_chunk >> metis_tac[])
QED

Theorem ao_cmp_operand_vars_eq:
  !ops. dfgDefs$operand_vars ops = venomInst$operand_vars ops
Proof
  Induct
  >- simp[dfgDefsTheory.operand_vars_def, venomInstTheory.operand_vars_def] >>
  Cases_on `h` >>
  simp[dfgDefsTheory.operand_vars_def, dfgDefsTheory.operand_var_def,
       venomInstTheory.operand_vars_def, venomInstTheory.operand_var_def]
QED

Theorem ao_cmp_phi_separation:
  !fn supply supply' fs inst flipped ignored.
  ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) (fn_insts fn))) /\
  ir_supply_covers_fn supply fn /\
  flipped = ao_cmp_flipped (dfg_build_function fn) (fn_insts fn) fs /\
  ignored = set supply'.irs_used_vars DIFF set supply.irs_used_vars /\
  MEM inst (fn_insts fn) /\ inst.inst_opcode = PHI ==>
  (!v. MEM (Var v) inst.inst_operands ==> v NOTIN ignored /\ v NOTIN flipped) /\
  (!v. MEM v inst.inst_outputs ==> v NOTIN flipped)
Proof
  rpt gen_tac >> strip_tac >>
  `DISJOINT (set (operand_vars inst.inst_operands)) flipped` by
    (gvs[] >> irule ao_cmp_flipped_nonconsumer_reads >> simp[]) >>
  `DISJOINT (set inst.inst_outputs) flipped` by
    (gvs[] >> irule ao_cmp_flipped_noncomparator_writes >>
     simp[is_comparator_def]) >>
  `DISJOINT (set (inst_ir_vars inst)) ignored` by
    (gvs[] >> irule ao_cmp_ignored_inst_vars >> metis_tac[]) >>
  gvs[ao_cmp_operand_vars_eq, pred_setTheory.DISJOINT_DEF, pred_setTheory.EXTENSION,
      inst_ir_vars_def, inst_uses_def, MEM_APPEND,
      MEM_operand_vars_eq_Var] >>
  metis_tac[]
QED

(* Atomic block entry: the suffix runner starts after the same PHI prefix.
   All PHI operands are read from the entry snapshot by eval_phis. *)
Theorem ao_cmp_expanded_phi_entry:
  !fn supply supply' fs rs ins ns xs ys ignored flipped s t.
  ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn)) /\
  ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) (fn_insts fn))) /\
  (!i. MEM i xs ==> MEM i (fn_insts fn)) /\
  ir_supply_covers_fn supply fn /\ ir_supply_inst_ok supply /\
  ao_cmp_flip_scan (dfg_build_function fn) (fn_insts fn) = (fs,rs,ins) /\
  ao_name_inserts_supply supply ins = (ns,supply') /\
  ys = FLAT (MAP (ao_cmp_flip_apply_inst fs rs ns) xs) /\
  flipped = ao_cmp_flipped (dfg_build_function fn) (fn_insts fn) fs /\
  ignored = set supply'.irs_used_vars DIFF set supply.irs_used_vars /\
  ao_cmp_state_rel ignored flipped s t /\
  s.vs_prev_bb = t.vs_prev_bb /\ s.vs_current_bb = t.vs_current_bb ==>
  phi_prefix_length ys = phi_prefix_length xs /\
  ((?e. eval_phis s xs = Error e /\ eval_phis t ys = Error e) \/
   (?u v. eval_phis s xs = OK u /\ eval_phis t ys = OK v /\
     ao_cmp_state_rel ignored flipped
       (u with vs_inst_idx := phi_prefix_length xs)
       (v with vs_inst_idx := phi_prefix_length ys) /\
     u.vs_prev_bb = v.vs_prev_bb /\ u.vs_current_bb = v.vs_current_bb))
Proof
  rpt gen_tac >> strip_tac >>
  `phi_prefix_length ys = phi_prefix_length xs /\
   (!z. eval_phis z ys = eval_phis z xs)` by
    (gvs[] >> drule_all ao_cmp_expansion_phi_layout >> simp[]) >>
  `!inst. MEM inst xs /\ inst.inst_opcode = PHI ==>
    (!v. MEM (Var v) inst.inst_operands ==> v NOTIN ignored /\ v NOTIN flipped) /\
    (!v. MEM v inst.inst_outputs ==> v NOTIN flipped)` by
    (gen_tac >> strip_tac >> irule ao_cmp_phi_separation >> metis_tac[]) >>
  simp[ao_cmp_state_rel_indices] >>
  irule ao_cmp_eval_phis >> gvs[] >> first_assum ACCEPT_TAC
QED

Theorem ao_cmp_expand_take_phis:
  !xs C. (!i. MEM i xs /\ i.inst_opcode = PHI ==> C i = [i]) ==>
    FLAT (MAP C (TAKE (phi_prefix_length xs) xs)) =
      TAKE (phi_prefix_length xs) xs /\
    phi_prefix_length xs <= LENGTH xs
Proof
  Induct >> simp[phi_prefix_length_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `h.inst_opcode = PHI` >> simp[phi_prefix_length_def] >>
  `C h = [h]` by metis_tac[MEM] >>
  `FLAT (MAP C (TAKE (phi_prefix_length xs) xs)) =
    TAKE (phi_prefix_length xs) xs /\ phi_prefix_length xs <= LENGTH xs` by
    (first_x_assum irule >> metis_tac[MEM]) >> simp[]
QED
