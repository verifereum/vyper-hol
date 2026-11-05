Theory basePtrConvergenceTransfer
Ancestors
  basePtrConvergenceOrder basePtrDefs basePtrProofs venomInst
  finite_map list pred_set

(* An enabled non-PHI write, including writes whose value is unchanged.
   No-op arithmetic branches are deliberately not constructors. *)
Inductive bp_write:
[~alloca:]
  (!i r out. inst_output i = SOME out /\ i.inst_opcode = ALLOCA ==>
     bp_write i r [ptr_from_alloca i])
[~assign:]
  (!i r out src. inst_output i = SOME out /\ i.inst_opcode = ASSIGN /\
     i.inst_operands = [Var src] ==>
     bp_write i r (bp_get_ptrs r src))
[~add_lit:]
  (!i r out src n. inst_output i = SOME out /\ i.inst_opcode = ADD /\
     (i.inst_operands = [Var src; Lit n] \/ i.inst_operands = [Lit n; Var src]) /\
     bp_get_ptrs r src <> [] ==>
     bp_write i r (MAP (\p. offset_by p (SOME (w2n n))) (bp_get_ptrs r src)))
[~add_left:]
  (!i r out x y. inst_output i = SOME out /\ i.inst_opcode = ADD /\
     i.inst_operands = [Var x; Var y] /\
     bp_get_ptrs r x <> [] /\ bp_get_ptrs r y = [] ==>
     bp_write i r (MAP (\p. offset_by p NONE) (bp_get_ptrs r x)))
[~add_right:]
  (!i r out x y. inst_output i = SOME out /\ i.inst_opcode = ADD /\
     i.inst_operands = [Var x; Var y] /\
     bp_get_ptrs r x = [] /\ bp_get_ptrs r y <> [] ==>
     bp_write i r (MAP (\p. offset_by p NONE) (bp_get_ptrs r y)))
[~sub_lit:]
  (!i r out src n. inst_output i = SOME out /\ i.inst_opcode = SUB /\
     i.inst_operands = [Var src; Lit n] /\ bp_get_ptrs r src <> [] ==>
     bp_write i r (MAP (\p. sub_offset_by p (SOME (w2n n))) (bp_get_ptrs r src)))
[~sub_var:]
  (!i r out x y. inst_output i = SOME out /\ i.inst_opcode = SUB /\
     i.inst_operands = [Var x; Var y] /\
     bp_get_ptrs r x <> [] /\ bp_get_ptrs r y = [] ==>
     bp_write i r (MAP (\p. offset_by p NONE) (bp_get_ptrs r x)))
End

Theorem bp_write_transfer:
  !i r ps. bp_write i r ps ==>
  !out. inst_output i = SOME out ==>
    SND (bp_handle_inst r i) = r |+ (out,ps)
Proof
  ho_match_mp_tac bp_write_ind >>
  rpt strip_tac >> gvs[bp_handle_inst_def]
QED

Theorem bp_list_le_nil_right:
  !xs. bp_list_le xs [] ==> xs = []
Proof
  simp[Once bp_list_le_cases]
QED

Theorem bp_map_le_nonempty:
  bp_map_le r s /\ bp_get_ptrs r v <> [] ==> bp_get_ptrs s v <> []
Proof
  simp[bp_map_le_def] >> metis_tac[bp_list_le_nil_right]
QED

Theorem bp_write_compare:
  !i r ps. bp_write i r ps ==>
  !s qs. bp_write i s qs /\ bp_map_le r s ==> bp_list_le ps qs
Proof
  ho_match_mp_tac bp_write_ind >> rpt strip_tac >>
  qpat_x_assum `bp_write _ _ _` mp_tac >>
  simp[Once bp_write_cases] >> strip_tac >> gvs[] >>
  fs[bp_map_le_def] >>
  metis_tac[bp_list_le_offset, bp_list_le_sub_offset, bp_list_le_nil_right]
QED

(* A universe can repeat a writer, but cannot contain two different writers
   for the same output.  SSA will supply this interface for fn_I. *)
Definition bp_unique_writers_def:
  bp_unique_writers insts <=>
  !i j out. MEM i insts /\ MEM j insts /\ inst_output i = SOME out /\
            inst_output j = SOME out ==> i = j
End

Definition bp_history_def:
  bp_history insts r <=>
  !i out. MEM i insts /\ i.inst_opcode <> PHI /\ inst_output i = SOME out ==>
    bp_get_ptrs r out = [] \/
    ?s. bp_map_le s r /\ bp_write i s (bp_get_ptrs r out)
End

Theorem bp_history_empty[simp]:
  bp_history insts FEMPTY
Proof
  simp[bp_history_def, bp_get_ptrs_def]
QED

Theorem bp_transfer_nonphi_cases:
  i.inst_opcode <> PHI /\ inst_output i = SOME out ==>
  SND (bp_handle_inst r i) = r \/
  ?ps. bp_write i r ps /\ SND (bp_handle_inst r i) = r |+ (out,ps)
Proof
  strip_tac >> Cases_on `i.inst_opcode` >>
  gvs[bp_handle_inst_def] >>
  simp[Once bp_write_cases] >>
  (Cases_on `i.inst_operands` >- simp[] >>
   rename1 `i.inst_operands = a::args` >>
   Cases_on `args`
   >- (Cases_on `a` >> gvs[] >> metis_tac[]) >>
   rename1 `i.inst_operands = a::b::rest` >>
   Cases_on `rest`
   >- (Cases_on `a` >> Cases_on `b` >> gvs[] >>
       rpt IF_CASES_TAC >> gvs[] >> metis_tac[]) >>
   Cases_on `a` >> Cases_on `b` >> simp[])
QED

Theorem bp_handle_inst_growth:
  MEM i insts /\ bp_history insts r /\ bp_map_wf V A r ==>
  bp_map_le r (SND (bp_handle_inst r i))
Proof
  strip_tac >> Cases_on `inst_output i`
  >- simp[bp_handle_inst_def] >>
  rename1 `inst_output i = SOME out` >>
  Cases_on `i.inst_opcode = PHI`
  >- (simp[bp_handle_inst_def] >> IF_CASES_TAC >> simp[] >>
      irule bp_map_le_write >> irule bp_normalize_prefix_growth >>
      fs[bp_map_wf_def]) >>
  drule_all bp_transfer_nonphi_cases >>
  disch_then (qspec_then `r` strip_assume_tac) >- simp[] >>
  simp[] >> irule bp_map_le_write >>
  qpat_x_assum `bp_history _ _` mp_tac >> simp[bp_history_def] >>
  disch_then (qspec_then `i` mp_tac) >> simp[] >> strip_tac
  >- simp[bp_list_le_rules] >>
  drule_all bp_write_compare >> simp[]
QED

Theorem bp_handle_inst_history:
  MEM i insts /\ bp_unique_writers insts /\ bp_history insts r /\
  bp_map_wf V A r ==>
  bp_history insts (SND (bp_handle_inst r i))
Proof
  strip_tac >>
  `bp_map_le r (SND (bp_handle_inst r i))` by
    (irule bp_handle_inst_growth >> metis_tac[]) >>
  simp[bp_history_def] >> rpt strip_tac >> rename1 `MEM j insts` >>
  Cases_on `i = j`
  >- (gvs[] >> drule_all bp_transfer_nonphi_cases >>
  disch_then (qspec_then `r` strip_assume_tac)
      >- (fs[bp_history_def] >> metis_tac[]) >>
      gvs[bp_get_ptrs_update] >> disj2_tac >> qexists_tac `r` >> simp[]) >>
  `inst_output i <> SOME out` by
    (fs[bp_unique_writers_def] >> metis_tac[]) >>
  `bp_get_ptrs (SND (bp_handle_inst r i)) out = bp_get_ptrs r out` by
    (Cases_on `bp_handle_inst r i` >> simp[] >>
     drule_all bp_handle_inst_other_var_proof >> simp[]) >>
  simp[] >> fs[bp_history_def] >>
  first_x_assum (qspec_then `j` mp_tac) >> simp[] >> strip_tac >- simp[] >>
  disj2_tac >> qexists_tac `s` >>
  metis_tac[bp_map_le_trans]
QED

Theorem bp_offset_base[simp]:
  ptr_base (offset_by p d) = ptr_base p
Proof
  Cases_on `p` >> rename1 `Ptr a off` >> Cases_on `off` >> Cases_on `d` >>
  simp[offset_by_def, ptr_base_def]
QED

Theorem bp_sub_offset_base[simp]:
  ptr_base (sub_offset_by p d) = ptr_base p
Proof
  Cases_on `p` >> rename1 `Ptr a off` >> Cases_on `off` >> Cases_on `d` >>
  simp[sub_offset_by_def, ptr_base_def] >> IF_CASES_TAC >> simp[ptr_base_def]
QED

Theorem bp_write_wf_value:
  !i r ps. bp_write i r ps ==>
  !V A. bp_map_wf V A r /\ (i.inst_opcode = ALLOCA ==> Allocation i.inst_id IN A) ==>
    ALL_DISTINCT (MAP ptr_base ps) /\ set (MAP ptr_base ps) SUBSET A
Proof
  ho_match_mp_tac bp_write_ind >> rpt strip_tac >>
  gvs[bp_map_wf_def, MAP_MAP_o, combinTheory.o_DEF,
      ptr_from_alloca_def, ptr_base_def, SF ETA_ss]
QED

Theorem bp_map_wf_member:
  bp_map_wf V A r /\ MEM p (bp_get_ptrs r v) ==> ptr_base p IN A
Proof
  simp[bp_map_wf_def, SUBSET_DEF, MEM_MAP] >> metis_tac[]
QED

Theorem bp_handle_inst_wf:
  bp_map_wf V A r /\
  (!out. inst_output i = SOME out ==> out IN V) /\
  (i.inst_opcode = ALLOCA ==> Allocation i.inst_id IN A) ==>
  bp_map_wf V A (SND (bp_handle_inst r i))
Proof
  strip_tac >> Cases_on `inst_output i` >- simp[bp_handle_inst_def] >>
  rename1 `inst_output i = SOME out` >>
  Cases_on `i.inst_opcode = PHI`
  >- (simp[bp_handle_inst_def] >> IF_CASES_TAC >> simp[] >>
      irule bp_map_wf_update >> simp[bp_normalize_distinct_bases] >>
      simp[SUBSET_DEF, MEM_MAP] >> rpt strip_tac >> gvs[] >>
      drule MEM_bp_normalize >> strip_tac >>
      gvs[MEM_FLAT, MEM_MAP] >> metis_tac[bp_map_wf_member]) >>
  drule_all bp_transfer_nonphi_cases >>
  disch_then (qspec_then `r` strip_assume_tac) >- simp[] >>
  simp[] >> irule bp_map_wf_update >>
  drule_all bp_write_wf_value >> simp[]
QED
