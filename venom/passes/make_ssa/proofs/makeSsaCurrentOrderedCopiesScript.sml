Theory makeSsaCurrentOrderedCopies
Ancestors
  makeSsaCurrentCleanupRuntime venomExecSemantics venomState venomInst
  stateFrame finite_map list

Definition current_copy_schedule_def:
  (current_copy_schedule Q known [] = T) /\
  (current_copy_schedule Q known (i::rest) <=>
    (i.inst_opcode = NOP /\ i.inst_operands = [] /\ i.inst_outputs = [] /\
      current_copy_schedule Q known rest) \/
    (?src dst value. i.inst_opcode = ASSIGN /\ i.inst_operands = [Var src] /\
      i.inst_outputs = [dst] /\ MEM src known /\ Q src = SOME value /\
      Q dst = SOME value /\ current_copy_schedule Q (dst::known) rest))
End

Theorem current_copy_schedule_nil[simp]:
  current_copy_schedule Q known []
Proof
  simp[current_copy_schedule_def]
QED

Theorem current_copy_schedule_mono:
  !copies known larger. current_copy_schedule Q known copies /\
    (!n. MEM n known ==> MEM n larger) ==>
    current_copy_schedule Q larger copies
Proof
  Induct >> simp[current_copy_schedule_def] >> rpt strip_tac
  >- (disj1_tac >> simp[] >> metis_tac[]) >>
  disj2_tac >> qexistsl_tac [`src`, `dst`, `value`] >> simp[] >>
  first_x_assum irule >> qexists_tac `dst::known` >> simp[] >> metis_tac[]
QED

Theorem current_copy_schedule_cong:
  (!n. MEM n known <=> MEM n known') ==>
  (current_copy_schedule Q known copies <=> current_copy_schedule Q known' copies)
Proof
  metis_tac[current_copy_schedule_mono]
QED

Theorem current_copy_schedule_shape:
  !copies known. current_copy_schedule Q known copies ==>
    EVERY current_cleanup_shape copies
Proof
  Induct >> simp[current_copy_schedule_def, current_cleanup_shape_def] >>
  rpt strip_tac >> simp[current_cleanup_shape_def] >> metis_tac[]
QED

Theorem current_copy_schedule_run:
  !copies known st. current_copy_schedule Q known copies /\
    (!n. MEM n known ==> lookup_var n st = Q n) ==>
    ?ready. current_copies_run copies st = OK ready /\
      (!n. MEM n (known ++ FLAT (MAP (\i. i.inst_outputs) copies)) ==>
        lookup_var n ready = Q n)
Proof
  Induct >> simp[current_copy_schedule_def, current_copies_run_def] >>
  rpt strip_tac
  >- (first_x_assum (qspec_then `known` mp_tac) >>
      simp[] >> disch_then (qspec_then `st` mp_tac) >> simp[] >>
      strip_tac >> qexists_tac `ready` >> simp[current_cleanup_nop_step] >>
      metis_tac[]) >>
  `lookup_var src st = SOME value` by metis_tac[] >>
  `!n. MEM n (dst::known) ==> lookup_var n (update_var dst value st) = Q n` by
    (simp[lookup_var_def, update_var_def, FLOOKUP_UPDATE] >>
     rpt strip_tac >> Cases_on `n = dst` >> gvs[lookup_var_def]) >>
  qpat_x_assum `!known st. _` (qspecl_then
    [`dst::known`, `update_var dst value st`] mp_tac) >>
  simp[] >> strip_tac >> qexists_tac `ready` >>
  drule_all current_cleanup_assign_step >>
  disch_then (qspec_then `st` assume_tac) >> simp[] >>
  rpt strip_tac >> first_x_assum irule >> simp[] >> metis_tac[]
QED


Theorem current_copy_schedule_insert[local]:
  current_copy_schedule Q ((known ++ [dst]) ++ rest) copies =
  current_copy_schedule Q (dst::(known ++ rest)) copies
Proof
  irule current_copy_schedule_cong >> simp[] >> metis_tac[]
QED

Theorem current_copy_schedule_append:
  !prefix known. current_copy_schedule Q known (prefix ++ suffix) <=>
    current_copy_schedule Q known prefix /\
    current_copy_schedule Q (known ++ FLAT (MAP (\i. i.inst_outputs) prefix)) suffix
Proof
  Induct >> simp[current_copy_schedule_def] >> rpt gen_tac >>
  Cases_on `h.inst_opcode = NOP`
  >- (simp[] >> eq_tac >> rpt strip_tac >> gvs[]) >>
  Cases_on `h.inst_opcode = ASSIGN`
  >- (simp[] >> eq_tac >> rpt strip_tac >> gvs[current_copy_schedule_insert] >>
      metis_tac[]) >>
  simp[]
QED

Theorem current_copy_schedule_nop:
  i.inst_opcode = NOP /\ i.inst_operands = [] /\ i.inst_outputs = [] ==>
  (current_copy_schedule Q known (i::rest) <=> current_copy_schedule Q known rest)
Proof
  simp[current_copy_schedule_def]
QED

Theorem current_copy_schedule_assign:
  i.inst_opcode = ASSIGN /\ i.inst_operands = [Var src] /\ i.inst_outputs = [dst] ==>
  (current_copy_schedule Q known (i::rest) <=>
    MEM src known /\ (?value. Q src = SOME value /\ Q dst = SOME value) /\
    current_copy_schedule Q (dst::known) rest)
Proof
  simp[current_copy_schedule_def] >> metis_tac[]
QED

Theorem current_copy_schedule_frame:
  current_copy_schedule Q known copies /\ current_copies_run copies st = OK ready ==>
  execution_frame ready = execution_frame st
Proof
  metis_tac[current_copy_schedule_shape, current_copies_run_frame]
QED

Theorem current_copy_schedule_untouched:
  current_copy_schedule Q known copies /\ current_copies_run copies st = OK ready /\
  ~MEM v (FLAT (MAP (\i. i.inst_outputs) copies)) ==>
  lookup_var v ready = lookup_var v st
Proof
  strip_tac >>
  `EVERY current_cleanup_shape copies` by metis_tac[current_copy_schedule_shape] >>
  irule current_copies_run_untouched >> qexists_tac `copies` >> simp[] >>
  gvs[MEM_FLAT, MEM_MAP] >> metis_tac[]
QED

Theorem current_copy_schedule_prefix:
  current_copy_schedule Q known (prefix ++ suffix) /\
  (!n. MEM n known ==> lookup_var n st = Q n) ==>
  ?mid. current_copies_run prefix st = OK mid /\
    (!n. MEM n (known ++ FLAT (MAP (\i. i.inst_outputs) prefix)) ==>
      lookup_var n mid = Q n) /\
    execution_frame mid = execution_frame st
Proof
  simp[current_copy_schedule_append] >> strip_tac >>
  drule_all current_copy_schedule_run >> strip_tac >>
  qexists_tac `ready` >> simp[] >>
  metis_tac[current_copy_schedule_frame]
QED
