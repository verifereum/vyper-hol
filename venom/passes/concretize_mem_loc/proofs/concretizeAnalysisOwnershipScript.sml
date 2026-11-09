Theory concretizeAnalysisOwnership
Ancestors venomWfProps
  concretizeAnalysisSizes o1ScheduleDecomp o1PassContract fcgDefs mem2varProofs
  relation list words arithmetic venomWf venomInst removeUnusedSsaProofs
  mem2varBlockSimHelpers pair

Definition source_call_def:
  source_call C f g <=>
    MEM f C.ctx_functions /\ MEM g C.ctx_functions /\
    MEM g.fn_name (fn_invoke_targets f)
End

Definition source_owns_def:
  source_owns C root aid sz <=>
    ?owner inst n rest.
      MEM root C.ctx_functions /\ MEM owner C.ctx_functions /\
      RTC (source_call C) root owner /\ MEM inst (fn_insts owner) /\
      inst.inst_opcode = ALLOCA /\ inst.inst_operands = Lit n :: rest /\
      aid = Allocation inst.inst_id /\ sz = w2n n
End

Theorem source_owns_literal:
  MEM fn C.ctx_functions /\ MEM inst (fn_insts fn) /\
  inst.inst_opcode = ALLOCA /\ inst.inst_operands = Lit n :: rest ==>
  source_owns C fn (Allocation inst.inst_id) (w2n n)
Proof
  rpt strip_tac >> simp[source_owns_def] >>
  qexistsl_tac [`fn`, `inst`, `rest`] >> simp[RTC_REFL]
QED

Theorem source_owns_prepend_call:
  source_call C f g /\ source_owns C g aid sz ==>
  source_owns C f aid sz
Proof
  rw[source_owns_def] >>
  qexistsl_tac [`owner`, `inst`, `rest`] >>
  gvs[source_call_def] >> metis_tac[RTC_RULES, source_call_def]
QED

Theorem source_call_precedes:
  callee_first names C.ctx_functions /\ source_call C f g ==>
  list_precedes g.fn_name f.fn_name names
Proof
  simp[callee_first_def, source_call_def] >> metis_tac[]
QED

Theorem source_call_rtc_precedes:
  !g h. RTC (source_call C) g h ==>
    !f names. callee_first names C.ctx_functions /\ source_call C f g ==>
      list_precedes h.fn_name f.fn_name names
Proof
  ho_match_mp_tac RTC_INDUCT >> rpt strip_tac
  >- metis_tac[source_call_precedes] >>
  first_x_assum (drule_all_then assume_tac) >>
  drule_all source_call_precedes >> strip_tac >>
  gvs[list_precedes_iff] >>
  qexistsl_tac [`i`, `j'`] >> simp[]
QED

Theorem ctx_inst_ids_flat:
  ctx_inst_ids_distinct C <=>
  ALL_DISTINCT (FLAT (MAP (\fn. MAP (\i. i.inst_id) (fn_insts fn)) C.ctx_functions))
Proof
  simp[ctx_inst_ids_distinct_def, fn_insts_def, fn_insts_blocks_flat,
       MAP_FLAT, MAP_MAP_o, combinTheory.o_DEF, ETA_THM]
QED

Theorem source_instruction_owner_unique:
  ctx_inst_ids_distinct C /\ MEM f C.ctx_functions /\ MEM g C.ctx_functions /\
  MEM i (fn_insts f) /\ MEM j (fn_insts g) /\ i.inst_id = j.inst_id ==>
  f = g
Proof
  rw[ctx_inst_ids_flat] >>
  irule ((venomFnInstsProofsTheory.all_distinct_flat_map_unique |> SPEC_ALL |>
      Q.GENL [`f`, `l`, `a`, `b`, `v`]) |> Q.ISPEC
    `\fn. MAP (\i. i.inst_id) (fn_insts fn)`) >>
  conj_tac >- (qexists_tac `C.ctx_functions` >> simp[]) >>
  qexists_tac `i.inst_id` >>
  simp[MEM_MAP] >> metis_tac[]
QED

Theorem source_instruction_unique:
  ctx_inst_ids_distinct C /\ MEM f C.ctx_functions /\ MEM g C.ctx_functions /\
  MEM i (fn_insts f) /\ MEM j (fn_insts g) /\ i.inst_id = j.inst_id ==>
  i = j
Proof
  strip_tac >>
  `f = g` by metis_tac[source_instruction_owner_unique] >> gvs[] >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts f))` by
    (gvs[ctx_inst_ids_flat] >> drule_all ALL_DISTINCT_FLAT_MAP_MEM >> simp[]) >>
  gvs[MEM_EL] >> metis_tac[ALL_DISTINCT_EL_IMP, LENGTH_MAP, EL_MAP]
QED

Theorem source_owns_size_unique:
  ctx_inst_ids_distinct C /\ source_owns C f aid s /\
  source_owns C g aid t ==> s = t
Proof
  rw[source_owns_def] >>
  `inst = inst'` by metis_tac[source_instruction_unique] >> gvs[]
QED

Theorem source_owns_callee_excludes:
  callee_first names C.ctx_functions /\ ctx_inst_ids_distinct C /\
  source_call C caller callee /\ source_owns C callee aid sz /\
  MEM inst (fn_insts caller) ==> aid <> Allocation inst.inst_id
Proof
  rw[source_owns_def] >> strip_tac >> gvs[] >>
  `caller = owner` by
    (irule source_instruction_owner_unique >>
     gvs[source_call_def] >> metis_tac[]) >>
  drule_all source_call_rtc_precedes >>
  gvs[list_precedes_iff] >> metis_tac[]
QED

Theorem source_owns_summary_excludes:
  callee_first names C.ctx_functions /\ ctx_inst_ids_distinct C /\
  source_call C caller callee /\
  EVERY (\(aid,pos,sz). source_owns C callee aid sz) entries /\
  MEM inst (fn_insts caller) ==>
  EVERY (\(aid,pos,sz). aid <> Allocation inst.inst_id) entries
Proof
  simp[EVERY_MEM, FORALL_PROD] >> rpt strip_tac >>
  first_x_assum drule >> strip_tac >>
  drule_all source_owns_callee_excludes >> simp[]
QED

Theorem source_member_ids_distinct:
  ctx_inst_ids_distinct C /\ MEM fn C.ctx_functions ==>
  fn_inst_ids_distinct fn
Proof
  strip_tac >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts fn))` by
    (gvs[ctx_inst_ids_flat] >> drule_all ALL_DISTINCT_FLAT_MAP_MEM >> simp[]) >>
  gvs[fn_inst_ids_distinct_def, fn_insts_def, fn_insts_blocks_flat,
      MAP_FLAT, MAP_MAP_o, combinTheory.o_DEF]
QED

Theorem source_owns_size_lookup:
  ctx_inst_ids_distinct C /\ source_owns C root (Allocation id) sz /\
  MEM owner C.ctx_functions /\ MEM inst (fn_insts owner) /\ inst.inst_id = id ==>
  FLOOKUP (source_alloca_sizes owner) id = SOME sz
Proof
  rw[source_owns_def] >>
  `inst = inst'` by metis_tac[source_instruction_unique] >> gvs[] >>
  irule source_alloca_sizes_literal >> simp[] >>
  metis_tac[source_member_ids_distinct]
QED
