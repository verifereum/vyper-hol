(* TOP-LEVEL: equal compiler layout keys imply equal complete evaluated
   memory layouts. Capacities can differ inside a rounded bytes/string
   region; strides and sparse defaults still agree throughout aggregates.
   Helpers invert keys and lift checked type evaluation through lists. *)
Theory memoryLayoutSource
Ancestors
  memoryLayoutRel memoryLayoutDefs memoryValueDefs valueEncoding valueLoadProps
  vyperTypeValues vyperValue vyperAST list pair arithmetic
Libs
  legacyInduction

Theorem memory_layout_key_array:
  !ty array_bound.
    memory_layout_key (ArrayT ty array_bound) = ArrayLayout (memory_layout_key ty) array_bound
Proof
  Cases_on `array_bound` >> simp[memory_layout_key_def]
QED

Theorem memory_layout_key_tuple:
  !tys. memory_layout_key (TupleT tys) = TupleLayout (MAP memory_layout_key tys)
Proof
  simp[memory_layout_key_def] >> CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[]
QED

Theorem memory_layout_key_array_cases:
  !ty elem_key array_bound.
    memory_layout_key ty = ArrayLayout elem_key array_bound <=>
    ?elem_ty. ty = ArrayT elem_ty array_bound /\ memory_layout_key elem_ty = elem_key
Proof
  rpt gen_tac >> Cases_on `ty` >> simp[memory_layout_key_array, memory_layout_key_def, CONJ_COMM] >>
  qmatch_goalsub_rename_tac `memory_layout_key (BaseT bt)` >>
  Cases_on `bt` >> simp[memory_layout_key_def] >>
  qmatch_goalsub_rename_tac `BytesT bound` >> Cases_on `bound` >> simp[memory_layout_key_def]
QED

Theorem memory_layout_key_tuple_cases:
  !ty keys.
    memory_layout_key ty = TupleLayout keys <=>
    ?tys. ty = TupleT tys /\ MAP memory_layout_key tys = keys
Proof
  rpt gen_tac >> Cases_on `ty` >> simp[memory_layout_key_array, memory_layout_key_def] >>
  CONV_TAC (DEPTH_CONV ETA_CONV) >> simp[] >>
  qmatch_goalsub_rename_tac `memory_layout_key (BaseT bt)` >>
  Cases_on `bt` >> simp[memory_layout_key_def] >>
  qmatch_goalsub_rename_tac `BytesT bound` >> Cases_on `bound` >> simp[memory_layout_key_def]
QED

Theorem memory_layout_key_base_cases:
  !bt aty. memory_layout_key (BaseT bt) = memory_layout_key aty ==>
    ?abt. aty = BaseT abt
Proof
  rpt gen_tac >> Cases_on `bt` >> Cases_on `aty` >>
  simp[memory_layout_key_array, memory_layout_key_def] >>
  qmatch_goalsub_rename_tac `BytesT bound` >> Cases_on `bound` >>
  simp[memory_layout_key_array, memory_layout_key_def]
QED

Theorem memory_layout_base_key_rel:
  !fbt abt. memory_layout_key (BaseT fbt) = memory_layout_key (BaseT abt) ==>
    memory_layout_rel (BaseTV fbt) (BaseTV abt)
Proof
  Cases_on `fbt` >> Cases_on `abt` >>
  simp[memory_layout_key_def] >> rpt strip_tac >>
  TRY (qmatch_goalsub_rename_tac `memory_layout_rel (BaseTV (BytesT fbound)) _` >>
    Cases_on `fbound` >> gvs[memory_layout_key_def]) >>
  TRY (qmatch_goalsub_rename_tac `memory_layout_rel _ (BaseTV (BytesT abound))` >>
    Cases_on `abound` >> gvs[memory_layout_key_def]) >>
  simp[memory_layout_rel_refl, memory_layout_rel_bytestring]
QED

Definition layout_key_transport_def:
  layout_key_transport fty <=>
    !aty tenv ftv atv.
      memory_layout_key fty = memory_layout_key aty /\
      evaluate_type tenv fty = SOME ftv /\ evaluate_type tenv aty = SOME atv ==>
      memory_layout_rel ftv atv
End

Theorem layout_key_transport_base:
  !bt. layout_key_transport (BaseT bt)
Proof
  gen_tac >> rewrite_tac[layout_key_transport_def] >> rpt gen_tac >> strip_tac >>
  drule_all memory_layout_key_base_cases >> strip_tac >> gvs[] >>
  qpat_x_assum `evaluate_type tenv (BaseT bt) = SOME ftv`
    (assume_tac o MATCH_MP evaluate_type_base_identity) >>
  qpat_x_assum `evaluate_type tenv (BaseT abt) = SOME atv`
    (assume_tac o MATCH_MP evaluate_type_base_identity) >>
  gvs[] >>
  irule memory_layout_base_key_rel >> simp[]
QED

Theorem layout_key_transport_array:
  !fty array_bound.
    layout_key_transport fty ==> layout_key_transport (ArrayT fty array_bound)
Proof
  rpt gen_tac >> DISCH_TAC >> rewrite_tac[layout_key_transport_def] >> rpt gen_tac >> strip_tac >>
  `?aty_elem. aty = ArrayT aty_elem array_bound /\
    memory_layout_key aty_elem = memory_layout_key fty` by
    (irule (iffLR memory_layout_key_array_cases) >>
     ONCE_REWRITE_TAC [GSYM memory_layout_key_array] >> sym_tac >> first_assum ACCEPT_TAC) >>
  gvs[] >>
  qpat_x_assum `evaluate_type tenv (ArrayT fty array_bound) = SOME ftv`
    (strip_assume_tac o MATCH_MP evaluate_type_ArrayT_cases) >>
  qpat_x_assum `evaluate_type tenv (ArrayT aty_elem array_bound) = SOME atv`
    (strip_assume_tac o MATCH_MP evaluate_type_ArrayT_cases) >> gvs[] >>
  irule memory_layout_rel_array >>
  qpat_x_assum `layout_key_transport fty` (mp_tac o REWRITE_RULE [layout_key_transport_def]) >>
  disch_then (qspecl_then [`aty_elem`, `tenv`] mp_tac) >> simp[]
QED

Theorem layout_key_transport_evaluated:
  !fty aty tenv ftv atv.
    layout_key_transport fty /\ memory_layout_key fty = memory_layout_key aty /\
    evaluate_type tenv fty = SOME ftv /\ evaluate_type tenv aty = SOME atv ==>
    memory_layout_rel ftv atv
Proof
  rpt strip_tac >>
  qpat_x_assum `layout_key_transport fty` (mp_tac o REWRITE_RULE [layout_key_transport_def]) >>
  disch_then (qspecl_then [`aty`, `tenv`, `ftv`, `atv`] mp_tac) >> simp[]
QED

Theorem layout_key_transport_list:
  !fts ats tenv ftvs atvs.
    EVERY layout_key_transport fts /\ MAP memory_layout_key fts = MAP memory_layout_key ats /\
    LIST_REL (\ty tv. evaluate_type tenv ty = SOME tv) fts ftvs /\
    LIST_REL (\ty tv. evaluate_type tenv ty = SOME tv) ats atvs ==>
    memory_layouts_rel ftvs atvs
Proof
  Induct_on `fts` >> rpt gen_tac >> Cases_on `ats` >> Cases_on `ftvs` >> Cases_on `atvs` >>
  simp[] >> rpt strip_tac >> irule memory_layouts_rel_cons >> conj_tac
  >- (drule_all layout_key_transport_evaluated >> simp[]) >>
  first_x_assum drule_all >> simp[]
QED

Theorem layout_key_transport_tuple:
  !fts. EVERY layout_key_transport fts ==> layout_key_transport (TupleT fts)
Proof
  rpt gen_tac >> DISCH_TAC >> rewrite_tac[layout_key_transport_def] >> rpt gen_tac >> strip_tac >>
  `?ats. aty = TupleT ats /\ MAP memory_layout_key ats = MAP memory_layout_key fts` by
    (irule (iffLR memory_layout_key_tuple_cases) >>
     ONCE_REWRITE_TAC [GSYM memory_layout_key_tuple] >> sym_tac >> first_assum ACCEPT_TAC) >>
  gvs[] >>
  qpat_x_assum `evaluate_type tenv (TupleT fts) = SOME ftv`
    (strip_assume_tac o MATCH_MP evaluate_type_TupleT_cases) >>
  qpat_x_assum `evaluate_type tenv (TupleT ats) = SOME atv`
    (strip_assume_tac o MATCH_MP evaluate_type_TupleT_cases) >> gvs[] >>
  `MAP memory_layout_key fts = MAP memory_layout_key ats` by simp[] >>
  irule memory_layout_rel_tuple >> drule_all layout_key_transport_list >> simp[]
QED

Theorem memory_layout_key_atomic_cases:
  (!ty id. memory_layout_key ty = StructLayout id <=> ty = StructT id) /\
  (!ty id. memory_layout_key ty = FlagLayout id <=> ty = FlagT id) /\
  (!ty. memory_layout_key ty = EmptyLayout <=> ty = NoneT)
Proof
  rpt conj_tac >> rpt gen_tac >> Cases_on `ty` >>
  simp[memory_layout_key_array, memory_layout_key_def] >>
  qmatch_goalsub_rename_tac `memory_layout_key (BaseT bt)` >>
  Cases_on `bt` >> simp[memory_layout_key_def] >>
  qmatch_goalsub_rename_tac `BytesT bound` >> Cases_on `bound` >> simp[memory_layout_key_def]
QED

Theorem layout_key_transport_atomic:
  (!id. layout_key_transport (StructT id)) /\
  (!id. layout_key_transport (FlagT id)) /\
  layout_key_transport NoneT
Proof
  rpt conj_tac >> rpt gen_tac >> rewrite_tac[layout_key_transport_def] >>
  rpt gen_tac >> simp[memory_layout_key_def] >> strip_tac >>
  FIRST [qpat_x_assum `memory_layout_key aty = _` mp_tac,
    qpat_x_assum `_ = memory_layout_key aty` (mp_tac o SYM)] >>
  simp[memory_layout_key_atomic_cases] >> strip_tac >> gvs[]
QED

Theorem all_layout_key_transports:
  (!ty. layout_key_transport ty) /\ (!tys. EVERY layout_key_transport tys)
Proof
  ho_match_mp_tac
    (legacyInduction.mutual_ind_from_ops
       (TypeBase.set_induction_of ``:type``)) >>
  simp[layout_key_transport_base, layout_key_transport_array, layout_key_transport_tuple,
    layout_key_transport_atomic]
QED

Theorem memory_layout_key_evaluated:
  !fty aty tenv ftv atv.
    memory_layout_key fty = memory_layout_key aty /\
    evaluate_type tenv fty = SOME ftv /\ evaluate_type tenv aty = SOME atv ==>
    memory_layout_rel ftv atv
Proof
  rpt strip_tac >>
  mp_tac (Q.SPECL [`fty`, `aty`, `tenv`, `ftv`, `atv`] layout_key_transport_evaluated) >>
  simp[all_layout_key_transports]
QED
