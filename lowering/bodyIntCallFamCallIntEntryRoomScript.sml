Theory bodyIntCallFamCallIntEntryRoom
Ancestors
  exprLoweringProps intCallLookup

Theorem fmp_room_callee:
  !ctx caller callee s t.
    alloca_room ctx caller s /\ fmp_room ctx caller s /\
    fn_directly_calls ctx caller.fn_name callee.fn_name /\
    lookup_function callee.fn_name ctx.ctx_functions = SOME callee /\
    t.vs_alloca_next = s.vs_alloca_next /\ t.vs_fmp = s.vs_fmp ==>
    fmp_room ctx callee t
Proof
  rpt gen_tac >> rewrite_tac[alloca_room_def] >> strip_tac >>
  `TC (fn_directly_calls ctx) caller.fn_name callee.fn_name`
    by metis_tac[relationTheory.TC_RULES] >>
  `{g | TC (fn_directly_calls ctx) callee.fn_name g} SUBSET
   {g | TC (fn_directly_calls ctx) caller.fn_name g}`
    by (rw[pred_setTheory.SUBSET_DEF] >> metis_tac[relationTheory.TC_RULES]) >>
  `FINITE {g | TC (fn_directly_calls ctx) callee.fn_name g}`
    by metis_tac[pred_setTheory.SUBSET_FINITE] >>
  `CARD {g | TC (fn_directly_calls ctx) callee.fn_name g} <
   CARD {g | TC (fn_directly_calls ctx) caller.fn_name g}`
    by (irule pred_setTheory.CARD_PSUBSET >> simp[pred_setTheory.PSUBSET_MEMBER] >>
        qexists_tac `callee.fn_name` >> simp[]) >>
  rewrite_tac[fmp_room_def] >> strip_tac >>
  `s.vs_alloca_next + pending_alloca_size caller s +
     CARD {g | TC (fn_directly_calls ctx) caller.fn_name g} *
       unit_alloca_frame ctx <= w2n s.vs_fmp /\
   w2n s.vs_fmp + 2 ** 65 < dimword (:256)` by
    (qpat_x_assum `fmp_room _ _ _` mp_tac >>
     simp[fmp_room_def] >> impl_tac
     >- metis_tac[relationTheory.TC_RULES, venomInstTheory.lookup_function_MEM] >>
     simp[]) >>
  qmatch_goalsub_abbrev_tac `CARD below * frame` >>
  qmatch_asmsub_abbrev_tac `CARD below < CARD above` >>
  `pending_alloca_size callee t <= frame`
    by (simp[Abbr `frame`] >> irule pending_alloca_size_le_frame >>
        metis_tac[venomInstTheory.lookup_function_MEM]) >>
  `frame * SUC (CARD below) <= frame * CARD above`
    by simp[arithmeticTheory.LE_MULT_LCANCEL] >>
  full_simp_tac bool_ss [arithmeticTheory.MULT_CLAUSES] >> decide_tac
QED

Theorem setup_callee_rooms:
  !ctx caller callee s t args.
    alloca_room ctx caller s /\ fmp_room ctx caller s /\
    fn_directly_calls ctx caller.fn_name callee.fn_name /\
    lookup_function callee.fn_name ctx.ctx_functions = SOME callee /\
    setup_callee callee args s = SOME t ==>
    alloca_room ctx callee t /\ fmp_room ctx callee t
Proof
  rpt gen_tac >> strip_tac >>
  `t.vs_alloca_next = s.vs_alloca_next /\ t.vs_fmp = s.vs_fmp` by
    (qpat_x_assum `setup_callee _ _ _ = _` mp_tac >>
     simp[venomExecSemanticsTheory.setup_callee_def, AllCaseEqs()] >>
     strip_tac >> gvs[]) >>
  conj_tac
  >- (irule alloca_room_callee >> metis_tac[]) >>
  irule fmp_room_callee >> metis_tac[]
QED
