(* Static allocation charges also bound the inherited dynamic frontier. *)
Theory bodyIntCallResource
Ancestors
  exprLoweringProps venomInst venomState relation pred_set arithmetic list

Theorem fmp_room_callee:
  alloca_room ctx caller s /\ fmp_room ctx caller s /\
  fn_directly_calls ctx caller.fn_name callee.fn_name /\
  lookup_function callee.fn_name ctx.ctx_functions = SOME callee /\
  t.vs_alloca_next = s.vs_alloca_next /\ t.vs_fmp = s.vs_fmp ==>
  fmp_room ctx callee t
Proof
  rewrite_tac[alloca_room_def, fmp_room_def] >> strip_tac >> strip_tac >>
  `TC (fn_directly_calls ctx) caller.fn_name callee.fn_name` by
    metis_tac[TC_RULES] >>
  `{g | TC (fn_directly_calls ctx) callee.fn_name g} SUBSET
   {g | TC (fn_directly_calls ctx) caller.fn_name g}` by
    (rw[SUBSET_DEF] >> metis_tac[TC_RULES]) >>
  `FINITE {g | TC (fn_directly_calls ctx) callee.fn_name g}` by
    metis_tac[SUBSET_FINITE] >>
  `CARD {g | TC (fn_directly_calls ctx) callee.fn_name g} <
   CARD {g | TC (fn_directly_calls ctx) caller.fn_name g}` by
    (irule CARD_PSUBSET >> simp[PSUBSET_MEMBER] >>
     qexists_tac `callee.fn_name` >> simp[]) >>
  `MEM callee ctx.ctx_functions` by metis_tac[lookup_function_MEM] >>
  `EXISTS (\inst. inst.inst_opcode = DALLOCA) (fn_insts caller) \/
   (?g f. TC (fn_directly_calls ctx) caller.fn_name g /\
      MEM f ctx.ctx_functions /\ f.fn_name = g /\
      EXISTS (\inst. inst.inst_opcode = DALLOCA) (fn_insts f))` by
    metis_tac[TC_RULES] >>
  qpat_x_assum `_ ==> _ /\ _` mp_tac >>
  (impl_tac >- metis_tac[]) >> strip_tac >> simp[] >>
  qmatch_goalsub_abbrev_tac `CARD below * frame` >>
  qmatch_asmsub_abbrev_tac `CARD below < CARD above` >>
  `pending_alloca_size callee t <= frame` by
    (simp[Abbr `frame`] >> irule pending_alloca_size_le_frame >> simp[]) >>
  `frame * SUC (CARD below) <= frame * CARD above` by
    simp[LE_MULT_LCANCEL] >>
  full_simp_tac bool_ss [MULT_CLAUSES] >> gvs[]
QED

(* A real outgoing call reserves one whole unit frame, independently of
   whether the callee itself has any remaining static allocations. *)
Theorem alloca_room_call_reserve:
  alloca_room ctx func s /\
  fn_directly_calls ctx func.fn_name name /\
  n <= pending_alloca_size func s /\ margin <= unit_alloca_frame ctx ==>
  s.vs_alloca_next + n + margin < dimword (:256)
Proof
  simp[alloca_room_def] >> strip_tac >>
  `TC (fn_directly_calls ctx) func.fn_name name` by metis_tac[TC_RULES] >>
  `0 < CARD {g | TC (fn_directly_calls ctx) func.fn_name g}` by
    (simp[GSYM NOT_ZERO_LT_ZERO, CARD_EQ_0, EXTENSION] >>
     qexists_tac `name` >> simp[]) >>
  `unit_alloca_frame ctx <=
   CARD {g | TC (fn_directly_calls ctx) func.fn_name g} * unit_alloca_frame ctx` by
    (simp[Once MULT_COMM, LE_MULT_CANCEL_LBARE]) >>
  decide_tac
QED
