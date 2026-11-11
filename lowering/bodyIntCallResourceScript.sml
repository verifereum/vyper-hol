(* Static allocation charges also bound the inherited dynamic frontier. *)
Theory bodyIntCallResource
Ancestors
  exprLoweringProps intCallCallee moduleLowering compileEnv emitHelper
  venomInst venomState relation pred_set arithmetic list finite_map words

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

(* Materialization's static charge is exactly the stack-parameter slots.
   The size bound is essential: ALLOCA's literal is a machine word. *)
Theorem materialize_internal_params_charge:
  !caps ce st ce' st'.
    materialize_internal_params ce caps st = (ce',st') /\
    ALL_DISTINCT (MAP FST caps) /\
    (!nm off sz. MEM nm (MAP FST caps) /\
       FLOOKUP ce.ce_vars nm = SOME (MemLoc off sz) ==>
       sz < dimword (:256)) ==>
    SUM (MAP alloca_lit_size
           (FILTER (\i. i.inst_opcode = ALLOCA) st'.cs_current_insts)) =
      SUM (MAP alloca_lit_size
           (FILTER (\i. i.inst_opcode = ALLOCA) st.cs_current_insts)) +
      internal_stack_size ce (MAP (\c. (FST c,FST (SND c))) caps)
Proof
  Induct >- simp[materialize_internal_params_def, comp_return_def,
                 internal_stack_size_def] >>
  PairCases >> rpt gen_tac >>
  simp[materialize_internal_params_def, internal_stack_size_def] >>
  rename1 `if is_stack then _ else _` >>
  rename1 `FLOOKUP ce.ce_vars nm` >>
  Cases_on `is_stack` >> simp[]
  >- (Cases_on `FLOOKUP ce.ce_vars nm` >> simp[]
      >- (strip_tac >> first_x_assum drule >> simp[] >> metis_tac[]) >>
      rename1 `SOME loc` >> Cases_on `loc` >> simp[] >>
      simp[emit_op_def, emit_void_def, comp_bind_def,
           comp_ignore_bind_def, comp_return_def, fresh_id_def,
           fresh_var_def, emit_def] >> strip_tac >>
      first_x_assum drule >>
      (impl_tac >- (simp[FLOOKUP_UPDATE] >> metis_tac[])) >>
      simp[mat_tail_stack_size, FILTER_APPEND_DISTRIB, MAP_APPEND, SUM_APPEND,
           alloca_lit_size_def, mk_inst_def] >>
      rename1 `FLOOKUP ce.ce_vars nm = SOME (MemLoc off sz)` >>
      `sz < dimword (:256)` by metis_tac[] >> simp[]) >>
  strip_tac >> first_x_assum drule >>
  (impl_tac >- (simp[FLOOKUP_UPDATE] >> metis_tac[])) >>
  simp[mat_tail_stack_size]
QED
