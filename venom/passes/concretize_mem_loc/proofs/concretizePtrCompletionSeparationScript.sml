Theory concretizePtrCompletionSeparation
Ancestors
  staticLayoutCompletionProofs staticLayoutAllocatorProofs concretizeMemLocDefs
  list finite_map alist staticLayoutDefs

Theorem ptr_completion_pair_aux[local]:
  !insts positions occupied completed.
  ALL_DISTINCT (MAP FST items) /\
  (!i item. MEM i insts /\ exact_static_alloca i = SOME item ==> MEM item items) /\
  (!c sc pc. MEM (c,sc) items /\ FLOOKUP positions c = SOME pc /\ 0 < sc ==>
    MEM (pc,sc) occupied) /\
  MEM (a,sa) items /\ MEM (b,sb) items /\ a <> b /\ 0 < sa /\ 0 < sb /\
  (!pa pb. FLOOKUP positions a = SOME pa /\ FLOOKUP positions b = SOME pb ==>
    reserved_intervals_disjoint (pa,sa) (pb,sb)) /\
  complete_alloc_positions_aux insts positions occupied = SOME completed ==>
  !pa pb. FLOOKUP completed a = SOME pa /\ FLOOKUP completed b = SOME pb ==>
    reserved_intervals_disjoint (pa,sa) (pb,sb)
Proof
  Induct >- (simp[complete_alloc_positions_aux_def] >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  Cases_on `h.inst_opcode = ALLOCA`
  >- (Cases_on `exact_static_alloca_size h` >>
      gvs[complete_alloc_positions_aux_def] >>
      Cases_on `FLOOKUP positions (Allocation h.inst_id)`
      >- (Cases_on `checked_first_fit occupied x` >>
          gvs[complete_alloc_positions_aux_def] >>
          `MEM (Allocation h.inst_id,x) items` by
            (qpat_x_assum `!i item. _`
               (qspecl_then [`h`,`(Allocation h.inst_id,x)`] mp_tac) >>
             simp[exact_static_alloca_def]) >>
          first_x_assum MATCH_MP_TAC >>
          qexistsl_tac [`positions |+ (Allocation h.inst_id,x')`,
            `if x = 0 then occupied else (x',x)::occupied`] >>
          simp[] >> conj_tac >- metis_tac[] >>
          conj_tac
          >- (rpt gen_tac >> strip_tac >>
              Cases_on `c = Allocation h.inst_id`
              >- (`sc = x` by metis_tac[ALOOKUP_ALL_DISTINCT_MEM, optionTheory.SOME_11] >>
                  gvs[FLOOKUP_UPDATE] >> simp[]) >>
              gvs[FLOOKUP_UPDATE] >> Cases_on `x = 0` >> simp[] >> metis_tac[]) >>
          rpt gen_tac >> strip_tac >>
          drule checked_first_fit_SOME >> strip_tac >>
          Cases_on `a = Allocation h.inst_id`
          >- (`sa = x` by metis_tac[ALOOKUP_ALL_DISTINCT_MEM, optionTheory.SOME_11] >>
              gvs[FLOOKUP_UPDATE] >> fs[EVERY_MEM] >> metis_tac[]) >>
          Cases_on `b = Allocation h.inst_id`
          >- (`sb = x` by metis_tac[ALOOKUP_ALL_DISTINCT_MEM, optionTheory.SOME_11] >>
              gvs[FLOOKUP_UPDATE] >> fs[EVERY_MEM] >>
              `reserved_intervals_disjoint (pb,sb) (pa,sa)` by metis_tac[] >>
              fs[reserved_intervals_disjoint_def]) >>
          gvs[FLOOKUP_UPDATE] >> metis_tac[]) >>
      gvs[] >> first_x_assum MATCH_MP_TAC >>
      qexistsl_tac [`positions`,`occupied`] >> simp[] >> metis_tac[]) >>
  gvs[complete_alloc_positions_aux_def, exact_static_alloca_def,
      exact_static_alloca_size_def] >>
  first_x_assum MATCH_MP_TAC >> qexistsl_tac [`positions`,`occupied`] >> simp[] >> metis_tac[]
QED

Theorem ptr_completion_pair_separation:
  static_alloca_items fn = SOME items /\
  complete_alloc_positions_with_imports items forced reserved imported fn positions = SOME completed /\
  merge_forced_positions items forced positions = SOME merged /\
  MEM (a,sa) items /\ MEM (b,sb) items /\ a <> b /\ 0 < sa /\ 0 < sb /\
  (!pa pb. FLOOKUP merged a = SOME pa /\ FLOOKUP merged b = SOME pb ==>
    reserved_intervals_disjoint (pa,sa) (pb,sb)) /\
  FLOOKUP completed a = SOME pa /\ FLOOKUP completed b = SOME pb ==>
  reserved_intervals_disjoint (pa,sa) (pb,sb)
Proof
  simp[complete_alloc_positions_with_imports_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  `ALL_DISTINCT (MAP FST items)` by metis_tac[static_alloca_items_ALL_DISTINCT] >>
  `!i item. MEM i (fn_insts fn) /\ exact_static_alloca i = SOME item ==>
    MEM item items` by
    (rpt gen_tac >> strip_tac >>
     `i.inst_opcode = ALLOCA` by fs[exact_static_alloca_def, exact_static_alloca_size_def, AllCaseEqs()] >>
     metis_tac[static_alloca_items_MEM]) >>
  `!c sc pc. MEM (c,sc) items /\ FLOOKUP merged c = SOME pc /\ 0 < sc ==>
    MEM (pc,sc) (reserved ++ occupied ++ imported)` by
    (drule checked_preserved_intervals_invariant >> simp[] >> metis_tac[]) >>
  drule_all ptr_completion_pair_aux >> metis_tac[]
QED
