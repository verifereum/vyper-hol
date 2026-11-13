Theory o1LowerDloadStackFunctions
Ancestors
  o1LowerDloadOccurrence o1PassContract fcgDefs venomInst list
  venomExecSemantics ctxLookupAgreeHelpers venomFnScheduleRunner contextCodegenRel

Theorem ld_list_precedes_trans:
  list_precedes x y names /\ list_precedes y z names ==>
  list_precedes x z names
Proof
  simp[list_precedes_iff] >> rpt strip_tac >> gvs[] >>
  qexistsl_tac [`i`, `j'`] >> simp[] >> decide_tac
QED

Theorem ld_list_precedes_irrefl:
  ~list_precedes x x names
Proof
  simp[list_precedes_iff] >> rpt strip_tac >> gvs[]
QED

Theorem ld_occ_live_functions:
  !vs C stk PG G tn fn inst s n a U B HP H.
  occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H ==>
  EVERY (\g. MEM g C.ctx_functions) (fn::MAP (\f. f.cf_fn) stk)
Proof
  ho_match_mp_tac occ_frame_reachable_ind >> simp[] >> rpt strip_tac >>
  imp_res_tac lookup_function_MEM >> gvs[]
QED

Theorem ld_invoke_target_member:
  !insts inst nm ops.
  MEM inst insts /\ inst.inst_opcode = INVOKE /\
  decode_invoke inst = SOME (nm,ops) ==>
  MEM nm (MAP FST (get_invoke_targets insts))
Proof
  Induct >> simp[get_invoke_targets_def] >> rpt gen_tac >> strip_tac
  >- (gvs[decode_invoke_def, AllCaseEqs()] >> simp[]) >>
  Cases_on `h.inst_opcode = INVOKE`
  >- (simp[] >> namedCases_on `h.inst_operands` ["", "arg rest"]
      >- (simp[] >> metis_tac[]) >>
      Cases_on `arg` >> simp[] >> metis_tac[]) >>
  simp[] >> metis_tac[]
QED

Theorem ld_active_callee_precedes:
  callee_first names C.ctx_functions /\ MEM fn C.ctx_functions /\
  active_inst fn inst s /\ inst.inst_opcode = INVOKE /\
  decode_invoke inst = SOME (nm,ops) /\
  lookup_function nm C.ctx_functions = SOME callee ==>
  list_precedes callee.fn_name fn.fn_name names
Proof
  strip_tac >>
  `MEM inst (fn_insts fn)` by
    (gvs[active_inst_def, fn_insts_def, fn_insts_blocks_MEM] >> metis_tac[MEM_EL]) >>
  `MEM nm (fn_invoke_targets fn)` by
    (simp[fn_invoke_targets_def, fcg_scan_function_def] >>
     irule ld_invoke_target_member >> metis_tac[]) >>
  `callee.fn_name = nm` by metis_tac[ctxLookupAgreeHelpersTheory.lookup_function_selected_name] >>
  gvs[callee_first_def]
QED

Theorem ld_occ_live_precedes:
  !vs C stk PG G tn fn inst s n a U B HP H.
  occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H ==>
  !names. callee_first names C.ctx_functions ==>
  !i j. i < j /\ j < LENGTH (fn::MAP (\f. f.cf_fn) stk) ==>
    list_precedes (EL i (fn::MAP (\f. f.cf_fn) stk)).fn_name
      (EL j (fn::MAP (\f. f.cf_fn) stk)).fn_name names
Proof
  ho_match_mp_tac occ_frame_reachable_strongind >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >> simp[] >> rpt strip_tac >> decide_tac)
  >- (rpt strip_tac >> metis_tac[])
  >- (rpt strip_tac >> metis_tac[])
  >- suspend "call"
  >> suspend "ret"
QED

Resume ld_occ_live_precedes[call]:
  rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
  `MEM fn C.ctx_functions` by
    (drule ld_occ_live_functions >> simp[]) >>
  `list_precedes fn'.fn_name fn.fn_name names` by
    (irule ld_active_callee_precedes >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >>
  namedCases_on `i` ["", "ii"]
  >- (namedCases_on `j` ["", "jj"] >> gvs[] >>
      namedCases_on `jj` ["", "kk"] >> gvs[] >>
      irule ld_list_precedes_trans >> qexists_tac `fn.fn_name` >> simp[] >>
      first_x_assum (qspec_then `names` mp_tac) >> simp[] >>
      disch_then (qspecl_then [`0`, `SUC kk`] mp_tac) >> simp[]) >>
  namedCases_on `j` ["", "jj"] >> gvs[] >>
  first_x_assum (qspec_then `names` mp_tac) >> simp[] >>
  disch_then (qspecl_then [`ii`, `jj`] mp_tac) >> simp[]
QED

Resume ld_occ_live_precedes[ret]:
  rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  first_x_assum (qspec_then `names` mp_tac) >> simp[] >>
  disch_then (qspecl_then [`SUC i`, `SUC j`] mp_tac) >>
  namedCases_on `i` ["", "ii"] >> namedCases_on `j` ["", "jj"] >> gvs[]
QED
Finalise ld_occ_live_precedes

Theorem ld_precedes_distinct:
  !fs. (!i j. i < j /\ j < LENGTH fs ==>
    list_precedes (EL i fs).fn_name (EL j fs).fn_name names) ==>
  ALL_DISTINCT (MAP (\g. g.fn_name) fs)
Proof
  Induct >- simp[] >> gen_tac >> disch_tac >>
  simp_tac bool_ss [MAP, ALL_DISTINCT] >> conj_tac
  >- (simp[MEM_MAP, MEM_EL] >> rpt strip_tac >>
      first_x_assum (qspecl_then [`0`, `SUC n`] mp_tac) >>
      simp[] >> metis_tac[ld_list_precedes_irrefl]) >>
  first_x_assum irule >> rpt gen_tac >> strip_tac >>
  first_x_assum (qspecl_then [`SUC i`, `SUC j`] mp_tac) >> simp[]
QED

Theorem ld_occ_live_distinct:
  occ_frame_reachable vs C stk PG G tn fn inst s n a U B HP H /\
  callee_first names C.ctx_functions ==>
  ALL_DISTINCT (MAP (\g. g.fn_name) (fn::MAP (\f. f.cf_fn) stk))
Proof
  strip_tac >> drule ld_occ_live_precedes >>
  disch_then (qspec_then `names` mp_tac) >>
  strip_tac >>
  irule ld_precedes_distinct >> metis_tac[]
QED
