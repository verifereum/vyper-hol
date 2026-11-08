(* Actual live-call order, independently of paired execution. *)
Theory lowerDloadPtrLiveFrames
Ancestors
  o1PassContract ptrDiscipline ctxLookupAgreeHelpers fcgBridge fcgDefs
  venomFnScheduleRunner venomExecSemantics venomInst list rich_list

Theorem dload_active_invoke_target:
  !fn ci s nm ops.
  active_inst fn ci s /\ ci.inst_opcode = INVOKE /\
  decode_invoke ci = SOME (nm,ops) ==>
  MEM nm (fn_invoke_targets fn)
Proof
  rpt gen_tac >> strip_tac >>
  `MEM ci (fn_insts fn)` by
    (qpat_assum `active_inst fn ci s`
       (mp_then (Pos last) mp_tac EVERY_active_inst) >>
     disch_then (qspec_then `\i. MEM i (fn_insts fn)` mp_tac) >>
     simp[EVERY_MEM]) >>
  gvs[decode_invoke_def, AllCaseEqs()] >>
  simp[fn_invoke_targets_def, fcg_scan_function_def, mem_get_invoke_targets] >>
  metis_tac[]
QED

Theorem dload_precedes_trans[local]:
  list_precedes x y names /\ list_precedes y z names ==>
  list_precedes x z names
Proof
  simp[list_precedes_iff] >> rpt strip_tac >> gvs[] >>
  metis_tac[arithmeticTheory.LESS_TRANS]
QED

Theorem dload_frame_live_order:
  !vs C stk PG G tn fn inst s.
  frame_reachable vs C stk PG G tn fn inst s ==>
  !names. callee_first names C.ctx_functions ==>
  EVERY (\f. MEM f C.ctx_functions) (fn :: MAP (\c. c.cf_fn) stk) /\
  (!i j. i < j /\ j < LENGTH (fn :: MAP (\c. c.cf_fn) stk) ==>
    list_precedes (EL i (fn :: MAP (\c. c.cf_fn) stk)).fn_name
      (EL j (fn :: MAP (\c. c.cf_fn) stk)).fn_name names)
Proof
  ho_match_mp_tac frame_reachable_ind >> rpt conj_tac
  >- (rpt gen_tac >> strip_tac >> rpt strip_tac >>
      drule lookup_function_MEM >> gvs[])
  >- (rpt gen_tac >> strip_tac >> rpt strip_tac >> metis_tac[])
  >- (rpt gen_tac >> strip_tac >> rpt strip_tac >> metis_tac[])
  >- suspend "call"
  >> suspend "ret"
QED
Resume dload_frame_live_order[call]:
  rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
  first_x_assum drule >> strip_tac >>
  drule_all dload_active_invoke_target >> strip_tac >>
  `MEM fn' C.ctx_functions` by metis_tac[lookup_function_MEM] >>
  `fn'.fn_name = nm` by metis_tac[lookup_function_selected_name] >>
  `list_precedes fn'.fn_name fn.fn_name names` by
    gvs[callee_first_def] >>
  gvs[EVERY_MEM] >> conj_tac >- metis_tac[] >>
  rpt gen_tac >> strip_tac >>
  Cases_on `i` >-
    (Cases_on `j` >> gvs[] >>
     rename1 `k < SUC (LENGTH stk)` >>
     Cases_on `k` >- simp[] >>
     irule dload_precedes_trans >> qexists_tac `fn.fn_name` >>
     simp[] >>
     qpat_x_assum `!i j. _` (qspecl_then [`0`,`SUC n`] mp_tac) >>
     simp[]) >>
  Cases_on `j` >> gvs[] >> first_x_assum irule >> simp[]
QED
Resume dload_frame_live_order[ret]:
  rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
  first_x_assum drule >> simp[] >> strip_tac >>
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!i j. _` (qspecl_then [`SUC i`,`SUC j`] mp_tac) >>
  simp[]
QED
Finalise dload_frame_live_order

Theorem dload_order_names_distinct[local]:
  !fs names.
  (!i j. i < j /\ j < LENGTH fs ==>
    list_precedes (EL i fs).fn_name (EL j fs).fn_name names) ==>
  ALL_DISTINCT (MAP (\f. f.fn_name) fs)
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >> conj_tac
  >- (simp[MEM_MAP, MEM_EL] >> rpt strip_tac >> gvs[] >>
      qpat_x_assum `!i j. _` (qspecl_then [`0`,`SUC n`] mp_tac) >>
      simp[list_precedes_iff]) >>
  first_x_assum irule >> qexists_tac `names` >>
  gen_tac >> gen_tac >> strip_tac >>
  qpat_x_assum `!i j. _` (qspecl_then [`SUC i`,`SUC j`] mp_tac) >> simp[]
QED

Theorem dload_frame_live_names_distinct:
  frame_reachable vs C stk PG G tn fn inst s /\
  callee_first names C.ctx_functions ==>
  ALL_DISTINCT (MAP (\f. f.fn_name) (fn :: MAP (\c. c.cf_fn) stk))
Proof
  strip_tac >> drule_all dload_frame_live_order >> strip_tac >>
  irule dload_order_names_distinct >> goal_assum (drule_at Any)
QED

Theorem dload_member_indices[local]:
  !fs ctx.
  EVERY (\f. MEM f ctx) fs /\ ALL_DISTINCT fs ==>
  ?ks. LENGTH ks = LENGTH fs /\ ALL_DISTINCT ks /\
    EVERY (\k. k < LENGTH ctx) ks /\ MAP (\k. EL k ctx) ks = fs
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  qpat_x_assum `MEM h ctx` mp_tac >> simp[MEM_EL] >> strip_tac >>
  qexists_tac `n :: ks` >> simp[] >> strip_tac >>
  `MEM (EL n ctx) (MAP (\k. EL k ctx) ks)` by
    (simp[MEM_MAP] >> metis_tac[]) >> gvs[]
QED

Theorem dload_frame_live_indices:
  frame_reachable vs C stk PG G tn fn inst s /\
  callee_first names C.ctx_functions ==>
  ?ks. LENGTH ks = LENGTH (fn :: MAP (\c. c.cf_fn) stk) /\
    ALL_DISTINCT ks /\ EVERY (\k. k < LENGTH C.ctx_functions) ks /\
    MAP (\k. EL k C.ctx_functions) ks = fn :: MAP (\c. c.cf_fn) stk
Proof
  strip_tac >>
  drule_all dload_frame_live_order >> strip_tac >>
  drule_all dload_frame_live_names_distinct >> strip_tac >>
  irule dload_member_indices >>
  metis_tac[ALL_DISTINCT_MAP]
QED
