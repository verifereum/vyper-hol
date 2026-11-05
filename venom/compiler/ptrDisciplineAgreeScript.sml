(*
 * Two contexts that agree on the functions a run can reach (ctx_agree)
 * have the same frame-reachable states, so the pointer discipline and the
 * taint bound carry over from one to the other: pruning a unit's
 * unreachable functions keeps them.
 *)
Theory ptrDisciplineAgree
Ancestors
  ptrDiscipline ctxLookupAgree ctxLookupAgreeHelpers venomExecSemantics
  venomInst venomState list

Theorem frame_reachable_ctx_agree:
  !R ctx ctx' vs.
    ctx_agree R ctx ctx' /\ ctx'.ctx_entry = ctx.ctx_entry /\
    (!entry. ctx.ctx_entry = SOME entry ==> R entry) ==>
    !stk PG G tn fn inst s.
      frame_reachable vs ctx stk PG G tn fn inst s ==>
      frame_reachable vs ctx' stk PG G tn fn inst s /\ R fn.fn_name /\
      lookup_function fn.fn_name ctx.ctx_functions = SOME fn /\
      EVERY (\f. R f.cf_fn.fn_name /\
                 lookup_function f.cf_fn.fn_name ctx.ctx_functions =
                   SOME f.cf_fn) stk
Proof
  rpt gen_tac >> disch_tac >> rpt gen_tac >> disch_tac >>
  qpat_x_assum `ctx_agree _ _ _ /\ _` mp_tac >>
  map_every qid_spec_tac [`ctx'`, `R`] >>
  pop_assum mp_tac >>
  map_every qid_spec_tac
    [`s`, `inst`, `fn`, `tn`, `G`, `PG`, `stk`, `ctx`, `vs`] >>
  ho_match_mp_tac frame_reachable_ind >> rpt conj_tac
  >- suspend "entry"
  >- suspend "next"
  >- suspend "block"
  >- suspend "call"
  >> suspend "ret"
QED

Resume frame_reachable_ctx_agree[entry]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  rename1 `ctx.ctx_entry = SOME name` >>
  `R name` by metis_tac[] >>
  `fn.fn_name = name` by metis_tac[lookup_function_selected_name] >>
  gvs[] >> irule frame_reachable_entry >> metis_tac[ctx_agree_def]
QED

Resume frame_reachable_ctx_agree[next]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  `step_inst fuel ctx inst s = step_inst fuel ctx' inst s`
    by metis_tac[ctx_agree_active_step] >>
  simp[] >> irule frame_reachable_next >> metis_tac[]
QED

Resume frame_reachable_ctx_agree[block]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  `step_inst fuel ctx inst s = step_inst fuel ctx' inst s`
    by metis_tac[ctx_agree_active_step] >>
  simp[] >> irule frame_reachable_block >> metis_tac[]
QED

Resume frame_reachable_ctx_agree[call]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  drule_all ctx_agree_selected_calls >> strip_tac >>
  drule_all fn_calls_within_active >> strip_tac >>
  `R nm` by metis_tac[inst_calls_within_def] >>
  rename1 `lookup_function nm ctx.ctx_functions = SOME callee` >>
  `callee.fn_name = nm` by metis_tac[lookup_function_selected_name] >>
  gvs[] >> irule frame_reachable_call >> metis_tac[ctx_agree_def]
QED

Resume frame_reachable_ctx_agree[ret]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  first_x_assum drule_all >> strip_tac >>
  rename1 `step_inst fuel ctx ri s = IntRet _ _` >>
  `step_inst fuel ctx ri s = step_inst fuel ctx' ri s`
    by metis_tac[ctx_agree_active_step] >>
  gvs[] >> irule frame_reachable_ret >> metis_tac[]
QED

Finalise frame_reachable_ctx_agree

(* The agreement in the direction a transfer from ctx to ctx' uses. *)
Theorem frame_reachable_ctx_agree_back:
  ctx_agree R ctx ctx' /\ ctx'.ctx_entry = ctx.ctx_entry /\
  (!entry. ctx.ctx_entry = SOME entry ==> R entry) /\
  frame_reachable vs ctx' stk PG G tn fn inst s ==>
  frame_reachable vs ctx stk PG G tn fn inst s /\
  !fuel. active_inst fn inst s ==>
         step_inst fuel ctx' inst s = step_inst fuel ctx inst s
Proof
  strip_tac >>
  `ctx_agree R ctx' ctx` by metis_tac[ctx_agree_sym] >>
  qspecl_then [`R`, `ctx'`, `ctx`, `vs`] mp_tac frame_reachable_ctx_agree >>
  impl_tac >- metis_tac[] >>
  disch_then drule >> strip_tac >> simp[] >>
  metis_tac[ctx_agree_active_step]
QED

Theorem final_taint_ctx_agree:
  ctx_agree R ctx ctx' /\ ctx'.ctx_entry = ctx.ctx_entry /\
  (!entry. ctx.ctx_entry = SOME entry ==> R entry) /\
  final_taint vs ctx' s_h tn T0 ==>
  final_taint vs ctx s_h tn T0
Proof
  rw[final_taint_def] >>
  drule_all frame_reachable_ctx_agree_back >> strip_tac >>
  metis_tac[]
QED

Theorem ptr_discipline_ctx_agree:
  ctx_agree R ctx ctx' /\ ctx'.ctx_entry = ctx.ctx_entry /\
  (!entry. ctx.ctx_entry = SOME entry ==> R entry) /\
  (!fn. MEM fn ctx'.ctx_functions ==> MEM fn ctx.ctx_functions) /\
  ptr_discipline lo ctx vs ==>
  ptr_discipline lo ctx' vs
Proof
  simp[ptr_discipline_def] >> strip_tac >> qexists_tac `P` >> conj_tac
  >- fs[EVERY_MEM] >>
  rpt gen_tac >> strip_tac >>
  drule_all frame_reachable_ctx_agree_back >> strip_tac >>
  first_x_assum drule >> strip_tac >> simp[] >>
  strip_tac >> first_x_assum irule >>
  fs[ctx_has_dalloca_def, EXISTS_MEM] >> metis_tac[]
QED

Theorem taint_within_ctx_agree:
  ctx_agree A ctx ctx' /\ ctx'.ctx_entry = ctx.ctx_entry /\
  (!entry. ctx.ctx_entry = SOME entry ==> A entry) /\
  taint_within D ctx vs ==>
  taint_within D ctx' vs
Proof
  simp[taint_within_def] >> strip_tac >> conj_tac >> rpt gen_tac >> strip_tac
  >- (drule_all frame_reachable_ctx_agree_back >> strip_tac >>
      first_x_assum irule >> metis_tac[])
  >> drule_all final_taint_ctx_agree >> strip_tac >>
  first_x_assum drule >> simp[]
QED
