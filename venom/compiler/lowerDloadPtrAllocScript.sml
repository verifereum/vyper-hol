Theory lowerDloadPtrAlloc
Ancestors
  lowerDloadPtrAggregate lowerDloadPtrRel lowerDloadPtrBoundary
  lowerDloadPtrCall ptrDiscipline venomExecSemantics venomState
  list pred_set finite_map words arithmetic

Theorem dload_table_stack_cons:
  dload_table_stack (f::fs) (s::ss) (t::ts) <=>
  f.dr_source = s.vs_allocas /\ f.dr_target = t.vs_allocas /\
  t.vs_alloca_next = s.vs_alloca_next +
    32 * SUM (MAP (\f. CARD f.dr_scratch) (f::fs)) /\
  dload_table_stack fs ss ts
Proof
  simp[dload_table_stack_def] >> eq_tac
  >- (strip_tac >> conj_tac
      >- (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
      conj_tac
      >- (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
      conj_tac
      >- (first_x_assum (qspec_then `0` mp_tac) >> simp[]) >>
      rpt strip_tac >> first_x_assum (qspec_then `SUC k` mp_tac) >> simp[]) >>
  strip_tac >> simp[] >> gen_tac >> Cases_on `k` >> simp[]
QED

Theorem dload_table_call_push:
  dload_table_stack (f::fs) (s::ss) (t::ts) /\
  setup_callee fn args s = SOME u /\ setup_callee gn bargs t = SOME v ==>
  dload_table_stack
    (<|dr_source := FEMPTY; dr_target := FEMPTY; dr_scratch := {}|> :: f::fs)
    (u::s::ss) (v::t::ts)
Proof
  strip_tac >>
  drule_all dload_setup_local_frame >> strip_tac >>
  imp_res_tac dload_setup_local_frame >>
  simp[dload_table_stack_cons] >>
  drule dload_table_stack_current >> simp[]
QED

Theorem dload_table_return_pop:
  dload_table_stack (f::g::fs) (u::s::ss) (v::t::ts) ==>
  dload_table_stack (g::fs)
    (merge_callee_state s u::ss) (merge_callee_state t v::ts)
Proof
  simp[dload_table_stack_cons, merge_callee_state_def]
QED

Theorem dload_table_original_fresh:
  dload_table_stack (f::fs) (s::ss) (t::ts) /\
  i.inst_id = j.inst_id /\ i.inst_outputs = [out] /\ j.inst_outputs = [out'] /\
  FLOOKUP s.vs_allocas i.inst_id = NONE /\
  FLOOKUP t.vs_allocas j.inst_id = NONE /\
  exec_alloca i s amount = OK u /\ exec_alloca j t amount = OK v ==>
  dload_table_stack
    ((f with <|dr_source := f.dr_source |+ (i.inst_id,(s.vs_alloca_next,w2n amount));
               dr_target := f.dr_target |+ (j.inst_id,(t.vs_alloca_next,w2n amount))|>)::fs)
    (u::ss) (v::ts)
Proof
  simp[dload_table_stack_cons] >> rpt strip_tac >>
  gvs[exec_alloca_def, update_var_def, dload_table_stack_cons] >>
  simp[ADD_ASSOC, ADD_COMM]
QED

Theorem dload_table_original_repeated:
  dload_table_stack (f::fs) (s::ss) (t::ts) /\
  i.inst_outputs = [out] /\ j.inst_outputs = [out'] /\
  FLOOKUP s.vs_allocas i.inst_id = SOME (b,n) /\
  FLOOKUP t.vs_allocas j.inst_id = SOME (c,n) /\
  exec_alloca i s amount = OK u /\ exec_alloca j t amount = OK v ==>
  dload_table_stack (f::fs) (u::ss) (v::ts)
Proof
  simp[dload_table_stack_cons] >> rpt strip_tac >>
  gvs[exec_alloca_def, update_var_def, dload_table_stack_cons]
QED

Theorem dload_table_scratch_fresh:
  dload_table_stack (f::fs) (s::ss) (t::ts) /\
  FINITE f.dr_scratch /\ i.inst_id NOTIN f.dr_scratch /\
  i.inst_outputs = [out] /\ FLOOKUP t.vs_allocas i.inst_id = NONE /\
  exec_alloca i t (32w:bytes32) = OK v ==>
  dload_table_stack
    ((f with <|dr_target := f.dr_target |+ (i.inst_id,(t.vs_alloca_next,32));
               dr_scratch := i.inst_id INSERT f.dr_scratch|>)::fs)
    (s::ss) (v::ts)
Proof
  simp[dload_table_stack_cons] >> rpt strip_tac >>
  gvs[exec_alloca_def, update_var_def, dload_table_stack_cons,
      dimword_def, CARD_INSERT] >> decide_tac
QED

Theorem dload_table_scratch_repeated:
  dload_table_stack (f::fs) (s::ss) (t::ts) /\
  i.inst_outputs = [out] /\ FLOOKUP t.vs_allocas i.inst_id = SOME (b,n) /\
  exec_alloca i t amount = OK v ==>
  dload_table_stack (f::fs) (s::ss) (v::ts)
Proof
  simp[dload_table_stack_cons] >> rpt strip_tac >>
  gvs[exec_alloca_def, update_var_def, dload_table_stack_cons]
QED

Theorem dload_layout_call_push:
  dload_live_layout lo sf tf fs ==>
  dload_live_layout lo sf tf
    (<|dr_source := FEMPTY; dr_target := FEMPTY; dr_scratch := {}|> :: fs)
Proof
  simp[dload_live_layout_def] >> strip_tac >>
  simp[dload_frame_sites_empty] >> conj_tac
  >- (rpt gen_tac >> Cases_on `k` >> simp[] >> metis_tac[]) >> conj_tac
  >- (rpt gen_tac >> Cases_on `k` >> simp[] >> metis_tac[]) >> conj_tac
  >- (rpt gen_tac >> Cases_on `k` >> Cases_on `j` >> simp[] >> metis_tac[]) >>
  rpt gen_tac >> Cases_on `k` >> Cases_on `j` >> simp[] >> metis_tac[]
QED

Theorem dload_layout_return_pop:
  dload_live_layout lo sf tf (f::fs) ==>
  dload_live_layout lo sf tf fs
Proof
  simp[dload_live_layout_def] >> strip_tac >> simp[] >> conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!k id b n. _ /\ FLOOKUP _ id = SOME (b,n) ==> _ /\ _ <= sf`
        (qspec_then `SUC k` mp_tac) >> simp[] >> metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!k id b n. _ /\ FLOOKUP _ id = SOME (b,n) ==> _ /\ _ <= tf`
        (qspec_then `SUC k` mp_tac) >> simp[] >> metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_x_assum `!k j id jd b n c m.
        _ /\ _ /\ FLOOKUP (EL k _).dr_source id = _ /\ _ ==> _`
        (qspecl_then [`SUC k`,`SUC j`] mp_tac) >>
      simp[] >> metis_tac[]) >>
  rpt strip_tac >>
  qpat_x_assum `!k j id jd b n c m. _` (qspecl_then [`SUC k`,`SUC j`] mp_tac) >>
  simp[] >> metis_tac[]
QED
