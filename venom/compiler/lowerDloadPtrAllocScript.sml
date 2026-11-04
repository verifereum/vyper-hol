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

Theorem dload_frame_scratch_finite:
  dload_frame_sites f ==> FINITE f.dr_scratch
Proof
  simp[dload_frame_sites_def] >> strip_tac >>
  irule SUBSET_FINITE >> qexists_tac `FDOM f.dr_target` >>
  simp[SUBSET_DEF] >> metis_tac[]
QED

Theorem dload_frame_original_insert:
  dload_frame_sites f /\ id NOTIN f.dr_scratch ==>
  dload_frame_sites
    (f with <|dr_source := f.dr_source |+ (id,(b,n));
              dr_target := f.dr_target |+ (id,(c,n))|>)
Proof
  simp[dload_frame_sites_def] >> strip_tac >> conj_tac
  >- (gvs[DISJOINT_INSERT] >> SET_TAC[]) >> conj_tac
  >- (rpt gen_tac >> simp[FLOOKUP_UPDATE] >>
      Cases_on `id' = id` >> simp[] >> metis_tac[]) >>
  rpt gen_tac >> simp[FLOOKUP_UPDATE] >>
  Cases_on `id' = id` >> simp[] >> metis_tac[]
QED

Theorem dload_frame_scratch_insert:
  dload_frame_sites f /\ id NOTIN FDOM f.dr_source ==>
  dload_frame_sites
    (f with <|dr_target := f.dr_target |+ (id,(c,32));
              dr_scratch := id INSERT f.dr_scratch|>)
Proof
  simp[dload_frame_sites_def] >> strip_tac >> conj_tac
  >- (gvs[DISJOINT_INSERT, DISJOINT_SYM] >> SET_TAC[]) >> conj_tac
  >- (rpt gen_tac >> simp[FLOOKUP_UPDATE] >>
      Cases_on `id' = id` >- simp[FLOOKUP_DEF] >> simp[] >> metis_tac[]) >>
  rpt gen_tac >> simp[FLOOKUP_UPDATE] >>
  Cases_on `id' = id` >> simp[] >> metis_tac[]
QED

Theorem dload_selected_insert_lookup:
  p g = (p f |+ (a,(front:num,len:num))) /\ k < LENGTH (g::fs) ==>
  (FLOOKUP (p (EL k (g::fs))) q = SOME (b,n) <=>
    (k = 0 /\ q = a /\ b = front /\ n = len) \/
    (~(k = 0 /\ q = a) /\
     FLOOKUP (p (EL k (f::fs))) q = SOME (b,n)))
Proof
  strip_tac >> Cases_on `k` >> simp[FLOOKUP_UPDATE] >>
  Cases_on `q = a` >> simp[] >> metis_tac[]
QED

Theorem dload_selected_insert_bounds:
  p g = (p f |+ (a,(front:num,len:num))) /\ lo <= front /\
  (!k q b n. k < LENGTH (f::fs) /\
     FLOOKUP (p (EL k (f::fs))) q = SOME (b,n) ==>
     lo <= b /\ b+n <= front) ==>
  !k q b n. k < LENGTH (g::fs) /\
     FLOOKUP (p (EL k (g::fs))) q = SOME (b,n) ==>
     lo <= b /\ b+n <= front+len
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  drule_all dload_selected_insert_lookup >>
  disch_then (drule o iffLR) >> strip_tac >- gvs[] >>
  `lo <= b /\ b+n <= front` by (first_x_assum irule >> qexistsl [`k`,`q`] >> gvs[]) >>
  decide_tac
QED

Theorem dload_selected_insert_separated:
  p g = (p f |+ (a,(front:num,len:num))) /\
  (!k q b n. k < LENGTH (f::fs) /\
     FLOOKUP (p (EL k (f::fs))) q = SOME (b,n) ==> b+n <= front) /\
  (!k j q r b n c m. k < LENGTH (f::fs) /\ j < LENGTH (f::fs) /\
     FLOOKUP (p (EL k (f::fs))) q = SOME (b,n) /\
     FLOOKUP (p (EL j (f::fs))) r = SOME (c,m) /\
     (k <> j \/ q <> r) /\ 0 < n /\ 0 < m ==>
     b+n <= c \/ c+m <= b) ==>
  !k j q r b n c m. k < LENGTH (g::fs) /\ j < LENGTH (g::fs) /\
     FLOOKUP (p (EL k (g::fs))) q = SOME (b,n) /\
     FLOOKUP (p (EL j (g::fs))) r = SOME (c,m) /\
     (k <> j \/ q <> r) /\ 0 < n /\ 0 < m ==>
     b+n <= c \/ c+m <= b
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  `FLOOKUP (p (EL k (g::fs))) q = SOME (b,n) <=>
    (k = 0 /\ q = a /\ b = front /\ n = len) \/
    (~(k = 0 /\ q = a) /\ FLOOKUP (p (EL k (f::fs))) q = SOME (b,n))`
    by (irule dload_selected_insert_lookup >> simp[]) >>
  `FLOOKUP (p (EL j (g::fs))) r = SOME (c,m) <=>
    (j = 0 /\ r = a /\ c = front /\ m = len) \/
    (~(j = 0 /\ r = a) /\ FLOOKUP (p (EL j (f::fs))) r = SOME (c,m))`
    by (irule dload_selected_insert_lookup >> simp[]) >>
  gvs[] >> metis_tac[]
QED

Theorem dload_layout_original_insert:
  dload_live_layout lo sf tf (f::fs) /\
  FLOOKUP f.dr_source id = NONE /\ FLOOKUP f.dr_target id = NONE /\
  tf+n < dimword (:256) ==>
  dload_live_layout lo (sf+n) (tf+n)
    ((f with <|dr_source := f.dr_source |+ (id,(sf,n));
               dr_target := f.dr_target |+ (id,(tf,n))|>)::fs)
Proof
  strip_tac >>
  `dload_frame_sites f` by fs[dload_live_layout_def] >>
  `id NOTIN f.dr_scratch` by
    (fs[dload_frame_sites_def, FLOOKUP_DEF] >> metis_tac[]) >>
  drule_all dload_frame_original_insert >> strip_tac >>
  fs[dload_live_layout_def] >> simp[dload_live_layout_def] >>
  conj_tac
  >- (ho_match_mp_tac (SRULE [ADD_COMM] (Q.INST
        [`front` |-> `sf`, `len` |-> `n`, `a` |-> `id`]
        dload_selected_insert_bounds)) >> simp[] >> first_assum MATCH_ACCEPT_TAC) >>
  conj_tac
  >- (ho_match_mp_tac (SRULE [ADD_COMM] (Q.INST
        [`front` |-> `tf`, `len` |-> `n`, `a` |-> `id`]
        dload_selected_insert_bounds)) >> simp[] >> first_assum MATCH_ACCEPT_TAC) >>
  conj_tac
  >- (ho_match_mp_tac (SRULE [] (Q.INST
        [`front` |-> `sf`, `len` |-> `n`, `a` |-> `id`]
        dload_selected_insert_separated)) >> simp[] >>
      rpt conj_tac >- (rpt strip_tac >> res_tac) >> first_assum MATCH_ACCEPT_TAC) >>
  ho_match_mp_tac (SRULE [] (Q.INST
    [`front` |-> `tf`, `len` |-> `n`, `a` |-> `id`]
    dload_selected_insert_separated)) >> simp[] >>
  rpt conj_tac >- (rpt strip_tac >> res_tac) >> first_assum MATCH_ACCEPT_TAC
QED

Theorem dload_layout_scratch_insert:
  dload_live_layout lo sf tf (f::fs) /\
  FLOOKUP f.dr_source id = NONE /\ FLOOKUP f.dr_target id = NONE /\
  tf+32 < dimword (:256) ==>
  dload_live_layout lo sf (tf+32)
    ((f with <|dr_target := f.dr_target |+ (id,(tf,32));
               dr_scratch := id INSERT f.dr_scratch|>)::fs)
Proof
  strip_tac >>
  `dload_frame_sites f` by fs[dload_live_layout_def] >>
  `id NOTIN FDOM f.dr_source` by fs[FLOOKUP_DEF] >>
  drule_all dload_frame_scratch_insert >> strip_tac >>
  fs[dload_live_layout_def] >> simp[dload_live_layout_def] >>
  conj_tac
  >- (rpt gen_tac >>
      qpat_x_assum `!k id b n. _ ==> _ /\ _ <= sf` (qspec_then `k` mp_tac) >>
      Cases_on `k` >> simp[] >> metis_tac[]) >>
  conj_tac
  >- (ho_match_mp_tac (SRULE [ADD_COMM] (Q.INST
        [`front` |-> `tf`, `len` |-> `32`, `a` |-> `id`]
        dload_selected_insert_bounds)) >> simp[] >> first_assum MATCH_ACCEPT_TAC) >>
  conj_tac
  >- (rpt gen_tac >>
      qpat_x_assum `!k j id jd b n c m. _ /\ _ /\ FLOOKUP _.dr_source _ = _ /\ _ ==> _`
        (qspecl_then [`k`,`j`] mp_tac) >>
      Cases_on `k` >> Cases_on `j` >> simp[] >> metis_tac[]) >>
  ho_match_mp_tac (SRULE [] (Q.INST
    [`front` |-> `tf`, `len` |-> `32`, `a` |-> `id`]
    dload_selected_insert_separated)) >> simp[] >>
  rpt conj_tac >- (rpt strip_tac >> res_tac) >> first_assum MATCH_ACCEPT_TAC
QED
