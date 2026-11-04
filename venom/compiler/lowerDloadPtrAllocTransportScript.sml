Theory lowerDloadPtrAllocTransport
Ancestors
  lowerDloadPtrAlloc lowerDloadPtrCall lowerDloadPtrTaint lowerDloadPtrAggregate
  lowerDloadPtrRel ptrDiscipline venomExecSemantics venomState codegenRel
  memLocDefs lowerDloadPtrSourceInv o1PassContract lowerDloadDefs
  finite_map list pred_set words

Theorem dload_live_site_original_insert:
  FLOOKUP f.dr_source id = NONE /\ FLOOKUP f.dr_target id = NONE /\
  dload_live_site (f::fs) owner q x y m ==>
  dload_live_site
    ((f with <|dr_source := f.dr_source |+ (id,(b,n));
               dr_target := f.dr_target |+ (id,(c,n))|>)::fs) owner q x y m
Proof
  Cases_on `owner` >> simp[dload_live_site_def, FLOOKUP_UPDATE] >>
  rpt strip_tac >> gvs[] >> metis_tac[optionTheory.NOT_NONE_SOME]
QED

Theorem dload_pointer_word_sites_mono:
  (!owner id b c n. dload_live_site fs owner id b c n ==>
                    dload_live_site gs owner id b c n) /\
  dload_pointer_word fs p q x y ==>
  dload_pointer_word gs p q x y
Proof
  PairCases_on `p` >> PairCases_on `q` >>
  simp[dload_pointer_word_def] >> metis_tac[]
QED

Theorem dload_value_word_sites_mono:
  (!owner id b c n. dload_live_site fs owner id b c n ==>
                    dload_live_site gs owner id b c n) /\
  dload_value_word fs mask p q x y ==>
  dload_value_word gs mask p q x y
Proof
  Cases_on `p` >> Cases_on `q` >>
  simp[dload_value_word_def] >> metis_tac[dload_pointer_word_sites_mono]
QED

Theorem dload_vars_match_sites_mono:
  (!owner id b c n. dload_live_site fs owner id b c n ==>
                    dload_live_site gs owner id b c n) /\
  dload_vars_match fs V G H tn un s t ==>
  dload_vars_match gs V G H tn un s t
Proof
  simp[dload_vars_match_def] >> rpt strip_tac >>
  metis_tac[dload_value_word_sites_mono]
QED

Theorem dload_param_values_sites_mono:
  (!owner id b c n. dload_live_site fs owner id b c n ==>
                    dload_live_site gs owner id b c n) /\
  dload_param_values fs PG PH xs ys ==>
  dload_param_values gs PG PH xs ys
Proof
  simp[dload_param_values_def, LIST_REL_EL_EQN, EL_GENLIST] >>
  rpt strip_tac >> gvs[] >> metis_tac[dload_value_word_sites_mono]
QED

Theorem dload_saved_metadata_head_replace:
  (!k. k < LENGTH cs ==>
    dload_saved_metadata (DROP (SUC k) (f::fs)) (EL k Ws) (EL k cs) (EL k ds)) <=>
  (!k. k < LENGTH cs ==>
    dload_saved_metadata (DROP (SUC k) (g::fs)) (EL k Ws) (EL k cs) (EL k ds))
Proof
  simp[]
QED

Theorem alloca_written_taint[local]:
  inst.inst_opcode = ALLOCA ==> written_taint tn inst s = {}
Proof
  strip_tac >>
  Cases_on `inst.inst_operands` >> simp[written_taint_def] >>
  rename1 `h::rest` >> Cases_on `rest` >> simp[written_taint_def] >>
  rename1 `h::j::rest` >> Cases_on `rest` >> simp[written_taint_def] >>
  rename1 `h::j::k::rest` >> Cases_on `rest` >> simp[written_taint_def]
QED

Theorem exec_alloca_memory_taint:
  inst.inst_opcode = ALLOCA /\ exec_alloca inst s amount = OK s' ==>
  s'.vs_memory = s.vs_memory /\
  (step_taint inst s s' tn).t_mem = tn.t_mem UNION new_site_bytes s s'
Proof
  strip_tac >>
  `written_taint tn inst s = {}` by simp[alloca_written_taint] >>
  qpat_x_assum `exec_alloca inst s amount = OK s'` mp_tac >>
  simp[exec_alloca_def, AllCaseEqs()] >> strip_tac >> gvs[] >>
  simp[update_var_def, step_taint_def, mem_taint_def,
       step_writes_def, source_memory_write_ranges_def, range_bytes_def]
QED

Theorem exec_alloca_fresh_new_bytes:
  inst.inst_outputs = [out] /\ FLOOKUP s.vs_allocas inst.inst_id = NONE /\
  exec_alloca inst s amount = OK s' ==>
  new_site_bytes s s' =
    {i | s.vs_alloca_next <= i /\ i < s.vs_alloca_next + w2n amount}
Proof
  simp[exec_alloca_def] >> strip_tac >> gvs[] >>
  simp[new_site_bytes_def, update_var_def, EXTENSION, FLOOKUP_UPDATE] >>
  gen_tac >> eq_tac
  >- (strip_tac >> Cases_on `inst.inst_id = aid` >> gvs[] >>
      gvs[FLOOKUP_DEF]) >>
  strip_tac >> qexists_tac `inst.inst_id` >> simp[] >>
  gvs[FLOOKUP_DEF]
QED

Theorem exec_alloca_repeated_new_bytes:
  inst.inst_outputs = [out] /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,n) /\
  exec_alloca inst s amount = OK s' ==>
  new_site_bytes s s' = {}
Proof
  simp[exec_alloca_def] >> strip_tac >> gvs[] >>
  simp[new_site_bytes_def, update_var_def, EXTENSION, FLOOKUP_DEF] >>
  metis_tac[]
QED

Theorem dload_live_site_original_insert_cases[local]:
  dload_live_site
    ((f with <|dr_source := f.dr_source |+ (id,(b,n));
               dr_target := f.dr_target |+ (id,(c,n))|>)::fs) owner q x y m ==>
  (owner = 0 /\ q = id /\ x = b /\ y = c /\ m = n) \/
  dload_live_site (f::fs) owner q x y m
Proof
  Cases_on `owner` >> simp[dload_live_site_def, FLOOKUP_UPDATE] >>
  Cases_on `id = q` >> simp[] >> rpt strip_tac >> gvs[]
QED

Theorem dload_memory_original_insert[local]:
  dload_live_layout lo sf tf (f::fs) /\
  dload_memory_match lo (f::fs) tn un s t /\
  s'.vs_memory = s.vs_memory /\ t'.vs_memory = t.vs_memory /\
  tn'.t_mem = tn.t_mem UNION {i | sf <= i /\ i < sf+n} /\
  un'.t_mem = un.t_mem UNION {i | tf <= i /\ i < tf+n} ==>
  dload_memory_match lo
    ((f with <|dr_source := f.dr_source |+ (id,(sf,n));
               dr_target := f.dr_target |+ (id,(tf,n))|>)::fs)
    tn' un' s' t'
Proof
  strip_tac >>
  `lo <= sf /\ sf <= tf` by fs[dload_live_layout_def] >>
  fs[dload_memory_match_def] >>
  rpt gen_tac >> strip_tac >>
  drule dload_live_site_original_insert_cases >> strip_tac
  >- (gvs[] >> simp[]) >>
  `lo <= b /\ b+n' <= sf /\ lo <= c /\ c+n' <= tf` by
    (drule_all dload_live_site_bounds >> simp[]) >>
  `b+k < sf /\ c+k < tf` by decide_tac >>
  simp[] >> metis_tac[]
QED

Theorem dload_alloca_fresh_memory:
  inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [out] /\
  FLOOKUP s.vs_allocas inst.inst_id = NONE /\
  FLOOKUP t.vs_allocas inst.inst_id = NONE /\
  exec_alloca inst s amount = OK s' /\ exec_alloca inst t amount = OK t' /\
  dload_live_layout lo s.vs_alloca_next t.vs_alloca_next (f::fs) /\
  dload_memory_match lo (f::fs) tn un s t ==>
  dload_memory_match lo
    ((f with <|dr_source := f.dr_source |+
                 (inst.inst_id,(s.vs_alloca_next,w2n amount));
               dr_target := f.dr_target |+
                 (inst.inst_id,(t.vs_alloca_next,w2n amount))|>)::fs)
    (step_taint inst s s' tn) (step_taint inst t t' un) s' t'
Proof
  strip_tac >>
  imp_res_tac exec_alloca_memory_taint >>
  imp_res_tac exec_alloca_fresh_new_bytes >>
  irule dload_memory_original_insert >> conj_tac >- simp[] >>
  qexistsl [`s`,`t`,`tn`,`un`] >> simp[]
QED

Theorem dload_alloca_repeated_memory:
  inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [out] /\
  FLOOKUP s.vs_allocas inst.inst_id = SOME (b,n) /\
  FLOOKUP t.vs_allocas inst.inst_id = SOME (c,n) /\
  exec_alloca inst s amount = OK s' /\ exec_alloca inst t amount = OK t' /\
  dload_memory_match lo fs tn un s t ==>
  dload_memory_match lo fs
    (step_taint inst s s' tn) (step_taint inst t t' un) s' t'
Proof
  strip_tac >>
  imp_res_tac exec_alloca_memory_taint >>
  imp_res_tac exec_alloca_repeated_new_bytes >>
  fs[dload_memory_match_def] >> metis_tac[]
QED

Theorem dload_alloca_fresh_pointer:
  dload_pointer_word
    ((f with <|dr_source := f.dr_source |+ (id,(b,n));
               dr_target := f.dr_target |+ (id,(c,n))|>)::fs)
    (b,n) (c,n) (n2w b) (n2w c)
Proof
  simp[dload_pointer_word_def, WORD_SUB_REFL, WORD_ADD_0] >>
  qexistsl [`0`,`id`] >> simp[dload_live_site_def, FLOOKUP_UPDATE]
QED

Theorem dload_alloca_repeated_pointer:
  FLOOKUP f.dr_source id = SOME (b,n) /\
  FLOOKUP f.dr_target id = SOME (c,n) ==>
  dload_pointer_word (f::fs) (b,n) (c,n) (n2w b) (n2w c)
Proof
  strip_tac >> simp[dload_pointer_word_def, WORD_SUB_REFL, WORD_ADD_0] >>
  qexistsl [`0`,`id`] >> simp[dload_live_site_def]
QED

Theorem dload_alloca_successor_headroom:
  o1_ctx_shape C /\ o1_src_inv D C vs /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  inst.inst_opcode = ALLOCA /\ step_inst fuel C inst s = OK s' /\
  active_inst fn inst' (s' with vs_inst_idx := SUC s.vs_inst_idx) ==>
  s'.vs_alloca_next + 32 * ctx_dload_count C < dimword (:256)
Proof
  strip_tac >>
  `frame_reachable vs C stk PG (step_prov PG G inst s')
    (step_taint inst s s' tn) fn inst'
    (s' with vs_inst_idx := SUC s.vs_inst_idx)` by
    (irule frame_reachable_next >>
     simp[venomInstTheory.is_terminator_def] >> metis_tac[]) >>
  drule_all o1_src_frame_dload_headroom_ok >>
  simp[dload_headroom_ok_def]
QED

Theorem dload_alloca_fresh_post_bound:
  inst.inst_outputs = [out] /\
  FLOOKUP s.vs_allocas inst.inst_id = NONE /\
  FLOOKUP t.vs_allocas inst.inst_id = NONE /\
  exec_alloca inst s amount = OK s' /\ exec_alloca inst t amount = OK t' /\
  dload_table_stack (f::fs) (s::ss) (t::ts) /\
  SUM (MAP (\f. CARD f.dr_scratch) (f::fs)) <= ctx_dload_count C /\
  o1_ctx_shape C /\ o1_src_inv D C vs /\
  frame_reachable vs C stk PG G tn fn inst s /\ active_inst fn inst s /\
  inst.inst_opcode = ALLOCA /\ step_inst fuel C inst s = OK s' /\
  active_inst fn inst' (s' with vs_inst_idx := SUC s.vs_inst_idx) ==>
  t'.vs_alloca_next < dimword (:256) /\
  t.vs_alloca_next + w2n amount < dimword (:256)
Proof
  strip_tac >> drule_all dload_alloca_successor_headroom >> strip_tac >>
  drule dload_table_stack_current >> strip_tac >>
  qpat_x_assum `exec_alloca inst s amount = OK s'` mp_tac >>
  qpat_x_assum `exec_alloca inst t amount = OK t'` mp_tac >>
  simp[exec_alloca_def, update_var_def] >> rpt strip_tac >> gvs[] >>
  decide_tac
QED

Theorem exec_alloca_post_vars[local]:
  i.inst_outputs = [out] /\ exec_alloca i s amount = OK s1 /\
  FLOOKUP s1.vs_allocas i.inst_id = SOME (b,n) ==>
  s1.vs_vars = s.vs_vars |+ (out,n2w b)
Proof
  simp[exec_alloca_def, AllCaseEqs()] >> strip_tac >>
  gvs[update_var_def, FLOOKUP_UPDATE]
QED

Theorem alloca_var_ghosts[local]:
  i.inst_opcode = ALLOCA /\ i.inst_outputs = [out] /\
  FLOOKUP s1.vs_allocas i.inst_id = SOME (b,n) ==>
  step_prov PG G i s1 = set_prov G [out] (SOME (b,n)) /\
  (step_taint i s s1 tn).t_var = set_var_taint tn.t_var [out] {}
Proof
  strip_tac >> simp[step_prov_def, out_prov_def, step_taint_def] >>
  namedCases_on `i.inst_operands` ["", "a ops"]
  >- simp[out_taint_def] >>
  namedCases_on `ops` ["", "b' rest"]
  >- (simp[out_taint_def] >> Cases_on `eval_operand a s` >> simp[]) >>
  Cases_on `rest` >> simp[out_taint_def] >>
  Cases_on `eval_operand a s` >> simp[]
QED

Theorem dload_alloca_vars_transport:
  i.inst_opcode = ALLOCA /\ i.inst_outputs = [out] /\
  exec_alloca i s amount = OK s1 /\ exec_alloca i t amount = OK t1 /\
  dload_vars_match fs V G H tn un s t /\
  (!owner id b c n. dload_live_site fs owner id b c n ==>
                     dload_live_site gs owner id b c n) /\
  FLOOKUP s1.vs_allocas i.inst_id = SOME (b,n) /\
  FLOOKUP t1.vs_allocas i.inst_id = SOME (c,n) /\
  dload_live_site gs owner i.inst_id b c n ==>
  dload_vars_match gs V
    (step_prov PG G i s1) (step_prov PH H i t1)
    (step_taint i s s1 tn) (step_taint i t t1 un) s1 t1
Proof
  strip_tac >>
  `s1.vs_vars = s.vs_vars |+ (out,n2w b)` by
    (irule exec_alloca_post_vars >> metis_tac[]) >>
  `t1.vs_vars = t.vs_vars |+ (out,n2w c)` by
    (irule exec_alloca_post_vars >> metis_tac[]) >>
  `dload_vars_match gs V G H tn un s t` by
    (irule dload_vars_match_sites_mono >> metis_tac[]) >>
  `dload_pointer_word gs (b,n) (c,n) (n2w b) (n2w c)` by
    (simp[dload_pointer_word_def, WORD_SUB_REFL, WORD_ADD_0] >> metis_tac[]) >>
  `step_prov PG G i s1 = set_prov G [out] (SOME (b,n)) /\
   (step_taint i s s1 tn).t_var = set_var_taint tn.t_var [out] {}` by
    (irule alloca_var_ghosts >> simp[]) >>
  `step_prov PH H i t1 = set_prov H [out] (SOME (c,n)) /\
   (step_taint i t t1 un).t_var = set_var_taint un.t_var [out] {}` by
    (irule alloca_var_ghosts >> simp[]) >>
  simp[dload_vars_match_def] >> rpt gen_tac >> strip_tac >>
  Cases_on `v = out`
  >- (gvs[lookup_var_def, set_prov_def, set_var_taint_def,
          FLOOKUP_UPDATE, op_taint_def, dload_value_word_def]) >>
  qpat_x_assum `dload_vars_match gs _ _ _ _ _ _ _` mp_tac >>
  simp[dload_vars_match_def] >> disch_then (qspec_then `v` mp_tac) >>
  simp[lookup_var_def, set_prov_def, set_var_taint_def,
       FLOOKUP_UPDATE, op_taint_def] >> strip_tac >> gvs[]
QED

(* Allocation integration: in the fresh branch of dload_actual_alloca_next,
   gs is the inserted head frame :: rs, fs is the old r :: rs.  The two
   absent lookups and dload_live_site_original_insert provide site monotonicity;
   exec_alloca supplies the post-table lookups at the old frontiers, and the
   inserted head gives the owner-zero live-site witness.  In the repeated
   branch gs = fs = r :: rs, monotonicity is reflexive, table-stack equality
   supplies the post-table lookups and the unchanged head gives owner zero.
   The stored n is used in both runs, not w2n amount in the repeated branch.
   This interface closes actual variable/provenance/variable-taint matching
   only.  Layout, saved metadata, other environment fields and full boundary
   reconstruction still need separate integration. *)
