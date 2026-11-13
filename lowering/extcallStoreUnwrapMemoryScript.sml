(* Captured argument unwrap: dispatch and retained registered byte windows. *)
Theory extcallStoreUnwrapMemory
Ancestors
  extcallUnwrapIdentityMemory extcallUnwrapWordMemory
  extcallUnwrapStorageMemory extcallUnwrapCodeMemory bodyMemoryDefs
  venomMemDefs exprLoweringProps

Theorem extcall_retained_windows[local]:
  stmt_state_rel ctx func cenv cx es s /\
  (!off len. off + len <= s.vs_alloca_next ==>
    mem_bytes_at off len z.vs_memory = mem_bytes_at off len s.vs_memory) ==>
  (!aid b sz off len. FLOOKUP s.vs_allocas aid = SOME (b,sz) /\
    aid < sm.cs_next_id /\ b <= off /\ off + len <= b + sz ==>
    mem_bytes_at off len z.vs_memory = mem_bytes_at off len s.vs_memory) /\
  (!name b sz off len. local_region cenv es.scopes s name b sz /\
    b <= off /\ off + len <= b + sz ==>
    mem_bytes_at off len z.vs_memory = mem_bytes_at off len s.vs_memory) /\
  (!name io itv iv off len. cenv.ce_is_ctor /\
    FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc io) /\
    FLOOKUP (case ALOOKUP es.immutables cx.txn.target of
      NONE => FEMPTY | SOME imms => get_source_immutables cenv.ce_module imms)
      name = SOME (itv,iv) /\
    io <= off /\ off + len <= io + type_memory_size itv ==>
    mem_bytes_at off len z.vs_memory = mem_bytes_at off len s.vs_memory)
Proof
  strip_tac >> conj_tac
  >- (rpt strip_tac >>
      `alloca_inv s` by fs[stmt_state_rel_def] >>
      `b + sz <= s.vs_alloca_next` by
        (fs[venomMemDefsTheory.alloca_inv_def, alloca_next_valid_def] >>
         metis_tac[]) >>
      first_x_assum irule >> decide_tac) >>
  conj_tac
  >- (rpt strip_tac >> drule_all body_local_region_frontier >> strip_tac >>
      first_x_assum irule >> decide_tac) >>
  rpt strip_tac >>
  `immutable_alloca_sep func cenv cx es s` by fs[stmt_state_rel_def] >>
  `io + type_memory_size itv <= s.vs_alloca_next` by
    (fs[immutable_alloca_sep_def] >> metis_tac[]) >>
  first_x_assum irule >> decide_tac
QED

Theorem extcall_captured_unwrap_mem:
  unwrap_value cenv vv sm = (op,su) /\
  fn_has_code sm su func /\ fn_inst_ids_distinct func /\
  stmt_state_rel ctx func cenv cx es s /\ local_ptrs_reserved cenv sm /\
  alloca_history func s /\ ~s.vs_halted /\
  s.vs_current_bb = sm.cs_current_bb /\
  s.vs_inst_idx = LENGTH sm.cs_current_insts /\
  read_result cx (Value v) es = (INL v,es) /\
  vv_holds cenv cx t (Value v) vv es s /\
  vv_store_bound cx t lt es (Value v) vv s /\
  vv_storage_live cx vv es s /\
  evaluate_type (get_tenv cx) t = SOME tv /\
  evaluate_type (get_tenv cx) lt = SOME ltv /\ val_wf tv v /\
  type_memory_bytes cenv lt = type_memory_size ltv /\
  type_memory_size ltv < dimword (:256) /\
  (!ty src. vv = StackValue ty src ==>
    !x. src = Var x ==> not_fresh_at sm x) /\
  (!ty p. vv = LocatedValue ty p ==>
    (p.ptr_location <> LocMemory \/ is_word_type ty \/ is_word_type lt ==> ty = lt) /\
    (!x. p.ptr_operand = Var x ==> not_fresh_at sm x) /\
    (p.ptr_location <> LocMemory ==> t = lt) /\
    (is_word_type lt /\ p.ptr_location = LocMemory ==>
      !w. eval_operand p.ptr_operand s = SOME w ==>
        w2n w + 32 <= s.vs_alloca_next) /\
    (p.ptr_location = LocCode /\ cenv.ce_is_ctor ==>
      !region. cenv.ce_imm_alloca = SOME region ==>
        eval_operand region s = SOME 0w /\
        (!x. region = Var x ==> not_fresh_at sm x))) ==>
  ?z. gas_path_mem ctx func s 0 (OK z) /\ ~z.vs_halted /\
    z.vs_current_bb = su.cs_current_bb /\
    z.vs_inst_idx = LENGTH su.cs_current_insts /\
    expr_val_rel cx t v op z /\ expr_store_bound cx t v op z /\
    (!w. ~is_word_type t /\ eval_operand op z = SOME w ==>
      type_memory_size ltv = 0 \/
      w2n w + type_memory_size ltv <= z.vs_alloca_next) /\
    (!x. not_fresh_at sm x ==> lookup_var x z = lookup_var x s) /\
    (!aid b sz off len. FLOOKUP s.vs_allocas aid = SOME (b,sz) /\
      aid < sm.cs_next_id /\ b <= off /\ off + len <= b + sz ==>
      mem_bytes_at off len z.vs_memory = mem_bytes_at off len s.vs_memory) /\
    (!name b sz off len. local_region cenv es.scopes s name b sz /\
      b <= off /\ off + len <= b + sz ==>
      mem_bytes_at off len z.vs_memory = mem_bytes_at off len s.vs_memory) /\
    (!name io itv iv off len. cenv.ce_is_ctor /\
      FLOOKUP cenv.ce_module_vars (cenv.ce_module,name) = SOME (ImmutableLoc io) /\
      FLOOKUP (case ALOOKUP es.immutables cx.txn.target of
        NONE => FEMPTY | SOME imms => get_source_immutables cenv.ce_module imms)
        name = SOME (itv,iv) /\
      io <= off /\ off + len <= io + type_memory_size itv ==>
      mem_bytes_at off len z.vs_memory = mem_bytes_at off len s.vs_memory) /\
    LENGTH s.vs_memory <= LENGTH z.vs_memory /\
    (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
      FLOOKUP z.vs_allocas aid = SOME entry) /\
    s.vs_alloca_next <= z.vs_alloca_next /\ alloca_history func z /\
    stmt_state_rel ctx func cenv cx es z /\
    contract_storage z = contract_storage s /\
    contract_transient z = contract_transient s /\
    z.vs_data_section = s.vs_data_section /\ z.vs_labels = s.vs_labels
Proof
  strip_tac >> Cases_on `vv`
  >- suspend "identity" >>
  rename1 `LocatedValue tag p` >>
  Cases_on `p.ptr_location = LocMemory /\ ~is_word_type tag /\ ~is_word_type lt`
  >- (qpat_x_assum `_ /\ _ /\ _` strip_assume_tac >> suspend "identity") >>
  `tag = lt` by metis_tac[] >>
  `!ty q. LocatedValue tag p = LocatedValue ty q ==> ty = lt /\
    (!x. q.ptr_operand = Var x ==> not_fresh_at sm x) /\
    (q.ptr_location <> LocMemory ==> t = lt) /\
    (is_word_type lt /\ q.ptr_location = LocMemory ==>
      !w. eval_operand q.ptr_operand s = SOME w ==>
        w2n w + 32 <= s.vs_alloca_next) /\
    (q.ptr_location = LocCode /\ cenv.ce_is_ctor ==>
      !region. cenv.ce_imm_alloca = SOME region ==>
        eval_operand region s = SOME 0w /\
        (!x. region = Var x ==> not_fresh_at sm x))` by
      (rpt gen_tac >> simp[NoAsms] >> strip_tac >>
       qpat_x_assum `!ty p'. LocatedValue tag p = LocatedValue ty p' ==> _`
         (qspecl_then [`ty`,`q`] mp_tac) >>
       gvs[NoAsms] >> metis_tac[]) >>
  Cases_on `is_word_type tag` >- suspend "word" >>
  Cases_on `p.ptr_location`
  >- metis_tac[]
  >- suspend "storage"
  >- suspend "storage"
  >- suspend "code" >>
  suspend "calldata"
QED

Resume extcall_captured_unwrap_mem[identity]:
  markerLib.RESUME_TAC >> (
  qmatch_asmsub_abbrev_tac `unwrap_value cenv cv sm` >>
  (Q.SUBGOAL_THEN `(?ty src. cv = StackValue ty src) \/
    (?ty p. cv = LocatedValue ty p /\ ~is_word_type ty /\
         ~is_word_type lt /\ p.ptr_location = LocMemory)` assume_tac
   >- (simp[Abbr `cv`] >> metis_tac[])) >>
  drule_all extcall_captured_unwrap_identity_mem >> strip_tac >>
  drule_all extcall_retained_windows >>
  disch_then (qspec_then `sm` strip_assume_tac) >>
  qexists_tac `z` >> pure_asm_rewrite_tac[] >> simp[])
QED
Resume extcall_captured_unwrap_mem[word]:
  qmatch_asmsub_abbrev_tac `unwrap_value cenv cv sm` >>
  (Q.SUBGOAL_THEN `?p. cv = LocatedValue lt p /\ is_word_type lt` assume_tac
   >- (simp[Abbr `cv`] >> metis_tac[])) >>
  drule_all extcall_captured_unwrap_word_mem >> strip_tac >>
  drule_all extcall_retained_windows >>
  disch_then (qspec_then `sm` strip_assume_tac) >>
  qexists_tac `z` >> pure_asm_rewrite_tac[] >> simp[]
QED
Resume extcall_captured_unwrap_mem[storage]:
  markerLib.RESUME_TAC >> (
  qmatch_asmsub_abbrev_tac `unwrap_value cenv cv sm` >>
  (Q.SUBGOAL_THEN `?p. cv = LocatedValue lt p /\ ~is_word_type lt /\
     (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient)` assume_tac
   >- (simp[Abbr `cv`] >> metis_tac[])) >>
  drule_all extcall_captured_unwrap_storage_mem >> simp[])
QED
Resume extcall_captured_unwrap_mem[code]:
  qmatch_asmsub_abbrev_tac `unwrap_value cenv cv sm` >>
  (Q.SUBGOAL_THEN `?p. cv = LocatedValue lt p /\ ~is_word_type lt /\
     p.ptr_location = LocCode` assume_tac
   >- (simp[Abbr `cv`] >> metis_tac[])) >>
  drule_all extcall_captured_unwrap_code_mem >> simp[]
QED
Resume extcall_captured_unwrap_mem[calldata]:
  fs[loweringPostsTheory.vv_holds_def]
QED
Finalise extcall_captured_unwrap_mem
