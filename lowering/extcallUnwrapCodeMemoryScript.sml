(* Runtime and constructor code-backed captured argument materialisation. *)
Theory extcallUnwrapCodeMemory
Ancestors
  extcallAllocMemory bodyImmutableUnwrapMemory exprSimMemUnwrap exprSimCopy exprSimMemDefs actualAllocExec
  loweringPosts fragGasPathMem exprLoweringProps valueEncodingProps
  context compileEnv fragExec loweringSlice venomState venomInst words list

Theorem extcall_captured_unwrap_code_mem:
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
  (!ty p. vv = LocatedValue ty p ==> ty = lt /\
    (!x. p.ptr_operand = Var x ==> not_fresh_at sm x) /\
    (p.ptr_location <> LocMemory ==> t = lt) /\
    (is_word_type lt /\ p.ptr_location = LocMemory ==>
      !w. eval_operand p.ptr_operand s = SOME w ==>
        w2n w + 32 <= s.vs_alloca_next) /\
    (p.ptr_location = LocCode /\ cenv.ce_is_ctor ==>
      !region. cenv.ce_imm_alloca = SOME region ==>
        eval_operand region s = SOME 0w /\
        (!x. region = Var x ==> not_fresh_at sm x))) /\
  (?p. vv = LocatedValue lt p /\ ~is_word_type lt /\
    p.ptr_location = LocCode) ==>
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
  strip_tac >> gvs[] >>
  qpat_x_assum `unwrap_value _ _ _ = _` mp_tac >>
  simp[exprLoweringTheory.unwrap_value_def, contextTheory.compile_ensure_in_memory_def,
    comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >> gvs[] >>
  rename1 `compile_alloc_buffer _ sm = (buf,mid)` >>
  `?a. eval_operand p.ptr_operand s = SOME a /\
    immutable_holds cenv cx lt (Value v) a es s` by gvs[vv_holds_def] >>
  `w2n a + type_memory_size ltv < dimword (:256)` by
    (drule_all immutable_holds_bounds >> simp[]) >>
  rename1 `compile_imm_copy_to_memory _ _ _ _ _ _ mid = ((),su)` >>
  `ci_mono sm mid` by
    (qspecl_then [`type_memory_size ltv`, `sm`] mp_tac
      ci_mono_compile_alloc_buffer >> simp[]) >>
  `ci_mono mid su` by
    (qpat_assum `compile_imm_copy_to_memory _ _ _ _ _ _ _ = _` mp_tac >>
     rpt (pop_assum kall_tac) >> strip_tac >>
     metis_tac[ci_mono_compile_imm_copy_to_memory, pairTheory.SND]) >>
  `cs_extends sm mid /\ cs_extends mid su /\
    sm.cs_next_var <= mid.cs_next_var /\ mid.cs_next_id <= su.cs_next_id` by
    gvs[ci_mono_def] >>
  `fn_has_code sm mid func /\ fn_has_code mid su func` by
    metis_tac[fn_has_code_split] >>
  drule_all alloc_buffer_source_path_mem_endpoint >> strip_tac >>
  suspend "allocated"
QED

Resume extcall_captured_unwrap_code_mem[allocated]:
  `copy_old_operand mid p.ptr_operand /\ copy_old_operand mid buf.buf_operand` by
    (rw[copy_old_operand_def] >> gvs[] >>
     metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  `(type_memory_size ltv + 31) DIV 32 = type_slot_size ltv` by
    simp[valueEncodingPropsTheory.type_memory_size_slots] >>
  qpat_x_assum `(_ + 31) DIV 32 = _`
    (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
  `alloca_inv u` by fs[stmt_state_rel_def] >>
  `w2n w + 0 + 32 * type_slot_size ltv <= u.vs_alloca_next /\
   w2n w + 0 + 32 * type_slot_size ltv < dimword (:256) /\
   w2n a + 0 + 32 * type_slot_size ltv < dimword (:256)` by
    gvs[valueEncodingPropsTheory.type_memory_size_slots] >>
  `MEM (mk_inst sm.cs_next_id ALLOCA [Lit (n2w (type_memory_size ltv))]
    [STRING #"%" (toString sm.cs_next_var)]) (fn_insts func)` by
    metis_tac[actual_alloc_buffer_site] >>
  `?z. gas_path_mem ctx func u 0 (OK z) /\
    copy_static z = copy_static u /\
    (!x. not_fresh_at mid x ==> lookup_var x z = lookup_var x u) /\
    z.vs_current_bb = su.cs_current_bb /\
    z.vs_inst_idx = LENGTH su.cs_current_insts /\ alloca_history func z /\
    LENGTH u.vs_memory <= LENGTH z.vs_memory /\
    (!off len. off + len <= w2n w \/ w2n w + type_memory_size ltv <= off ==>
      mem_bytes_at off len z.vs_memory = mem_bytes_at off len u.vs_memory) /\
    val_in_memory ltv v (w2n w) z.vs_memory /\
    val_footprint ltv v <= type_memory_size ltv` by
    (Cases_on `cenv.ce_is_ctor` >> fs[]
     >- suspend "constructor" >> suspend "runtime") >>
  suspend "finish"
QED

Resume extcall_captured_unwrap_code_mem[constructor]:
  gvs[] >>
  `!region. cenv.ce_imm_alloca = SOME region ==>
    eval_operand region (q with vs_inst_idx := LENGTH mid.cs_current_insts) = SOME 0w /\
    copy_old_operand mid region` by
    (rpt strip_tac >>
     `eval_operand region s = SOME 0w /\ copy_old_operand sm region` by
       (fs[copy_old_operand_def] >> metis_tac[]) >>
     `copy_old_operand mid region` by
       (irule copy_old_operand_mono >> qexists_tac `sm` >> simp[]) >>
     Cases_on `region` >> fs[eval_operand_def, copy_old_operand_def]) >>
  `w2n a + type_memory_size ltv <= s.vs_alloca_next` by
    metis_tac[ctor_immutable_frontier] >>
  `w2n a + 0 + 32 * type_slot_size ltv <= q.vs_alloca_next` by
    gvs[valueEncodingPropsTheory.type_memory_size_slots] >>
  drule ctor_code_copy_path_mem >> disch_then drule >>
  disch_then (qspecl_then
    [`q with vs_inst_idx := LENGTH mid.cs_current_insts`, `a`, `w`, `ctx`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  rename1 `gas_path_mem ctx func _ 0 (OK copied)` >>
  qexists_tac `copied` >> simp[] >>
  suspend "constructor_contents"
QED

Resume extcall_captured_unwrap_code_mem[constructor_contents]:
  `immutable_holds cenv cx lt (Value v) a es
    (q with vs_inst_idx := LENGTH mid.cs_current_insts)` by
    (qpat_x_assum `immutable_holds _ _ _ _ _ _ s` mp_tac >>
     simp[immutable_holds_def]) >>
  `regions_disjoint (w2n a) (type_memory_size ltv)
    (w2n w) (type_memory_size ltv)` by
    (irule immutable_holds_alloca_disjoint >>
     qexistsl_tac [`cenv`, `ctx`, `cx`, `es`, `func`] >>
     goal_assum (drule_at Any) >> simp[mk_inst_def] >>
     qexists_tac `mk_inst sm.cs_next_id ALLOCA
       [Lit (n2w (type_memory_size ltv))]
       [STRING #"%" (toString sm.cs_next_var)]` >>
     gvs[mk_inst_def]) >>
  drule_at (Pos last) copy_ctor_contents >>
  disch_then (qspecl_then [`v`, `lt`, `func`, `es`, `cx`, `ctx`, `cenv`] mp_tac) >>
  (impl_tac >- fs[]) >>
  strip_tac >> gvs[] >> first_assum ACCEPT_TAC
QED

Resume extcall_captured_unwrap_code_mem[runtime]:
  fs[] >>
  `w2n a + type_memory_size ltv <= LENGTH u.vs_data_section` by
    (irule runtime_immutable_data_section >> metis_tac[]) >>
  `w2n a + 0 + 32 * type_slot_size ltv <= LENGTH u.vs_data_section` by
    gvs[valueEncodingPropsTheory.type_memory_size_slots] >>
  drule code_copy_path_mem >> disch_then drule >>
  disch_then (qspecl_then [`u`, `a`, `w`, `ctx`] mp_tac) >>
  (impl_tac >- gvs[]) >> strip_tac >>
  rename1 `gas_path_mem ctx func _ 0 (OK copied)` >>
  qexists_tac `copied` >> simp[] >>
  mp_tac (runtime_copy_frame_facts |> Q.INST [`zm` |-> `copied.vs_memory`, `tv` |-> `ltv`]) >>
  (impl_tac >- fs[]) >> strip_tac >>
  `val_wf ltv v /\ val_in_memory ltv v (w2n w) copied.vs_memory /\
   val_footprint ltv v <= type_memory_size ltv` by
    (irule copy_runtime_contents >>
     simp[] >> metis_tac[]) >>
  gvs[] >> gvs[]
QED

Resume extcall_captured_unwrap_code_mem[finish]:
  drule exprSimStorageCopyTheory.copy_static_fields >> strip_tac >>
  `local_ptrs_reserved cenv mid` by
    metis_tac[local_ptrs_reserved_next_var] >>
  drule_all actual_alloc_buffer_site >> strip_tac >>
  `stmt_state_rel ctx func cenv cx es z` by
    (irule copy_buffer_state_rel_frame >>
     qexistsl_tac [`w2n w`, `mk_inst sm.cs_next_id ALLOCA
       [Lit (n2w (type_memory_size ltv))]
       [STRING #"%" (toString sm.cs_next_var)]`, `u`, `mid`,
       `type_memory_size ltv`] >>
     gvs[mk_inst_def] >> conj_tac
     >- (rpt strip_tac >>
         gvs[] >>
         qpat_x_assum `!name b len. local_region _ _ _ _ _ _ ==> _` drule >>
         fs[loweringStateRelDefsTheory.regions_disjoint_def]) >>
     rpt strip_tac >>
     qpat_x_assum `!off len. _ ==> mem_bytes_at _ _ _ = _`
       (qspecl_then [`off`, `len`] mp_tac) >> simp[]) >>
  suspend "endpoint"
QED
Resume extcall_captured_unwrap_code_mem[endpoint]:
  `eval_operand buf.buf_operand z = SOME w` by
    (fs[eval_operand_def] >> metis_tac[]) >>
  qexists_tac `z` >> conj_tac
  >- (drule_all gas_path_mem_then >> simp[]) >>
  simp[expr_val_rel_def, expr_store_bound_def] >>
  conj_tac >- (drule exprSimPropsTheory.val_store_size_le >> simp[] >> gvs[]) >>
  conj_tac >- gvs[] >>
  conj_tac
  >- (rpt strip_tac >>
      `not_fresh_at mid x` by
        (irule freshWritesTheory.not_fresh_at_mono >> qexists_tac `sm` >> simp[]) >>
      metis_tac[]) >>
  conj_tac
  >- (rpt strip_tac >>
      `regions_disjoint (w2n w) (type_memory_size ltv) b sz` by metis_tac[] >>
      qpat_x_assum `!off len. _ ==> mem_bytes_at _ _ _ = _`
        (qspecl_then [`off`, `len`] mp_tac) >>
      simp[] >> (impl_tac >- fs[loweringStateRelDefsTheory.regions_disjoint_def]) >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >>
      `local_region cenv es.scopes u name b sz` by
        metis_tac[copy_buffer_local_region_frame] >>
      `regions_disjoint (w2n w) (type_memory_size ltv) b sz` by metis_tac[] >>
      qpat_x_assum `!off len. _ ==> mem_bytes_at _ _ _ = _`
        (qspecl_then [`off`, `len`] mp_tac) >>
      simp[] >> (impl_tac >- fs[loweringStateRelDefsTheory.regions_disjoint_def]) >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >>
      `regions_disjoint (w2n w) (type_memory_size ltv) io (type_memory_size itv)` by
        (irule extcall_alloc_immutable_separation >>
         qexistsl_tac [`buf`, `cenv`, `ctx`, `cx`, `es`, `func`, `iv`, `mid`,
           `name`, `sm`, `u`] >> simp[]) >>
      qpat_x_assum `!off len. _ ==> mem_bytes_at _ _ _ = _`
        (qspecl_then [`off`, `len`] mp_tac) >>
      simp[] >> (impl_tac >- fs[loweringStateRelDefsTheory.regions_disjoint_def]) >> simp[]) >>
  `q.vs_data_section = s.vs_data_section` by
    (drule_all extcall_alloc_data_section >> simp[]) >>
  gvs[] >> fs[contract_storage_def, contract_transient_def]
QED
Finalise extcall_captured_unwrap_code_mem
