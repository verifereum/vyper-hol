(* Retained byte windows during storage-backed argument materialisation. *)
Theory extcallUnwrapStorageMemory
Ancestors
  extcallAllocMemory exprSimMemUnwrap exprSimCopy exprSimMemDefs actualAllocExec
  loweringPosts fragGasPathMem exprLoweringProps valueEncodingProps
  venomState venomInst words list

Theorem extcall_captured_unwrap_storage_mem:
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
    (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient)) ==>
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
  drule storage_unwrap_layout_facts >> simp[] >>
  disch_then drule >> strip_tac >>
  `type_memory_size ltv < dimword (:256)` by simp[] >>
  `?a. eval_operand p.ptr_operand s = SOME a /\
    storage_holds cx (p.ptr_location = LocTransient) lt (Value v) a es s` by
    (Cases_on `p.ptr_location` >> gvs[vv_holds_def]) >>
  drule_all alloc_buffer_source_path_mem_endpoint >> strip_tac >>
  `storage_holds cx (p.ptr_location = LocTransient) lt (Value v) a es u` by
    (qpat_x_assum `storage_holds _ _ _ _ _ _ s` mp_tac >>
     simp[storage_holds_def]) >>
  `!x. p.ptr_operand = Var x \/ buf.buf_operand = Var x ==>
    not_fresh_at mid x` by
    (gen_tac >> strip_tac
     >- (irule freshWritesTheory.not_fresh_at_mono >>
         qexists_tac `sm` >> simp[]) >> fs[]) >>
  `w2n w + 32 * type_slot_size ltv < 2**256 /\
   w2n w + 32 * type_slot_size ltv <= u.vs_alloca_next` by
    fs[valueEncodingPropsTheory.type_memory_size_slots, wordsTheory.dimword_def] >>
  `(type_memory_bytes cenv lt + 31) DIV 32 = type_slot_size ltv` by
    simp[valueEncodingPropsTheory.type_memory_size_slots] >>
  `type_slot_size ltv < 2**256` by
    fs[valueEncodingPropsTheory.type_memory_size_slots, wordsTheory.dimword_def] >>
  qpat_x_assum `(_ + 31) DIV 32 = _`
    (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
  SUBGOAL_THEN ``p.ptr_location = LocStorage \/ p.ptr_location = LocTransient``
    assume_tac >- simp[] >>
  `(type_memory_size ltv + 31) DIV 32 = type_slot_size ltv` by
    simp[valueEncodingPropsTheory.type_memory_size_slots] >>
  qpat_x_assum `(_ + 31) DIV 32 = _`
    (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
  gvs[] >>
  FIRST [drule (SRULE [] (Q.SPEC `LocStorage` storage_unwrap_typed_suffix_path_mem)),
         drule (SRULE [] (Q.SPEC `LocTransient` storage_unwrap_typed_suffix_path_mem))] >>
  disch_then (qspecl_then [`ctx`, `func`, `cenv`, `cx`, `es`,
    `q with vs_inst_idx := LENGTH mid.cs_current_insts`, `lt`, `v`, `a`, `w`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >> strip_tac >>
  suspend "finish"
QED

Resume extcall_captured_unwrap_storage_mem[finish]:
  markerLib.RESUME_TAC >> (
  drule exprSimStorageCopyTheory.copy_static_fields >> strip_tac >>
  `local_ptrs_reserved cenv mid` by
    metis_tac[local_ptrs_reserved_next_var] >>
  drule_all actual_alloc_buffer_site >> strip_tac >>
  `stmt_state_rel ctx func cenv cx es z` by
    (irule copy_buffer_state_rel_frame >>
     qexistsl_tac [`w2n w`, `mk_inst sm.cs_next_id ALLOCA
       [Lit (n2w (type_memory_size ltv))]
       [STRING #"%" (toString sm.cs_next_var)]`,
       `q with vs_inst_idx := LENGTH mid.cs_current_insts`, `mid`,
       `type_memory_size ltv`] >>
     simp[mk_inst_def] >>
     conj_tac
     >- (rpt strip_tac >>
         qpat_x_assum `!name b len. local_region _ _ _ _ _ _ ==> _` drule >>
         simp[loweringStateRelDefsTheory.regions_disjoint_def] >> decide_tac) >>
     rpt strip_tac >>
     qpat_x_assum `!off len. _ ==> mem_bytes_at _ _ _ = _`
       (qspecl_then [`off`, `len`] mp_tac) >> simp[]) >>
  suspend "endpoint")
QED

Resume extcall_captured_unwrap_storage_mem[endpoint]:
  markerLib.RESUME_TAC >> (
  qexists_tac `z` >>
  conj_tac
  >- (drule_all gas_path_mem_then >> simp[]) >>
  simp[expr_val_rel_def, expr_store_bound_def] >>
  conj_tac >- (drule exprSimPropsTheory.val_store_size_le >> simp[] >> decide_tac) >>
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
      simp[] >> impl_tac >- fs[loweringStateRelDefsTheory.regions_disjoint_def] >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >>
      `local_region cenv es.scopes
         (q with vs_inst_idx := LENGTH mid.cs_current_insts) name b sz` by
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
           `name`, `sm`, `q with vs_inst_idx := LENGTH mid.cs_current_insts`] >> simp[]) >>
      qpat_x_assum `!off len. _ ==> mem_bytes_at _ _ _ = _`
        (qspecl_then [`off`, `len`] mp_tac) >>
      simp[] >> (impl_tac >- fs[loweringStateRelDefsTheory.regions_disjoint_def]) >> simp[]) >>
  `q.vs_data_section = s.vs_data_section` by
    (drule_all extcall_alloc_data_section >> simp[]) >>
  gvs[] >>
  fs[contract_storage_def, contract_transient_def])
QED
Finalise extcall_captured_unwrap_storage_mem
