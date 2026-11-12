(* Code tuple materialisation retains the allocation at the common gas endpoint. *)
Theory tupleAssignImmutableDeployCodeOwned
Ancestors
  bodyMemAggregateMaterialise bodyMemAggregateBoundary exprSimMemUnwrap
  exprSimStorageCopy exprLoweringProps freshWrites valueEncodingProps
  loweringPosts fragGasPathMem exprLowering context compileEnv
  loweringStateRelDefs exprSimCopy exprSimAlloc fragExec bodyImmutableUnwrapMemory
  venomExecSemantics venomInst venomState

Theorem tuple_immutable_code_materialise_owned:
  !ctx func cenv cx e es sa sm sb s0 es' v tys p op s.
    post_value_type cenv e = expr_type e /\
    unwrap_value cenv (LocatedValue (TupleT tys) p) sm = (op, sb) /\
    p.ptr_location = LocCode /\ ~is_word_type (TupleT tys) /\
    local_ptrs_reserved cenv sa /\
    MAP FDOM es.scopes = MAP FDOM es'.scopes /\ sa.cs_next_var <= sm.cs_next_var /\
    sa.cs_next_id <= sm.cs_next_id /\
    fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
    (!x. p.ptr_operand = Var x ==> not_fresh_at sm x) /\
    (!tvt. evaluate_type (get_tenv cx) (TupleT tys) = SOME tvt ==>
           type_memory_bytes cenv (TupleT tys) = type_memory_size tvt) /\
    vv_post ctx func cenv cx e es sa sm s0 es' (Value v) (LocatedValue (TupleT tys) p) s /\
    alloca_history func s /\ s0.vs_alloca_next <= s.vs_alloca_next /\
    ~s.vs_halted /\ s.vs_current_bb = sm.cs_current_bb /\
    s.vs_inst_idx = LENGTH sm.cs_current_insts ==>
    ?u w tv. gas_path_mem ctx func s 0 (OK u) /\
      expr_post ctx func cenv cx e es sa sb s0 es' v op u /\
      evaluate_type (get_tenv cx) (TupleT tys) = SOME tv /\
      eval_operand op u = SOME w /\
      w2n w + type_memory_size tv <= u.vs_alloca_next /\
      alloca_history func u /\ s.vs_alloca_next <= u.vs_alloca_next /\
      u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      FLOOKUP u.vs_allocas sm.cs_next_id =
        SOME (w2n w, type_memory_bytes cenv (TupleT tys)) /\
      sa.cs_next_id <= sm.cs_next_id /\ sm.cs_next_id < sb.cs_next_id /\
      (!name b len. local_region cenv es'.scopes u name b len ==>
         regions_disjoint (w2n w) (type_memory_bytes cenv (TupleT tys)) b len)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `unwrap_value _ _ _ = _` mp_tac >>
  simp[unwrap_value_def, contextTheory.compile_ensure_in_memory_def,
       comp_bind_def, comp_ignore_bind_def, comp_return_def] >>
  pairarg_tac >> simp[] >> pairarg_tac >> simp[] >> strip_tac >>
  gvs[] >> rename1 `compile_alloc_buffer _ sm = (buf,mid)` >>
  rename1 `compile_imm_copy_to_memory _ _ _ _ _ _ mid = (_,sc)` >>
  `TupleT tys = expr_type e` by gvs[vv_post_def, vv_holds_def] >>
  `?a. eval_operand p.ptr_operand s = SOME a /\
       immutable_holds cenv cx (TupleT tys) (Value v) a es' s` by
    gvs[vv_post_def, vv_holds_def] >>
  `?tv. evaluate_type (get_tenv cx) (TupleT tys) = SOME tv` by
    (gvs[immutable_holds_def] >> metis_tac[]) >>
  `val_wf tv v /\ w2n a + type_memory_size tv < dimword (:256)` by
    (drule_all immutable_holds_bounds >> simp[]) >>
  `type_memory_bytes cenv (TupleT tys) = type_memory_size tv` by metis_tac[] >>
  `type_memory_bytes cenv (TupleT tys) < dimword (:256)` by decide_tac >>
  `ci_mono sm mid` by
    (qspecl_then [`type_memory_bytes cenv (TupleT tys)`, `sm`] mp_tac
       ci_mono_compile_alloc_buffer >> simp[]) >>
  `ci_mono mid sc` by
    (qpat_assum `compile_imm_copy_to_memory _ _ _ _ _ _ _ = _` mp_tac >>
     rpt (pop_assum kall_tac) >> strip_tac >>
     metis_tac[ci_mono_compile_imm_copy_to_memory, pairTheory.SND]) >>
  `cs_extends sm mid /\ cs_extends mid sc /\
   sm.cs_next_var <= mid.cs_next_var /\ mid.cs_next_id <= sc.cs_next_id` by
    gvs[ci_mono_def] >>
  `fn_has_code sm mid func /\ fn_has_code mid sc func` by
    metis_tac[fn_has_code_split] >>
  `local_ptrs_reserved cenv sm` by metis_tac[local_ptrs_reserved_next_var] >>
  `stmt_state_rel ctx func cenv cx es' s` by fs[vv_post_def] >>
  drule_all alloc_buffer_source_path_mem >> strip_tac >>
  suspend "copy_and_finish"
QED

Resume tuple_immutable_code_materialise_owned[copy_and_finish]:
  `copy_old_operand mid p.ptr_operand /\ copy_old_operand mid buf.buf_operand` by
    (rw[copy_old_operand_def] >> gvs[] >>
     metis_tac[freshWritesTheory.not_fresh_at_mono]) >>
  `(type_memory_bytes cenv (TupleT tys) + 31) DIV 32 = type_slot_size tv` by
    (simp[valueEncodingPropsTheory.type_memory_size_slots] >> decide_tac) >>
  qpat_x_assum `(_ + 31) DIV 32 = _`
    (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
  `alloca_inv u` by fs[stmt_state_rel_def] >>
  `w2n w + type_memory_size tv <= u.vs_alloca_next /\
   w2n w + type_memory_size tv < dimword (:256)` by gvs[] >>
  `w2n w + 0 + 32 * type_slot_size tv <= u.vs_alloca_next /\
   w2n w + 0 + 32 * type_slot_size tv < dimword (:256) /\
   w2n a + 0 + 32 * type_slot_size tv < dimword (:256)` by
    gvs[valueEncodingPropsTheory.type_memory_size_slots] >>
  `MEM (mk_inst sm.cs_next_id ALLOCA [Lit (n2w (type_memory_bytes cenv (TupleT tys)))]
       [STRING #"%" (toString sm.cs_next_var)]) (fn_insts func)` by
    metis_tac[buffer_alloc_code] >>
  `?z. gas_path_mem ctx func u 0 (OK z) /\
       copy_static z = copy_static u /\
       (!x. not_fresh_at mid x ==> lookup_var x z = lookup_var x u) /\
       z.vs_current_bb = sc.cs_current_bb /\
       z.vs_inst_idx = LENGTH sc.cs_current_insts /\ alloca_history func z /\
       LENGTH u.vs_memory <= LENGTH z.vs_memory /\
       (!off len. off + len <= w2n w \/ w2n w + type_memory_size tv <= off ==>
          mem_bytes_at off len z.vs_memory = mem_bytes_at off len u.vs_memory) /\
       val_in_memory tv v (w2n w) z.vs_memory /\
       val_footprint tv v <= type_memory_size tv` by
    (Cases_on `cenv.ce_is_ctor` >> fs[]
     >- suspend "ctor"
     >> suspend "runtime") >>
  `eval_operand buf.buf_operand z = SOME w` by
    (qsuff_tac `eval_operand buf.buf_operand z = eval_operand buf.buf_operand u`
     >- gvs[] >>
     irule exprSimStorageCopyTheory.storage_copy_operand_preserved >> simp[] >>
     qexists_tac `mid` >> simp[]) >>
  `expr_post ctx func cenv cx e es sa sc s0 es' v buf.buf_operand z` by
    (irule buffer_post_transport >>
     (conj_tac >- first_assum ACCEPT_TAC) >>
     (conj_tac >- first_assum ACCEPT_TAC) >>
     qexistsl_tac [`mid`, `p`, `s`, `sm`, `TupleT tys`, `tv`, `u`, `w`] >>
     asm_rewrite_tac [] >> simp[]) >>
  `z.vs_alloca_next = u.vs_alloca_next /\ z.vs_allocas = u.vs_allocas` by
    (drule copy_static_fields >> simp[]) >>
  `local_ptrs_reserved cenv mid` by metis_tac[local_ptrs_reserved_next_var] >>
  `!name b len. local_region cenv es'.scopes z name b len ==>
     regions_disjoint (w2n w) (type_memory_bytes cenv (TupleT tys)) b len` by
    metis_tac[copy_buffer_local_region_frame] >>
  qexistsl_tac [`z`, `w`, `tv`] >> simp[] >>
  reverse conj_tac >- metis_tac[] >>
  `0 = 0 + 0` by simp[] >> pop_assum SUBST1_TAC >>
  irule gas_path_mem_then >> qexists_tac `u` >> simp[]
QED

Resume tuple_immutable_code_materialise_owned[ctor]:
  `immutable_base_zero cenv s` by fs[stmt_state_rel_def] >>
  `!region. cenv.ce_imm_alloca = SOME region ==>
      eval_operand region u = SOME 0w /\ copy_old_operand mid region` by
    (rpt strip_tac >>
     `eval_operand region s = SOME 0w` by fs[immutable_base_zero_def] >>
     `!x. cenv.ce_imm_alloca = SOME (Var x) ==> not_fresh_at sa x` by
       metis_tac[local_ptrs_reserved_imm_base] >>
     `copy_old_operand sa region` by
       (simp[copy_old_operand_def] >> rpt strip_tac >> gvs[]) >>
     `copy_old_operand sm region` by
       (irule copy_old_operand_mono >> qexists_tac `sa` >> fs[]) >>
     `copy_old_operand mid region` by
       (irule copy_old_operand_mono >> qexists_tac `sm` >> fs[]) >>
     `eval_operand region u = eval_operand region s` by
       (Cases_on `region` >> fs[eval_operand_def, copy_old_operand_def]) >> fs[]) >>
  `w2n a + type_memory_size tv <= s.vs_alloca_next` by
    metis_tac[ctor_immutable_frontier] >>
  `w2n a + 0 + 32 * type_slot_size tv <= u.vs_alloca_next` by
    gvs[valueEncodingPropsTheory.type_memory_size_slots] >>
  `copy_old_operand mid (Var p')` by simp[copy_old_operand_def] >>
  drule ctor_code_copy_path_mem >> disch_then drule >>
  disch_then (qspecl_then [`u`, `a`, `w`, `ctx`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  rename1 `gas_path_mem ctx func u 0 (OK zcopy)` >>
  qexists_tac `zcopy` >> simp[] >>
  `immutable_holds cenv cx (TupleT tys) (Value v) a es' u` by
    (qpat_x_assum `immutable_holds _ _ _ _ _ _ s` mp_tac >>
     simp[immutable_holds_def]) >>
  `regions_disjoint (w2n a) (type_memory_size tv)
      (w2n w) (type_memory_size tv)` by
    (irule immutable_holds_alloca_disjoint >>
     qexistsl_tac [`cenv`, `ctx`, `cx`, `es'`, `func`] >>
     goal_assum (drule_at Any) >> simp[mk_inst_def] >>
     qexists_tac `mk_inst sm.cs_next_id ALLOCA
       [Lit (n2w (type_memory_size tv))]
       [STRING #"%" (toString sm.cs_next_var)]` >> gvs[mk_inst_def]) >>
  mp_tac (copy_ctor_contents
          |> Q.INST [`uu` |-> `u`, `zz` |-> `zcopy`, `es` |-> `es'`, `t` |-> `TupleT tys`]) >>
  (impl_tac >- (asm_rewrite_tac [] >> fs[])) >>
  strip_tac >> gvs[] >> first_assum ACCEPT_TAC
QED

Resume tuple_immutable_code_materialise_owned[runtime]:
  `w2n a + type_memory_size tv <= LENGTH u.vs_data_section` by
    (irule runtime_immutable_data_section >> metis_tac[]) >>
  `w2n a + 0 + 32 * type_slot_size tv <= LENGTH u.vs_data_section` by
    gvs[valueEncodingPropsTheory.type_memory_size_slots] >>
  `copy_old_operand mid (Var p')` by simp[copy_old_operand_def] >>
  drule code_copy_path_mem >> disch_then drule >>
  disch_then (qspecl_then [`u`, `a`, `w`, `ctx`] mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  rename1 `gas_path_mem ctx func u 0 (OK zcopy)` >>
  qexists_tac `zcopy` >> simp[] >>
  mp_tac (runtime_copy_frame_facts |> Q.INST [`zm` |-> `zcopy.vs_memory`]) >>
  impl_tac >- fs[] >> strip_tac >>
  drule_all (SRULE [arithmeticTheory.ADD_COMM] copy_runtime_contents) >> strip_tac >>
  gvs[] >> first_assum ACCEPT_TAC
QED

Finalise tuple_immutable_code_materialise_owned
