(* Storage/transient tuple copies retain their allocation at the gas endpoint. *)
Theory tupleAssignImmutableDeployStorageOwned
Ancestors
  bodyMemAggregateMaterialise bodyMemAggregateBoundary exprSimMemUnwrap
  exprSimStorageCopy exprLoweringProps freshWrites valueEncodingProps
  loweringPosts fragGasPathMem exprLowering context compileEnv
  loweringStateRelDefs exprSimCopy exprSimAlloc fragExec bodyImmutableUnwrapMemory
  venomExecSemantics venomInst venomState

Theorem tuple_immutable_storage_materialise_owned:
  !ctx func cenv cx e es sa sm sb s0 es' v tys p op s.
    post_value_type cenv e = expr_type e /\
    unwrap_value cenv (LocatedValue (TupleT tys) p) sm = (op, sb) /\
    (p.ptr_location = LocStorage \/ p.ptr_location = LocTransient) /\
    ~is_word_type (TupleT tys) /\
    local_ptrs_reserved cenv sa /\
    MAP FDOM es.scopes = MAP FDOM es'.scopes /\ sa.cs_next_var <= sm.cs_next_var /\
    sa.cs_next_id <= sm.cs_next_id /\
    fn_has_code sm sb func /\ fn_inst_ids_distinct func /\
    (!x. p.ptr_operand = Var x ==> not_fresh_at sm x) /\
    (!tvt. evaluate_type (get_tenv cx) (TupleT tys) = SOME tvt ==>
           type_memory_bytes cenv (TupleT tys) = type_memory_size tvt /\
           type_memory_size tvt < 2 ** 64) /\
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
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all storage_unwrap_layout_facts >> strip_tac >>
  drule_all storage_unwrap_type_facts >> strip_tac >>
  `local_ptrs_reserved cenv sm` by
    metis_tac[local_ptrs_reserved_next_var] >>
  drule_all alloc_buffer_source_path_mem >> strip_tac >>
  `storage_holds cx (p.ptr_location = LocTransient) (TupleT tys) (Value v) a es' u` by
    (qpat_x_assum `storage_holds _ _ _ _ _ _ s` mp_tac >>
     simp[storage_holds_def]) >>
  `!x. p.ptr_operand = Var x \/ buf.buf_operand = Var x ==>
       not_fresh_at mid x` by
    (gen_tac >> strip_tac
     >- (irule freshWritesTheory.not_fresh_at_mono >>
         qexists_tac `sm` >> simp[]) >> fs[]) >>
  `w2n w + 32 * type_slot_size tv < 2**256 /\
   w2n w + 32 * type_slot_size tv <= u.vs_alloca_next` by
    fs[valueEncodingPropsTheory.type_memory_size_slots, wordsTheory.dimword_def] >>
  qpat_x_assum `(_ + 31) DIV 32 = _`
    (fn th => RULE_ASSUM_TAC (REWRITE_RULE [th])) >>
  drule_all storage_unwrap_typed_suffix_path_mem >> strip_tac >>
  `expr_post ctx func cenv cx e es sa sb s0 es' v buf.buf_operand z` by
    (irule buffer_post_transport >>
     (conj_tac >- first_assum ACCEPT_TAC) >>
     (conj_tac >- first_assum ACCEPT_TAC) >>
     qexistsl_tac [`mid`, `p`, `s`, `sm`, `TupleT tys`, `tv`, `u`, `w`] >>
     asm_rewrite_tac [] >> simp[]) >>
  `z.vs_alloca_next = u.vs_alloca_next /\ z.vs_allocas = u.vs_allocas` by
    (drule copy_static_fields >> simp[]) >>
  `local_ptrs_reserved cenv mid` by
    metis_tac[local_ptrs_reserved_next_var] >>
  `!name b len. local_region cenv es'.scopes z name b len ==>
     regions_disjoint (w2n w) (type_memory_bytes cenv (TupleT tys)) b len` by
    metis_tac[copy_buffer_local_region_frame] >>
  qexistsl_tac [`z`, `w`, `tv`] >> simp[] >>
  reverse conj_tac >- metis_tac[] >>
  `0 = 0 + 0` by simp[] >> pop_assum SUBST1_TAC >>
  irule gas_path_mem_then >> qexists_tac `u` >> simp[]
QED
