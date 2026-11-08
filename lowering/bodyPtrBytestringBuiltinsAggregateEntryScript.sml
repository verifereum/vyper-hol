Theory bodyPtrBytestringBuiltinsAggregateEntry
Ancestors bodyPtrBytestringBuiltinsMemoryEntry
          bodyPtrBytestringBuiltinsStoreAllocationTrace
          bodyPtrBytestringBuiltinsAllocationTrace
          bodyPtrBytestringBuiltinsImageTupleHistory
          bodyPtrBytestringBuiltinsImageFrontier
          exprLowering context compileEnv emitHelper venomInst list

Theorem tuple_destination_memory_entry:
  !buf k s dst t.
  tuple_history buf k s /\ emit_op ADD [buf; Lit (n2w k)] s = (dst,t) ==>
  image_entry t /\ (!b. ~tail_alloc b t.cs_current_insts)
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- metis_tac[tuple_history_destination] >>
  gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, comp_return_def,
      fresh_var_def, fresh_id_def, emit_def, tail_alloc_append, mk_inst_def]
QED

Theorem allocation_trace_saved_bound:
  !s t j. allocation_trace s t /\ j < s.cs_next_var ==> j < t.cs_next_var
Proof
  simp[allocation_trace_def] >> rpt strip_tac >> decide_tac
QED

Theorem compile_make_tuple_entry:
  !cfn cenv es.
  (!e ty u vv v. MEM e es /\ image_entry u /\ cfn cenv ty e u = (vv,v) ==>
    image_entry v /\ allocation_trace u v) /\
  (!vv u op v. image_entry u /\ (!b. ~tail_alloc b u.cs_current_insts) /\
    unwrap_value cenv vv u = (op,v) ==>
    image_entry v /\ (!b. ~tail_alloc b v.cs_current_insts) /\ allocation_trace u v) ==>
  !j k s r t.
  tuple_history (Var (STRING #"%" (toString j))) k s /\ j < s.cs_next_var /\
  compile_make_tuple cfn cenv es (Var (STRING #"%" (toString j))) k s = (r,t) ==>
  image_entry t /\ j < t.cs_next_var
Proof
  rpt gen_tac >> Induct_on `es`
  >- simp[compile_make_tuple_def, comp_return_def, tuple_history_def] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `compile_make_tuple _ _ (_::_) _ _ _ = _` mp_tac >>
  simp[Once compile_make_tuple_def, comp_bind_def, comp_ignore_bind_def] >>
  disch_tac >>
  Cases_on `cfn cenv (expr_type h) h s` >> fs[] >>
  rename1 `cfn cenv (expr_type h) h s = (vv,u)` >>
  Cases_on `emit_op ADD [Var (STRING #"%" (toString j)); Lit (n2w k)] u` >> fs[] >>
  rename1 `emit_op ADD _ u = (dst,v)` >>
  Cases_on `unwrap_value cenv vv v` >> fs[] >>
  rename1 `unwrap_value cenv vv v = (op,w)` >>
  Cases_on `compile_store_memory cenv op dst (expr_type h) (lowered_value_type cenv h) w` >> fs[] >>
  `image_entry s` by fs[tuple_history_def] >>
  `image_entry u /\ allocation_trace s u` by metis_tac[] >>
  `tuple_history (Var (STRING #"%" (toString j))) k u` by
    metis_tac[tuple_history_callback, allocation_trace_protected_tail] >>
  `image_entry v /\ (!b. ~tail_alloc b v.cs_current_insts)` by
    metis_tac[tuple_destination_memory_entry] >>
  `allocation_trace u v` by metis_tac[allocation_trace_emit_op] >>
  `image_entry w /\ (!b. ~tail_alloc b w.cs_current_insts) /\ allocation_trace v w` by
    metis_tac[] >>
  `image_entry r' /\ (!b. ~tail_alloc b r'.cs_current_insts)` by
    metis_tac[compile_store_memory_entry, pairTheory.SND] >>
  `allocation_trace w r'` by
    metis_tac[compile_store_memory_allocation_trace, pairTheory.SND] >>
  `j < r'.cs_next_var` by metis_tac[allocation_trace_saved_bound] >>
  first_x_assum irule >> simp[tuple_history_def] >> metis_tac[]
QED
