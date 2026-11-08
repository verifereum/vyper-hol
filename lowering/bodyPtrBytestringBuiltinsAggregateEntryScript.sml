Theory bodyPtrBytestringBuiltinsAggregateEntry
Ancestors bodyPtrBytestringBuiltinsAggregateConsumer
          bodyPtrBytestringBuiltinsMemoryEntry
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
  (!e callty u vv v. MEM e es /\ image_entry u /\ cfn cenv callty e u = (vv,v) ==>
    image_entry v /\ allocation_trace u v /\
    (!ty p. vv = LocatedValue ty p /\ ~is_word_type ty /\ p.ptr_location = LocCode /\
      type_memory_bytes cenv ty = 0 ==> expr_type e = ty /\ lowered_value_type cenv e = ty)) ==>
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
  `!ty p. vv = LocatedValue ty p /\ ~is_word_type ty /\ p.ptr_location = LocCode /\
      type_memory_bytes cenv ty = 0 ==> expr_type h = ty /\ lowered_value_type cenv h = ty` by
    metis_tac[] >>
  `image_entry r' /\ allocation_trace v r'` by
    (drule_all unwrap_store_memory_entry >> simp[]) >>
  `j < v.cs_next_var /\ j < r'.cs_next_var` by
    metis_tac[allocation_trace_saved_bound] >>
  `!off. tuple_history (Var (STRING #"%" (toString j))) off r'` by
    (simp[tuple_history_def] >> metis_tac[allocation_trace_protected_tail]) >>
  first_x_assum irule >> simp[] >> conj_tac
  >- (rpt gen_tac >> strip_tac >> first_x_assum irule >> simp[] >> metis_tac[]) >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED

Theorem compile_struct_lit_entry:
  !cfn cenv sty fields.
  (!fname e callty u vv v.
    MEM (fname,e) fields /\ image_entry u /\ cfn cenv callty e u = (vv,v) ==>
    image_entry v /\ allocation_trace u v /\
    (!ty p. vv = LocatedValue ty p /\ ~is_word_type ty /\ p.ptr_location = LocCode /\
      type_memory_bytes cenv ty = 0 ==>
      (case ALOOKUP (get_struct_fields cenv.ce_struct_fields
          (case sty of StructT n => nsid_to_string n | _ => "")) fname of
         SOME (fty,sz) => fty | NONE => expr_type e) = ty /\
      lowered_value_type cenv e = ty)) ==>
  !j k s r t.
  tuple_history (Var (STRING #"%" (toString j))) k s /\ j < s.cs_next_var /\
  compile_struct_lit cfn cenv sty fields (Var (STRING #"%" (toString j))) k s = (r,t) ==>
  image_entry t /\ j < t.cs_next_var
Proof
  rpt gen_tac >> Induct_on `fields`
  >- simp[compile_struct_lit_def, comp_return_def, tuple_history_def] >>
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >> PairCases_on `h` >>
  qpat_x_assum `compile_struct_lit _ _ _ (_::_) _ _ _ = _` mp_tac >>
  simp[Once compile_struct_lit_def, comp_bind_def, comp_ignore_bind_def] >>
  disch_tac >>
  Cases_on `cfn cenv (expr_type h1) h1 s` >> fs[] >>
  rename1 `cfn cenv (expr_type h1) h1 s = (vv,u)` >>
  Cases_on `emit_op ADD [Var (STRING #"%" (toString j)); Lit (n2w k)] u` >> fs[] >>
  rename1 `emit_op ADD _ u = (dst,v)` >>
  Cases_on `unwrap_value cenv vv v` >> fs[] >>
  rename1 `unwrap_value cenv vv v = (op,w)` >>
  qmatch_asmsub_abbrev_tac `compile_store_memory cenv op dst fty` >>
  Cases_on `compile_store_memory cenv op dst fty (lowered_value_type cenv h1) w` >> fs[] >>
  `image_entry s` by fs[tuple_history_def] >>
  `image_entry u /\ allocation_trace s u` by metis_tac[] >>
  `tuple_history (Var (STRING #"%" (toString j))) k u` by
    metis_tac[tuple_history_callback, allocation_trace_protected_tail] >>
  `image_entry v /\ (!b. ~tail_alloc b v.cs_current_insts)` by
    metis_tac[tuple_destination_memory_entry] >>
  `allocation_trace u v` by metis_tac[allocation_trace_emit_op] >>
  `!ty p. vv = LocatedValue ty p /\ ~is_word_type ty /\ p.ptr_location = LocCode /\
      type_memory_bytes cenv ty = 0 ==> fty = ty /\ lowered_value_type cenv h1 = ty` by
    (simp[Abbr `fty`] >> metis_tac[]) >>
  `image_entry r' /\ allocation_trace v r'` by
    (drule_all unwrap_store_memory_entry >> simp[]) >>
  `j < v.cs_next_var /\ j < r'.cs_next_var` by
    metis_tac[allocation_trace_saved_bound] >>
  `!off. tuple_history (Var (STRING #"%" (toString j))) off r'` by
    (simp[tuple_history_def] >> metis_tac[allocation_trace_protected_tail]) >>
  first_x_assum irule >> simp[] >> conj_tac
  >- (rpt gen_tac >> strip_tac >> first_x_assum irule >> simp[] >> metis_tac[]) >>
  goal_assum (drule_at Any) >> simp[] >> metis_tac[]
QED
