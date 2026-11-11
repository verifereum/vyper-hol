(* Conditional fixed-array normalization with counted pointer execution. *)
Theory annAssignTypedCopyFixedPtr
Ancestors
  annAssignTypedCopyFixedMetadataPtr annAssignTypedCopyFixedControlPtr
  annAssignTypedCopyArrayTraversalPtr annAssignTypedCopyAtomsPtr
  typedMemoryCopy bodyPtrStructLitMonotoneRepresentation
  context compileEnv fragExec fragGasPathPtr valueEncodingDefs valueEncoding
  venomState words arithmetic list bodyPtrDefs

(* The bulk compiler branch is a single memory copy, with its complete
   ambient resource frame.  tv describes the represented whole object. *)
Theorem annassign_sarray_bulk_counted[local]:
  !ce dst dt src st n sa sb fn s b a G tn D ctx PG tv v.
    compile_copy_sarray_typed ce (Var dst) dt (Var src) st n sa = ((),sb) /\
    type_memory_bytes ce dt = type_memory_bytes ce st /\
    ~is_abi_dynamic ce.ce_struct_fields dt /\
    n * type_memory_bytes ce dt < dimword (:256) /\
    fn_has_code sa sb fn /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
    ~ctx_has_dalloca ctx /\
    ptr_covers G tn dst s (n * type_memory_bytes ce dt) /\
    ptr_covers G tn src s (n * type_memory_bytes ce dt) /\
    lookup_var dst s = SOME b /\ lookup_var src s = SOME a /\
    val_wf tv v /\ val_footprint tv v <= n * type_memory_bytes ce dt /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
      val_in_memory tv v (w2n a) m) ==>
    ?H tm t.
      gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t) /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~t.vs_halted /\
      typed_copy_state_frame sa (w2n b) (n * type_memory_bytes ce dt) s t /\
      (!m. mem_agree_outside tm.t_mem t.vs_memory m ==>
        val_in_memory tv v (w2n b) m) /\
      tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
      (!x. lookup_var x t = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
        op_taint tm (Var x) = op_taint tn (Var x)) /\
      (!i. ~(w2n b <= i /\ i < w2n b + n * type_memory_bytes ce dt) ==>
        mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory /\
        (i IN tm.t_mem <=> i IN tn.t_mem))
Proof
  rpt gen_tac >> strip_tac >>
  `compile_copy_memory (Var dst) (Var src) (n * type_memory_bytes ce dt) sa = ((),sb)` by
    (qpat_x_assum `compile_copy_sarray_typed _ _ _ _ _ _ _ = _` mp_tac >>
     simp[Once compile_store_memory_typed_def]) >>
  drule_all annassign_copy_memory_counted_ambient_ptr >>
  disch_then (qspecl_then [`D`,`PG`] strip_assume_tac) >>
  qexistsl_tac [`Gf`,`tf`,`u`] >> simp[]
QED
