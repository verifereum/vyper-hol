(* Nominal struct normalization uses the compiler's original source table.
   Widening into StructT is nominal (typed_copy_struct_widening), so the
   metadata correspondence is equality, not a permutation of field names. *)
Theory annAssignTypedCopyStructPtr
Ancestors
  annAssignTypedCopyTuplePtr typedNormalizeFields typedMemoryCopy
  context compileEnv valueEncodingDefs valueEncoding fragGasPathPtr
  ptrDiscipline venomState bodyPtrDefs finite_map words

Theorem annassign_struct_copy_counted_ambient_ptr:
  !ce D ctx PG R.
    (!dt st dtv stv dp sp sa sb fn G tn s b a v.
      R dt st dtv stv /\
      compile_store_memory_typed ce (Var dp) dt (Var sp) st sa = ((),sb) /\
      fn_has_code sa sb fn /\ s.vs_current_bb = sa.cs_current_bb /\
      s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
      ~ctx_has_dalloca ctx /\ not_fresh_at sa dp /\ not_fresh_at sa sp /\
      lookup_var dp s = SOME b /\ lookup_var sp s = SOME a /\
      ptr_covers G tn dp s (type_memory_bytes ce dt) /\
      ptr_covers G tn sp s (type_memory_bytes ce st) /\
      type_memory_bytes ce dt = type_memory_size dtv /\
      type_memory_bytes ce st = type_memory_size stv /\
      w2n b + type_memory_size dtv < dimword (:256) /\
      w2n a + type_memory_size stv < dimword (:256) /\
      (w2n b + type_memory_size dtv <= w2n a \/
       w2n a + type_memory_size stv <= w2n b) /\
      val_wf dtv v /\ val_wf stv v /\
      (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
           val_in_memory stv v (w2n a) m) ==>
      cs_extends sa sb /\
      ?H tm t.
        gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t) /\
        t.vs_current_bb = sb.cs_current_bb /\
        t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~t.vs_halted /\
        t.vs_prev_bb = s.vs_prev_bb /\
        typed_copy_state_frame sa (w2n b) (type_memory_size dtv) s t /\
        tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
        (!x. not_fresh_at sa x ==>
          lookup_var x t = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
          op_taint tm (Var x) = op_taint tn (Var x)) /\
        (!i. ~(w2n b <= i /\ i < w2n b + type_memory_size dtv) ==>
          mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory /\
          (i IN tm.t_mem <=> i IN tn.t_mem)) /\
        (!m. mem_agree_outside tm.t_mem t.vs_memory m ==>
          val_in_memory dtv v (w2n b) m)) ==>
    !fields source_fields tvs vs dst src doff soff sa sz fn G tn s b a nd ns.
      (!name ty n. MEM (name,ty,n) fields ==>
        ALOOKUP source_fields name = SOME (ty,n) /\ n = type_memory_bytes ce ty) /\
      LENGTH tvs = LENGTH fields /\ LENGTH vs = LENGTH fields /\
      (!k. k < LENGTH fields ==>
        R (FST (SND (EL k fields))) (FST (SND (EL k fields)))
          (EL k tvs) (EL k tvs) /\
        type_memory_bytes ce (FST (SND (EL k fields))) = type_memory_size (EL k tvs)) /\
      tuple_val_wf vs tvs /\
      compile_struct_typed_copy ce (Var dst) (Var src) fields source_fields
        doff soff sa = ((),sz) /\
      fn_has_code sa sz fn /\ s.vs_current_bb = sa.cs_current_bb /\
      s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
      ~ctx_has_dalloca ctx /\ not_fresh_at sa dst /\ not_fresh_at sa src /\
      lookup_var dst s = SOME b /\ lookup_var src s = SOME a /\
      ptr_covers G tn dst s nd /\ ptr_covers G tn src s ns /\
      doff + type_memory_size_list tvs <= nd /\
      soff + type_memory_size_list tvs <= ns /\
      w2n b + nd < dimword (:256) /\ w2n a + ns < dimword (:256) /\
      (w2n a + ns <= w2n b \/ w2n b + nd <= w2n a) /\
      (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
        fields_in_memory (ZIP (MAP FST fields,vs)) (ZIP (MAP FST fields,tvs))
          (w2n a + soff) m) ==>
      cs_extends sa sz /\
      ?H tm t.
        gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t) /\
        t.vs_current_bb = sz.cs_current_bb /\
        t.vs_inst_idx = LENGTH sz.cs_current_insts /\ ~t.vs_halted /\
        t.vs_prev_bb = s.vs_prev_bb /\
        typed_copy_state_frame sa (w2n b + doff) (type_memory_size_list tvs) s t /\
        tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
        (!x. not_fresh_at sa x ==>
          lookup_var x t = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
          op_taint tm (Var x) = op_taint tn (Var x)) /\
        (!i. ~(w2n b + doff <= i /\ i < w2n b + doff + type_memory_size_list tvs) ==>
          mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory /\
          (i IN tm.t_mem <=> i IN tn.t_mem)) /\
        (!m. mem_agree_outside tm.t_mem t.vs_memory m ==>
          fields_in_memory (ZIP (MAP FST fields,vs)) (ZIP (MAP FST fields,tvs))
            (w2n b + doff) m)
Proof
  rpt gen_tac >> disch_then (mp_tac o MATCH_MP annassign_typed_copy_fields_counted_ambient_ptr) >>
  disch_then (mk_asm "loop") >> rpt gen_tac >> strip_tac >>
  `compile_typed_copy_fields ce (Var dst) (Var src)
     (MAP (FST o SND) fields) (MAP (FST o SND) fields) doff soff sa = ((),sz)` by
    (drule normalize_struct_as_fields >> disch_then (fn th => rewrite_tac[GSYM th]) >> simp[]) >>
  asm_x "loop" (fn th =>
    qpat_assum `compile_typed_copy_fields ce _ _ _ _ _ _ sa = ((),sz)`
      (mp_then (Pos (el 8)) mp_tac th)) >>
  disch_then (qspecl_then [`tvs`, `tvs`, `vs`] mp_tac) >>
  simp[typed_copy_fields_tuple_zip] >>
  disch_then (irule o SRULE []) >>
  simp[val_wf_def, listTheory.EL_MAP] >>
  qexistsl_tac [`nd`, `ns`] >>
  gvs[typed_copy_fields_tuple_zip]
QED
