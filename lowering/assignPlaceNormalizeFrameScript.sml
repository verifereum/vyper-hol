Theory assignPlaceNormalizeFrame
Ancestors
  placeRelayoutNormalizeFrame stmtSimDefs

(* Keep the original starting watermark: the fresh normalization buffer is
   disjoint from each old allocation whose bytes the caller must frame. *)
Theorem assign_place_normalize_framed_path:
  !ctx func cenv cx es ty sty stv dtv v val_op sa sm sb buf s sw.
    compile_alloc_buffer (type_memory_bytes cenv ty) sa = (buf, sm) /\
    compile_store_memory_typed cenv buf.buf_operand ty val_op sty sm = ((), sb) /\
    MEM (mk_inst sa.cs_next_id ALLOCA [Lit (n2w (type_memory_bytes cenv ty))]
      [STRING #"%" (toString sa.cs_next_var)]) (fn_insts func) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\
    (!x. val_op = Var x ==> not_fresh_at sa x) /\
    type_widens_to (get_tenv cx) sty ty /\
    evaluate_type (get_tenv cx) sty = SOME stv /\
    evaluate_type (get_tenv cx) ty = SOME dtv /\
    type_memory_bytes cenv ty = type_memory_size dtv /\
    type_memory_size dtv < dimword (:256) /\
    value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
    acyclic_struct_metadata cenv.ce_struct_fields /\
    sfields_tenv_consistent cenv.ce_struct_fields (get_tenv cx) /\
    (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
       ALL_DISTINCT (MAP FST fields) /\
       EVERY (\(fname, fty, sz). !tv. evaluate_type (get_tenv cx) fty = SOME tv ==>
         sz = type_memory_size tv) fields) /\
    stmt_state_rel ctx func cenv cx es s /\ eval_operand val_op s = SOME sw /\
    val_in_memory stv v (w2n sw) s.vs_memory /\
    w2n sw + type_memory_size stv < dimword (:256) /\
    ((?aid b len. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,len) /\
       b <= w2n sw /\ w2n sw + type_memory_size stv <= b + len) \/
     (?n b len. local_region cenv es.scopes s n b len /\
       b <= w2n sw /\ w2n sw + type_memory_size stv <= b + len)) /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?u w. gas_marked_path F ctx func s 0 (OK u) /\
      stmt_state_rel ctx func cenv cx es u /\
      eval_operand buf.buf_operand u = SOME w /\
      w2n w + type_memory_size dtv < dimword (:256) /\
      val_in_memory dtv v (w2n w) u.vs_memory /\
      FLOOKUP u.vs_allocas sa.cs_next_id = SOME (w2n w, type_memory_size dtv) /\
      (!x. not_fresh_at sa x ==> lookup_var x u = lookup_var x s) /\
      (!aid entry. FLOOKUP s.vs_allocas aid = SOME entry ==>
        FLOOKUP u.vs_allocas aid = SOME entry) /\
      (!off len. off + len <= w2n w \/ w2n w + type_memory_size dtv <= off ==>
        mem_bytes_at off len u.vs_memory = mem_bytes_at off len s.vs_memory) /\
      (!aid b len. aid < sa.cs_next_id /\ FLOOKUP s.vs_allocas aid = SOME (b,len) ==>
        regions_disjoint (w2n w) (type_memory_size dtv) b len) /\
      (!name b len. local_region cenv es.scopes s name b len ==>
        regions_disjoint (w2n w) (type_memory_size dtv) b len) /\
      ~u.vs_halted /\ u.vs_current_bb = sb.cs_current_bb /\
      u.vs_inst_idx = LENGTH sb.cs_current_insts /\
      alloca_frame cenv es sa s cenv es u
Proof
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all place_normalize_framed_path >> strip_tac >>
  `alloca_frame cenv es sa s cenv es u` by
    (irule alloca_frame_of_mem_frame >>
     simp[] >>
     (reverse conj_tac >- metis_tac[]) >>
     rpt strip_tac >>
     `regions_disjoint (w2n w) (type_memory_size dtv) off sz` by metis_tac[] >>
     gvs[loweringStateRelDefsTheory.regions_disjoint_def]) >>
  qexistsl_tac [`u`, `w`] >> asm_rewrite_tac[]
QED
