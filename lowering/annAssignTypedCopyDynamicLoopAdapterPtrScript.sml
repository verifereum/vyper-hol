(* Compiler-relative unequal-layout dynamic payload execution. *)
Theory annAssignTypedCopyDynamicLoopAdapterPtr
Ancestors
  annAssignTypedCopyDynamicSlowAdmissiblePtr

Theorem annassign_dynamic_slow_payload_counted:
  !ce dst_op dt cap src_op st sa sb fn s src dst L f stv dtv G tn D ctx PG.
    ~(type_memory_bytes ce dt = type_memory_bytes ce st /\ dt = st) /\
    compile_copy_dynarray_typed ce dst_op dt cap src_op st sa = ((),sb) /\
    fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\
    type_memory_bytes ce st = type_memory_size stv /\
    type_memory_bytes ce dt = type_memory_size dtv /\
    0 < type_memory_size stv /\ 0 < type_memory_size dtv /\
    src + L * type_memory_size stv < dimword(:256) /\
    dst + L * type_memory_size dtv < dimword(:256) /\
    (src + L * type_memory_size stv <= dst \/
     dst + L * type_memory_size dtv <= src) /\ L < dimword(:256) /\
    (!i. i < L ==> val_wf stv (f i) /\ val_wf dtv (f i)) /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts+7 /\ ~s.vs_halted /\
    lookup_var ("%" ++ toString sa.cs_next_var) s = SOME (n2w L) /\
    op_taint tn (Var ("%" ++ toString sa.cs_next_var)) = {} /\
    FLOOKUP G ("%" ++ toString sa.cs_next_var) = NONE /\
    lookup_var ("%" ++ toString (sa.cs_next_var+3)) s = SOME (n2w src) /\
    lookup_var ("%" ++ toString (sa.cs_next_var+4)) s = SOME (n2w dst) /\
    ptr_covers G tn ("%" ++ toString (sa.cs_next_var+3)) s (L * type_memory_size stv) /\
    ptr_covers G tn ("%" ++ toString (sa.cs_next_var+4)) s (L * type_memory_size dtv) /\
    (!i. i < L ==> !m. mem_agree_outside tn.t_mem s.vs_memory m ==>
      val_in_memory stv (f i) (src + i * type_memory_size stv) m) /\
    (!sc se xr yr u aw bw H tm v.
      compile_store_memory_typed ce (Var yr) dt (Var xr) st sc = ((),se) /\
      fn_has_code sc se fn /\ not_fresh_at sc xr /\ not_fresh_at sc yr /\
      u.vs_current_bb = sc.cs_current_bb /\
      u.vs_inst_idx = LENGTH sc.cs_current_insts /\ ~u.vs_halted /\
      lookup_var xr u = SOME aw /\ lookup_var yr u = SOME bw /\
      ptr_covers H tm xr u (type_memory_size stv) /\
      ptr_covers H tm yr u (type_memory_size dtv) /\
      w2n aw + type_memory_size stv < dimword(:256) /\
      w2n bw + type_memory_size dtv < dimword(:256) /\
      (w2n aw + type_memory_size stv <= w2n bw \/
       w2n bw + type_memory_size dtv <= w2n aw) /\
      val_wf stv v /\ val_wf dtv v /\
      (!m. mem_agree_outside tm.t_mem u.vs_memory m ==>
        val_in_memory stv v (w2n aw) m) ==>
      ?K tk z. gas_path_ptr D 0 ctx fn PG H tm u 0 K tk (OK z) /\
        z.vs_current_bb = se.cs_current_bb /\
        z.vs_inst_idx = LENGTH se.cs_current_insts /\ ~z.vs_halted /\
        typed_copy_state_frame sc (w2n bw) (type_memory_size dtv) u z /\
        (!m. mem_agree_outside tk.t_mem z.vs_memory m ==>
          val_in_memory dtv v (w2n bw) m) /\
        tk.t_stor = tm.t_stor /\ tk.t_trans = tm.t_trans /\ tk.t_imm = tm.t_imm /\
        (!x. not_fresh_at sc x ==>
          lookup_var x z = lookup_var x u /\ FLOOKUP K x = FLOOKUP H x /\
          op_taint tk (Var x) = op_taint tm (Var x)) /\
        (!i. ~(w2n bw <= i /\ i < w2n bw + type_memory_size dtv) ==>
          mem_bytes_at i 1 z.vs_memory = mem_bytes_at i 1 u.vs_memory /\
          (i IN tk.t_mem <=> i IN tm.t_mem))) ==>
    ?H tm t. gas_path_ptr D 0 ctx fn PG G tn s 0 H tm (OK t) /\
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~t.vs_halted /\
      (!m. mem_agree_outside tm.t_mem t.vs_memory m ==>
        typed_copy_index_prefix f dtv dst L L m) /\
      typed_copy_state_frame sa dst (L * type_memory_size dtv) s t /\
      (!i. ~(dst <= i /\ i < dst + L * type_memory_size dtv) ==>
        mem_bytes_at i 1 t.vs_memory = mem_bytes_at i 1 s.vs_memory /\
        (i IN tm.t_mem <=> i IN tn.t_mem)) /\
      tm.t_stor = tn.t_stor /\ tm.t_trans = tn.t_trans /\ tm.t_imm = tn.t_imm /\
      (!x. not_fresh_at sa x \/ x = "%" ++ toString (sa.cs_next_var+3) \/
        x = "%" ++ toString (sa.cs_next_var+4) \/ x = "%" ++ toString sa.cs_next_var ==>
        lookup_var x t = lookup_var x s /\ FLOOKUP H x = FLOOKUP G x /\
        op_taint tm (Var x) = op_taint tn (Var x))
Proof
  rpt gen_tac >> strip_tac >>
  match_mp_tac (Q.INST [`P` |-> `\v. T`] (SPEC_ALL annassign_dynamic_slow_payload_admissible_counted)) >>
  gvs[arithmeticTheory.ADD_COMM] >> gvs[]
QED
