(* Join static flat copying and the indexed counted loop. *)
Theory typedCopyFixedArrayConditionalPathPtr
Ancestors typedCopyFixedArraySlowPathPtr typedCopyFixedArrayFastPathPtr
 typedCopyFixedArrayCountBoundPtr

Theorem compile_copy_sarray_typed_robust_path_ptr_conditional:
 !D ctx fn PG ce tenv dty sty.
 (!N i S B stv dtv V tn tn' mem mem'.
   i < N /\
   (S + N * type_memory_size stv <= B \/ B + N * type_memory_size dtv <= S) /\
   (!j. j < N ==> val_wf stv (V j) /\ val_wf dtv (V j)) /\
   (!x. ~(B + i * type_memory_size dtv <= x /\
           x < B + (i+1) * type_memory_size dtv) ==>
     mem_bytes_at x 1 mem' = mem_bytes_at x 1 mem /\ (x IN tn' <=> x IN tn)) /\
   (!j. j < N ==> !m. mem_agree_outside tn mem m ==>
     val_in_memory stv (V j) (S + j * type_memory_size stv) m) /\
   (!j. j < i ==> !m. mem_agree_outside tn mem m ==>
     val_in_memory dtv (V j) (B + j * type_memory_size dtv) m) /\
   (!m. mem_agree_outside tn' mem' m ==>
     val_in_memory dtv (V i) (B + i * type_memory_size dtv) m) ==>
   (!j. j < N ==> !m. mem_agree_outside tn' mem' m ==>
     val_in_memory stv (V j) (S + j * type_memory_size stv) m) /\
   (!j. j < i+1 ==> !m. mem_agree_outside tn' mem' m ==>
     val_in_memory dtv (V j) (B + j * type_memory_size dtv) m)) ==>
 (!cd cs sa sb Gh th sh aw bw dtv stv v.
   acyclic_struct_metadata ce.ce_struct_fields /\
   sfields_tenv_consistent ce.ce_struct_fields tenv /\
   (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
    ALL_DISTINCT (MAP FST fields) /\
    EVERY (\(fname,fty,sz). !tv. evaluate_type tenv fty = SOME tv ==>
      sz = type_memory_size tv) fields) /\
   type_widens_to tenv sty dty /\ evaluate_type tenv sty = SOME stv /\
   evaluate_type tenv dty = SOME dtv /\
   value_has_type stv v /\ value_has_type dtv v /\ val_wf stv v /\ val_wf dtv v /\
   compile_store_memory_typed ce (Var cd) dty (Var cs) sty sa = ((),sb) /\
   not_fresh_at sa cd /\ not_fresh_at sa cs /\
   lookup_var cs sh = SOME aw /\ lookup_var cd sh = SOME bw /\
   ptr_covers Gh th cs sh (type_memory_bytes ce sty) /\
   ptr_covers Gh th cd sh (type_memory_bytes ce dty) /\
   w2n aw + type_memory_bytes ce sty < dimword(:256) /\
   w2n bw + type_memory_bytes ce dty < dimword(:256) /\
   (w2n aw + type_memory_bytes ce sty <= w2n bw \/
    w2n bw + type_memory_bytes ce dty <= w2n aw) /\
   fn_has_code sa sb fn /\ sh.vs_current_bb = sa.cs_current_bb /\
   sh.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~sh.vs_halted /\
   ~ctx_has_dalloca ctx /\
   (!m. mem_agree_outside th.t_mem sh.vs_memory m ==>
     val_in_memory stv v (w2n aw) m) ==>
   ?Gf tnf sf.
   gas_path_ptr D 0 ctx fn PG Gh th sh 0 Gf tnf (OK sf) /\
   sf.vs_current_bb = sb.cs_current_bb /\
   sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
   (sf with <|vs_vars := sh.vs_vars; vs_memory := sh.vs_memory;
    vs_prev_bb := sh.vs_prev_bb; vs_current_bb := sh.vs_current_bb;
    vs_inst_idx := sh.vs_inst_idx|>) = sh /\
   tnf.t_stor = th.t_stor /\ tnf.t_trans = th.t_trans /\ tnf.t_imm = th.t_imm /\
   (!p. not_fresh_at sa p ==>
    lookup_var p sf = lookup_var p sh /\ FLOOKUP Gf p = FLOOKUP Gh p /\
    op_taint tnf (Var p) = op_taint th (Var p)) /\
   (!i. ~(w2n bw <= i /\ i < w2n bw + type_memory_bytes ce dty) ==>
    mem_bytes_at i 1 sf.vs_memory = mem_bytes_at i 1 sh.vs_memory /\
    (i IN tnf.t_mem <=> i IN th.t_mem)) /\
   (!m. mem_agree_outside tnf.t_mem sf.vs_memory m ==>
    val_in_memory dtv v (w2n bw) m)) ==>
 !N sa sz G tn s dst src a b stv dtv v.
 acyclic_struct_metadata ce.ce_struct_fields /\
 sfields_tenv_consistent ce.ce_struct_fields tenv /\
 (!name fields. FLOOKUP ce.ce_struct_fields name = SOME fields ==>
  ALL_DISTINCT (MAP FST fields) /\
  EVERY (\(fname,fty,sz). !tv. evaluate_type tenv fty = SOME tv ==>
   sz = type_memory_size tv) fields) /\
 type_widens_to tenv sty dty /\
 evaluate_type tenv sty = SOME stv /\ evaluate_type tenv dty = SOME dtv /\
 value_has_type (ArrayTV stv (Fixed N)) v /\
 value_has_type (ArrayTV dtv (Fixed N)) v /\
 val_wf (ArrayTV stv (Fixed N)) v /\ val_wf (ArrayTV dtv (Fixed N)) v /\
 compile_copy_sarray_typed ce (Var dst) dty (Var src) sty N sa = ((),sz) /\
 not_fresh_at sa dst /\ not_fresh_at sa src /\
 lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
 ptr_covers G tn src s (N * type_memory_bytes ce sty) /\
 ptr_covers G tn dst s (N * type_memory_bytes ce dty) /\
 w2n a + N * type_memory_bytes ce sty < dimword(:256) /\
 w2n b + N * type_memory_bytes ce dty < dimword(:256) /\
 (w2n a + N * type_memory_bytes ce sty <= w2n b \/
  w2n b + N * type_memory_bytes ce dty <= w2n a) /\
 fn_has_code sa sz fn /\ s.vs_current_bb = sa.cs_current_bb /\
 s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\ ~ctx_has_dalloca ctx /\
 (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
  val_in_memory (ArrayTV stv (Fixed N)) v (w2n a) m) ==>
 ?Gf tnf sf.
 gas_path_ptr D 0 ctx fn PG G tn s 0 Gf tnf (OK sf) /\
 sf.vs_current_bb = sz.cs_current_bb /\
 sf.vs_inst_idx = LENGTH sz.cs_current_insts /\ ~sf.vs_halted /\
 (sf with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
   vs_prev_bb := s.vs_prev_bb; vs_current_bb := s.vs_current_bb;
   vs_inst_idx := s.vs_inst_idx|>) = s /\
 tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\ tnf.t_imm = tn.t_imm /\
 (!p. not_fresh_at sa p ==>
  lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
  op_taint tnf (Var p) = op_taint tn (Var p)) /\
 (!i. ~(w2n b <= i /\ i < w2n b + N * type_memory_bytes ce dty) ==>
  mem_bytes_at i 1 sf.vs_memory = mem_bytes_at i 1 s.vs_memory /\
  (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
 (!m. mem_agree_outside tnf.t_mem sf.vs_memory m ==>
  val_in_memory (ArrayTV dtv (Fixed N)) v (w2n b) m)
Proof
 ntac 8 gen_tac >> disch_then (mk_asm "indexed") >>
 disch_then (mk_asm "child") >> rpt gen_tac >>
 disch_then (map_every assume_tac o CONJUNCTS) >>
 Cases_on `type_memory_bytes ce dty = type_memory_bytes ce sty /\
   ~is_abi_dynamic ce.ce_struct_fields dty`
 >- (irule compile_copy_sarray_typed_fast_robust_path_ptr >> simp[] >> metis_tac[]) >>
 `N < dimword(:256)` by
   (irule typed_copy_sarray_slow_count_bound >>
    metis_tac[]) >>
 asm "indexed" mp_tac >>
 disch_then (mp_then Any mp_tac compile_copy_sarray_typed_slow_robust_path_ptr_conditional) >>
 disch_then (fn th => asm "child" (mp_then (Pos hd) mp_tac th)) >>
 disch_then irule >> simp[] >> metis_tac[]
QED
