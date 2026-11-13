(* Fixed-array specialization of the shared indexed runtime path. *)
Theory typedCopyFixedArraySlowPathPtr
Ancestors typedCopyIndexedLoopPathPtr typedCopyLoopCompilerBoundaryPtr
  typedCopyLoopLayoutPtr
  typedMemoryCopy

Theorem compile_copy_sarray_typed_slow_robust_path_ptr_conditional:
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
 ~(type_memory_bytes ce dty = type_memory_bytes ce sty /\
   ~is_abi_dynamic ce.ce_struct_fields dty) /\ N < dimword(:256) /\
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
 drule_all compile_copy_sarray_typed_loop_layout >> strip_tac >>
 rename1 `compile_store_memory_typed ce (Var dp) dty (Var sp) sty si = ((),se)` >>
 `si.cs_next_var = sa.cs_next_var + 7` by simp[] >>
 drule_all typed_copy_loop_register_boundaries >> strip_tac >>
 drule_at (Pat `compile_store_memory_typed _ _ _ _ _ _ = _`)
   typed_copy_loop_slice_locations >>
 disch_then (qspecl_then [`sa`, `sz`, `HD (TL si.cs_blocks)`,
   `HD si.cs_blocks`, `HD sz.cs_blocks`, `fn`] mp_tac) >>
 impl_tac >-
   (qpat_assum `fn_has_code sa sz fn` (fn th => rewrite_tac[th]) >>
    qpat_assum `si = _` (fn th => simp_tac (srw_ss()) [th]) >>
    qpat_assum `sb = _` (fn th => simp_tac (srw_ss()) [th]) >>
    qpat_assum `sc = _` (fn th => simp_tac (srw_ss()) [th]) >>
    qpat_assum `sz = _` (fn th => simp_tac (srw_ss()) [th]) >>
    qpat_assum `tail = _` (fn th => simp_tac (srw_ss()) [th])) >> strip_tac >>
 `type_memory_bytes ce sty = type_memory_size stv /\
  type_memory_bytes ce dty = type_memory_size dtv` by
   (conj_tac >> irule typed_copy_memory_size >> qexists_tac `tenv` >>
    simp[] >> metis_tac[]) >>
 qpat_assum `value_has_type (ArrayTV stv (Fixed N)) v` mp_tac >>
 Cases_on `v` >> simp[NoAsms, vyperTypingTheory.value_has_type_def] >>
 rename1 `ArrayV av` >> Cases_on `av` >>
 simp[NoAsms, vyperTypingTheory.value_has_type_def] >> strip_tac >>
 rename1 `SArrayV kvs` >>
 qabbrev_tac `V = \j. case ALOOKUP kvs j of NONE => default_value stv | SOME v => v` >>
 `!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
   (!j. j < N ==> val_wf stv (V j) /\ val_wf dtv (V j) /\
     val_in_memory stv (V j) (w2n a + j * type_memory_size stv) m) /\
   (!mem' off. (!j. j < N ==> val_in_memory dtv (V j)
      (off + j * type_memory_size dtv) mem') ==>
     val_in_memory (ArrayTV dtv (Fixed N)) (ArrayV (SArrayV kvs)) off mem')` by
   (gen_tac >> strip_tac >>
    qpat_x_assum `!m. _ ==> val_in_memory (ArrayTV stv (Fixed N)) _ _ _`
      (qspec_then `m` mp_tac) >> asm_rewrite_tac[] >> strip_tac >>
    drule_all typed_copy_sarray_representation >> simp[Abbr `V`]) >>
 `!j. j < N ==> value_has_type stv (V j) /\ value_has_type dtv (V j) /\
   val_wf stv (V j) /\ val_wf dtv (V j)` by suspend "element_types" >>
 pop_assum (mk_asm "elements") >>
 `si.cs_current_bb = body' /\ LENGTH si.cs_current_insts = 4 /\
  sz.cs_current_bb = exit /\ LENGTH sz.cs_current_insts = 0 /\
  (HD (TL si.cs_blocks)).bb_label = sa.cs_current_bb /\
  (HD si.cs_blocks).bb_label = cond /\
  (HD sz.cs_blocks).bb_label = se.cs_current_bb /\
  (HD (TL si.cs_blocks)).bb_instructions = sa.cs_current_insts ++
   [mk_inst sa.cs_next_id ASSIGN [Lit 0w] [ctr];
    mk_inst (sa.cs_next_id+1) JMP [Label cond] []] /\
  (HD si.cs_blocks).bb_instructions =
   [mk_inst sc.cs_next_id LT [Var ctr;Lit (n2w N)] [lt];
    mk_inst (sc.cs_next_id+1) ISZERO [Var lt] [done];
    mk_inst (sc.cs_next_id+2) JNZ [Var done;Label exit;Label body'] []] /\
  (HD sz.cs_blocks).bb_instructions = se.cs_current_insts ++
   [mk_inst se.cs_next_id ADD [Var ctr;Lit 1w] [STRCAT "%" (toString se.cs_next_var)];
    mk_inst (se.cs_next_id+1) ASSIGN [Var (STRCAT "%" (toString se.cs_next_var))] [ctr];
    mk_inst (se.cs_next_id+2) JMP [Label cond] []]` by
   (qpat_assum `si = _` (fn th => simp_tac (srw_ss()) [th]) >>
    qpat_assum `sb = _` (fn th => simp_tac (srw_ss()) [th]) >>
    qpat_assum `sc = _` (fn th => simp_tac (srw_ss()) [th]) >>
    qpat_assum `sz = _` (fn th => simp_tac (srw_ss()) [th]) >>
    qpat_assum `tail = _` (fn th => simp_tac (srw_ss()) [th])) >>
 `lookup_block s.vs_current_bb fn.fn_blocks = SOME (HD (TL si.cs_blocks)) /\
  lookup_block cond fn.fn_blocks = SOME (HD si.cs_blocks) /\
  lookup_block se.cs_current_bb fn.fn_blocks = SOME (HD sz.cs_blocks) /\
  lookup_block body' fn.fn_blocks = SOME bb` by metis_tac[] >>
 qpat_assum `isPREFIX si.cs_current_insts bb.bb_instructions`
   (strip_assume_tac o REWRITE_RULE [rich_listTheory.IS_PREFIX_APPEND]) >>
 rename1 `bb.bb_instructions = si.cs_current_insts ++ suffix` >>
 `bb.bb_instructions =
   [mk_inst sb.cs_next_id MUL [Var ctr;Lit (n2w (type_memory_bytes ce sty))] [so];
    mk_inst (sb.cs_next_id+1) MUL [Var ctr;Lit (n2w (type_memory_bytes ce dty))] [doff];
    mk_inst (sb.cs_next_id+2) ADD [Var src;Var so] [sp];
    mk_inst (sb.cs_next_id+3) ADD [Var dst;Var doff] [dp]] ++ suffix` by
   (qpat_assum `bb.bb_instructions = _ ++ _` (fn th => rewrite_tac[th]) >>
    qpat_assum `si = _` (fn th => simp_tac (srw_ss()) [th])) >>
 asm "indexed" mp_tac >>
 disch_then (mp_then Any mp_tac typed_copy_indexed_loop_path_ptr_conditional) >>
 disch_then (fn th => asm "child" (mp_then (Pos hd) mp_tac th)) >>
 disch_then (drule_at (Pat `compile_store_memory_typed _ _ _ _ _ _ = _`)) >>
 disch_then (fn th => asm "elements" (mp_then Any mp_tac th)) >>
 disch_then (fn th => qpat_assum `ptr_covers G tn src s _`
   (mp_then (Pat `ptr_covers _ _ src _ _`) mp_tac th)) >>
 disch_then (fn th => qpat_assum `ptr_covers G tn dst s _`
   (mp_then (Pat `ptr_covers _ _ dst _ _`) mp_tac th)) >>
 disch_then (qspec_then `sa` mp_tac) >>
 disch_then (fn th => qpat_assum `lookup_var src s = SOME a`
   (mp_then (Pat `lookup_var src _ = _`) mp_tac th)) >>
 disch_then (fn th => qpat_assum `lookup_var dst s = SOME b`
   (mp_then (Pat `lookup_var dst _ = _`) mp_tac th)) >>
 disch_then (fn th => qpat_assum `(HD si.cs_blocks).bb_instructions = _`
   (mp_then (Pat `_.bb_instructions = [mk_inst _ LT _ _; _; _]`) mp_tac th)) >>
 disch_then (fn th => qpat_assum `(HD (TL si.cs_blocks)).bb_instructions = _`
   (mp_then (Pat `_.bb_instructions = _ ++ [mk_inst _ ASSIGN _ _; _]`) mp_tac th)) >>
 disch_then (fn th => qpat_assum `(HD sz.cs_blocks).bb_instructions = _`
   (mp_then (Pat `_.bb_instructions = _ ++ [mk_inst _ ADD _ _; _; _]`) mp_tac th)) >>
 disch_then (fn th => qpat_assum `bb.bb_instructions = [mk_inst _ MUL _ _; _; _; _] ++ _`
   (mp_then (Pat `_.bb_instructions = [mk_inst _ MUL _ _; _; _; _] ++ _`) mp_tac th)) >>
 map_every (fn pat => qpat_x_assum pat kall_tac)
   [`si = _`, `sb = _`, `sc = _`, `sz = _`, `tail = _`,
    `cond = _`, `body' = _`, `exit = _`, `ctr = _`, `lt = _`, `done = _`,
    `so = _`, `doff = _`, `sp = _`, `dp = _`] >>
 impl_tac >- (simp[venomStateTheory.eval_operand_def,
   ptrDisciplineTheory.op_taint_def, ptrDisciplineTheory.op_prov_def] >>
   conj_tac >- first_assum ACCEPT_TAC >>
   conj_tac >- (qpat_x_assum `ALL_DISTINCT _` mp_tac >> simp[]) >>
   qpat_x_assum `!p. not_fresh_at sa p ==> _` mp_tac >>
   simp[] >> metis_tac[]) >>
 strip_tac >> qexistsl_tac [`Gf`, `tnf`, `sf`] >> simp[] >>
 conj_tac >-
   (qpat_x_assum `sf with <|vs_vars := _; vs_memory := _; vs_prev_bb := _;
      vs_current_bb := _; vs_inst_idx := _|> = s` mp_tac >>
    simp[venomStateTheory.venom_state_component_equality]) >>
 qpat_x_assum `!m. mem_agree_outside tn.t_mem s.vs_memory m ==> _`
   (qspec_then `s.vs_memory` mp_tac) >>
 simp[bodyPtrDefsTheory.mem_agree_outside_def] >> strip_tac >>
 rpt strip_tac >> first_x_assum irule >>
 rpt strip_tac >> qpat_x_assum `!j. j < N ==> !m. _` drule >>
 simp[bodyPtrDefsTheory.mem_agree_outside_def]
QED

Resume compile_copy_sarray_typed_slow_robust_path_ptr_conditional[element_types]:
 qpat_assum `!m. mem_agree_outside tn.t_mem s.vs_memory m ==> _`
   (qspec_then `s.vs_memory` mp_tac) >>
 simp[bodyPtrDefsTheory.mem_agree_outside_def] >> strip_tac >>
 gen_tac >> strip_tac >>
 `value_has_type stv (V j)` by
   (simp[Abbr `V`] >> Cases_on `ALOOKUP kvs j` >> simp[]
    >- metis_tac[vyperTypeDefaultsTheory.default_value_has_type_thm]
    >> metis_tac[valueEncodingProofsTheory.sparse_has_type_lookup]) >>
 `value_has_type dtv (V j)` by
   (drule_all vyperTypeArgFitsTheory.type_widens_to_value_has_type >> simp[]) >>
 metis_tac[]
QED

Finalise compile_copy_sarray_typed_slow_robust_path_ptr_conditional
