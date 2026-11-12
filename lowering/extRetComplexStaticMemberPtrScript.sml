Theory extRetComplexStaticMemberPtr
Ancestors
  extRetComplexMemberStatePtr extRetSemanticResultPtr extRetChildNarrowFramePtr
  extRetDynamicBodyPtr extRetRecursiveResourcePtr extRetRecursiveFramePtr
  extRetFramedChildPtr extRetRecursiveChildPtr extRetScratchResourcePtr
  abiEncoderChildContext abiEncoderMemberCode emitHelper fragGasSeqPtr fragGasPathPtr
  abiEncoderInput allocaSiteResource bodyPtrDefs compileEnv fragExec
  vyperABI vyperTypeABI vyperTyping vyperValue
  venomState venomMemDefs ptrDiscipline valueEncoding words finite_map
  pred_set list rich_list arithmetic loweringStateRelDefs

Theorem encoder_complex_static_member_coordinates:
  encoder_complex_layout so ho ms hs tails dyn ns caps children
    sites a scap b dcap protected active cid cursor /\
  j < LENGTH ms /\ ~EL j dyn ==>
  caps j = EL j hs /\ EL j ns = EL j hs /\ EL j tails = 0 /\
  encoder_member_offset ho hs (j+1) =
    encoder_member_offset ho hs j + EL j hs /\
  encoder_member_offset ho hs j + caps j <= ho+SUM hs /\
  encoder_member_offset ho hs j + caps j <= dcap /\
  encoder_member_offset (ho+SUM hs) tails (j+1) =
    encoder_member_offset (ho+SUM hs) tails j
Proof
  strip_tac >>
  `LENGTH hs = LENGTH ms /\ LENGTH tails = LENGTH ms /\
   ho+SUM hs+SUM tails <= dcap /\
   EL j ns <= caps j /\ EL j ns = EL j hs /\ caps j <= EL j hs /\
   EL j tails = 0` by metis_tac[encoder_complex_layout_def] >>
  `SUM (TAKE j hs) + EL j hs <= SUM hs` by
    (mp_tac (Q.ISPECL [`\n:num. n`, `hs:num list`, `j:num`] abi_encoder_prefix_sum_bound) >> simp[]) >>
  `encoder_member_offset ho hs (j+1) =
     encoder_member_offset ho hs j + EL j hs /\
   encoder_member_offset (ho+SUM hs) tails (j+1) =
     encoder_member_offset (ho+SUM hs) tails j + EL j tails` by
    metis_tac[encoder_member_offset_step] >>
  fs[encoder_member_offset_def] >> decide_tac
QED

(* The source robustness boundary is independent of the current child. Its
   narrow frame also preserves all later members, including zero windows. *)
Theorem encoder_complex_static_unread_sources:
  encoder_complex_member_inv ctx fn sites protected
    src dst ip a b scap dcap active cid cursor
    so ho ms hs tails tv v j sa G tn s /\
  encoder_resource ctx fn childsites a scap protected sf /\
  regions_disjoint (a,scap) (dest,cap) /\
  mem_agree_outside (encoder_write_envelope childsites sf dest cap)
    sf.vs_memory s.vs_memory /\
  (!i. i NOTIN encoder_write_envelope childsites sf dest cap ==>
    (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
  (!i. j+1 <= i /\ i < LENGTH ms ==>
    val_wf (tv i) (v i) /\
    encoder_member_offset so ms i + val_footprint (tv i) (v i) <= scap) ==>
  !i mem. j+1 <= i /\ i < LENGTH ms /\
    mem_agree_outside tnf.t_mem sf.vs_memory mem ==>
    val_in_memory (tv i) (v i) (a+encoder_member_offset so ms i) mem
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  `val_wf (tv i) (v i) /\
   encoder_member_offset so ms i + val_footprint (tv i) (v i) <= scap` by
    metis_tac[] >>
  `!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    val_in_memory (tv i) (v i) (a+encoder_member_offset so ms i) m` by
    (fs[encoder_complex_member_inv_def] >>
     `j <= i` by decide_tac >> metis_tac[]) >>
  `a <= a+encoder_member_offset so ms i /\
   (a+encoder_member_offset so ms i)+val_footprint (tv i) (v i) <= a+scap` by
    decide_tac >>
  drule_all encoder_complex_unread_frame >> simp[]
QED

Theorem encoder_complex_registered_cell_excludes_scratch:
  alloca_inv s /\ FLOOKUP s.vs_allocas cid = SOME (cursor,32) /\
  cid NOTIN children /\ cursor <= i /\ i < cursor+32 ==>
  i NOTIN encoder_scratch_span children s
Proof
  strip_tac >>
  pure_rewrite_tac[encoder_scratch_span_def, GSPECIFICATION] >> BETA_TAC >>
  pure_rewrite_tac[pairTheory.PAIR_EQ, AND_CLAUSES] >> strip_tac >>
  pop_assum (strip_assume_tac o PURE_REWRITE_RULE [EQ_CLAUSES]) >>
  `cid <> id` by metis_tac[] >>
  `regions_disjoint (cursor,32) (b,n)` by
    (irule alloca_site_registered_disjoint >> metis_tac[]) >>
  fs[regions_disjoint_def] >> decide_tac
QED

Theorem encoder_complex_static_cursor_frame:
  alloca_inv sf /\ FLOOKUP sf.vs_allocas cid = SOME (cursor,32) /\
  cid NOTIN children /\ regions_disjoint (cursor,32) (dest,cap) /\
  mem_agree_outside (encoder_write_envelope children sf dest cap)
    sf.vs_memory s.vs_memory /\
  (!i. i NOTIN encoder_write_envelope children sf dest cap ==>
    (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
  (!i. cursor <= i /\ i < cursor+32 ==> i NOTIN tn.t_mem) ==>
  mload cursor sf = mload cursor s /\
  (!i. cursor <= i /\ i < cursor+32 ==> i NOTIN tnf.t_mem)
Proof
  strip_tac >> irule encoder_frame_clean_word >>
  qexistsl_tac [`tn`, `encoder_write_envelope children sf dest cap`] >> simp[] >>
  gen_tac >> strip_tac >>
  `i NOTIN encoder_scratch_span children sf` by
    (irule encoder_complex_registered_cell_excludes_scratch >> metis_tac[]) >>
  simp[encoder_write_envelope_def] >> fs[regions_disjoint_def] >> decide_tac
QED

Theorem encoder_complex_static_clean_prefixes:
  encoder_complex_layout so ho ms hs tails dyn ns caps children
    sites a scap b dcap protected active cid cursor /\
  j < LENGTH ms /\ ~EL j dyn /\
  encoder_resource ctx fn (children j) a scap protected sf /\
  mem_agree_outside
    (encoder_write_envelope (children j) sf
      (b+encoder_member_offset ho hs j) (caps j)) sf.vs_memory s.vs_memory /\
  (!i. i NOTIN encoder_write_envelope (children j) sf
      (b+encoder_member_offset ho hs j) (caps j) ==>
    (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
  (!i. b <= i /\ i < b+encoder_member_offset ho hs j ==> i NOTIN tn.t_mem) /\
  (!i. b+(ho+SUM hs) <= i /\
    i < b+encoder_member_offset (ho+SUM hs) tails j ==> i NOTIN tn.t_mem) /\
  (!i. b+encoder_member_offset ho hs j <= i /\
    i < b+encoder_member_offset ho hs j+EL j ns ==> i NOTIN tnf.t_mem) ==>
  (!i. b <= i /\ i < b+encoder_member_offset ho hs (j+1) ==> i NOTIN tnf.t_mem) /\
  (!i. b+(ho+SUM hs) <= i /\
    i < b+encoder_member_offset (ho+SUM hs) tails (j+1) ==> i NOTIN tnf.t_mem)
Proof
  strip_tac >> drule_all encoder_complex_static_member_coordinates >> strip_tac >>
  `?id p sz. MEM (id,p,sz) protected /\ p <= b /\ b+dcap <= p+sz` by
    metis_tac[encoder_complex_layout_def] >>
  `!i. b <= i /\ i < b+dcap ==>
    i NOTIN encoder_scratch_span (children j) sf` by
    (gen_tac >> strip_tac >>
     `p <= i /\ i < p+sz` by decide_tac >>
     metis_tac[encoder_complex_scratch_excludes_protected]) >>
  `encoder_member_offset (ho+SUM hs) tails j <= dcap` by
    (`j < LENGTH tails` by metis_tac[encoder_complex_layout_def] >>
     `SUM (TAKE j tails) + EL j tails <= SUM tails` by
       (mp_tac (Q.ISPECL [`\n:num. n`, `tails:num list`, `j:num`] abi_encoder_prefix_sum_bound) >> simp[]) >>
     fs[encoder_complex_layout_def, encoder_member_offset_def] >> decide_tac) >>
  conj_tac
  >- (gen_tac >> strip_tac >>
      Cases_on `i < b+encoder_member_offset ho hs j`
      >- (`i NOTIN encoder_write_envelope (children j) sf
             (b+encoder_member_offset ho hs j) (caps j)` by
            (simp[encoder_write_envelope_def] >> decide_tac) >> metis_tac[]) >>
      `b+encoder_member_offset ho hs j <= i /\
       i < b+encoder_member_offset ho hs j+EL j ns` by decide_tac >> metis_tac[]) >>
  gen_tac >> strip_tac >>
  `i NOTIN encoder_write_envelope (children j) sf
    (b+encoder_member_offset ho hs j) (caps j)` by
    (simp[encoder_write_envelope_def] >> decide_tac) >> metis_tac[]
QED

Theorem encoder_complex_static_invariant_advance:
  encoder_complex_layout so ho ms hs tails dyn ns caps children
    sites a scap b dcap protected active cid cursor /\
  j < LENGTH ms /\ ~EL j dyn /\
  encoder_complex_member_inv ctx fn sites protected src dst ip a b scap dcap
    active cid cursor so ho ms hs tails tv v j sa G tn s /\
  (!x. not_fresh_at sa x ==> not_fresh_at sb x) /\
  ~sf.vs_halted /\ encoder_resource ctx fn sites a scap protected sf /\
  encoder_dynamic_effect sa sites b dcap G tn s Gf tnf sf /\
  mem_agree_outside
    (encoder_write_envelope (children j) sf
      (b+encoder_member_offset ho hs j) (caps j)) sf.vs_memory s.vs_memory /\
  (!i. i NOTIN encoder_write_envelope (children j) sf
      (b+encoder_member_offset ho hs j) (caps j) ==>
    (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
  (!i. b+encoder_member_offset ho hs j <= i /\
    i < b+encoder_member_offset ho hs j+EL j ns ==> i NOTIN tnf.t_mem) /\
  (!i. j+1 <= i /\ i < LENGTH ms ==>
    val_wf (tv i) (v i) /\
    encoder_member_offset so ms i + val_footprint (tv i) (v i) <= scap) ==>
  encoder_complex_member_inv ctx fn sites protected src dst ip a b scap dcap
    active cid cursor so ho ms hs tails tv v (j+1) sb Gf tnf sf
Proof
  strip_tac >> drule_all encoder_complex_static_member_coordinates >> strip_tac >>
  `children j SUBSET sites` by metis_tac[encoder_complex_layout_def] >>
  `encoder_resource ctx fn (children j) a scap protected sf` by
    (irule encoder_resource_restrict >> metis_tac[]) >>
  `regions_disjoint (a,scap)
     (b+encoder_member_offset ho hs j,caps j)` by
    (fs[encoder_complex_layout_def, regions_disjoint_def] >> decide_tac) >>
  `!i mem. j+1 <= i /\ i < LENGTH ms /\
    mem_agree_outside tnf.t_mem sf.vs_memory mem ==>
    val_in_memory (tv i) (v i) (a+encoder_member_offset so ms i) mem` by
    (rpt gen_tac >> disch_tac >>
     irule encoder_complex_static_unread_sources >> metis_tac[]) >>
  `(!i. b <= i /\ i < b+encoder_member_offset ho hs (j+1) ==> i NOTIN tnf.t_mem) /\
   (!i. b+(ho+SUM hs) <= i /\
    i < b+encoder_member_offset (ho+SUM hs) tails (j+1) ==> i NOTIN tnf.t_mem)` by
    (irule encoder_complex_static_clean_prefixes >>
     metis_tac[encoder_complex_member_inv_def]) >>
  `active ==> mload cursor sf = mload cursor s /\
    (!i. cursor <= i /\ i < cursor+32 ==> i NOTIN tnf.t_mem)` by
    (strip_tac >>
     `alloca_inv sf` by
       (qpat_x_assum `encoder_resource ctx fn sites a scap protected sf` mp_tac >>
        simp_tac std_ss [encoder_resource_def, extRetScratchResourcePtrTheory.scratch_resource_def]) >>
     `FLOOKUP sf.vs_allocas cid = SOME (cursor,32) /\
      cid NOTIN children j /\ regions_disjoint (cursor,32)
        (b+encoder_member_offset ho hs j,caps j)` by
       (fs[encoder_complex_layout_def, encoder_complex_member_inv_def,
           encoder_dynamic_effect_def, regions_disjoint_def] >>
        metis_tac[LESS_EQ_ADD, LESS_EQ_TRANS, ADD_ASSOC]) >>
     irule encoder_complex_static_cursor_frame >>
     metis_tac[encoder_complex_member_inv_def]) >>
  Cases_on `active` >>
  gvs[encoder_complex_member_inv_def, encoder_dynamic_effect_def] >>
  rpt conj_tac >> rpt strip_tac >>
  gvs[ptr_covers_def, op_prov_def] >> metis_tac[]
QED

(* Source-aware version of the static narrow wrapper: the real ADD preserves
   the operands that the recursive source contract will subsequently read. *)
Theorem encoder_static_child_source_narrow_framed_counted_ptr[local]:
  compile_abi_encode_child (Var dst) src ei F h dp sa = (out,sb) /\
  fn_has_code sa sb fn /\ s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\ ~s.vs_halted /\
  ~ctx_has_dalloca ctx /\ lookup_var dst s = SOME (n2w b) /\
  ptr_covers G tn dst s cap /\ b+cap < dimword(:256) /\
  h+child_cap <= cap /\ children SUBSET sites /\
  encoder_resource ctx fn sites q source_len protected s /\
  (!head sc Gp tnp sp.
    emit_op ADD [Var dst; Lit (n2w h)] sa = (Var head,sc) /\
    compile_abi_encode_to_buf (Var head) src ei sc = (out,sb) /\
    sp.vs_current_bb = sc.cs_current_bb /\
    sp.vs_inst_idx = LENGTH sc.cs_current_insts /\ ~sp.vs_halted /\
    lookup_var head sp = SOME (n2w (b+h)) /\ ptr_covers Gp tnp head sp child_cap /\
    encoder_resource ctx fn children q source_len protected sp /\
    sp.vs_memory = s.vs_memory /\ tnp.t_mem = tn.t_mem /\
    sp.vs_allocas = s.vs_allocas /\
    (!x. not_fresh_at sa x ==>
      lookup_var x sp = lookup_var x s /\ FLOOKUP Gp x = FLOOKUP G x /\
      op_taint tnp (Var x) = op_taint tn (Var x)) ==>
    ?Gm tnm sm. encoder_framed_child_result D ctx fn PG sc sb children q
      source_len protected (b+h) child_cap out n cost Gp tnp sp Gm tnm sm) ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s cost Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\ ~sf.vs_halted /\
    eval_operand out sf = SOME (n2w n) /\ op_taint tnf out = {} /\
    (!i. b+h <= i /\ i < b+h+n ==> i NOTIN tnf.t_mem) /\
    encoder_resource ctx fn sites q source_len protected sf /\
    encoder_dynamic_effect sa sites b cap G tn s Gf tnf sf /\
    mem_agree_outside (encoder_write_envelope children sf (b+h) child_cap)
      sf.vs_memory s.vs_memory /\
    (!i. i NOTIN encoder_write_envelope children sf (b+h) child_cap ==>
      (i IN tnf.t_mem <=> i IN tn.t_mem))
Proof
  strip_tac >> drule_all abi_encoder_static_child_structural_context >> strip_tac >>
  `?hv. head = Var hv` by
    gvs[emit_op_def, comp_bind_def, comp_ignore_bind_def, fresh_var_def,
      fresh_id_def, emit_def, comp_return_def] >> gvs[] >>
  `w2n (n2w b : bytes32)+h < dimword(:256)` by
    (simp[w2n_n2w, LESS_MOD] >> decide_tac) >>
  `h+child_cap <= cap` by decide_tac >>
  drule_all (extRetBulkCopyCountedPtrTheory.emit_bulk_offset_ambient_counted_ptr |>
    SPEC_ALL |> Q.INST [`n` |-> `child_cap`, `extent` |-> `cap`]) >>
  disch_then (qspecl_then [`PG`, `D`] strip_assume_tac) >>
  `encoder_resource ctx fn sites q source_len protected sf` by
    (irule encoder_resource_fields >> qexists_tac `s` >> simp[]) >>
  `encoder_resource ctx fn children q source_len protected sf` by
    (irule encoder_resource_restrict >> qexists_tac `sites` >> simp[]) >>
  qpat_x_assum `!Gp tnp sp. _`
    (qspecl_then [`Gf`, `tnf`, `sf`] mp_tac) >>
  (impl_tac >- (simp[w2n_n2w, LESS_MOD] >> metis_tac[])) >> strip_tac >>
  fs[encoder_framed_child_result_def, encoder_ambient_frame_def] >>
  `scratch_resource ctx fn sites q source_len sm` by
    (irule encoder_child_scratch_restore >>
     qexistsl_tac [`children`, `sf`] >> fs[encoder_resource_def]) >>
  `encoder_resource ctx fn sites q source_len protected sm` by
    (irule encoder_child_resource_restore >> simp[] >> qexists_tac `sf` >> simp[]) >>
  `encoder_write_envelope children sm (b+h) child_cap SUBSET
    encoder_write_envelope sites sm b cap` by
    (irule encoder_child_envelope_subset >> simp[]) >>
  `!x. not_fresh_at sa x ==> not_fresh_at prepared x` by
    (gvs[not_fresh_at_def] >> rpt strip_tac >> decide_tac) >>
  qexistsl_tac [`Gm`, `tnm`, `sm`] >>
  conj_tac >-
    (irule (gas_path_ptr_then |> Q.INST [`n` |-> `0`] |> SRULE []) >>
     qexistsl_tac [`Gf`, `sf`, `tnf`] >> simp[]) >>
  simp[encoder_dynamic_effect_def, encoder_ambient_frame_def] >> conj_tac >-
    (conj_tac >- (irule encoder_memory_frame_mono >> metis_tac[]) >>
     fs[SUBSET_DEF] >> metis_tac[]) >>
  fs[SUBSET_DEF] >> metis_tac[]
QED

Theorem encoder_complex_static_member_counted_ptr:
  encoder_complex_layout so ho ms hs tails dyn ns caps children
    sites a scap b dcap protected active cid cursor /\
  j < LENGTH ms /\ ~EL j dyn /\
  encoder_complex_member_inv ctx fn sites protected src dst ip a b scap dcap
    active cid cursor so ho ms hs tails tv v j sa G tn s /\
  not_fresh_at sa es /\
  lookup_var es s = SOME (n2w (a+encoder_member_offset so ms j)) /\
  ptr_covers G tn es s (EL j ms) /\
  (!i. j+1 <= i /\ i < LENGTH ms ==>
    val_wf (tv i) (v i) /\
    encoder_member_offset so ms i + val_footprint (tv i) (v i) <= scap) /\
  vyper_to_abi env ty (v j) = SOME av /\
  EL j ns = LENGTH (enc (vyper_to_abi_type env ty) av) /\
  compile_abi_encode_child (Var dst) (Var es) ei F
    (encoder_member_offset ho hs j) dp sa = (out,sb) /\
  fn_has_code sa sb fn /\ ~ctx_has_dalloca ctx /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  (!head sc Gp tnp sp.
    emit_op ADD [Var dst; Lit (n2w (encoder_member_offset ho hs j))] sa = (Var head,sc) /\
    compile_abi_encode_to_buf (Var head) (Var es) ei sc = (out,sb) /\
    sp.vs_current_bb = sc.cs_current_bb /\
    sp.vs_inst_idx = LENGTH sc.cs_current_insts /\ ~sp.vs_halted /\
    lookup_var head sp = SOME (n2w (b+encoder_member_offset ho hs j)) /\
    ptr_covers Gp tnp head sp (caps j) /\
    lookup_var es sp = SOME (n2w (a+encoder_member_offset so ms j)) /\
    ptr_covers Gp tnp es sp (EL j ms) /\
    (!mem. mem_agree_outside tnp.t_mem sp.vs_memory mem ==>
      val_in_memory (tv j) (v j) (a+encoder_member_offset so ms j) mem) /\
    encoder_resource ctx fn (children j) a scap protected sp ==>
    ?n Gm tnm sm. encoder_semantic_framed_result env ty (v j)
      D ctx fn PG sc sb (children j) a scap protected
      (b+encoder_member_offset ho hs j) (caps j) out n cost Gp tnp sp Gm tnm sm) ==>
  ?Gf tnf sf.
    gas_path_ptr D 0 ctx fn PG G tn s cost Gf tnf (OK sf) /\
    sf.vs_current_bb = sb.cs_current_bb /\
    sf.vs_inst_idx = LENGTH sb.cs_current_insts /\
    encoder_complex_member_inv ctx fn sites protected src dst ip a b scap dcap
      active cid cursor so ho ms hs tails tv v (j+1) sb Gf tnf sf /\
    encoder_dynamic_effect sa sites b dcap G tn s Gf tnf sf
Proof
  strip_tac >>
  `!head sc Gp tnp sp.
    emit_op ADD [Var dst; Lit (n2w (encoder_member_offset ho hs j))] sa = (Var head,sc) /\
    compile_abi_encode_to_buf (Var head) (Var es) ei sc = (out,sb) /\
    sp.vs_current_bb = sc.cs_current_bb /\
    sp.vs_inst_idx = LENGTH sc.cs_current_insts /\ ~sp.vs_halted /\
    lookup_var head sp = SOME (n2w (b+encoder_member_offset ho hs j)) /\
    ptr_covers Gp tnp head sp (caps j) /\
    encoder_resource ctx fn (children j) a scap protected sp /\
    sp.vs_memory = s.vs_memory /\ tnp.t_mem = tn.t_mem /\
    sp.vs_allocas = s.vs_allocas /\
    (!x. not_fresh_at sa x ==>
      lookup_var x sp = lookup_var x s /\ FLOOKUP Gp x = FLOOKUP G x /\
      op_taint tnp (Var x) = op_taint tn (Var x)) ==>
    ?Gm tnm sm. encoder_framed_child_result D ctx fn PG sc sb (children j)
      a scap protected (b+encoder_member_offset ho hs j) (caps j) out
      (EL j ns) cost Gp tnp sp Gm tnm sm` by
    (rpt gen_tac >> strip_tac >>
     `lookup_var es sp = SOME (n2w (a+encoder_member_offset so ms j)) /\
      ptr_covers Gp tnp es sp (EL j ms)` by
       (gvs[ptr_covers_def, op_prov_def] >> metis_tac[]) >>
     `!mem. mem_agree_outside tnp.t_mem sp.vs_memory mem ==>
        val_in_memory (tv j) (v j) (a+encoder_member_offset so ms j) mem` by
       (fs[encoder_complex_member_inv_def] >> metis_tac[LESS_OR_EQ]) >>
     qpat_x_assum `!head sc Gp tnp sp. _`
       (qspecl_then [`head`, `sc`, `Gp`, `tnp`, `sp`] mp_tac) >>
     (impl_tac >- simp[]) >> strip_tac >>
     gvs[encoder_semantic_framed_result_def] >> metis_tac[]) >>
  `~s.vs_halted /\ lookup_var dst s = SOME (n2w b) /\
   ptr_covers G tn dst s dcap /\ encoder_resource ctx fn sites a scap protected s` by
    fs[encoder_complex_member_inv_def] >>
  `b+dcap < dimword(:256) /\ children j SUBSET sites` by
    metis_tac[encoder_complex_layout_def] >>
  `encoder_member_offset ho hs j + caps j <= dcap` by
    metis_tac[encoder_complex_static_member_coordinates] >>
  drule_all encoder_static_child_source_narrow_framed_counted_ptr >> strip_tac >>
  `!x. not_fresh_at sa x ==> not_fresh_at sb x` by
    (drule abi_encoder_child_bounds >> simp[not_fresh_at_def] >>
     rpt strip_tac >> decide_tac) >>
  qexistsl_tac [`Gf`, `tnf`, `sf`] >> simp[] >>
  irule encoder_complex_static_invariant_advance >> metis_tac[]
QED
