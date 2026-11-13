(* Nominal traversal reuses the ordered tuple execution at the same endpoint.
   Exact field lookup and size agreement are explicit metadata obligations. *)
Theory typedNormalizeStructSemanticMem
Ancestors
  typedNormalizeTupleSemanticMem typedNormalizeFields valueEncodingProofs
  valueEncoding list rich_list arithmetic words venomState venomExecSemantics
  memContinuation

Theorem normalize_struct_semantic_cont:
  DT = MAP (FST o SND) fields /\ LENGTH DT = LENGTH tvs /\
  LENGTH vs = LENGTH DT /\ LENGTH names = LENGTH DT /\
  (!name ty sz. MEM (name,ty,sz) fields ==>
    ALOOKUP src_fields name = SOME (ty,sz) /\ sz = type_memory_bytes ce ty) /\
  LIST_REL (\ty tv. type_memory_bytes ce ty = type_memory_size tv) DT tvs /\
  EVERY2 val_wf tvs vs /\
  (!i. d i = b + SUM (MAP (type_memory_bytes ce) (TAKE i DT))) /\
  (!i. h i = a + SUM (MAP (type_memory_bytes ce) (TAKE i DT))) /\
  (h (LENGTH DT) <= b \/ d (LENGTH DT) <= a) /\
  d (LENGTH DT) <= s.vs_alloca_next /\ h (LENGTH DT) <= s.vs_alloca_next /\
  d (LENGTH DT) < dimword (:256) /\ h (LENGTH DT) < dimword (:256) /\
  fields_in_memory (ZIP (names,vs)) (ZIP (names,tvs)) a s.vs_memory /\
  (!i sd se dp sp u.
    i < LENGTH DT /\
    compile_store_memory_typed ce dp (EL i DT) sp (EL i DT) sd = ((),se) /\
    eval_operand dp u = SOME (n2w (d i)) /\
    eval_operand sp u = SOME (n2w (h i)) /\
    (!x. dp = Var x \/ sp = Var x ==> not_fresh_at sd x) /\
    fn_has_code sd se fn /\
    (emitted_blocks sd se <> [] ==>
      ?bb. lookup_block se.cs_current_bb fn.fn_blocks = SOME bb /\
        phi_prefix_length bb.bb_instructions = 0) /\ ~u.vs_halted /\
    u.vs_current_bb = sd.cs_current_bb /\
    u.vs_inst_idx = LENGTH sd.cs_current_insts /\
    d (SUC i) <= u.vs_alloca_next /\ h (SUC i) <= u.vs_alloca_next /\
    d i + type_memory_size (EL i tvs) < dimword (:256) /\
    h i + type_memory_size (EL i tvs) < dimword (:256) /\
    (h i + type_memory_size (EL i tvs) <= d i \/
      d i + type_memory_size (EL i tvs) <= h i) /\
    val_in_memory (EL i tvs) (EL i vs) (h i) u.vs_memory ==>
    ?v. mem_cont_sim ctx fn u v /\
      val_in_memory (EL i tvs) (EL i vs) (d i) v.vs_memory /\
      ~v.vs_halted /\ v.vs_current_bb = se.cs_current_bb /\
      v.vs_inst_idx = LENGTH se.cs_current_insts /\
      (!p k. p+k <= d i \/ d i+type_memory_size (EL i tvs) <= p ==>
        mem_bytes_at p k v.vs_memory = mem_bytes_at p k u.vs_memory) /\
      (!x. not_fresh_at sd x ==> lookup_var x v = lookup_var x u) /\
      (v with <|vs_vars := u.vs_vars; vs_memory := u.vs_memory;
        vs_current_bb := u.vs_current_bb; vs_inst_idx := u.vs_inst_idx;
        vs_prev_bb := u.vs_prev_bb|>) = u) /\
  compile_struct_typed_copy ce dst src fields src_fields 0 0 sa = ((),sb) /\
  (emitted_blocks sa sb <> [] ==>
    ?bb. lookup_block sb.cs_current_bb fn.fn_blocks = SOME bb /\
      phi_prefix_length bb.bb_instructions = 0) /\
  fn_has_code sa sb fn /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\ s.vs_inst_idx = LENGTH sa.cs_current_insts /\
  eval_operand dst s = SOME (n2w b) /\ eval_operand src s = SOME (n2w a) /\
  (!x. dst = Var x \/ src = Var x ==> not_fresh_at sa x) ==>
  ?t. mem_cont_sim ctx fn s t /\ ~t.vs_halted /\
    t.vs_current_bb = sb.cs_current_bb /\
    t.vs_inst_idx = LENGTH sb.cs_current_insts /\
    fields_in_memory (ZIP (names,vs)) (ZIP (names,tvs)) b t.vs_memory /\
    (!p k. p+k <= b \/ b+type_memory_size_list tvs <= p ==>
      mem_bytes_at p k t.vs_memory = mem_bytes_at p k s.vs_memory) /\
    (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
    (t with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
      vs_current_bb := s.vs_current_bb; vs_inst_idx := s.vs_inst_idx;
      vs_prev_bb := s.vs_prev_bb|>) = s
Proof
  strip_tac >>
  `compile_typed_copy_fields ce dst src DT DT 0 0 sa = ((),sb)` by
    (drule normalize_struct_as_fields >>
     disch_then (qspecl_then [`src`,`dst`,`0`,`0`] mp_tac) >> simp[] >> metis_tac[]) >>
  `LENGTH names = LENGTH vs /\ LENGTH names = LENGTH tvs` by metis_tac[] >>
  `tuple_in_memory vs tvs a s.vs_memory` by
    (gvs[fields_in_memory_tuple, MAP_ZIP]) >>
  pure_rewrite_tac[fields_in_memory_tuple] >>
  `MAP SND (ZIP (names,vs)) = vs` by simp[MAP_ZIP] >>
  `MAP SND (ZIP (names,tvs)) = tvs` by simp[MAP_ZIP] >>
  qpat_x_assum `MAP SND (ZIP (names,vs)) = vs` (fn th => rewrite_tac[th]) >>
  qpat_x_assum `MAP SND (ZIP (names,tvs)) = tvs` (fn th => rewrite_tac[th]) >>
  irule normalize_tuple_semantic_cont >>
  simp[] >>
  qexistsl_tac [`DT`, `DT`, `a`, `ce`, `d`, `dst`, `h`, `src`, `tvs`] >>
  gvs[] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED
