(* Only the live source prefix must be separate from the destination. *)
Theory appendDynamicLiveStagePtr
Ancestors appendDynamicStagePathPtr valueEncodingProps vyperTyping bodyPtrDefs arithmetic

Theorem append_dynamic_live_stage_path_ptr:
  !cx ctx PG R cenv et tv vs sn dn src dst sa sb G tn s a b D func.
    compile_copy_dynarray_typed cenv (Var dst) et dn (Var src) et sa = ((),sb) /\
    supported_full_word_type et /\
    type_memory_bytes cenv et = type_memory_size tv /\
    value_has_type (ArrayTV tv (Dynamic sn)) (ArrayV (DynArrayV vs)) /\
    (!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
      val_in_memory (ArrayTV tv (Dynamic sn)) (ArrayV (DynArrayV vs)) (w2n a) m) /\
    not_fresh_at sa src /\ not_fresh_at sa dst /\
    lookup_var src s = SOME a /\ lookup_var dst s = SOME b /\
    ptr_covers G tn src s (32+sn*type_memory_size tv) /\
    ptr_covers G tn dst s (32+dn*type_memory_size tv) /\
    sn <= dn /\ dn < dimword(:256) /\
    LENGTH vs * type_memory_size tv < dimword(:256) /\
    w2n a+32 < dimword(:256) /\ w2n b+32 < dimword(:256) /\
    (w2n a+32+LENGTH vs*type_memory_size tv <= w2n b \/
     w2n b+32+dn*type_memory_size tv <= w2n a) /\
    fn_has_code sa sb func /\ ~ctx_has_dalloca ctx /\ ~s.vs_halted /\
    s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?Gf tnf sf.
      gas_path_ptr D 0 ctx func PG G tn s 0 Gf tnf (OK sf) /\
      ~sf.vs_halted /\ sf.vs_current_bb = sb.cs_current_bb /\
      sf.vs_inst_idx = LENGTH sb.cs_current_insts /\
      (sf with <|vs_vars := s.vs_vars; vs_memory := s.vs_memory;
        vs_inst_idx := s.vs_inst_idx|>) = s /\
      frag_exec_ptr cx ctx PG sa sb
        (\g t v. g = G /\ t = tn /\ v = s)
        (\g t v. g = Gf /\ t = tnf /\ v = sf) R /\
      (!m. mem_agree_outside tnf.t_mem sf.vs_memory m ==>
        val_in_memory (ArrayTV tv (Dynamic dn)) (ArrayV (DynArrayV vs)) (w2n b) m) /\
      (!i. i < w2n b \/ w2n b+32+dn*type_memory_size tv <= i ==>
        mem_bytes_at i 1 sf.vs_memory = mem_bytes_at i 1 s.vs_memory /\
        (i IN tnf.t_mem <=> i IN tn.t_mem)) /\
      cs_extends sa sb /\
      tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
      tnf.t_imm = tn.t_imm /\ sf.vs_call_ctx = s.vs_call_ctx /\
      sf.vs_accounts = s.vs_accounts /\ sf.vs_transient = s.vs_transient /\
      (!p. not_fresh_at sa p ==>
        lookup_var p sf = lookup_var p s /\ FLOOKUP Gf p = FLOOKUP G p /\
        op_taint tnf (Var p) = op_taint tn (Var p))
Proof
  rpt gen_tac >> strip_tac >>
  `LENGTH vs <= sn` by gvs[value_has_type_def] >>
  `value_has_type (ArrayTV tv (Dynamic (LENGTH vs))) (ArrayV (DynArrayV vs))` by
    gvs[value_has_type_def] >>
  `!m. mem_agree_outside tn.t_mem s.vs_memory m ==>
    val_in_memory (ArrayTV tv (Dynamic (LENGTH vs))) (ArrayV (DynArrayV vs)) (w2n a) m` by
    metis_tac[val_in_memory_dynarray] >>
  `ptr_covers G tn src s (32+LENGTH vs*type_memory_size tv)` by
    (gvs[ptr_covers_def] >>
     `LENGTH vs * type_memory_size tv <= sn * type_memory_size tv` by simp[] >>
     decide_tac) >>
  irule append_dynamic_stage_path_ptr >>
  asm_rewrite_tac[] >>
  qexistsl [`a`, `cenv`, `dst`, `et`, `LENGTH vs`, `src`] >>
  asm_rewrite_tac[] >> decide_tac
QED
