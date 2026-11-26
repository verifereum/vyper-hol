(* The memory routes share one reached length slice.  This adapter packages
   the value/local-place result without choosing a new descriptor at install. *)
Theory bodyForArrayMemoryPacketMods
Ancestors
  bodyForArrayLengthPacketMods bodyForArrayHeldLengthMods
  bodyForArrayEntryMods bodyForArrayHeaderInstallMods
  bodyFullPostsMods bodyFullPredsMods loweringPosts
  fragGasOriginPtr vyperInterpreter vyperStorageTrace vyperStorageFootprint
  vyperValue vyperAST venomState words list finite_map arithmetic
Libs
  monadsyntax

Theorem for_array_memory_packet_mods:
  expr_body_pre_mods mods c cx env e es /\ expr_type e = ArrayT elem bd /\
  eval_expr cx e es = (INL raw,em) /\ bound_length bd <= n /\
  vv_post_mods H ctx func c cx e es sa sb s0 em raw vv s /\
  ptr_vv_ok cx (post_value_type c e) raw vv em G tn s /\
  (!v. raw = Value v /\
       ~is_word_type (post_value_type c e) /\
       ~is_bytestring_type (post_value_type c e) ==>
       vv_own c cx (post_value_type c e) sa sb em raw vv s) /\
  ((?v. raw = Value v) \/ (?name path. raw = PlaceR (MemoryPlace name path))) /\
  (vv_location vv = NONE \/ vv_location vv = SOME LocMemory) /\
  compile_expr c (expr_type e) e sa = (vv,sb) /\ local_ptrs_reserved c sa /\
  (case bd of Fixed k => comp_return (Lit (n2w k))
    | Dynamic _ => compile_ptr_load c.ce_is_ctor c.ce_imm_alloca LocMemory
                    (vv_operand vv)) sb = (len_op,sc) /\
  fn_has_code sb sc func /\ ~s.vs_halted /\
  s.vs_current_bb = sb.cs_current_bb /\
  s.vs_inst_idx = LENGTH sb.cs_current_insts /\
  allocas_from lo s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\
  (!et av vs pe pb pet a z Gz tz.
    evaluate_type (get_tenv cx) (expr_type e) = SOME (ArrayTV et bd) /\
    read_result cx raw em = (INL (ArrayV av),em) /\
    value_has_type (ArrayTV et bd) (ArrayV av) /\
    eval_iterator cx (Array e) es = (INL vs,em) /\
    vs = MAP Value (array_elements (ArrayTV et bd) av) /\
    compatible_bound (Dynamic n) (LENGTH vs) /\
    (!tail. array_iterator_results cx (expr_type e) raw
      (em with gas_obs := tail) = (INL vs,em with gas_obs := tail)) /\
    post_value_type c e = ArrayT pe pb /\
    evaluate_type (get_tenv cx) (post_value_type c e) =
      SOME (ArrayTV pet pb) /\
    val_wf (ArrayTV pet pb) (ArrayV av) /\
    (!D. gas_origin_ptr_path
      (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK z,Gz,tz)) /\
    eval_operand len_op z = SOME (n2w (LENGTH vs)) /\
    op_taint tz len_op = {} /\ op_prov Gz len_op = NONE /\
    ~z.vs_halted /\ z.vs_current_bb = sc.cs_current_bb /\
    z.vs_inst_idx = LENGTH sc.cs_current_insts /\
    array_length_frame sb s G tn z Gz tz /\
    eval_operand (vv_operand vv) z = SOME a /\
    op_taint tz (vv_operand vv) = {} /\
    op_prov Gz (vv_operand vv) = op_prov G (vv_operand vv) /\
    ptr_mem_ok cx (post_value_type c e) (ArrayV av)
      (vv_operand vv) Gz tz z /\
    z.vs_alloca_next = s.vs_alloca_next /\
    z.vs_allocas = s.vs_allocas /\ z.vs_memory = s.vs_memory /\
    (raw = Value (ArrayV av) /\ 0 < type_memory_size (ArrayTV pet pb) ==>
       ?aid b sz. FLOOKUP z.vs_allocas aid = SOME (b,sz) /\
         sa.cs_next_id <= aid /\ aid < sb.cs_next_id /\
         b <= w2n a /\ w2n a + type_memory_size (ArrayTV pet pb) <= b + sz) /\
    (0 < type_memory_size (ArrayTV pet pb) ==>
       w2n a + type_memory_size (ArrayTV pet pb) <= z.vs_alloca_next /\
       ((?aid b sz. FLOOKUP z.vs_allocas aid = SOME (b,sz) /\ aid < sb.cs_next_id /\
           b <= w2n a /\ w2n a + type_memory_size (ArrayTV pet pb) <= b + sz) \/
        (?name b sz. local_region c em.scopes s name b sz /\
           b <= w2n a /\ w2n a + type_memory_size (ArrayTV pet pb) <= b + sz))) ==>
    (LENGTH vs <= bound_length bd /\
    ret_pc_ok c sa0 z /\ return_buf_frame d c sa0 z /\
    return_buf_sep d c em z /\
    z.vs_current_bb = saL.cs_current_bb /\
    z.vs_inst_idx = LENGTH saL.cs_current_insts /\
    (!fn inst q. frag_reachable ctx func z fn inst q ==>
      dalloca_fmp_headroom inst q) /\
    for_array_outer_frame_mods ctx func c sa0 es0 s0 G0 tn0
      em Gz tz z /\
    (!K. valid_horizon cx st0 K em.storage_trace ==>
      stmt_state_rel K ctx func c cx em z /\
      immutable_frame_mods func c cx em z /\
      storage_well_formed_on cx em (FST K) /\
      ghost_inv_at_mods (DF K) lo d c cx em Gz tz z) /\
    (raw = Value (ArrayV av) ==>
      (!K t G' tn'. valid_horizon cx st0 K em.storage_trace /\
        for_array_install_frame_mods saL z Gz tz G' tn' t ==>
        for_array_entry_route_mods c cx lo (sty,bd,loc)
          (em,sbExpr,z,Gz,tz) (vv_operand vv,a)
          vs (ForArrayOwned av) K vs em G' tn' t)) /\
    (!name path. raw = PlaceR (MemoryPlace name path) ==>
      (!K t G' tn'. valid_horizon cx st0 K em.storage_trace /\
        for_array_install_frame_mods saL z Gz tz G' tn' t ==>
        for_array_entry_route_mods c cx lo (sty,bd,loc)
          (em,sbExpr,z,Gz,tz) (vv_operand vv,a)
          vs (ForArrayHeld name path av) K vs em G' tn' t)))) ==>
  ?vs a z Gz tz capture.
    for_array_length_packet_mods mods (DF,lo,d,ctx,func,shadow_func)
      (explicit,PG) cx env st0
      (es0,sa0,s0,G0,tn0)
      ((c,id,fty,e,sty,bd,ret_ty,loop_body),
       (vv,sbExpr,shadow_sa0,shadow_sbExpr,loc,len_op,saL),
       item,blocks,addr_cut,body_cut)
      raw n (s,G,tn) (em,z,Gz,tz,a,capture,vs)
Proof
  DISCH_THEN (map_every assume_tac o CONJUNCTS) >>
  mp_tac (SPEC_ALL for_array_held_length_ready_mods) >>
  impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qx_choosel_then
    [`et`,`av`,`vs`,`pe`,`pb`,`pet`,`a`,`z`,`Gz`,`tz`]
    (fn reached =>
      qpat_x_assum `!et av vs pe pb pet a z Gz tz. _`
        (fn rule => map_every assume_tac (CONJUNCTS (MATCH_MP rule reached))) >>
      map_every assume_tac (CONJUNCTS reached))) >>
  `!K. valid_horizon cx st0 K em.storage_trace ==>
       gas_origin_ptr_path (DF K,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK z,Gz,tz) /\
       stmt_state_rel K ctx func c cx em z /\ immutable_frame_mods func c cx em z /\
       storage_well_formed_on cx em (FST K) /\ ghost_inv_at_mods (DF K) lo d c cx em Gz tz z` by
    (qx_gen_tac `h` >> disch_tac >> conj_tac
     >- (qpat_assum `!D. gas_origin_ptr_path _ _ _ _` (qspec_then `DF h` ACCEPT_TAC)) >>
     qpat_assum `!K. valid_horizon _ _ K _ ==> stmt_state_rel _ _ _ _ _ _ _ /\ _`
       (drule_then ACCEPT_TAC)) >>
  `?cap. !K t G' tn'. valid_horizon cx st0 K em.storage_trace /\
           for_array_install_frame_mods saL z Gz tz G' tn' t ==>
           for_array_entry_route_mods c cx lo (sty,bd,loc)
             (em,sbExpr,z,Gz,tz) (vv_operand vv,a) vs cap K vs em G' tn' t` by
    (qpat_x_assum `(?v. raw = Value v) \/ _` strip_assume_tac
     >- (rename1 `raw = Value v` >>
         `raw = Value (ArrayV av)` by
           (qpat_assum `raw = Value v` (fn eq =>
              qpat_assum `read_result _ raw _ = _`
                (mp_tac o PURE_ONCE_REWRITE_RULE [eq])) >>
            simp[vyperStateTheory.read_result_def, vyperStateTheory.return_def]) >>
         qexists `ForArrayOwned av` >>
         qpat_assum `raw = Value (ArrayV av) ==> _` (drule_then ACCEPT_TAC)) >>
     rename1 `raw = PlaceR (MemoryPlace held_name held_path)` >>
     qexists `ForArrayHeld held_name held_path av` >>
     qpat_assum `!name path. raw = PlaceR (MemoryPlace name path) ==> _`
       (qspecl_then [`held_name`,`held_path`] (drule_then ACCEPT_TAC))) >>
  qexistsl [`vs`,`a`,`z`,`Gz`,`tz`,`cap`] >>
  pure_rewrite_tac[for_array_length_packet_mods_def] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
