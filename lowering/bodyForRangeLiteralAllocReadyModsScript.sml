(* Allocate the literal Range slot, stopping at the entry jump. The same
   allocation witness is used by the literal setup and the loop rounds. *)
Theory bodyForRangeLiteralAllocReadyMods
Ancestors
  bodyForRangeLiteralCodeMods bodyForRangeAllocMods bodyForRangeHeaderMods
  bodyFullIfExpReach bodyFullPostsMods stmtSimDefs loweringPosts
  venomInst venomState fragExec vyperStorageTrace vyperStorageFootprint
  ASCIInumbers finite_map list rich_list

val _ = Parse.hide "body";

Theorem range_literal_alloc_ready_mods:
  stmt_env cenv lctx ty
    (For id typ (Range (Literal a1 (IntL n1)) (Literal a2 (IntL n2))) bound body) sa =
    (cenv,sb) /\
  stmt_env (gas_shadow_env T cenv) lctx ty
    (gas_shadow_stmt
      (For id typ (Range (Literal a1 (IntL n1)) (Literal a2 (IntL n2))) bound body)) ssa =
    (gas_shadow_env T cenv,ssb) /\
  gas_shadow_state sa ssa /\ fn_has_code sa sb func /\ fn_has_code ssa ssb sfunc /\
  fn_inst_ids_distinct func /\ local_ptrs_reserved cenv sa /\ cenv.ce_alloca_locals /\
  FLOOKUP cenv.ce_vars id = NONE /\
  type_memory_bytes cenv typ = 32 /\ type_memory_size tyv = 32 /\ word_memory_type tyv /\
  (!x z. cenv.ce_return_buf = SOME (PtrVar (Var x) z) ==> not_fresh_at sa x) /\
  ret_pc_ok cenv sa s0 /\ return_buf_frame d cenv sa s0 /\ return_buf_sep d cenv es s0 /\
  ~s0.vs_halted /\ s0.vs_current_bb = sa.cs_current_bb /\
  s0.vs_inst_idx = LENGTH sa.cs_current_insts /\ storage_trace_domain cx st0 es.storage_trace /\
  (!H. valid_horizon cx st0 H es.storage_trace ==>
       stmt_state_rel H ctx func cenv cx es s0 /\
       immutable_frame_mods func cenv cx es s0 /\
       storage_well_formed_on cx es (FST H) /\
       ghost_inv_at_mods (DF H) lo d cenv cx es G0 tn0 s0) /\
  alloca_history func s0 /\
  (!bb. MEM bb func.fn_blocks ==> phi_prefix_length bb.bb_instructions = 0) /\
  (!fn inst u. frag_reachable ctx func s0 fn inst u ==> dalloca_fmp_headroom inst u) ==>
  ?p sz ainst cv ev dv nv en cn bl inc ex bc body_cenv sb0 sb1 sj ss0 ss1 bbb bb
   w sA GA tnA.
    p = STRING #"%" (toString sa.cs_next_var) /\ sz = type_memory_bytes cenv typ /\
    ainst = mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)] [p] /\
    nv = STRING #"%" (toString sj.cs_next_var) /\ sj.cs_next_var = sb1.cs_next_var /\
    declare_local cenv id typ sa = (bc,sa with cs_next_var := sa.cs_next_var + 1) /\
    for_code func cenv bc ty body id tyv p sz ainst cv ev dv nv cn ex bl inc
      (sa.cs_next_id + 5) (sa.cs_next_id + 6) (sa.cs_next_id + 7)
      bbb sj.cs_next_id (sj.cs_next_id + 1) (sj.cs_next_id + 2) sb0 sb1 sj /\
    sb0.cs_current_bb = bl /\
    sb0.cs_current_insts = [mk_inst (sa.cs_next_id + 7) MSTORE [Var p; Var cv] []] /\
    sb.cs_current_bb = ex /\ sb.cs_current_insts = [] /\
    sa.cs_next_var <= sb0.cs_next_var /\ sb0.cs_next_var <= sb.cs_next_var /\
    sa.cs_next_id <= sb0.cs_next_id /\ cs_extends sa sb /\
    ~not_fresh_at sa p /\ ~not_fresh_at sa cv /\ ~not_fresh_at sa ev /\ ~not_fresh_at sa dv /\
    cv <> ev /\ p <> cv /\ p <> ev /\
    (!x. not_fresh_at sa x ==> not_fresh_at sb0 x) /\
    cs_extends sa sb0 /\ cs_extends sb0 sb1 /\ cs_extends sb1 sb /\
    cs_extends ssa ss0 /\ cs_extends ss1 ssb /\
    stmts_env bc (InLoop ex inc) ty body sb0 = (body_cenv,sb1) /\
    stmts_env (gas_shadow_env T bc) (InLoop ex inc) ty (MAP gas_shadow_stmt body) ss0 =
      (gas_shadow_env T body_cenv,ss1) /\
    gas_shadow_state sb0 ss0 /\ gas_shadow_state sb1 ss1 /\
    fn_has_code sb0 sb1 func /\ fn_has_code ss0 ss1 sfunc /\
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s0,G0,tn0) [] (OK sA,GA,tnA)) /\
    sA.vs_current_bb = sa.cs_current_bb /\ sA.vs_inst_idx = LENGTH sa.cs_current_insts + 1 /\
    lookup_block sA.vs_current_bb func.fn_blocks = SOME bb /\
    get_instruction bb sA.vs_inst_idx = SOME (mk_inst (sa.cs_next_id + 1) JMP [Label en] []) /\
    lookup_block en func.fn_blocks =
      SOME <|bb_label := en; bb_instructions :=
        [mk_inst (sa.cs_next_id + 2) ASSIGN [Lit (i2w n1)] [cv];
         mk_inst (sa.cs_next_id + 3) ADD [Lit (i2w n1); Lit (i2w n2 - i2w n1)] [ev];
         mk_inst (sa.cs_next_id + 4) JMP [Label cn] []]|> /\
    ~sA.vs_halted /\
    lookup_var p sA = SOME w /\ ptr_covers GA tnA p sA sz /\
    FLOOKUP sA.vs_allocas ainst.inst_id = SOME (w2n w,sz) /\
    (!x z. cenv.ce_return_pc = SOME (PtrVar (Var x) z) ==> not_fresh_at sa x) /\
    ret_pc_ok cenv sa sA /\ return_buf_frame d cenv sa sA /\ return_buf_sep d cenv es sA /\
    (!H. valid_horizon cx st0 H es.storage_trace ==>
         stmt_state_rel H ctx func cenv cx es sA /\
         immutable_frame_mods func cenv cx es sA /\
         storage_well_formed_on cx es (FST H) /\
         ghost_inv_at_mods (DF H) lo d cenv cx es GA tnA sA) /\
    (!fn inst u. frag_reachable ctx func sA fn inst u ==> dalloca_fmp_headroom inst u) /\
    range_outer_frame_mods ctx func cenv sa es s0 G0 tn0 es GA tnA sA
Proof
  strip_tac >>
  `(!l. FLOOKUP cenv.ce_vars id = SOME l ==> ?q z. l = PtrVar q z) /\
   32 <= type_memory_bytes cenv typ` by simp[] >>
  drule_all range_literal_code_mods >>
  disch_then (qx_choosel_then
    [`p`,`sz`,`ainst`,`cv`,`ev`,`dv`,`nv`,`en`,`cn`,`bl`,`inc`,`ex`,`bc`,
     `body_cenv`,`sb0`,`sb1`,`sj`,`ss0`,`ss1`,`bbb`] strip_assume_tac) >>
  `alloca_frame cenv es sa s0 cenv es s0` by simp[alloca_frame_same] >>
  `lookup_block sa.cs_current_bb func.fn_blocks =
    SOME <|bb_label := sa.cs_current_bb; bb_instructions := sa.cs_current_insts ++
      [mk_inst sa.cs_next_id ALLOCA [Lit (n2w sz)] [p]] ++
      [mk_inst (sa.cs_next_id + 1) JMP [Label en] []]|>` by
    (qpat_assum `ainst = _` (SUBST1_TAC o SYM) >>
     pure_once_rewrite_tac[APPEND_ASSOC_CONS] >>
     pure_rewrite_tac[APPEND] >> first_assum ACCEPT_TAC) >>
  `sz < dimword (:256)` by simp[wordsTheory.dimword_def, venomMemPropsTheory.dimindex_256] >>
  (* The allocation starts at the original frame; coalesce its two
     input snapshots before matching the remaining premises. *)
  drule_all (SIMP_RULE std_ss [] (Q.INST
    [`st` |-> `sa`, `s` |-> `s0`, `ea` |-> `es`, `GE` |-> `G0`, `tnE` |-> `tn0`]
    (SPEC_ALL range_slot_alloc_path_mods))) >>
  disch_then (qspecl_then [`explicit`,`PG`]
    (qx_choosel_then [`w`,`sA`,`GA`,`tnA`] strip_assume_tac)) >>
  qabbrev_tac `bb = <|bb_label := sa.cs_current_bb;
    bb_instructions := sa.cs_current_insts ++ [ainst; mk_inst (sa.cs_next_id + 1) JMP [Label en] []]|>` >>
  `lookup_block sA.vs_current_bb func.fn_blocks = SOME bb` by simp[Abbr `bb`] >>
  `get_instruction bb sA.vs_inst_idx = SOME (mk_inst (sa.cs_next_id + 1) JMP [Label en] [])` by
    simp[Abbr `bb`, get_instruction_def, EL_APPEND_EQN] >>
  `sa.cs_next_var <= sb0.cs_next_var /\ cv <> ev /\ p <> cv /\ p <> ev` by simp[] >>
  `lookup_var p sA = SOME w /\ ptr_covers GA tnA p sA sz /\
   FLOOKUP sA.vs_allocas ainst.inst_id = SOME (w2n w,sz)` by
    (qpat_assum `p = STRING _ _` SUBST1_TAC >> qpat_assum `ainst = _` SUBST1_TAC >>
     simp[NoAsms, mk_inst_def] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `!x z. cenv.ce_return_pc = SOME (PtrVar (Var x) z) ==> not_fresh_at sa x` by
    (qpat_assum `ret_pc_ok cenv sa s0` (mp_tac o REWRITE_RULE [ret_pc_ok_def]) >>
     rpt strip_tac >> first_x_assum (drule_then strip_assume_tac) >> first_assum ACCEPT_TAC) >>
  `!H. valid_horizon cx st0 H es.storage_trace ==>
       stmt_state_rel H ctx func cenv cx es sA /\ immutable_frame_mods func cenv cx es sA /\
       storage_well_formed_on cx es (FST H) /\ ghost_inv_at_mods (DF H) lo d cenv cx es GA tnA sA` by
    (gen_tac >> disch_tac >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ sA /\ _`
       (drule_then strip_assume_tac) >>
     qpat_assum `!H. valid_horizon _ _ H _ ==> stmt_state_rel _ _ _ _ _ _ s0 /\ _`
       (drule_then strip_assume_tac) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `!fn inst u. frag_reachable ctx func sA fn inst u ==> dalloca_fmp_headroom inst u` by
    (qpat_assum `!D. gas_origin_ptr_path _ _ _ (OK sA,GA,tnA)`
       (qspec_then `DF (storage_trace_horizon es.storage_trace)`
         (mp_then (Pos hd) mp_tac gas_origin_ptr_path_dalloca_fmp_headroom)) >>
     qpat_assum `!fn inst u. frag_reachable ctx func s0 fn inst u ==> _`
       (pure_rewrite_tac o single o EQT_INTRO) >> simp[]) >>
  `range_outer_frame_mods ctx func cenv sa es s0 G0 tn0 es GA tnA sA` by
    (rewrite_tac[range_outer_frame_mods_def] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  qexistsl [`p`,`sz`,`ainst`,`cv`,`ev`,`dv`,`nv`,`en`,`cn`,`bl`,`inc`,`ex`,`bc`,
            `body_cenv`,`sb0`,`sb1`,`sj`,`ss0`,`ss1`,`bbb`,`bb`,`w`,`sA`,`GA`,`tnA`] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED
