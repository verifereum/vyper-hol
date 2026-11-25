(* Use the stopped window execution for both the bytes and the real prefix. *)
Theory entryCreateAbiWindowScope
Ancestors
  entryCreateEncodeObserverCode entryStoreObserverStep entryCreateEncodeObserverRun
  entryCreateEncodeObserverPath entryCreateEncodeObserverFrame
  decoderOriginAllocationFrame fragGasOriginPtr fragExec ptrDiscipline
  exprSimAbiEncodeObliviousFacts exprSimAbiGasBridge compileEnv venomInst
  exprLoweringProps finite_map list pred_set

Theorem saved_encode_step_room[local]:
  gas_origin_ptr_edge (D,lo,E,C,f,PG) (u,G,tn) [] (OK v,H,nu) /\
  ~v.vs_halted /\ v.vs_fmp = u.vs_fmp /\ alloca_inv v /\ fn_inst_ids_distinct f /\
  (ctx_has_dalloca C ==> allocas_below_fmp u /\
   u.vs_alloca_next + pending_alloca_size f u <= w2n u.vs_initial_fmp) ==>
  (ctx_has_dalloca C ==> allocas_below_fmp v /\
   v.vs_alloca_next + pending_alloca_size f v <= w2n v.vs_initial_fmp)
Proof
  strip_tac >>
  `gas_origin_ptr_path (D,lo,E,C,f,PG) (u,G,tn) [] (OK v,H,nu)` by
    (irule (SIMP_RULE std_ss [APPEND] (Q.INST [`left` |-> `[]`, `right` |-> `[]`]
       (SPEC_ALL (cj 2 gas_origin_ptr_path_rules)))) >>
     qexistsl_tac [`H`,`v`,`nu`] >> simp[cj 1 gas_origin_ptr_path_rules]) >>
  qpat_assum `gas_origin_ptr_path _ _ _ _`
    (mp_then (Pat `gas_origin_ptr_path _ _ _ _`) mp_tac decoder_origin_path_room) >>
  asm_rewrite_tac[]
QED

Theorem saved_encode_stopped_path[local]:
  fn_inst_ids_distinct f /\ (ctx_has_dalloca oc ==> ctx_has_dalloca ctx) /\
  (!lbl idx bb i. (lbl,idx) IN frag_observer_region a b /\
    (lbl,idx) <> frag_observer_cut b /\
    lookup_block lbl (frag_observer a b f id).fn_blocks = SOME bb /\
    get_instruction bb idx = SOME i ==>
    MEM i (frag_code a b) /\ i.inst_id IN frag_ids a b /\ encode_window_opcode i.inst_opcode /\
    ?real. lookup_block lbl f.fn_blocks = SOME real /\ get_instruction real idx = SOME i) /\
  (!i l. MEM i (frag_code a b) /\ MEM l (create_cut_targets i.inst_opcode i.inst_operands) ==>
    (l,0) IN frag_observer_region a b /\
    ?ob real. lookup_block l (frag_observer a b f id).fn_blocks = SOME ob /\
      lookup_block l f.fn_blocks = SOME real /\
      phi_prefix_length ob.bb_instructions = 0 /\ phi_prefix_length real.bb_instructions = 0) /\
  alloca_inv s /\ (ctx_has_dalloca ctx ==> allocas_below_fmp s /\
    s.vs_alloca_next + pending_alloca_size f s <= w2n s.vs_initial_fmp) /\
  (s.vs_current_bb,s.vs_inst_idx) IN frag_observer_region a b /\
  gas_origin_ptr_path (D,lo,explicit,oc,frag_observer a b f id,PG)
    (s,G,tn) [] (OK t,G',tn') ==>
  gas_origin_ptr_path (D,lo,explicit,ctx,f,PG) (s,G,tn) [] (OK t,G',tn') /\
  create_expr_prefix a b explicit ctx f s [] t /\
  abi_encoder_extend_sim ctx f s t
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qabbrev_tac `guard = \u. alloca_inv u /\
    (ctx_has_dalloca ctx ==> allocas_below_fmp u /\
     u.vs_alloca_next + pending_alloca_size f u <= w2n u.vs_initial_fmp)` >>
  irule create_encode_stopped_path_transfer >> asm_rewrite_tac[] >>
  qexistsl_tac [`guard`,`id`,`oc`] >> asm_rewrite_tac[] >>
  conj_tac >- simp[Abbr `guard`] >>
  map_every qx_gen_tac [`u`,`Gu`,`tu`,`v`,`H`,`nu`] >>
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  fs[Abbr `guard`] >>
  `gas_origin_ptr_edge (D,lo,explicit,ctx,f,PG) (u,Gu,tu) [] (OK v,H,nu) /\
   create_prefix_step a b explicit ctx f u [] v /\
   abi_observer_step ctx f (frag_observer_cut b) u v /\
   (v.vs_current_bb,v.vs_inst_idx) IN frag_observer_region a b /\
   ~v.vs_halted /\ v.vs_fmp = u.vs_fmp /\ (alloca_inv u ==> alloca_inv v)` by
    (irule create_observer_joint_step_transfer >> asm_rewrite_tac[] >>
     qexistsl_tac [`frag_observer a b f id`, `oc`] >> simp[] >>
     conj_tac
     >- (rpt gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
         qpat_assum `!lbl idx bb i. _`
           (qspecl_then [`u.vs_current_bb`,`u.vs_inst_idx`,`ob`,`i`] mp_tac) >>
         (impl_tac >- asm_rewrite_tac[]) >>
         disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
         asm_rewrite_tac[] >> fs[encode_window_opcode_def] >>
         qpat_x_assum `_ \/ _` strip_assume_tac >> gvs[]) >>
     rpt strip_tac >> metis_tac[]) >>
  `alloca_inv v` by simp[] >> asm_rewrite_tac[] >>
  qpat_assum `gas_origin_ptr_edge (D,lo,explicit,ctx,f,PG) _ _ _`
    (mp_then (Pat `gas_origin_ptr_edge _ _ _ _`) mp_tac saved_encode_step_room) >>
  asm_rewrite_tac[]
QED

Theorem create_saved_encode_window_confined:
  compile_abi_encode_to_buf dst src ei st = (out,en) /\
  abi_encoder_admissible ei /\
  (?ct rv. enc ct rv = bs /\
    !mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
      abi_encoder_window_input ei ct rv sb cap mem) /\
  eval_operand src s = SOME (n2w sb) /\ eval_operand dst s = SOME (n2w d) /\
  op_taint tn src = {} /\ op_taint tn dst = {} /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at st x) /\
  fn_has_code st en func /\ fn_inst_ids_distinct func /\ no_phi_fn func /\
  ALL_DISTINCT (en.cs_current_bb :: MAP (\bb. bb.bb_label) (emitted_blocks st en)) /\
  alloca_inv s /\ alloca_room ctx func s /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s /\
    s.vs_alloca_next + pending_alloca_size func s <= w2n s.vs_initial_fmp) /\
  (0 < cap ==> sb + cap <= s.vs_alloca_next /\
    venomMemDefs$regions_disjoint (sb,cap) (d,LENGTH bs) /\
    ?p. src = Var p /\ ptr_covers G tn p s cap) /\
  d + LENGTH bs <= s.vs_alloca_next /\
  (0 < LENGTH bs ==> ?p. dst = Var p /\ ptr_covers G tn p s (LENGTH bs)) /\
  (!inst b sz. MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\
    inst.inst_id IN frag_ids st en /\ FLOOKUP s.vs_allocas inst.inst_id = SOME (b,sz) ==>
    sz = 32 /\ (0 < cap ==> venomMemDefs$regions_disjoint (sb,cap) (b,sz)) /\
    venomMemDefs$regions_disjoint (d,LENGTH bs) (b,sz)) /\
  ~s.vs_halted /\ s.vs_current_bb = st.cs_current_bb /\
  s.vs_inst_idx = LENGTH st.cs_current_insts ==>
  ?t G' tn'.
    mem_bytes_at d (LENGTH bs) t.vs_memory = bs /\
    eval_operand out t = SOME (n2w (LENGTH bs)) /\
    window_phase ctx func st en (window_alloca_sites func (frag_ids st en))
      [(d,LENGTH bs)] s t /\ abi_encode_exec_frame func s t /\
    op_taint tn' out = {} /\ (!x. out = Var x ==> not_fresh_at en x) /\
    (!i. d <= i /\ i < d + LENGTH bs ==> i NOTIN tn'.t_mem) /\
    (!x. not_fresh_at st x ==>
      FLOOKUP G' x = FLOOKUP G x /\ op_taint tn' (Var x) = op_taint tn (Var x)) /\
    (!i. (i < d \/ d + LENGTH bs <= i) /\
      (!id b sz. id IN window_alloca_sites func (frag_ids st en) /\
        FLOOKUP t.vs_allocas id = SOME (b,sz) ==> i < b \/ b + sz <= i) ==>
      (i IN tn'.t_mem <=> i IN tn.t_mem)) /\
    tn'.t_stor = tn.t_stor /\ tn'.t_trans = tn.t_trans /\ tn'.t_imm = tn.t_imm /\
    create_expr_prefix st en explicit ctx func s [] t /\
    !D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn')
Proof
  disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  drule_all create_encode_observer_code >>
  disch_then (qx_choose_then `id` (MAP_EVERY assume_tac o CONJUNCTS)) >>
  `!i. MEM i (fn_insts (frag_observer st en func id)) /\
       MEM i.inst_opcode [ALLOCA; INVOKE; DALLOCA] ==> MEM i (fn_insts func)` by
    (rpt strip_tac >> first_x_assum irule >> fs[]) >>
  `ctx_has_dalloca (ctx with ctx_functions := [frag_observer st en func id]) ==>
   ctx_has_dalloca ctx` by
    (`MEM func ctx.ctx_functions` by
       metis_tac[alloca_room_def, venomInstTheory.lookup_function_MEM] >>
     simp[ctx_has_dalloca_def, EXISTS_MEM] >> strip_tac >>
     qexists_tac `func` >> simp[] >> qexists_tac `inst` >> simp[] >>
     first_x_assum irule >> simp[]) >>
  mp_tac (Q.INST [`obs` |-> `frag_observer st en func id`]
     (SPEC_ALL create_encode_registered_source_window)) >>
  (impl_tac >- asm_rewrite_tac[]) >>
  disch_then (qx_choosel_then [`t`,`G'`,`tn'`] (MAP_EVERY assume_tac o CONJUNCTS)) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (s,G,tn) [] (OK t,G',tn') /\
       create_expr_prefix st en explicit ctx func s [] t /\
       abi_encoder_extend_sim ctx func s t` by
    (gen_tac >> qpat_assum `!D. gas_origin_ptr_path _ _ _ _`
       (qspec_then `D` (mp_then (Pat `gas_origin_ptr_path _ _ _ _`)
          (qspec_then `ctx` mp_tac) saved_encode_stopped_path)) >>
     asm_rewrite_tac[]) >>
  qpat_assum `!D. gas_origin_ptr_path _ _ _ _ /\ _`
    (qspec_then `ARB` (MAP_EVERY assume_tac o CONJUNCTS)) >>
  `!i. MEM i (fn_insts (frag_observer st en func id)) /\
       i.inst_opcode = ALLOCA ==> MEM i (fn_insts func)` by
    (rpt strip_tac >> qpat_assum `!i. _ /\ i.inst_opcode <> STOP ==> _` irule >> simp[]) >>
  drule_all create_encode_window_frame_transfer >> strip_tac >>
  qexistsl_tac [`t`,`G'`,`tn'`] >> asm_rewrite_tac[] >>
  gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
  qpat_assum `!i. _ ==> (i IN tn'.t_mem <=> _)` (qspec_then `i` mp_tac) >>
  (impl_tac >-
    (conj_tac >- first_assum ACCEPT_TAC >>
     rpt gen_tac >> disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
     qpat_assum `!j b sz. j IN window_alloca_sites func _ /\ _ ==> _` irule >>
     first_assum (irule_at Any) >>
     qpat_assum `_ SUBSET window_alloca_sites func _` (mp_tac o REWRITE_RULE [SUBSET_DEF]) >>
     disch_then irule >> first_assum ACCEPT_TAC)) >>
  disch_then ACCEPT_TAC
QED
