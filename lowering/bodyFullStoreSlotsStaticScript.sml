Theory bodyFullStoreSlotsStatic
Ancestors
  bodyFullStoreSlotsPath augAssignFullStore placeStoreSlots
  bodyFullStoreSlotsStaticSource bodyFullStoreSlotsStaticTrace
  bodyFullStoreSlotsStaticFrame bodyFullStoreSlotsStaticRelabel
  bodyFullStoreSlotsStaticSeparation bodyFullStoreSlotsStaticTraceUnique
  bodyFullStoreSlotsStaticZero bodyFullStoreSlotsStaticHorizon
  bodyFullStoreSlotsStaticTransfer bodyFullStoreSlotsStaticExit
  bodyFullStoreSlotsStaticEncoding bodyFullStoreSlotsStaticTraceTransfer
  exprSimAbiGasBridge ptrDiscipline bodyPtrDefs venomExecSemantics
  abiEncoderObserver fragExec
  venomState venomInst compileEnv list rich_list pred_set arithmetic exprSimAbiDecodeSetupObserve

Theorem compile_store_slots_static_origin_ptr_path:
 !cenv tenv ty tv v src dst tr sa sb s sw dw tn G writes func ctx lo explicit PG.
  acyclic_struct_metadata cenv.ce_struct_fields /\
  sfields_tenv_consistent cenv.ce_struct_fields tenv /\
  (!name fields. FLOOKUP cenv.ce_struct_fields name = SOME fields ==>
     ALL_DISTINCT (MAP FST fields) /\
     EVERY (\(fname,fty,sz). !rt. evaluate_type tenv fty = SOME rt ==>
              sz = type_memory_size rt) fields) /\
  evaluate_type tenv ty = SOME tv /\ value_has_type tv v /\
  compile_store_slots cenv src dst ty tr sa = ((),sb) /\
  (!x. src = Var x \/ dst = Var x ==> not_fresh_at sa x) /\
  eval_operand src s = SOME sw /\ eval_operand dst s = SOME dw /\
  op_taint tn src = {} /\ op_taint tn dst = {} /\
  (!mem. mem_agree_outside tn.t_mem s.vs_memory mem ==>
         val_in_memory tv v (w2n sw) mem) /\
  (type_memory_size tv <> 0 ==>
     ?x. src = Var x /\ ptr_covers G tn x s (type_memory_size tv)) /\
  w2n sw + type_memory_size tv < dimword (:256) /\
  w2n dw + type_slot_size tv <= dimword (:256) /\
  (type_memory_size tv = 0 \/
   w2n sw + type_memory_size tv <= s.vs_alloca_next) /\
  encode_value tv v = SOME writes /\
  fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
  (ctx_has_dalloca ctx ==> allocas_below_fmp s) /\ allocas_from lo s /\ lo <= s.vs_alloca_next /\
  s.vs_call_ctx.cc_static /\ ~s.vs_halted /\
  s.vs_current_bb = sa.cs_current_bb /\
  s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
  ?t Gf tnf.
    (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
      (s,G,tn) []
      ((if type_slot_size tv = 0 then OK t
        else Abort ExHalt_abort (halt_state (set_returndata [] t))),Gf,tnf)) /\
    store_copy_normalize s t = s /\
    (!x. not_fresh_at sa x ==>
      lookup_var x t = lookup_var x s /\ FLOOKUP Gf x = FLOOKUP G x /\
      op_taint tnf (Var x) = op_taint tn (Var x)) /\
    tnf.t_mem = tn.t_mem /\ tnf.t_imm = tn.t_imm /\
    tnf.t_stor = tn.t_stor /\ tnf.t_trans = tn.t_trans /\
    t.vs_memory = s.vs_memory /\ t.vs_allocas = s.vs_allocas /\
    t.vs_alloca_next = s.vs_alloca_next /\ t.vs_fmp = s.vs_fmp /\
    t.vs_labels = s.vs_labels /\ t.vs_call_ctx = s.vs_call_ctx /\
    ~t.vs_halted /\
    (type_slot_size tv = 0 ==>
      t.vs_current_bb = sb.cs_current_bb /\
      t.vs_inst_idx = LENGTH sb.cs_current_insts) /\
    (type_slot_size tv <> 0 ==>
      ?bb inst. lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
        get_instruction bb t.vs_inst_idx = SOME inst /\
        inst.inst_opcode = (if tr then TSTORE else SSTORE) /\
        step_inst_base inst t = Abort ExHalt_abort (halt_state (set_returndata [] t)))
Proof
  rpt gen_tac >> disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  drule_all store_slots_fragment_source_certificate >>
  disch_then (qx_choose_then `ell` (qx_choose_then `ids`
    (qx_choose_then `id` (qx_choose_then `canon`
      (REPEAT_TCL CONJUNCTS_THEN assume_tac))))) >>
  qabbrev_tac `A = start_relabel ell ids sa` >>
  qabbrev_tac `B = start_swap sa ell ids sb` >>
  qpat_x_assum `let a = _ in _` mp_tac >>
  simp[LET_THM] >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  qabbrev_tac `s0 = s with vs_call_ctx := (s.vs_call_ctx with cc_static := F)` >>
  qabbrev_tac `a0 = s0 with vs_current_bb := ell` >>
  `eval_operand src a0 = SOME sw /\ eval_operand dst a0 = SOME dw` by
    (Cases_on `src` >> Cases_on `dst` >>
     gvs[Abbr `a0`, Abbr `s0`, eval_operand_def, lookup_var_def]) >>
  `(type_memory_size tv <> 0 ==>
      ?x. src = Var x /\ ptr_covers G tn x a0 (type_memory_size tv)) /\
   (!mem. mem_agree_outside tn.t_mem a0.vs_memory mem ==>
      val_in_memory tv v (w2n sw) mem) /\
   (ctx_has_dalloca ctx ==> allocas_below_fmp a0) /\
   allocas_from lo a0 /\ lo <= a0.vs_alloca_next /\
   ~a0.vs_call_ctx.cc_static /\ ~a0.vs_halted /\
   a0.vs_current_bb = A.cs_current_bb /\
   a0.vs_inst_idx = LENGTH A.cs_current_insts` by
    (gvs[Abbr `a0`, Abbr `s0`, ptr_covers_def, lookup_var_def,
         allocas_below_fmp_def, allocas_from_def] >> metis_tac[]) >>
  `!x. src = Var x \/ dst = Var x ==> not_fresh_at A x` by
    (gvs[loweringStateRelDefsTheory.not_fresh_at_def] >> metis_tac[]) >>
  `cs_extends sa sb` by
    metis_tac[bodyFullStoreSlotsStaticLayoutTheory.store_slots_fragment_syntax_shape] >>
  mp_tac (Q.INST [`sa` |-> `A`, `sb` |-> `B`,
                  `s` |-> `a0`, `func` |-> `canon`]
    (SPEC_ALL compile_store_slots_origin_ptr_path)) >>
  (impl_tac >- (asm_rewrite_tac[] >> simp[Abbr `a0`, Abbr `s0`])) >>
  disch_then (qx_choose_then `out` (qx_choose_then `ks`
    (qx_choose_then `Gout` (qx_choose_then `tnout`
      (REPEAT_TCL CONJUNCTS_THEN assume_tac))))) >>
  `gas_origin_ptr_path (ARB,lo,explicit,ctx,frag_observer A B canon id,PG)
    (a0,G,tn) [] (OK out,Gout,tnout)` by simp[] >>
  drule_at (Pat `gas_origin_ptr_path _ _ _ _`) store_slots_observer_first_cut >>
  disch_then (qspec_then `tr` mp_tac) >>
  (impl_tac >-
    (asm_rewrite_tac[frag_observer_cut_def] >>
     conj_tac >- (gvs[MEM] >> metis_tac[]) >>
     gvs[MEM] >> metis_tac[])) >>
  disch_then (qx_choose_then `xs` (qx_choose_then `k`
    (REPEAT_TCL CONJUNCTS_THEN assume_tac))) >>
  Cases_on `EL k xs` >> rename1 `EL k xs = (u,rest)` >>
  Cases_on `rest` >> rename1 `EL k xs = (u,Gu,tnu)` >>
  qabbrev_tac `pre = TAKE (SUC k) xs` >>
  `pre <> [] /\ HD pre = (a0,G,tn) /\ LAST pre = (u,Gu,tnu) /\
   LENGTH pre = SUC k` by
    (simp[Abbr `pre`, TAKE_EQ_NIL, LENGTH_TAKE, HD_TAKE, LAST_TAKE_EL] >>
     gvs[] >> decide_tac) >>
  `!lbl bb. lbl <> A.cs_current_bb /\
     lookup_block lbl canon.fn_blocks = SOME bb ==>
     phi_prefix_length bb.bb_instructions = 0` by
    (rpt strip_tac >> irule abi_decode_observer_nonentry_phi_zero >>
     metis_tac[]) >>
  `!n a Ga tna b Gb tnb.
    SUC n < LENGTH pre /\ EL n pre = (a,Ga,tna) /\
    EL (SUC n) pre = (b,Gb,tnb) ==>
    ?bb i.
      lookup_block a.vs_current_bb canon.fn_blocks = SOME bb /\
      get_instruction bb a.vs_inst_idx = SOME i /\
      MEM i (frag_code A B) /\
      MEM i.inst_opcode [ASSIGN;ADD;MUL;EQ;LT;ISZERO;SHR;MLOAD;JMP;JNZ] /\
      (!x. not_fresh_at A x ==> ~MEM x i.inst_outputs) /\
      (!fuel mid target.
        step_inst fuel ctx i a = OK mid /\ is_terminator i.inst_opcode /\
        lookup_block mid.vs_current_bb canon.fn_blocks = SOME target ==>
        phi_prefix_length target.bb_instructions = 0) /\
      gas_origin_ptr_edge (ARB,lo,explicit,ctx,canon,PG)
        (a,Ga,tna) [] (OK b,Gb,tnb)` by
    (rpt gen_tac >> strip_tac >>
     `n < k /\ SUC n < LENGTH xs /\ EL n xs = (a,Ga,tna) /\
      EL (SUC n) xs = (b,Gb,tnb)` by
       (gvs[Abbr `pre`, EL_TAKE] >> decide_tac) >>
     qpat_assum `!n a Ga tna. n < k /\ _ ==> _`
       (qspecl_then [`n`,`a`,`Ga`,`tna`] mp_tac) >> simp[] >>
     disch_then (CONJUNCTS_THEN2 assume_tac
       (qx_choose_then `bb` (qx_choose_then `i`
         (REPEAT_TCL CONJUNCTS_THEN assume_tac)))) >>
     qexistsl_tac [`bb`,`i`] >> asm_rewrite_tac[] >>
     conj_tac >- metis_tac[] >>
     conj_tac >-
       (rpt strip_tac >>
        `MEM i.inst_opcode [JMP;JNZ;DJMP]` by
          gvs[MEM, is_terminator_def] >>
        `~MEM (Label ell) i.inst_operands` by
          (qpat_x_assum `EVERY (\i. ~MEM (Label ell) _) _` mp_tac >>
           simp[EVERY_MEM] >> metis_tac[]) >>
        `mid.vs_current_bb <> ell` by
          (irule frag_observer_jump_no_reentry >>
           qexistsl_tac [`i`,`a`] >> simp[] >>
           gvs[MEM, step_inst_non_invoke]) >>
        metis_tac[]) >>
     qpat_x_assum `!n a Ga tna b Gb tnb. _`
       (qspec_then `n` mp_tac) >> simp[]) >>
  mp_tac (Q.INST [`L` |-> `pre`, `sa` |-> `A`, `s` |-> `a0`,
                  `func` |-> `canon`, `D` |-> `ARB`]
    (SPEC_ALL store_slots_readonly_prefix_frame)) >>
  (impl_tac >- (asm_rewrite_tac[] >> rpt strip_tac >>
    qpat_x_assum `!n a Ga tna b Gb tnb. SUC n < LENGTH pre /\ _ ==> _`
      (qspec_then `n` mp_tac) >> simp[] >>
    disch_then (qx_choose_then `bb` (qx_choose_then `i`
      (REPEAT_TCL CONJUNCTS_THEN assume_tac))) >>
    qexistsl_tac [`bb`,`i`] >> asm_rewrite_tac[])) >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `!n. SUC n < LENGTH pre ==>
    gas_origin_ptr_edge (ARB,lo,explicit,ctx,canon,PG) (EL n pre) []
      (OK (FST (EL (SUC n) pre)), SND (EL (SUC n) pre))` by
    (rpt strip_tac >> Cases_on `EL n pre` >> Cases_on `EL (SUC n) pre` >>
     rename1 `EL n pre = (a,Ga_tna)` >>
     rename1 `EL (SUC n) pre = (b,Gb_tnb)` >>
     Cases_on `Ga_tna` >> Cases_on `Gb_tnb` >>
     qpat_x_assum `!n a Ga tna b Gb tnb. SUC n < LENGTH pre /\ _ ==> _`
       (qspec_then `n` mp_tac) >> simp[] >> metis_tac[]) >>
  `!a u' cb inst.
    frag_relabel_state ell sa.cs_current_bb a u' /\
    (a.vs_current_bb,a.vs_inst_idx) IN frag_observer_region A B /\
    (a.vs_current_bb,a.vs_inst_idx) <> frag_observer_cut B /\
    lookup_block a.vs_current_bb canon.fn_blocks = SOME cb /\
    get_instruction cb a.vs_inst_idx = SOME inst ==>
    ?ab. lookup_block u'.vs_current_bb func.fn_blocks = SOME ab /\
      get_instruction ab u'.vs_inst_idx = SOME inst` by suspend "fetch" >>
  mp_tac (Q.INST [`L` |-> `ell`, `entry` |-> `sa.cs_current_bb`,
    `canon` |-> `canon`, `func` |-> `func`, `D` |-> `ARB`]
    (Q.SPECL [`pre`,`s0`] store_slots_relabel_checked_prefix)) >>
  (impl_tac >-
    (asm_rewrite_tac[] >>
     conj_tac >-
       (simp[Abbr `a0`] >> irule frag_relabel_state_initial >>
        simp[Abbr `s0`]) >>
     conj_tac >- metis_tac[] >>
     suspend "relabel_fetch")) >>
  disch_then (qx_choose_then `ys` (REPEAT_TCL CONJUNCTS_THEN assume_tac)) >>
  suspend "assemble"
QED

Resume compile_store_slots_static_origin_ptr_path[relabel_fetch]:
  rpt strip_tac >>
  Cases_on `EL i pre` >> rename1 `EL i pre = (a,ghosts)` >>
  Cases_on `ghosts` >> rename1 `EL i pre = (a,Ga,tna)` >>
  `EL i xs = (a,Ga,tna) /\ i < k` by
    (gvs[Abbr `pre`, EL_TAKE] >> decide_tac) >>
  qpat_assum `!n a Ga tna. n < k /\ _ ==> _`
    (qspecl_then [`i`,`a`,`Ga`,`tna`] mp_tac) >> simp[] >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (qx_choose_then `cb` (qx_choose_then `inst`
      (REPEAT_TCL CONJUNCTS_THEN assume_tac)))) >>
  `(a.vs_current_bb,a.vs_inst_idx) IN frag_observer_region A B` by
    (qpat_assum `!n a Ga tna. n <= k /\ _ ==> _`
      (qspecl_then [`i`,`a`,`Ga`,`tna`] mp_tac) >> simp[]) >>
  `?ab. lookup_block u'.vs_current_bb func.fn_blocks = SOME ab /\
        get_instruction ab u'.vs_inst_idx = SOME inst` by
    (first_x_assum irule >> qexistsl_tac [`a`,`cb`] >> simp[] >>
     qpat_assum `frag_relabel_state _ _ _ _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[]) >>
  qexistsl_tac [`cb`,`ab`,`inst`] >> simp[] >>
  conj_tac >-
    (qpat_assum `inst.inst_opcode = ASSIGN \/ _` mp_tac >> tautLib.TAUT_TAC) >>
  strip_tac >> qpat_x_assum `EVERY (\i. ~MEM (Label ell) _) _` mp_tac >>
  simp[EVERY_MEM] >> disch_then (qspec_then `inst` mp_tac) >> simp[]
QED

Resume compile_store_slots_static_origin_ptr_path[fetch]:
  rpt gen_tac >> strip_tac >>
  `(a.vs_current_bb = ell ==> LENGTH sa.cs_current_insts <= a.vs_inst_idx)` by
    (qpat_assum `(_,_) IN frag_observer_region A B` mp_tac >>
     simp[Abbr `A`, Abbr `B`] >> disch_tac >>
     drule exprSimAbiGasBridgeEdgeTheory.frag_relabel_edge_region_entry_bound >>
     simp[]) >>
  drule frag_relabel_state_fields >> strip_tac >>
     Cases_on `sa.cs_blocks = sb.cs_blocks`
     >- (`emitted_blocks A B = [] /\ B.cs_current_bb = ell /\
           canon = frag_observer A B func id` by
           simp[Abbr `A`, Abbr `B`, start_relabel_def, start_swap_def,
                fragExecTheory.emitted_blocks_def] >>
         `a.vs_current_bb = ell` by
           (qpat_assum `(_,_) IN frag_observer_region A B` mp_tac >>
            qpat_assum `emitted_blocks A B = []` mp_tac >>
            qpat_assum `B.cs_current_bb = ell` mp_tac >>
            POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
            gvs[frag_observer_region_def]) >>
         `cb = <|bb_label := B.cs_current_bb;
                 bb_instructions := B.cs_current_insts ++ [mk_inst id STOP [] []]|>` by
           (qpat_assum `lookup_block a.vs_current_bb canon.fn_blocks = SOME cb` mp_tac >>
            qpat_assum `canon = frag_observer A B func id` mp_tac >>
            qpat_assum `a.vs_current_bb = ell` mp_tac >>
            qpat_assum `B.cs_current_bb = ell` mp_tac >>
            POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
            qpat_x_assum `B.cs_current_bb = ell` (SUBST_ALL_TAC o SYM) >>
            gvs[frag_observer_cut_lookup]) >>
         `a.vs_inst_idx < LENGTH B.cs_current_insts` by
           (qpat_assum `get_instruction cb a.vs_inst_idx = SOME inst` mp_tac >>
            qpat_assum `cb = <|bb_label := _; bb_instructions := _|>` mp_tac >>
            qpat_assum `(a.vs_current_bb,a.vs_inst_idx) <> frag_observer_cut B` mp_tac >>
            qpat_assum `a.vs_current_bb = ell` mp_tac >>
            qpat_assum `B.cs_current_bb = ell` mp_tac >>
            POP_ASSUM_LIST (K all_tac) >>
            simp[get_instruction_def, frag_observer_cut_def] >> rpt strip_tac >> decide_tac) >>
         `sb.cs_current_bb = sa.cs_current_bb /\
          isPREFIX sa.cs_current_insts sb.cs_current_insts` by
           (qpat_assum `cs_extends sa sb` mp_tac >>
            qpat_assum `sa.cs_blocks = sb.cs_blocks` mp_tac >>
            POP_ASSUM_LIST (K all_tac) >> simp[cs_extends_def] >>
            rpt strip_tac >> gvs[]) >>
         qpat_assum `fn_has_code sa sb func` mp_tac >>
         rewrite_tac[fragExecTheory.fn_has_code_def] >>
         disch_then (CONJUNCTS_THEN2 kall_tac
           (qx_choose_then `ab` strip_assume_tac)) >>
         qexists_tac `ab` >> conj_tac
         >- (qpat_x_assum `sb.cs_current_bb = sa.cs_current_bb` (SUBST_ALL_TAC o SYM) >>
             asm_rewrite_tac[]) >>
         qpat_assum `get_instruction cb a.vs_inst_idx = SOME inst` mp_tac >>
         qpat_assum `cb = <|bb_label := _; bb_instructions := _|>` mp_tac >>
         qpat_assum `sa.cs_blocks = sb.cs_blocks ==> _` mp_tac >>
         qpat_assum `sa.cs_blocks = sb.cs_blocks` mp_tac >>
         qpat_assum `LENGTH ids = LENGTH sa.cs_current_insts` mp_tac >>
         qpat_assum `sb.cs_current_insts <<= ab.bb_instructions` mp_tac >>
         qpat_assum `sa.cs_current_insts <<= sb.cs_current_insts` mp_tac >>
         qpat_assum `a.vs_inst_idx < LENGTH B.cs_current_insts` mp_tac >>
         qpat_assum `a.vs_current_bb = ell ==> _` mp_tac >>
         qpat_assum `a.vs_current_bb = ell` mp_tac >>
         qpat_assum `u'.vs_inst_idx = _` mp_tac >>
         POP_ASSUM_LIST (K all_tac) >> simp[] >> rpt strip_tac >>
         gvs[IS_PREFIX_APPEND, get_instruction_def, DROP_LENGTH_APPEND,
             EL_APPEND_EQN]) >>
     `canon = frag_relabel_observer sa sb ell ids func id /\
      frag_observer_cut B = frag_observer_cut sb` by
       simp[Abbr `B`, start_swap_def, frag_observer_cut_def] >>
     simp[] >>
     irule frag_relabel_instruction_agrees >>
     asm_rewrite_tac[] >> qexistsl_tac [`cb`,`id`,`ids`,`sb`] >>
     qpat_x_assum `canon = frag_relabel_observer _ _ _ _ _ _`
       (SUBST_ALL_TAC o SYM) >>
     qpat_x_assum `frag_observer_cut B = frag_observer_cut sb`
       (SUBST_ALL_TAC o SYM) >> simp[]
QED

Resume compile_store_slots_static_origin_ptr_path[assemble]:
  `ys <> []` by (strip_tac >> gvs[]) >>
  qabbrev_tac `v0 = FST (LAST ys)` >>
  `HD ys = (s0,G,tn) /\ LAST ys = (v0,Gu,tnu) /\
   frag_relabel_state ell sa.cs_current_bb u v0` by
    (qpat_assum `!i. i < LENGTH pre ==> _` (qspec_then `0` mp_tac) >>
     qpat_assum `!i. i < LENGTH pre ==> _`
       (qspec_then `LENGTH pre - 1` mp_tac) >>
     qpat_assum `HD pre = _` mp_tac >>
     qpat_assum `LAST pre = _` mp_tac >>
     qpat_assum `FST (HD ys) = _` mp_tac >>
     qpat_assum `LENGTH ys = LENGTH pre` mp_tac >>
     qpat_assum `pre <> []` mp_tac >> qpat_assum `ys <> []` mp_tac >>
     qpat_x_assum `Abbrev (v0 = _)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     rpt strip_tac >>
     `0 < LENGTH pre` by (Cases_on `pre` >> gvs[]) >>
     `EL (LENGTH pre - 1) ys = LAST ys /\
      EL (LENGTH pre - 1) pre = LAST pre` by
       metis_tac[LAST_EL, PRE_SUB1] >>
     gvs[Abbr `v0`, EL] >>
     Cases_on `HD ys` >> Cases_on `LAST ys` >> gvs[]) >>
  `!n a Ga tna b Gb tnb.
    SUC n < LENGTH ys /\ EL n ys = (a,Ga,tna) /\
    EL (SUC n) ys = (b,Gb,tnb) ==>
    ?bb i. lookup_block a.vs_current_bb func.fn_blocks = SOME bb /\
      get_instruction bb a.vs_inst_idx = SOME i /\
      MEM i.inst_opcode [ASSIGN;ADD;MUL;EQ;LT;ISZERO;SHR;MLOAD;JMP;JNZ] /\
      gas_origin_ptr_edge (ARB,lo,explicit,ctx,func,PG)
        (a,Ga,tna) [] (OK b,Gb,tnb)` by suspend "ys_fetch" >>
  drule store_slots_readonly_list_horizon >> disch_then assume_tac >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
    (s0 with vs_call_ctx := (s0.vs_call_ctx with cc_static := T),G,tn) []
    (OK (v0 with vs_call_ctx := (v0.vs_call_ctx with cc_static := T)),Gu,tnu)` by
    (irule store_slots_readonly_prefix_static >>
     (conj_tac >- simp[Abbr `s0`]) >>
     qexists_tac `ys` >> asm_rewrite_tac[]) >>
  `!a Ga tna b Gb tnb.
    (a.vs_current_bb,a.vs_inst_idx) IN frag_observer_region A B /\
    (a.vs_current_bb,a.vs_inst_idx) <> frag_observer_cut B /\
    gas_origin_ptr_edge (ARB,lo,explicit,ctx,canon,PG)
      (a,Ga,tna) [] (OK b,Gb,tnb) ==>
    abi_observer_step ctx canon (frag_observer_cut B) a b` by
    suspend "observer_edge" >>
  qabbrev_tac `ms = MAP FST pre` >>
  `ms <> [] /\ HD ms = a0 /\ LAST ms = u /\ LENGTH ms = SUC k` by
    (simp[Abbr `ms`, MAP_EQ_NIL, MAP_HD, LAST_MAP]) >>
  `!n. SUC n < LENGTH ms ==>
    let a = EL n ms in let b = EL (SUC n) ms in
      (a.vs_current_bb,a.vs_inst_idx) <> frag_observer_cut B /\
      ~a.vs_halted /\ ~b.vs_halted /\
      ?bb i mid.
        lookup_block a.vs_current_bb canon.fn_blocks = SOME bb /\
        get_instruction bb a.vs_inst_idx = SOME i /\
        MEM i.inst_opcode [ASSIGN;ADD;MUL;EQ;LT;ISZERO;SHR;MLOAD;JMP;JNZ] /\
        step_inst 0 ctx i a = OK mid /\
        b = (if is_terminator i.inst_opcode then mid
             else mid with vs_inst_idx := SUC a.vs_inst_idx) /\
        (is_terminator i.inst_opcode ==>
          mid.vs_inst_idx = 0 /\
          ?target. lookup_block mid.vs_current_bb canon.fn_blocks = SOME target /\
            phi_prefix_length target.bb_instructions = 0)` by suspend "raw_prefix" >>
  `(type_slot_size tv = 0 <=>
     (u.vs_current_bb,u.vs_inst_idx) = frag_observer_cut B)` by
    (eq_tac >- suspend "zero_cut" >> suspend "positive_cut") >>
  suspend "finish"
QED

Resume compile_store_slots_static_origin_ptr_path[ys_fetch]:
  rpt gen_tac >> strip_tac >>
  `n < LENGTH pre /\ SUC n < LENGTH pre` by (gvs[] >> decide_tac) >>
  Cases_on `EL n pre` >> rename1 `EL n pre = (ca,ghosts)` >>
  Cases_on `ghosts` >> rename1 `EL n pre = (ca,cG,ctn)` >>
  Cases_on `EL (SUC n) pre` >> rename1 `EL (SUC n) pre = (cb,ghosts)` >>
  Cases_on `ghosts` >> rename1 `EL (SUC n) pre = (cb,dG,dtn)` >>
  qpat_assum `!i. i < LENGTH pre ==> _` (qspec_then `n` mp_tac) >>
  (impl_tac >- simp[]) >> disch_then (strip_assume_tac o SRULE []) >>
  qpat_assum `!n a Ga tna b Gb tnb. SUC n < LENGTH pre /\ _ ==> _`
    (qspecl_then [`n`,`ca`,`cG`,`ctn`,`cb`,`dG`,`dtn`] mp_tac) >>
  simp[] >>
  disch_then (qx_choose_then `bb` (qx_choose_then `inst`
    (REPEAT_TCL CONJUNCTS_THEN assume_tac))) >>
  `EL n xs = (ca,cG,ctn) /\ n < k` by
    (qpat_assum `Abbrev (pre = _)` mp_tac >>
     qpat_assum `EL n pre = _` mp_tac >>
     qpat_assum `SUC n < LENGTH pre` mp_tac >>
     qpat_assum `k < LENGTH xs` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     rpt strip_tac >> gvs[Abbr `pre`, EL_TAKE, LENGTH_TAKE] >> decide_tac) >>
  `frag_relabel_state ell sa.cs_current_bb ca a` by
    (qpat_assum `frag_relabel_state _ _ (FST _) (FST _)` mp_tac >>
     qpat_assum `EL n pre = _` mp_tac >>
     qpat_assum `EL n ys = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[]) >>
  `(ca.vs_current_bb,ca.vs_inst_idx) IN frag_observer_region A B` by
    (qpat_assum `!n a Ga tna. n <= k /\ _ ==> _`
      (qspecl_then [`n`,`ca`,`cG`,`ctn`] mp_tac) >> simp[]) >>
  `(ca.vs_current_bb,ca.vs_inst_idx) <> frag_observer_cut B` by
    (qpat_assum `!n a Ga tna. n < k /\ _ ==> _`
      (qspecl_then [`n`,`ca`,`cG`,`ctn`] mp_tac) >> simp[]) >>
  `?ab. lookup_block a.vs_current_bb func.fn_blocks = SOME ab /\
    get_instruction ab a.vs_inst_idx = SOME inst` by
    (first_x_assum irule >> qexistsl_tac [`ca`,`bb`] >> simp[]) >>
  qexistsl_tac [`ab`,`inst`] >> asm_rewrite_tac[] >>
  qpat_assum `!i. SUC i < LENGTH ys ==> _` (qspec_then `n` mp_tac) >>
  qpat_assum `EL n ys = _` mp_tac >>
  qpat_assum `EL (SUC n) ys = _` mp_tac >>
  qpat_assum `SUC n < LENGTH ys` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> simp[]
QED

Resume compile_store_slots_static_origin_ptr_path[finish]:
  qabbrev_tac `t = v0 with vs_call_ctx := (v0.vs_call_ctx with cc_static := T)` >>
  `s0 with vs_call_ctx := (s0.vs_call_ctx with cc_static := T) = s` by
    (qpat_assum `s.vs_call_ctx.cc_static` mp_tac >>
     qpat_assum `Abbrev (s0 = _)` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
     simp[Abbr `s0`, venom_state_component_equality, call_context_component_equality]) >>
  `!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG)
     (s,G,tn) [] (OK t,Gu,tnu)` by
    (qpat_assum `!D. gas_origin_ptr_path _ (s0 with vs_call_ctx := _,_,_) [] _` mp_tac >>
     qpat_assum `s0 with vs_call_ctx := _ = s` (fn th => rewrite_tac [th]) >>
     simp[Abbr `t`]) >>
  `(type_slot_size tv <> 0 ==>
     (!D. gas_origin_ptr_path (D,lo,explicit,ctx,func,PG) (t,Gu,tnu) []
       (Abort ExHalt_abort (halt_state (set_returndata [] t)),Gu,tnu)) /\
     ?bb inst. lookup_block t.vs_current_bb func.fn_blocks = SOME bb /\
       get_instruction bb t.vs_inst_idx = SOME inst /\
       inst.inst_opcode = (if tr then TSTORE else SSTORE) /\
       step_inst_base inst t = Abort ExHalt_abort (halt_state (set_returndata [] t)))` by
    suspend "positive_exit" >>
  qexistsl_tac [`t`,`Gu`,`tnu`] >>
  conj_tac >-
    (qx_gen_tac `D` >> IF_CASES_TAC
     >- qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) [] (OK t,Gu,tnu)`
          (qspec_then `D` ACCEPT_TAC) >>
     `type_slot_size tv <> 0` by
       (qpat_assum `type_slot_size tv = 0 <=> _` mp_tac >>
        (simp[])) >>
     irule fragGasOriginPtrLoopTheory.gas_origin_ptr_path_trans >>
     qexistsl_tac [`Gu`,`t`,`tnu`] >> conj_tac
     >- qpat_assum `!D. gas_origin_ptr_path _ (s,G,tn) [] (OK t,Gu,tnu)`
          (qspec_then `D` ACCEPT_TAC) >>
     qpat_assum `type_slot_size tv <> 0 ==> _ /\ ?bb inst. _`
       (fn imp => qpat_assum `type_slot_size tv <> 0`
         (fn nz => qspec_then `D` ACCEPT_TAC (CONJUNCT1 (MP imp nz))))) >>
  reverse (rpt conj_tac)
  >- (qpat_assum `type_slot_size tv <> 0 ==> _ /\ ?bb inst. _` mp_tac >>
      POP_ASSUM_LIST (K all_tac) >> tautLib.TAUT_TAC)
  >- suspend "zero_cursor"
  >> suspend "common_frame"
QED

Resume compile_store_slots_static_origin_ptr_path[zero_cursor]:
  strip_tac >>
  `(u.vs_current_bb,u.vs_inst_idx) = frag_observer_cut B` by
    (qpat_assum `type_slot_size tv = 0 <=> _` mp_tac >>
     qpat_assum `type_slot_size tv = 0` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> tautLib.TAUT_TAC) >>
  drule frag_relabel_state_fields >>
  qpat_assum `(u.vs_current_bb,u.vs_inst_idx) = frag_observer_cut B` mp_tac >>
  qpat_assum `LENGTH B.cs_current_insts = LENGTH sb.cs_current_insts` mp_tac >>
  qpat_assum `sa.cs_blocks = sb.cs_blocks ==> B.cs_current_bb = ell /\ _` mp_tac >>
  qpat_assum `sa.cs_blocks <> sb.cs_blocks ==> B.cs_current_bb = sb.cs_current_bb /\ _` mp_tac >>
  qpat_assum `cs_extends sa sb` mp_tac >>
  qpat_assum `ell <> sb.cs_current_bb` mp_tac >>
  qpat_assum `Abbrev (t = _)` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
  Cases_on `sa.cs_blocks = sb.cs_blocks` >>
  gvs[Abbr `t`, frag_observer_cut_def, cs_extends_def]
QED

Resume compile_store_slots_static_origin_ptr_path[common_frame]:
  markerLib.RESUME_TAC >>
  qpat_assum `store_copy_normalize a0 u = a0` mp_tac >>
  qpat_assum `!x. not_fresh_at A x ==> lookup_var x u = _ /\ _` mp_tac >>
  qpat_assum `tnu.t_mem = tn.t_mem` mp_tac >>
  qpat_assum `tnu.t_imm = tn.t_imm` mp_tac >>
  qpat_assum `tnu.t_stor = tn.t_stor` mp_tac >>
  qpat_assum `tnu.t_trans = tn.t_trans` mp_tac >>
  qpat_assum `~u.vs_halted` mp_tac >>
  qpat_assum `frag_relabel_state ell sa.cs_current_bb u v0` mp_tac >>
  qpat_assum `A.cs_next_var = sa.cs_next_var` mp_tac >>
  qpat_assum `s.vs_call_ctx.cc_static` mp_tac >>
  qpat_assum `Abbrev (t = _)` mp_tac >>
  qpat_assum `Abbrev (a0 = _)` mp_tac >>
  qpat_assum `Abbrev (s0 = _)` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >>
  gvs[frag_relabel_state_def, Abbr `t`, Abbr `a0`, Abbr `s0`,
      stmtSimStoreCopyTheory.store_copy_normalize_def,
      lookup_var_def, loweringStateRelDefsTheory.not_fresh_at_def,
      venom_state_component_equality, call_context_component_equality]
QED

Resume compile_store_slots_static_origin_ptr_path[observer_edge]:
  rpt gen_tac >> strip_tac >>
  `!i lbl. MEM i (frag_code A B) /\ MEM i.inst_opcode [JMP;JNZ] /\
     MEM (Label lbl) i.inst_operands ==>
     lbl <> A.cs_current_bb /\ ?bb. lookup_block lbl canon.fn_blocks = SOME bb` by
    (qpat_assum `!i l. _ ==> l <> A.cs_current_bb /\ _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> simp[MEM] >> metis_tac[]) >>
  qpat_assum `frag_observer A B canon id = canon` (fn th =>
    drule_at (Pat `gas_origin_ptr_edge _ _ _ _`) (REWRITE_RULE [th]
      (Q.INST [`sa` |-> `A`, `sb` |-> `B`, `func` |-> `canon`,
               `id` |-> `id`]
        store_slots_observer_edge_step))) >>
  simp[MEM] >> metis_tac[]
QED

Resume compile_store_slots_static_origin_ptr_path[raw_prefix]:
  qx_gen_tac `n` >> strip_tac >> simp[LET_THM] >>
  `SUC n < LENGTH pre /\ n < k /\ n < LENGTH pre` by (simp[] >> decide_tac) >>
  `n < LENGTH xs /\ SUC n < LENGTH xs` by decide_tac >>
  Cases_on `EL n pre` >> rename1 `EL n pre = (a,gh)` >>
  Cases_on `gh` >> rename1 `EL n pre = (a,Ga,tna)` >>
  Cases_on `EL (SUC n) pre` >> rename1 `EL (SUC n) pre = (b,gh)` >>
  Cases_on `gh` >> rename1 `EL (SUC n) pre = (b,Gb,tnb)` >>
  `EL n xs = (a,Ga,tna) /\ EL (SUC n) xs = (b,Gb,tnb)` by
    (qpat_assum `Abbrev (pre = _)` mp_tac >>
     qpat_assum `EL n pre = _` mp_tac >> qpat_assum `EL (SUC n) pre = _` mp_tac >>
     qpat_assum `n < k` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
     `n < SUC k /\ SUC n < SUC k` by decide_tac >>
     gvs[Abbr `pre`, EL_TAKE]) >>
  qpat_assum `!n a Ga tna. n <= k /\ _ ==> _`
    (qspecl_then [`n`,`a`,`Ga`,`tna`] mp_tac) >>
  (impl_tac >- (simp[] >> decide_tac)) >> disch_tac >>
  qpat_assum `!n a Ga tna. n < k /\ _ ==> _`
    (qspecl_then [`n`,`a`,`Ga`,`tna`] mp_tac) >> simp[] >>
  disch_then (CONJUNCTS_THEN2 assume_tac kall_tac) >>
  qpat_assum `!n a Ga tna b Gb tnb. SUC n < LENGTH pre /\ _ ==> _`
    (qspecl_then [`n`,`a`,`Ga`,`tna`,`b`,`Gb`,`tnb`] mp_tac) >> simp[] >>
  disch_then (qx_choose_then `bb` (qx_choose_then `i`
    (REPEAT_TCL CONJUNCTS_THEN assume_tac))) >>
  qpat_assum `!a Ga tna b Gb tnb. _ ==> abi_observer_step _ _ _ _ _`
    (qspecl_then [`a`,`Ga`,`tna`,`b`,`Gb`,`tnb`] mp_tac) >>
  simp[abi_observer_step_def] >>
  disch_then (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac strip_assume_tac)) >>
  simp[Abbr `ms`, EL_MAP, IgnAsm `b = _`] >- simp[] >>
  `middle.vs_inst_idx = 0` by suspend "jump_index" >>
  `phi_prefix_length target.bb_instructions = 0` by
    (qpat_assum `!fuel mid target. _ ==> phi_prefix_length _ = 0`
       (qspecl_then [`0`,`middle`,`target`] mp_tac) >> simp[]) >>
  `entered = middle` by metis_tac[eval_phis_no_phi, exec_result_11] >>
  simp[venom_state_component_equality] >> metis_tac[]
QED

Resume compile_store_slots_static_origin_ptr_path[jump_index]:
  qpat_assum `i.inst_opcode = ASSIGN \/ _` mp_tac >>
  qpat_assum `is_terminator i.inst_opcode` mp_tac >>
  qpat_assum `step_inst 0 ctx i a = OK middle` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >>
  simp[is_terminator_def] >> rpt strip_tac >>
  gvs[is_terminator_def, step_inst_non_invoke, step_inst_base_JMP,
      step_inst_base_JNZ, AllCaseEqs(), jump_to_def]
QED

Resume compile_store_slots_static_origin_ptr_path[zero_cut]:
  strip_tac >>
  mp_tac (Q.INST [`sa` |-> `A`, `sb` |-> `B`, `s` |-> `a0`,
                  `func` |-> `canon`] slots_zero_readonly_completion) >>
  (impl_tac >- asm_rewrite_tac[]) >>
  disch_then (qx_choose_then `zs` (REPEAT_TCL CONJUNCTS_THEN assume_tac)) >>
  `!n. n < LENGTH ms /\ n < LENGTH zs ==> EL n ms = EL n zs` by
    suspend "zero_agree" >>
  `0 < LENGTH zs` by (simp[LENGTH_NON_NIL]) >>
  `EL (LENGTH zs - 1) zs = LAST zs` by simp[LAST_EL, PRE_SUB1] >>
  `EL k ms = u` by
    (qpat_assum `LAST ms = u` mp_tac >> qpat_assum `LENGTH ms = SUC k` mp_tac >>
     qpat_assum `ms <> []` mp_tac >> POP_ASSUM_LIST (K all_tac) >>
     rpt disch_tac >> drule LAST_EL >> simp[PRE_SUB1]) >>
  `LENGTH ms <= LENGTH zs` by
    (spose_not_then assume_tac >>
     `SUC (LENGTH zs - 1) < LENGTH ms` by decide_tac >>
     `LENGTH zs - 1 < LENGTH ms /\ LENGTH zs - 1 < LENGTH zs` by decide_tac >>
     `EL (LENGTH zs - 1) ms = LAST zs` by simp[] >>
     qpat_assum `!n. SUC n < LENGTH ms ==> _`
       (qspec_then `LENGTH zs - 1` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     rewrite_tac[LET_THM] >> BETA_TAC >>
     disch_then (CONJUNCTS_THEN2 mp_tac kall_tac) >>
     qpat_assum `EL (LENGTH zs - 1) ms = LAST zs` SUBST1_TAC >>
     simp[frag_observer_cut_def]) >>
  `k < LENGTH ms /\ k < LENGTH zs` by decide_tac >>
  `EL k zs = u` by
    (qpat_assum `!n. n < LENGTH ms /\ _ ==> _` (qspec_then `k` mp_tac) >>
     simp[]) >>
  Cases_on `LENGTH ms = LENGTH zs`
  >- (`k = LENGTH zs - 1` by decide_tac >>
      qpat_assum `EL k zs = u` mp_tac >>
      simp[frag_observer_cut_def] >> metis_tac[frag_observer_cut_def]) >>
  `SUC k < LENGTH zs` by decide_tac >>
  spose_not_then assume_tac >>
  qpat_assum `!a Ga tna. (u,Gu,tnu) = _ ==> _`
    (qspecl_then [`u`,`Gu`,`tnu`] mp_tac) >>
  rewrite_tac[] >>
  disch_then (DISJ_CASES_THEN2 (fn th =>
    qpat_assum `(u.vs_current_bb,u.vs_inst_idx) <> frag_observer_cut B`
      (fn nth => CONTR_TAC (MP nth th))) strip_assume_tac) >>
  qpat_assum `!j. SUC j < LENGTH zs ==> _` (qspec_then `k` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  qpat_assum `EL k zs = u` SUBST1_TAC >>
  qpat_assum `lookup_block u.vs_current_bb (frag_observer A B canon id).fn_blocks = _` mp_tac >>
  qpat_assum `frag_observer A B canon id = canon` SUBST1_TAC >>
  qpat_assum `get_instruction _ u.vs_inst_idx = _` mp_tac >>
  qpat_assum `_.inst_opcode = (if tr then TSTORE else SSTORE)` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> Cases_on `tr` >> gvs[MEM]
QED

Resume compile_store_slots_static_origin_ptr_path[zero_agree]:
  Induct >- (strip_tac >> metis_tac[EL]) >> strip_tac >>
  `n < LENGTH ms /\ n < LENGTH zs` by decide_tac >>
  `EL n ms = EL n zs` by simp[] >>
  qpat_assum `!n. SUC n < LENGTH ms ==> _` (qspec_then `n` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  qpat_assum `!j. SUC j < LENGTH zs ==> _` (qspec_then `n` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  qpat_assum `EL n ms = EL n zs` SUBST1_TAC >>
  POP_ASSUM_LIST (K all_tac) >> rewrite_tac[LET_THM] >> BETA_TAC >>
  rpt strip_tac >> gvs[]
QED

Resume compile_store_slots_static_origin_ptr_path[positive_cut]:
  disch_tac >> spose_not_then assume_tac >>
  `?j. MEM j (MAP FST writes)` by
    metis_tac[slots_encoding_positive_support] >>
  `!j. MEM j (MAP FST writes) ==> j < type_slot_size tv` by
    metis_tac[CONJUNCT1 vyperEncodeDecodeTheory.encode_writes_bounded] >>
  mp_tac (Q.INST [`tr` |-> `tr`, `key` |-> `dw+n2w j`, `s` |-> `a0`,
    `t` |-> `u`, `ks` |-> `ks`, `dw` |-> `dw`, `sw` |-> `sw`,
    `value` |-> `mload (w2n sw+32*j) a0`,
    `R` |-> `local_prefix ctx canon (frag_observer_cut B)`,
    `success` |-> `(\a b. (a.vs_current_bb,a.vs_inst_idx) IN frag_observer_region A B /\
        (b.vs_current_bb,b.vs_inst_idx) = frag_observer_cut B /\
        ?Gb tnb. gas_origin_ptr_path (ARB,lo,explicit,ctx,canon,PG)
          (a,G,tn) [] (OK b,Gb,tnb))`]
    (Q.INST_TYPE [`:'a` |-> `:256`] slots_readonly_positive_separation)) >>
  BETA_TAC >> (impl_tac >- (conj_tac >- suspend "bank_replay" >>
    conj_tac >- suspend "bank_unique" >>
    conj_tac >- suspend "bank_completion" >> suspend "bank_selected")) >>
  simp[]
QED

Resume compile_store_slots_static_origin_ptr_path[bank_replay]:
  qx_gen_tac `w` >>
  qabbrev_tac `aw = (if tr then tstore else sstore) (dw+n2w j) w a0` >>
  qabbrev_tac `uw = (if tr then tstore else sstore) (dw+n2w j) w u` >>
  qabbrev_tac `bm = MAP (\q. q with <|vs_transient := aw.vs_transient;
                                        vs_accounts := aw.vs_accounts|>) ms` >>
  `HD bm = aw /\ LAST bm = uw /\ LENGTH bm = SUC k` by
    suspend "bank_endpoints" >>
  mp_tac (Q.SPECL [`ms`,`0`,`ctx`,`canon`,`aw.vs_accounts`,`aw.vs_transient`]
    slots_readonly_bank_replay) >>
  (impl_tac >- (rpt strip_tac >>
    qpat_assum `!n. SUC n < LENGTH ms ==> _` (qspec_then `n` mp_tac) >>
    (impl_tac >- first_assum ACCEPT_TAC) >>
    rewrite_tac[LET_THM] >> BETA_TAC >>
    disch_then (CONJUNCTS_THEN2 kall_tac (CONJUNCTS_THEN2 kall_tac
      (CONJUNCTS_THEN2 kall_tac (qx_choose_then `bb` (qx_choose_then `i`
        (qx_choose_then `mid` (REPEAT_TCL CONJUNCTS_THEN assume_tac))))))) >>
    qexistsl_tac [`bb`,`i`,`mid`] >> asm_rewrite_tac[])) >>
  rewrite_tac[LET_THM] >> BETA_TAC >>
  qpat_assum `Abbrev (bm = _)` (fn th => rewrite_tac [GSYM (REWRITE_RULE[markerTheory.Abbrev_def] th)]) >>
  disch_then (REPEAT_TCL CONJUNCTS_THEN assume_tac) >>
  `!n. SUC n < LENGTH bm ==>
    abi_observer_step ctx canon (frag_observer_cut B) (EL n bm) (EL (SUC n) bm)` by
    suspend "bank_adjacent" >>
  `!d n. n+d = k ==> local_prefix ctx canon (frag_observer_cut B) (EL n bm) uw` by
    suspend "bank_induct" >>
  `bm <> []` by (strip_tac >> gvs[]) >>
  `EL 0 bm = aw` by simp[EL] >>
  qpat_assum `!d n. n+d = k ==> _` (qspecl_then [`k`,`0`] mp_tac) >>
  (impl_tac >- simp[]) >> asm_rewrite_tac[]
QED

Resume compile_store_slots_static_origin_ptr_path[bank_endpoints]:
  `u.vs_accounts = a0.vs_accounts /\ u.vs_transient = a0.vs_transient` by
    (qpat_assum `store_copy_normalize a0 u = a0` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >>
     simp[stmtSimStoreCopyTheory.store_copy_normalize_def,
          venom_state_component_equality]) >>
  Cases_on `tr` >>
  simp[Abbr `bm`, MAP_HD, LAST_MAP, Abbr `aw`, Abbr `uw`,
       sstore_def, tstore_def, LET_THM, venom_state_component_equality]
QED

Resume compile_store_slots_static_origin_ptr_path[bank_induct]:
  Induct >-
    (simp[] >>
     `bm <> []` by (strip_tac >> gvs[]) >>
     `EL k bm = uw` by
       (qpat_assum `bm <> []` (mp_tac o MATCH_MP LAST_EL) >> simp[PRE_SUB1]) >>
     simp[] >> irule (cj 1 local_prefix_rules) >>
     Cases_on `tr` >> simp[Abbr `uw`, sstore_def, tstore_def, LET_THM]) >>
  rpt strip_tac >>
  `SUC n < LENGTH bm /\ SUC n + d = k` by (simp[] >> decide_tac) >>
  irule (cj 2 local_prefix_rules) >> qexists_tac `EL (SUC n) bm` >> simp[]
QED

Resume compile_store_slots_static_origin_ptr_path[bank_adjacent]:
  qx_gen_tac `n` >> strip_tac >>
  qmatch_goalsub_abbrev_tac `abi_observer_step _ _ _ (EL _ bm) _` >>
  `SUC n < LENGTH ms /\ n < LENGTH ms` by (simp[] >> decide_tac) >>
  qpat_assum `!n. SUC n < LENGTH ms ==> let a = _ in _`
    (qspec_then `n` mp_tac) >> (impl_tac >- first_assum ACCEPT_TAC) >>
  rewrite_tac[LET_THM] >> BETA_TAC >>
  disch_then (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac (qx_choose_then `bb` (qx_choose_then `i`
      (qx_choose_then `mid` (REPEAT_TCL CONJUNCTS_THEN assume_tac))))))) >>
  qpat_assum `!n. SUC n < LENGTH ms ==> ?bb i mid. _`
    (qspec_then `n` mp_tac) >> (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (qx_choose_then `bb'` (qx_choose_then `i'`
    (qx_choose_then `mid'` (REPEAT_TCL CONJUNCTS_THEN assume_tac)))) >>
  `EL n bm = (EL n ms) with <|vs_transient := aw.vs_transient;
                              vs_accounts := aw.vs_accounts|> /\
   EL (SUC n) bm = (EL (SUC n) ms) with <|vs_transient := aw.vs_transient;
                                        vs_accounts := aw.vs_accounts|>` by
    (qpat_assum `Abbrev (bm = _)` mp_tac >>
     qpat_assum `n < LENGTH ms` mp_tac >>
     qpat_assum `SUC n < LENGTH ms` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >> simp[Abbr `bm`, EL_MAP]) >>
  `bb' = bb /\ i' = i` by
    (qpat_assum `lookup_block (EL n bm).vs_current_bb _ = SOME bb'` mp_tac >>
     qpat_assum `lookup_block (EL n ms).vs_current_bb _ = SOME bb` mp_tac >>
     qpat_assum `get_instruction bb' (EL n ms).vs_inst_idx = SOME i'` mp_tac >>
     qpat_assum `get_instruction bb (EL n ms).vs_inst_idx = SOME i` mp_tac >>
     qpat_assum `EL n bm = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >> gvs[]) >>
  rewrite_tac[abi_observer_step_def] >>
  conj_tac >- simp[] >> conj_tac >- simp[] >> conj_tac >- (simp[] >> (metis_tac[])) >>
  qexistsl_tac [`bb'`,`i'`,`mid'`] >>
  conj_tac >- first_assum ACCEPT_TAC >> conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (qpat_assum `i' = i` SUBST1_TAC >>
    qpat_assum `MEM i.inst_opcode _` mp_tac >>
    POP_ASSUM_LIST (K all_tac) >> simp[MEM] >> rpt strip_tac >> gvs[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qpat_assum `i' = i` SUBST_ALL_TAC >>
  reverse (Cases_on `is_terminator i.inst_opcode`)
  >- (disj1_tac >> conj_tac >- first_assum ACCEPT_TAC >>
      qpat_assum `EL (SUC n) bm = (if _ then _ else _)` SUBST1_TAC >>
      qpat_assum `EL n bm = _ with <|vs_transient := _; vs_accounts := _|>` SUBST1_TAC >>
      simp[]) >>
  disj2_tac >> conj_tac >- first_assum ACCEPT_TAC >>
  qpat_assum `is_terminator i.inst_opcode ==> _` mp_tac >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (CONJUNCTS_THEN2 assume_tac (qx_choose_then `target` strip_assume_tac)) >>
  `mid' = mid with <|vs_transient := aw.vs_transient; vs_accounts := aw.vs_accounts|>` by
    (qpat_assum `EL (SUC n) bm = _ with <|vs_transient := _; vs_accounts := _|>` mp_tac >>
     qpat_assum `EL (SUC n) bm = (if _ then _ else _)` mp_tac >>
     qpat_assum `EL (SUC n) ms = (if _ then _ else _)` mp_tac >>
     qpat_assum `is_terminator i.inst_opcode` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >> gvs[]) >>
  conj_tac >-
    (qpat_assum `mid' = _ with <|vs_transient := _; vs_accounts := _|>` SUBST1_TAC >>
     qpat_assum `EL (SUC n) ms = (if _ then _ else _)` mp_tac >>
     qpat_assum `~(EL (SUC n) ms).vs_halted` mp_tac >>
     qpat_assum `is_terminator i.inst_opcode` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> rpt strip_tac >> gvs[]) >>
  qexistsl_tac [`target`,`mid'`] >>
  qpat_assum `EL (SUC n) bm = (if _ then _ else _)` SUBST1_TAC >>
  simp[eval_phis_no_phi, venom_state_component_equality]
QED

Resume compile_store_slots_static_origin_ptr_path[bank_unique]:
  rpt strip_tac >>
  qpat_assum `frag_observer A B canon id = canon` (fn th =>
    drule_at (Pat `gas_origin_ptr_path _ _ _ _`) (REWRITE_RULE [th]
      (Q.INST [`sa` |-> `A`, `sb` |-> `B`, `func` |-> `canon`,
               `id` |-> `id`] store_slots_observer_cut_unique))) >>
  asm_rewrite_tac[] >> simp[]
QED

Resume compile_store_slots_static_origin_ptr_path[bank_selected]:
  qx_gen_tac `w` >>
  qabbrev_tac `aw = (if tr then tstore else sstore) (dw+n2w j) w a0` >>
  `!p. mload p aw = mload p a0` by
    (Cases_on `tr` >> simp[Abbr `aw`, sstore_def, tstore_def, LET_THM, mload_def]) >>
  qpat_assum `!p. mload p aw = _` (fn th =>
    mp_tac (REWRITE_RULE [th] (Q.INST [`s` |-> `aw`]
      (Q.INST_TYPE [`:'a` |-> `:bytes32`] slots_fold_selected_key)))) >>
  asm_rewrite_tac[] >> simp[]
QED

Resume compile_store_slots_static_origin_ptr_path[bank_completion]:
  qx_gen_tac `w` >>
  qabbrev_tac `aw = (if tr then tstore else sstore) (dw+n2w j) w a0` >>
  `!op. eval_operand op aw = eval_operand op a0` by
    (gen_tac >> Cases_on `op` >> Cases_on `tr` >>
     simp[Abbr `aw`, sstore_def, tstore_def, LET_THM, eval_operand_def, lookup_var_def]) >>
  `!p. mload p aw = mload p a0` by
    (Cases_on `tr` >> simp[Abbr `aw`, sstore_def, tstore_def, LET_THM, mload_def]) >>
  `(type_memory_size tv <> 0 ==>
      ?x. src = Var x /\ ptr_covers G tn x aw (type_memory_size tv)) /\
   (!mem. mem_agree_outside tn.t_mem aw.vs_memory mem ==>
      val_in_memory tv v (w2n sw) mem) /\
   (ctx_has_dalloca ctx ==> allocas_below_fmp aw) /\
   allocas_from lo aw /\ lo <= aw.vs_alloca_next /\
   (type_memory_size tv = 0 \/ w2n sw + type_memory_size tv <= aw.vs_alloca_next) /\
   ~aw.vs_call_ctx.cc_static /\ ~aw.vs_halted /\
   aw.vs_current_bb = A.cs_current_bb /\
   aw.vs_inst_idx = LENGTH A.cs_current_insts` by suspend "bank_input" >>
  mp_tac (Q.INST [`sa` |-> `A`, `sb` |-> `B`,
                  `s` |-> `aw`, `func` |-> `canon`]
    (SPEC_ALL compile_store_slots_origin_ptr_path)) >>
  (impl_tac >- (asm_rewrite_tac[] >> simp[])) >>
  disch_then (qx_choose_then `bw` (qx_choose_then `kw`
    (qx_choose_then `Gw` (qx_choose_then `tnw`
      (REPEAT_TCL CONJUNCTS_THEN assume_tac))))) >>
  qexists_tac `bw` >>
  `(aw.vs_current_bb,aw.vs_inst_idx) IN frag_observer_region A B /\
   (bw.vs_current_bb,bw.vs_inst_idx) = frag_observer_cut B /\
   ?Gb tnb. gas_origin_ptr_path (ARB,lo,explicit,ctx,canon,PG)
      (aw,G,tn) [] (OK bw,Gb,tnb)` suffices_by
    (disch_then (fn th => rewrite_tac [th]) >> suspend "bank_load") >>
    (`(a0.vs_current_bb,a0.vs_inst_idx) IN frag_observer_region A B` by
       (qpat_assum `!n a Ga tna. n <= k /\ _ ==> _`
         (qspecl_then [`0`,`a0`,`G`,`tn`] mp_tac) >> simp[EL]) >>
     `(aw.vs_current_bb,aw.vs_inst_idx) IN frag_observer_region A B` by
       (qpat_assum `(a0.vs_current_bb,a0.vs_inst_idx) IN _` mp_tac >>
        qpat_assum `Abbrev (aw = _)` mp_tac >>
        POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
        Cases_on `tr` >> simp[Abbr `aw`, sstore_def, tstore_def, LET_THM]) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- simp[frag_observer_cut_def] >>
     qexistsl_tac [`Gw`,`tnw`] >> simp[])
QED

Resume compile_store_slots_static_origin_ptr_path[bank_input]:
  qpat_assum `Abbrev (aw = _)` mp_tac >>
  qpat_assum `type_memory_size tv <> 0 ==> ?x. _ /\ ptr_covers _ _ _ a0 _` mp_tac >>
  qpat_assum `!mem. mem_agree_outside _ a0.vs_memory mem ==> _` mp_tac >>
  qpat_assum `ctx_has_dalloca ctx ==> allocas_below_fmp a0` mp_tac >>
  qpat_assum `allocas_from lo a0` mp_tac >>
  qpat_assum `lo <= a0.vs_alloca_next` mp_tac >>
  qpat_assum `type_memory_size tv = 0 \/ _ <= s.vs_alloca_next` mp_tac >>
  qpat_assum `Abbrev (a0 = _)` mp_tac >>
  qpat_assum `Abbrev (s0 = _)` mp_tac >>
  qpat_assum `~a0.vs_call_ctx.cc_static` mp_tac >>
  qpat_assum `~a0.vs_halted` mp_tac >>
  qpat_assum `a0.vs_current_bb = A.cs_current_bb` mp_tac >>
  qpat_assum `a0.vs_inst_idx = LENGTH A.cs_current_insts` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >> Cases_on `tr` >>
  gvs[Abbr `aw`, Abbr `a0`, Abbr `s0`, sstore_def, tstore_def, LET_THM,
      ptr_covers_def, lookup_var_def, allocas_below_fmp_def, allocas_from_def] >>
  rpt conj_tac >> rpt strip_tac >> metis_tac[]
QED

Resume compile_store_slots_static_origin_ptr_path[bank_load]:
  markerLib.RESUME_TAC >>
  `(if tr then tload else sload) (dw+n2w j) (store_copy_normalize aw bw) =
    (if tr then tload else sload) (dw+n2w j) bw` by
    (POP_ASSUM_LIST (K all_tac) >> Cases_on `tr` >>
     simp[stmtSimStoreCopyTheory.store_copy_normalize_def,
       sload_def, tload_def, contract_storage_def, contract_transient_def]) >>
  qpat_assum `store_copy_normalize aw bw = _` (fn th =>
    qpat_assum `(if tr then tload else sload) _ (store_copy_normalize aw bw) = _`
      (assume_tac o REWRITE_RULE [th])) >>
  `(if tr then tload else sload) (dw+n2w j)
      (FOLDL (\q k. (if tr then tstore else sstore) (dw+n2w k)
         (mload (w2n sw+32*k) aw) q) aw kw) = mload (w2n sw+32*j) aw` by
    (irule (Q.INST_TYPE [`:'a` |-> `:bytes32`] slots_fold_selected_key) >>
     qexistsl_tac [`tv`,`writes`] >> asm_rewrite_tac[]) >>
  `(if tr then tload else sload) (dw+n2w j)
      (FOLDL (\q k. (if tr then tstore else sstore) (dw+n2w k)
         (mload (w2n sw+32*k) aw) q) aw ks) = mload (w2n sw+32*j) aw` by
    (irule (Q.INST_TYPE [`:'a` |-> `:bytes32`] slots_fold_selected_key) >>
     qexistsl_tac [`tv`,`writes`] >> asm_rewrite_tac[]) >>
  qpat_assum `!p. mload p aw = mload p a0`
    (fn th => rewrite_tac [GSYM th]) >>
  qpat_assum `(if tr then tload else sload) _ (FOLDL _ aw kw) = mload _ aw`
    (fn th => qpat_assum `(if tr then tload else sload) _ (FOLDL _ aw kw) = _ bw`
      (fn eq => rewrite_tac [GSYM (REWRITE_RULE [th] eq)])) >>
  qpat_assum `(if tr then tload else sload) _ (FOLDL _ aw ks) = mload _ aw`
    (fn th => rewrite_tac [th])
QED

Resume compile_store_slots_static_origin_ptr_path[positive_exit]:
  disch_tac >>
  `(u.vs_current_bb,u.vs_inst_idx) <> frag_observer_cut B` by
    (qpat_assum `type_slot_size tv = 0 <=> _` mp_tac >>
     qpat_assum `type_slot_size tv <> 0` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> tautLib.TAUT_TAC) >>
  qpat_assum `!a Ga tna. (u,Gu,tnu) = _ ==> _`
    (qspecl_then [`u`,`Gu`,`tnu`] (DISJ_CASES_THEN2
      (fn th => qpat_assum `(u.vs_current_bb,u.vs_inst_idx) <> frag_observer_cut B`
        (fn nth => CONTR_TAC (MP nth th)))
      (CONJUNCTS_THEN2 assume_tac (qx_choose_then `cb` (qx_choose_then `i`
        (REPEAT_TCL CONJUNCTS_THEN assume_tac)))) o REWRITE_RULE [])) >>
  `(u.vs_current_bb,u.vs_inst_idx) IN frag_observer_region A B` by
    (qpat_assum `!n a Ga tna. n <= k /\ _ ==> _`
       (qspecl_then [`k`,`u`,`Gu`,`tnu`] mp_tac) >> simp[]) >>
  qpat_assum `frag_observer A B canon id = canon` (fn obs =>
    qpat_x_assum `lookup_block u.vs_current_bb (frag_observer A B canon id).fn_blocks = SOME cb`
      (assume_tac o REWRITE_RULE [obs])) >>
  qpat_assum `!a u' cb inst. frag_relabel_state _ _ _ _ /\ _ ==> _`
    (qspecl_then [`u`,`v0`,`cb`,`i`] mp_tac) >>
  (impl_tac >- asm_rewrite_tac[]) >>
  disch_then (qx_choose_then `ab` (CONJUNCTS_THEN assume_tac)) >>
  Cases_on `EL (SUC k) xs` >> rename1 `EL (SUC k) xs = (b,gh)` >>
  Cases_on `gh` >> rename1 `EL (SUC k) xs = (b,Gb,tnb)` >>
  `gas_origin_ptr_edge (ARB,lo,explicit,ctx,canon,PG) (u,Gu,tnu) [] (OK b,Gb,tnb)` by
    (qpat_assum `frag_observer A B canon id = canon` (fn obs =>
       qpat_assum `!n a Ga tna b Gb tnb. SUC n < LENGTH xs /\ _ ==> _`
         (qspecl_then [`k`,`u`,`Gu`,`tnu`,`b`,`Gb`,`tnb`] (mp_tac o REWRITE_RULE [obs]))) >>
     asm_rewrite_tac[]) >>
  `MEM i.inst_opcode
      [ASSIGN;ADD;MUL;EQ;LT;ISZERO;SHR;MLOAD;JMP;JNZ;SSTORE;TSTORE] /\
   (MEM i.inst_opcode [JMP;JNZ] ==> ~MEM (Label ell) i.inst_operands)` by
    (qpat_assum `i.inst_opcode = _` mp_tac >>
     POP_ASSUM_LIST (K all_tac) >> Cases_on `tr` >> simp[MEM]) >>
  `!lbl bb. lbl <> ell /\ lookup_block lbl canon.fn_blocks = SOME bb ==>
    phi_prefix_length bb.bb_instructions = 0` by
    (qpat_assum `A.cs_current_bb = ell` (fn lab =>
       qpat_assum `!lbl bb. lbl <> A.cs_current_bb /\ _ ==> _`
         (ACCEPT_TAC o REWRITE_RULE [lab]))) >>
  mp_tac (Q.INST [`L` |-> `ell`, `entry` |-> `sa.cs_current_bb`, `a` |-> `u`,
                   `v` |-> `v0`, `inst` |-> `i`, `Ga` |-> `Gu`, `tna` |-> `tnu`,
                   `D` |-> `ARB`] store_slots_relabel_checked_edge) >>
  (impl_tac >- asm_rewrite_tac[]) >>
  disch_then (qx_choose_then `w` (CONJUNCTS_THEN2 kall_tac assume_tac)) >>
  mp_tac bodyFullStoreSlotsStaticStoresTheory.store_slots_fragment_store_site_code >>
  (impl_tac >-
    (qpat_assum `frag_code A B = frag_code sa sb` (SUBST1_TAC o SYM) >>
     qpat_assum `i.inst_opcode = _` SUBST1_TAC >> Cases_on `tr` >> asm_rewrite_tac[])) >>
  disch_then (mp_tac o CONJUNCT2) >>
  disch_then (qx_choose_then `dst0` (qx_choose_then `valop`
    (qx_choose_then `ca` (qx_choose_then `cz` strip_assume_tac)))) >>
  `v0.vs_current_bb = ca.cs_current_bb /\ v0.vs_inst_idx = LENGTH ca.cs_current_insts` by
    suspend "store_cursor" >>
  simp[NoAsms, Abbr `t`] >>
  drule_all store_slots_checked_store_static >> disch_then ACCEPT_TAC
QED

Resume compile_store_slots_static_origin_ptr_path[store_cursor]:
  drule emitHelperPropsTheory.emitted_insts_emit_void >> strip_tac >>
  drule exprLoweringPropsTheory.emit_void_same_blocks >>
  rewrite_tac[exprLoweringPropsTheory.same_blocks_def] >> strip_tac >>
  drule_all fn_has_code_same_block >>
  disch_then (qx_choose_then `site` (CONJUNCTS_THEN2 assume_tac (qspec_then `0` mp_tac))) >>
  simp[] >> disch_tac >>
  `get_instruction site (LENGTH ca.cs_current_insts) = SOME i` by simp[] >>
  qpat_assum `lookup_block v0.vs_current_bb _ = SOME ab` mp_tac >>
  qpat_assum `lookup_block ca.cs_current_bb _ = SOME site` mp_tac >>
  qpat_assum `get_instruction ab v0.vs_inst_idx = SOME i` mp_tac >>
  qpat_assum `get_instruction site (LENGTH ca.cs_current_insts) = SOME i` mp_tac >>
  qpat_assum `fn_inst_ids_distinct func` mp_tac >>
  POP_ASSUM_LIST (K all_tac) >> rpt disch_tac >>
  `MEM ab func.fn_blocks /\ MEM site func.fn_blocks /\
   ab.bb_label = v0.vs_current_bb /\ site.bb_label = ca.cs_current_bb` by
    metis_tac[venomExecPropsTheory.lookup_block_MEM,venomExecPropsTheory.lookup_block_label] >>
  `v0.vs_inst_idx < LENGTH ab.bb_instructions /\
   LENGTH ca.cs_current_insts < LENGTH site.bb_instructions /\
   EL v0.vs_inst_idx ab.bb_instructions = i /\
   EL (LENGTH ca.cs_current_insts) site.bb_instructions = i` by
    gvs[get_instruction_def,AllCaseEqs()] >>
  `MEM i ab.bb_instructions /\ MEM i site.bb_instructions` by metis_tac[MEM_EL] >>
  `ab = site` by metis_tac[venomFnInstsProofsTheory.inst_in_unique_block] >>
  qpat_x_assum `ab = site` SUBST_ALL_TAC >>
  conj_tac >- metis_tac[] >>
  drule_all venomFnInstsProofsTheory.fn_inst_ids_block_distinct >> disch_tac >>
  qspecl_then [`MAP (\i. i.inst_id) site.bb_instructions`,
    `v0.vs_inst_idx`,`LENGTH ca.cs_current_insts`] mp_tac ALL_DISTINCT_EL_IMP >>
  simp[EL_MAP]
QED

Finalise compile_store_slots_static_origin_ptr_path

