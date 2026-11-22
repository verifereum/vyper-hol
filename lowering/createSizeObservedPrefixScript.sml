Theory createSizeObservedPrefix
Ancestors
  abiEncoderProps fragExec fragGasOrigin venomExecSemantics venomInst venomState relation
  list words createMarkedPath pair arithmetic vfmConstants exprLoweringProps rich_list
  context integer_word createCtorSegmentArrival createSizeEdgePC abiBufferAllocationCode
  emitHelperProps venomExecProofs createExprSizeExitDefs createSizePrefixReplay

Theorem raw_observed_prefix_cases[local]:
  create_expr_prefix a b explicit ctx fn s ms t ==>
  (t = s /\ ms = []) \/
  ?u left. create_prefix_step a b explicit ctx fn s left u /\
    RTC (create_marked_edge (create_prefix_step a b explicit ctx fn)) (u,left) (t,ms)
Proof
  simp[create_expr_prefix_marked] >>
  disch_then (mp_tac o ONCE_REWRITE_RULE [RTC_CASES1]) >>
  simp[EXISTS_PROD,create_marked_edge_def] >> metis_tac[]
QED

Theorem raw_observed_prefix_fetch[local]:
  create_expr_prefix a b explicit ctx fn s ms t /\
  a.cs_next_id <= b.cs_next_id /\
  ctor_segment_fetch fn t = SOME j /\ j.inst_opcode <> PHI /\ b.cs_next_id <= j.inst_id ==>
  ?i. ctor_segment_fetch fn s = SOME i /\ i.inst_opcode <> PHI /\ a.cs_next_id <= i.inst_id
Proof
  strip_tac >> drule raw_observed_prefix_cases >> strip_tac
  >- (qexists_tac `j` >> fs[] >> decide_tac) >>
  qpat_x_assum `create_prefix_step _ _ _ _ _ _ _ _`
    (strip_assume_tac o REWRITE_RULE[create_prefix_step_def]) >>
  qpat_x_assum `gas_origin_edge _ _ _ _ _ _ _` mp_tac >>
  simp[gas_origin_edge_def,exit_result_def] >> strip_tac >> gvs[] >>
  fs[ctor_segment_fetch_def,frag_ids_def] >> metis_tac[step_inst_ok_imp_not_phi]
QED

Theorem raw_observed_prefix_live:
  create_expr_prefix a b explicit ctx fn s ms t /\ ~s.vs_halted ==> ~t.vs_halted
Proof
  simp[create_expr_prefix_marked] >>
  `!x y. RTC (create_marked_edge (create_prefix_step a b explicit ctx fn)) x y ==>
    ~(FST x).vs_halted ==> ~(FST y).vs_halted` suffices_by
    (disch_then (qspecl_then [`(s,[])`,`(t,ms)`] mp_tac) >> simp[]) >>
  ho_match_mp_tac RTC_INDUCT >>
  simp[FORALL_PROD,create_marked_edge_def,create_prefix_step_def,PULL_EXISTS] >>
  rpt strip_tac >>
  qpat_x_assum `gas_origin_edge _ _ _ _ _ _ _`
    (strip_assume_tac o SIMP_RULE bool_ss [gas_origin_edge_def]) >>
  gvs[jump_to_def,exit_result_def] >>
  qpat_x_assum `OK _ = step_inst _ _ _ _` (fs o single o SYM) >>
  fs[exit_result_def]
QED

Theorem raw_observed_prefix_join:
  create_expr_prefix a b explicit ctx fn s left u /\
  create_expr_prefix b c explicit ctx fn u right t /\
  a.cs_next_id <= b.cs_next_id /\ b.cs_next_id <= c.cs_next_id /\
  t.vs_current_bb = c.cs_current_bb /\ t.vs_inst_idx = LENGTH c.cs_current_insts /\
  ctor_segment_fetch fn t = SOME i /\ c.cs_next_id <= i.inst_id ==>
  create_expr_prefix a c explicit ctx fn s (left ++ right) t
Proof
  simp[create_expr_prefix_marked] >> strip_tac >>
  `!x y. create_marked_edge (create_prefix_step a b explicit ctx fn) x y ==>
         create_marked_edge (create_prefix_step a c explicit ctx fn) x y` by
    (simp[FORALL_PROD,create_marked_edge_def,create_prefix_step_def,frag_ids_def,PULL_EXISTS] >>
     rpt gen_tac >> strip_tac >> TRY (goal_assum (drule_at Any)) >>
     TRY (first_assum ACCEPT_TAC) >> TRY (decide_tac) >>
     rpt strip_tac >> gvs[ctor_segment_fetch_def] >> decide_tac) >>
  `RTC (create_marked_edge (create_prefix_step a c explicit ctx fn)) (s,[]) (u,left)` by
    metis_tac[RTC_MONOTONE] >>
  `!x y. create_marked_edge (create_prefix_step b c explicit ctx fn) x y ==>
         create_marked_edge (create_prefix_step a c explicit ctx fn) x y` by
    (simp[FORALL_PROD,create_marked_edge_def,create_prefix_step_def,frag_ids_def,PULL_EXISTS] >>
     metis_tac[LESS_EQ_TRANS]) >>
  qpat_assum `RTC (create_marked_edge (create_prefix_step b c _ _ _)) _ _`
    (mp_tac o MATCH_MP create_marked_rtc_rebase) >>
  disch_then (qspec_then `left` mp_tac) >> simp[] >> strip_tac >>
  `RTC (create_marked_edge (create_prefix_step a c explicit ctx fn)) (u,left) (t,left ++ right)` by
    metis_tac[RTC_MONOTONE] >> metis_tac[RTC_TRANS]
QED

Theorem raw_observed_prefix_single[local]:
  fn_has_code a b fn /\ b.cs_current_bb = a.cs_current_bb /\
  b.cs_current_insts = a.cs_current_insts ++ [i] /\ ~is_terminator i.inst_opcode /\
  s.vs_current_bb = a.cs_current_bb /\ s.vs_inst_idx = LENGTH a.cs_current_insts /\
  t.vs_current_bb = b.cs_current_bb /\ t.vs_inst_idx = LENGTH b.cs_current_insts /\
  create_expr_prefix a b explicit ctx fn s ms t ==>
  gas_origin_edge F explicit ctx fn s ms (OK t)
Proof
  strip_tac >>
  `s <> t` by (strip_tac >> gvs[]) >>
  drule raw_observed_prefix_cases >> strip_tac >- fs[] >>
  qpat_x_assum `create_prefix_step a b _ _ _ s _ _`
    (strip_assume_tac o REWRITE_RULE[create_prefix_step_def]) >>
  drule_all fn_has_code_same_block >> strip_tac >> gvs[] >>
  `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\ get_instruction bb s.vs_inst_idx = SOME i` by simp[] >>
  drule_all create_ok_edge_pc >> strip_tac >> gvs[] >>
  qpat_x_assum `RTC _ _ _` (mp_tac o ONCE_REWRITE_RULE[RTC_CASES1]) >>
  simp[EXISTS_PROD,create_marked_edge_def,create_prefix_step_def] >> metis_tac[]
QED

(* Following any number of empty bands does not lose the next actual fetch. *)

Theorem raw_observed_index_fetch[local]:
  !n k.
    (!i. k <= i /\ i < k+n ==>
      (C i).cs_next_id <= (C (SUC i)).cs_next_id /\
      create_expr_prefix (C i) (C (SUC i)) explicit ctx fn (St i) (M i) (St (SUC i))) /\
    ctor_segment_fetch fn (St (k+n)) = SOME j /\ j.inst_opcode <> PHI /\
    (C (k+n)).cs_next_id <= j.inst_id ==>
  ?x. ctor_segment_fetch fn (St k) = SOME x /\ x.inst_opcode <> PHI /\
      (C k).cs_next_id <= x.inst_id
Proof
  Induct >- simp[] >> rpt gen_tac >> strip_tac >>
  `k + SUC n = SUC k + n` by decide_tac >>
  `?x. ctor_segment_fetch fn (St (SUC k)) = SOME x /\ x.inst_opcode <> PHI /\
     (C (SUC k)).cs_next_id <= x.inst_id` by
    (first_x_assum irule >>
     qpat_assum `k + SUC n = SUC k + n` (pure_rewrite_tac o single o SYM) >>
     asm_rewrite_tac[] >> rpt gen_tac >> strip_tac >>
     first_assum irule >> decide_tac) >>
  `k <= k /\ k < k+SUC n` by decide_tac >>
  qpat_x_assum `!i. k <= i /\ i < k+SUC n ==> _`
    (qspec_then `k` mp_tac) >> asm_rewrite_tac[] >> strip_tac >>
  drule_all raw_observed_prefix_fetch >> simp[]
QED

Theorem raw_observed_index_live[local]:
  !i. i <= n /\ ~ (St 0).vs_halted /\
    (!j. j < n ==> create_expr_prefix (C j) (C (SUC j)) explicit ctx fn
                    (St j) (M j) (St (SUC j))) ==>
    ~(St i).vs_halted
Proof
  Induct >> simp[] >> strip_tac >>
  `i <= n /\ i < n` by decide_tac >>
  metis_tac[raw_observed_prefix_live]
QED

Theorem raw_observed_pairs:
  !n f g.
    LENGTH (FLAT (GENLIST (\i. [f i; g i]) n)) = 2*n /\
    (!i. i < n ==>
       EL (2*i) (FLAT (GENLIST (\i. [f i; g i]) n)) = f i /\
       EL (SUC (2*i)) (FLAT (GENLIST (\i. [f i; g i]) n)) = g i)
Proof
  Induct >- simp[] >>
  rpt gen_tac >> first_x_assum (qspecl_then [`f o SUC`,`g o SUC`] mp_tac) >>
  simp[GENLIST_CONS,combinTheory.o_DEF,ADD_CLAUSES] >>
  strip_tac >> Cases >- simp[] >>
  `!j. 2 * SUC j = SUC (SUC (2*j))` by (simp[MULT_CLAUSES] >> decide_tac) >>
  rewrite_tac[LESS_MONO_EQ] >> strip_tac >>
  qpat_assum `!i. i < n ==> _` (drule_then strip_assume_tac) >>
  asm_simp_tac bool_ss [EL,HD,TL] >>
  qpat_assum `EL (SUC (2 * _)) _ = _` (mp_tac o REWRITE_RULE [EL]) >> simp[]
QED

Theorem raw_observed_prefix_emit:
  emit_op opc ops a = (out,b) /\ ~is_terminator opc /\ fn_has_code a b fn /\
  (s.vs_current_bb,s.vs_inst_idx) = (a.cs_current_bb,LENGTH a.cs_current_insts) /\
  (t.vs_current_bb,t.vs_inst_idx) = (b.cs_current_bb,LENGTH b.cs_current_insts) /\
  create_expr_prefix a b explicit ctx fn s ms t ==>
  gas_origin_edge F explicit ctx fn s ms (OK t)
Proof
  strip_tac >> drule exprLoweringPropsTheory.emit_op_extends >> strip_tac >>
  drule emitHelperPropsTheory.emitted_insts_emit_op >> strip_tac >>
  irule raw_observed_prefix_single >>
  qexistsl_tac [`a`,`b`,`mk_inst a.cs_next_id opc ops [STRING #"%" (toString a.cs_next_var)]`] >>
  gvs[mk_inst_def,exprLoweringPropsTheory.same_blocks_def]
QED

Theorem raw_observed_prefix_copy:
  compile_copy_memory_dynamic dst data len a = ((),b) /\ fn_has_code a b fn /\
  (s.vs_current_bb,s.vs_inst_idx) = (a.cs_current_bb,LENGTH a.cs_current_insts) /\
  (t.vs_current_bb,t.vs_inst_idx) = (b.cs_current_bb,LENGTH b.cs_current_insts) /\
  create_expr_prefix a b explicit ctx fn s ms t ==>
  gas_origin_edge F explicit ctx fn s ms (OK t)
Proof
  simp[contextTheory.compile_copy_memory_dynamic_def] >> strip_tac >>
  drule exprLoweringPropsTheory.emit_void_extends >> strip_tac >>
  drule emitHelperPropsTheory.emitted_insts_emit_void >> strip_tac >>
  irule raw_observed_prefix_single >>
  qexistsl_tac [`a`,`b`,`mk_inst a.cs_next_id MCOPY [dst;data;len] []`] >>
  gvs[mk_inst_def,is_terminator_def,exprLoweringPropsTheory.same_blocks_def]
QED

Theorem raw_observed_prefix_alloc:
  compile_alloc_buffer cap a = (buf,b) /\ fn_has_code a b fn /\
  (s.vs_current_bb,s.vs_inst_idx) = (a.cs_current_bb,LENGTH a.cs_current_insts) /\
  (t.vs_current_bb,t.vs_inst_idx) = (b.cs_current_bb,LENGTH b.cs_current_insts) /\
  create_expr_prefix a b explicit ctx fn s ms t ==>
  gas_origin_edge F explicit ctx fn s ms (OK t)
Proof
  strip_tac >> drule compile_alloc_buffer_code >> strip_tac >>
  irule raw_observed_prefix_single >>
  qexistsl_tac [`a`,`b`,
    `mk_inst a.cs_next_id ALLOCA [Lit (n2w cap)] [STRING #"%" (toString a.cs_next_var)]`] >>
  gvs[mk_inst_def,is_terminator_def]
QED

(* Convert the cut list once, and compute the first remaining fetch at every
   boundary. The latter justifies widening a two-band constructor row. *)

Theorem raw_observed_spine:
  C = (\i. EL i code) /\ Obs = (\i. EL i states) /\ M = (\i. EL i chunks0) /\
  LENGTH code = SUC n /\ LENGTH chunks0 = n /\
  LIST_REL (\c s. s.vs_current_bb = c.cs_current_bb /\
                  s.vs_inst_idx = LENGTH c.cs_current_insts) code states /\
  ~ (Obs 0).vs_halted /\ ctor_segment_fetch fn (Obs n) = SOME dispatch /\
  dispatch.inst_opcode <> PHI /\ (C n).cs_next_id <= dispatch.inst_id /\
  (!i. i < n ==> (C i).cs_next_id <= (C (SUC i)).cs_next_id /\
      create_expr_prefix (C i) (C (SUC i)) explicit ctx fn (Obs i) (M i) (Obs (SUC i))) ==>
  (!i. i <= n ==> ~ (Obs i).vs_halted /\
    ((Obs i).vs_current_bb,(Obs i).vs_inst_idx) =
      ((C i).cs_current_bb,LENGTH (C i).cs_current_insts) /\
    ?j. ctor_segment_fetch fn (Obs i) = SOME j /\ j.inst_opcode <> PHI /\
       (C i).cs_next_id <= j.inst_id) /\
  (!i. SUC i < n ==>
    create_expr_prefix (C i) (C (SUC (SUC i))) explicit ctx fn
      (Obs i) (M i ++ M (SUC i)) (Obs (SUC (SUC i)))) /\
  (!i. i < n ==> FLAT (DROP i chunks0) = M i ++ FLAT (DROP (SUC i) chunks0))
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Q.SUBGOAL_THEN `!i. i <= n ==> ~ (Obs i).vs_halted /\
    ((Obs i).vs_current_bb,(Obs i).vs_inst_idx) =
      ((C i).cs_current_bb,LENGTH (C i).cs_current_insts) /\
    ?j. ctor_segment_fetch fn (Obs i) = SOME j /\ j.inst_opcode <> PHI /\
       (C i).cs_next_id <= j.inst_id` assume_tac
  >- (rpt gen_tac >> disch_tac >> conj_tac
      >- (irule (Q.INST [`St` |-> `Obs`, `C` |-> `C`, `M` |-> `M`,
                         `explicit` |-> `explicit`, `ctx` |-> `ctx`, `fn` |-> `fn`, `n` |-> `n`]
                raw_observed_index_live) >>
          qpat_assum `!i. i < n ==> _` mp_tac >> metis_tac[]) >>
      conj_tac >- (fs[LIST_REL_EL_EQN] >> first_assum irule >> decide_tac) >>
      `i + (n-i) = n` by decide_tac >>
      match_mp_tac (Q.SPECL [`n-i`,`i`] (Q.INST [`St` |-> `Obs`, `C` |-> `C`, `M` |-> `M`,
           `explicit` |-> `explicit`, `ctx` |-> `ctx`, `fn` |-> `fn`, `j` |-> `dispatch`]
           raw_observed_index_fetch)) >>
      qpat_assum `i + (n-i) = n` (pure_rewrite_tac o single) >>
      conj_tac >- (rpt gen_tac >> strip_tac >> first_assum irule >> decide_tac) >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  asm_rewrite_tac[] >> conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `i < n /\ SUC (SUC i) <= n` by decide_tac >>
      qpat_assum `!i. i <= n ==> _` (qspec_then `SUC (SUC i)` (drule_then strip_assume_tac)) >>
      qpat_assum `!i. i < n ==> _`
        (fn th => map_every (fn q => qspec_then q (drule_then strip_assume_tac) th) [`i`,`SUC i`]) >>
      irule raw_observed_prefix_join >> gvs[] >>
      rpt (goal_assum (drule_at Any)) >>
      qexistsl_tac [`EL (SUC i) code`,`EL (SUC i) states`] >> simp[] >>
      metis_tac[LESS_MONO_EQ, LESS_OR_EQ]) >>
  rpt strip_tac >> qspecl_then [`i`,`chunks0`] mp_tac rich_listTheory.DROP_CONS_EL >> simp[]
QED
