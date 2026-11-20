(* Quantitative transport through the optimizer with fixed own-code bytes. *)
Theory asmFinalizerPrefixOwn
Ancestors
  asmSpliceOwn asmSplice asmSem asmSymSem asmSymPc asmOptimizer asmWf
  asmFinalizerPrefixCompose asmFinalizerPrefixRename asmOwnMergeRename
  asmFinalizerPrefixIszero asmOptMergeIszero asmFinalizerPrefixJumpDelete
  asmFinalizerPrefixPruneJumps asmOptPruneJumps
  asmFinalizerPrefixInefficient asmOptInefficientJumps
  asmFinalizerPrefixUnreachable asmOptPruneUnreachable
  asmFinalizerPrefixUnused asmOptPruneUnused asmFinalizerPrefixPeephole
  asmFinalizerPrefixPeepFixed asmFinalizerPrefixPeepSwap asmFinalizerPrefixPeepComm
  symbolResolve arithmetic list rich_list finite_map pair

val transport_own = ``\p q.
  ?K. 0 < K /\ !env own s n a.
    s.as_pc = 0 /\ sym_steps_own p env own n (sym_init s) = SymOK a ==>
    (?m b. sym_steps_own q env own m (sym_init s) = SymOK b /\ n <= K * (m+1)) /\
    (!op. op IN {"GAS"; "CALL"; "STATICCALL"; "DELEGATECALL"; "CREATE";
                 "CREATE2"} /\
       a.sym_base.as_pc < LENGTH p /\ EL a.sym_base.as_pc p = AsmOp op ==>
     ?m b. sym_steps_own q env own m (sym_init s) = SymOK b /\
       b.sym_base.as_pc < LENGTH q /\ EL b.sym_base.as_pc q = AsmOp op /\
       (b.sym_base with as_pc := 0) = (a.sym_base with as_pc := 0) /\
       MAP sval_val b.sym_stack = MAP sval_val a.sym_stack /\
       FDOM b.sym_mem_labels = FDOM a.sym_mem_labels)``;

fun own_steps_specialize th =
  BETA_RULE (SIMP_RULE bool_ss [pairTheory.FORALL_PROD, pairTheory.UNCURRY,
    pairTheory.FST, pairTheory.SND]
    (BETA_RULE (Q.ISPEC `\p. UNCURRY (sym_steps_own p)` th)));

val own_refl = own_steps_specialize prefix_transport_refl_for;
val own_trans = own_steps_specialize prefix_transport_trans_for;

(* Each chunk includes any unchanged instructions executed before leaving the splice. *)
fun chunk_steps chunk suffix (asl, goal) =
  let
    val steps = rand (rator (lhs goal))
    val window = INST [``n:num`` |-> steps]
      (Q.INST [`chunk` |-> chunk, `post` |-> suffix, `ss` |-> `u`]
        sym_steps_own_agree_on_chunk)
  in
    (mp_tac window >> pure_rewrite_tac [GSYM APPEND_ASSOC, APPEND] >>
     simp[]) (asl, goal)
  end;


Theorem iszero_pair_site_own[local]:
  !pre x rest.
    asm_returns_zero_or_one x /\
    asm_static_wf (pre ++ [x; AsmOp "ISZERO"; AsmOp "ISZERO"] ++ rest) ==>
    ^transport_own (pre ++ [x; AsmOp "ISZERO"; AsmOp "ISZERO"] ++ rest)
               (pre ++ [x] ++ rest)
Proof
  BETA_TAC >> rpt gen_tac >> strip_tac >>
  `?name. x = AsmOp name` by gvs[asm_returns_zero_or_one_def] >>
  qpat_x_assum `x = AsmOp name` SUBST_ALL_TAC >>
  `name <> "CODESIZE" /\ name <> "CODECOPY" /\
   name <> "JUMP" /\ name <> "JUMPI"` by gvs[asm_returns_zero_or_one_def] >>
  irule bounded_splice_prefix_transport_own >>
  simp[asm_splice_ok_def, is_data_inst_def, asm_label_refs_def, asm_inst_size_def] >>
  qexists_tac `3` >> rpt gen_tac >> strip_tac >>
  `!n. n <= 3 ==> sym_steps_own
      (pre ++ [AsmOp name; AsmOp "ISZERO"; AsmOp "ISZERO"] ++ rest) env own n u =
      sym_steps (pre ++ [AsmOp name; AsmOp "ISZERO"; AsmOp "ISZERO"] ++ rest) env n u`
    by (rpt strip_tac >> chunk_steps `[AsmOp name; AsmOp "ISZERO"; AsmOp "ISZERO"]` `rest`) >>
  `sym_steps_own (pre ++ [AsmOp name] ++ rest) env own 1 u =
    sym_steps (pre ++ [AsmOp name] ++ rest) env 1 u`
    by (chunk_steps `[AsmOp name]` `rest`) >>
  qexists_tac `3` >> simp[] >>
  mp_tac (Q.SPECL [`pre`,`AsmOp name`,`rest`,`env`,`u`]
    iszero_pair_prefix_window) >> (impl_tac >- simp[]) >> strip_tac >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `i <= 3` by decide_tac >>
      `sym_steps (pre ++ [AsmOp name; AsmOp "ISZERO"; AsmOp "ISZERO"] ++ rest) env i u
          = SymOK a` by metis_tac[] >>
      qpat_x_assum `!i a. _ ==> !op. _` (qspecl_then [`i`,`a`] mp_tac) >> simp[]) >>
  rpt gen_tac >> strip_tac >> qexists_tac `1` >>
  qpat_assum `!a. sym_steps _ _ 3 _ = _ ==> _`
    (qspec_then `a` (drule_then (map_every assume_tac o CONJUNCTS))) >>
  qpat_assum `sym_steps_own _ _ _ 1 _ = sym_steps _ _ _ _`
    (fn th => PURE_REWRITE_TAC [th]) >>
  rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE
    (DISJ2_TAC >> first_assum ACCEPT_TAC) ORELSE decide_tac)
QED

Theorem iszero_jumpi_site_own[local]:
  !pre l rest.
    asm_static_wf (pre ++ [AsmOp "ISZERO"; AsmOp "ISZERO"] ++
                         AsmPushLabel l :: AsmOp "JUMPI" :: rest) ==>
    ^transport_own (pre ++ [AsmOp "ISZERO"; AsmOp "ISZERO"] ++
                      AsmPushLabel l :: AsmOp "JUMPI" :: rest)
               (pre ++ [] ++ AsmPushLabel l :: AsmOp "JUMPI" :: rest)
Proof
  BETA_TAC >> rpt gen_tac >> strip_tac >>
  irule bounded_splice_prefix_transport_own >>
  simp[asm_splice_ok_def, is_data_inst_def, asm_label_refs_def, asm_inst_size_def] >>
  qexists_tac `4` >> rpt gen_tac >> strip_tac >>
  `!n. n <= 4 ==> sym_steps_own (pre ++ [AsmOp "ISZERO"; AsmOp "ISZERO"] ++
      AsmPushLabel l :: AsmOp "JUMPI" :: rest) env own n u =
      sym_steps (pre ++ [AsmOp "ISZERO"; AsmOp "ISZERO"] ++
      AsmPushLabel l :: AsmOp "JUMPI" :: rest) env n u` by
    (rpt strip_tac >> chunk_steps
      `[AsmOp "ISZERO"; AsmOp "ISZERO"; AsmPushLabel l; AsmOp "JUMPI"]` `rest`) >>
  `sym_steps_own (pre ++ AsmPushLabel l :: AsmOp "JUMPI" :: rest) env own 2 u =
    sym_steps (pre ++ AsmPushLabel l :: AsmOp "JUMPI" :: rest) env 2 u` by
    (chunk_steps `[AsmPushLabel l; AsmOp "JUMPI"]` `rest`) >>
  qexists_tac `4` >> simp[] >>
  mp_tac (Q.SPECL [`pre`,`l`,`rest`,`env`,`u`] iszero_jumpi_prefix_window) >>
  (impl_tac >- simp[]) >> strip_tac >> conj_tac
  >- (rpt strip_tac >> `i <= 4` by decide_tac >>
      `sym_steps (pre ++ [AsmOp "ISZERO"; AsmOp "ISZERO"] ++
           AsmPushLabel l :: AsmOp "JUMPI" :: rest) env i u = SymOK a` by metis_tac[] >>
      qpat_x_assum `!i a. _ ==> !op. _` (qspecl_then [`i`,`a`] mp_tac) >>
      impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >>
      disch_then (qspec_then `op` mp_tac) >>
      simp[] >> POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
  rpt strip_tac >> qexists_tac `2` >>
  qpat_assum `!a. sym_steps _ _ 4 _ = _ ==> _`
    (qspec_then `a` (drule_then (map_every assume_tac o CONJUNCTS))) >>
  qpat_assum `sym_steps_own _ _ _ 2 _ = sym_steps _ _ _ _`
    (fn th => PURE_REWRITE_TAC [th]) >>
  rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE decide_tac)
QED

Theorem merge_iszero_prefix_transport_own[local]:
  !p. asm_static_wf p ==> ^transport_own p (FST (merge_iszero p))
Proof
  BETA_TAC >>
  mp_tac (BETA_RULE (Q.SPEC `^transport_own` merge_iszero_prefix_transport_for)) >>
  impl_tac >- (pure_rewrite_tac [GSYM APPEND_ASSOC, APPEND] >>
    rpt conj_tac >> MAP_FIRST MATCH_ACCEPT_TAC
      (map (PURE_REWRITE_RULE [GSYM APPEND_ASSOC, APPEND])
        [own_refl, own_trans, BETA_RULE iszero_pair_site_own,
         BETA_RULE iszero_jumpi_site_own])) >>
  simp[]
QED

Theorem jump_to_next_prefix_transport_own[local]:
  !pre x rest.
    asm_static_wf (pre ++ [AsmPushLabel x; AsmOp "JUMP"] ++ AsmLabel x :: rest) ==>
    ^transport_own (pre ++ [AsmPushLabel x; AsmOp "JUMP"] ++ AsmLabel x :: rest)
               (pre ++ [] ++ AsmLabel x :: rest)
Proof
  BETA_TAC >> rpt gen_tac >> strip_tac >>
  irule bounded_splice_prefix_transport_own >>
  simp[asm_splice_ok_def, is_data_inst_def, asm_label_refs_def, asm_inst_size_def] >>
  qexists_tac `2` >> rpt gen_tac >> strip_tac >>
  `!n. n <= 2 ==> sym_steps_own
      (pre ++ [AsmPushLabel x; AsmOp "JUMP"] ++ AsmLabel x :: rest) env own n u =
      sym_steps (pre ++ [AsmPushLabel x; AsmOp "JUMP"] ++ AsmLabel x :: rest) env n u`
    by (rpt strip_tac >> chunk_steps `[AsmPushLabel x; AsmOp "JUMP"]` `AsmLabel x :: rest`) >>
  qexists_tac `2` >> simp[] >>
  drule_all (SIMP_RULE bool_ss [LET_THM] jump_delete_prefix_chunk) >> strip_tac >> conj_tac
  >- (rpt gen_tac >> strip_tac >> `i <= 2` by decide_tac >>
      `sym_steps (pre ++ [AsmPushLabel x; AsmOp "JUMP"] ++ AsmLabel x :: rest) env i u
        = SymOK a` by metis_tac[] >>
      qpat_x_assum `!env. sym_steps _ env 2 _ = _ /\ _`
        (qspec_then `env` strip_assume_tac) >>
      qpat_x_assum `!i a. _ ==> _ /\ !op. _` (qspecl_then [`i`,`a`] mp_tac) >>
      impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
      strip_tac >> rpt gen_tac >> strip_tac >>
      first_x_assum (qspec_then `op` mp_tac) >>
      simp[] >> POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
  rpt gen_tac >> strip_tac >> gvs[] >> qexists_tac `0` >>
  simp[sym_steps_own_def, splice_pc_def, sym_with_pc_def,
       sym_state_component_equality, asm_state_component_equality]
QED

Theorem prune_jumps_prefix_transport_own[local]:
  !p. asm_static_wf p ==> ^transport_own p (FST (prune_inefficient_jumps p))
Proof
  BETA_TAC >>
  mp_tac (BETA_RULE (Q.SPEC `^transport_own` prune_jumps_prefix_walk)) >>
  impl_tac >- (pure_rewrite_tac [GSYM APPEND_ASSOC, APPEND] >>
    rpt conj_tac >> MAP_FIRST MATCH_ACCEPT_TAC
      (map (PURE_REWRITE_RULE [GSYM APPEND_ASSOC, APPEND])
        [own_refl, own_trans, BETA_RULE jump_to_next_prefix_transport_own])) >>
  disch_then (fn th => gen_tac >> qspecl_then [`p`,`[]`] mp_tac th) >>
  simp[]
QED

Theorem terminal_site_prefix_own[local]:
  !pre t x post.
    asm_terminal_op t /\ ~asm_reachable_marker x /\
    asm_static_wf (pre ++ [t;x] ++ post) ==>
    ^transport_own (pre ++ [t;x] ++ post) (pre ++ [t] ++ post)
Proof
  BETA_TAC >> rpt gen_tac >> strip_tac >>
  MATCH_MP_TAC (Q.SPECL [`pre`,`[t;x]`,`[t]`,`post`,`1`]
    bounded_splice_prefix_transport_own) >>
  conj_tac >- metis_tac[terminal_prefix_splice_ok] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (gvs[asm_terminal_op_def, asm_reachable_marker_def] >>
              rpt strip_tac >> gvs[asm_reachable_marker_def]) >>
  rpt gen_tac >> strip_tac >>
  `t <> AsmOp "CODESIZE" /\ t <> AsmOp "CODECOPY"` by gvs[asm_terminal_op_def] >>
  `sym_steps_own (pre ++ [t;x] ++ post) env own 1 u =
    sym_steps (pre ++ [t;x] ++ post) env 1 u`
    by (chunk_steps `[t]` `x::post`) >>
  `sym_steps_own (pre ++ [t] ++ post) env own 1 u =
    sym_steps (pre ++ [t] ++ post) env 1 u`
    by (chunk_steps `[t]` `post`) >>
  qexists_tac `1` >> simp[sym_steps_own_def] >>
  drule_all terminal_prefix_window >>
  disch_then (qspecl_then [`post`, `env`] strip_assume_tac) >>
  rpt strip_tac >> qexists_tac `1` >> simp[] >> metis_tac[sym_steps_def]
QED

Theorem prune_unreachable_prefix_transport_own[local]:
  !p. asm_static_wf p ==> ^transport_own p (FST (prune_unreachable_code p))
Proof
  BETA_TAC >>
  mp_tac (BETA_RULE (Q.SPEC `^transport_own` prune_unreachable_prefix_walk)) >>
  impl_tac >- (rpt conj_tac >> MAP_FIRST MATCH_ACCEPT_TAC
    [own_refl, own_trans, BETA_RULE terminal_site_prefix_own]) >>
  disch_then (fn th => gen_tac >> qspecl_then [`p`,`F`,`[]`] mp_tac th) >>
  simp[prune_unreachable_code_def]
QED

Theorem unused_label_prefix_site_own[local]:
  !pre l post.
    asm_static_wf (pre ++ [AsmLabel l] ++ post) /\
    ~MEM l (asm_label_refs (pre ++ [AsmLabel l] ++ post)) ==>
    ^transport_own (pre ++ [AsmLabel l] ++ post) (pre ++ [] ++ post)
Proof
  BETA_TAC >> rpt gen_tac >> strip_tac >>
  MATCH_MP_TAC (Q.SPECL [`pre`,`[AsmLabel l]`,`[]`,`post`,`1`]
    bounded_splice_prefix_transport_own) >>
  simp[asm_splice_ok_def, is_data_inst_def, asm_label_refs_def] >>
  conj_tac >- gvs[asm_label_refs_def] >>
  rpt gen_tac >> strip_tac >>
  `sym_steps_own (pre ++ [AsmLabel l] ++ post) env own 1 u =
    sym_steps (pre ++ [AsmLabel l] ++ post) env 1 u`
    by (chunk_steps `[AsmLabel l]` `post`) >>
  qexists_tac `1` >> simp[] >>
  `LENGTH pre < LENGTH (pre ++ [AsmLabel l] ++ post) /\
   EL (LENGTH pre) (pre ++ [AsmLabel l] ++ post) = AsmLabel l`
    by simp[EL_APPEND_EQN] >>
  conj_tac >- (rpt strip_tac >> gvs[sym_steps_own_def]) >>
  rpt gen_tac >>
  simp[sym_steps_pos, sym_steps_def, sym_step_def, sym_lift_def, asm_step_def,
       asm_next_def, sym_terminal_def] >>
  strip_tac >> qexists_tac `0` >>
  gvs[sym_steps_own_def, splice_pc_def, sym_with_pc_def,
      sym_state_component_equality, asm_state_component_equality]
QED

Theorem prune_unused_prefix_transport_own[local]:
  !p. asm_static_wf p ==> ^transport_own p (FST (prune_unused_jumpdests p))
Proof
  BETA_TAC >>
  mp_tac (BETA_RULE (Q.SPEC `^transport_own` prune_unused_prefix_walk)) >>
  impl_tac >- (pure_rewrite_tac [GSYM APPEND_ASSOC, APPEND] >>
    rpt conj_tac >> MAP_FIRST MATCH_ACCEPT_TAC
      (map (PURE_REWRITE_RULE [GSYM APPEND_ASSOC, APPEND])
        [own_refl, own_trans, BETA_RULE unused_label_prefix_site_own])) >>
  disch_then (fn th => gen_tac >> qspecl_then [`p`,`[]`,`asm_label_refs p`] mp_tac th) >>
  simp[prune_unused_jumpdests_def]
QED

Theorem inefficient_jump_site_own[local]:
  !pre x y rest.
    asm_static_wf (pre ++ [AsmPushLabel x; AsmOp "JUMPI"; AsmPushLabel y; AsmOp "JUMP"] ++ AsmLabel
      x :: rest) ==>
    ^transport_own
      (pre ++ [AsmPushLabel x; AsmOp "JUMPI"; AsmPushLabel y; AsmOp "JUMP"] ++ AsmLabel x :: rest)
      (pre ++ [AsmOp "ISZERO"; AsmPushLabel y; AsmOp "JUMPI"] ++ AsmLabel x :: rest)
Proof
  BETA_TAC >> rpt gen_tac >> strip_tac >>
  MATCH_MP_TAC (Q.SPECL [`pre`,`[AsmPushLabel x; AsmOp "JUMPI"; AsmPushLabel y; AsmOp "JUMP"]`,
    `[AsmOp "ISZERO"; AsmPushLabel y; AsmOp "JUMPI"]`,`AsmLabel x :: rest`,`4`]
    bounded_splice_prefix_transport_own) >>
  conj_tac
  >- (simp[asm_splice_ok_def, is_data_inst_def, asm_label_refs_def, asm_inst_size_def] >>
      rw[] >> EVAL_TAC) >>
  simp[] >> rpt gen_tac >> strip_tac >>
  qabbrev_tac `p = pre ++ [AsmPushLabel x; AsmOp "JUMPI"; AsmPushLabel y; AsmOp "JUMP"] ++
    AsmLabel x :: rest` >>
  qabbrev_tac `q = pre ++ [AsmOp "ISZERO"; AsmPushLabel y; AsmOp "JUMPI"] ++ AsmLabel x :: rest` >>
  mp_tac (Q.SPECL [`pre`,`x`,`y`,`rest`,`env`,`u`]
    inefficient_jump_window_with_bounds) >>
  (impl_tac >- fs[Abbr `p`]) >> strip_tac >>
  `!n. n <= d ==> sym_steps_own p env own n u = sym_steps p env n u` by
    (rpt strip_tac >> irule sym_steps_own_eq_without_code_reads >>
     rpt strip_tac >>
     `i < d` by decide_tac >>
     qpat_x_assum `!i a. i < d /\ _ ==> _`
       (qspecl_then [`i`,`t`] mp_tac) >>
     (impl_tac >- fs[Abbr `p`]) >> strip_tac >>
     `i = 0 \/ i = 1 \/ i = 2 \/ i = 3` by decide_tac >>
     gvs[Abbr `p`, EL_APPEND_EQN]) >>
  `!n. n <= 3 ==> sym_steps_own q env own n u = sym_steps q env n u` by
    (rpt strip_tac >> simp[Abbr `q`] >>
     chunk_steps `[AsmOp "ISZERO"; AsmPushLabel y; AsmOp "JUMPI"]` `AsmLabel x :: rest`) >>
  qexists_tac `d` >> simp[] >> conj_tac
  >- (rpt strip_tac >>
      `i <= d` by decide_tac >>
      `sym_steps p env i u = SymOK a` by metis_tac[] >>
      qpat_assum `!i a. i < d /\ _ ==> _` (qspecl_then [`i`,`a`] mp_tac) >>
      (impl_tac >- fs[Abbr `p`]) >>
      strip_tac >> first_x_assum (qspec_then `op` mp_tac) >> fs[Abbr `p`]) >>
  rpt gen_tac >> strip_tac >>
  `sym_steps p env d u = SymOK a` by metis_tac[LESS_EQ_REFL] >>
  qpat_assum `!a. _ ==> ?e. _` (qspec_then `a` mp_tac) >>
  (impl_tac >- fs[Abbr `p`]) >>
  strip_tac >> qexists_tac `e` >>
  qpat_assum `!n. n <= 3 ==> _` (qspec_then `e` mp_tac) >> fs[Abbr `q`]
QED

Theorem inefficient_jumps_prefix_transport_own[local]:
  !p. asm_static_wf p ==> ^transport_own p (FST (optimize_inefficient_jumps p))
Proof
  BETA_TAC >>
  mp_tac (BETA_RULE (Q.SPEC `^transport_own` inefficient_jumps_prefix_walk)) >>
  impl_tac >- (rpt conj_tac >> MAP_FIRST MATCH_ACCEPT_TAC
    [own_refl, own_trans, BETA_RULE inefficient_jump_site_own]) >>
  simp[]
QED


Theorem merge_jumpdests_prefix_transport_own[local]:
  !p. asm_static_wf p ==> ^transport_own p (FST (merge_jumpdests p))
Proof
  BETA_TAC >>
  mp_tac (BETA_RULE (Q.SPEC `^transport_own` merge_jumpdests_prefix_transport_for)) >>
  impl_tac >- (rpt conj_tac >> MAP_FIRST MATCH_ACCEPT_TAC
    [own_refl, own_trans, rename_site_prefix_transport_own]) >>
  simp[]
QED

val peep_checkpoint = ``\pre pat repl post (i:num) a.
  !op. op IN {"GAS"; "CALL"; "STATICCALL"; "DELEGATECALL"; "CREATE"; "CREATE2"} /\
    a.sym_base.as_pc < LENGTH (pre ++ pat ++ post) /\
    EL a.sym_base.as_pc (pre ++ pat ++ post) = AsmOp op ==>
    i = 0 /\ repl <> [] /\ HD repl = HD pat``;
val peep_shift = ``\(pre:asm_inst list) (pat:asm_inst list) (repl:asm_inst list) a.
  sym_with_pc (splice_pc (LENGTH pre) (LENGTH pat) (LENGTH repl) a.sym_base.as_pc) a``;
val peep_complete = ``\(pre:asm_inst list) (pat:asm_inst list) a (e:num).
  (a.sym_base.as_pc <= LENGTH pre \/ LENGTH pre + LENGTH pat <= a.sym_base.as_pc) /\
  (e = 0 ==> LENGTH pre + LENGTH pat <= a.sym_base.as_pc)``;

Theorem peephole_site_prefix_transport_own[local]:
  !pre pat repl post.
  asm_splice_ok pat repl /\ (!l. ~MEM (AsmLabel l) pat) /\
  EVERY (\a. a <> AsmOp "CODESIZE" /\ a <> AsmOp "CODECOPY" /\
              a <> AsmOp "JUMP" /\ a <> AsmOp "JUMPI") (pat ++ repl) /\
  (!env u. u.sym_base.as_pc = LENGTH pre /\ u.sym_base.as_stack = [] /\
    sym_state_labels_in (asm_label_refs (pre ++ pat ++ post)) u ==>
    ?d. 0 < d /\ d <= LENGTH pat /\
      (!i a. i < d /\ sym_steps (pre ++ pat ++ post) env i u = SymOK a ==>
        ^peep_checkpoint pre pat repl post i a) /\
      (!a. sym_steps (pre ++ pat ++ post) env d u = SymOK a ==>
        ?e. e <= LENGTH repl /\ sym_steps (pre ++ repl ++ post) env e u =
          SymOK (^peep_shift pre pat repl a) /\ ^peep_complete pre pat a e)) ==>
  asm_static_wf (pre ++ pat ++ post) ==>
    asm_static_wf (pre ++ repl ++ post) /\
    ^transport_own (pre ++ pat ++ post) (pre ++ repl ++ post)
Proof
  BETA_TAC >> rpt gen_tac >> strip_tac >> strip_tac >> conj_tac
  >- (irule (cj 1 asm_splice_static_wf) >> qexists_tac `pat` >> simp[]) >>
  MATCH_MP_TAC (Q.SPECL [`pre`,`pat`,`repl`,`post`,`LENGTH (pat:asm_inst list)`]
    bounded_splice_prefix_transport_own) >> simp[] >>
  rpt gen_tac >> strip_tac >>
  mp_tac (BETA_RULE (Q.INST
    [`p` |-> `pre ++ pat ++ post`, `q` |-> `pre ++ repl ++ post`,
     `s` |-> `u`, `D` |-> `LENGTH (pat:asm_inst list)`, `E` |-> `LENGTH (repl:asm_inst list)`,
     `checkpoint` |-> `^peep_checkpoint pre pat repl post`,
     `shift` |-> `^peep_shift pre pat repl`,
     `complete` |-> `^peep_complete pre pat`] bounded_window_transfer_own)) >>
  impl_tac
  >- (conj_tac >- (rpt strip_tac >> chunk_steps `pat` `post` >>
          fs[EVERY_MEM] >> metis_tac[MEM_TAKE]) >>
      conj_tac >- (rpt strip_tac >> chunk_steps `repl` `post` >>
          fs[EVERY_MEM] >> metis_tac[MEM_TAKE]) >>
      first_x_assum (qspecl_then [`env`,`u`] mp_tac) >> simp[]) >>
  simp[]
QED

(* Instantiate site validity and the aligned step window for the chosen rewrite. *)
fun prove_peephole_site pat repl args window =
  mp_tac (BETA_RULE (Q.SPECL [`pre`, pat, repl, `rest`]
    peephole_site_prefix_transport_own)) >>
  impl_tac
  >- (conj_tac >- simp[asm_splice_ok_def, is_data_inst_def,
                       asm_label_refs_def, asm_inst_size_def, DISJ_IMP_THM, FORALL_AND_THM] >>
      conj_tac >- simp[] >>
      conj_tac >- simp[] >>
      mp_tac (BETA_RULE (Q.SPECL (`pre` :: `rest` :: args) window)) >> simp[]) >>
  pure_rewrite_tac [GSYM APPEND_ASSOC, APPEND] >>
  simp[];

Theorem peephole_prefix_transport_own[local]:
  !p q c. asm_static_wf p /\ stack_peephole_opts p = SOME(q,c) ==>
    ^transport_own p q
Proof
  qabbrev_tac `tr = ^transport_own` >>
  `!p. tr p p` by (unabbrev_all_tac >> BETA_TAC >> MATCH_ACCEPT_TAC own_refl) >>
  `!p q r. tr p q /\ tr q r ==> tr p r`
    by (unabbrev_all_tac >> BETA_TAC >> MATCH_ACCEPT_TAC own_trans) >>
  `IS_SOME (symbolResolve$evm_opcode_byte "DUP2")` by EVAL_TAC >>
  qspec_then `\p q. asm_static_wf p ==> asm_static_wf q /\ tr p q`
    mp_tac peephole_walk_relation >>
  (impl_tac >- (BETA_TAC >> conj_tac >- metis_tac[] >>
    conj_tac >- metis_tac[] >>
    conj_tac >- suspend "dup_swap2_swap1" >>
    conj_tac >- suspend "dup_swap_pop" >>
    conj_tac >- suspend "swap_pop_pop" >>
    conj_tac >- suspend "swap_pair" >>
    conj_tac >- suspend "swap_comm" >>
    suspend "dup_swap")) >>
  strip_tac >> rpt gen_tac >> strip_tac >>
  first_x_assum (qspecl_then [`p`, `[]`, `q`, `c`] mp_tac) >>
  simp[Abbr `tr`]
QED

Resume peephole_prefix_transport_own[dup_swap2_swap1]:
  rpt gen_tac >> simp[Abbr `tr`] >>
  prove_peephole_site `[AsmOp "DUP1"; AsmOp "SWAP2"; AsmOp "SWAP1"]`
    `[AsmOp "SWAP1"; AsmOp "DUP2"]` [] dup1_swap2_swap1_bounded_window_target_bound
QED

Resume peephole_prefix_transport_own[dup_swap_pop]:
  rpt gen_tac >> simp[Abbr `tr`] >>
  prove_peephole_site `[AsmOp "DUP1"; AsmOp "SWAP1"; AsmOp "POP"]`
    `[]` [] dup1_swap1_pop_bounded_window_target_bound
QED

Resume peephole_prefix_transport_own[swap_pop_pop]:
  rpt gen_tac >> simp[Abbr `tr`] >>
  prove_peephole_site `[AsmOp "SWAP1"; AsmOp "POP"; AsmOp "POP"]`
    `[AsmOp "POP"; AsmOp "POP"]` [] swap1_pop_pop_bounded_window_target_bound
QED

Resume peephole_prefix_transport_own[swap_pair]:
  rpt gen_tac >> strip_tac >> simp[Abbr `tr`] >>
  `name <> "CODECOPY" /\ name <> "CODESIZE" /\ name <> "JUMP" /\ name <> "JUMPI"`
    by (rpt conj_tac >> strip_tac >> gvs[]) >>
  prove_peephole_site `[AsmOp name; AsmOp name]`
    `[]` [`name`] swap_pair_bounded_window_target_bound
QED

Resume peephole_prefix_transport_own[swap_comm]:
  rpt gen_tac >> strip_tac >> simp[Abbr `tr`] >>
  qpat_x_assum `asm_commutative_op y` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >> strip_tac >>
  `?name. y = AsmOp name` by (Cases_on `y` >> fs[asm_commutative_op_def]) >>
  qpat_x_assum `y = AsmOp name` SUBST_ALL_TAC >>
  `name <> "CODECOPY" /\ name <> "CODESIZE" /\ name <> "JUMP" /\ name <> "JUMPI"`
    by (rpt conj_tac >> strip_tac >> gvs[] >>
        qpat_x_assum `asm_commutative_op _` mp_tac >> EVAL_TAC) >>
  prove_peephole_site `[AsmOp "SWAP1"; AsmOp name]`
    `[AsmOp name]` [`AsmOp name`] swap1_commutative_bounded_window_target_bound
QED

Resume peephole_prefix_transport_own[dup_swap]:
  rpt gen_tac >> simp[Abbr `tr`] >>
  prove_peephole_site `[AsmOp "DUP1"; AsmOp "SWAP1"]`
    `[AsmOp "DUP1"]` [] dup1_swap1_bounded_window_target_bound
QED

Finalise peephole_prefix_transport_own

Theorem accepted_finalizers_prefix_transport_own:
  !fin rp p q. fin IN accepted_finalizers /\ fin rp p = SOME q /\
    asm_static_wf p ==> ^transport_own p q
Proof
  BETA_TAC >>
  mp_tac (own_steps_specialize accepted_finalizers_prefix_transport_conditional_for) >>
  (impl_tac >- (rpt conj_tac >> MAP_FIRST MATCH_ACCEPT_TAC
    (map BETA_RULE [merge_iszero_prefix_transport_own, prune_jumps_prefix_transport_own,
      inefficient_jumps_prefix_transport_own, peephole_prefix_transport_own,
      merge_jumpdests_prefix_transport_own, prune_unreachable_prefix_transport_own,
      prune_unused_prefix_transport_own]))) >>
  disch_then MATCH_ACCEPT_TAC
QED
