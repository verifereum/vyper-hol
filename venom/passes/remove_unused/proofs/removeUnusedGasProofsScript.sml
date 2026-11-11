(* Local oracle reconstruction interface, independent of same-state simulation. *)
Theory removeUnusedGasProofs
Ancestors
  gasCount gasOracleReplay execEquivParamBase execEquivParamProps
  venomExecSemantics venomState venomExecProps
  removeUnusedProofs removeUnusedSsaProofs stateEquivProofs venomInstProofs1
  list rich_list pred_set arithmetic stateEquiv prim_rec words

(* Full-state equalities retain every non-gas frame field. *)
Theorem remove_unused_gas_cons:
  inst.inst_outputs = [out] ==>
  exec_gas inst (s with vs_gas_readings := d::tail) =
    OK (update_var out d (s with vs_gas_readings := tail))
Proof
  simp[exec_gas_def]
QED

Theorem remove_unused_gas_empty:
  inst.inst_outputs = [out] ==>
  exec_gas inst (s with vs_gas_readings := []) =
    OK (update_var out 0w (s with vs_gas_readings := []))
Proof
  simp[exec_gas_def]
QED

(* Paired retained GAS is provided by vsr_exec_gas.  Call boundaries are
   gas_setup_callee, gas_setup_callee_readings, gas_merge_callee and
   gas_merge_callee_readings from gasOracleReplay; do not duplicate them. *)

Theorem remove_unused_gas_prefix_length:
  LENGTH (gas_prefix n gs) = n
Proof
  simp[gas_prefix_def, LENGTH_TAKE_EQ]
QED

Theorem remove_unused_gas_prefix_el:
  i < n ==>
  EL i (gas_prefix n gs) =
    if i < LENGTH gs then EL i gs else 0w
Proof
  strip_tac >> simp[gas_prefix_def, EL_TAKE, EL_APPEND_EQN] >>
  Cases_on `i < LENGTH gs` >> simp[EL_REPLICATE]
QED

Theorem remove_unused_gas_prefix_eq:
  !n a b. gas_prefix n a = gas_prefix n b <=>
    !i. i < n ==>
      (if i < LENGTH a then EL i a else 0w) =
      (if i < LENGTH b then EL i b else 0w)
Proof
  simp[LIST_EQ_REWRITE, remove_unused_gas_prefix_length,
       remove_unused_gas_prefix_el]
QED

Theorem remove_unused_gas_prefix_idem:
  !a n. gas_prefix n (gas_prefix n a) = gas_prefix n a
Proof
  simp[remove_unused_gas_prefix_eq, remove_unused_gas_prefix_length,
       remove_unused_gas_prefix_el]
QED

Theorem remove_unused_filter_positions_finite:
  FINITE {i | i < LENGTH gs /\ P (EL i gs)}
Proof
  irule SUBSET_FINITE >> qexists_tac `count (LENGTH gs)` >>
  simp[SUBSET_DEF]
QED

Theorem remove_unused_filter_positions_card:
  !gs P. CARD {i | i < LENGTH gs /\ P (EL i gs)} =
    LENGTH (FILTER P gs)
Proof
  Induct_on `gs` >- simp[] >> rpt gen_tac >>
  `{i | i < LENGTH (h::gs) /\ P (EL i (h::gs))} =
     (if P h then 0 INSERT IMAGE SUC {i | i < LENGTH gs /\ P (EL i gs)}
      else IMAGE SUC {i | i < LENGTH gs /\ P (EL i gs)})` by
    (rw[EXTENSION] >> Cases_on `x` >> simp[]) >>
  Cases_on `P h` >>
  simp[IMAGE_FINITE, remove_unused_filter_positions_finite,
       CARD_INSERT, IN_IMAGE, CARD_IMAGE_SUC]
QED

Theorem remove_unused_gas_sparse_positions:
  !gs inds k. FINITE inds /\ CARD inds = SUC k /\
    (!i. i IN inds ==> i < LENGTH gs /\ EL i gs <> 0w) ==>
    k < LENGTH (FILTER (\x. x <> 0w) gs)
Proof
  rpt strip_tac >>
  `CARD inds <= CARD {i | i < LENGTH gs /\ EL i gs <> 0w}` by
    (irule CARD_SUBSET >>
     simp[remove_unused_filter_positions_finite, SUBSET_DEF]) >>
  gvs[remove_unused_filter_positions_card]
QED

(* Error observations ignore residual-oracle length.  Use replay on both
   sides to compare through one common padded prefix, even for short hs. *)
Theorem remove_unused_gas_replay_error:
  gas_replay_at n f s ==>
  !tail. ((?e. f (s with vs_gas_readings :=
                     gas_prefix n s.vs_gas_readings ++ tail) = Error e) <=>
          (?e. f s = Error e))
Proof
  simp[gas_replay_at_def] >> strip_tac >> gen_tac >>
  first_x_assum (qspec_then `tail` mp_tac) >>
  Cases_on `f s` >>
  Cases_on `f (s with vs_gas_readings :=
                gas_prefix n s.vs_gas_readings ++ tail)` >>
  simp[lift_result_def]
QED

Theorem remove_unused_gas_error_finite_dependence:
  !fuel ctx fn s gs. ?n. !hs.
    gas_prefix n hs = gas_prefix n gs ==>
    ((?e. run_blocks fuel ctx fn (s with vs_gas_readings := hs) = Error e) <=>
     (?e. run_blocks fuel ctx fn (s with vs_gas_readings := gs) = Error e))
Proof
  rpt gen_tac >>
  mp_tac (cj 1 gas_replay_fuel) >>
  disch_then (qspecl_then [`fuel`, `ctx`, `fn`,
                          `s with vs_gas_readings := gs`] mp_tac) >>
  simp[gas_replay_def] >> disch_then (qx_choose_then `n` assume_tac) >>
  qexists_tac `n` >> rpt strip_tac >>
  mp_tac (cj 1 gas_replay_fuel) >>
  disch_then (qspecl_then [`fuel`, `ctx`, `fn`,
                          `s with vs_gas_readings := hs`] mp_tac) >>
  simp[gas_replay_def] >> disch_then (qx_choose_then `m` assume_tac) >>
  mp_tac (Q.INST [`n` |-> `n`, `f` |-> `run_blocks fuel ctx fn`,
                   `s` |-> `s with vs_gas_readings := gs`]
                  remove_unused_gas_replay_error) >>
  simp[] >> disch_then (qspec_then `gas_prefix m (DROP n hs)` mp_tac) >>
  mp_tac (Q.INST [`n` |-> `m`, `f` |-> `run_blocks fuel ctx fn`,
                   `s` |-> `s with vs_gas_readings := hs`]
                  remove_unused_gas_replay_error) >>
  simp[] >> disch_then (qspec_then `gas_prefix n (DROP m hs)` mp_tac) >>
  qpat_x_assum `gas_prefix n hs = gas_prefix n gs`
    (fn th => pure_rewrite_tac[GSYM th]) >>
  simp[GSYM gas_prefix_add, ADD_COMM] >> metis_tac[]
QED

Theorem remove_unused_infinite_fibre:
  !s f:num -> 'a. INFINITE s /\ FINITE (IMAGE f s) ==>
    ?v. INFINITE {n | n IN s /\ f n = v}
Proof
  rpt strip_tac >> spose_not_then assume_tac >>
  `s = BIGUNION (IMAGE (\v. {n | n IN s /\ f n = v}) (IMAGE f s))` by
    (simp[EXTENSION, IN_BIGUNION_IMAGE, IN_IMAGE] >> metis_tac[]) >>
  `FINITE s` by
    (pop_assum SUBST1_TAC >> irule FINITE_BIGUNION >>
     simp[IMAGE_FINITE, IN_IMAGE] >> metis_tac[]) >>
  metis_tac[]
QED

Theorem remove_unused_stream_cluster:
  FINITE (UNIV:'a set) ==>
  !a:num -> num -> 'a. ?w. !m.
    INFINITE {n | !i. i < m ==> a n i = w i}
Proof
  strip_tac >> gen_tac >>
  `!m s. INFINITE s ==> ?v. INFINITE {n | n IN s /\ a n m = v}` by
    (rpt strip_tac >>
     qspecl_then [`s`, `\n. a n m`] mp_tac remove_unused_infinite_fibre >>
     simp[] >> disch_then irule >>
     metis_tac[SUBSET_FINITE, SUBSET_UNIV]) >>
  qabbrev_tac `c = \m s. @v. INFINITE {n | n IN s /\ a n m = v}` >>
  `!m s. INFINITE s ==> INFINITE {n | n IN s /\ a n m = c m s}` by
    (simp[Abbr `c`] >> metis_tac[SELECT_AX]) >>
  qspecl_then [`UNIV:num set`,
    `\m s. {n | n IN s /\ a n m = c m s}`] mp_tac num_Axiom >>
  disch_then (qx_choose_then `b` strip_assume_tac) >>
  `!m. INFINITE (b m) /\
       !n. n IN b m ==> !i. i < m ==> a n i = c i (b i)` by
    (Induct >- simp[INFINITE_NUM_UNIV] >>
     simp[] >> rpt strip_tac >> Cases_on `i = m` >> gvs[] >>
     first_x_assum irule >> simp[]) >>
  qexists_tac `\i. c i (b i)` >> gen_tac >>
  irule INFINITE_SUBSET >> qexists_tac `b m` >>
  simp[SUBSET_DEF] >> metis_tac[]
QED

Theorem remove_unused_sparse_cluster_support:
  !k (a:num -> (256 word) list) w.
    (!n. LENGTH (FILTER (\x. x <> 0w) (a n)) <= k) /\
    (!m. ?n. !i. i < m ==>
      (if i < LENGTH (a n) then EL i (a n) else 0w) = w i) ==>
    FINITE {i | w i <> 0w}
Proof
  rpt strip_tac >> spose_not_then assume_tac >>
  drule (iffLR infinite_num_inj) >>
  disch_then (qx_choose_then `g` assume_tac) >>
  qabbrev_tac `inds = IMAGE g (count (SUC k))` >>
  `FINITE inds /\ CARD inds = SUC k /\
    !i. i IN inds ==> w i <> 0w` by
    (simp[Abbr `inds`, IMAGE_FINITE] >> conj_tac
     >- (irule EQ_TRANS >> qexists_tac `CARD (count (SUC k))` >>
         conj_tac >- (irule CARD_IMAGE_INJ >> gvs[INJ_DEF]) >> simp[]) >>
     gvs[INJ_DEF, IN_IMAGE] >> metis_tac[]) >>
  first_x_assum (qspec_then `SUC (MAX_SET inds)`
    (qx_choose_then `n` assume_tac)) >>
  `!i. i IN inds ==> i < LENGTH (a n) /\ EL i (a n) <> 0w` by
    (rpt strip_tac >>
     `i < SUC (MAX_SET inds)` by
       (drule_all MAX_SET_PROPERTY >> simp[]) >>
     first_x_assum (qspec_then `i` mp_tac) >>
     Cases_on `i < LENGTH (a n)` >> gvs[]) >>
  drule_all remove_unused_gas_sparse_positions >>
  qpat_x_assum `!j. LENGTH _ <= k` (qspec_then `n` mp_tac) >> simp[]
QED

Theorem remove_unused_infinite_unbounded:
  !s:num set. INFINITE s ==> !N. ?n. N <= n /\ n IN s
Proof
  rpt strip_tac >>
  qspecl_then [`s`, `count N`] mp_tac IN_INFINITE_NOT_FINITE >>
  simp[] >> metis_tac[NOT_LESS]
QED

Theorem remove_unused_actual_oracle_nonzero:
  !n gs:(256 word) list.
    LENGTH (FILTER (\w. w <> 0w) (gas_prefix n gs ++ DROP n gs)) =
    LENGTH (FILTER (\w. w <> 0w) gs)
Proof
  rpt gen_tac >>
  Cases_on `n <= LENGTH gs`
  >- (`n - LENGTH gs = 0` by decide_tac >>
      simp[gas_prefix_def, TAKE_APPEND, listTheory.TAKE_DROP]) >>
  simp[gas_prefix_def, TAKE_APPEND, listTheory.DROP_LENGTH_TOO_LONG,
       listTheory.TAKE_LENGTH_TOO_LONG, FILTER_APPEND] >>
  simp[FILTER_EQ_NIL, EVERY_MEM] >>
  metis_tac[MEM_TAKE, MEM_REPLICATE]
QED

Theorem remove_unused_sparse_oracle_cluster:
  !k (a:num -> (256 word) list).
    (!n. LENGTH (FILTER (\x. x <> 0w) (a n)) <= k) ==>
    ?gs. LENGTH (FILTER (\x. x <> 0w) gs) <= k /\
      !m N. ?n. N <= n /\ gas_prefix m (a n) = gas_prefix m gs
Proof
  rpt strip_tac >>
  mp_tac (INST_TYPE [alpha |-> ``:256 word``] remove_unused_stream_cluster) >>
  simp[WORD_FINITE] >>
  disch_then (qspec_then
    `\n i. if i < LENGTH (a n) then EL i (a n) else 0w`
    (qx_choose_then `w` assume_tac)) >>
  `FINITE {i | w i <> 0w}` by
    (irule remove_unused_sparse_cluster_support >>
     qexistsl_tac [`a`, `k`] >> simp[] >> gen_tac >>
     first_x_assum (qspec_then `m` mp_tac) >>
     disch_then (mp_tac o MATCH_MP INFINITE_INHAB) >> simp[]) >>
  qabbrev_tac `b = SUC (MAX_SET {i | w i <> 0w})` >>
  `!i. (if i < b then EL i (GENLIST w b) else 0w) = w i` by
    (gen_tac >> Cases_on `i < b` >- simp[EL_GENLIST] >>
     `w i = 0w` suffices_by simp[] >>
     spose_not_then assume_tac >>
     `i <= MAX_SET {i | w i <> 0w}` by
       (irule MAX_SET_PROPERTY >> simp[]) >> gvs[Abbr `b`]) >>
  `!m N. ?n. N <= n /\ gas_prefix m (a n) = gas_prefix m (GENLIST w b)` by
    (rpt gen_tac >>
     qpat_x_assum `!m. INFINITE _` (qspec_then `m` mp_tac) >>
     disch_then (mp_tac o MATCH_MP remove_unused_infinite_unbounded) >>
     disch_then (qspec_then `N` (qx_choose_then `n` strip_assume_tac)) >>
     qexists_tac `n` >> gvs[remove_unused_gas_prefix_eq]) >>
  qexists_tac `GENLIST w b` >> simp[] >>
  first_x_assum (qspecl_then [`b`, `0`] (qx_choose_then `n` strip_assume_tac)) >>
  `gas_prefix b (GENLIST w b) = GENLIST w b` by
    simp[gas_prefix_def, TAKE_APPEND] >>
  mp_tac (Q.SPECL [`b`, `a (n:num)`] remove_unused_actual_oracle_nonzero) >>
  gvs[FILTER_APPEND] >>
  qpat_x_assum `!n. LENGTH _ <= k` (qspec_then `n` mp_tac) >> decide_tac
QED

Theorem remove_unused_sparse_oracle_compactness:
  !P k.
    (!n:num. ?gs:(256 word) list.
      LENGTH (FILTER (\x. x <> 0w) gs) <= k /\
      !j. j <= n ==> P j gs) /\
    (!j gs. ?m. !hs. gas_prefix m hs = gas_prefix m gs ==>
      (P j hs <=> P j gs)) ==>
    ?gs. LENGTH (FILTER (\x. x <> 0w) gs) <= k /\ !j. P j gs
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `!n. ?gs. _` mp_tac >>
  simp[SKOLEM_THM] >> disch_then (qx_choose_then `a` assume_tac) >>
  `!n. LENGTH (FILTER (\x. x <> 0w) (a n)) <= k` by simp[] >>
  drule remove_unused_sparse_oracle_cluster >>
  disch_then (qx_choose_then `gs` strip_assume_tac) >>
  qexists_tac `gs` >> simp[] >> gen_tac >>
  qpat_x_assum `!j gs. ?m. _` (qspecl_then [`j`, `gs`]
    (qx_choose_then `m` assume_tac)) >>
  qpat_x_assum `!m N. ?n. _` (qspecl_then [`m`, `j`]
    (qx_choose_then `n` strip_assume_tac)) >>
  first_x_assum (qspec_then `a n` mp_tac) >> simp[] >>
  qpat_x_assum `!n. _ /\ _` (qspec_then `n` mp_tac) >>
  metis_tac[]
QED

Theorem remove_unused_semantic_error_mono:
  (!n ctx inst s. !m e.
    step_inst n ctx inst s = Error e /\ e <> "out of fuel" /\ n <= m ==>
    step_inst m ctx inst s = Error e) /\
  (!n ctx bb s. !m e.
    exec_block n ctx bb s = Error e /\ e <> "out of fuel" /\ n <= m ==>
    exec_block m ctx bb s = Error e) /\
  (!n ctx fn s. !m e.
    run_blocks n ctx fn s = Error e /\ e <> "out of fuel" /\ n <= m ==>
    run_blocks m ctx fn s = Error e)
Proof
  ho_match_mp_tac run_defs_ind >> rpt conj_tac
  >- suspend "instruction"
  >- suspend "block"
  >> suspend "runner"
QED

Resume remove_unused_semantic_error_mono[instruction]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- (gvs[Once step_inst_def, AllCaseEqs()] >>
      simp[Once step_inst_def] >>
      rename1 `run_blocks n ctx callee cs = _` >>
      `run_blocks m ctx callee cs = run_blocks n ctx callee cs` by
        (gvs[] >> drule (cj 3 fuel_mono) >> simp[]) >>
      simp[Once step_inst_def]) >>
  gvs[step_inst_non_invoke]
QED

Resume remove_unused_semantic_error_mono[block]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `exec_block _ _ _ _ = _` mp_tac >>
  simp[Once exec_block_def] >>
  Cases_on `get_instruction bb s.vs_inst_idx` >> simp[]
  >- (strip_tac >> gvs[] >> simp[Once exec_block_def]) >>
  rename1 `SOME inst` >>
  Cases_on `step_inst n ctx inst s` >> simp[]
  >- (rename1 `step_inst n ctx inst s = OK v` >>
      `step_inst m ctx inst s = OK v` by
        (drule (cj 1 fuel_mono) >> simp[]) >>
      Cases_on `is_terminator inst.inst_opcode` >> simp[] >>
      strip_tac >> simp[Once exec_block_def] >>
      first_x_assum drule >> simp[]) >>
  strip_tac >> gvs[] >>
  `step_inst m ctx inst s = Error e` by metis_tac[] >>
  simp[Once exec_block_def]
QED

Resume remove_unused_semantic_error_mono[runner]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `n` >- gvs[run_blocks_def] >>
  Cases_on `m` >- gvs[] >>
  qmatch_goalsub_rename_tac `run_blocks (SUC mf) ctx fn s` >>
  qpat_x_assum `run_blocks _ _ _ _ = _`
    (mp_tac o ONCE_REWRITE_RULE [run_blocks_def]) >>
  simp[] >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks` >> simp[]
  >- (strip_tac >> gvs[] >> simp[Once run_blocks_def]) >>
  rename1 `SOME bb` >>
  qspecl_then [`s`, `bb.bb_instructions`] strip_assume_tac
    eval_phis_ok_or_error_defs >> simp[]
  >- (rename1 `eval_phis s bb.bb_instructions = OK ps` >>
      qmatch_goalsub_rename_tac `exec_block smallfuel ctx bb _` >>
      qmatch_goalsub_abbrev_tac `exec_block smallfuel ctx bb start` >>
      Cases_on `exec_block smallfuel ctx bb start` >> simp[]
      >- (rename1 `exec_block smallfuel ctx bb start = OK v` >>
          `exec_block mf ctx bb start = OK v` by
            (drule (cj 2 fuel_mono) >> simp[]) >>
          Cases_on `v.vs_halted` >> simp[] >> strip_tac >>
          gvs[Abbr `start`] >> simp[Once run_blocks_def] >>
          metis_tac[]) >>
      strip_tac >> gvs[] >>
      `exec_block mf ctx bb start = Error e` by
        (gvs[Abbr `start`] >> metis_tac[]) >>
      simp[Once run_blocks_def]) >>
  strip_tac >> gvs[] >> simp[Once run_blocks_def]
QED

Finalise remove_unused_semantic_error_mono

Theorem remove_unused_run_blocks_error_mono:
  !n ctx fn s m e.
    run_blocks n ctx fn s = Error e /\ e <> "out of fuel" /\ n <= m ==>
    run_blocks m ctx fn s = Error e
Proof
  metis_tac[cj 3 remove_unused_semantic_error_mono]
QED

Theorem remove_unused_run_blocks_error_all_fuel:
  !n ctx fn s e.
    run_blocks n ctx fn s = Error e /\ e <> "out of fuel" ==>
    !fuel. ?err. run_blocks fuel ctx fn s = Error err
Proof
  rpt strip_tac >> Cases_on `n <= fuel`
  >- metis_tac[remove_unused_run_blocks_error_mono] >>
  Cases_on `run_blocks fuel ctx fn s` >> simp[] >>
  drule (cj 3 fuel_mono) >> simp[] >>
  qexists_tac `n` >> simp[]
QED

(* tail may be empty: the final residual is the actual suffix, not padding. *)
Theorem remove_unused_gas_two_reads:
  i.inst_outputs = [x] /\ j.inst_outputs = [y] ==>
  ?mid.
    exec_gas i (s with vs_gas_readings := d::v::tail) = OK mid /\
    exec_gas j mid =
      OK (update_var y v (update_var x d (s with vs_gas_readings := tail)))
Proof
  strip_tac >>
  qexists_tac `update_var x d (s with vs_gas_readings := v::tail)` >>
  simp[exec_gas_def]
QED

(* Continuations may include the exec_block instruction-index update.  They
   receive the complete post-instruction state; only their INPUT premise
   normalizes readings.  The final relations never ignore the oracle. *)
Theorem remove_unused_deleted_gas_continuation:
  !inst live out V s t m (src_cont:venom_state -> exec_result) dst_cont.
    inst.inst_opcode = GAS /\ inst.inst_outputs = [out] /\ out IN V /\
    remove_unused_inst live inst = mk_nop_inst inst /\
    s.vs_inst_idx = t.vs_inst_idx /\
    state_equiv V (s with vs_gas_readings := t.vs_gas_readings) t /\
    gas_replay_at m dst_cont t /\ ~(?e. dst_cont t = Error e) /\
    (!u v j.
      state_equiv V (v with vs_gas_readings := u.vs_gas_readings) u /\
      gas_replay_at j dst_cont u /\ ~(?e. dst_cont u = Error e) ==>
      ?q:(256 word) list.
        LENGTH (FILTER (\w. w <> 0w) q) <=
          LENGTH (FILTER (\w. w <> 0w) (gas_prefix j u.vs_gas_readings)) /\
        !tail.
          (?e. e <> "out of fuel" /\
            src_cont (v with vs_gas_readings := q ++ tail) = Error e) \/
          lift_result (state_equiv V) (execution_equiv V) (execution_equiv V)
            (src_cont (v with vs_gas_readings := q ++ tail))
            (dst_cont (u with vs_gas_readings :=
              gas_prefix j u.vs_gas_readings ++ tail))) ==>
    ?p:(256 word) list.
      LENGTH (FILTER (\w. w <> 0w) p) <=
        LENGTH (FILTER (\w. w <> 0w) (gas_prefix m t.vs_gas_readings)) /\
      !tail.
        let r = case exec_gas inst (s with vs_gas_readings := p ++ tail) of
                  OK a => src_cont a | other => other in
        (?e. e <> "out of fuel" /\ r = Error e) \/
        lift_result (state_equiv V) (execution_equiv V) (execution_equiv V)
          r (dst_cont (t with vs_gas_readings :=
            gas_prefix m t.vs_gas_readings ++ tail))
Proof
  rpt strip_tac >>
  `state_equiv V
     ((update_var out 0w s) with vs_gas_readings := t.vs_gas_readings) t` by
    (pure_once_rewrite_tac[GSYM gas_update_var] >>
     irule state_equiv_effect_free_compose >>
     qexistsl [`{out}`, `s with vs_gas_readings := t.vs_gas_readings`] >>
     simp[update_var_state_equiv]) >>
  first_x_assum (qspecl_then [`t`, `update_var out 0w s`, `m`] mp_tac) >>
  impl_tac >- metis_tac[] >> strip_tac >>
  qexists_tac `0w::q` >> simp[exec_gas_def, gas_update_var]
QED

Theorem remove_unused_retained_gas_continuation:
  !inst out V s t u w m (src_cont:venom_state -> exec_result) dst_cont.
    inst.inst_opcode = GAS /\ inst.inst_outputs = [out] /\
    s.vs_inst_idx = t.vs_inst_idx /\
    state_equiv V (s with vs_gas_readings := t.vs_gas_readings) t /\
    exec_gas inst t = OK u /\
    w = (case t.vs_gas_readings of [] => 0w | h::rest => h) /\
    gas_replay_at m dst_cont u /\ ~(?e. dst_cont u = Error e) /\
    (!a b j.
      state_equiv V (b with vs_gas_readings := a.vs_gas_readings) a /\
      gas_replay_at j dst_cont a /\ ~(?e. dst_cont a = Error e) ==>
      ?q:(256 word) list.
        LENGTH (FILTER (\z. z <> 0w) q) <=
          LENGTH (FILTER (\z. z <> 0w) (gas_prefix j a.vs_gas_readings)) /\
        !tail.
          (?e. e <> "out of fuel" /\
            src_cont (b with vs_gas_readings := q ++ tail) = Error e) \/
          lift_result (state_equiv V) (execution_equiv V) (execution_equiv V)
            (src_cont (b with vs_gas_readings := q ++ tail))
            (dst_cont (a with vs_gas_readings :=
              gas_prefix j a.vs_gas_readings ++ tail))) ==>
    ?p:(256 word) list.
      LENGTH (FILTER (\z. z <> 0w) p) <=
        LENGTH (FILTER (\z. z <> 0w)
          (gas_prefix (SUC m) t.vs_gas_readings)) /\
      !tail.
        let r = case exec_gas inst (s with vs_gas_readings := p ++ tail) of
                  OK a => src_cont a | other => other in
        let r' = case exec_gas inst
                        (t with vs_gas_readings :=
                          gas_prefix (SUC m) t.vs_gas_readings ++ tail) of
                   OK a => dst_cont a | other => other in
        (?e. e <> "out of fuel" /\ r = Error e) \/
        lift_result (state_equiv V) (execution_equiv V) (execution_equiv V)
          r r'
Proof
  rpt strip_tac >>
  `u = update_var out w (t with vs_gas_readings := u.vs_gas_readings)` by
    (Cases_on `t.vs_gas_readings` >> gvs[exec_gas_def]) >>
  `gas_prefix (SUC m) t.vs_gas_readings =
     w :: gas_prefix m u.vs_gas_readings` by
    (Cases_on `t.vs_gas_readings` >> gvs[exec_gas_def, gas_prefix_suc]) >>
  `state_equiv V
     ((update_var out w s) with vs_gas_readings := u.vs_gas_readings) u` by
    (qpat_assum `u = update_var _ _ _` (fn th => once_rewrite_tac[th]) >>
     pure_once_rewrite_tac[GSYM gas_update_var] >>
     irule stateEquivProofsTheory.update_var_preserves >>
     qpat_x_assum `state_equiv V _ t` mp_tac >>
     simp[state_equiv_def, execution_equiv_def,
          stateFrameTheory.execution_frame_def, venom_state_component_equality,
          lookup_var_def]) >>
  qpat_x_assum `w = (case t.vs_gas_readings of [] => 0w | h::rest => h)` kall_tac >>
  first_x_assum (qspecl_then [`u`, `update_var out w s`, `m`] mp_tac) >>
  impl_tac >- metis_tac[] >> strip_tac >>
  qexists_tac `w::q` >> conj_tac
  >- (Cases_on `w = 0w` >> simp[]) >>
  gen_tac >>
  qpat_x_assum `!tail. _` (qspec_then `tail` mp_tac) >>
  qpat_assum `u = update_var _ _ _` (fn th => once_rewrite_tac[th]) >>
  simp[exec_gas_def, gas_update_var]
QED

(* Non-GAS base instructions consume no readings, including terminators. *)
Theorem remove_unused_base_oracle_transport:
  inst.inst_opcode <> GAS ==>
  !gs. lift_result
    (\a b. a.vs_gas_readings = s.vs_gas_readings /\
           b = (a with vs_gas_readings := gs))
    (\a b. a.vs_gas_readings = s.vs_gas_readings /\
           b = (a with vs_gas_readings := gs))
    (\a b. a.vs_gas_readings = s.vs_gas_readings /\
           b = (a with vs_gas_readings := gs))
    (step_inst_base inst s)
    (step_inst_base inst (s with vs_gas_readings := gs))
Proof
  strip_tac >> drule gas_base_non_gas >>
  simp[gas_replay_at_def]
QED

Theorem remove_unused_replay_ok:
  !n f s u. gas_replay_at n f s /\ f s = OK u ==>
    u.vs_gas_readings = DROP n s.vs_gas_readings /\
    !gs. f (s with vs_gas_readings := gas_prefix n s.vs_gas_readings ++ gs) =
         OK (u with vs_gas_readings := gs)
Proof
  rpt gen_tac >> strip_tac >>
  qpat_x_assum `gas_replay_at n f s` mp_tac >>
  simp[gas_replay_at_def] >> strip_tac >> conj_tac
  >- (first_x_assum (qspec_then `[]` mp_tac) >>
      Cases_on `f (s with vs_gas_readings := gas_prefix n s.vs_gas_readings ++ [])` >>
      gvs[lift_result_def]) >>
  gen_tac >> first_x_assum (qspec_then `gs` mp_tac) >>
  Cases_on `f (s with vs_gas_readings := gas_prefix n s.vs_gas_readings ++ gs)` >>
  gvs[lift_result_def]
QED

Theorem remove_unused_base_oracle_ok:
  !inst s u. inst.inst_opcode <> GAS /\ step_inst_base inst s = OK u ==>
  u.vs_gas_readings = s.vs_gas_readings /\
  !gs. step_inst_base inst (s with vs_gas_readings := gs) =
       OK (u with vs_gas_readings := gs)
Proof
  rpt gen_tac >> strip_tac >>
  `gas_replay_at 0 (step_inst_base inst) s` by
    (irule gas_base_non_gas >> simp[]) >>
  drule_all remove_unused_replay_ok >> simp[]
QED

(* Direct transport also covers retained terminators; no continuation needed. *)
Theorem remove_unused_retained_base_transport:
  state_equiv V (s with vs_gas_readings := t.vs_gas_readings) t /\
  (!x. MEM (Var x) inst.inst_operands ==> x NOTIN V) ==>
  !gs. lift_result (state_equiv V) (execution_equiv V) (execution_equiv V)
    (step_inst_base inst (s with vs_gas_readings := gs))
    (step_inst_base inst (t with vs_gas_readings := gs))
Proof
  rpt strip_tac >>
  rewrite_tac[GSYM stateEquivPropsTheory.result_equiv_is_lift_result] >>
  irule execEquivPropsTheory.step_inst_base_result_equiv >> simp[] >>
  qpat_x_assum `state_equiv V _ t` mp_tac >>
  simp[state_equiv_def, execution_equiv_def,
       stateFrameTheory.execution_frame_def, lookup_var_def]
QED

Theorem remove_unused_retained_base_continuation:
  !inst V s t u m (src_cont:venom_state -> exec_result) dst_cont.
    inst.inst_opcode <> GAS /\ inst.inst_opcode <> INVOKE /\
    state_equiv V (s with vs_gas_readings := t.vs_gas_readings) t /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN V) /\
    step_inst_base inst t = OK u /\
    gas_replay_at m dst_cont u /\ ~(?e. dst_cont u = Error e) /\
    (!a b j.
      state_equiv V (b with vs_gas_readings := a.vs_gas_readings) a /\
      gas_replay_at j dst_cont a /\ ~(?e. dst_cont a = Error e) ==>
      ?q:(256 word) list.
        LENGTH (FILTER (\z. z <> 0w) q) <=
          LENGTH (FILTER (\z. z <> 0w) (gas_prefix j a.vs_gas_readings)) /\
        !tail.
          (?e. e <> "out of fuel" /\
            src_cont (b with vs_gas_readings := q ++ tail) = Error e) \/
          lift_result (state_equiv V) (execution_equiv V) (execution_equiv V)
            (src_cont (b with vs_gas_readings := q ++ tail))
            (dst_cont (a with vs_gas_readings :=
              gas_prefix j a.vs_gas_readings ++ tail))) ==>
    ?p:(256 word) list.
      LENGTH (FILTER (\z. z <> 0w) p) <=
        LENGTH (FILTER (\z. z <> 0w) (gas_prefix m t.vs_gas_readings)) /\
      !tail.
        let r = case step_inst_base inst (s with vs_gas_readings := p ++ tail) of
                  OK a => src_cont a | other => other in
        let r' = case step_inst_base inst
                        (t with vs_gas_readings :=
                          gas_prefix m t.vs_gas_readings ++ tail) of
                   OK a => dst_cont a | other => other in
        (?e. e <> "out of fuel" /\ r = Error e) \/
        lift_result (state_equiv V) (execution_equiv V) (execution_equiv V)
          r r'
Proof
  rpt strip_tac >>
  `result_equiv V
     (step_inst_base inst (s with vs_gas_readings := t.vs_gas_readings))
     (step_inst_base inst t)` by
    (irule execEquivPropsTheory.step_inst_base_result_equiv >> simp[]) >>
  Cases_on `step_inst_base inst (s with vs_gas_readings := t.vs_gas_readings)` >>
  gvs[result_equiv_def] >> rename1 `state_equiv V v u` >>
  `u.vs_gas_readings = t.vs_gas_readings /\
   !gs. step_inst_base inst (t with vs_gas_readings := gs) =
        OK (u with vs_gas_readings := gs)` by
    (irule remove_unused_base_oracle_ok >> simp[]) >>
  `!gs. step_inst_base inst (s with vs_gas_readings := gs) =
        OK (v with vs_gas_readings := gs)` by
    (qspecl_then [`inst`, `s with vs_gas_readings := t.vs_gas_readings`, `v`]
       mp_tac remove_unused_base_oracle_ok >> simp[]) >>
  `state_equiv V (v with vs_gas_readings := u.vs_gas_readings) u` by
    (gvs[state_equiv_def, execution_equiv_def,
         stateFrameTheory.execution_frame_def, venom_state_component_equality,
         lookup_var_def]) >>
  first_x_assum (qspecl_then [`u`, `v`, `m`] mp_tac) >>
  impl_tac >- metis_tac[] >> strip_tac >>
  qexists_tac `q` >> gvs[]
QED

(* Inspect the actual error constructors, not merely fuel independence. *)
Theorem remove_unused_effect_free_not_fuel_error:
  !inst s. is_effect_free_op inst.inst_opcode ==>
    step_inst_base inst s <> Error "out of fuel"
Proof
  rpt strip_tac >> Cases_on `inst.inst_opcode` >>
  gvs[venomInstTheory.is_effect_free_op_def] >>
  gvs[step_inst_base_opcode_eqs] >>
  gvs[exec_pure1_def, exec_pure2_def, exec_pure3_def,
      exec_read0_def, exec_read1_def, AllCaseEqs()]
QED

Theorem remove_unused_deleted_base_continuation:
  !inst V s t m (src_cont:venom_state -> exec_result) dst_cont.
    is_effect_free_op inst.inst_opcode /\
    inst.inst_opcode <> GAS /\ inst.inst_opcode <> INVOKE /\
    set inst.inst_outputs SUBSET V /\
    state_equiv V (s with vs_gas_readings := t.vs_gas_readings) t /\
    gas_replay_at m dst_cont t /\ ~(?e. dst_cont t = Error e) /\
    (!a b j.
      state_equiv V (b with vs_gas_readings := a.vs_gas_readings) a /\
      gas_replay_at j dst_cont a /\ ~(?e. dst_cont a = Error e) ==>
      ?q:(256 word) list.
        LENGTH (FILTER (\z. z <> 0w) q) <=
          LENGTH (FILTER (\z. z <> 0w) (gas_prefix j a.vs_gas_readings)) /\
        !tail.
          (?e. e <> "out of fuel" /\
            src_cont (b with vs_gas_readings := q ++ tail) = Error e) \/
          lift_result (state_equiv V) (execution_equiv V) (execution_equiv V)
            (src_cont (b with vs_gas_readings := q ++ tail))
            (dst_cont (a with vs_gas_readings :=
              gas_prefix j a.vs_gas_readings ++ tail))) ==>
    ?p:(256 word) list.
      LENGTH (FILTER (\z. z <> 0w) p) <=
        LENGTH (FILTER (\z. z <> 0w) (gas_prefix m t.vs_gas_readings)) /\
      !tail.
        let r = case step_inst_base inst (s with vs_gas_readings := p ++ tail) of
                  OK a => src_cont a | other => other in
        (?e. e <> "out of fuel" /\ r = Error e) \/
        lift_result (state_equiv V) (execution_equiv V) (execution_equiv V)
          r (dst_cont (t with vs_gas_readings :=
            gas_prefix m t.vs_gas_readings ++ tail))
Proof
  rpt strip_tac >>
  `(?v. step_inst_base inst s = OK v) \/
   (?e. step_inst_base inst s = Error e)` by
    metis_tac[effect_free_step_ok_or_error, step_inst_non_invoke]
  >- (drule_all venomInstProofsTheory.step_inst_base_effect_free_state_equiv >>
      strip_tac >>
      `state_equiv V (v with vs_gas_readings := t.vs_gas_readings) t` by
        (irule state_equiv_effect_free_compose >>
         qexistsl [`set inst.inst_outputs`, `s with vs_gas_readings := t.vs_gas_readings`] >>
         simp[] >>
         gvs[state_equiv_def, execution_equiv_def,
             stateFrameTheory.execution_frame_def, lookup_var_def]) >>
      first_x_assum (qspecl_then [`t`, `v`, `m`] mp_tac) >>
      impl_tac >- metis_tac[] >> strip_tac >>
      `!gs. step_inst_base inst (s with vs_gas_readings := gs) =
            OK (v with vs_gas_readings := gs)` by
        (drule_all remove_unused_base_oracle_ok >> simp[]) >>
      qexists_tac `q` >> simp[]) >>
  qexists_tac `[]` >> simp[] >> gen_tac >>
  drule remove_unused_base_oracle_transport >>
  disch_then (qspec_then `s` (qspec_then `tail` mp_tac)) >>
  Cases_on `step_inst_base inst (s with vs_gas_readings := tail)` >>
  gvs[lift_result_def] >>
  strip_tac >> gvs[] >>
  drule remove_unused_effect_free_not_fuel_error >>
  disch_then (qspec_then `s with vs_gas_readings := tail` mp_tac) >> simp[]
QED

(* Preserve a supplied callee replay count through the real INVOKE wrapper. *)
Theorem remove_unused_invoke_replay_at:
  !inst name ops ctx fn args s cs fuel n.
    inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME (name,ops) /\
    lookup_function name ctx.ctx_functions = SOME fn /\
    eval_operands ops s = SOME args /\ setup_callee fn args s = SOME cs /\
    gas_replay_at n (run_blocks fuel ctx fn) cs ==>
    gas_replay_at n (step_inst fuel ctx inst) s
Proof
  rpt strip_tac >>
  drule gas_setup_callee_readings >> strip_tac >>
  qpat_x_assum `gas_replay_at n _ _` mp_tac >>
  simp[gas_replay_at_def, step_inst_def, gas_setup_callee] >>
  disch_tac >> gen_tac >>
  first_x_assum (qspec_then `tail` mp_tac) >>
  Cases_on `run_blocks fuel ctx fn cs` >>
  Cases_on `run_blocks fuel ctx fn
    (cs with vs_gas_readings := gas_prefix n s.vs_gas_readings ++ tail)` >>
  gvs[lift_result_def, gas_merge_callee, gas_adopt_return, gas_bind_outputs] >>
  strip_tac >> gvs[] >>
  Cases_on `bind_outputs inst.inst_outputs i.iret_values
    (adopt_return_fmp i (merge_callee_state s v))` >>
  simp[lift_result_def] >>
  drule gas_bind_outputs_readings >> simp[gas_adopt_return_readings]
QED

Theorem remove_unused_invoke_pair_replay:
  !inst V s t fuel ctx.
    inst.inst_opcode = INVOKE /\
    state_equiv V (s with vs_gas_readings := t.vs_gas_readings) t /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN V) /\
    ~(?e. step_inst fuel ctx inst t = Error e) ==>
    ?n. gas_replay_at n (step_inst fuel ctx inst)
          (s with vs_gas_readings := t.vs_gas_readings) /\
        gas_replay_at n (step_inst fuel ctx inst) t
Proof
  rpt strip_tac >> Cases_on `decode_invoke inst`
  >- gvs[step_inst_def] >>
  PairCases_on `x` >> rename1 `decode_invoke inst = SOME (name, ops)` >>
  Cases_on `lookup_function name ctx.ctx_functions`
  >- gvs[step_inst_def] >> rename1 `SOME fn` >>
  Cases_on `eval_operands ops t`
  >- gvs[step_inst_def] >> rename1 `eval_operands ops t = SOME args` >>
  Cases_on `setup_callee fn args t`
  >- gvs[step_inst_def] >> rename1 `setup_callee fn args t = SOME cs` >>
  `inst.inst_operands = Label name :: ops` by
    gvs[decode_invoke_def, AllCaseEqs()] >>
  `eval_operands ops (s with vs_gas_readings := t.vs_gas_readings) =
   eval_operands ops t` by
    (irule eval_operands_state_equiv >> qexists_tac `V` >>
     simp[] >> metis_tac[MEM]) >>
  `setup_callee fn args (s with vs_gas_readings := t.vs_gas_readings) =
   setup_callee fn args t` by
    (irule setup_callee_state_equiv >> qexists_tac `V` >> simp[]) >>
  qspecl_then [`fuel`, `ctx`] (mp_tac o cj 1) gas_replay_fuel >>
  disch_then (qspecl_then [`fn`, `cs`] mp_tac) >>
  rewrite_tac[gas_replay_def] >> strip_tac >>
  qexists_tac `n` >> conj_tac >>
  irule remove_unused_invoke_replay_at >> metis_tac[]
QED

Theorem remove_unused_retained_invoke_transport:
  !inst V s t fuel ctx gs.
    inst.inst_opcode = INVOKE /\
    state_equiv V (s with vs_gas_readings := t.vs_gas_readings) t /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN V) ==>
    lift_result (state_equiv V) (execution_equiv V) (execution_equiv V)
      (step_inst fuel ctx inst (s with vs_gas_readings := gs))
      (step_inst fuel ctx inst (t with vs_gas_readings := gs))
Proof
  rpt strip_tac >>
  rewrite_tac[GSYM stateEquivPropsTheory.result_equiv_is_lift_result] >>
  irule step_inst_result_equiv_full >> simp[venomInstTheory.is_terminator_def] >>
  qpat_x_assum `state_equiv V _ t` mp_tac >>
  simp[state_equiv_def, execution_equiv_def,
       stateFrameTheory.execution_frame_def, lookup_var_def]
QED

Theorem remove_unused_retained_invoke_continuation:
  !inst V s t u fuel ctx m (src_cont:venom_state -> exec_result) dst_cont.
    inst.inst_opcode = INVOKE /\
    state_equiv V (s with vs_gas_readings := t.vs_gas_readings) t /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN V) /\
    step_inst fuel ctx inst t = OK u /\
    gas_replay_at m dst_cont u /\ ~(?e. dst_cont u = Error e) /\
    (!a b j.
      state_equiv V (b with vs_gas_readings := a.vs_gas_readings) a /\
      gas_replay_at j dst_cont a /\ ~(?e. dst_cont a = Error e) ==>
      ?q:(256 word) list.
        LENGTH (FILTER (\z. z <> 0w) q) <=
          LENGTH (FILTER (\z. z <> 0w) (gas_prefix j a.vs_gas_readings)) /\
        !tail.
          (?e. e <> "out of fuel" /\
            src_cont (b with vs_gas_readings := q ++ tail) = Error e) \/
          lift_result (state_equiv V) (execution_equiv V) (execution_equiv V)
            (src_cont (b with vs_gas_readings := q ++ tail))
            (dst_cont (a with vs_gas_readings :=
              gas_prefix j a.vs_gas_readings ++ tail))) ==>
    ?n (p:(256 word) list).
      gas_replay_at n (step_inst fuel ctx inst) t /\
      LENGTH (FILTER (\z. z <> 0w) p) <=
        LENGTH (FILTER (\z. z <> 0w) (gas_prefix (n + m) t.vs_gas_readings)) /\
      !tail.
        let r = case step_inst fuel ctx inst (s with vs_gas_readings := p ++ tail) of
                  OK a => src_cont a | other => other in
        let r' = case step_inst fuel ctx inst
                        (t with vs_gas_readings :=
                          gas_prefix (n + m) t.vs_gas_readings ++ tail) of
                   OK a => dst_cont a | other => other in
        (?e. e <> "out of fuel" /\ r = Error e) \/
        lift_result (state_equiv V) (execution_equiv V) (execution_equiv V)
          r r'
Proof
  rpt strip_tac >>
  `result_equiv V
     (step_inst fuel ctx inst (s with vs_gas_readings := t.vs_gas_readings))
     (step_inst fuel ctx inst t)` by
    (irule step_inst_result_equiv_full >> simp[venomInstTheory.is_terminator_def]) >>
  Cases_on `step_inst fuel ctx inst (s with vs_gas_readings := t.vs_gas_readings)` >>
  gvs[result_equiv_def] >> rename1 `state_equiv V v u` >>
  `?n. gas_replay_at n (step_inst fuel ctx inst)
          (s with vs_gas_readings := t.vs_gas_readings) /\
       gas_replay_at n (step_inst fuel ctx inst) t` by
    (irule remove_unused_invoke_pair_replay >> simp[] >>
     qexists_tac `V` >> simp[]) >>
  `u.vs_gas_readings = DROP n t.vs_gas_readings /\
   !gs. step_inst fuel ctx inst
     (t with vs_gas_readings := gas_prefix n t.vs_gas_readings ++ gs) =
     OK (u with vs_gas_readings := gs)` by
    (drule_all remove_unused_replay_ok >> simp[]) >>
  `!gs. step_inst fuel ctx inst
     (s with vs_gas_readings := gas_prefix n t.vs_gas_readings ++ gs) =
     OK (v with vs_gas_readings := gs)` by
    (qpat_assum `step_inst _ _ _ (s with vs_gas_readings := _) = OK v`
       (mp_then (Pos last) mp_tac remove_unused_replay_ok) >>
     simp[] >> disch_then drule >> simp[]) >>
  `state_equiv V (v with vs_gas_readings := u.vs_gas_readings) u` by
    (gvs[state_equiv_def, execution_equiv_def,
         stateFrameTheory.execution_frame_def, venom_state_component_equality,
         lookup_var_def]) >>
  first_x_assum (qspecl_then [`u`, `v`, `m`] mp_tac) >>
  impl_tac >- metis_tac[] >> strip_tac >>
  `gas_prefix (m + n) t.vs_gas_readings =
     gas_prefix n t.vs_gas_readings ++ gas_prefix m u.vs_gas_readings` by
    (once_rewrite_tac[ADD_COMM] >> simp[gas_prefix_add]) >>
  qexistsl [`n`, `gas_prefix n t.vs_gas_readings ++ q`] >>
  simp[FILTER_APPEND] >>
  pure_rewrite_tac[GSYM APPEND_ASSOC] >> asm_rewrite_tac[] >> gvs[]
QED

(* Halt, Abort and internal returns bypass caller continuations.  The supplied
   replay count can be any actual witness for the unchanged target call. *)
Theorem remove_unused_retained_invoke_terminal:
  !inst V s t fuel ctx n (src_cont:venom_state -> exec_result) dst_cont.
    inst.inst_opcode = INVOKE /\
    state_equiv V (s with vs_gas_readings := t.vs_gas_readings) t /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN V) /\
    gas_replay_at n (step_inst fuel ctx inst) t /\
    ~(?a. step_inst fuel ctx inst t = OK a) /\
    ~(?e. step_inst fuel ctx inst t = Error e) ==>
    ?p:(256 word) list.
      LENGTH (FILTER (\z. z <> 0w) p) <=
        LENGTH (FILTER (\z. z <> 0w) (gas_prefix n t.vs_gas_readings)) /\
      !tail.
        lift_result (state_equiv V) (execution_equiv V) (execution_equiv V)
          (case step_inst fuel ctx inst (s with vs_gas_readings := p ++ tail) of
             OK a => src_cont a | other => other)
          (case step_inst fuel ctx inst
                  (t with vs_gas_readings := gas_prefix n t.vs_gas_readings ++ tail) of
             OK a => dst_cont a | other => other)
Proof
  rpt strip_tac >> qexists_tac `gas_prefix n t.vs_gas_readings` >> simp[] >>
  gen_tac >>
  `~(?a. step_inst fuel ctx inst
      (t with vs_gas_readings := gas_prefix n t.vs_gas_readings ++ tail) = OK a)` by
    (qpat_x_assum `gas_replay_at n _ t` mp_tac >>
     rewrite_tac[gas_replay_at_def] >> disch_then (qspec_then `tail` mp_tac) >>
     Cases_on `step_inst fuel ctx inst t` >> gvs[] >>
     Cases_on `step_inst fuel ctx inst
       (t with vs_gas_readings := gas_prefix n t.vs_gas_readings ++ tail)` >>
     gvs[lift_result_def]) >>
  `lift_result (state_equiv V) (execution_equiv V) (execution_equiv V)
     (step_inst fuel ctx inst
       (s with vs_gas_readings := gas_prefix n t.vs_gas_readings ++ tail))
     (step_inst fuel ctx inst
       (t with vs_gas_readings := gas_prefix n t.vs_gas_readings ++ tail))` by
    (irule remove_unused_retained_invoke_transport >> simp[]) >>
  qpat_x_assum `state_equiv V _ t` kall_tac >>
  qpat_x_assum `!x. MEM (Var x) _ ==> _` kall_tac >>
  Cases_on `step_inst fuel ctx inst
    (t with vs_gas_readings := gas_prefix n t.vs_gas_readings ++ tail)` >> gvs[] >>
  Cases_on `step_inst fuel ctx inst
    (s with vs_gas_readings := gas_prefix n t.vs_gas_readings ++ tail)` >>
  gvs[lift_result_def]
QED

Theorem remove_unused_replay_count_unique:
  !f s n m.
    gas_replay_at n f s /\ gas_replay_at m f s /\
    ~(?e. f s = Error e) ==> n = m
Proof
  rpt strip_tac >> wlog_tac `n <= m` [`n`, `m`]
  >- (`m <= n` by decide_tac >> metis_tac[]) >>
  `m = n + (m - n)` by decide_tac >>
  `gas_prefix m s.vs_gas_readings =
   gas_prefix n s.vs_gas_readings ++
   gas_prefix (m - n) (DROP n s.vs_gas_readings)` by
    metis_tac[gas_prefix_add] >>
  qpat_x_assum `gas_replay_at n f s` mp_tac >>
  rewrite_tac[gas_replay_at_def] >>
  disch_then (qspec_then `gas_prefix (m - n) (DROP n s.vs_gas_readings)` mp_tac) >>
  qpat_x_assum `gas_replay_at m f s` mp_tac >>
  rewrite_tac[gas_replay_at_def] >>
  disch_then (qspec_then `[]` mp_tac) >>
  Cases_on `f s` >> gvs[] >>
  Cases_on `f (s with vs_gas_readings := gas_prefix m s.vs_gas_readings)` >>
  gvs[lift_result_def, venom_state_component_equality] >>
  rpt strip_tac >>
  qpat_x_assum `gas_prefix (m - n) _ = []`
    (mp_tac o AP_TERM ``LENGTH : bytes32 list -> num``) >>
  rewrite_tac[remove_unused_gas_prefix_length, LENGTH] >>
  decide_tac
QED

Theorem remove_unused_replay_bind_ok_count:
  !f k s u n m.
    gas_replay_at n f s /\ f s = OK u /\ gas_replay_at m k u ==>
    gas_replay_at (n + m) (\v. gas_bind_ok (f v) k) s
Proof
  rpt strip_tac >>
  simp[gas_replay_at_def, gas_prefix_add, APPEND_ASSOC] >>
  gen_tac >>
  qpat_x_assum `gas_replay_at n f s` mp_tac >>
  simp[gas_replay_at_def] >>
  disch_then (qspec_then
    `gas_prefix m (DROP n s.vs_gas_readings) ++ tail` mp_tac) >>
  Cases_on `f (s with vs_gas_readings :=
    gas_prefix n s.vs_gas_readings ++
    (gas_prefix m (DROP n s.vs_gas_readings) ++ tail))` >>
  simp[lift_result_def] >> strip_tac >> gvs[] >>
  qpat_x_assum `gas_replay_at m k u` mp_tac >>
  simp[gas_replay_at_def] >>
  disch_then (qspec_then `tail` mp_tac) >>
  simp[gas_bind_ok_def, DROP_DROP_T, ADD_COMM]
QED

Theorem remove_unused_replay_bind_terminal_count:
  !f k s n.
    gas_replay_at n f s /\ ~(?u. f s = OK u) ==>
    gas_replay_at n (\v. gas_bind_ok (f v) k) s
Proof
  rpt strip_tac >> Cases_on `f s` >> gvs[] >>
  qpat_x_assum `gas_replay_at n f s` mp_tac >>
  simp[gas_replay_at_def] >> disch_tac >> gen_tac >>
  first_x_assum (qspec_then `tail` mp_tac) >>
  Cases_on `f (s with vs_gas_readings :=
    gas_prefix n s.vs_gas_readings ++ tail)` >>
  simp[lift_result_def, gas_bind_ok_def]
QED

Theorem remove_unused_replay_count_cong:
  f s = g s /\
  (!gs. f (s with vs_gas_readings := gs) =
        g (s with vs_gas_readings := gs)) /\
  gas_replay_at n g s ==> gas_replay_at n f s
Proof
  simp[gas_replay_at_def] >> metis_tac[]
QED

Theorem remove_unused_replay_count_preupdate:
  (!u gs. h (u with vs_gas_readings := gs) =
             (h u with vs_gas_readings := gs)) /\
  (!u. (h u).vs_gas_readings = u.vs_gas_readings) /\
  gas_replay_at n f (h s) ==>
  gas_replay_at n (\u. f (h u)) s
Proof
  simp[gas_replay_at_def] >> rpt strip_tac >> gvs[]
QED


(* Threshold audit: the callee and caller each consume an exhausted reading.
   Padding both zeros protects the appended nonzero suffix across return. *)
Theorem remove_unused_call_prefix_threshold_probe[local]:
  let callee = mk_raw_function "callee"
        [<|bb_label := "c"; bb_instructions :=
           [mk_inst 0 GAS [] ["x"]; mk_inst 1 RET [Lit 0w] []]|>] in
  let caller = mk_raw_function "caller"
        [<|bb_label := "b"; bb_instructions :=
           [mk_inst 2 INVOKE [Label "callee"] [];
            mk_inst 3 GAS [] ["y"]; mk_inst 4 STOP [] []]|>] in
  let ctx = mk_venom_context [caller;callee] (SOME "caller") in
  let t = init_venom_state "b" in
  run_blocks 1 ctx caller t = Error "out of fuel" /\
  run_blocks 1 ctx caller (t with vs_gas_readings := [0w;0w;7w]) =
    Error "out of fuel" /\
  (?u. run_blocks 2 ctx caller t = Halt u /\
       u.vs_gas_readings = [] /\ lookup_var "y" u = SOME 0w) /\
  (?u. run_blocks 2 ctx caller (t with vs_gas_readings := [0w;0w;7w]) = Halt u /\
       u.vs_gas_readings = [7w] /\ lookup_var "y" u = SOME 0w)
Proof
  EVAL_TAC >> simp[finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem remove_unused_gas_prefix_split:
  !a b xs ys. gas_prefix (a+b) xs = gas_prefix (a+b) ys ==>
    gas_prefix a xs = gas_prefix a ys /\
    gas_prefix b (DROP a xs) = gas_prefix b (DROP a ys)
Proof
  rpt gen_tac >> rewrite_tac[gas_prefix_add] >> strip_tac >>
  conj_tac
  >- (qpat_x_assum `_ ++ _ = _ ++ _`
        (mp_tac o AP_TERM ``TAKE a : (256 word) list -> (256 word) list``) >>
      simp[TAKE_APPEND, TAKE_LENGTH_ID_rwt, remove_unused_gas_prefix_length]) >>
  qpat_x_assum `_ ++ _ = _ ++ _`
    (mp_tac o AP_TERM ``DROP a : (256 word) list -> (256 word) list``) >>
  simp[DROP_APPEND, DROP_LENGTH_TOO_LONG, remove_unused_gas_prefix_length]
QED

Theorem remove_unused_gas_prefix_append:
  !n xs tail.
    gas_prefix n (gas_prefix n xs ++ tail) = gas_prefix n xs /\
    DROP n (gas_prefix n xs ++ tail) = tail
Proof
  rpt gen_tac >> conj_tac
  >- (simp[remove_unused_gas_prefix_eq, remove_unused_gas_prefix_length,
           remove_unused_gas_prefix_el, EL_APPEND_EQN]) >>
  simp[DROP_APPEND, DROP_LENGTH_TOO_LONG, remove_unused_gas_prefix_length]
QED

Theorem remove_unused_gas_prefix_agree_mono:
  !m n xs ys. m <= n /\ gas_prefix n xs = gas_prefix n ys ==>
    gas_prefix m xs = gas_prefix m ys
Proof
  simp[remove_unused_gas_prefix_eq] >> rpt strip_tac >>
  first_x_assum irule >> decide_tac
QED

Theorem remove_unused_successful_prefix_threshold:
  (!N ctx inst s. !k gs.
    ~(?e. step_inst N ctx inst s = Error e) /\ k <= N /\
    gas_prefix (gas_count_step N ctx inst s) gs =
      gas_prefix (gas_count_step N ctx inst s) s.vs_gas_readings ==>
    (((?e. step_inst k ctx inst (s with vs_gas_readings := gs) = Error e) <=>
      (?e. step_inst k ctx inst s = Error e)) /\
     (~(?e. step_inst k ctx inst s = Error e) ==>
      lift_result
        (\a b. b = (a with vs_gas_readings := DROP (gas_count_step N ctx inst s) gs))
        (\a b. b = (a with vs_gas_readings := DROP (gas_count_step N ctx inst s) gs))
        (\a b. b = (a with vs_gas_readings := DROP (gas_count_step N ctx inst s) gs))
        (step_inst N ctx inst s) (step_inst k ctx inst (s with vs_gas_readings := gs))))) /\
  (!N ctx bb s. !k gs.
    ~(?e. exec_block N ctx bb s = Error e) /\ k <= N /\
    gas_prefix (gas_count_block N ctx bb s) gs =
      gas_prefix (gas_count_block N ctx bb s) s.vs_gas_readings ==>
    (((?e. exec_block k ctx bb (s with vs_gas_readings := gs) = Error e) <=>
      (?e. exec_block k ctx bb s = Error e)) /\
     (~(?e. exec_block k ctx bb s = Error e) ==>
      lift_result
        (\a b. b = (a with vs_gas_readings := DROP (gas_count_block N ctx bb s) gs))
        (\a b. b = (a with vs_gas_readings := DROP (gas_count_block N ctx bb s) gs))
        (\a b. b = (a with vs_gas_readings := DROP (gas_count_block N ctx bb s) gs))
        (exec_block N ctx bb s) (exec_block k ctx bb (s with vs_gas_readings := gs))))) /\
  (!N ctx fn s. !k gs.
    ~(?e. run_blocks N ctx fn s = Error e) /\ k <= N /\
    gas_prefix (gas_count_blocks N ctx fn s) gs =
      gas_prefix (gas_count_blocks N ctx fn s) s.vs_gas_readings ==>
    (((?e. run_blocks k ctx fn (s with vs_gas_readings := gs) = Error e) <=>
      (?e. run_blocks k ctx fn s = Error e)) /\
     (~(?e. run_blocks k ctx fn s = Error e) ==>
      lift_result
        (\a b. b = (a with vs_gas_readings := DROP (gas_count_blocks N ctx fn s) gs))
        (\a b. b = (a with vs_gas_readings := DROP (gas_count_blocks N ctx fn s) gs))
        (\a b. b = (a with vs_gas_readings := DROP (gas_count_blocks N ctx fn s) gs))
        (run_blocks N ctx fn s) (run_blocks k ctx fn (s with vs_gas_readings := gs)))))
Proof
  ho_match_mp_tac gas_count_defs_ind >> rpt conj_tac
  >- suspend "step"
  >- suspend "block"
  >> suspend "blocks"
QED
Resume remove_unused_successful_prefix_threshold[step]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- suspend "invoke" >>
  qpat_x_assum `!v callee_name arg_ops fn args s''. _` kall_tac >>
  gvs[step_inst_def] >>
  Cases_on `inst.inst_opcode = GAS`
  >- suspend "gas" >>
  `gas_replay_at 0 (step_inst_base inst) s` by
    (irule gas_base_non_gas >> simp[]) >>
  gvs[gas_count_step_def, gas_replay_at_def] >>
  first_x_assum (qspec_then `gs` mp_tac) >>
  Cases_on `step_inst_base inst s` >> gvs[lift_result_def] >>
  Cases_on `step_inst_base inst (s with vs_gas_readings := gs)` >>
  simp[lift_result_def]
QED
Resume remove_unused_successful_prefix_threshold[gas]:
  gvs[gas_count_step_def] >>
  qpat_x_assum `gas_prefix 1 _ = _` mp_tac >>
  rewrite_tac[remove_unused_gas_prefix_eq] >>
  disch_then (qspec_then `0` mp_tac) >> simp[] >> strip_tac >>
  gvs[step_inst_base_def] >>
  Cases_on `inst.inst_outputs` >> gvs[exec_gas_def] >>
  rename1 `inst.inst_outputs = out::outs` >>
  Cases_on `outs` >> gvs[exec_gas_def] >>
  Cases_on `s.vs_gas_readings` >> Cases_on `gs` >>
  gvs[exec_gas_def, lift_result_def]
QED
Resume remove_unused_successful_prefix_threshold[invoke]:
  qpat_x_assum `~(?e. step_inst _ _ _ _ = Error e)` mp_tac >>
  simp[step_inst_def] >>
  Cases_on `decode_invoke inst` >- simp[] >>
  PairCases_on `x` >> simp[] >>
  Cases_on `lookup_function x0 ctx.ctx_functions` >- simp[] >>
  rename1 `lookup_function x0 ctx.ctx_functions = SOME fn` >>
  Cases_on `eval_operands x1 s` >- simp[] >>
  rename1 `eval_operands x1 s = SOME args` >>
  Cases_on `setup_callee fn args s` >- simp[] >>
  rename1 `setup_callee fn args s = SOME cs` >>
  strip_tac >>
  `~(?e. run_blocks N ctx fn cs = Error e)` by
    (Cases_on `run_blocks N ctx fn cs` >> gvs[]) >>
  `cs.vs_gas_readings = s.vs_gas_readings` by
    (drule gas_setup_callee_readings >> simp[]) >>
  `gas_prefix (gas_count_blocks N ctx fn cs) gs =
   gas_prefix (gas_count_blocks N ctx fn cs) cs.vs_gas_readings` by
    gvs[gas_count_step_def] >>
  qpat_x_assum `!v callee_name arg_ops fn args s''. _` mp_tac >>
  simp[] >> disch_then (qspecl_then [`k`, `gs`] mp_tac) >> simp[] >>
  gvs[gas_setup_callee, gas_count_step_def] >> strip_tac >>
  Cases_on `run_blocks k ctx fn cs`
  >- suspend "invoke_ok"
  >- suspend "invoke_halt"
  >- suspend "invoke_abort"
  >- suspend "invoke_ret"
  >> gvs[lift_result_def]
QED
Resume remove_unused_successful_prefix_threshold[invoke_ok]:
  `run_blocks N ctx fn cs = OK v` by
    (irule (cj 3 fuel_mono) >> simp[] >> qexists_tac `k` >> simp[]) >>
  gvs[]
QED
Resume remove_unused_successful_prefix_threshold[invoke_halt]:
  `run_blocks N ctx fn cs = Halt v` by
    (irule (cj 3 fuel_mono) >> simp[] >> qexists_tac `k` >> simp[]) >>
  gvs[lift_result_def] >>
  Cases_on `run_blocks k ctx fn (cs with vs_gas_readings := gs)` >>
  gvs[lift_result_def]
QED
Resume remove_unused_successful_prefix_threshold[invoke_abort]:
  `run_blocks N ctx fn cs = Abort a v` by
    (irule (cj 3 fuel_mono) >> simp[] >> qexists_tac `k` >> simp[]) >>
  gvs[lift_result_def] >>
  Cases_on `run_blocks k ctx fn (cs with vs_gas_readings := gs)` >>
  gvs[lift_result_def]
QED
Resume remove_unused_successful_prefix_threshold[invoke_ret]:
  `run_blocks N ctx fn cs = IntRet i v` by
    (irule (cj 3 fuel_mono) >> simp[] >> qexists_tac `k` >> simp[]) >>
  gvs[lift_result_def] >>
  Cases_on `run_blocks k ctx fn (cs with vs_gas_readings := gs)` >>
  gvs[lift_result_def, gas_merge_callee, gas_adopt_return,
      gas_bind_outputs] >>
  Cases_on `bind_outputs inst.inst_outputs i.iret_values
    (adopt_return_fmp i (merge_callee_state s v))` >> gvs[lift_result_def]
QED
Resume remove_unused_successful_prefix_threshold[block]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `get_instruction bb s.vs_inst_idx`
  >- (qpat_x_assum `~(?e. exec_block _ _ _ _ = Error e)` mp_tac >>
      simp[Once exec_block_def]) >>
  rename1 `get_instruction bb s.vs_inst_idx = SOME inst` >>
  `~(?e. step_inst N ctx inst s = Error e)` by
    (qpat_x_assum `~(?e. exec_block _ _ _ _ = Error e)` mp_tac >>
     simp[Once exec_block_def] >> Cases_on `step_inst N ctx inst s` >> simp[]) >>
  qpat_x_assum `!inst. _` (qspec_then `inst` mp_tac) >> simp[] >>
  strip_tac >>
  `gas_count_step N ctx inst s <= gas_count_block N ctx bb s` by
    simp[Once gas_count_block_def] >>
  `gas_prefix (gas_count_step N ctx inst s) gs =
   gas_prefix (gas_count_step N ctx inst s) s.vs_gas_readings` by
    (irule remove_unused_gas_prefix_agree_mono >>
     qexists_tac `gas_count_block N ctx bb s` >> simp[]) >>
  qpat_x_assum `!k' gs'. _` (qspecl_then [`k`, `gs`] mp_tac) >>
  simp[] >> strip_tac >>
  Cases_on `step_inst k ctx inst s`
  >- suspend "block_ok"
  >- suspend "block_halt"
  >- suspend "block_abort"
  >- suspend "block_ret"
  >> suspend "block_error"
QED
Resume remove_unused_successful_prefix_threshold[block_error]:
  qpat_x_assum `!inst s''. _` kall_tac >>
  gvs[] >>
  pure_once_rewrite_tac[exec_block_def] >> simp[] >>
  Cases_on `step_inst k ctx inst (s with vs_gas_readings := gs)` >>
  gvs[lift_result_def]
QED
Resume remove_unused_successful_prefix_threshold[block_halt]:
  qpat_x_assum `!inst s''. _` kall_tac >>
  `step_inst N ctx inst s = Halt v` by
    (irule (cj 1 fuel_mono) >> simp[] >> qexists_tac `k` >> simp[]) >>
  gvs[lift_result_def] >>
  Cases_on `step_inst k ctx inst (s with vs_gas_readings := gs)` >>
  gvs[lift_result_def] >>
  `exec_block k ctx bb s = Halt v` by simp[Once exec_block_def] >>
  `exec_block N ctx bb s = Halt v` by simp[Once exec_block_def] >>
  `exec_block k ctx bb (s with vs_gas_readings := gs) =
    Halt (v with vs_gas_readings := DROP (gas_count_step N ctx inst s) gs)` by
    simp[Once exec_block_def] >>
  `gas_count_block N ctx bb s = gas_count_step N ctx inst s` by
    simp[Once gas_count_block_def] >>
  simp[lift_result_def]
QED
Resume remove_unused_successful_prefix_threshold[block_abort]:
  qpat_x_assum `!inst s''. _` kall_tac >>
  `step_inst N ctx inst s = Abort a v` by
    (irule (cj 1 fuel_mono) >> simp[] >> qexists_tac `k` >> simp[]) >>
  gvs[lift_result_def] >>
  Cases_on `step_inst k ctx inst (s with vs_gas_readings := gs)` >>
  gvs[lift_result_def] >>
  `exec_block k ctx bb s = Abort a v` by simp[Once exec_block_def] >>
  `exec_block N ctx bb s = Abort a v` by simp[Once exec_block_def] >>
  `exec_block k ctx bb (s with vs_gas_readings := gs) =
    Abort a (v with vs_gas_readings := DROP (gas_count_step N ctx inst s) gs)` by
    simp[Once exec_block_def] >>
  `gas_count_block N ctx bb s = gas_count_step N ctx inst s` by
    simp[Once gas_count_block_def] >>
  simp[lift_result_def]
QED
Resume remove_unused_successful_prefix_threshold[block_ret]:
  qpat_x_assum `!inst s''. _` kall_tac >>
  `step_inst N ctx inst s = IntRet i v` by
    (irule (cj 1 fuel_mono) >> simp[] >> qexists_tac `k` >> simp[]) >>
  gvs[lift_result_def] >>
  Cases_on `step_inst k ctx inst (s with vs_gas_readings := gs)` >>
  gvs[lift_result_def] >>
  `exec_block k ctx bb s = IntRet i v` by simp[Once exec_block_def] >>
  `exec_block N ctx bb s = IntRet i v` by simp[Once exec_block_def] >>
  `exec_block k ctx bb (s with vs_gas_readings := gs) =
    IntRet i (v with vs_gas_readings := DROP (gas_count_step N ctx inst s) gs)` by
    simp[Once exec_block_def] >>
  `gas_count_block N ctx bb s = gas_count_step N ctx inst s` by
    simp[Once gas_count_block_def] >>
  simp[lift_result_def]
QED
Resume remove_unused_successful_prefix_threshold[block_ok]:
  `step_inst N ctx inst s = OK v` by
    (irule (cj 1 fuel_mono) >> simp[] >> qexists_tac `k` >> simp[]) >>
  gvs[lift_result_def] >>
  Cases_on `step_inst k ctx inst (s with vs_gas_readings := gs)` >>
  gvs[lift_result_def] >>
  Cases_on `is_terminator inst.inst_opcode`
  >- suspend "block_term" >>
  `gas_count_block N ctx bb s = gas_count_step N ctx inst s +
     gas_count_block N ctx bb (v with vs_inst_idx := SUC s.vs_inst_idx)` by
    simp[Once gas_count_block_def] >>
  `v.vs_gas_readings = DROP (gas_count_step N ctx inst s) s.vs_gas_readings` by
    (mp_tac (cj 1 gas_count_suffix) >>
     disch_then (qspecl_then [`N`, `ctx`, `inst`, `s`] mp_tac) >>
     simp[gas_count_suffix_def]) >>
  qpat_x_assum `gas_prefix (gas_count_block N ctx bb s) _ = _` mp_tac >>
  asm_rewrite_tac[] >> disch_then (mp_then Any strip_assume_tac remove_unused_gas_prefix_split) >>
  qpat_x_assum `~is_terminator _ ==> _` mp_tac >> simp[] >>
  disch_then (qspecl_then [`k`, `DROP (gas_count_step N ctx inst s) gs`] mp_tac) >>
  `exec_block N ctx bb s = exec_block N ctx bb
     (v with vs_inst_idx := SUC s.vs_inst_idx)` by simp[Once exec_block_def] >>
  `exec_block k ctx bb s = exec_block k ctx bb
     (v with vs_inst_idx := SUC s.vs_inst_idx)` by simp[Once exec_block_def] >>
  `exec_block k ctx bb (s with vs_gas_readings := gs) = exec_block k ctx bb
     (v with <|vs_inst_idx := SUC s.vs_inst_idx;
       vs_gas_readings := DROP (gas_count_step N ctx inst s) gs|>)` by
    simp[Once exec_block_def] >>
  impl_tac >- (simp[] >> metis_tac[]) >>
  pure_asm_rewrite_tac[DROP_DROP_T] >>
  simp[Once ADD_COMM]
QED
Resume remove_unused_successful_prefix_threshold[block_term]:
  qpat_x_assum `~is_terminator _ ==> _` kall_tac >>
  Cases_on `v.vs_halted` >>
  `exec_block k ctx bb s = (if v.vs_halted then Halt v else OK v)` by
    simp[Once exec_block_def] >>
  `exec_block N ctx bb s = (if v.vs_halted then Halt v else OK v)` by
    simp[Once exec_block_def] >>
  `exec_block k ctx bb (s with vs_gas_readings := gs) =
    (if v.vs_halted then Halt (v with vs_gas_readings := DROP (gas_count_step N ctx inst s) gs)
     else OK (v with vs_gas_readings := DROP (gas_count_step N ctx inst s) gs))` by
    simp[Once exec_block_def] >>
  `gas_count_block N ctx bb s = gas_count_step N ctx inst s` by
    simp[Once gas_count_block_def] >>
  simp[lift_result_def]
QED
Resume remove_unused_successful_prefix_threshold[blocks]:
  rpt gen_tac >> strip_tac >> rpt gen_tac >> strip_tac >>
  Cases_on `k`
  >- (`!t. run_blocks 0 ctx fn t = Error "out of fuel"` by
        simp[Once run_blocks_def] >> simp[]) >>
  rename1 `SUC m <= N` >>
  Cases_on `N` >- gvs[] >> rename1 `SUC m <= SUC n` >>
  Cases_on `lookup_block s.vs_current_bb fn.fn_blocks`
  >- (qpat_x_assum `~(?e. run_blocks _ _ _ _ = Error e)` mp_tac >>
      simp[Once run_blocks_def]) >>
  rename1 `lookup_block s.vs_current_bb fn.fn_blocks = SOME bb` >>
  reverse (qspecl_then [`s`, `bb.bb_instructions`] strip_assume_tac eval_phis_ok_or_error_defs)
  >- (qpat_x_assum `~(?e. run_blocks _ _ _ _ = Error e)` mp_tac >>
      simp[Once run_blocks_def]) >>
  rename1 `eval_phis s bb.bb_instructions = OK sp` >>
  `sp.vs_gas_readings = s.vs_gas_readings` by metis_tac[gas_count_phis_ok] >>
  `eval_phis (s with vs_gas_readings := gs) bb.bb_instructions =
     OK (sp with vs_gas_readings := gs)` by
    (qspecl_then [`bb.bb_instructions`, `s`] mp_tac gas_eval_phis >>
     simp[gas_replay_at_def] >> disch_then (qspec_then `gs` mp_tac) >>
     Cases_on `eval_phis (s with vs_gas_readings := gs) bb.bb_instructions` >>
     simp[lift_result_def]) >>  `~(?e. exec_block n ctx bb
      (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions) = Error e)` by
    (qpat_x_assum `~(?e. run_blocks _ _ _ _ = Error e)` mp_tac >>
     simp[Once run_blocks_def] >>
     Cases_on `exec_block n ctx bb (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)` >> simp[]) >>
  `gas_count_block n ctx bb
      (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions) <=
    gas_count_blocks (SUC n) ctx fn s` by
    (simp[Once gas_count_blocks_def] >>
     Cases_on `exec_block n ctx bb (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)` >> simp[]) >>
  `gas_prefix (gas_count_block n ctx bb
      (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)) gs =
   gas_prefix (gas_count_block n ctx bb
      (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)) sp.vs_gas_readings` by
    (irule remove_unused_gas_prefix_agree_mono >>
     qexists_tac `gas_count_blocks (SUC n) ctx fn s` >> simp[]) >>
  qpat_x_assum `!N' bb' s_phi. _` mp_tac >> simp[] >>
  disch_then (qspecl_then [`m`, `gs`] mp_tac) >> simp[] >> strip_tac >>
  qpat_x_assum `( !e. exec_block _ _ _ _ <> Error e) ==> _` mp_tac >>
  (impl_tac >- metis_tac[]) >> strip_tac >>
  Cases_on `exec_block m ctx bb (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)`
  >- suspend "blocks_ok"
  >- suspend "blocks_halt"
  >- suspend "blocks_abort"
  >- suspend "blocks_ret"
  >> suspend "blocks_error"
QED
Resume remove_unused_successful_prefix_threshold[blocks_error]:
  qpat_x_assum `!N' bb' s_phi s''. _` kall_tac >>
  gvs[] >>
  pure_once_rewrite_tac[run_blocks_def] >>
  simp[gas_eval_phis] >>
  Cases_on `exec_block m ctx bb
    (sp with <|vs_inst_idx := phi_prefix_length bb.bb_instructions;
               vs_gas_readings := gs|>)` >> gvs[lift_result_def]
QED
Resume remove_unused_successful_prefix_threshold[blocks_halt]:
  qpat_x_assum `!N' bb' s_phi s''. _` kall_tac >>
  `exec_block n ctx bb (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions) = Halt v` by
    (irule (cj 2 fuel_mono) >> simp[] >> qexists_tac `m` >> simp[]) >>
  gvs[lift_result_def] >>
  Cases_on `exec_block m ctx bb
    (sp with <|vs_inst_idx := phi_prefix_length bb.bb_instructions;
               vs_gas_readings := gs|>)` >> gvs[lift_result_def] >>
  `run_blocks (SUC n) ctx fn s = Halt v` by simp[Once run_blocks_def] >>
  `run_blocks (SUC m) ctx fn s = Halt v` by simp[Once run_blocks_def] >>
  `run_blocks (SUC m) ctx fn (s with vs_gas_readings := gs) =
     Halt (v with vs_gas_readings := DROP (gas_count_block n ctx bb
       (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)) gs)` by
    simp[Once run_blocks_def, gas_eval_phis] >>
  `gas_count_blocks (SUC n) ctx fn s = gas_count_block n ctx bb
       (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)` by
    simp[Once gas_count_blocks_def] >>
  simp[lift_result_def]
QED
Resume remove_unused_successful_prefix_threshold[blocks_abort]:
  qpat_x_assum `!N' bb' s_phi s''. _` kall_tac >>
  `exec_block n ctx bb (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions) = Abort a v` by
    (irule (cj 2 fuel_mono) >> simp[] >> qexists_tac `m` >> simp[]) >>
  gvs[lift_result_def] >>
  Cases_on `exec_block m ctx bb
    (sp with <|vs_inst_idx := phi_prefix_length bb.bb_instructions;
               vs_gas_readings := gs|>)` >> gvs[lift_result_def] >>
  `run_blocks (SUC n) ctx fn s = Abort a v` by simp[Once run_blocks_def] >>
  `run_blocks (SUC m) ctx fn s = Abort a v` by simp[Once run_blocks_def] >>
  `run_blocks (SUC m) ctx fn (s with vs_gas_readings := gs) =
     Abort a (v with vs_gas_readings := DROP (gas_count_block n ctx bb
       (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)) gs)` by
    simp[Once run_blocks_def] >>
  `gas_count_blocks (SUC n) ctx fn s = gas_count_block n ctx bb
       (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)` by
    simp[Once gas_count_blocks_def] >>
  simp[lift_result_def]
QED
Resume remove_unused_successful_prefix_threshold[blocks_ret]:
  qpat_x_assum `!N' bb' s_phi s''. _` kall_tac >>
  `exec_block n ctx bb (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions) = IntRet i v` by
    (irule (cj 2 fuel_mono) >> simp[] >> qexists_tac `m` >> simp[]) >>
  gvs[lift_result_def] >>
  Cases_on `exec_block m ctx bb
    (sp with <|vs_inst_idx := phi_prefix_length bb.bb_instructions;
               vs_gas_readings := gs|>)` >> gvs[lift_result_def] >>
  `run_blocks (SUC n) ctx fn s = IntRet i v` by simp[Once run_blocks_def] >>
  `run_blocks (SUC m) ctx fn s = IntRet i v` by simp[Once run_blocks_def] >>
  `run_blocks (SUC m) ctx fn (s with vs_gas_readings := gs) =
     IntRet i (v with vs_gas_readings := DROP (gas_count_block n ctx bb
       (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)) gs)` by
    simp[Once run_blocks_def] >>
  `gas_count_blocks (SUC n) ctx fn s = gas_count_block n ctx bb
       (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)` by
    simp[Once gas_count_blocks_def] >>
  simp[lift_result_def]
QED
Resume remove_unused_successful_prefix_threshold[blocks_ok]:
  `exec_block n ctx bb (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions) = OK v` by
    (irule (cj 2 fuel_mono) >> simp[] >> qexists_tac `m` >> simp[]) >>
  gvs[lift_result_def] >>
  Cases_on `exec_block m ctx bb
    (sp with <|vs_inst_idx := phi_prefix_length bb.bb_instructions;
               vs_gas_readings := gs|>)` >> gvs[lift_result_def] >>
  Cases_on `v.vs_halted`
  >- suspend "blocks_stopped" >>
  `run_blocks (SUC n) ctx fn s = run_blocks n ctx fn v` by
    simp[Once run_blocks_def] >>
  `run_blocks (SUC m) ctx fn s = run_blocks m ctx fn v` by
    simp[Once run_blocks_def] >>
  `run_blocks (SUC m) ctx fn (s with vs_gas_readings := gs) =
     run_blocks m ctx fn (v with vs_gas_readings := DROP (gas_count_block n ctx bb
       (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)) gs)` by
    simp[Once run_blocks_def] >>
  `gas_count_blocks (SUC n) ctx fn s = gas_count_block n ctx bb
       (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions) + gas_count_blocks n ctx fn v` by
    simp[Once gas_count_blocks_def] >>
  `v.vs_gas_readings = DROP (gas_count_block n ctx bb
       (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)) s.vs_gas_readings` by
    (mp_tac (cj 2 gas_count_suffix) >>
     disch_then (qspecl_then [`n`, `ctx`, `bb`,
       `sp with vs_inst_idx := phi_prefix_length bb.bb_instructions`] mp_tac) >>
     simp[gas_count_suffix_def]) >>
  qpat_x_assum `gas_prefix (gas_count_blocks (SUC n) ctx fn s) _ = _` mp_tac >>
  asm_rewrite_tac[] >>
  disch_then (mp_then Any strip_assume_tac remove_unused_gas_prefix_split) >>
  qpat_x_assum `~v.vs_halted ==> _` mp_tac >> simp[] >>
  disch_then (qspecl_then [`m`, `DROP (gas_count_block n ctx bb
       (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)) gs`] mp_tac) >>
  (impl_tac >- (simp[] >> metis_tac[])) >>
  pure_asm_rewrite_tac[DROP_DROP_T] >> simp[Once ADD_COMM]
QED
Resume remove_unused_successful_prefix_threshold[blocks_stopped]:
  qpat_x_assum `~v.vs_halted ==> _` kall_tac >>
  `run_blocks (SUC n) ctx fn s = Halt v` by simp[Once run_blocks_def] >>
  `run_blocks (SUC m) ctx fn s = Halt v` by simp[Once run_blocks_def] >>
  `run_blocks (SUC m) ctx fn (s with vs_gas_readings := gs) =
     Halt (v with vs_gas_readings := DROP (gas_count_block n ctx bb
       (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)) gs)` by
    simp[Once run_blocks_def] >>
  `gas_count_blocks (SUC n) ctx fn s = gas_count_block n ctx bb
       (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions)` by
    simp[Once gas_count_blocks_def] >>
  simp[lift_result_def]
QED
Finalise remove_unused_successful_prefix_threshold

Theorem remove_unused_step_successful_prefix_threshold:
  !N ctx inst s k gs.
    ~(?e. step_inst N ctx inst s = Error e) /\ k <= N /\
    gas_prefix (gas_count_step N ctx inst s) gs =
      gas_prefix (gas_count_step N ctx inst s) s.vs_gas_readings ==>
    (((?e. step_inst k ctx inst (s with vs_gas_readings := gs) = Error e) <=>
      (?e. step_inst k ctx inst s = Error e)) /\
     (~(?e. step_inst k ctx inst s = Error e) ==>
      lift_result
        (\a b. b = (a with vs_gas_readings := DROP (gas_count_step N ctx inst s) gs))
        (\a b. b = (a with vs_gas_readings := DROP (gas_count_step N ctx inst s) gs))
        (\a b. b = (a with vs_gas_readings := DROP (gas_count_step N ctx inst s) gs))
        (step_inst N ctx inst s) (step_inst k ctx inst (s with vs_gas_readings := gs))))
Proof
  MATCH_ACCEPT_TAC (cj 1 remove_unused_successful_prefix_threshold)
QED

Theorem remove_unused_block_successful_prefix_threshold:
  !N ctx bb s k gs.
    ~(?e. exec_block N ctx bb s = Error e) /\ k <= N /\
    gas_prefix (gas_count_block N ctx bb s) gs =
      gas_prefix (gas_count_block N ctx bb s) s.vs_gas_readings ==>
    (((?e. exec_block k ctx bb (s with vs_gas_readings := gs) = Error e) <=>
      (?e. exec_block k ctx bb s = Error e)) /\
     (~(?e. exec_block k ctx bb s = Error e) ==>
      lift_result
        (\a b. b = (a with vs_gas_readings := DROP (gas_count_block N ctx bb s) gs))
        (\a b. b = (a with vs_gas_readings := DROP (gas_count_block N ctx bb s) gs))
        (\a b. b = (a with vs_gas_readings := DROP (gas_count_block N ctx bb s) gs))
        (exec_block N ctx bb s) (exec_block k ctx bb (s with vs_gas_readings := gs))))
Proof
  MATCH_ACCEPT_TAC (cj 2 remove_unused_successful_prefix_threshold)
QED

Theorem remove_unused_blocks_successful_prefix_threshold:
  !N ctx fn s k gs.
    ~(?e. run_blocks N ctx fn s = Error e) /\ k <= N /\
    gas_prefix (gas_count_blocks N ctx fn s) gs =
      gas_prefix (gas_count_blocks N ctx fn s) s.vs_gas_readings ==>
    (((?e. run_blocks k ctx fn (s with vs_gas_readings := gs) = Error e) <=>
      (?e. run_blocks k ctx fn s = Error e)) /\
     (~(?e. run_blocks k ctx fn s = Error e) ==>
      lift_result
        (\a b. b = (a with vs_gas_readings := DROP (gas_count_blocks N ctx fn s) gs))
        (\a b. b = (a with vs_gas_readings := DROP (gas_count_blocks N ctx fn s) gs))
        (\a b. b = (a with vs_gas_readings := DROP (gas_count_blocks N ctx fn s) gs))
        (run_blocks N ctx fn s) (run_blocks k ctx fn (s with vs_gas_readings := gs))))
Proof
  MATCH_ACCEPT_TAC (cj 3 remove_unused_successful_prefix_threshold)
QED

Theorem remove_unused_step_successful_replay_count:
  !N ctx inst s. ~(?e. step_inst N ctx inst s = Error e) ==>
    gas_replay_at (gas_count_step N ctx inst s) (step_inst N ctx inst) s
Proof
  rpt strip_tac >> rewrite_tac[gas_replay_at_def] >> gen_tac >>
  drule remove_unused_step_successful_prefix_threshold >>
  disch_then (qspecl_then [`N`, `gas_prefix (gas_count_step N ctx inst s) s.vs_gas_readings ++ tail`] mp_tac) >>
  simp[remove_unused_gas_prefix_append] >>
  mp_tac (cj 1 gas_count_suffix) >>
  disch_then (qspecl_then [`N`, `ctx`, `inst`, `s`] mp_tac) >>
  Cases_on `step_inst N ctx inst s` >> gvs[gas_count_suffix_def] >>
  Cases_on `step_inst N ctx inst
    (s with vs_gas_readings := gas_prefix (gas_count_step N ctx inst s) s.vs_gas_readings ++ tail)` >>
  simp[lift_result_def]
QED

Theorem remove_unused_block_successful_replay_count:
  !N ctx bb s. ~(?e. exec_block N ctx bb s = Error e) ==>
    gas_replay_at (gas_count_block N ctx bb s) (exec_block N ctx bb) s
Proof
  rpt strip_tac >> rewrite_tac[gas_replay_at_def] >> gen_tac >>
  drule remove_unused_block_successful_prefix_threshold >>
  disch_then (qspecl_then [`N`, `gas_prefix (gas_count_block N ctx bb s) s.vs_gas_readings ++ tail`] mp_tac) >>
  simp[remove_unused_gas_prefix_append] >>
  mp_tac (cj 2 gas_count_suffix) >>
  disch_then (qspecl_then [`N`, `ctx`, `bb`, `s`] mp_tac) >>
  Cases_on `exec_block N ctx bb s` >> gvs[gas_count_suffix_def] >>
  Cases_on `exec_block N ctx bb
    (s with vs_gas_readings := gas_prefix (gas_count_block N ctx bb s) s.vs_gas_readings ++ tail)` >>
  simp[lift_result_def]
QED

Theorem remove_unused_blocks_successful_replay_count:
  !N ctx fn s. ~(?e. run_blocks N ctx fn s = Error e) ==>
    gas_replay_at (gas_count_blocks N ctx fn s) (run_blocks N ctx fn) s
Proof
  rpt strip_tac >> rewrite_tac[gas_replay_at_def] >> gen_tac >>
  drule remove_unused_blocks_successful_prefix_threshold >>
  disch_then (qspecl_then [`N`, `gas_prefix (gas_count_blocks N ctx fn s) s.vs_gas_readings ++ tail`] mp_tac) >>
  simp[remove_unused_gas_prefix_append] >>
  mp_tac (cj 3 gas_count_suffix) >>
  disch_then (qspecl_then [`N`, `ctx`, `fn`, `s`] mp_tac) >>
  Cases_on `run_blocks N ctx fn s` >> gvs[gas_count_suffix_def] >>
  Cases_on `run_blocks N ctx fn
    (s with vs_gas_readings := gas_prefix (gas_count_blocks N ctx fn s) s.vs_gas_readings ++ tail)` >>
  simp[lift_result_def]
QED

Theorem remove_unused_step_replay_count:
  !N n ctx inst s.
    gas_replay_at n (step_inst N ctx inst) s /\
    ~(?e. step_inst N ctx inst s = Error e) ==> n = gas_count_step N ctx inst s
Proof
  rpt strip_tac >> irule remove_unused_replay_count_unique >>
  qexistsl_tac [`step_inst N ctx inst`, `s`] >>
  metis_tac[remove_unused_step_successful_replay_count]
QED

Theorem remove_unused_block_replay_count:
  !N n ctx bb s.
    gas_replay_at n (exec_block N ctx bb) s /\
    ~(?e. exec_block N ctx bb s = Error e) ==> n = gas_count_block N ctx bb s
Proof
  rpt strip_tac >> irule remove_unused_replay_count_unique >>
  qexistsl_tac [`exec_block N ctx bb`, `s`] >>
  metis_tac[remove_unused_block_successful_replay_count]
QED

Theorem remove_unused_blocks_replay_count:
  !N n ctx fn s.
    gas_replay_at n (run_blocks N ctx fn) s /\
    ~(?e. run_blocks N ctx fn s = Error e) ==> n = gas_count_blocks N ctx fn s
Proof
  rpt strip_tac >> irule remove_unused_replay_count_unique >>
  qexistsl_tac [`run_blocks N ctx fn`, `s`] >>
  metis_tac[remove_unused_blocks_successful_replay_count]
QED

Theorem remove_unused_step_replay_threshold:
  !N n ctx inst s.
    gas_replay_at n (step_inst N ctx inst) s /\
    ~(?e. step_inst N ctx inst s = Error e) ==>
    !tail k. k <= N ==>
      ((?e. step_inst k ctx inst
          (s with vs_gas_readings := gas_prefix n s.vs_gas_readings ++ tail) = Error e) <=>
       (?e. step_inst k ctx inst s = Error e))
Proof
  rpt gen_tac >> strip_tac >>
  `n = gas_count_step N ctx inst s` by metis_tac[remove_unused_step_replay_count] >>
  rpt strip_tac >> drule remove_unused_step_successful_prefix_threshold >>
  disch_then (qspecl_then [`k`, `gas_prefix n s.vs_gas_readings ++ tail`] mp_tac) >>
  simp[remove_unused_gas_prefix_append]
QED

Theorem remove_unused_block_replay_threshold:
  !N n ctx bb s.
    gas_replay_at n (exec_block N ctx bb) s /\
    ~(?e. exec_block N ctx bb s = Error e) ==>
    !tail k. k <= N ==>
      ((?e. exec_block k ctx bb
          (s with vs_gas_readings := gas_prefix n s.vs_gas_readings ++ tail) = Error e) <=>
       (?e. exec_block k ctx bb s = Error e))
Proof
  rpt gen_tac >> strip_tac >>
  `n = gas_count_block N ctx bb s` by metis_tac[remove_unused_block_replay_count] >>
  rpt strip_tac >> drule remove_unused_block_successful_prefix_threshold >>
  disch_then (qspecl_then [`k`, `gas_prefix n s.vs_gas_readings ++ tail`] mp_tac) >>
  simp[remove_unused_gas_prefix_append]
QED

Theorem remove_unused_blocks_replay_threshold:
  !N n ctx fn s.
    gas_replay_at n (run_blocks N ctx fn) s /\
    ~(?e. run_blocks N ctx fn s = Error e) ==>
    !tail k. k <= N ==>
      ((?e. run_blocks k ctx fn
          (s with vs_gas_readings := gas_prefix n s.vs_gas_readings ++ tail) = Error e) <=>
       (?e. run_blocks k ctx fn s = Error e))
Proof
  rpt gen_tac >> strip_tac >>
  `n = gas_count_blocks N ctx fn s` by metis_tac[remove_unused_blocks_replay_count] >>
  rpt strip_tac >> drule remove_unused_blocks_successful_prefix_threshold >>
  disch_then (qspecl_then [`k`, `gas_prefix n s.vs_gas_readings ++ tail`] mp_tac) >>
  simp[remove_unused_gas_prefix_append]
QED

Theorem remove_unused_call_replay_threshold_probe[local]:
  let callee = mk_raw_function "callee"
        [<|bb_label := "c"; bb_instructions :=
           [mk_inst 0 GAS [] ["x"]; mk_inst 1 RET [Lit 0w] []]|>] in
  let caller = mk_raw_function "caller"
        [<|bb_label := "b"; bb_instructions :=
           [mk_inst 2 INVOKE [Label "callee"] [];
            mk_inst 3 GAS [] ["y"]; mk_inst 4 STOP [] []]|>] in
  let ctx = mk_venom_context [caller;callee] (SOME "caller") in
  let t = init_venom_state "b" in
  !tail k. k <= 2 ==>
    ((?e. run_blocks k ctx caller (t with vs_gas_readings :=
       gas_prefix (gas_count_blocks 2 ctx caller t) t.vs_gas_readings ++ tail) = Error e) <=>
     (?e. run_blocks k ctx caller t = Error e))
Proof
  mp_tac remove_unused_call_prefix_threshold_probe >>
  pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  qmatch_goalsub_abbrev_tac `run_blocks 2 ctx caller t` >> strip_tac >>
  `~(?e. run_blocks 2 ctx caller t = Error e)` by (strip_tac >> gvs[]) >>
  drule remove_unused_blocks_successful_replay_count >> strip_tac >>
  rpt strip_tac >> irule remove_unused_blocks_replay_threshold >>
  qexists_tac `2` >> simp[]
QED

Theorem remove_unused_retained_invoke_terminal_aligned:
  !inst V s t N ctx n
    (src_cont:num -> venom_state -> exec_result) dst_cont.
    inst.inst_opcode = INVOKE /\
    state_equiv V (s with vs_gas_readings := t.vs_gas_readings) t /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN V) /\
    gas_replay_at n (step_inst N ctx inst) t /\
    ~(?a. step_inst N ctx inst t = OK a) /\
    ~(?e. step_inst N ctx inst t = Error e) ==>
    ?p:(256 word) list.
      LENGTH (FILTER (\z. z <> 0w) p) <=
        LENGTH (FILTER (\z. z <> 0w) (gas_prefix n t.vs_gas_readings)) /\
      (!tail.
        lift_result (state_equiv V) (execution_equiv V) (execution_equiv V)
          (gas_bind_ok (step_inst N ctx inst (s with vs_gas_readings := p ++ tail))
            (src_cont N))
          (gas_bind_ok (step_inst N ctx inst
            (t with vs_gas_readings := gas_prefix n t.vs_gas_readings ++ tail))
            (dst_cont N))) /\
      (!tail k. k <= N /\
        (?e. gas_bind_ok (step_inst k ctx inst
          (t with vs_gas_readings := gas_prefix n t.vs_gas_readings ++ tail))
          (dst_cont k) = Error e) ==>
        ?e. gas_bind_ok (step_inst k ctx inst
          (s with vs_gas_readings := p ++ tail)) (src_cont k) = Error e)
Proof
  rpt strip_tac >> qexists_tac `gas_prefix n t.vs_gas_readings` >> simp[] >>
  `!tail. ~(?a. step_inst N ctx inst
      (t with vs_gas_readings := gas_prefix n t.vs_gas_readings ++ tail) = OK a)` by
    (gen_tac >> qpat_x_assum `gas_replay_at n _ t` mp_tac >>
     rewrite_tac[gas_replay_at_def] >> disch_then (qspec_then `tail` mp_tac) >>
     Cases_on `step_inst N ctx inst t` >> gvs[] >>
     Cases_on `step_inst N ctx inst
       (t with vs_gas_readings := gas_prefix n t.vs_gas_readings ++ tail)` >>
     simp[lift_result_def]) >>
  conj_tac
  >- (gen_tac >> drule_all remove_unused_retained_invoke_transport >>
      disch_then (qspecl_then [`N`, `ctx`, `gas_prefix n t.vs_gas_readings ++ tail`] mp_tac) >>
      Cases_on `step_inst N ctx inst
        (t with vs_gas_readings := gas_prefix n t.vs_gas_readings ++ tail)` >> gvs[] >>
      Cases_on `step_inst N ctx inst
        (s with vs_gas_readings := gas_prefix n t.vs_gas_readings ++ tail)` >>
      simp[lift_result_def, gas_bind_ok_def]) >>
  rpt strip_tac >>
  `~(?a. step_inst k ctx inst
      (t with vs_gas_readings := gas_prefix n t.vs_gas_readings ++ tail) = OK a)` by
    (strip_tac >> drule (cj 1 fuel_mono) >> simp[] >>
     qexists_tac `N` >> simp[] >> metis_tac[]) >>
  drule_all remove_unused_retained_invoke_transport >>
  disch_then (qspecl_then [`k`, `ctx`, `gas_prefix n t.vs_gas_readings ++ tail`] mp_tac) >>
  Cases_on `step_inst k ctx inst
    (t with vs_gas_readings := gas_prefix n t.vs_gas_readings ++ tail)` >>
  gvs[gas_bind_ok_def] >>
  Cases_on `step_inst k ctx inst
    (s with vs_gas_readings := gas_prefix n t.vs_gas_readings ++ tail)` >>
  simp[lift_result_def, gas_bind_ok_def]
QED

Theorem remove_unused_retained_invoke_continuation_aligned:
  !inst V s t u N ctx m
    (src_cont:num -> venom_state -> exec_result) dst_cont.
    inst.inst_opcode = INVOKE /\
    state_equiv V (s with vs_gas_readings := t.vs_gas_readings) t /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN V) /\
    step_inst N ctx inst t = OK u /\
    gas_replay_at m (dst_cont N) u /\ ~(?e. dst_cont N u = Error e) /\
    (!a b j.
      state_equiv V (b with vs_gas_readings := a.vs_gas_readings) a /\
      gas_replay_at j (dst_cont N) a /\ ~(?e. dst_cont N a = Error e) ==>
      ?q:(256 word) list.
        LENGTH (FILTER (\z. z <> 0w) q) <=
          LENGTH (FILTER (\z. z <> 0w) (gas_prefix j a.vs_gas_readings)) /\
        (!tail.
          (?e. e <> "out of fuel" /\
            src_cont N (b with vs_gas_readings := q ++ tail) = Error e) \/
          lift_result (state_equiv V) (execution_equiv V) (execution_equiv V)
            (src_cont N (b with vs_gas_readings := q ++ tail))
            (dst_cont N (a with vs_gas_readings :=
              gas_prefix j a.vs_gas_readings ++ tail))) /\
        (!tail k. k <= N /\
          (?e. dst_cont k (a with vs_gas_readings :=
            gas_prefix j a.vs_gas_readings ++ tail) = Error e) ==>
          ?e. src_cont k (b with vs_gas_readings := q ++ tail) = Error e)) ==>
    ?n (p:(256 word) list).
      gas_replay_at n (step_inst N ctx inst) t /\
      LENGTH (FILTER (\z. z <> 0w) p) <=
        LENGTH (FILTER (\z. z <> 0w) (gas_prefix (n + m) t.vs_gas_readings)) /\
      (!tail.
        (?e. e <> "out of fuel" /\
          gas_bind_ok (step_inst N ctx inst (s with vs_gas_readings := p ++ tail))
            (src_cont N) = Error e) \/
        lift_result (state_equiv V) (execution_equiv V) (execution_equiv V)
          (gas_bind_ok (step_inst N ctx inst (s with vs_gas_readings := p ++ tail))
            (src_cont N))
          (gas_bind_ok (step_inst N ctx inst (t with vs_gas_readings :=
             gas_prefix (n + m) t.vs_gas_readings ++ tail)) (dst_cont N))) /\
      (!tail k. k <= N /\
        (?e. gas_bind_ok (step_inst k ctx inst (t with vs_gas_readings :=
          gas_prefix (n + m) t.vs_gas_readings ++ tail)) (dst_cont k) = Error e) ==>
        ?e. gas_bind_ok (step_inst k ctx inst (s with vs_gas_readings := p ++ tail))
          (src_cont k) = Error e)
Proof
  rpt strip_tac >>
  `result_equiv V
     (step_inst N ctx inst (s with vs_gas_readings := t.vs_gas_readings))
     (step_inst N ctx inst t)` by
    (irule step_inst_result_equiv_full >> simp[venomInstTheory.is_terminator_def]) >>
  Cases_on `step_inst N ctx inst (s with vs_gas_readings := t.vs_gas_readings)` >>
  gvs[result_equiv_def] >> rename1 `state_equiv V v u` >>
  `?n. gas_replay_at n (step_inst N ctx inst)
          (s with vs_gas_readings := t.vs_gas_readings) /\
       gas_replay_at n (step_inst N ctx inst) t` by
    (irule remove_unused_invoke_pair_replay >> simp[] >>
     qexists_tac `V` >> simp[]) >>
  `u.vs_gas_readings = DROP n t.vs_gas_readings /\
   !gs. step_inst N ctx inst
     (t with vs_gas_readings := gas_prefix n t.vs_gas_readings ++ gs) =
     OK (u with vs_gas_readings := gs)` by
    (drule_all remove_unused_replay_ok >> simp[]) >>
  `!gs. step_inst N ctx inst
     (s with vs_gas_readings := gas_prefix n t.vs_gas_readings ++ gs) =
     OK (v with vs_gas_readings := gs)` by
    (qpat_assum `step_inst _ _ _ (s with vs_gas_readings := _) = OK v`
       (mp_then (Pos last) mp_tac remove_unused_replay_ok) >>
     simp[] >> disch_then drule >> simp[]) >>
  `state_equiv V (v with vs_gas_readings := u.vs_gas_readings) u` by
    (gvs[state_equiv_def, execution_equiv_def,
         stateFrameTheory.execution_frame_def, venom_state_component_equality,
         lookup_var_def]) >>
  first_x_assum (qspecl_then [`u`, `v`, `m`] mp_tac) >>
  impl_tac >- metis_tac[] >> strip_tac >>
  `gas_prefix (m + n) t.vs_gas_readings =
     gas_prefix n t.vs_gas_readings ++ gas_prefix m u.vs_gas_readings` by
    (once_rewrite_tac[ADD_COMM] >> simp[gas_prefix_add]) >>
  qexistsl [`n`, `gas_prefix n t.vs_gas_readings ++ q`] >>
  simp[FILTER_APPEND] >>
  (conj_tac >- gvs[]) >> conj_tac
  >- (pure_rewrite_tac[GSYM APPEND_ASSOC] >> asm_rewrite_tac[] >>
      gvs[gas_bind_ok_def]) >>
  suspend "smaller_fuel"
QED

Resume remove_unused_retained_invoke_continuation_aligned[smaller_fuel]:
  pure_rewrite_tac[GSYM APPEND_ASSOC] >> rpt strip_tac >>
  `!gs. ((?e. step_inst k ctx inst
       (t with vs_gas_readings := gas_prefix n t.vs_gas_readings ++ gs) = Error e) <=>
      (?e. step_inst k ctx inst t = Error e))` by
    (gen_tac >> irule remove_unused_step_replay_threshold >>
     qexists_tac `N` >> simp[]) >>
  `lift_result (state_equiv V) (execution_equiv V) (execution_equiv V)
    (step_inst k ctx inst
      (s with vs_gas_readings := gas_prefix n t.vs_gas_readings ++ (q ++ tail)))
    (step_inst k ctx inst
      (t with vs_gas_readings := gas_prefix n t.vs_gas_readings ++ (q ++ tail)))` by
    (irule remove_unused_retained_invoke_transport >> simp[]) >>
  Cases_on `?err. step_inst k ctx inst
    (s with vs_gas_readings := gas_prefix n t.vs_gas_readings ++ (q ++ tail)) = Error err`
  >- (pop_assum strip_assume_tac >> simp[gas_bind_ok_def]) >>
  `step_inst k ctx inst
    (s with vs_gas_readings := gas_prefix n t.vs_gas_readings ++ (q ++ tail)) =
      OK (v with vs_gas_readings := q ++ tail)` by
    (`step_inst N ctx inst
       (s with vs_gas_readings := gas_prefix n t.vs_gas_readings ++ (q ++ tail)) =
       step_inst k ctx inst
       (s with vs_gas_readings := gas_prefix n t.vs_gas_readings ++ (q ++ tail))` by
       (irule (cj 1 fuel_mono) >> (conj_tac >- metis_tac[]) >>
        qexists_tac `k` >> simp[]) >>
     metis_tac[]) >>
  `~(?err. step_inst k ctx inst
    (t with vs_gas_readings := gas_prefix n t.vs_gas_readings ++ (q ++ tail)) = Error err)` by
    (qpat_x_assum `!gs. _ <=> _` kall_tac >>
     qpat_x_assum `lift_result _ _ _ _ _` mp_tac >>
     asm_rewrite_tac[] >>
     Cases_on `step_inst k ctx inst
       (t with vs_gas_readings := gas_prefix n t.vs_gas_readings ++ (q ++ tail))` >>
     simp[lift_result_def] >> metis_tac[]) >>
  `~(?err. step_inst k ctx inst
    (t with vs_gas_readings := gas_prefix n t.vs_gas_readings ++
      (gas_prefix m u.vs_gas_readings ++ tail)) = Error err)` by metis_tac[] >>
  `step_inst k ctx inst
    (t with vs_gas_readings := gas_prefix n t.vs_gas_readings ++
      (gas_prefix m u.vs_gas_readings ++ tail)) =
    OK (u with vs_gas_readings := gas_prefix m u.vs_gas_readings ++ tail)` by
    (`step_inst N ctx inst
      (t with vs_gas_readings := gas_prefix n t.vs_gas_readings ++
        (gas_prefix m u.vs_gas_readings ++ tail)) =
      step_inst k ctx inst
      (t with vs_gas_readings := gas_prefix n t.vs_gas_readings ++
        (gas_prefix m u.vs_gas_readings ++ tail))` by
       (irule (cj 1 fuel_mono) >> (conj_tac >- metis_tac[]) >>
        qexists_tac `k` >> simp[]) >> metis_tac[]) >>
  gvs[gas_bind_ok_def] >> metis_tac[]
QED

Finalise remove_unused_retained_invoke_continuation_aligned

Theorem remove_unused_block_prefix_reconstruction_aligned:
  !N ctx lr V bb s t n.
    block_nop_outputs lr bb SUBSET V /\
    (!inst v. MEM inst bb.bb_instructions /\ MEM (Var v) inst.inst_operands ==>
              v NOTIN V) /\
    s.vs_inst_idx = t.vs_inst_idx /\
    state_equiv V (s with vs_gas_readings := t.vs_gas_readings) t /\
    gas_replay_at n (exec_block N ctx (remove_unused_block lr bb)) t /\
    ~(?e. exec_block N ctx (remove_unused_block lr bb) t = Error e) ==>
    ?p:(256 word) list.
      LENGTH (FILTER (\w. w <> 0w) p) <=
        LENGTH (FILTER (\w. w <> 0w) (gas_prefix n t.vs_gas_readings)) /\
      (!tail.
        (?e. e <> "out of fuel" /\
          exec_block N ctx bb (s with vs_gas_readings := p ++ tail) = Error e) \/
        lift_result (state_equiv V) (execution_equiv V) (execution_equiv V)
          (exec_block N ctx bb (s with vs_gas_readings := p ++ tail))
          (exec_block N ctx (remove_unused_block lr bb)
            (t with vs_gas_readings := gas_prefix n t.vs_gas_readings ++ tail))) /\
      (!tail k. k <= N /\
        (?e. exec_block k ctx (remove_unused_block lr bb)
          (t with vs_gas_readings := gas_prefix n t.vs_gas_readings ++ tail) = Error e) ==>
        ?e. exec_block k ctx bb (s with vs_gas_readings := p ++ tail) = Error e)
Proof
  rpt gen_tac >> map_every qid_spec_tac [`n`, `s`, `t`] >>
  measureInduct_on `LENGTH bb.bb_instructions - t.vs_inst_idx` >>
  rpt strip_tac >> Cases_on `t.vs_inst_idx < LENGTH bb.bb_instructions`
  >- suspend "in_range" >>
  qpat_x_assum `~(?e. _ = Error e)` mp_tac >>
  simp[Once exec_block_def, get_instruction_remove_unused]
QED

Resume remove_unused_block_prefix_reconstruction_aligned[in_range]:
  gvs[] >> qabbrev_tac `i = t.vs_inst_idx` >>
  qabbrev_tac `inst = EL i bb.bb_instructions` >>
  qabbrev_tac `live = live_after_at lr bb.bb_label i (LENGTH bb.bb_instructions)` >>
  `get_instruction bb i = SOME inst /\
   get_instruction (remove_unused_block lr bb) i =
     SOME (remove_unused_inst live inst)` by
    simp[venomInstTheory.get_instruction_def, get_instruction_remove_unused,
         Abbr `inst`, Abbr `live`] >>
  `MEM inst bb.bb_instructions` by simp[Abbr `inst`, EL_MEM] >>
  `!x. MEM (Var x) inst.inst_operands ==> x NOTIN V` by metis_tac[] >>
  qabbrev_tac `src_cont = \k a. exec_block k ctx bb
    (a with vs_inst_idx := SUC i)` >>
  qabbrev_tac `dst_cont = \k a. exec_block k ctx (remove_unused_block lr bb)
    (a with vs_inst_idx := SUC i)` >>
  `!a b j.
    state_equiv V (b with vs_gas_readings := a.vs_gas_readings) a /\
    gas_replay_at j (dst_cont N) a /\ ~(?e. dst_cont N a = Error e) ==>
    ?q:(256 word) list.
      LENGTH (FILTER (\w. w <> 0w) q) <=
        LENGTH (FILTER (\w. w <> 0w) (gas_prefix j a.vs_gas_readings)) /\
      (!tail.
        (?e. e <> "out of fuel" /\
          src_cont N (b with vs_gas_readings := q ++ tail) = Error e) \/
        lift_result (state_equiv V) (execution_equiv V) (execution_equiv V)
          (src_cont N (b with vs_gas_readings := q ++ tail))
          (dst_cont N (a with vs_gas_readings := gas_prefix j a.vs_gas_readings ++ tail))) /\
      (!tail k. k <= N /\
        (?e. dst_cont k (a with vs_gas_readings := gas_prefix j a.vs_gas_readings ++ tail) = Error e) ==>
        ?e. src_cont k (b with vs_gas_readings := q ++ tail) = Error e)` by
    (rpt strip_tac >>
     first_x_assum (qspec_then `SUC i` mp_tac) >>
     impl_tac >- simp[] >>
     disch_then (qspec_then `a with vs_inst_idx := SUC i` mp_tac) >> simp[] >>
     disch_then (qspecl_then [`b with vs_inst_idx := SUC i`, `j`] mp_tac) >>
     impl_tac
     >- (conj_tac >- first_assum ACCEPT_TAC >> simp[] >> conj_tac
         >- (irule execEquivProofsTheory.state_equiv_inst_idx >> simp[]) >>
         conj_tac
         >- (qpat_x_assum `gas_replay_at j (dst_cont N) a` mp_tac >>
             simp[Abbr `dst_cont`, gas_replay_at_def]) >>
         gvs[Abbr `dst_cont`]) >>
     simp[Abbr `src_cont`, Abbr `dst_cont`]) >>
  qpat_x_assum `!y. LENGTH bb.bb_instructions < _ ==> _` kall_tac >>
  Cases_on `remove_unused_inst live inst = inst`
  >- suspend "retained" >>
  suspend "deleted"
QED

Resume remove_unused_block_prefix_reconstruction_aligned[retained]:
  Cases_on `is_terminator inst.inst_opcode`
  >- suspend "terminator" >>
  `!k gs. exec_block k ctx bb (s with vs_gas_readings := gs) =
    gas_bind_ok (step_inst k ctx inst (s with vs_gas_readings := gs)) (src_cont k)` by
    (rpt gen_tac >> simp[Once exec_block_def, Abbr `i`, Abbr `src_cont`, gas_bind_ok_def]) >>
  `!k gs. exec_block k ctx (remove_unused_block lr bb) (t with vs_gas_readings := gs) =
    gas_bind_ok (step_inst k ctx inst (t with vs_gas_readings := gs)) (dst_cont k)` by
    (rpt gen_tac >> simp[Once exec_block_def, Abbr `i`, Abbr `dst_cont`, gas_bind_ok_def]) >>
  `exec_block N ctx (remove_unused_block lr bb) t =
    gas_bind_ok (step_inst N ctx inst t) (dst_cont N)` by
    (first_x_assum (qspecl_then [`N`, `t.vs_gas_readings`] mp_tac) >> simp[]) >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- suspend "invoke" >>
  Cases_on `inst.inst_opcode = GAS`
  >- suspend "gas" >>
  Cases_on `?u. step_inst_base inst t = OK u`
  >- (pop_assum strip_assume_tac >> suspend "base_ok") >>
  suspend "base_terminal"
QED

Resume remove_unused_block_prefix_reconstruction_aligned[invoke]:
  Cases_on `?u. step_inst N ctx inst t = OK u`
  >- (pop_assum strip_assume_tac >>
      `~(?e. dst_cont N u = Error e)` by gvs[gas_bind_ok_def] >>
      `gas_replay (dst_cont N) u` by
        (simp[Abbr `dst_cont`] >> irule gas_replay_preupdate >> simp[] >>
         metis_tac[cj 3 gas_replay_fuel]) >>
      fs[gas_replay_def] >> rename1 `gas_replay_at m (dst_cont N) u` >>
      drule_all (SRULE [] remove_unused_retained_invoke_continuation_aligned) >> strip_tac >>
      rename1 `gas_replay_at j (step_inst N ctx inst) t` >>
      `gas_replay_at (j + m) (\v. gas_bind_ok (step_inst N ctx inst v) (dst_cont N)) t` by
        (drule_all remove_unused_replay_bind_ok_count >> simp[]) >>
      `gas_replay_at (j + m) (exec_block N ctx (remove_unused_block lr bb)) t` by
        (irule remove_unused_replay_count_cong >>
         qexists_tac `\v. gas_bind_ok (step_inst N ctx inst v) (dst_cont N)` >> simp[]) >>
      `n = j + m` by (irule remove_unused_replay_count_unique >> metis_tac[]) >>
      gvs[] >> qexists_tac `p` >> asm_rewrite_tac[]) >>
  `~(?e. step_inst N ctx inst t = Error e)` by
    (Cases_on `step_inst N ctx inst t` >> gvs[gas_bind_ok_def]) >>
  `gas_replay (step_inst N ctx inst) t` by metis_tac[cj 2 gas_replay_fuel] >>
  fs[gas_replay_def] >> rename1 `gas_replay_at j (step_inst N ctx inst) t` >>
  `gas_replay_at j (\v. gas_bind_ok (step_inst N ctx inst v) (dst_cont N)) t` by
    (drule_all (SRULE [] remove_unused_replay_bind_terminal_count) >> simp[]) >>
  `gas_replay_at j (exec_block N ctx (remove_unused_block lr bb)) t` by
    (irule remove_unused_replay_count_cong >>
     qexists_tac `\v. gas_bind_ok (step_inst N ctx inst v) (dst_cont N)` >> simp[]) >>
  `n = j` by (irule remove_unused_replay_count_unique >> metis_tac[]) >> gvs[] >>
  drule_all (SRULE [] remove_unused_retained_invoke_terminal_aligned) >>
  disch_then (qspecl_then [`src_cont`, `dst_cont`] strip_assume_tac) >>
  qexists_tac `p` >> asm_rewrite_tac[] >> metis_tac[]
QED

Resume remove_unused_block_prefix_reconstruction_aligned[deleted]:
  `remove_unused_inst live inst = mk_nop_inst inst` by
    metis_tac[remove_unused_inst_cases] >>
  `~is_terminator inst.inst_opcode` by
    metis_tac[remove_unused_inst_nop_not_terminator] >>
  `set inst.inst_outputs SUBSET V` by
    (irule SUBSET_TRANS >> qexists_tac `block_nop_outputs lr bb` >> simp[] >>
     irule nop_outputs_in_block_nop_outputs >> qexists_tac `i` >>
     simp[Abbr `inst`, Abbr `live`]) >>
  `!k gs. exec_block k ctx (remove_unused_block lr bb) (t with vs_gas_readings := gs) =
     dst_cont k (t with vs_gas_readings := gs)` by
    (rpt gen_tac >> simp[Once exec_block_def, Abbr `dst_cont`, Abbr `i`,
      passSharedDefsTheory.mk_nop_inst_def, step_inst_def,
      step_inst_base_opcode_eqs, venomInstTheory.is_terminator_def]) >>
  `exec_block N ctx (remove_unused_block lr bb) t = dst_cont N t` by
    (first_x_assum (qspecl_then [`N`, `t.vs_gas_readings`] mp_tac) >> simp[]) >>
  `gas_replay_at n (dst_cont N) t` by
    (irule remove_unused_replay_count_cong >>
     qexists_tac `exec_block N ctx (remove_unused_block lr bb)` >> simp[]) >>
  `~(?e. dst_cont N t = Error e)` by metis_tac[] >>
  Cases_on `inst.inst_opcode = GAS`
  >- suspend "deleted_gas" >>
  `is_effect_free_op inst.inst_opcode` by metis_tac[remove_unused_inst_nop_effect_free] >>
  `inst.inst_opcode <> INVOKE` by
    (Cases_on `inst.inst_opcode = INVOKE` >> gvs[venomInstTheory.is_effect_free_op_def]) >>
  `!k gs. exec_block k ctx bb (s with vs_gas_readings := gs) =
    gas_bind_ok (step_inst_base inst (s with vs_gas_readings := gs)) (src_cont k)` by
    (rpt gen_tac >> simp[Once exec_block_def, Abbr `i`, Abbr `src_cont`,
      step_inst_def, gas_bind_ok_def]) >>
  `(?v. step_inst_base inst s = OK v) \/ (?e. step_inst_base inst s = Error e)` by
    metis_tac[effect_free_step_ok_or_error, step_inst_non_invoke]
  >- suspend "deleted_base_ok" >>
  qexists_tac `[]` >> simp[] >>
  `!gs. ?err. err <> "out of fuel" /\
    step_inst_base inst (s with vs_gas_readings := gs) = Error err` by
    (gen_tac >> drule remove_unused_base_oracle_transport >>
     disch_then (qspec_then `s` (qspec_then `gs` mp_tac)) >>
     Cases_on `step_inst_base inst (s with vs_gas_readings := gs)` >>
     gvs[lift_result_def] >>
     metis_tac[remove_unused_effect_free_not_fuel_error]) >>
  conj_tac
  >- (gen_tac >> first_x_assum (qspec_then `tail` strip_assume_tac) >>
      simp[gas_bind_ok_def]) >>
  rpt strip_tac >> first_x_assum (qspec_then `tail` strip_assume_tac) >>
  simp[gas_bind_ok_def]
QED

Resume remove_unused_block_prefix_reconstruction_aligned[deleted_base_ok]:
  drule_all venomInstProofsTheory.step_inst_base_effect_free_state_equiv >> strip_tac >>
  `state_equiv V (v with vs_gas_readings := t.vs_gas_readings) t` by
    (irule state_equiv_effect_free_compose >>
     qexistsl [`set inst.inst_outputs`, `s with vs_gas_readings := t.vs_gas_readings`] >>
     simp[] >> gvs[state_equiv_def, execution_equiv_def,
       stateFrameTheory.execution_frame_def, lookup_var_def]) >>
  first_x_assum (qspecl_then [`t`, `v`, `n`] mp_tac) >>
  impl_tac >- metis_tac[] >> strip_tac >>
  `!gs. step_inst_base inst (s with vs_gas_readings := gs) =
    OK (v with vs_gas_readings := gs)` by
    (drule_all remove_unused_base_oracle_ok >> simp[]) >>
  qexists_tac `q` >> asm_rewrite_tac[] >> simp[gas_bind_ok_def]
QED

Resume remove_unused_block_prefix_reconstruction_aligned[deleted_gas]:
  `!k gs. exec_block k ctx bb (s with vs_gas_readings := gs) =
    gas_bind_ok (exec_gas inst (s with vs_gas_readings := gs)) (src_cont k)` by
    (rpt gen_tac >> simp[Once exec_block_def, Abbr `i`, Abbr `src_cont`,
      step_inst_def, step_inst_base_opcode_eqs, gas_bind_ok_def]) >>
  Cases_on `?out. inst.inst_outputs = [out]`
  >- (pop_assum strip_assume_tac >>
      `out IN V` by gvs[SUBSET_DEF] >>
      `state_equiv V
        ((update_var out 0w s) with vs_gas_readings := t.vs_gas_readings) t` by
        (pure_once_rewrite_tac[GSYM gas_update_var] >>
         irule state_equiv_effect_free_compose >>
         qexistsl [`{out}`, `s with vs_gas_readings := t.vs_gas_readings`] >>
         simp[update_var_state_equiv]) >>
      first_x_assum (qspecl_then [`t`, `update_var out 0w s`, `n`] mp_tac) >>
      impl_tac >- metis_tac[] >> strip_tac >>
      qexists_tac `0w::q` >> asm_rewrite_tac[] >>
      simp[exec_gas_def, gas_update_var, gas_bind_ok_def]) >>
  `!gs. exec_gas inst (s with vs_gas_readings := gs) = Error "read0 requires single output"` by
    (gen_tac >> Cases_on `inst.inst_outputs` >> gvs[exec_gas_def] >>
     Cases_on `t'` >> gvs[]) >>
  qexists_tac `[]` >> simp[gas_bind_ok_def]
QED

Resume remove_unused_block_prefix_reconstruction_aligned[base_ok]:
  rename1 `step_inst_base inst t = OK u` >>
  `~(?e. dst_cont N u = Error e)` by gvs[step_inst_def, gas_bind_ok_def] >>
  `gas_replay (dst_cont N) u` by
    (simp[Abbr `dst_cont`] >> irule gas_replay_preupdate >> simp[] >>
     metis_tac[cj 3 gas_replay_fuel]) >>
  fs[gas_replay_def] >> rename1 `gas_replay_at m (dst_cont N) u` >>
  `gas_replay_at 0 (step_inst_base inst) t` by simp[gas_base_non_gas] >>
  `gas_replay_at (0 + m) (\v. gas_bind_ok (step_inst_base inst v) (dst_cont N)) t` by
    (drule_all remove_unused_replay_bind_ok_count >> simp[]) >>
  `gas_replay_at m (exec_block N ctx (remove_unused_block lr bb)) t` by
    (irule remove_unused_replay_count_cong >>
     qexists_tac `\v. gas_bind_ok (step_inst_base inst v) (dst_cont N)` >> fs[step_inst_def]) >>
  `n = m` by (irule remove_unused_replay_count_unique >> metis_tac[]) >> gvs[] >>
  `result_equiv V
     (step_inst_base inst (s with vs_gas_readings := t.vs_gas_readings))
     (step_inst_base inst t)` by
    (irule execEquivPropsTheory.step_inst_base_result_equiv >> simp[]) >>
  Cases_on `step_inst_base inst (s with vs_gas_readings := t.vs_gas_readings)` >>
  gvs[result_equiv_def] >> rename1 `state_equiv V v u` >>
  `u.vs_gas_readings = t.vs_gas_readings /\
   !gs. step_inst_base inst (t with vs_gas_readings := gs) =
        OK (u with vs_gas_readings := gs)` by
    (irule remove_unused_base_oracle_ok >> simp[]) >>
  `!gs. step_inst_base inst (s with vs_gas_readings := gs) =
        OK (v with vs_gas_readings := gs)` by
    (qspecl_then [`inst`, `s with vs_gas_readings := t.vs_gas_readings`, `v`]
       mp_tac remove_unused_base_oracle_ok >> simp[]) >>
  `state_equiv V (v with vs_gas_readings := u.vs_gas_readings) u` by
    (gvs[state_equiv_def, execution_equiv_def,
         stateFrameTheory.execution_frame_def, venom_state_component_equality, lookup_var_def]) >>
  first_x_assum (qspecl_then [`u`, `v`, `m`] mp_tac) >>
  impl_tac >- metis_tac[] >> strip_tac >>
  qexists_tac `q` >> gvs[step_inst_def, gas_bind_ok_def]
QED

Resume remove_unused_block_prefix_reconstruction_aligned[gas]:
  `?out. inst.inst_outputs = [out]` by
    (spose_not_then assume_tac >> Cases_on `inst.inst_outputs` >>
     gvs[step_inst_def, step_inst_base_opcode_eqs, exec_gas_def, gas_bind_ok_def] >>
     Cases_on `t'` >> gvs[]) >> pop_assum strip_assume_tac >>
  `?u. exec_gas inst t = OK u` by
    (Cases_on `t.vs_gas_readings` >> simp[exec_gas_def]) >> pop_assum strip_assume_tac >>
  `~(?e. dst_cont N u = Error e)` by
    gvs[step_inst_def, step_inst_base_opcode_eqs, gas_bind_ok_def] >>
  `gas_replay (dst_cont N) u` by
    (simp[Abbr `dst_cont`] >> irule gas_replay_preupdate >> simp[] >>
     metis_tac[cj 3 gas_replay_fuel]) >>
  fs[gas_replay_def] >> rename1 `gas_replay_at m (dst_cont N) u` >>
  `gas_replay_at 1 (exec_gas inst) t` by simp[gas_exec_gas] >>
  `gas_replay_at (1 + m) (\v. gas_bind_ok (exec_gas inst v) (dst_cont N)) t` by
    (drule_all remove_unused_replay_bind_ok_count >> simp[]) >>
  `gas_replay_at (SUC m) (exec_block N ctx (remove_unused_block lr bb)) t` by
    (irule remove_unused_replay_count_cong >>
     qexists_tac `\v. gas_bind_ok (exec_gas inst v) (dst_cont N)` >>
     fs[step_inst_def, step_inst_base_opcode_eqs, ADD1]) >>
  `n = SUC m` by (irule remove_unused_replay_count_unique >> metis_tac[]) >> gvs[] >>
  qabbrev_tac `w = case t.vs_gas_readings of [] => 0w | h::rest => h` >>
  `u = update_var out w (t with vs_gas_readings := u.vs_gas_readings)` by
    (Cases_on `t.vs_gas_readings` >>
     gvs[exec_gas_def, Abbr `w`, gas_update_var, venom_state_component_equality]) >>
  `gas_prefix (SUC m) t.vs_gas_readings = w :: gas_prefix m u.vs_gas_readings` by
    (Cases_on `t.vs_gas_readings` >> gvs[exec_gas_def, gas_prefix_suc, Abbr `w`]) >>
  `state_equiv V ((update_var out w s) with vs_gas_readings := u.vs_gas_readings) u` by
    (qpat_assum `u = update_var _ _ _` (fn th => once_rewrite_tac[th]) >>
     pure_once_rewrite_tac[GSYM gas_update_var] >>
     irule stateEquivProofsTheory.update_var_preserves >>
     qpat_x_assum `state_equiv V _ t` mp_tac >>
     simp[state_equiv_def, execution_equiv_def,
          stateFrameTheory.execution_frame_def, venom_state_component_equality, lookup_var_def]) >>
  first_x_assum (qspecl_then [`u`, `update_var out w s`, `m`] mp_tac) >>
  impl_tac >- metis_tac[] >> strip_tac >>
  qexists_tac `w::q` >> (conj_tac >- (Cases_on `w = 0w` >> simp[])) >>
  `!gs. (u with vs_gas_readings := gs) =
    (update_var out w t with vs_gas_readings := gs)` by
    (gen_tac >> qpat_assum `u = update_var _ _ _` (fn th => once_rewrite_tac[th]) >>
     simp[gas_update_var]) >>
  qpat_x_assum `!tail. (?e. _) \/ _` mp_tac >>
  qpat_x_assum `!tail k. k <= N /\ _ ==> _` mp_tac >>
  simp[exec_gas_def, gas_update_var, step_inst_def, step_inst_base_opcode_eqs, gas_bind_ok_def]
QED

Resume remove_unused_block_prefix_reconstruction_aligned[base_terminal]:
  `gas_replay_at 0 (step_inst_base inst) t` by simp[gas_base_non_gas] >>
  `gas_replay_at 0 (\v. gas_bind_ok (step_inst_base inst v) (dst_cont N)) t` by
    (drule_all remove_unused_replay_bind_terminal_count >> simp[]) >>
  `gas_replay_at 0 (exec_block N ctx (remove_unused_block lr bb)) t` by
    (irule remove_unused_replay_count_cong >>
     qexists_tac `\v. gas_bind_ok (step_inst_base inst v) (dst_cont N)` >> fs[step_inst_def]) >>
  `n = 0` by (irule remove_unused_replay_count_unique >> metis_tac[]) >> gvs[] >>
  `!gs. ~(?a. step_inst_base inst (t with vs_gas_readings := gs) = OK a)` by
    (gen_tac >> qpat_x_assum `gas_replay_at 0 (step_inst_base inst) t` mp_tac >>
     rewrite_tac[gas_replay_at_def] >> disch_then (qspec_then `gs` mp_tac) >>
     Cases_on `step_inst_base inst t` >> gvs[] >>
     Cases_on `step_inst_base inst (t with vs_gas_readings := gs)` >>
     simp[lift_result_def]) >>
  `!k gs. lift_result (state_equiv V) (execution_equiv V) (execution_equiv V)
    (exec_block k ctx bb (s with vs_gas_readings := gs))
    (exec_block k ctx (remove_unused_block lr bb) (t with vs_gas_readings := gs))` by
    (rpt gen_tac >> asm_rewrite_tac[] >>
     drule_all remove_unused_retained_base_transport >>
     disch_then (qspec_then `gs` mp_tac) >>
     Cases_on `step_inst_base inst (t with vs_gas_readings := gs)` >> gvs[] >>
     Cases_on `step_inst_base inst (s with vs_gas_readings := gs)` >>
     simp[lift_result_def, gas_bind_ok_def, step_inst_def]) >>
  qexists_tac `[]` >> simp[] >> conj_tac
  >- metis_tac[] >> rpt strip_tac >>
  qpat_x_assum `!k gs. lift_result _ _ _ _ _`
    (qspecl_then [`k`, `tail`] mp_tac) >>
  asm_rewrite_tac[] >>
  Cases_on `gas_bind_ok (step_inst k ctx inst (s with vs_gas_readings := tail)) (src_cont k)` >>
  simp[lift_result_def]
QED

Resume remove_unused_block_prefix_reconstruction_aligned[terminator]:
  `inst.inst_opcode <> GAS /\ inst.inst_opcode <> INVOKE` by
    (Cases_on `inst.inst_opcode` >> gvs[venomInstTheory.is_terminator_def]) >>
  `!k gs. exec_block k ctx bb (s with vs_gas_readings := gs) =
    gas_bind_ok (step_inst_base inst (s with vs_gas_readings := gs))
      (\a. if a.vs_halted then Halt a else OK a)` by
    (rpt gen_tac >> simp[Once exec_block_def, Abbr `i`, step_inst_def, gas_bind_ok_def] >>
     Cases_on `step_inst_base inst (s with vs_gas_readings := gs)` >> simp[]) >>
  `!k gs. exec_block k ctx (remove_unused_block lr bb) (t with vs_gas_readings := gs) =
    gas_bind_ok (step_inst_base inst (t with vs_gas_readings := gs))
      (\a. if a.vs_halted then Halt a else OK a)` by
    (rpt gen_tac >> simp[Once exec_block_def, Abbr `i`, step_inst_def, gas_bind_ok_def] >>
     Cases_on `step_inst_base inst (t with vs_gas_readings := gs)` >> simp[]) >>
  `exec_block N ctx (remove_unused_block lr bb) t =
    gas_bind_ok (step_inst_base inst t) (\a. if a.vs_halted then Halt a else OK a)` by
    (first_x_assum (qspecl_then [`N`, `t.vs_gas_readings`] mp_tac) >> simp[]) >>
  `gas_replay_at 0 (step_inst_base inst) t` by simp[gas_base_non_gas] >>
  `gas_replay_at 0 (\v. gas_bind_ok (step_inst_base inst v)
      (\a. if a.vs_halted then Halt a else OK a)) t` by
    (qpat_x_assum `gas_replay_at 0 (step_inst_base inst) t` mp_tac >>
     simp[gas_replay_at_def] >> strip_tac >> gen_tac >>
     first_x_assum (qspec_then `tail` mp_tac) >>
     Cases_on `step_inst_base inst t` >>
     Cases_on `step_inst_base inst (t with vs_gas_readings := tail)` >>
     simp[lift_result_def, gas_bind_ok_def] >> rpt strip_tac >> gvs[] >>
     rpt IF_CASES_TAC >> simp[lift_result_def]) >>
  `gas_replay_at 0 (exec_block N ctx (remove_unused_block lr bb)) t` by
    (irule remove_unused_replay_count_cong >>
     qexists_tac `\v. gas_bind_ok (step_inst_base inst v)
       (\a. if a.vs_halted then Halt a else OK a)` >> simp[]) >>
  `n = 0` by (irule remove_unused_replay_count_unique >> metis_tac[]) >> gvs[] >>
  suspend "terminator_finish"
QED

Resume remove_unused_block_prefix_reconstruction_aligned[terminator_finish]:
  `!gs. lift_result (state_equiv V) (execution_equiv V) (execution_equiv V)
    (exec_block N ctx bb (s with vs_gas_readings := gs))
    (exec_block N ctx (remove_unused_block lr bb) (t with vs_gas_readings := gs))` by
    (gen_tac >> asm_rewrite_tac[] >>
     drule_all remove_unused_retained_base_transport >>
     disch_then (qspec_then `gs` mp_tac) >>
     Cases_on `step_inst_base inst (s with vs_gas_readings := gs)` >>
     Cases_on `step_inst_base inst (t with vs_gas_readings := gs)` >>
     simp[lift_result_def, gas_bind_ok_def] >> strip_tac >>
     `v.vs_halted = v'.vs_halted` by
       gvs[state_equiv_def, execution_equiv_def, stateFrameTheory.execution_frame_def] >>
     Cases_on `v'.vs_halted` >> simp[lift_result_def] >>
     metis_tac[stateEquivPropsTheory.state_equiv_implies_execution_equiv]) >>
  qexists_tac `[]` >> simp[] >> conj_tac
  >- metis_tac[] >> rpt strip_tac >>
  qpat_x_assum `!gs. lift_result _ _ _ _ _` (qspec_then `tail` mp_tac) >>
  asm_rewrite_tac[] >>
  Cases_on `step_inst_base inst (s with vs_gas_readings := tail)` >>
  simp[lift_result_def, gas_bind_ok_def] >>
  IF_CASES_TAC >> simp[lift_result_def]
QED

Finalise remove_unused_block_prefix_reconstruction_aligned

(* The original fixed-fuel interface is now a projection of the aligned proof. *)
Theorem remove_unused_block_prefix_reconstruction:
  !fuel ctx lr V bb s t n.
    block_nop_outputs lr bb SUBSET V /\
    (!inst v. MEM inst bb.bb_instructions /\ MEM (Var v) inst.inst_operands ==>
              v NOTIN V) /\
    s.vs_inst_idx = t.vs_inst_idx /\
    state_equiv V (s with vs_gas_readings := t.vs_gas_readings) t /\
    gas_replay_at n (exec_block fuel ctx (remove_unused_block lr bb)) t /\
    ~(?e. exec_block fuel ctx (remove_unused_block lr bb) t = Error e) ==>
    ?p:(256 word) list.
      LENGTH (FILTER (\w. w <> 0w) p) <=
        LENGTH (FILTER (\w. w <> 0w) (gas_prefix n t.vs_gas_readings)) /\
      !tail.
        (?e. e <> "out of fuel" /\
          exec_block fuel ctx bb (s with vs_gas_readings := p ++ tail) = Error e) \/
        lift_result (state_equiv V) (execution_equiv V) (execution_equiv V)
          (exec_block fuel ctx bb (s with vs_gas_readings := p ++ tail))
          (exec_block fuel ctx (remove_unused_block lr bb)
            (t with vs_gas_readings := gas_prefix n t.vs_gas_readings ++ tail))
Proof
  rpt strip_tac >> drule_all remove_unused_block_prefix_reconstruction_aligned >>
  metis_tac[]
QED

Theorem remove_unused_replay_count_result_equiv:
  !f g s t n m.
    gas_replay_at n f s /\ gas_replay_at m g t /\
    s.vs_gas_readings = t.vs_gas_readings /\
    ~(?e. g t = Error e) /\
    (!gs. result_equiv {} (f (s with vs_gas_readings := gs))
                         (g (t with vs_gas_readings := gs))) ==>
    n = m
Proof
  rpt strip_tac >>
  `gas_prefix (n + m) s.vs_gas_readings =
   gas_prefix n s.vs_gas_readings ++
   gas_prefix m (DROP n s.vs_gas_readings)` by simp[gas_prefix_add] >>
  `gas_prefix (n + m) t.vs_gas_readings =
   gas_prefix m t.vs_gas_readings ++
   gas_prefix n (DROP m t.vs_gas_readings)` by
    metis_tac[gas_prefix_add, ADD_COMM] >>
  qpat_x_assum `!gs. result_equiv {} _ _`
    (qspec_then `gas_prefix (n+m) t.vs_gas_readings` mp_tac) >>
  qpat_x_assum `gas_replay_at n f s` mp_tac >>
  rewrite_tac[gas_replay_at_def] >>
  disch_then (qspec_then `gas_prefix m (DROP n s.vs_gas_readings)` mp_tac) >>
  qpat_x_assum `gas_replay_at m g t` mp_tac >>
  rewrite_tac[gas_replay_at_def] >>
  disch_then (qspec_then `gas_prefix n (DROP m t.vs_gas_readings)` mp_tac) >>
  asm_rewrite_tac[] >>
  Cases_on `g t` >> gvs[lift_result_def] >>
  Cases_on `f s` >>
  Cases_on `g (t with vs_gas_readings := gas_prefix (n+m) t.vs_gas_readings)` >>
  Cases_on `f (s with vs_gas_readings := gas_prefix (n+m) t.vs_gas_readings)` >>
  gvs[lift_result_def, result_equiv_def, state_equiv_def,
      execution_equiv_def] >>
  rpt strip_tac >>
  qpat_x_assum `gas_prefix m _ = gas_prefix n _`
    (mp_tac o AP_TERM ``LENGTH : bytes32 list -> num``) >>
  simp[remove_unused_gas_prefix_length]
QED

Theorem remove_unused_clear_nops_replay_count:
  !N ctx bb s n.
    gas_replay_at n (exec_block N ctx (clear_nops_block bb))
      (s with vs_inst_idx := LENGTH (FILTER (\inst. inst.inst_opcode <> NOP)
        (TAKE s.vs_inst_idx bb.bb_instructions))) /\
    ~(?e. exec_block N ctx (clear_nops_block bb)
      (s with vs_inst_idx := LENGTH (FILTER (\inst. inst.inst_opcode <> NOP)
        (TAKE s.vs_inst_idx bb.bb_instructions))) = Error e) ==>
    gas_replay_at n (exec_block N ctx bb) s
Proof
  rpt strip_tac >>
  `?m. gas_replay_at m (exec_block N ctx bb) s` by
    metis_tac[gas_replay_fuel, gas_replay_def] >>
  `m = n` suffices_by metis_tac[] >>
  irule remove_unused_replay_count_result_equiv >>
  qexistsl [`exec_block N ctx bb`, `exec_block N ctx (clear_nops_block bb)`,
    `s`, `s with vs_inst_idx := LENGTH (FILTER (\inst. inst.inst_opcode <> NOP)
        (TAKE s.vs_inst_idx bb.bb_instructions))`] >>
  simp[] >> reverse conj_tac >- gvs[] >> gen_tac >>
  qspec_then `s with vs_gas_readings := gs` mp_tac
    (passSharedPropsTheory.clear_nops_block_gen |> Q.SPECL [`N`, `ctx`, `bb`]) >>
  simp[]
QED

Theorem remove_unused_phi_error:
  !insts s e. eval_phis s insts = Error e ==> e = "phi evaluation failed"
Proof
  Induct_on `insts` >- simp[Once eval_phis_def] >>
  rpt gen_tac >>
  first_x_assum (qspecl_then [`s`, `e`] mp_tac) >>
  pure_once_rewrite_tac[eval_phis_def] >>
  Cases_on `h.inst_opcode = PHI` >> simp[] >>
  Cases_on `eval_one_phi s h` >> simp[] >>
  rename1 `SOME pair` >> PairCases_on `pair` >> simp[] >>
  Cases_on `eval_phis s insts` >> simp[]
QED

Theorem remove_unused_phi_replay_ok:
  eval_phis s insts = OK u ==>
  u.vs_gas_readings = s.vs_gas_readings /\
  !gs. eval_phis (s with vs_gas_readings := gs) insts =
       OK (u with vs_gas_readings := gs)
Proof
  strip_tac >> qspecl_then [`insts`, `s`] mp_tac gas_eval_phis >>
  simp[gas_replay_at_def] >> strip_tac >> conj_tac
  >- (first_x_assum (qspec_then `[]` mp_tac) >>
      Cases_on `eval_phis (s with vs_gas_readings := []) insts` >>
      simp[lift_result_def]) >>
  gen_tac >> first_x_assum (qspec_then `gs` mp_tac) >>
  Cases_on `eval_phis (s with vs_gas_readings := gs) insts` >>
  simp[lift_result_def]
QED

Theorem remove_unused_phi_replay_error:
  eval_phis s insts = Error e ==>
  eval_phis (s with vs_gas_readings := gs) insts = Error e /\
  e <> "out of fuel"
Proof
  strip_tac >> drule remove_unused_phi_error >> strip_tac >>
  qspecl_then [`insts`, `s`] mp_tac gas_eval_phis >>
  simp[gas_replay_at_def] >> disch_then (qspec_then `gs` mp_tac) >>
  Cases_on `eval_phis (s with vs_gas_readings := gs) insts` >>
  simp[lift_result_def] >> metis_tac[remove_unused_phi_error]
QED

Theorem remove_unused_run_block_replay_threshold:
  !N n ctx bb s.
    gas_replay_at n (run_block N ctx bb) s /\
    ~(?e. run_block N ctx bb s = Error e) ==>
    !tail k. k <= N ==>
      ((?e. run_block k ctx bb
          (s with vs_gas_readings := gas_prefix n s.vs_gas_readings ++ tail) = Error e) <=>
       (?e. run_block k ctx bb s = Error e))
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`s`, `bb.bb_instructions`] strip_assume_tac eval_phis_ok_or_error_defs
  >- (rename1 `eval_phis s bb.bb_instructions = OK sp` >>
      drule remove_unused_phi_replay_ok >> strip_tac >>
      qabbrev_tac `u = sp with vs_inst_idx := phi_prefix_length bb.bb_instructions` >>
      `!k gs. run_block k ctx bb (s with vs_gas_readings := gs) =
        exec_block k ctx bb (u with vs_gas_readings := gs)` by
        simp[run_block_def, Abbr `u`] >>
      `!k. run_block k ctx bb s = exec_block k ctx bb u` by
        simp[run_block_def, Abbr `u`] >>
      `u.vs_gas_readings = s.vs_gas_readings` by simp[Abbr `u`] >>
      `gas_replay_at n (exec_block N ctx bb) u` by
        gvs[gas_replay_at_def] >>
      `~(?e. exec_block N ctx bb u = Error e)` by metis_tac[] >>
      rpt strip_tac >>
      drule_all remove_unused_block_replay_threshold >>
      disch_then (qspec_then `tail` mp_tac) >> simp[]) >>
  gvs[run_block_def]
QED

Theorem remove_unused_run_block_prefix_reconstruction_aligned:
  !N ctx lr V bb s t n.
    (!i j. i < j /\ j < LENGTH bb.bb_instructions /\
      (EL j bb.bb_instructions).inst_opcode = PHI ==>
      (EL i bb.bb_instructions).inst_opcode = PHI) /\
    block_nop_outputs lr bb SUBSET V /\
    (!inst v. MEM inst bb.bb_instructions /\ MEM (Var v) inst.inst_operands ==>
              v NOTIN V) /\
    s.vs_inst_idx = 0 /\ t.vs_inst_idx = 0 /\
    state_equiv V (s with vs_gas_readings := t.vs_gas_readings) t /\
    gas_replay_at n (run_block N ctx (clear_nops_block (remove_unused_block lr bb))) t /\
    ~(?e. run_block N ctx (clear_nops_block (remove_unused_block lr bb)) t = Error e) ==>
    ?p:(256 word) list.
      LENGTH (FILTER (\w. w <> 0w) p) <=
        LENGTH (FILTER (\w. w <> 0w) (gas_prefix n t.vs_gas_readings)) /\
      (!tail.
        (?e. e <> "out of fuel" /\
          run_block N ctx bb (s with vs_gas_readings := p ++ tail) = Error e) \/
        lift_result (state_equiv V) (execution_equiv V) (execution_equiv V)
          (run_block N ctx bb (s with vs_gas_readings := p ++ tail))
          (run_block N ctx (clear_nops_block (remove_unused_block lr bb))
            (t with vs_gas_readings := gas_prefix n t.vs_gas_readings ++ tail))) /\
      (!tail k. k <= N /\
        (?e. run_block k ctx (clear_nops_block (remove_unused_block lr bb))
          (t with vs_gas_readings := gas_prefix n t.vs_gas_readings ++ tail) = Error e) ==>
        ?e. run_block k ctx bb (s with vs_gas_readings := p ++ tail) = Error e)
Proof
  rpt strip_tac >>
  qspecl_then [`s`, `bb.bb_instructions`] strip_assume_tac eval_phis_ok_or_error_defs
  >- suspend "phi_success" >>
  qexists_tac `[]` >> simp[] >>
  `!gs. eval_phis (s with vs_gas_readings := gs) bb.bb_instructions = Error e /\
        e <> "out of fuel"` by metis_tac[remove_unused_phi_replay_error] >>
  simp[run_block_def] >> metis_tac[]
QED

Resume remove_unused_run_block_prefix_reconstruction_aligned[phi_success]:
  rename1 `eval_phis s bb.bb_instructions = OK sp` >>
  drule remove_unused_phi_replay_ok >> strip_tac >>
  `?tp. eval_phis t
      (FILTER (\inst. inst.inst_opcode <> NOP)
        (MAPi (\idx inst. remove_unused_inst
          (live_after_at lr bb.bb_label idx (LENGTH bb.bb_instructions)) inst)
          bb.bb_instructions)) = OK tp /\
      state_equiv V (sp with vs_gas_readings := t.vs_gas_readings) tp` by
    (ho_match_mp_tac eval_phis_remove_unused >>
     qexists_tac `s with vs_gas_readings := t.vs_gas_readings` >>
     simp[] >> conj_tac >- metis_tac[] >> conj_tac
     >- (rpt strip_tac >>
         `set (EL idx bb.bb_instructions).inst_outputs SUBSET block_nop_outputs lr bb` by
           (irule nop_outputs_in_block_nop_outputs >> qexists_tac `idx` >> simp[]) >>
         metis_tac[SUBSET_TRANS]) >>
     metis_tac[]) >>
  qabbrev_tac `mb = remove_unused_block lr bb` >>
  qabbrev_tac `cb = clear_nops_block mb` >>
  `eval_phis t cb.bb_instructions = OK tp` by
    gvs[Abbr `cb`, Abbr `mb`, passSharedDefsTheory.clear_nops_block_def,
        removeUnusedDefsTheory.remove_unused_block_def] >>
  drule remove_unused_phi_replay_ok >> strip_tac >>
  qabbrev_tac `i = phi_prefix_length bb.bb_instructions` >>
  qabbrev_tac `j = phi_prefix_length cb.bb_instructions` >>
  `j = LENGTH (FILTER (\inst. inst.inst_opcode <> NOP)
        (TAKE i mb.bb_instructions))` by
    (simp[Abbr `i`, Abbr `j`, Abbr `cb`, Abbr `mb`,
       passSharedDefsTheory.clear_nops_block_def, removeUnusedDefsTheory.remove_unused_block_def] >>
     ho_match_mp_tac phi_prefix_length_remove_unused_clear >> metis_tac[]) >>
  `!k gs. run_block k ctx bb (s with vs_gas_readings := gs) =
     exec_block k ctx bb ((sp with vs_inst_idx := i) with vs_gas_readings := gs)` by
    simp[run_block_def, Abbr `i`] >>
  `!k gs. run_block k ctx cb (t with vs_gas_readings := gs) =
     exec_block k ctx cb ((tp with vs_inst_idx := j) with vs_gas_readings := gs)` by
    simp[run_block_def, Abbr `j`] >>
  suspend "entry_replay"
QED

Resume remove_unused_run_block_prefix_reconstruction_aligned[entry_replay]:
  qpat_x_assum `!a b. a < b /\ _ ==> _` kall_tac >>
  qpat_x_assum `state_equiv V (s with vs_gas_readings := _) t` kall_tac >>
  qpat_x_assum `eval_phis s _ = OK sp` kall_tac >>
  qpat_x_assum `!gs. eval_phis (s with vs_gas_readings := gs) _ = _` kall_tac >>
  qpat_x_assum `eval_phis t (FILTER _ _) = _` kall_tac >>
  `gas_replay_at n (exec_block N ctx cb) (tp with vs_inst_idx := j)` by
    (qpat_x_assum `gas_replay_at n _ t` mp_tac >>
     simp[gas_replay_at_def, run_block_def, Abbr `j`]) >>
  `~(?e. exec_block N ctx cb (tp with vs_inst_idx := j) = Error e)` by
    gvs[run_block_def, Abbr `j`] >>
  `gas_replay_at n (exec_block N ctx mb) (tp with vs_inst_idx := i)` by
    (irule remove_unused_clear_nops_replay_count >>
     gvs[Abbr `cb`]) >>
  `!k gs. result_equiv {}
     (exec_block k ctx mb ((tp with vs_inst_idx := i) with vs_gas_readings := gs))
     (exec_block k ctx cb ((tp with vs_inst_idx := j) with vs_gas_readings := gs))` by
    (rpt gen_tac >>
     qspecl_then [`k`, `ctx`, `mb`,
       `(tp with vs_inst_idx := i) with vs_gas_readings := gs`] mp_tac
       passSharedPropsTheory.clear_nops_block_gen >>
     simp[Abbr `cb`]) >>
  `~(?e. exec_block N ctx mb (tp with vs_inst_idx := i) = Error e)` by
    (first_x_assum (qspecl_then [`N`, `tp.vs_gas_readings`] mp_tac) >>
     simp[] >> Cases_on `exec_block N ctx mb (tp with vs_inst_idx := i)` >>
     Cases_on `exec_block N ctx cb (tp with vs_inst_idx := j)` >>
     gvs[result_equiv_def, lift_result_def]) >>
  `state_equiv V
     ((sp with vs_inst_idx := i) with vs_gas_readings :=
       (tp with vs_inst_idx := i).vs_gas_readings)
     (tp with vs_inst_idx := i)` by
    (simp[] >> irule execEquivProofsTheory.state_equiv_inst_idx >> simp[]) >>
  suspend "entry_compose"
QED

Resume remove_unused_run_block_prefix_reconstruction_aligned[entry_compose]:
  qpat_x_assum `gas_replay_at n (exec_block N ctx mb) _` mp_tac >>
  qpat_x_assum `~(?e. exec_block N ctx mb _ = Error e)` mp_tac >>
  qpat_x_assum `state_equiv V ((_ with vs_inst_idx := i) with vs_gas_readings := _) _` mp_tac >>
  simp[Abbr `mb`] >> rpt strip_tac >>
  drule_at (Pat `gas_replay_at _ _ _`)
    remove_unused_block_prefix_reconstruction_aligned >>
  disch_then (qspecl_then [`V`, `sp with vs_inst_idx := i`] mp_tac) >>
  simp[] >> (impl_tac >- metis_tac[]) >> strip_tac >>
  qexists_tac `p` >> simp[] >>
  rpt (qpat_x_assum `gas_replay_at _ _ _` kall_tac) >>
  rpt (qpat_x_assum `state_equiv _ _ _` kall_tac) >>
  rpt (qpat_x_assum `eval_phis _ _ = _` kall_tac) >>
  rpt (qpat_x_assum `!gs. eval_phis _ _ = _` kall_tac) >>
  rpt (qpat_x_assum `~(?e. _ = Error e)` kall_tac) >>
  qpat_x_assum `block_nop_outputs _ _ SUBSET _` kall_tac >>
  qpat_x_assum `!inst v. MEM inst _ /\ _ ==> _` kall_tac >>
  conj_tac
  >- (gen_tac >> qpat_x_assum `!tail. (?e. _ /\ _) \/ _`
        (qspec_then `tail` mp_tac) >>
      strip_tac >- metis_tac[] >> disj2_tac >>
      irule lift_result_compose_result_equiv >>
      qexists_tac `exec_block N ctx (remove_unused_block lr bb)
        ((tp with vs_inst_idx := i) with vs_gas_readings :=
          gas_prefix n t.vs_gas_readings ++ tail)` >>
      conj_tac
      >- (qpat_x_assum `!k gs. result_equiv {} _ _`
            (qspecl_then [`N`, `gas_prefix n t.vs_gas_readings ++ tail`] mp_tac) >>
          simp[]) >> simp[]) >>
  rpt strip_tac >>
  qpat_x_assum `!tail k. _` (qspecl_then [`tail`, `k`] mp_tac) >>
  simp[] >> (impl_tac >- (
    qpat_x_assum `!k gs. result_equiv {} _ _`
      (qspecl_then [`k`, `gas_prefix n t.vs_gas_readings ++ tail`] mp_tac) >>
    simp[] >>
    Cases_on `exec_block k ctx (remove_unused_block lr bb)
      (tp with <|vs_inst_idx := i;
        vs_gas_readings := gas_prefix n t.vs_gas_readings ++ tail|>)` >>
    simp[result_equiv_def, lift_result_def])) >> simp[]
QED

Finalise remove_unused_run_block_prefix_reconstruction_aligned

(* Continuation reconstruction can use a canonical representative of a
   state_equiv class: dead-variable differences cannot affect the runner. *)
Theorem remove_unused_runner_state_transport:
  !V fn.
    (!bb inst v. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
      MEM (Var v) inst.inst_operands ==> v NOTIN V) ==>
    !fuel ctx s t. state_equiv V s t ==>
      lift_result (state_equiv V) (execution_equiv V) (execution_equiv V)
        (run_blocks fuel ctx fn s) (run_blocks fuel ctx fn t)
Proof
  rpt gen_tac >> strip_tac >>
  qspecl_then [`state_equiv V`, `execution_equiv V`, `fn`] mp_tac
    execEquivParamPropsTheory.exec_block_preserves_R >>
  (impl_tac >- (
    simp[execEquivParamPropsTheory.state_equiv_execution_equiv_valid_state_rel] >>
    rpt conj_tac
    >- metis_tac[stateEquivPropsTheory.state_equiv_trans]
    >- metis_tac[stateEquivPropsTheory.execution_equiv_trans] >>
    rpt strip_tac >>
    `x NOTIN V` by metis_tac[] >>
    gvs[state_equiv_def, execution_equiv_def])) >>
  metis_tac[]
QED

Theorem remove_unused_permanent_continuation_error[local]:
  !N ctx fn bb s u.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    run_block N ctx bb s = OK u /\ ~u.vs_halted /\
    (!fuel. ?e. run_blocks fuel ctx fn u = Error e) ==>
    !fuel. ?e. run_blocks fuel ctx fn s = Error e
Proof
  rpt gen_tac >> strip_tac >> Cases
  >- simp[Once run_blocks_def] >> rename1 `SUC m` >>
  pure_once_rewrite_tac[run_blocks_unfold] >> simp[] >>
  Cases_on `N <= m`
  >- (`run_block m ctx bb s = OK u` by
        (irule venomExecPropsTheory.run_block_fuel_mono_OK >>
         qexists_tac `N` >> simp[]) >> simp[]) >>
  `m <= N` by decide_tac >>
  Cases_on `run_block m ctx bb s` >> simp[] >>
  `run_block N ctx bb s = run_block m ctx bb s` by
    (irule venomExecPropsTheory.run_block_fuel_mono >> simp[] >>
     qexists_tac `m` >> simp[]) >> gvs[]
QED

(* Runner reconstruction is stated over paired lookups, so that the fuel
   induction does not unfold either the liveness analysis or block mapping. *)
local
fun runner_terminal_tac g = (
  qpat_x_assum `!ctx lr V fn fn' s t n. _` kall_tac >>
  qpat_x_assum `!bb. MEM bb _ ==> _` kall_tac >>
  qpat_x_assum `!bb inst v. MEM bb fn.fn_blocks /\ _ ==> _` kall_tac >>
  `!gs. run_blocks (SUC N) ctx fn' (t with vs_gas_readings := gs) =
    gas_bind_ok (run_block N ctx cb (t with vs_gas_readings := gs))
      (\u. if u.vs_halted then Halt u else run_blocks N ctx fn' u)` by
    (gen_tac >> irule gas_run_blocks_layer >> simp[]) >>
  `run_blocks (SUC N) ctx fn' t =
    gas_bind_ok (run_block N ctx cb t)
      (\u. if u.vs_halted then Halt u else run_blocks N ctx fn' u)` by
    (irule gas_run_blocks_layer >> simp[]) >>
  `gas_replay_at nb (\v. gas_bind_ok (run_block N ctx cb v)
      (\u. if u.vs_halted then Halt u else run_blocks N ctx fn' u)) t` by
    (irule remove_unused_replay_bind_terminal_count >> simp[]) >>
  `gas_replay_at nb (run_blocks (SUC N) ctx fn') t` by
    (qpat_x_assum `gas_replay_at nb (\v. _) t` mp_tac >>
     simp[gas_replay_at_def]) >>
  `n = nb` by metis_tac[remove_unused_replay_count_unique] >>
  gvs[] >> qexists_tac `p` >> simp[] >>
  conj_tac >- terminal_high_tac >>
  terminal_low_tac) g

and terminal_high_tac g = (gen_tac >>
  qpat_x_assum `!tail. (?e. _ /\ _) \/ _` (qspec_then `tail` mp_tac) >>
  strip_tac
  >- (disj1_tac >> irule remove_unused_run_blocks_error_all_fuel >>
      qexistsl_tac [`e`, `SUC N`] >>
      simp[Once run_blocks_unfold]) >>
  disj2_tac >>
  qpat_x_assum `gas_replay_at n (run_block N ctx cb) t` mp_tac >>
  simp[gas_replay_at_def] >> disch_then (qspec_then `tail` mp_tac) >>
  Cases_on `run_block N ctx cb
    (t with vs_gas_readings := gas_prefix n t.vs_gas_readings ++ tail)` >>
  simp[lift_result_def] >> strip_tac >>
  Cases_on `run_block N ctx bb (s with vs_gas_readings := p ++ tail)` >>
  gvs[lift_result_def] >>
  pure_once_rewrite_tac[run_blocks_unfold] >>
  simp[gas_bind_ok_def, lift_result_def]) g

and terminal_low_tac g = (rpt gen_tac >> strip_tac >>
  Cases_on `k`
  >- simp[Once run_blocks_def] >> rename1 `SUC m <= SUC N` >>
  `m <= N` by simp[] >>
  `?e. run_block m ctx cb
      (t with vs_gas_readings := gas_prefix n t.vs_gas_readings ++ tail) = Error e` by
    (qpat_x_assum `run_blocks (SUC m) _ _ _ = Error _` mp_tac >>
     pure_once_rewrite_tac[run_blocks_unfold] >> simp[] >>
     Cases_on `run_block m ctx cb
       (t with vs_gas_readings := gas_prefix n t.vs_gas_readings ++ tail)` >>
     simp[] >>
     `run_block N ctx cb
       (t with vs_gas_readings := gas_prefix n t.vs_gas_readings ++ tail) = OK v'` by
       (irule venomExecPropsTheory.run_block_fuel_mono_OK >>
        qexists_tac `m` >> simp[]) >>
     qpat_x_assum `gas_replay_at n (run_block N ctx cb) t` mp_tac >>
     simp[gas_replay_at_def] >> disch_then (qspec_then `tail` mp_tac) >>
     simp[lift_result_def]) >>
  `?e. run_block m ctx bb (s with vs_gas_readings := p ++ tail) = Error e` by
    metis_tac[] >>
  pure_once_rewrite_tac[run_blocks_unfold] >> simp[]) g

and runner_ok_tac g = (
  `v.vs_inst_idx = 0 /\ ~v.vs_halted` by
    metis_tac[venomExecPropsTheory.run_block_OK_inst_idx_0,
      venomExecPropsTheory.run_block_OK_not_halted] >>
  `~(?e. run_blocks N ctx fn' v = Error e)` by
    (qpat_x_assum `~(?e. run_blocks (SUC N) _ _ _ = Error e)` mp_tac >>
     simp[Once run_blocks_unfold]) >>
  qabbrev_tac `nc = gas_count_blocks N ctx fn' v` >>
  `gas_replay_at nc (run_blocks N ctx fn') v` by
    metis_tac[remove_unused_blocks_successful_replay_count] >>
  `v.vs_gas_readings = DROP nb t.vs_gas_readings` by
    (qpat_x_assum `gas_replay_at nb (run_block N ctx cb) t` mp_tac >>
     simp[gas_replay_at_def] >> disch_then (qspec_then `[]` mp_tac) >>
     Cases_on `run_block N ctx cb
       (t with vs_gas_readings := gas_prefix nb t.vs_gas_readings)` >>
     simp[lift_result_def] >> metis_tac[]) >>
  `gas_replay_at nc
      (\u. if u.vs_halted then Halt u else run_blocks N ctx fn' u) v` by
    (qpat_x_assum `gas_replay_at nc (run_blocks N ctx fn') v` mp_tac >>
     simp[gas_replay_at_def]) >>
  `gas_replay_at (nb + nc) (\u. gas_bind_ok (run_block N ctx cb u)
      (\v. if v.vs_halted then Halt v else run_blocks N ctx fn' v)) t` by
    (irule remove_unused_replay_bind_ok_count >> simp[]) >>
  `!gs. run_blocks (SUC N) ctx fn' (t with vs_gas_readings := gs) =
    gas_bind_ok (run_block N ctx cb (t with vs_gas_readings := gs))
      (\u. if u.vs_halted then Halt u else run_blocks N ctx fn' u)` by
    (gen_tac >> irule gas_run_blocks_layer >> simp[]) >>
  `run_blocks (SUC N) ctx fn' t =
    gas_bind_ok (run_block N ctx cb t)
      (\u. if u.vs_halted then Halt u else run_blocks N ctx fn' u)` by
    (irule gas_run_blocks_layer >> simp[]) >>
  `gas_replay_at (nb + nc) (run_blocks (SUC N) ctx fn') t` by
    (qpat_x_assum `gas_replay_at (nb + nc) (\u. _) t` mp_tac >>
     simp[gas_replay_at_def]) >>
  `n = nb + nc` by metis_tac[remove_unused_replay_count_unique] >>
  `?pc:(256 word) list.
      LENGTH (FILTER (\w. w <> 0w) pc) <=
        LENGTH (FILTER (\w. w <> 0w) (gas_prefix nc v.vs_gas_readings)) /\
      (!tail.
        (!fuel. ?e.
          run_blocks fuel ctx fn (v with vs_gas_readings := pc ++ tail) = Error e) \/
        lift_result (state_equiv V) (execution_equiv V) (execution_equiv V)
          (run_blocks N ctx fn (v with vs_gas_readings := pc ++ tail))
          (run_blocks N ctx fn'
            (v with vs_gas_readings := gas_prefix nc v.vs_gas_readings ++ tail))) /\
      (!tail k. k <= N /\
        (?e. run_blocks k ctx fn'
          (v with vs_gas_readings := gas_prefix nc v.vs_gas_readings ++ tail) = Error e) ==>
        ?e. run_blocks k ctx fn (v with vs_gas_readings := pc ++ tail) = Error e)` by
    (qpat_assum `!ctx lr V fn fn' s t n. _` irule >>
     simp[stateEquivPropsTheory.state_equiv_refl] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- (qexists_tac `lr` >> simp[] >>
       qpat_x_assum `!ctx lr V fn fn' s t n. _` kall_tac >> metis_tac[]) >>
     gvs[]) >>
  qpat_x_assum `!ctx lr V fn fn' s t n. _` kall_tac >>
  `!tail. run_block N ctx cb
      (t with vs_gas_readings := gas_prefix nb t.vs_gas_readings ++ tail) =
      OK (v with vs_gas_readings := tail)` by
    (gen_tac >> qpat_x_assum `gas_replay_at nb (run_block N ctx cb) t` mp_tac >>
     simp[gas_replay_at_def] >> disch_then (qspec_then `tail` mp_tac) >>
     Cases_on `run_block N ctx cb
       (t with vs_gas_readings := gas_prefix nb t.vs_gas_readings ++ tail)` >>
     simp[lift_result_def]) >>
  `!fuel a b. state_equiv V a b ==>
    lift_result (state_equiv V) (execution_equiv V) (execution_equiv V)
      (run_blocks fuel ctx fn a) (run_blocks fuel ctx fn b)` by
    (rpt strip_tac >> irule remove_unused_runner_state_transport >>
     simp[] >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `!bb. MEM bb _ ==> _` kall_tac >>
  qpat_x_assum `!bb inst v. MEM bb fn.fn_blocks /\ _ ==> _` kall_tac >>
  qpat_x_assum `state_equiv V (s with vs_gas_readings := _) t` kall_tac >>
  qexists_tac `p ++ pc` >>
  conj_tac
  >- (gvs[FILTER_APPEND, gas_prefix_add] >> decide_tac) >>
  conj_tac >- runner_continue_high_tac >>
  runner_continue_low_tac) g

and runner_continue_high_tac g = (
  gen_tac >>
  qpat_x_assum `!tail. (?e. _ /\ _) \/ _`
    (qspec_then `pc ++ tail` mp_tac) >> simp[] >> strip_tac
  >- (disj1_tac >> irule remove_unused_run_blocks_error_all_fuel >>
      qexistsl_tac [`e`, `SUC N`] >>
      simp[Once run_blocks_unfold, APPEND_ASSOC]) >>
  Cases_on `run_block N ctx bb (s with vs_gas_readings := p ++ (pc ++ tail))` >>
  gvs[lift_result_def] >> rename1 `state_equiv V u (v with vs_gas_readings := pc ++ tail)` >>
  `~u.vs_halted` by
    gvs[state_equiv_def, execution_equiv_def, stateFrameTheory.execution_frame_def] >>
  qpat_x_assum `!tail. (!fuel. _) \/ _` (qspec_then `tail` mp_tac) >>
  strip_tac
  >- (disj1_tac >> irule remove_unused_permanent_continuation_error >>
      qexistsl_tac [`N`, `bb`, `u`] >> simp[APPEND_ASSOC] >>
      gen_tac >>
      qpat_x_assum `!fuel a b. _`
        (qspecl_then [`fuel`, `u`, `v with vs_gas_readings := pc ++ tail`] mp_tac) >>
      simp[] >>
      first_x_assum (qspec_then `fuel` strip_assume_tac) >>
      Cases_on `run_blocks fuel ctx fn u` >> simp[lift_result_def]) >>
  disj2_tac >>
  pure_once_rewrite_tac[run_blocks_unfold] >>
  pure_rewrite_tac[gas_prefix_add, GSYM APPEND_ASSOC] >>
  simp[] >>
  pure_rewrite_tac[gas_bind_ok_def] >> simp[] >>
  qpat_x_assum `!fuel a b. _`
    (qspecl_then [`N`, `u`, `v with vs_gas_readings := pc ++ tail`] mp_tac) >>
  simp[] >> strip_tac >>
  irule passSimulationProofsTheory.lift_result_trans_proof >>
  conj_tac >- metis_tac[stateEquivPropsTheory.execution_equiv_trans] >>
  conj_tac >- metis_tac[stateEquivPropsTheory.state_equiv_trans] >>
  conj_tac >- metis_tac[stateEquivPropsTheory.execution_equiv_trans] >>
  qexists_tac `run_blocks N ctx fn (v with vs_gas_readings := pc ++ tail)` >>
  simp[]) g

and runner_continue_low_tac g = (
  rpt gen_tac >> strip_tac >>
  Cases_on `k` >- simp[run_blocks_def] >>
  rename1 `SUC m <= SUC N` >>
  `m <= N` by decide_tac >>
  `!a b. (?e. run_block m ctx cb
      (t with vs_gas_readings := gas_prefix nb t.vs_gas_readings ++ a) = Error e) <=>
    (?e. run_block m ctx cb
      (t with vs_gas_readings := gas_prefix nb t.vs_gas_readings ++ b) = Error e)` by
    (drule remove_unused_run_block_replay_threshold >> simp[] >>
     strip_tac >> rpt gen_tac >>
     first_assum (qspec_then `a` mp_tac) >>
     first_x_assum (qspec_then `b` mp_tac) >> simp[]) >>
  qpat_x_assum `run_blocks (SUC m) _ _ _ = Error _` mp_tac >>
  pure_once_rewrite_tac[run_blocks_unfold] >>
  simp[] >> pure_rewrite_tac[gas_prefix_add, GSYM APPEND_ASSOC] >>
  Cases_on `run_block m ctx cb
    (t with vs_gas_readings := gas_prefix nb t.vs_gas_readings ++
      (gas_prefix nc (DROP nb t.vs_gas_readings) ++ tail))`
  >- low_target_ok_tac
  >- simp[] >- simp[] >- simp[] >>
  strip_tac >>
  `?e. run_block m ctx cb (t with vs_gas_readings := gas_prefix nb t.vs_gas_readings ++ (pc ++ tail)) = Error e` by metis_tac[] >>
  `?e. run_block m ctx bb (s with vs_gas_readings := p ++ (pc ++ tail)) = Error e` by
    (qpat_x_assum `!tail k. k <= N /\ (?e. run_block k _ _ _ = Error e) ==> _` irule >> simp[]) >>
  pure_once_rewrite_tac[run_blocks_unfold] >> simp[APPEND_ASSOC]) g

and low_target_ok_tac g = (
  rename1 `run_block m ctx cb _ = OK w` >>
  `run_block N ctx cb
    (t with vs_gas_readings := gas_prefix nb t.vs_gas_readings ++
      (gas_prefix nc (DROP nb t.vs_gas_readings) ++ tail)) = OK w` by
    (irule venomExecPropsTheory.run_block_fuel_mono_OK >> qexists_tac `m` >> simp[]) >>
  `w = v with vs_gas_readings := gas_prefix nc (DROP nb t.vs_gas_readings) ++ tail` by
    (qpat_x_assum `!tail. run_block N ctx cb _ = OK _`
       (qspec_then `gas_prefix nc (DROP nb t.vs_gas_readings) ++ tail` mp_tac) >>
     pure_rewrite_tac[GSYM APPEND_ASSOC] >> simp[]) >>
  gvs[] >> strip_tac >>
  `?e. run_blocks m ctx fn (v with vs_gas_readings := pc ++ tail) = Error e` by
    (qpat_x_assum `!tail k. k <= N /\ (?e. run_blocks k _ _ _ = Error e) ==> _` irule >> simp[]) >>
  qpat_x_assum `!tail. (?e. _ /\ _) \/ _` (qspec_then `pc ++ tail` mp_tac) >>
  simp[] >> strip_tac
  >- (rename1 `eblock <> "out of fuel"` >>
      `!fuel. ?e. run_blocks fuel ctx fn
        (s with vs_gas_readings := p ++ (pc ++ tail)) = Error e` by
        (irule remove_unused_run_blocks_error_all_fuel >>
         qexistsl_tac [`eblock`, `SUC N`] >> simp[Once run_blocks_unfold, APPEND_ASSOC]) >>
      first_x_assum (qspec_then `SUC m` mp_tac) >>
      pure_rewrite_tac[APPEND_ASSOC] >>
      pure_once_rewrite_tac[run_blocks_unfold] >> simp[]) >>
  Cases_on `?e. run_block m ctx bb (s with vs_gas_readings := p ++ pc ++ tail) = Error e`
  >- gvs[] >>
  `run_block N ctx bb (s with vs_gas_readings := p ++ pc ++ tail) =
   run_block m ctx bb (s with vs_gas_readings := p ++ pc ++ tail)` by
    (irule venomExecPropsTheory.run_block_fuel_mono >> simp[] >> metis_tac[]) >>
  Cases_on `run_block m ctx bb (s with vs_gas_readings := p ++ pc ++ tail)` >>
  gvs[lift_result_def] >> rename1 `state_equiv V u (v with vs_gas_readings := pc ++ tail)` >>
  `~u.vs_halted` by
    gvs[state_equiv_def, execution_equiv_def, stateFrameTheory.execution_frame_def] >>
  qpat_x_assum `!fuel a b. _`
    (qspecl_then [`m`, `u`, `v with vs_gas_readings := pc ++ tail`] mp_tac) >>
  simp[] >>
  Cases_on `run_blocks m ctx fn u` >> simp[lift_result_def]) g
in

Theorem remove_unused_run_blocks_prefix_reconstruction_aligned:
  !N ctx lr V fn fn' s t n.
    (!lbl. lookup_block lbl fn'.fn_blocks =
      OPTION_MAP (\bb. clear_nops_block (remove_unused_block lr bb))
        (lookup_block lbl fn.fn_blocks)) /\
    (!bb. MEM bb fn.fn_blocks ==>
      (!i j. i < j /\ j < LENGTH bb.bb_instructions /\
        (EL j bb.bb_instructions).inst_opcode = PHI ==>
        (EL i bb.bb_instructions).inst_opcode = PHI) /\
      block_nop_outputs lr bb SUBSET V) /\
    (!bb inst v. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
      MEM (Var v) inst.inst_operands ==> v NOTIN V) /\
    s.vs_inst_idx = 0 /\ t.vs_inst_idx = 0 /\
    state_equiv V (s with vs_gas_readings := t.vs_gas_readings) t /\
    gas_replay_at n (run_blocks N ctx fn') t /\
    ~(?e. run_blocks N ctx fn' t = Error e) ==>
    ?p:(256 word) list.
      LENGTH (FILTER (\w. w <> 0w) p) <=
        LENGTH (FILTER (\w. w <> 0w) (gas_prefix n t.vs_gas_readings)) /\
      (!tail.
        (!fuel. ?e.
          run_blocks fuel ctx fn (s with vs_gas_readings := p ++ tail) = Error e) \/
        lift_result (state_equiv V) (execution_equiv V) (execution_equiv V)
          (run_blocks N ctx fn (s with vs_gas_readings := p ++ tail))
          (run_blocks N ctx fn'
            (t with vs_gas_readings := gas_prefix n t.vs_gas_readings ++ tail))) /\
      (!tail k. k <= N /\
        (?e. run_blocks k ctx fn'
          (t with vs_gas_readings := gas_prefix n t.vs_gas_readings ++ tail) = Error e) ==>
        ?e. run_blocks k ctx fn (s with vs_gas_readings := p ++ tail) = Error e)
Proof
  Induct_on `N`
  >- simp[Once run_blocks_def] >>
  rpt gen_tac >> strip_tac >>
  `s.vs_current_bb = t.vs_current_bb` by
    gvs[state_equiv_def, execution_equiv_def, stateFrameTheory.execution_frame_def] >>
  Cases_on `lookup_block t.vs_current_bb fn.fn_blocks`
  >- (qpat_x_assum `~(?e. run_blocks _ _ _ _ = Error e)` mp_tac >>
      simp[Once run_blocks_unfold]) >>
  rename1 `lookup_block t.vs_current_bb fn.fn_blocks = SOME bb` >>
  qabbrev_tac `cb = clear_nops_block (remove_unused_block lr bb)` >>
  `lookup_block t.vs_current_bb fn'.fn_blocks = SOME cb` by simp[Abbr `cb`] >>
  `MEM bb fn.fn_blocks` by metis_tac[venomExecPropsTheory.lookup_block_MEM] >>
  `~(?e. run_block N ctx cb t = Error e)` by
    (qpat_x_assum `~(?e. run_blocks _ _ _ _ = Error e)` mp_tac >>
     simp[Once run_blocks_unfold] >> Cases_on `run_block N ctx cb t` >> simp[]) >>
  `?nb. gas_replay_at nb (run_block N ctx cb) t` by
    (rewrite_tac[GSYM gas_replay_def] >> irule gas_run_block >>
     metis_tac[cj 3 gas_replay_fuel]) >>
  `?p. LENGTH (FILTER (\w. w <> 0w) p) <=
        LENGTH (FILTER (\w. w <> 0w) (gas_prefix nb t.vs_gas_readings)) /\
      (!tail.
        (?e. e <> "out of fuel" /\
          run_block N ctx bb (s with vs_gas_readings := p ++ tail) = Error e) \/
        lift_result (state_equiv V) (execution_equiv V) (execution_equiv V)
          (run_block N ctx bb (s with vs_gas_readings := p ++ tail))
          (run_block N ctx cb
            (t with vs_gas_readings := gas_prefix nb t.vs_gas_readings ++ tail))) /\
      (!tail k. k <= N /\
        (?e. run_block k ctx cb
          (t with vs_gas_readings := gas_prefix nb t.vs_gas_readings ++ tail) = Error e) ==>
        ?e. run_block k ctx bb (s with vs_gas_readings := p ++ tail) = Error e)` by
    (simp[Abbr `cb`] >> irule remove_unused_run_block_prefix_reconstruction_aligned >>
     simp[] >> metis_tac[]) >>
  Cases_on `run_block N ctx cb t`
  >- runner_ok_tac
  >- runner_terminal_tac
  >- runner_terminal_tac
  >- runner_terminal_tac >> gvs[]
QED
end

(* Structural interfaces for the concrete protected-liveness pass. *)
Theorem remove_unused_single_pass_lookup_block:
  !lbl fn.
    lookup_block lbl (remove_unused_single_pass fn).fn_blocks =
      OPTION_MAP (\bb. clear_nops_block
        (remove_unused_block (protect_liveness fn (remove_unused_phi_vars fn)
          (liveness_analyze fn)) bb))
        (lookup_block lbl fn.fn_blocks)
Proof
  rpt gen_tac >>
  simp[removeUnusedDefsTheory.remove_unused_single_pass_def,
       passSharedDefsTheory.clear_nops_function_def,
       passTransformTheory.function_map_transform_def,
       listTheory.MAP_MAP_o, combinTheory.o_DEF] >>
  irule passSimulationPropsTheory.lookup_block_map >>
  simp[passSharedDefsTheory.clear_nops_block_def, remove_unused_block_label]
QED

Theorem remove_unused_wf_phi_prefix:
  !fn bb. wf_function fn /\ MEM bb fn.fn_blocks ==>
    !i j. i < j /\ j < LENGTH bb.bb_instructions /\
      (EL j bb.bb_instructions).inst_opcode = PHI ==>
      (EL i bb.bb_instructions).inst_opcode = PHI
Proof
  metis_tac[venomWfTheory.wf_function_def, venomWfTheory.bb_well_formed_def]
QED

Theorem remove_unused_single_pass_prefix_reconstruction_aligned:
  !N ctx fn s t n.
    wf_function fn /\ wf_ssa fn /\ ssa_form fn /\
    s.vs_inst_idx = 0 /\ t.vs_inst_idx = 0 /\
    state_equiv (single_pass_nop_outputs fn)
      (s with vs_gas_readings := t.vs_gas_readings) t /\
    gas_replay_at n (run_blocks N ctx (remove_unused_single_pass fn)) t /\
    ~(?e. run_blocks N ctx (remove_unused_single_pass fn) t = Error e) ==>
    ?p:(256 word) list.
      LENGTH (FILTER (\w. w <> 0w) p) <=
        LENGTH (FILTER (\w. w <> 0w) (gas_prefix n t.vs_gas_readings)) /\
      (!tail.
        (!fuel. ?e.
          run_blocks fuel ctx fn (s with vs_gas_readings := p ++ tail) = Error e) \/
        lift_result (state_equiv (single_pass_nop_outputs fn))
          (execution_equiv (single_pass_nop_outputs fn))
          (execution_equiv (single_pass_nop_outputs fn))
          (run_blocks N ctx fn (s with vs_gas_readings := p ++ tail))
          (run_blocks N ctx (remove_unused_single_pass fn)
            (t with vs_gas_readings := gas_prefix n t.vs_gas_readings ++ tail))) /\
      (!tail k. k <= N /\
        (?e. run_blocks k ctx (remove_unused_single_pass fn)
          (t with vs_gas_readings := gas_prefix n t.vs_gas_readings ++ tail) = Error e) ==>
        ?e. run_blocks k ctx fn (s with vs_gas_readings := p ++ tail) = Error e)
Proof
  rpt gen_tac >> strip_tac >>
  irule remove_unused_run_blocks_prefix_reconstruction_aligned >>
  simp[] >>
  conj_tac >- metis_tac[nop_output_not_used_as_operand] >>
  reverse conj_tac >- metis_tac[] >>
  qexists_tac `protect_liveness fn (remove_unused_phi_vars fn) (liveness_analyze fn)` >>
  simp[remove_unused_single_pass_lookup_block] >>
  metis_tac[remove_unused_wf_phi_prefix, block_nop_outputs_subset_single_pass,
            nop_output_not_used_as_operand]
QED

Theorem remove_unused_blocks_actual_oracle_replay:
  !N ctx fn t.
    ~(?e. run_blocks N ctx fn t = Error e) ==>
    run_blocks N ctx fn
      (t with vs_gas_readings :=
        gas_prefix (gas_count_blocks N ctx fn t) t.vs_gas_readings ++
        DROP (gas_count_blocks N ctx fn t) t.vs_gas_readings) =
    run_blocks N ctx fn t
Proof
  rpt strip_tac >>
  drule remove_unused_blocks_successful_replay_count >>
  rewrite_tac[gas_replay_at_def] >>
  disch_then (qspec_then `DROP (gas_count_blocks N ctx fn t) t.vs_gas_readings` mp_tac) >>
  Cases_on `run_blocks N ctx fn t` >> gvs[lift_result_def] >>
  Cases_on `run_blocks N ctx fn
    (t with vs_gas_readings :=
      gas_prefix (gas_count_blocks N ctx fn t) t.vs_gas_readings ++
      DROP (gas_count_blocks N ctx fn t) t.vs_gas_readings)` >>
  simp[lift_result_def] >> strip_tac >> gvs[] >>
  simp[venomStateTheory.venom_state_component_equality]
QED

Theorem remove_unused_blocks_actual_oracle_error:
  !N ctx fn t k.
    ~(?e. run_blocks N ctx fn t = Error e) /\ k <= N ==>
    ((?e. run_blocks k ctx fn
       (t with vs_gas_readings :=
         gas_prefix (gas_count_blocks N ctx fn t) t.vs_gas_readings ++
         DROP (gas_count_blocks N ctx fn t) t.vs_gas_readings) = Error e) <=>
     (?e. run_blocks k ctx fn t = Error e))
Proof
  rpt strip_tac >>
  drule remove_unused_blocks_successful_prefix_threshold >>
  disch_then (qspecl_then [`k`,
    `gas_prefix (gas_count_blocks N ctx fn t) t.vs_gas_readings ++
     DROP (gas_count_blocks N ctx fn t) t.vs_gas_readings`] mp_tac) >>
  simp[remove_unused_gas_prefix_append]
QED

Theorem remove_unused_single_pass_finite_reconstruction:
  !N ctx fn s t.
    wf_function fn /\ wf_ssa fn /\ ssa_form fn /\
    s.vs_inst_idx = 0 /\ t.vs_inst_idx = 0 /\
    state_equiv (single_pass_nop_outputs fn)
      (s with vs_gas_readings := t.vs_gas_readings) t /\
    ~(?e. run_blocks N ctx (remove_unused_single_pass fn) t = Error e) ==>
    ?gs:(256 word) list.
      LENGTH (FILTER (\w. w <> 0w) gs) <=
        LENGTH (FILTER (\w. w <> 0w) t.vs_gas_readings) /\
      ((!fuel. ?e. run_blocks fuel ctx fn (s with vs_gas_readings := gs) = Error e) \/
        lift_result (state_equiv (single_pass_nop_outputs fn))
          (execution_equiv (single_pass_nop_outputs fn))
          (execution_equiv (single_pass_nop_outputs fn))
          (run_blocks N ctx fn (s with vs_gas_readings := gs))
          (run_blocks N ctx (remove_unused_single_pass fn) t)) /\
      (!k. k <= N /\
        (?e. run_blocks k ctx (remove_unused_single_pass fn) t = Error e) ==>
        ?e. run_blocks k ctx fn (s with vs_gas_readings := gs) = Error e)
Proof
  rpt gen_tac >> strip_tac >>
  `gas_replay_at (gas_count_blocks N ctx (remove_unused_single_pass fn) t)
    (run_blocks N ctx (remove_unused_single_pass fn)) t` by
      (irule remove_unused_blocks_successful_replay_count >> metis_tac[]) >>
  drule_all remove_unused_single_pass_prefix_reconstruction_aligned >>
  disch_then (qx_choose_then `p` strip_assume_tac) >>
  qexists_tac `p ++ DROP (gas_count_blocks N ctx (remove_unused_single_pass fn) t) t.vs_gas_readings` >>
  conj_tac
  >- (qspec_then `gas_count_blocks N ctx (remove_unused_single_pass fn) t`
        (qspec_then `t.vs_gas_readings` mp_tac) remove_unused_actual_oracle_nonzero >>
      simp[FILTER_APPEND] >> decide_tac) >>
  conj_tac
  >- (drule remove_unused_blocks_actual_oracle_replay >>
      disch_then (fn th => rewrite_tac[GSYM th]) >>
      first_x_assum (qspec_then
        `DROP (gas_count_blocks N ctx (remove_unused_single_pass fn) t) t.vs_gas_readings` mp_tac) >>
      simp[]) >>
  rpt strip_tac >>
  drule_all remove_unused_blocks_actual_oracle_error >>
  strip_tac >>
  first_x_assum irule >> simp[]
QED

(* Error continuations use actual finite oracles, without replaying an Error. *)
Theorem remove_unused_deleted_gas_error_continuation:
  !inst out V s t (src_cont:venom_state -> exec_result) dst_cont.
    inst.inst_opcode = GAS /\ inst.inst_outputs = [out] /\ out IN V /\
    state_equiv V (s with vs_gas_readings := t.vs_gas_readings) t /\
    (?e. dst_cont t = Error e) /\
    (!a b. state_equiv V (b with vs_gas_readings := a.vs_gas_readings) a /\
      (?e. dst_cont a = Error e) ==>
      ?q:(256 word) list.
        LENGTH (FILTER (\w. w <> 0w) q) <=
          LENGTH (FILTER (\w. w <> 0w) a.vs_gas_readings) /\
        ?e. src_cont (b with vs_gas_readings := q) = Error e) ==>
    ?gs:(256 word) list.
      LENGTH (FILTER (\w. w <> 0w) gs) <=
        LENGTH (FILTER (\w. w <> 0w) t.vs_gas_readings) /\
      ?e. (case exec_gas inst (s with vs_gas_readings := gs) of
             OK a => src_cont a | other => other) = Error e
Proof
  rpt strip_tac >>
  `state_equiv V
     ((update_var out 0w s) with vs_gas_readings := t.vs_gas_readings) t` by
    (pure_once_rewrite_tac[GSYM gas_update_var] >>
     irule state_equiv_effect_free_compose >>
     qexistsl [`{out}`, `s with vs_gas_readings := t.vs_gas_readings`] >>
     simp[update_var_state_equiv]) >>
  first_x_assum (qspecl_then [`t`, `update_var out 0w s`] mp_tac) >>
  impl_tac >- metis_tac[] >> strip_tac >>
  qexists_tac `0w::q` >> simp[exec_gas_def, gas_update_var] >> metis_tac[]
QED

Theorem remove_unused_retained_base_error_transport:
  !inst V s t.
    state_equiv V (s with vs_gas_readings := t.vs_gas_readings) t /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN V) /\
    (?e. step_inst_base inst t = Error e) ==>
    ?e. step_inst_base inst (s with vs_gas_readings := t.vs_gas_readings) = Error e
Proof
  rpt strip_tac >> drule_all remove_unused_retained_base_transport >>
  disch_then (qspec_then `t.vs_gas_readings` mp_tac) >>
  Cases_on `step_inst_base inst (s with vs_gas_readings := t.vs_gas_readings)` >>
  gvs[lift_result_def]
QED

Theorem remove_unused_retained_invoke_error_transport:
  !inst V s t fuel ctx.
    inst.inst_opcode = INVOKE /\
    state_equiv V (s with vs_gas_readings := t.vs_gas_readings) t /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN V) /\
    (?e. step_inst fuel ctx inst t = Error e) ==>
    ?e. step_inst fuel ctx inst (s with vs_gas_readings := t.vs_gas_readings) = Error e
Proof
  rpt strip_tac >> drule_all remove_unused_retained_invoke_transport >>
  disch_then (qspecl_then [`fuel`, `ctx`, `t.vs_gas_readings`] mp_tac) >>
  Cases_on `step_inst fuel ctx inst (s with vs_gas_readings := t.vs_gas_readings)` >>
  gvs[lift_result_def]
QED

Theorem remove_unused_retained_base_error_continuation:
  !inst V s t u (src_cont:venom_state -> exec_result) dst_cont.
    inst.inst_opcode <> GAS /\ inst.inst_opcode <> INVOKE /\
    state_equiv V (s with vs_gas_readings := t.vs_gas_readings) t /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN V) /\
    step_inst_base inst t = OK u /\ (?e. dst_cont u = Error e) /\
    (!a b. state_equiv V (b with vs_gas_readings := a.vs_gas_readings) a /\
      (?e. dst_cont a = Error e) ==>
      ?q:(256 word) list.
        LENGTH (FILTER (\w. w <> 0w) q) <=
          LENGTH (FILTER (\w. w <> 0w) a.vs_gas_readings) /\
        ?e. src_cont (b with vs_gas_readings := q) = Error e) ==>
    ?gs:(256 word) list.
      LENGTH (FILTER (\w. w <> 0w) gs) <=
        LENGTH (FILTER (\w. w <> 0w) t.vs_gas_readings) /\
      ?e. (case step_inst_base inst (s with vs_gas_readings := gs) of
             OK a => src_cont a | other => other) = Error e
Proof
  rpt strip_tac >>
  drule_all remove_unused_retained_base_transport >>
  disch_then (qspec_then `t.vs_gas_readings` mp_tac) >>
  Cases_on `step_inst_base inst (s with vs_gas_readings := t.vs_gas_readings)` >>
  gvs[lift_result_def] >> strip_tac >> rename1 `state_equiv V v u` >>
  `u.vs_gas_readings = t.vs_gas_readings` by
    metis_tac[remove_unused_base_oracle_ok] >>
  `!gs. step_inst_base inst (s with vs_gas_readings := gs) =
        OK (v with vs_gas_readings := gs)` by
    (qspecl_then [`inst`, `s with vs_gas_readings := t.vs_gas_readings`, `v`]
       mp_tac remove_unused_base_oracle_ok >> simp[]) >>
  `state_equiv V (v with vs_gas_readings := u.vs_gas_readings) u` by
    (gvs[state_equiv_def, execution_equiv_def,
         stateFrameTheory.execution_frame_def, venom_state_component_equality,
         lookup_var_def]) >>
  first_x_assum (qspecl_then [`u`, `v`] mp_tac) >>
  impl_tac >- metis_tac[] >> strip_tac >>
  qexists_tac `q` >> simp[] >> metis_tac[]
QED

Theorem remove_unused_retained_invoke_error_continuation:
  !inst V s t u fuel ctx (src_cont:venom_state -> exec_result) dst_cont.
    inst.inst_opcode = INVOKE /\
    state_equiv V (s with vs_gas_readings := t.vs_gas_readings) t /\
    (!x. MEM (Var x) inst.inst_operands ==> x NOTIN V) /\
    step_inst fuel ctx inst t = OK u /\ (?e. dst_cont u = Error e) /\
    (!a b. state_equiv V (b with vs_gas_readings := a.vs_gas_readings) a /\
      (?e. dst_cont a = Error e) ==>
      ?q:(256 word) list.
        LENGTH (FILTER (\w. w <> 0w) q) <=
          LENGTH (FILTER (\w. w <> 0w) a.vs_gas_readings) /\
        ?e. src_cont (b with vs_gas_readings := q) = Error e) ==>
    ?gs:(256 word) list.
      LENGTH (FILTER (\w. w <> 0w) gs) <=
        LENGTH (FILTER (\w. w <> 0w) t.vs_gas_readings) /\
      ?e. (case step_inst fuel ctx inst (s with vs_gas_readings := gs) of
             OK a => src_cont a | other => other) = Error e
Proof
  rpt strip_tac >>
  `result_equiv V
     (step_inst fuel ctx inst (s with vs_gas_readings := t.vs_gas_readings))
     (step_inst fuel ctx inst t)` by
    (irule step_inst_result_equiv_full >> simp[venomInstTheory.is_terminator_def]) >>
  Cases_on `step_inst fuel ctx inst (s with vs_gas_readings := t.vs_gas_readings)` >>
  gvs[result_equiv_def] >> rename1 `state_equiv V v u` >>
  `?n. gas_replay_at n (step_inst fuel ctx inst)
          (s with vs_gas_readings := t.vs_gas_readings) /\
       gas_replay_at n (step_inst fuel ctx inst) t` by
    (irule remove_unused_invoke_pair_replay >> simp[] >>
     qexists_tac `V` >> simp[]) >>
  `u.vs_gas_readings = DROP n t.vs_gas_readings` by
    metis_tac[remove_unused_replay_ok] >>
  `!gs. step_inst fuel ctx inst
     (s with vs_gas_readings := gas_prefix n t.vs_gas_readings ++ gs) =
     OK (v with vs_gas_readings := gs)` by
    (qpat_assum `step_inst _ _ _ (s with vs_gas_readings := _) = OK v`
       (mp_then (Pos last) mp_tac remove_unused_replay_ok) >>
     simp[] >> disch_then drule >> simp[]) >>
  `state_equiv V (v with vs_gas_readings := u.vs_gas_readings) u` by
    (gvs[state_equiv_def, execution_equiv_def,
         stateFrameTheory.execution_frame_def, venom_state_component_equality,
         lookup_var_def]) >>
  first_x_assum (qspecl_then [`u`, `v`] mp_tac) >>
  impl_tac >- metis_tac[] >> strip_tac >>
  qexists_tac `gas_prefix n t.vs_gas_readings ++ q` >> conj_tac
  >- (qspecl_then [`n`, `t.vs_gas_readings`] mp_tac
        remove_unused_actual_oracle_nonzero >>
      gvs[FILTER_APPEND] >> decide_tac) >>
  simp[] >> metis_tac[]
QED

Theorem remove_unused_retained_gas_error_continuation:
  !inst out V s t u w (src_cont:venom_state -> exec_result) dst_cont.
    inst.inst_opcode = GAS /\ inst.inst_outputs = [out] /\
    state_equiv V (s with vs_gas_readings := t.vs_gas_readings) t /\
    exec_gas inst t = OK u /\
    w = (case t.vs_gas_readings of [] => 0w | h::rest => h) /\
    (?e. dst_cont u = Error e) /\
    (!a b. state_equiv V (b with vs_gas_readings := a.vs_gas_readings) a /\
      (?e. dst_cont a = Error e) ==>
      ?q:(256 word) list.
        LENGTH (FILTER (\z. z <> 0w) q) <=
          LENGTH (FILTER (\z. z <> 0w) a.vs_gas_readings) /\
        ?e. src_cont (b with vs_gas_readings := q) = Error e) ==>
    ?gs:(256 word) list.
      LENGTH (FILTER (\z. z <> 0w) gs) <=
        LENGTH (FILTER (\z. z <> 0w) t.vs_gas_readings) /\
      ?e. (case exec_gas inst (s with vs_gas_readings := gs) of
             OK a => src_cont a | other => other) = Error e
Proof
  rpt strip_tac >>
  `u = update_var out w (t with vs_gas_readings := u.vs_gas_readings)` by
    (Cases_on `t.vs_gas_readings` >> gvs[exec_gas_def]) >>
  `state_equiv V
     ((update_var out w s) with vs_gas_readings := u.vs_gas_readings) u` by
    (qpat_assum `u = update_var _ _ _` (fn th => once_rewrite_tac[th]) >>
     pure_once_rewrite_tac[GSYM gas_update_var] >>
     irule stateEquivProofsTheory.update_var_preserves >>
     qpat_x_assum `state_equiv V _ t` mp_tac >>
     simp[state_equiv_def, execution_equiv_def,
          stateFrameTheory.execution_frame_def, venom_state_component_equality,
          lookup_var_def]) >>
  first_x_assum (qspecl_then [`u`, `update_var out w s`] mp_tac) >>
  impl_tac >- metis_tac[] >> strip_tac >>
  qexists_tac `w::q` >> conj_tac
  >- (Cases_on `t.vs_gas_readings` >>
      gvs[exec_gas_def, gas_update_var] >>
      Cases_on `h = 0w` >> simp[]) >>
  simp[exec_gas_def, gas_update_var] >> metis_tac[]
QED

Theorem remove_unused_deleted_base_error_continuation:
  !inst V s t (src_cont:venom_state -> exec_result) dst_cont.
    is_effect_free_op inst.inst_opcode /\
    inst.inst_opcode <> GAS /\ inst.inst_opcode <> INVOKE /\
    set inst.inst_outputs SUBSET V /\
    state_equiv V (s with vs_gas_readings := t.vs_gas_readings) t /\
    (?e. dst_cont t = Error e) /\
    (!a b. state_equiv V (b with vs_gas_readings := a.vs_gas_readings) a /\
      (?e. dst_cont a = Error e) ==>
      ?q:(256 word) list.
        LENGTH (FILTER (\w. w <> 0w) q) <=
          LENGTH (FILTER (\w. w <> 0w) a.vs_gas_readings) /\
        ?e. src_cont (b with vs_gas_readings := q) = Error e) ==>
    ?gs:(256 word) list.
      LENGTH (FILTER (\w. w <> 0w) gs) <=
        LENGTH (FILTER (\w. w <> 0w) t.vs_gas_readings) /\
      ?e. (case step_inst_base inst (s with vs_gas_readings := gs) of
             OK a => src_cont a | other => other) = Error e
Proof
  rpt strip_tac >>
  `(?v. step_inst_base inst s = OK v) \/
   (?e. step_inst_base inst s = Error e)` by
    metis_tac[effect_free_step_ok_or_error, step_inst_non_invoke]
  >- (drule_all venomInstProofsTheory.step_inst_base_effect_free_state_equiv >>
      strip_tac >>
      `state_equiv V (v with vs_gas_readings := t.vs_gas_readings) t` by
        (irule state_equiv_effect_free_compose >>
         qexistsl [`set inst.inst_outputs`, `s with vs_gas_readings := t.vs_gas_readings`] >>
         simp[] >>
         gvs[state_equiv_def, execution_equiv_def,
             stateFrameTheory.execution_frame_def, lookup_var_def]) >>
      first_x_assum (qspecl_then [`t`, `v`] mp_tac) >>
      impl_tac >- metis_tac[] >> strip_tac >>
      `!gs. step_inst_base inst (s with vs_gas_readings := gs) =
            OK (v with vs_gas_readings := gs)` by
        (drule_all remove_unused_base_oracle_ok >> simp[]) >>
      qexists_tac `q` >> simp[] >> metis_tac[]) >>
  qexists_tac `[]` >> simp[] >>
  drule remove_unused_base_oracle_transport >>
  disch_then (qspec_then `s` (qspec_then `[]` mp_tac)) >>
  Cases_on `step_inst_base inst (s with vs_gas_readings := [])` >>
  gvs[lift_result_def]
QED

Theorem remove_unused_block_error_reconstruction:
  !N ctx lr V bb s t.
    block_nop_outputs lr bb SUBSET V /\
    (!inst v. MEM inst bb.bb_instructions /\ MEM (Var v) inst.inst_operands ==>
              v NOTIN V) /\
    s.vs_inst_idx = t.vs_inst_idx /\
    state_equiv V (s with vs_gas_readings := t.vs_gas_readings) t /\
    (?e. exec_block N ctx (remove_unused_block lr bb) t = Error e) ==>
    ?gs:(256 word) list.
      LENGTH (FILTER (\w. w <> 0w) gs) <=
        LENGTH (FILTER (\w. w <> 0w) t.vs_gas_readings) /\
      ?e. exec_block N ctx bb (s with vs_gas_readings := gs) = Error e
Proof
  rpt gen_tac >> map_every qid_spec_tac [`s`, `t`] >>
  measureInduct_on `LENGTH bb.bb_instructions - t.vs_inst_idx` >>
  rpt strip_tac >> Cases_on `t.vs_inst_idx < LENGTH bb.bb_instructions`
  >- suspend "in_range" >>
  qexists_tac `[]` >> simp[Once exec_block_def, venomInstTheory.get_instruction_def]
QED

Resume remove_unused_block_error_reconstruction[in_range]:
  gvs[] >> qabbrev_tac `i = t.vs_inst_idx` >>
  qabbrev_tac `inst = EL i bb.bb_instructions` >>
  qabbrev_tac `live = live_after_at lr bb.bb_label i (LENGTH bb.bb_instructions)` >>
  `get_instruction bb i = SOME inst /\
   get_instruction (remove_unused_block lr bb) i =
     SOME (remove_unused_inst live inst)` by
    simp[venomInstTheory.get_instruction_def, get_instruction_remove_unused,
         Abbr `inst`, Abbr `live`] >>
  `MEM inst bb.bb_instructions` by simp[Abbr `inst`, EL_MEM] >>
  `!x. MEM (Var x) inst.inst_operands ==> x NOTIN V` by metis_tac[] >>
  qabbrev_tac `src_cont = \a. exec_block N ctx bb
    (a with vs_inst_idx := SUC i)` >>
  qabbrev_tac `dst_cont = \a. exec_block N ctx (remove_unused_block lr bb)
    (a with vs_inst_idx := SUC i)` >>
  `!a b.
    state_equiv V (b with vs_gas_readings := a.vs_gas_readings) a /\
    (?e. dst_cont a = Error e) ==>
    ?q:(256 word) list.
      LENGTH (FILTER (\w. w <> 0w) q) <=
        LENGTH (FILTER (\w. w <> 0w) a.vs_gas_readings) /\
      ?e. src_cont (b with vs_gas_readings := q) = Error e` by
    (rpt strip_tac >>
     first_x_assum (qspec_then `SUC i` mp_tac) >>
     impl_tac >- simp[] >>
     disch_then (qspec_then `a with vs_inst_idx := SUC i` mp_tac) >> simp[] >>
     disch_then (qspec_then `b with vs_inst_idx := SUC i` mp_tac) >>
     impl_tac
     >- (conj_tac >- first_assum ACCEPT_TAC >>
         gvs[Abbr `dst_cont`] >>
         irule execEquivProofsTheory.state_equiv_inst_idx >> simp[]) >>
     simp[Abbr `src_cont`, Abbr `dst_cont`]) >>
  qpat_x_assum `!y. LENGTH bb.bb_instructions < _ ==> _` kall_tac >>
  Cases_on `remove_unused_inst live inst = inst`
  >- suspend "retained" >>
  suspend "deleted"
QED

Resume remove_unused_block_error_reconstruction[retained]:
  Cases_on `is_terminator inst.inst_opcode`
  >- suspend "terminator" >>
  `!gs. exec_block N ctx bb (s with vs_gas_readings := gs) =
    gas_bind_ok (step_inst N ctx inst (s with vs_gas_readings := gs)) src_cont` by
    (gen_tac >> simp[Once exec_block_def, Abbr `i`, Abbr `src_cont`, gas_bind_ok_def]) >>
  `!gs. exec_block N ctx (remove_unused_block lr bb) (t with vs_gas_readings := gs) =
    gas_bind_ok (step_inst N ctx inst (t with vs_gas_readings := gs)) dst_cont` by
    (gen_tac >> simp[Once exec_block_def, Abbr `i`, Abbr `dst_cont`, gas_bind_ok_def]) >>
  `exec_block N ctx (remove_unused_block lr bb) t =
    gas_bind_ok (step_inst N ctx inst t) dst_cont` by
    (first_x_assum (qspec_then `t.vs_gas_readings` mp_tac) >> simp[]) >>
  Cases_on `inst.inst_opcode = INVOKE`
  >- suspend "invoke" >>
  Cases_on `inst.inst_opcode = GAS`
  >- suspend "gas" >>
  Cases_on `step_inst_base inst t` >> gvs[step_inst_def, gas_bind_ok_def]
  >- (irule remove_unused_retained_base_error_continuation >>
      simp[] >> qexistsl [`V`, `dst_cont`] >> simp[]) >>
  drule_all remove_unused_retained_base_transport >>
  disch_then (qspec_then `t.vs_gas_readings` mp_tac) >>
  Cases_on `step_inst_base inst (s with vs_gas_readings := t.vs_gas_readings)` >>
  gvs[lift_result_def] >>
  qexists_tac `t.vs_gas_readings` >> simp[]
QED

Resume remove_unused_block_error_reconstruction[invoke]:
  Cases_on `step_inst N ctx inst t` >> gvs[gas_bind_ok_def]
  >- (simp[gas_bind_ok_def] >>
      irule remove_unused_retained_invoke_error_continuation >>
      simp[] >> qexistsl [`V`, `dst_cont`] >> simp[]) >>
  drule_all remove_unused_retained_invoke_transport >>
  disch_then (qspecl_then [`N`, `ctx`, `t.vs_gas_readings`] mp_tac) >>
  Cases_on `step_inst N ctx inst (s with vs_gas_readings := t.vs_gas_readings)` >>
  gvs[lift_result_def] >>
  qexists_tac `t.vs_gas_readings` >> simp[gas_bind_ok_def]
QED

Resume remove_unused_block_error_reconstruction[gas]:
  Cases_on `?out. inst.inst_outputs = [out]`
  >- (pop_assum strip_assume_tac >>
      `?u. exec_gas inst t = OK u` by
        (Cases_on `t.vs_gas_readings` >> simp[exec_gas_def]) >>
      gvs[step_inst_def, step_inst_base_opcode_eqs, gas_bind_ok_def] >>
      irule remove_unused_retained_gas_error_continuation >> simp[] >>
      qexistsl [`V`, `dst_cont`] >> simp[]) >>
  qexists_tac `[]` >>
  simp[step_inst_def, step_inst_base_opcode_eqs, exec_gas_def, gas_bind_ok_def] >>
  Cases_on `inst.inst_outputs` >> gvs[] >> Cases_on `t'` >> gvs[]
QED

Resume remove_unused_block_error_reconstruction[terminator]:
  `inst.inst_opcode <> GAS /\ inst.inst_opcode <> INVOKE` by
    (Cases_on `inst.inst_opcode` >> gvs[venomInstTheory.is_terminator_def]) >>
  `?err. step_inst_base inst t = Error err` by
    (qpat_x_assum `exec_block N ctx (remove_unused_block lr bb) t = Error e` mp_tac >>
     simp[Once exec_block_def, Abbr `i`, step_inst_def] >>
     Cases_on `step_inst_base inst t` >> simp[] >>
     IF_CASES_TAC >> simp[]) >>
  drule_all remove_unused_retained_base_transport >>
  disch_then (qspec_then `t.vs_gas_readings` mp_tac) >>
  Cases_on `step_inst_base inst (s with vs_gas_readings := t.vs_gas_readings)` >>
  gvs[lift_result_def] >>
  qexists_tac `t.vs_gas_readings` >>
  simp[Once exec_block_def, step_inst_def]
QED

Resume remove_unused_block_error_reconstruction[deleted]:
  `remove_unused_inst live inst = mk_nop_inst inst` by
    metis_tac[remove_unused_inst_cases] >>
  `~is_terminator inst.inst_opcode` by
    metis_tac[remove_unused_inst_nop_not_terminator] >>
  `set inst.inst_outputs SUBSET V` by
    (irule SUBSET_TRANS >> qexists_tac `block_nop_outputs lr bb` >> simp[] >>
     irule nop_outputs_in_block_nop_outputs >> qexists_tac `i` >>
     simp[Abbr `inst`, Abbr `live`]) >>
  `dst_cont t = Error e` by
    (qpat_x_assum `exec_block N ctx (remove_unused_block lr bb) t = Error e` mp_tac >>
     simp[Once exec_block_def, Abbr `dst_cont`, Abbr `i`,
       passSharedDefsTheory.mk_nop_inst_def, step_inst_def,
       step_inst_base_opcode_eqs, venomInstTheory.is_terminator_def]) >>
  `!gs. exec_block N ctx bb (s with vs_gas_readings := gs) =
    gas_bind_ok (step_inst N ctx inst (s with vs_gas_readings := gs)) src_cont` by
    (gen_tac >> simp[Once exec_block_def, Abbr `i`, Abbr `src_cont`, gas_bind_ok_def]) >>
  Cases_on `inst.inst_opcode = GAS`
  >- (Cases_on `?out. inst.inst_outputs = [out]`
      >- (pop_assum strip_assume_tac >>
          `out IN V` by gvs[SUBSET_DEF] >>
          simp[step_inst_def, step_inst_base_opcode_eqs, gas_bind_ok_def] >>
          irule remove_unused_deleted_gas_error_continuation >> simp[] >>
          qexistsl [`V`, `dst_cont`] >> simp[]) >>
      qexists_tac `[]` >>
      simp[step_inst_def, step_inst_base_opcode_eqs, exec_gas_def, gas_bind_ok_def] >>
      Cases_on `inst.inst_outputs` >> gvs[] >> Cases_on `t'` >> gvs[]) >>
  `is_effect_free_op inst.inst_opcode` by metis_tac[remove_unused_inst_nop_effect_free] >>
  `inst.inst_opcode <> INVOKE` by
    (Cases_on `inst.inst_opcode = INVOKE` >> gvs[venomInstTheory.is_effect_free_op_def]) >>
  simp[step_inst_def, gas_bind_ok_def] >>
  irule remove_unused_deleted_base_error_continuation >> simp[] >>
  qexistsl [`V`, `dst_cont`] >> simp[]
QED

Finalise remove_unused_block_error_reconstruction

Theorem remove_unused_run_block_error_reconstruction:
  !N ctx lr V bb s t.
    (!i j. i < j /\ j < LENGTH bb.bb_instructions /\
      (EL j bb.bb_instructions).inst_opcode = PHI ==>
      (EL i bb.bb_instructions).inst_opcode = PHI) /\
    block_nop_outputs lr bb SUBSET V /\
    (!inst v. MEM inst bb.bb_instructions /\ MEM (Var v) inst.inst_operands ==>
              v NOTIN V) /\
    s.vs_inst_idx = 0 /\ t.vs_inst_idx = 0 /\
    state_equiv V (s with vs_gas_readings := t.vs_gas_readings) t /\
    (?e. run_block N ctx (clear_nops_block (remove_unused_block lr bb)) t = Error e) ==>
    ?gs:(256 word) list.
      LENGTH (FILTER (\w. w <> 0w) gs) <=
        LENGTH (FILTER (\w. w <> 0w) t.vs_gas_readings) /\
      ?e. run_block N ctx bb (s with vs_gas_readings := gs) = Error e
Proof
  rpt strip_tac >>
  qspecl_then [`s`, `bb.bb_instructions`] strip_assume_tac eval_phis_ok_or_error_defs
  >- suspend "phi_success" >>
  qexists_tac `[]` >> simp[] >>
  `!gs. eval_phis (s with vs_gas_readings := gs) bb.bb_instructions = Error e' /\
        e' <> "out of fuel"` by metis_tac[remove_unused_phi_replay_error] >>
  simp[run_block_def]
QED

Resume remove_unused_run_block_error_reconstruction[phi_success]:
  rename1 `eval_phis s bb.bb_instructions = OK sp` >>
  drule remove_unused_phi_replay_ok >> strip_tac >>
  `?tp. eval_phis t
      (FILTER (\inst. inst.inst_opcode <> NOP)
        (MAPi (\idx inst. remove_unused_inst
          (live_after_at lr bb.bb_label idx (LENGTH bb.bb_instructions)) inst)
          bb.bb_instructions)) = OK tp /\
      state_equiv V (sp with vs_gas_readings := t.vs_gas_readings) tp` by
    (ho_match_mp_tac eval_phis_remove_unused >>
     qexists_tac `s with vs_gas_readings := t.vs_gas_readings` >>
     simp[] >> conj_tac >- metis_tac[] >> conj_tac
     >- (rpt strip_tac >>
         `set (EL idx bb.bb_instructions).inst_outputs SUBSET block_nop_outputs lr bb` by
           (irule nop_outputs_in_block_nop_outputs >> qexists_tac `idx` >> simp[]) >>
         metis_tac[SUBSET_TRANS]) >>
     metis_tac[]) >>
  qabbrev_tac `mb = remove_unused_block lr bb` >>
  qabbrev_tac `cb = clear_nops_block mb` >>
  `eval_phis t cb.bb_instructions = OK tp` by
    gvs[Abbr `cb`, Abbr `mb`, passSharedDefsTheory.clear_nops_block_def,
        removeUnusedDefsTheory.remove_unused_block_def] >>
  drule remove_unused_phi_replay_ok >> strip_tac >>
  qabbrev_tac `i = phi_prefix_length bb.bb_instructions` >>
  qabbrev_tac `j = phi_prefix_length cb.bb_instructions` >>
  `j = LENGTH (FILTER (\inst. inst.inst_opcode <> NOP)
        (TAKE i mb.bb_instructions))` by
    (simp[Abbr `i`, Abbr `j`, Abbr `cb`, Abbr `mb`,
       passSharedDefsTheory.clear_nops_block_def, removeUnusedDefsTheory.remove_unused_block_def] >>
     ho_match_mp_tac phi_prefix_length_remove_unused_clear >> metis_tac[]) >>
  `!gs. run_block N ctx bb (s with vs_gas_readings := gs) =
     exec_block N ctx bb ((sp with vs_inst_idx := i) with vs_gas_readings := gs)` by
    simp[run_block_def, Abbr `i`] >>
  `exec_block N ctx cb (tp with vs_inst_idx := j) = Error e` by
    gvs[run_block_def, Abbr `j`] >>
  suspend "entry"
QED

Resume remove_unused_run_block_error_reconstruction[entry]:
  `?err. exec_block N ctx mb (tp with vs_inst_idx := i) = Error err` by
    (qspecl_then [`N`, `ctx`, `mb`, `tp with vs_inst_idx := i`] mp_tac
       passSharedPropsTheory.clear_nops_block_gen >>
     simp[Abbr `cb`] >>
     Cases_on `exec_block N ctx mb (tp with vs_inst_idx := i)` >>
     gvs[result_equiv_def, lift_result_def]) >>
  `state_equiv V
     ((sp with vs_inst_idx := i) with vs_gas_readings :=
       (tp with vs_inst_idx := i).vs_gas_readings)
     (tp with vs_inst_idx := i)` by
    (simp[] >> irule execEquivProofsTheory.state_equiv_inst_idx >> simp[]) >>
  `?gs:(256 word) list.
     LENGTH (FILTER (\w. w <> 0w) gs) <=
       LENGTH (FILTER (\w. w <> 0w) (tp with vs_inst_idx := i).vs_gas_readings) /\
     ?err. exec_block N ctx bb ((sp with vs_inst_idx := i) with vs_gas_readings := gs) = Error err` by
    (irule remove_unused_block_error_reconstruction >>
     simp[] >> qexistsl [`V`, `lr`] >>
     gvs[Abbr `mb`] >> metis_tac[]) >>
  qexists_tac `gs` >> gvs[]
QED

Finalise remove_unused_run_block_error_reconstruction

Theorem remove_unused_run_blocks_error_reconstruction:
  !N ctx lr V fn fn' s t.
    (!lbl. lookup_block lbl fn'.fn_blocks =
      OPTION_MAP (\bb. clear_nops_block (remove_unused_block lr bb))
        (lookup_block lbl fn.fn_blocks)) /\
    (!bb. MEM bb fn.fn_blocks ==>
      (!i j. i < j /\ j < LENGTH bb.bb_instructions /\
        (EL j bb.bb_instructions).inst_opcode = PHI ==>
        (EL i bb.bb_instructions).inst_opcode = PHI) /\
      block_nop_outputs lr bb SUBSET V) /\
    (!bb inst v. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions /\
      MEM (Var v) inst.inst_operands ==> v NOTIN V) /\
    s.vs_inst_idx = 0 /\ t.vs_inst_idx = 0 /\
    state_equiv V (s with vs_gas_readings := t.vs_gas_readings) t /\
    (?e. run_blocks N ctx fn' t = Error e) ==>
    ?gs:(256 word) list.
      LENGTH (FILTER (\w. w <> 0w) gs) <=
        LENGTH (FILTER (\w. w <> 0w) t.vs_gas_readings) /\
      ?e. run_blocks N ctx fn (s with vs_gas_readings := gs) = Error e
Proof
  Induct_on `N`
  >- (rpt strip_tac >> qexists_tac `[]` >> simp[Once run_blocks_def]) >>
  rpt gen_tac >> strip_tac >>
  `s.vs_current_bb = t.vs_current_bb` by
    gvs[state_equiv_def, execution_equiv_def, stateFrameTheory.execution_frame_def] >>
  Cases_on `lookup_block t.vs_current_bb fn.fn_blocks`
  >- (qexists_tac `[]` >> simp[Once run_blocks_unfold]) >>
  rename1 `lookup_block t.vs_current_bb fn.fn_blocks = SOME bb` >>
  qabbrev_tac `cb = clear_nops_block (remove_unused_block lr bb)` >>
  `lookup_block t.vs_current_bb fn'.fn_blocks = SOME cb` by simp[Abbr `cb`] >>
  `MEM bb fn.fn_blocks` by metis_tac[venomExecPropsTheory.lookup_block_MEM] >>
  Cases_on `?e. run_block N ctx cb t = Error e`
  >- (`?gs:(256 word) list.
       LENGTH (FILTER (\w. w <> 0w) gs) <=
         LENGTH (FILTER (\w. w <> 0w) t.vs_gas_readings) /\
       ?e. run_block N ctx bb (s with vs_gas_readings := gs) = Error e` by
        (irule remove_unused_run_block_error_reconstruction >>
         simp[] >> conj_tac >- metis_tac[] >>
         qexistsl [`V`, `lr`] >> gvs[Abbr `cb`] >> metis_tac[]) >>
      qexists_tac `gs` >> simp[Once run_blocks_unfold]) >>
  Cases_on `run_block N ctx cb t` >>
  gvs[Once run_blocks_unfold] >>
  suspend "continue"
QED

Resume remove_unused_run_blocks_error_reconstruction[continue]:
  `v.vs_inst_idx = 0 /\ ~v.vs_halted` by
    metis_tac[venomExecPropsTheory.run_block_OK_inst_idx_0,
      venomExecPropsTheory.run_block_OK_not_halted] >>
  gvs[] >>
  `?gc:(256 word) list.
     LENGTH (FILTER (\w. w <> 0w) gc) <=
       LENGTH (FILTER (\w. w <> 0w) v.vs_gas_readings) /\
     ?e. run_blocks N ctx fn (v with vs_gas_readings := gc) = Error e` by
    (qpat_assum `!ctx lr V fn fn' s t. _` irule >>
     simp[stateEquivPropsTheory.state_equiv_refl] >>
     qexistsl [`V`, `fn'`, `lr`] >> simp[] >> metis_tac[]) >>
  qpat_x_assum `!ctx lr V fn fn' s t. _` kall_tac >>
  `?nb. gas_replay_at nb (run_block N ctx cb) t` by
    (rewrite_tac[GSYM gas_replay_def] >> irule gas_run_block >>
     metis_tac[cj 3 gas_replay_fuel]) >>
  `?p:(256 word) list.
      LENGTH (FILTER (\w. w <> 0w) p) <=
        LENGTH (FILTER (\w. w <> 0w) (gas_prefix nb t.vs_gas_readings)) /\
      (!tail.
        (?e. e <> "out of fuel" /\
          run_block N ctx bb (s with vs_gas_readings := p ++ tail) = Error e) \/
        lift_result (state_equiv V) (execution_equiv V) (execution_equiv V)
          (run_block N ctx bb (s with vs_gas_readings := p ++ tail))
          (run_block N ctx cb
            (t with vs_gas_readings := gas_prefix nb t.vs_gas_readings ++ tail))) /\
      (!tail k. k <= N /\
        (?e. run_block k ctx cb
          (t with vs_gas_readings := gas_prefix nb t.vs_gas_readings ++ tail) = Error e) ==>
        ?e. run_block k ctx bb (s with vs_gas_readings := p ++ tail) = Error e)` by
    (simp[Abbr `cb`] >> irule remove_unused_run_block_prefix_reconstruction_aligned >>
     simp[] >> metis_tac[]) >>
  qpat_x_assum `!tail k. k <= N /\ _ ==> _` kall_tac >>
  qpat_x_assum `!lbl. lookup_block lbl _ = _` kall_tac >>
  qpat_x_assum `!bb. MEM bb _ ==> _` kall_tac >>
  qpat_x_assum `run_blocks N ctx fn' v = Error e` kall_tac >>
  suspend "assemble"
QED

Resume remove_unused_run_blocks_error_reconstruction[assemble]:
  `v.vs_gas_readings = DROP nb t.vs_gas_readings` by
    (qpat_x_assum `gas_replay_at nb (run_block N ctx cb) t` mp_tac >>
     simp[gas_replay_at_def] >> disch_then (qspec_then `[]` mp_tac) >>
     Cases_on `run_block N ctx cb
       (t with vs_gas_readings := gas_prefix nb t.vs_gas_readings)` >>
     simp[lift_result_def] >> metis_tac[]) >>
  `run_block N ctx cb
      (t with vs_gas_readings := gas_prefix nb t.vs_gas_readings ++ gc) =
    OK (v with vs_gas_readings := gc)` by
    (qpat_x_assum `gas_replay_at nb (run_block N ctx cb) t` mp_tac >>
     simp[gas_replay_at_def] >> disch_then (qspec_then `gc` mp_tac) >>
     Cases_on `run_block N ctx cb
       (t with vs_gas_readings := gas_prefix nb t.vs_gas_readings ++ gc)` >>
     simp[lift_result_def]) >>
  qexists_tac `p ++ gc` >> conj_tac
  >- (mp_tac (Q.SPECL [`nb`, `t.vs_gas_readings`] remove_unused_actual_oracle_nonzero) >>
      gvs[FILTER_APPEND] >> decide_tac) >>
  qpat_x_assum `!tail. (?e. _ /\ _) \/ _` (qspec_then `gc` mp_tac) >>
  simp[] >> strip_tac
  >- simp[Once run_blocks_unfold] >>
  Cases_on `run_block N ctx bb (s with vs_gas_readings := p ++ gc)` >>
  gvs[lift_result_def] >>
  rename1 `state_equiv V u (v with vs_gas_readings := gc)` >>
  `~u.vs_halted` by
    gvs[state_equiv_def, execution_equiv_def, stateFrameTheory.execution_frame_def] >>
  `lift_result (state_equiv V) (execution_equiv V) (execution_equiv V)
     (run_blocks N ctx fn u)
     (run_blocks N ctx fn (v with vs_gas_readings := gc))` by
    (irule remove_unused_runner_state_transport >> simp[] >> first_assum ACCEPT_TAC) >>
  Cases_on `run_blocks N ctx fn u` >>
  gvs[lift_result_def, Once run_blocks_unfold]
QED

Finalise remove_unused_run_blocks_error_reconstruction

Theorem remove_unused_single_pass_error_reconstruction:
  !N ctx fn s t.
    wf_function fn /\ wf_ssa fn /\ ssa_form fn /\
    s.vs_inst_idx = 0 /\ t.vs_inst_idx = 0 /\
    state_equiv (single_pass_nop_outputs fn)
      (s with vs_gas_readings := t.vs_gas_readings) t /\
    (?e. run_blocks N ctx (remove_unused_single_pass fn) t = Error e) ==>
    ?gs:(256 word) list.
      LENGTH (FILTER (\w. w <> 0w) gs) <=
        LENGTH (FILTER (\w. w <> 0w) t.vs_gas_readings) /\
      ?e. run_blocks N ctx fn (s with vs_gas_readings := gs) = Error e
Proof
  rpt gen_tac >> strip_tac >>
  irule remove_unused_run_blocks_error_reconstruction >> simp[] >>
  qexistsl [`single_pass_nop_outputs fn`, `remove_unused_single_pass fn`,
    `protect_liveness fn (remove_unused_phi_vars fn) (liveness_analyze fn)`] >>
  simp[remove_unused_single_pass_lookup_block] >>
  metis_tac[remove_unused_wf_phi_prefix, block_nop_outputs_subset_single_pass,
            nop_output_not_used_as_operand]
QED

Theorem remove_unused_run_blocks_error_downward:
  !N ctx fn s k.
    (?e. run_blocks N ctx fn s = Error e) /\ k <= N ==>
    ?e. run_blocks k ctx fn s = Error e
Proof
  rpt strip_tac >> Cases_on `run_blocks k ctx fn s` >> simp[] >>
  drule (cj 3 fuel_mono) >> simp[] >> qexists_tac `N` >> simp[]
QED

Theorem remove_unused_single_pass_permanent_error_reconstruction:
  !ctx fn s t.
    wf_function fn /\ wf_ssa fn /\ ssa_form fn /\
    s.vs_inst_idx = 0 /\ t.vs_inst_idx = 0 /\
    state_equiv (single_pass_nop_outputs fn)
      (s with vs_gas_readings := t.vs_gas_readings) t /\
    (!fuel. ?e. run_blocks fuel ctx (remove_unused_single_pass fn) t = Error e) ==>
    ?gs:(256 word) list.
      LENGTH (FILTER (\w. w <> 0w) gs) <=
        LENGTH (FILTER (\w. w <> 0w) t.vs_gas_readings) /\
      !fuel. ?e. run_blocks fuel ctx fn (s with vs_gas_readings := gs) = Error e
Proof
  rpt gen_tac >> strip_tac >>
  ho_match_mp_tac remove_unused_sparse_oracle_compactness >> conj_tac
  >- (gen_tac >>
      `?gs:(256 word) list.
         LENGTH (FILTER (\w. w <> 0w) gs) <=
           LENGTH (FILTER (\w. w <> 0w) t.vs_gas_readings) /\
         ?e. run_blocks n ctx fn (s with vs_gas_readings := gs) = Error e` by
        (irule remove_unused_single_pass_error_reconstruction >> simp[] >>
         qexists_tac `t` >> simp[]) >>
      qexists_tac `gs` >> simp[] >> rpt strip_tac >>
      irule remove_unused_run_blocks_error_downward >>
      qexists_tac `n` >> simp[]) >>
  simp[remove_unused_gas_error_finite_dependence]
QED
