Theory staticAbortOptPruneJumps
Ancestors
  staticAbortOptPruneJumpsWalk staticAbortOptPruneJumpsStopped
  staticAbortOptPruneJumpsArms staticAbortOptPruneUnreachableZeroOrigin
  staticAbortOptPruneUnreachableLayout staticAbortOptPruneUnreachableCheck
  staticAbortProtectedActualPrefix staticAbortRoleStep staticAbortOptMergeIszeroBranchPackage
  asmOptOwnPruneJumps asmDataEnv asmSplice asmSymPc
  asmSem asmSymSem asmSymBridge asmWf asmOptimizer finite_map pred_set
  words arithmetic list rich_list

(* Eliminate naming premises when matching a worker's specialized result. *)
val prune_alias_conv = REDEPTH_CONV (FIRST_CONV
  [Unwind.UNWIND_FORALL_CONV, REWR_CONV LET_THM, BETA_CONV]);
val prune_specialize = CONV_RULE prune_alias_conv;
fun prune_introduce names = map_every (fn name => qx_gen_tac name >>
  disch_then (assume_tac o
    CONV_RULE (RAND_CONV (REDEPTH_CONV Unwind.UNWIND_FORALL_CONV)))) names;

(* Only the two non-label instructions are removed. The retained index
   used for a fetch is distinct from the splice boundary used for a cut. *)
Theorem prune_jump_layout[local]:
  !p. p = pre ++ [AsmPushLabel x; AsmOp "JUMP"; AsmLabel x] ++ tail ==>
  !q. q = pre ++ [AsmLabel x] ++ tail ==>
  !b. b = LENGTH pre ==>
  !r. r = splice_pc b 2 0 ==>
  asm_static_wf p ==>
  asm_static_wf q /\ FILTER is_data_inst q = FILTER is_data_inst p /\
  (!i. i < LENGTH p /\ i <> b /\ i <> b+1 ==>
       r i < LENGTH q /\ EL (r i) q = EL i p) /\
  (!l i. INDEX_OF (AsmLabel l) p = SOME i ==>
       i <> b /\ i <> b+1 /\ INDEX_OF (AsmLabel l) q = SOME (r i))
Proof
  CONV_TAC prune_alias_conv >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >> strip_tac >>
  `asm_static_wf (pre ++ AsmLabel x :: tail) /\
   FILTER is_data_inst (pre ++ AsmLabel x :: tail) =
   FILTER is_data_inst (pre ++ AsmPushLabel x :: AsmOp "JUMP" :: AsmLabel x :: tail)` by
    (mp_tac (Q.INST [`pat` |-> `[AsmPushLabel x; AsmOp "JUMP"]`,
                     `repl` |-> `[]:asm_inst list`, `pfx` |-> `pre`,
                     `sfx` |-> `AsmLabel x :: tail`] asm_splice_static_wf) >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
     simp[asm_splice_ok_def, is_data_inst_def, asm_label_refs_def,
          symbolResolveTheory.asm_inst_size_def]) >>
  asm_rewrite_tac[] >> conj_tac
  >- (gen_tac >> strip_tac >>
      mp_tac (Q.INST [`pat` |-> `[AsmPushLabel x; AsmOp "JUMP"]`,
                      `repl` |-> `[]:asm_inst list`, `pfx` |-> `pre`,
                      `sfx` |-> `AsmLabel x :: tail`]
               (INST_TYPE [alpha |-> ``:asm_inst``] splice_fetch)) >>
      pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
      (impl_tac >- (simp[] >> decide_tac)) >> simp[]) >>
  rpt gen_tac >> strip_tac >>
  mp_tac (Q.INST [`pat` |-> `[AsmPushLabel x; AsmOp "JUMP"]`,
                  `repl` |-> `[]:asm_inst list`, `pfx` |-> `pre`,
                  `sfx` |-> `AsmLabel x :: tail`] splice_index_of_label) >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  simp[] >> strip_tac >>
  qpat_x_assum `!i. INDEX_OF _ _ = SOME i ==> _` (qspec_then `i` mp_tac) >>
  simp[] >> decide_tac
QED

(* The label name survives the contraction, but its assembled word changes. *)
Theorem prune_jump_taken_layout[local]:
  !p. p = pre ++ [AsmPushLabel x; AsmOp "JUMP"; AsmLabel x] ++ tail ==>
  !q. q = pre ++ [AsmLabel x] ++ tail ==>
  asm_static_wf p /\ FLOOKUP (SND (compute_label_offsets p)) l = SOME old /\
  FLOOKUP (build_offset_to_pc p) old = SOME dest ==>
  ?fresh. FLOOKUP (SND (compute_label_offsets q)) l = SOME fresh /\
          fresh < dimword(:256) /\ FLOOKUP (build_offset_to_pc q) fresh = SOME (splice_pc (LENGTH pre) 2 0 dest)
Proof
  CONV_TAC prune_alias_conv >>
  qabbrev_tac `p = pre ++ [AsmPushLabel x; AsmOp "JUMP"; AsmLabel x] ++ tail` >>
  qabbrev_tac `q = pre ++ [AsmLabel x] ++ tail` >>
  strip_tac >>
  drule_all staticAbortOptPruneUnreachableLayoutTheory.lookup_pair_code_label_index >>
  strip_tac >>
  `asm_static_wf q /\ INDEX_OF (AsmLabel l) q = SOME (splice_pc (LENGTH pre) 2 0 dest)` by
    (mp_tac (prune_specialize prune_jump_layout) >>
     simp[Abbr `p`, Abbr `q`] >> metis_tac[]) >>
  drule_all asm_static_wf_code_label >>
  disch_then (qx_choose_then `fresh` strip_assume_tac) >>
  qexists `fresh` >> asm_rewrite_tac[] >>
  irule vyperArithTheory.lt_dimword_256 >> qexists `16` >> simp[]
QED

(* At the interior cut the destination replays to the state before the
   erased push. At all other cuts the symbolic stack is unchanged. *)
Theorem prune_jump_actual_root[local]:
  !p. p = pre ++ [AsmPushLabel x; AsmOp "JUMP"; AsmLabel x] ++ tail ==>
  !q. q = pre ++ [AsmLabel x] ++ tail ==>
  !b. b = LENGTH pre ==>
  !eq. eq = asm_data_env q (assemble q ++ data) ==>
  s.as_pc = 0 /\ asm_static_wf p /\ s.as_code = assemble p ++ data /\
  sym_steps p (asm_data_env p (assemble p ++ data)) n (sym_init s) = SymOK ss ==>
  asm_static_wf q /\ FILTER is_data_inst q = FILTER is_data_inst p /\
  ?j v t.
    sym_steps q eq j (sym_init (s with as_code := assemble q ++ data)) = SymOK v /\
    asm_steps (SND(compute_label_offsets q)) (build_offset_to_pc q) q j
      (s with as_code := assemble q ++ data) = AsmOK t /\
    asm_sym_rel q eq t v /\
    t.as_pc = (if ss.sym_base.as_pc = b+1 then b else splice_pc b 2 0 ss.sym_base.as_pc) /\
    t.as_call_ctx = ss.sym_base.as_call_ctx /\
    t.as_requests = ss.sym_base.as_requests /\ LENGTH t.as_stack = LENGTH v.sym_stack /\
    (if ss.sym_base.as_pc = b+1 then ss.sym_stack = Lab x 0 :: v.sym_stack
     else ss.sym_stack = v.sym_stack)
Proof
  CONV_TAC prune_alias_conv >>
  qabbrev_tac `p = pre ++ [AsmPushLabel x; AsmOp "JUMP"; AsmLabel x] ++ tail` >>
  qabbrev_tac `q = pre ++ [AsmLabel x] ++ tail` >>
  strip_tac >>
  `asm_static_wf q /\ FILTER is_data_inst q = FILTER is_data_inst p` by
    (mp_tac (prune_specialize prune_jump_layout) >>
     simp[Abbr `p`, Abbr `q`] >> metis_tac[]) >>
  asm_rewrite_tac[] >>
  qabbrev_tac `ep = asm_data_env p (assemble p ++ data)` >>
  (`?j v. sym_steps q ep j (sym_init s) = SymOK v /\
          v.sym_base.as_pc = (if ss.sym_base.as_pc = LENGTH pre+1 then LENGTH pre
                              else splice_pc (LENGTH pre) 2 0 ss.sym_base.as_pc) /\
          v.sym_base.as_call_ctx = ss.sym_base.as_call_ctx /\
          v.sym_base.as_requests = ss.sym_base.as_requests /\
          (if ss.sym_base.as_pc = LENGTH pre+1 then ss.sym_stack = Lab x 0 :: v.sym_stack
           else ss.sym_stack = v.sym_stack)` by
    (mp_tac (Q.INST [`n` |-> `n`, `env` |-> `ep`]
              (prune_specialize prune_jump_site_stopped_prefix)) >>
     qpat_assum `Abbrev (p = _)`
       (fn th => rewrite_tac [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]) >>
     qpat_assum `Abbrev (q = _)`
       (fn th => rewrite_tac [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]) >>
     (impl_tac >- asm_rewrite_tac[]) >>
     Cases_on `ss.sym_base.as_pc = LENGTH pre+1` >>
     asm_rewrite_tac[] >> strip_tac
     >- (qexistsl [`j`, `u`] >> fs[sym_with_pc_def]) >>
     qexistsl [`j`, `sym_with_pc (splice_pc (LENGTH pre) 2 0 ss.sym_base.as_pc) ss`] >>
     simp[sym_with_pc_def])) >>
  (`?t. asm_steps (SND(compute_label_offsets q)) (build_offset_to_pc q) q j
          (s with as_code := assemble q ++ data) = AsmOK t /\
        asm_sym_rel q (asm_data_env q (assemble q ++ data)) t v /\
        t.as_pc = v.sym_base.as_pc /\ LENGTH t.as_stack = LENGTH v.sym_stack /\
        t.as_call_ctx = v.sym_base.as_call_ctx /\ t.as_requests = v.sym_base.as_requests` by
    (irule stopped_symbolic_prefix_actual_code >> simp[] >>
     qexists `p` >> fs[Abbr `ep`])) >>
  qexistsl [`j`, `v`, `t`] >>
  `asm_data_env q (assemble q ++ data) = ep` by
    (simp[Abbr `ep`] >> metis_tac[asm_data_env_agree]) >>
  `sym_init (s with as_code := assemble q ++ data) = sym_init s` by simp[sym_init_def] >>
  simp[]
QED

(* The bypass already accounts for the pop at an interior cut. Apply
   precisely its slot shift to the demands justified by stopped replay. *)
Theorem prune_jump_root_slots[local]:
  !b. b = LENGTH (pre:asm_inst list) ==>
  !r. r = splice_pc b 2 0 ==>
  !d. d = (if pc (e:num#num) = b+1 then 1 else 0) ==>
  !Demand. Demand = (\w stack.
    (!k l org. tag w k = SOME(l,org) ==>
       k < LENGTH stack /\ EL k stack = Lab l 0) /\
    (!k. boolean w k ==> k < LENGTH stack /\
       (EL k stack = Val 0w \/ EL k stack = Val 1w))) ==>
  e IN V /\ t.as_pc = (if pc e = b+1 then b else r (pc e)) /\
  LENGTH t.as_stack = LENGTH dst /\ height e = LENGTH src /\
  (if pc e = b+1 then src = Lab x 0 :: dst else src = dst) /\
  Demand e src /\
  ((pc e = b \/ (pc e = b+1 /\ (!l org. tag e 0 = SOME(l,org) ==> l=x))) ==>
   ?z. z IN V /\ pc z = b+2 /\ height e = height z + d /\
       (!k l org. tag z k = SOME(l,org) ==> tag e (k+d) = SOME(l,org)) /\
       (!k. boolean z k ==> boolean e (k+d))) ==>
  ?z. z IN V /\ pc z <> b /\ pc z <> b+1 /\ r (pc z) = t.as_pc /\
      height z = LENGTH t.as_stack /\ Demand z dst
Proof
  CONV_TAC prune_alias_conv >>
  qabbrev_tac `b = LENGTH pre` >> strip_tac >>
  Cases_on `pc e = b+1`
  >- (`pc e <> b` by decide_tac >>
      gvs[] >>
      `!l org. tag e 0 = SOME(l,org) ==> l=x` by
        (map_every qx_gen_tac [`l`,`org`] >>
         disch_then (fn tag0 =>
           qpat_assum `!k l org. tag e k = SOME(l,org) ==> _`
             (qspecl_then [`0`,`l`,`org`] mp_tac) >>
           pure_rewrite_tac[tag0, EL, HD, sval_11] >> simp[])) >>
      qpat_x_assum `_ ==> ?z. _` (drule_then (qx_choose_then `z` strip_assume_tac)) >>
      qexists `z` >> simp[splice_pc_def] >>
      gvs[GSYM ADD1, EL] >> conj_tac
      >- (map_every qx_gen_tac [`k`,`l`,`org`] >> strip_tac >>
          qpat_assum `!k l org. tag z k = SOME(l,org) ==> _`
            (drule_then assume_tac) >>
          qpat_assum `!k l org. tag e k = SOME(l,org) ==> _`
            (drule_then mp_tac) >>
          pure_rewrite_tac[EL, TL, LESS_MONO_EQ] >> disch_then ACCEPT_TAC) >>
      qx_gen_tac `k` >> strip_tac >>
      qpat_assum `!k. boolean z k ==> _` (drule_then assume_tac) >>
      qpat_assum `!k. boolean e k ==> _` (drule_then mp_tac) >>
      pure_rewrite_tac[EL, TL, LESS_MONO_EQ] >> disch_then ACCEPT_TAC) >>
  Cases_on `pc e = b`
  >- (gvs[] >>
      qexists `z` >> gvs[splice_pc_def] >> metis_tac[]) >>
  qexists `e` >> gvs[]
QED

(* Select the surviving root of the cut before constructing retained arms. *)
Theorem prune_jump_replayed_root[local]:
  !Shape. Shape =
    (\p cc req pc height need tag boolean i (t:asm_state).
      t.as_pc = pc i /\ LENGTH t.as_stack = height i /\
      t.as_call_ctx = cc /\ t.as_requests = req /\
      (need i ==> t.as_call_ctx.cc_static) /\
      (!k l origin. tag i k = SOME(l,origin) ==>
         k < height i /\ origin < LENGTH p /\
         (EL origin p = AsmPushLabel l \/
          (?d. EL origin p = AsmPushOfst l d) \/ EL origin p = AsmDataLabel l) /\
         ?off dest.
           FLOOKUP (SND(compute_label_offsets p)) l = SOME off /\
           off < dimword(:256) /\
           FLOOKUP (build_offset_to_pc p) off = SOME dest /\
           EL k t.as_stack = (n2w off:bytes32)) /\
      (!k. boolean i k ==> k < height i /\
         (EL k t.as_stack = 0w \/ EL k t.as_stack = 1w))) ==>
  !Flow. Flow =
    (\p pc height tag boolean (x:num#num) (y:num#num).
    !hi. hi = height x ==>
    !hj. hj = height y ==>
    !ins. ins = EL (pc x) p ==>
    !inherit. inherit =
      (\(src:num -> num option)
        (fresh:num -> (string#num)option) (bnew:num -> bool).
        (!k l origin. tag y k = SOME(l,origin) ==>
           k < hj /\ (fresh k = SOME(l,origin) \/
           ?a. src k = SOME a /\ a < hi /\ tag x a = SOME(l,origin))) /\
        (!k. boolean y k ==> k < hj /\
           (bnew k \/ ?a. src k = SOME a /\ a < hi /\ boolean x a))) ==>
    case ins of
      AsmLabel l => hj = hi /\ inherit (\k. SOME k) (\k. NONE) (\k. F)
    | AsmPush bs =>
        hj = hi+1 /\
        inherit (\k. if k=0 then NONE else SOME(k-1)) (\k. NONE)
          (\k. k=0 /\ !t u.
            asm_step (SND(compute_label_offsets p)) (build_offset_to_pc p)
              (AsmPush bs) t = AsmOK u ==>
            (EL 0 u.as_stack = 0w \/ EL 0 u.as_stack = 1w))
    | AsmPushLabel l =>
        hj = hi+1 /\
        inherit (\k. if k=0 then NONE else SOME(k-1))
          (\k. if k=0 then SOME(l,pc x) else NONE) (\k. F)
    | AsmPushOfst l d =>
        hj = hi+1 /\
        inherit (\k. if k=0 then NONE else SOME(k-1))
          (\k. if k=0 /\ d=0 then SOME(l,pc x) else NONE) (\k. F)
    | AsmOp name =>
        (case ALOOKUP dup_table name of
           SOME n =>
             n < hi /\ hj = hi+1 /\
             inherit (\k. SOME(if k=0 then n else k-1)) (\k. NONE) (\k. F)
         | NONE =>
           case ALOOKUP swap_table name of
             SOME n =>
               0 < n /\ n < hi /\ hj = hi /\
               inherit (\k. SOME(if k=0 then n else if k=n then 0 else k))
                 (\k. NONE) (\k. F)
             | NONE =>
               !a. a = asm_op_arity name ==>
               !m. m = hj + a - hi ==>
               a <= hi /\ hj = m+(hi-a) /\
               ((name="JUMP" \/ name="JUMPI") ==> m=0) /\
               inherit (\k. if k<m then NONE else SOME(k-m+a)) (\k. NONE)
                 (\k. k=0 /\ m=1 /\ asm_returns_zero_or_one ins /\
                   !t u. LENGTH t.as_stack=hi /\
                     asm_step (SND(compute_label_offsets p)) (build_offset_to_pc p)
                       ins t = AsmOK u ==>
                     (EL 0 u.as_stack=0w \/ EL 0 u.as_stack=1w)))
    | _ => F) ==>
  !Open. Open =
    (\p cc req (V:(num#num)->bool) X (rank:(num#num)->num) pc height need
      (tag:(num#num)->num->(string#num)option)
      (boolean:(num#num)->num->bool) edge.
    !S. S = Shape p cc req pc height need tag boolean ==>
    !target. target = (\x y.
      ?l origin off. tag x 0 = SOME(l,origin) /\
        FLOOKUP (SND(compute_label_offsets p)) l = SOME off /\
        off < dimword(:256) /\
        FLOOKUP (build_offset_to_pc p) off = SOME(pc y)) ==>
      FINITE V /\ X SUBSET V /\
      (!x. x IN V ==> ?t. S x t) /\
      (!x. x IN V DIFF X ==> pc x < LENGTH p) /\
      (!x y. edge x y ==>
         x IN V DIFF X /\ y IN V /\ rank y < rank x /\
         Flow p pc height tag boolean x y /\
         (if EL (pc x) p = AsmOp "JUMP" then target x y
          else if EL (pc x) p = AsmOp "JUMPI"
               then pc y = pc x+1 \/ target x y
          else pc y = pc x+1)) /\
      (!x t. x IN V DIFF X /\ S x t ==>
         (?u. (asm_steps (SND(compute_label_offsets p)) (build_offset_to_pc p)
                      p 1 t = AsmRevert u \/
                asm_steps (SND(compute_label_offsets p)) (build_offset_to_pc p)
                      p 1 t = AsmFault u) /\ u.as_requests=req) \/
         (?y u. edge x y /\
            asm_steps (SND(compute_label_offsets p)) (build_offset_to_pc p)
              p 1 t = AsmOK u /\ S y u))) ==>
  !p. p = pre ++ [AsmPushLabel x; AsmOp "JUMP"; AsmLabel x] ++ tail ==>
  !q. q = pre ++ [AsmLabel x] ++ tail ==>
  !b. b = LENGTH pre ==>
  !Demand. Demand = (\w stack.
    (!k l org. tag w k = SOME(l,org) ==>
       k < LENGTH stack /\ EL k stack = Lab l 0) /\
    (!k. boolean w k ==> k < LENGTH stack /\
       (EL k stack = Val 0w \/ EL k stack = Val 1w))) ==>
  s.as_pc = 0 /\ s.as_code = assemble p ++ data /\ asm_static_wf p /\
  sym_steps p (asm_data_env p (assemble p ++ data)) n (sym_init s) = SymOK ss /\
  Open p cc req V {} rank pc height need tag boolean edge /\
  e IN V /\ ss.sym_base.as_pc = pc e /\ height e = LENGTH ss.sym_stack /\
  ss.sym_base.as_call_ctx = cc /\ ss.sym_base.as_requests = req /\ Demand e ss.sym_stack ==>
  asm_static_wf q /\ FILTER is_data_inst q = FILTER is_data_inst p /\
  ?j v t z.
    sym_steps q (asm_data_env q (assemble q ++ data)) j
      (sym_init (s with as_code := assemble q ++ data)) = SymOK v /\
    asm_steps (SND(compute_label_offsets q)) (build_offset_to_pc q) q j
      (s with as_code := assemble q ++ data) = AsmOK t /\
    asm_sym_rel q (asm_data_env q (assemble q ++ data)) t v /\
    t.as_call_ctx = cc /\ t.as_requests = req /\
    z IN V /\ pc z <> b /\ pc z <> b+1 /\ splice_pc b 2 0 (pc z) = t.as_pc /\
    height z = LENGTH t.as_stack /\ Demand z v.sym_stack
Proof
  prune_introduce [`Shape`,`Flow`,`Open`,`p`,`q`,`b`,`Demand`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `asm_static_wf q /\ FILTER is_data_inst q = FILTER is_data_inst p /\
   ?j v t.
     sym_steps q (asm_data_env q (assemble q ++ data)) j
       (sym_init (s with as_code := assemble q ++ data)) = SymOK v /\
     asm_steps (SND(compute_label_offsets q)) (build_offset_to_pc q) q j
       (s with as_code := assemble q ++ data) = AsmOK t /\
     asm_sym_rel q (asm_data_env q (assemble q ++ data)) t v /\
     t.as_pc = (if pc e = b+1 then b else splice_pc b 2 0 (pc e)) /\
     t.as_call_ctx = cc /\ t.as_requests = req /\ LENGTH t.as_stack = LENGTH v.sym_stack /\
     (if pc e = b+1 then ss.sym_stack = Lab x 0 :: v.sym_stack else ss.sym_stack = v.sym_stack)`
    by suspend "actual" >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  qexistsl [`j`,`v`,`t`] >>
  mp_tac (Q.INST [`src` |-> `ss.sym_stack`, `dst` |-> `v.sym_stack`]
    (SPEC_ALL (prune_specialize (INST_TYPE [alpha |-> ``:num``] prune_jump_root_slots)))) >>
  pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  qpat_assum `b = LENGTH pre` (fn th => pure_rewrite_tac[GSYM th]) >>
  (impl_tac >- suspend "bypass") >>
  disch_then (qx_choose_then `z` strip_assume_tac) >> qexists `z` >>
  ntac 5 (conj_tac >- first_assum ACCEPT_TAC) >>
  fs[]
QED

Resume prune_jump_replayed_root[actual]:
  mp_tac (Q.INST [`ss` |-> `ss`, `n` |-> `n`, `s` |-> `s`, `data` |-> `data`]
    (SPEC_ALL (prune_specialize prune_jump_actual_root))) >>
  pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  qpat_assum `(p:asm_inst list) = _` (fn th => pure_rewrite_tac[GSYM th]) >>
  qpat_assum `(q:asm_inst list) = _` (fn th => pure_rewrite_tac[GSYM th]) >>
  (impl_tac >- (ntac 3 (conj_tac >- first_assum ACCEPT_TAC) >> first_assum ACCEPT_TAC)) >>
  qpat_assum `b = LENGTH pre` (fn th => pure_rewrite_tac[GSYM th]) >>
  asm_rewrite_tac[]
QED

Resume prune_jump_replayed_root[bypass]:
  qpat_assum `Demand e ss.sym_stack` mp_tac >>
  qpat_assum `Demand = _` (fn th => pure_rewrite_tac[th]) >>
  CONV_TAC (REDEPTH_CONV BETA_CONV) >>
  disch_then strip_assume_tac >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  disch_tac >>
  mp_tac (Q.INST [`v` |-> `e`]
    (SPEC_ALL (prune_specialize staticAbortOptPruneJumpsBypassTheory.prune_jump_site_bypass))) >>
  pure_rewrite_tac[LET_THM] >> BETA_TAC >>
  qpat_assum `b = LENGTH pre` (fn th => pure_rewrite_tac[GSYM th]) >>
  (impl_tac >- (
    ntac 2 (conj_tac >- first_assum ACCEPT_TAC) >>
    (reverse conj_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
    qpat_assum `Open _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
    qpat_assum `Open = _` (fn th => pure_rewrite_tac[th]) >>
    qpat_assum `Flow = _` (fn th => pure_rewrite_tac[th]) >>
    qpat_assum `Shape = _` (fn th => pure_rewrite_tac[th]) >>
    simp[LET_THM, NoAsms] >>
    disch_then (map_every assume_tac o CONJUNCTS) >>
    (reverse conj_tac >- first_assum ACCEPT_TAC) >>
    rpt gen_tac >> disch_tac >>
    qpat_assum `!u w. edge u w ==> _` (drule_then strip_assume_tac) >>
    conj_tac >> first_assum ACCEPT_TAC)) >>
  `((if pc e = b then (0:num) else 1) = if pc e = b+1 then 1 else 0)` by
    (Cases_on `pc e = b` >- simp[] >> metis_tac[]) >>
  pop_assum (fn th => pure_rewrite_tac[th]) >>
  disch_then (qx_choose_then `z` (map_every assume_tac o CONJUNCTS)) >>
  qexists `z` >>
  ntac 4 (conj_tac >- first_assum ACCEPT_TAC) >> first_assum ACCEPT_TAC
QED

Finalise prune_jump_replayed_root

(* A source normal arm supplies its original slot map and output height.
   Contract it before changing the meanings of label tags. *)
Theorem prune_jump_retained_arm_flow[local]:
  !Inherit. Inherit = (\height tag boolean (u:num#num) (w:num#num) src fresh bnew.
    (!k l origin. tag w k = SOME(l,origin) ==>
       k < height w /\ (fresh k = SOME(l,origin) \/
       ?h. src k = SOME h /\ h < height u /\ tag u h = SOME(l,origin))) /\
    (!k. boolean w k ==> k < height w /\
       (bnew k \/ ?h. src k = SOME h /\ h < height u /\ boolean u h))) ==>
  !Shape. Shape =
    (\p cc req pc height need tag boolean i (t:asm_state).
      t.as_pc = pc i /\ LENGTH t.as_stack = height i /\
      t.as_call_ctx = cc /\ t.as_requests = req /\
      (need i ==> t.as_call_ctx.cc_static) /\
      (!k l origin. tag i k = SOME(l,origin) ==>
         k < height i /\ origin < LENGTH p /\
         (EL origin p = AsmPushLabel l \/
          (?d. EL origin p = AsmPushOfst l d) \/ EL origin p = AsmDataLabel l) /\
         ?off dest.
           FLOOKUP (SND(compute_label_offsets p)) l = SOME off /\
           off < dimword(:256) /\
           FLOOKUP (build_offset_to_pc p) off = SOME dest /\
           EL k t.as_stack = (n2w off:bytes32)) /\
      (!k. boolean i k ==> k < height i /\
         (EL k t.as_stack = 0w \/ EL k t.as_stack = 1w))) ==>
  !Flow. Flow =
    (\p pc height tag boolean (u:num#num) (w:num#num).
    !hi. hi = height u ==>
    !hj. hj = height w ==>
    !ins. ins = EL (pc u) p ==>
    !inherit. inherit = Inherit height tag boolean u w ==>
    case ins of
      AsmLabel l => hj = hi /\ inherit (\k. SOME k) (\k. NONE) (\k. F)
    | AsmPush bs =>
        hj = hi+1 /\
        inherit (\k. if k=0 then NONE else SOME(k-1)) (\k. NONE)
          (\k. k=0 /\ !t u.
            asm_step (SND(compute_label_offsets p)) (build_offset_to_pc p)
              (AsmPush bs) t = AsmOK u ==>
            (EL 0 u.as_stack = 0w \/ EL 0 u.as_stack = 1w))
    | AsmPushLabel l =>
        hj = hi+1 /\
        inherit (\k. if k=0 then NONE else SOME(k-1))
          (\k. if k=0 then SOME(l,pc u) else NONE) (\k. F)
    | AsmPushOfst l d =>
        hj = hi+1 /\
        inherit (\k. if k=0 then NONE else SOME(k-1))
          (\k. if k=0 /\ d=0 then SOME(l,pc u) else NONE) (\k. F)
    | AsmOp name =>
        (case ALOOKUP dup_table name of
           SOME n =>
             n < hi /\ hj = hi+1 /\
             inherit (\k. SOME(if k=0 then n else k-1)) (\k. NONE) (\k. F)
         | NONE =>
           case ALOOKUP swap_table name of
             SOME n =>
               0 < n /\ n < hi /\ hj = hi /\
               inherit (\k. SOME(if k=0 then n else if k=n then 0 else k))
                 (\k. NONE) (\k. F)
           | NONE =>
               !a. a = asm_op_arity name ==>
               !m. m = hj + a - hi ==>
               a <= hi /\ hj = m+(hi-a) /\
               ((name="JUMP" \/ name="JUMPI") ==> m=0) /\
               inherit (\k. if k<m then NONE else SOME(k-m+a)) (\k. NONE)
                 (\k. k=0 /\ m=1 /\ asm_returns_zero_or_one ins /\
                   !t v. LENGTH t.as_stack=hi /\
                     asm_step (SND(compute_label_offsets p)) (build_offset_to_pc p)
                       ins t = AsmOK v ==>
                     (EL 0 v.as_stack=0w \/ EL 0 v.as_stack=1w)))
    | _ => F) ==>
  !Target. Target = (\p (u:num#num) w.
    ?l origin off. tag u 0 = SOME(l,origin) /\
      FLOOKUP (SND(compute_label_offsets p)) l = SOME off /\
      off < dimword(:256) /\ FLOOKUP (build_offset_to_pc p) off = SOME(pc w)) ==>
  !Open. Open = (\p.
    !S. S = Shape p cc req pc height need tag boolean ==>
      FINITE V /\ {} SUBSET V /\
      (!u. u IN V ==> ?t. S u t) /\
      (!u. u IN V DIFF {} ==> pc u < LENGTH p) /\
      (!u w. edge u w ==>
         u IN V DIFF {} /\ w IN V /\ (rank:(num#num)->num) w < rank u /\
         Flow p pc height tag boolean u w /\
         (if EL (pc u) p = AsmOp "JUMP" then Target p u w
          else if EL (pc u) p = AsmOp "JUMPI"
               then pc w = pc u+1 \/ Target p u w
          else pc w = pc u+1)) /\
      (!u t. u IN V DIFF {} /\ S u t ==>
         (?v. (asm_steps (SND(compute_label_offsets p)) (build_offset_to_pc p)
                      p 1 t = AsmRevert v \/
                asm_steps (SND(compute_label_offsets p)) (build_offset_to_pc p)
                      p 1 t = AsmFault v) /\ v.as_requests=req) \/
         (?w v. edge u w /\
            asm_steps (SND(compute_label_offsets p)) (build_offset_to_pc p)
              p 1 t = AsmOK v /\ S w v))) ==>
  !p. p = pre ++ [AsmPushLabel x; AsmOp "JUMP"; AsmLabel x] ++ tail ==>
  !b. b = LENGTH pre ==>
  !r. r = splice_pc b 2 0 ==>
  !Keep. Keep = (\z. z IN V /\ pc z <> b /\ pc z <> b+1) ==>
  !Bypass. Bypass = (\z.
    Keep z /\ rank z < rank u /\ height z = height w /\
    (if pc w = b then pc z = b+2 else z = w) /\
    (if isTaken then z = w /\ Target p u z else r (pc z) = r (pc u) + 1)) ==>
  !q. q = pre ++ [AsmLabel x] ++ tail ==>
  asm_static_wf p /\ Open p /\ Keep u /\ edge u w /\
  (if isTaken then Target p u w else pc w = pc u+1) ==>
  ?z. Bypass z /\ Flow p pc height tag boolean u z /\
      (!k l. tag z k = SOME(l,b) ==> ?h. tag u h = SOME(l,b)) /\
      (isTaken ==> ?l origin off. tag u 0 = SOME(l,origin) /\
        FLOOKUP (SND(compute_label_offsets q)) l = SOME off /\
        off < dimword(:256) /\ FLOOKUP (build_offset_to_pc q) off = SOME(r (pc z))) /\
      (!rho. (!l. rho l (pc u) = r (pc u)) ==>
         Flow q (r o pc) height (\w k. OPTION_MAP (\(l,i). (l,rho l i)) (tag w k))
           boolean u z)
Proof
  prune_introduce [`Inherit`,`Shape`,`Flow`,`Target`,`Open`,`p`,`b`,`r`,`Keep`,`Bypass`,`q`] >>
  strip_tac >>
  `Keep u` by first_assum ACCEPT_TAC >>
  `pc u <> b /\ pc u <> b+1` by gvs[] >>
  `!src fresh bnew. Inherit height tag boolean u w src fresh bnew ==>
      ?z. Bypass z /\ Inherit height tag boolean u z src fresh bnew`
    by suspend "lift" >>
  `Flow p pc height tag boolean u w` by suspend "old_flow" >>
  `?z. Bypass z /\ Flow p pc height tag boolean u z` by suspend "rebuild" >>
  qexists `z` >> ntac 2 (conj_tac >- first_assum ACCEPT_TAC) >>
  (conj_tac >- suspend "deleted_inherited") >>
  (conj_tac >- (disch_tac >>
    qpat_assum `Bypass z` mp_tac >>
    qpat_assum `Bypass = _` (fn th => pure_rewrite_tac[th]) >> BETA_TAC >>
    qpat_assum `isTaken` (fn th => rewrite_tac[th, COND_CLAUSES]) >> strip_tac >>
    qpat_assum `Target p u _` mp_tac >>
    qpat_assum `Target = _` (fn th => pure_rewrite_tac[th]) >> BETA_TAC >> strip_tac >>
    suspend "taken_layout")) >>
  suspend "retag"
QED

Resume prune_jump_retained_arm_flow[lift]:
  rpt gen_tac >> disch_tac >>
  mp_tac (Q.INST [`legal` |-> `\a:bool. T`, `taken` |-> `\a:bool. isTaken`,
                 `v` |-> `\a:bool. w`, `H` |-> `height w`]
    (SPEC_ALL (prune_specialize
      (INST_TYPE [``:'arm`` |-> ``:bool``] prune_jump_site_retained_arms)))) >>
  simp_tac bool_ss [LET_THM, ADD_CLAUSES] >>
  qpat_assum `b = LENGTH pre` (fn th => pure_rewrite_tac[GSYM th]) >>
  qpat_assum `_ = splice_pc b 2 0` (fn th => pure_rewrite_tac[GSYM th]) >>
  (impl_tac >- (
    (conj_tac >- first_assum ACCEPT_TAC) >>
    (conj_tac >- first_assum ACCEPT_TAC) >>
    conj_tac
    >- (qpat_assum `Open p` mp_tac >>
        map_every (fn pat => qpat_assum pat (fn th => pure_rewrite_tac[th]))
          [`Open = _`, `Flow = _`, `Shape = _`, `Inherit = _`, `Target = _`] >>
        simp_tac bool_ss [LET_THM] >>
        disch_then (map_every assume_tac o CONJUNCTS) >>
        (reverse conj_tac >- first_assum ACCEPT_TAC) >>
        rpt gen_tac >> disch_tac >>
        qpat_assum `!u w. edge u w ==> _` (drule_then strip_assume_tac) >>
        conj_tac >> first_assum ACCEPT_TAC) >>
    ntac 3 (conj_tac >- first_assum ACCEPT_TAC) >>
    conj_tac
    >- (qpat_assum `Inherit height tag boolean u w src fresh bnew` mp_tac >>
        qpat_assum `Inherit = _` (fn th => pure_rewrite_tac[th]) >>
        BETA_TAC >> simp_tac bool_ss []) >>
    qpat_assum `if isTaken then Target p u w else _` mp_tac >>
    qpat_assum `Target = _` (fn th => pure_rewrite_tac[th]) >>
    BETA_TAC >> asm_rewrite_tac[])) >>
  disch_then (qx_choose_then `f` (qspec_then `F` strip_assume_tac)) >>
  `pc w <> b+1` by (strip_tac >> fs[]) >>
  qexists `f F` >>
  reverse conj_tac
  >- (qpat_assum `Inherit = _` (fn th => pure_rewrite_tac[th]) >>
      simp_tac bool_ss [] >>
      qpat_assum `!k l i. tag (f F) k = SOME (l,i) ==> _` mp_tac >>
      qpat_assum `!k. boolean (f F) k ==> _` mp_tac >>
      qpat_assum `(if pc w = b+1 then 1 else 0) = 0`
        (fn th => pure_rewrite_tac[th, ADD_CLAUSES]) >>
      POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
  qpat_assum `Bypass = _` (fn th => pure_rewrite_tac[th]) >>
  qpat_assum `Keep = _` (fn th => pure_rewrite_tac[th]) >>
  BETA_TAC >>
  qpat_x_assum `if pc w = b \/ pc w = b+1 then _ else _` mp_tac >>
  qpat_x_assum `if isTaken then f F = w /\ _ else _` mp_tac >>
  qpat_assum `Target = _` (fn th => pure_rewrite_tac[th]) >> BETA_TAC >>
  qpat_x_assum `(p:asm_inst list) = _` (fn th => pure_rewrite_tac[GSYM th]) >>
  qpat_assum `height (f F) + _ = height w` mp_tac >>
  qpat_assum `(if pc w = b+1 then 1 else 0) = 0`
    (fn th => pure_rewrite_tac[th, ADD_CLAUSES]) >>
  Cases_on `pc w = b` >> Cases_on `isTaken` >>
  asm_simp_tac std_ss [] >> rpt (disch_then strip_assume_tac) >>
  asm_simp_tac arith_ss [] >>
  simp[splice_pc_def]
QED

Resume prune_jump_retained_arm_flow[old_flow]:
  qpat_assum `Open p` mp_tac >>
  qpat_assum `Open = _` (fn th => pure_rewrite_tac[th]) >>
  simp_tac bool_ss [LET_THM, DIFF_EMPTY] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `!u w. edge u w ==> _` (drule_then strip_assume_tac) >>
  first_assum ACCEPT_TAC
QED

Resume prune_jump_retained_arm_flow[rebuild]:
  qpat_x_assum `Flow p pc height tag boolean u w` mp_tac >>
  qpat_assum `Flow = _` (fn th => pure_rewrite_tac[th]) >>
  simp_tac bool_ss [LET_THM] >>
  Cases_on `EL (pc u) p` >>
  qpat_assum `EL (pc u) p = _` (fn th => simp_tac (srw_ss()) [th,LET_THM]) >>
  TRY (qpat_assum `EL (pc u) p = AsmOp _` (K ALL_TAC) >>
    rename1 `EL (pc u) p = AsmOp name` >>
    Cases_on `ALOOKUP dup_table name` >>
    TRY (qpat_assum `ALOOKUP dup_table name = NONE` (K ALL_TAC) >>
         Cases_on `ALOOKUP swap_table name`) >>
    FILTER_ASM_REWRITE_TAC (can (match_term ``ALOOKUP _ _ = (_:num option)``)) [] >>
    simp_tac (srw_ss()) [LET_THM]) >>
  strip_tac >>
  qpat_assum `!src fresh bnew. Inherit height tag boolean u w src fresh bnew ==> _`
    (drule_then (qx_choose_then `z` strip_assume_tac)) >>
  `height z = height w` by
    (qpat_assum `Bypass z` mp_tac >>
     qpat_assum `Bypass = _` (fn th => pure_rewrite_tac[th]) >> BETA_TAC >> simp[]) >>
  qexists `z` >>
  FILTER_ASM_REWRITE_TAC (can (match_term ``height z = height w``)) [] >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume prune_jump_retained_arm_flow[deleted_inherited]:
  rpt strip_tac >>
  qpat_x_assum `Flow p pc height tag boolean u z` mp_tac >>
  qpat_assum `Flow = _` (fn th => pure_rewrite_tac[th]) >>
  qpat_assum `Inherit = _` (fn th => pure_rewrite_tac[th]) >>
  simp_tac bool_ss [LET_THM] >>
  Cases_on `EL (pc u) p` >> simp[] >>
  TRY (rename1 `ALOOKUP dup_table name` >>
       Cases_on `ALOOKUP dup_table name` >> simp[] >>
       TRY (Cases_on `ALOOKUP swap_table name` >> simp[])) >>
  strip_tac >>
  qpat_assum `!k l origin. tag z k = _ ==> _`
    (qspecl_then [`k`,`l`,`b`] mp_tac) >>
  simp[AllCaseEqs()] >> metis_tac[]
QED

Resume prune_jump_retained_arm_flow[taken_layout]:
  mp_tac (Q.INST [`l` |-> `l`, `old` |-> `off`, `dest` |-> `(pc:num#num->num) (z:num#num)`]
    (SPEC_ALL (prune_specialize prune_jump_taken_layout))) >>
  map_every (fn pat => qpat_assum pat (fn th => pure_rewrite_tac[GSYM th]))
    [`(p:asm_inst list) = _`, `(q:asm_inst list) = _`, `b = LENGTH pre`,
     `r = splice_pc b 2 0`] >>
  (impl_tac >- (
    (conj_tac >- first_assum ACCEPT_TAC) >>
    (conj_tac >- first_assum ACCEPT_TAC) >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choose_then `fresh` strip_assume_tac) >>
  qexistsl [`l`, `origin`, `fresh`] >> rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume prune_jump_retained_arm_flow[retag]:
  qx_gen_tac `relabel` >> strip_tac >>
  rename1 `r = splice_pc b 2 0` >>
  `pc u < LENGTH p` by
    (qpat_assum `Open p` mp_tac >>
     qpat_assum `Open = _` (fn th => pure_rewrite_tac[th]) >>
     simp_tac bool_ss [LET_THM, DIFF_EMPTY] >>
     disch_then (map_every assume_tac o CONJUNCTS) >>
     qpat_assum `Keep u` mp_tac >>
     qpat_assum `Keep = _` (fn th => pure_rewrite_tac[th]) >>
     BETA_TAC >> strip_tac >> first_assum irule >> first_assum ACCEPT_TAC) >>
  `EL (r (pc u)) q = EL (pc u) p` by
    (mp_tac (prune_specialize prune_jump_layout) >>
     map_every (fn pat => qpat_assum pat (fn th => pure_rewrite_tac[GSYM th]))
       [`(p:asm_inst list) = _`, `(q:asm_inst list) = _`, `b = LENGTH pre`,
        `r = splice_pc b 2 0`] >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     disch_then (map_every assume_tac o CONJUNCTS) >>
     qpat_assum `!i. i < LENGTH p /\ _ ==> _` (qspec_then `pc u` mp_tac) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
     simp_tac bool_ss []) >>
  qabbrev_tac `P = OPTION_MAP (\(l,i). (l,(relabel:string->num->num) l i))` >>
  `!src f g bp bq. Inherit height tag boolean u z src f bp /\
     (!k l i. f k = SOME(l,i) ==> g k = SOME(l,relabel l i)) /\
     (!k. bp k ==> bq k) ==>
     Inherit height (\w k. P (tag w k)) boolean u z src g bq` by
    (qpat_assum `Inherit = _` (fn th => pure_rewrite_tac[th]) >>
     simp_tac bool_ss [] >> rpt gen_tac >> strip_tac >> conj_tac
     >- (rpt gen_tac >> disch_then mp_tac >>
         simp[Abbr `P`, AllCaseEqs()] >>
         disch_then (qx_choose_then `origin_pair` strip_assume_tac) >>
         PairCases_on `origin_pair` >> fs[] >>
         qpat_assum `!k l origin. tag z k = _ ==> _` (drule_then strip_assume_tac) >>
         (* E0616 stopped here with pointwise OPTION_MAP equality:
            disj1_tac >> qpat_assum `!k. OPTION_MAP _ (f k) = g k`
              (qspec_then `k` (mp_tac o SYM)) >> simp[]. *)
         simp[] >> disj2_tac >> rename1 `src k = SOME h` >> qexists `h` >> simp[]) >>
     rpt gen_tac >> disch_tac >>
     qpat_assum `!k. boolean z k ==> _` (drule_then strip_assume_tac) >>
     simp[] >> qpat_assum `!k. bp k ==> bq k` irule >> first_assum ACCEPT_TAC) >>
  `!bs t. asm_step (SND(compute_label_offsets q)) (build_offset_to_pc q) (AsmPush bs) t =
          asm_step (SND(compute_label_offsets p)) (build_offset_to_pc p) (AsmPush bs) t` by
    simp[asm_step_def] >>
  `!name. asm_returns_zero_or_one (AsmOp name) ==>
     !t. asm_step (SND(compute_label_offsets q)) (build_offset_to_pc q) (AsmOp name) t =
         asm_step (SND(compute_label_offsets p)) (build_offset_to_pc p) (AsmOp name) t` by
    (rpt strip_tac >>
     `name <> "JUMP" /\ name <> "JUMPI"` by fs[asm_returns_zero_or_one_def] >>
     simp[asm_step_def, asm_step_op_def, asm_step_control_def]) >>
  qpat_assum `Abbrev (P = _)` (fn th =>
    pure_rewrite_tac[GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]) >>
  qpat_x_assum `Flow p pc height tag boolean u z` mp_tac >>
  qpat_assum `Flow = _` (fn th => pure_rewrite_tac[th]) >>
  simp_tac bool_ss [LET_THM, combinTheory.o_THM] >>
  qpat_assum `EL (r (pc u)) q = _` (fn th => pure_rewrite_tac[th]) >>
  Cases_on `EL (pc u) p` >> simp_tac (srw_ss()) [LET_THM] >>
  TRY (rename1 `ALOOKUP dup_table name` >>
       Cases_on `ALOOKUP dup_table name` >> simp_tac (srw_ss()) [LET_THM] >>
       TRY (Cases_on `ALOOKUP swap_table name` >> simp_tac (srw_ss()) [LET_THM])) >>
  strip_tac >> rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  qpat_assum `!src f g bp bq. _ ==> _` irule >>
  first_assum (irule_at Any) >>
  csimp[Abbr `P`] >> metis_tac[]
QED

Finalise prune_jump_retained_arm_flow

(* A fall arm and a taken arm are lifted separately, even when the source
   witnesses (or their destination PCs) coincide. Only their union is a row.
   Move carries the retained-membership, rank and Flow obligations. *)
Theorem prune_jump_retained_row_arms[local]:
  !R Move.
  !New. New = (\z.
    (ins <> AsmOp "JUMP" /\
      ?w. R w /\ fall w /\ Move F w z /\ height z = height w /\ fallQ z) \/
    ((ins = AsmOp "JUMP" \/ ins = AsmOp "JUMPI") /\
      ?w. R w /\ taken w /\ Move T w z /\ height z = height w /\ takenQ z)) ==>
  !arm. arm = (\E P (n:num). ?z. E z /\ P z /\ height z = n) ==>
  !legal. legal = (\E P n. !z. E z ==> P z /\ height z = n) ==>
  !next. next = (\E f n. arm E f n /\ legal E f n) ==>
  !stop. stop = (\E a. a <= h /\ untagged a /\ !z. ~E z) ==>
  !row. row = (\E f j.
    case ins of
      AsmLabel l => next E f h
    | AsmPush bs => next E f (h+1)
    | AsmPushLabel l => resolved l /\ next E f (h+1)
    | AsmPushOfst l d => resolved l /\ next E f (h+1)
    | AsmOp name =>
        if name = "INVALID" then stop E 0
        else if name = "REVERT" then stop E 2
        else if MEM name ["SSTORE";"TSTORE";"LOG0";"LOG1";"LOG2";"LOG3";"LOG4"]
             then isStatic /\ stop E (asm_op_arity name)
        else
          (case ALOOKUP dup_table name of
             SOME n => n < h /\ next E f (h+1)
           | NONE => case ALOOKUP swap_table name of
               SOME n => 0 < n /\ n < h /\ next E f h
             | NONE =>
                 if name = "JUMP" then
                   1 <= h /\ arm E j (h-1) /\ legal E j (h-1)
                 else if name = "JUMPI" then
                   2 <= h /\ condition_untagged /\ arm E f (h-2) /\ arm E j (h-2) /\
                   legal E (\z. f z \/ j z) (h-2)
                 else
                   ?m. static_abort_straight name m /\ asm_op_arity name <= h /\
                       untagged (asm_op_arity name) /\ next E f (h-asm_op_arity name+m))
    | _ => F) ==>
  (!w. ins <> AsmOp "JUMP" /\ R w /\ fall w ==>
       ?z. Move F w z /\ height z = height w /\ fallQ z) /\
  (!w. (ins = AsmOp "JUMP" \/ ins = AsmOp "JUMPI") /\ R w /\ taken w ==>
       ?z. Move T w z /\ height z = height w /\ takenQ z) /\
  row R fall taken ==>
  row New fallQ takenQ
Proof
  ntac 2 gen_tac >>
  prune_introduce [`New`,`arm`,`legal`,`next`,`stop`,`row`] >> strip_tac >>
  `!n. ins <> AsmOp "JUMP" /\ arm R fall n ==> arm New fallQ n` by
    (qpat_assum `arm = _` (fn th => pure_rewrite_tac[th]) >> BETA_TAC >>
     qpat_assum `New = _` (fn th => pure_rewrite_tac[th]) >> BETA_TAC >>
     gen_tac >> disch_then (CONJUNCTS_THEN2 assume_tac
       (qx_choose_then `w` strip_assume_tac)) >>
     qpat_assum `!w. ins <> AsmOp "JUMP" /\ R w /\ fall w ==> _`
       (drule_all_then (qx_choose_then `z` strip_assume_tac)) >>
     qexists `z` >> reverse conj_tac >- asm_rewrite_tac[] >>
     disj1_tac >> conj_tac >- first_assum ACCEPT_TAC >>
     qexists `w` >> asm_rewrite_tac[]) >>
  `!n. (ins = AsmOp "JUMP" \/ ins = AsmOp "JUMPI") /\ arm R taken n ==>
        arm New takenQ n` by
    (qpat_assum `arm = _` (fn th => pure_rewrite_tac[th]) >> BETA_TAC >>
     qpat_assum `New = _` (fn th => pure_rewrite_tac[th]) >> BETA_TAC >>
     gen_tac >> disch_then (CONJUNCTS_THEN2 assume_tac
       (qx_choose_then `w` strip_assume_tac)) >>
     qpat_assum `!w. (ins = AsmOp "JUMP" \/ ins = AsmOp "JUMPI") /\ R w /\ taken w ==> _`
       (drule_all_then (qx_choose_then `z` strip_assume_tac)) >>
     qexists `z` >> reverse conj_tac >- asm_rewrite_tac[] >>
     disj2_tac >> conj_tac >- first_assum ACCEPT_TAC >>
     qexists `w` >> asm_rewrite_tac[]) >>
  `!n P. legal R P n ==> !z. New z ==> height z = n` by
    (map_every (fn p => qpat_assum p (fn th => pure_rewrite_tac[th]) >> BETA_TAC)
       [`legal = _`, `New = _`] >>
     rpt gen_tac >> disch_tac >> gen_tac >> strip_tac >>
     qpat_assum `!w. R w ==> _` (drule_then strip_assume_tac) >> asm_rewrite_tac[]) >>
  `!z. New z ==> (ins = AsmOp "JUMP" ==> takenQ z) /\
                  (ins = AsmOp "JUMPI" ==> fallQ z \/ takenQ z)` by
    (map_every (fn p => qpat_assum p (fn th => pure_rewrite_tac[th]) >> BETA_TAC)
       [`New = _`] >>
     rpt strip_tac >> asm_rewrite_tac[]) >>
  `!n. ins <> AsmOp "JUMP" /\ ins <> AsmOp "JUMPI" /\ next R fall n ==>
        next New fallQ n` by
    (qpat_assum `next = _` (fn th => pure_rewrite_tac[th]) >> BETA_TAC >>
     rpt gen_tac >> strip_tac >> conj_tac
     >- (qpat_assum `!n. ins <> AsmOp "JUMP" /\ arm R fall n ==> _` irule >> simp[]) >>
     qpat_assum `legal = _` (fn th => pure_rewrite_tac[th]) >> BETA_TAC >>
     gen_tac >> strip_tac >> reverse conj_tac
     >- (qpat_assum `!n P. legal R P n ==> _` drule >> disch_then drule >>
         disch_then ACCEPT_TAC) >>
     qpat_assum `New z` mp_tac >>
     map_every (fn p => qpat_assum p (fn th => pure_rewrite_tac[th]) >> BETA_TAC)
       [`New = _`] >>
     asm_rewrite_tac[] >> strip_tac >> first_assum ACCEPT_TAC) >>
  `!a. stop R a ==> stop New a` by
    (map_every (fn p => qpat_assum p (fn th => pure_rewrite_tac[th]) >> BETA_TAC)
       [`stop = _`, `New = _`] >>
     rpt strip_tac >>
     (first_assum ACCEPT_TAC ORELSE
      (rename1 `R w` >> qpat_assum `!w. ~R w` (qspec_then `w` mp_tac) >>
       asm_rewrite_tac[]))) >>
  qpat_x_assum `row R fall taken` mp_tac >>
  qpat_assum `row = _` (fn th => pure_rewrite_tac[th]) >> BETA_TAC >>
  Cases_on `ins` >> simp_tac (srw_ss()) [] >>
  TRY (qpat_assum `!n. _ /\ _ /\ next R fall n ==> _`
    (fn th => simp_tac (srw_ss()) [th])) >>
  rename1 `ALOOKUP dup_table name` >>
  Cases_on `name = "JUMP"`
  >- (qpat_assum `name = "JUMP"` SUBST_ALL_TAC >>
      simp_tac (srw_ss()) [dup_table_def, swap_table_def] >> strip_tac >>
      rpt (conj_tac >- first_assum ACCEPT_TAC) >> conj_tac
      >- (qpat_assum `!n. _ /\ arm R taken n ==> _`
           (fn th => MATCH_MP_TAC (SRULE [] th)) >> first_assum ACCEPT_TAC) >>
      qpat_assum `legal = _` (fn th => pure_rewrite_tac[th]) >> BETA_TAC >>
      gen_tac >> strip_tac >> conj_tac
      >- (qpat_assum `!z. New z ==> _` drule >> simp_tac (srw_ss()) []) >>
      qpat_assum `!n P. legal R P n ==> _` drule >> disch_then drule >>
      disch_then ACCEPT_TAC) >>
  Cases_on `name = "JUMPI"`
  >- (qpat_assum `name = "JUMPI"` SUBST_ALL_TAC >>
      simp_tac (srw_ss()) [dup_table_def, swap_table_def] >> strip_tac >>
      rpt (conj_tac >- first_assum ACCEPT_TAC) >> conj_tac
      >- (qpat_assum `!n. _ /\ arm R fall n ==> _`
           (fn th => MATCH_MP_TAC (SRULE [] th)) >> first_assum ACCEPT_TAC) >> conj_tac
      >- (qpat_assum `!n. _ /\ arm R taken n ==> _`
           (fn th => MATCH_MP_TAC (SRULE [] th)) >> first_assum ACCEPT_TAC) >>
      qpat_assum `legal = _` (fn th => pure_rewrite_tac[th]) >> BETA_TAC >>
      gen_tac >> strip_tac >> conj_tac
      >- (qpat_assum `!z. New z ==> _` drule >> simp_tac (srw_ss()) []) >>
      qpat_assum `!n P. legal R P n ==> _` drule >> disch_then drule >>
      disch_then ACCEPT_TAC) >>
  `!n. next R fall n ==> next New fallQ n` by
    (qpat_assum `!n. _ /\ _ /\ next R fall n ==> _` (mp_tac o SRULE []) >>
     asm_rewrite_tac[]) >>
  qpat_assum `name <> "JUMP"` (fn th => rewrite_tac[th]) >>
  qpat_assum `name <> "JUMPI"` (fn th => rewrite_tac[th]) >>
  IF_CASES_TAC >> rewrite_tac[COND_CLAUSES]
  >- (strip_tac >> qpat_assum `!a. stop R a ==> _` irule >> first_assum ACCEPT_TAC) >>
  IF_CASES_TAC >> rewrite_tac[COND_CLAUSES]
  >- (strip_tac >> qpat_assum `!a. stop R a ==> _` irule >> first_assum ACCEPT_TAC) >>
  IF_CASES_TAC >> rewrite_tac[COND_CLAUSES]
  >- (strip_tac >> conj_tac >- first_assum ACCEPT_TAC >>
      qpat_assum `!a. stop R a ==> _` irule >> first_assum ACCEPT_TAC) >>
  Cases_on `ALOOKUP dup_table name` >>
  qpat_assum `ALOOKUP dup_table name = _`
    (fn th => rewrite_tac[th, optionTheory.option_case_def] >> BETA_TAC)
  >- (Cases_on `ALOOKUP swap_table name` >>
      qpat_assum `ALOOKUP swap_table name = _`
        (fn th => rewrite_tac[th, optionTheory.option_case_def] >> BETA_TAC)
      >- (strip_tac >> rename1 `static_abort_straight name m` >> qexists `m` >>
          rpt (conj_tac >- first_assum ACCEPT_TAC) >>
          qpat_assum `!n. next R fall n ==> _` irule >> first_assum ACCEPT_TAC) >>
      strip_tac >> rpt (conj_tac >- first_assum ACCEPT_TAC) >>
      qpat_assum `!n. next R fall n ==> _` irule >> first_assum ACCEPT_TAC) >>
  strip_tac >> rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  qpat_assum `!n. next R fall n ==> _` irule >> first_assum ACCEPT_TAC
QED

(* A demand for a deleted producer is inherited on every retained edge.
   Along a rooted path it therefore comes from a Lab at the replay endpoint. *)
Theorem prune_jump_deleted_origin_producer[local]:
  !(R:(num#num)->(num#num)->bool) tag d e z n path q env j s v l k.
    path 0 = e /\ path n = z /\ (!i. i < n ==> R (path i) (path (SUC i))) /\
    (!a b i. R a b /\ tag b i = SOME(l,d) ==> ?h. tag a h = SOME(l,d)) /\
    (!i. tag e i = SOME(l,d) ==> i < LENGTH v.sym_stack /\ EL i v.sym_stack = Lab l 0) /\
    sym_steps q env j (sym_init s) = SymOK v /\ tag z k = SOME(l,d) ==>
    ?i. i < LENGTH q /\ (EL i q = AsmPushLabel l \/ EL i q = AsmPushOfst l 0)
Proof
  rpt strip_tac >>
  `!i. i <= n ==> !a. tag (path i) a = SOME(l,d) ==> ?h. tag e h = SOME(l,d)` by
    (Induct >- metis_tac[] >> rpt strip_tac >>
     `i < n /\ i <= n` by decide_tac >>
     `R (path i) (path (SUC i))` by simp[] >>
     qpat_assum `!a b j. R a b /\ _ ==> _` (drule_all_then strip_assume_tac) >>
     qpat_assum `i <= n ==> _` (drule_then drule) >> simp[]) >>
  `?h. tag e h = SOME(l,d)` by
    (qpat_assum `!i. i <= n ==> _` (qspec_then `n` mp_tac) >> simp[] >>
     disch_then drule >> simp[]) >>
  `MEM (Lab l 0) v.sym_stack` by (simp[MEM_EL] >> metis_tac[]) >>
  drule_all stopped_lab_zero_producer >> strip_tac >>
  qexists `u.sym_base.as_pc` >> simp[]
QED

(* Restrict the contracted relation before assigning a replacement for an
   erased producer: only a rooted demand has a replay provenance proof. *)
Theorem prune_jump_cut_rows[local]:
  !Shape. Shape = (\p cc req pc height need tag boolean (u:num#num) (t:asm_state).
    t.as_pc = pc u /\ LENGTH t.as_stack = height u /\
    t.as_call_ctx = cc /\ t.as_requests = req /\
    (need u ==> t.as_call_ctx.cc_static) /\
    (!k l i. tag u k = SOME(l,i) ==>
      k < height u /\ i < LENGTH p /\
      (EL i p = AsmPushLabel l \/ (?d. EL i p = AsmPushOfst l d) \/ EL i p = AsmDataLabel l) /\
      ?off dest. FLOOKUP (SND(compute_label_offsets p)) l = SOME off /\
        off < dimword(:256) /\ FLOOKUP (build_offset_to_pc p) off = SOME dest /\
        EL k t.as_stack = (n2w off:bytes32)) /\
    (!k. boolean u k ==> k < height u /\ (EL k t.as_stack=0w \/ EL k t.as_stack=1w))) ==>
  !Inherit. Inherit = (\height tag boolean (u:num#num) (w:num#num) src fresh bnew.
    (!k l i. tag w k = SOME(l,i) ==> k < height w /\
      (fresh k = SOME(l,i) \/ ?h. src k = SOME h /\ h < height u /\ tag u h = SOME(l,i))) /\
    (!k. boolean w k ==> k < height w /\ (bnew k \/ ?h. src k = SOME h /\ h < height u /\ boolean u h))) ==>
  !Flow. Flow = (\p pc height tag boolean (u:num#num) (w:num#num).
    !hi. hi = height u ==>
    !hj. hj = height w ==>
    !ins. ins = EL (pc u) p ==>
    !inherit. inherit = Inherit height tag boolean u w ==>
    case ins of
      AsmLabel l => hj = hi /\ inherit (\k. SOME k) (\k. NONE) (\k. F)
    | AsmPush bs => hj = hi+1 /\
        inherit (\k. if k=0 then NONE else SOME(k-1)) (\k. NONE)
          (\k. k=0 /\ !t v. asm_step (SND(compute_label_offsets p)) (build_offset_to_pc p)
                         (AsmPush bs) t = AsmOK v ==> (EL 0 v.as_stack=0w \/ EL 0 v.as_stack=1w))
    | AsmPushLabel l => hj = hi+1 /\
        inherit (\k. if k=0 then NONE else SOME(k-1)) (\k. if k=0 then SOME(l,pc u) else NONE) (\k. F)
    | AsmPushOfst l d => hj = hi+1 /\
        inherit (\k. if k=0 then NONE else SOME(k-1)) (\k. if k=0 /\ d=0 then SOME(l,pc u) else NONE) (\k. F)
    | AsmOp name =>
        (case ALOOKUP dup_table name of
           SOME n => n < hi /\ hj = hi+1 /\
             inherit (\k. SOME(if k=0 then n else k-1)) (\k. NONE) (\k. F)
         | NONE => case ALOOKUP swap_table name of
           SOME n => 0 < n /\ n < hi /\ hj = hi /\
             inherit (\k. SOME(if k=0 then n else if k=n then 0 else k)) (\k. NONE) (\k. F)
         | NONE =>
             !a. a = asm_op_arity name ==>
             !m. m = hj + a - hi ==>
             a <= hi /\ hj = m+(hi-a) /\ ((name="JUMP" \/ name="JUMPI") ==> m=0) /\
             inherit (\k. if k<m then NONE else SOME(k-m+a)) (\k. NONE)
               (\k. k=0 /\ m=1 /\ asm_returns_zero_or_one ins /\
                 !t v. LENGTH t.as_stack=hi /\
                   asm_step (SND(compute_label_offsets p)) (build_offset_to_pc p) ins t = AsmOK v ==>
                   (EL 0 v.as_stack=0w \/ EL 0 v.as_stack=1w)))
    | _ => F) ==>
  !Target. Target = (\p pc tag (u:num#num) (w:num#num).
    ?l i off. tag u 0=SOME(l,i) /\ FLOOKUP (SND(compute_label_offsets p)) l=SOME off /\
      off < dimword(:256) /\ FLOOKUP (build_offset_to_pc p) off=SOME(pc w)) ==>
  !Check. Check = (\ins (h:num) untagged condition_untagged isStatic resolved E height f j.
    !arm. arm = (\P n. ?z. E z /\ P z /\ height z = n) ==>
    !legal. legal = (\P n. !z. E z ==> P z /\ height z = n) ==>
    !next. next = (\n. arm f n /\ legal f n) ==>
    !stop. stop = (\a. a <= h /\ untagged a /\ !z. ~E z) ==>
    case ins of
      AsmLabel l => next h
    | AsmPush bs => next (h+1)
    | AsmPushLabel l => resolved l /\ next (h+1)
    | AsmPushOfst l d => resolved l /\ next (h+1)
    | AsmOp name =>
        if name="INVALID" then stop 0
        else if name="REVERT" then stop 2
        else if MEM name ["SSTORE";"TSTORE";"LOG0";"LOG1";"LOG2";"LOG3";"LOG4"]
             then isStatic /\ stop (asm_op_arity name)
        else (case ALOOKUP dup_table name of
                SOME n => n<h /\ next (h+1)
              | NONE => case ALOOKUP swap_table name of
                SOME n => 0<n /\ n<h /\ next h
              | NONE => if name="JUMP" then 1<=h /\ arm j (h-1) /\ legal j (h-1)
                        else if name="JUMPI" then 2<=h /\ condition_untagged /\
                               arm f (h-2) /\ arm j (h-2) /\ legal (\z. f z \/ j z) (h-2)
                        else ?m. static_abort_straight name m /\ asm_op_arity name <= h /\
                             untagged (asm_op_arity name) /\ next (h-asm_op_arity name+m))
    | _ => F) ==>
  !Slots. Slots = (\p cc height need tag boolean (u:num#num).
    (need u ==> cc.cc_static) /\
    (!k. boolean u k ==> k < height u /\ tag u k=NONE) /\
    (!k l i. tag u k=SOME(l,i) ==> k < height u /\ i < LENGTH p /\
      (EL i p=AsmPushLabel l \/ EL i p=AsmPushOfst l 0) /\
      ?off dest. FLOOKUP (SND(compute_label_offsets p)) l=SOME off /\
        off < dimword(:256) /\ FLOOKUP (build_offset_to_pc p) off=SOME dest)) ==>
  !Row. Row = (\p cc pc height tag E (u:num#num).
    pc u < LENGTH p /\ Check (EL (pc u) p) (height u) (\a. !k. k<a ==> tag u k=NONE)
      (tag u 1=NONE) cc.cc_static (\l. IS_SOME (FLOOKUP (SND(compute_label_offsets p)) l))
      (E u) height (\w. pc w=pc u+1) (Target p pc tag u)) ==>
  !Rows. Rows = (\p cc (V:(num#num)->bool) X (rank:(num#num)->num) pc height need tag boolean E.
    (!u. u IN V ==> Slots p cc height need tag boolean u) /\
    (!u w. E u w ==> u IN V DIFF X /\ w IN V /\ rank w < rank u /\ Flow p pc height tag boolean u w) /\
    (!u. u IN V DIFF X ==> Row p cc pc height tag E u)) ==>
  !Control. Control = (\p pc tag (u:num#num) w.
    if EL (pc u) p = AsmOp "JUMP" then Target p pc tag u w
    else if EL (pc u) p = AsmOp "JUMPI" then pc w=pc u+1 \/ Target p pc tag u w
    else pc w=pc u+1) ==>
  !Open. Open = (\p cc req (V:(num#num)->bool) X (rank:(num#num)->num) pc height need tag boolean E.
    !S. S = Shape p cc req pc height need tag boolean ==>
    !lo. lo = SND(compute_label_offsets p) ==>
    !otp. otp = build_offset_to_pc p ==>
    FINITE V /\ X SUBSET V /\ (!u. u IN V ==> ?t. S u t) /\
    (!u. u IN V DIFF X ==> pc u < LENGTH p) /\
    (!u w. E u w ==> u IN V DIFF X /\ w IN V /\ rank w < rank u /\
      Flow p pc height tag boolean u w /\ Control p pc tag u w) /\
    (!u t. u IN V DIFF X /\ S u t ==>
      (?v. (asm_steps lo otp p 1 t=AsmRevert v \/ asm_steps lo otp p 1 t=AsmFault v) /\ v.as_requests=req) \/
      (?w v. E u w /\ asm_steps lo otp p 1 t=AsmOK v /\ S w v))) ==>
  !Reach. Reach = (\(E:(num#num)->(num#num)->bool) e u.
    ?n path. path 0=e /\ path n=u /\ !k. k<n ==> E (path k) (path (SUC k))) ==>
  !Demand. Demand = (\tag boolean (e:num#num) stk.
    (!k l i. tag e k=SOME(l,i) ==> k<LENGTH stk /\ EL k stk=Lab l 0) /\
    (!k. boolean e k ==> k<LENGTH stk /\ (EL k stk=Val 0w \/ EL k stk=Val 1w))) ==>
  !Cert. Cert = (\p ss a. ?V e rank pc height need tag boolean E.
    Rows p a.as_call_ctx V {} rank pc height need tag boolean E /\
    Open p a.as_call_ctx a.as_requests V {} rank pc height need tag boolean E /\
    e IN V /\ (!u. u IN V ==> Reach E e u) /\
    Shape p a.as_call_ctx a.as_requests pc height need tag boolean e a /\ Demand tag boolean e ss.sym_stack) ==>
  !p. p = pre ++ [AsmPushLabel x; AsmOp "JUMP"; AsmLabel x] ++ tail ==>
  !q. q = pre ++ [AsmLabel x] ++ tail ==>
  !ep. ep = asm_data_env p (assemble p ++ data) ==>
  !eq. eq = asm_data_env q (assemble q ++ data) ==>
  s.as_pc=0 /\ s.as_code=assemble p ++ data /\ asm_static_wf p /\
  sym_steps p ep n (sym_init s)=SymOK ss /\ asm_sym_rel p ep a ss /\ Cert p ss a ==>
  ?j v t. sym_steps q eq j (sym_init (s with as_code := assemble q ++ data))=SymOK v /\
    asm_steps (SND(compute_label_offsets q)) (build_offset_to_pc q) q j
      (s with as_code := assemble q ++ data)=AsmOK t /\
    asm_sym_rel q eq t v /\ t.as_call_ctx=a.as_call_ctx /\ t.as_requests=a.as_requests /\ Cert q v t
Proof
  prune_introduce [`Shape`,`Inherit`,`Flow`,`Target`,`Check`,`Slots`,`Row`,
    `Rows`,`Control`,`Open`,`Reach`,`Demand`,`Cert`,`p`,`q`,`ep`,`eq`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `Cert p ss a` mp_tac >>
  qpat_assum `Cert = _` (fn th => pure_rewrite_tac[th]) >> BETA_TAC >>
  disch_then (qx_choose_then `V` (qx_choose_then `e` (qx_choose_then `rank`
    (qx_choose_then `pc` (qx_choose_then `height` (qx_choose_then `need`
    (qx_choose_then `tag` (qx_choose_then `boolean` (qx_choose_then `edge`
    (map_every assume_tac o CONJUNCTS)))))))))) >>
  qabbrev_tac `b = LENGTH (pre:asm_inst list)` >>
  qabbrev_tac `r = splice_pc b 2 0` >>
  qabbrev_tac `Keep = \u:num#num. u IN V /\ pc u <> b /\ pc u <> b+1` >>
  suspend "start"
QED

Resume prune_jump_cut_rows[start]:
  `ss.sym_base.as_pc = pc e /\ height e = LENGTH ss.sym_stack /\
   ss.sym_base.as_call_ctx = a.as_call_ctx /\ ss.sym_base.as_requests = a.as_requests` by
    (drule_then strip_assume_tac asm_sym_rel_pc >>
     qpat_assum `Shape p _ _ _ _ _ _ _ e a` mp_tac >>
     qpat_assum `Shape = _` (fn th => pure_rewrite_tac[th]) >> BETA_TAC >> strip_tac >>
     qpat_assum `asm_sym_rel p ep a ss` mp_tac >>
     simp_tac (srw_ss()) [asm_sym_rel_def] >> strip_tac >> simp[]) >>
  `asm_static_wf q /\
   ?j v t z. sym_steps q eq j (sym_init (s with as_code := assemble q ++ data))=SymOK v /\
     asm_steps (SND(compute_label_offsets q)) (build_offset_to_pc q) q j
       (s with as_code := assemble q ++ data)=AsmOK t /\
     asm_sym_rel q eq t v /\ t.as_call_ctx=a.as_call_ctx /\ t.as_requests=a.as_requests /\
     Keep z /\ r (pc z)=t.as_pc /\ height z=LENGTH t.as_stack /\ Demand tag boolean z v.sym_stack`
    by suspend "replay" >>
  qexistsl [`j`,`v`,`t`] >> ntac 5 (conj_tac >- first_assum ACCEPT_TAC) >>
  suspend "graph"
QED

Resume prune_jump_cut_rows[replay]:
  mp_tac (CONV_RULE (REDEPTH_CONV (REWR_CONV LET_THM ORELSEC BETA_CONV))
    (Q.INST [`cc` |-> `a.as_call_ctx`, `req` |-> `a.as_requests`]
      (SPEC_ALL (prune_specialize prune_jump_replayed_root)))) >>
  map_every (fn pat => qpat_assum pat (fn th => pure_rewrite_tac[GSYM th]))
    [`(p:asm_inst list) = _`, `(q:asm_inst list) = _`, `ep = _`, `eq = _`] >>
  (impl_tac >- (
    ntac 4 (conj_tac >- first_assum ACCEPT_TAC) >> conj_tac
    >- (qpat_assum `Open p _ _ V {} rank pc height need tag boolean edge` mp_tac >>
        map_every (fn pat => qpat_assum pat (fn th => pure_rewrite_tac[th]))
          [`Open = _`, `Control = _`, `Target = _`, `Shape = _`, `Flow = _`, `Inherit = _`] >>
        CONV_TAC (REDEPTH_CONV (REWR_CONV LET_THM ORELSEC BETA_CONV)) >>
        DISCH_THEN ACCEPT_TAC) >>
    ntac 5 (conj_tac >- first_assum ACCEPT_TAC) >>
    qpat_assum `Demand tag boolean e ss.sym_stack` mp_tac >>
    qpat_assum `Demand = _` (fn th => pure_rewrite_tac[th]) >> BETA_TAC >> simp[])) >>
  disch_then (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 (K all_tac) strip_assume_tac)) >>
  conj_tac >- first_assum ACCEPT_TAC >> qexistsl [`j`,`v`,`t`,`z`] >>
  ntac 5 (conj_tac >- first_assum ACCEPT_TAC) >>
  simp[Abbr `Keep`, Abbr `r`, Abbr `b`] >>
  qpat_assum `Demand = _` (fn th => pure_rewrite_tac[th]) >> BETA_TAC >> simp[]
QED

Resume prune_jump_cut_rows[graph]:
  qabbrev_tac `pcQ = r o pc` >>
  qabbrev_tac `Move = \u take w y.
    Keep y /\ rank y < rank u /\ height y = height w /\
    (if take then Target q pcQ tag u y else pcQ y = pcQ u+1) /\
    (!k l. tag y k=SOME(l,b) ==> ?h. tag u h=SOME(l,b)) /\
    (!rho. (!l. rho l (pc u)=r (pc u)) ==>
      Flow q pcQ height (\w k. OPTION_MAP (\(l,i). (l,rho l i)) (tag w k)) boolean u y)` >>
  `!u take w. Keep u /\ edge u w /\
      (if take then Target p pc tag u w else pc w=pc u+1) ==>
    ?y. Move u take w y` by suspend "moves" >>
  qabbrev_tac `R = \u y.
    (EL (pc u) p <> AsmOp "JUMP" /\
     ?w. edge u w /\ pc w=pc u+1 /\ Move u F w y) \/
    ((EL (pc u) p = AsmOp "JUMP" \/ EL (pc u) p = AsmOp "JUMPI") /\
     ?w. edge u w /\ Target p pc tag u w /\ Move u T w y)` >>
  qabbrev_tac `A = {u | Keep u /\ Reach R z u}` >>
  qabbrev_tac `E = \u y. u IN A /\ R u y` >>
  suspend "rooted"
QED

Resume prune_jump_cut_rows[moves]:
  rpt gen_tac >> strip_tac >>
  mp_tac (CONV_RULE (REDEPTH_CONV (REWR_CONV LET_THM ORELSEC BETA_CONV))
    (Q.INST [`cc` |-> `a.as_call_ctx`, `req` |-> `a.as_requests`, `isTaken` |-> `take`]
      (SPEC_ALL (prune_specialize prune_jump_retained_arm_flow)))) >>
  map_every (fn pat => qpat_assum pat (pure_rewrite_tac o single o GSYM))
    [`(p:asm_inst list) = _`, `(q:asm_inst list) = _`] >>
  map_every (fn pat => qpat_assum pat
    (pure_rewrite_tac o single o GSYM o REWRITE_RULE [markerTheory.Abbrev_def]))
    [`Abbrev (b = _)`, `Abbrev (r = _)`] >>
  (impl_tac >- (
    conj_tac >- first_assum ACCEPT_TAC >> conj_tac
    >- (qpat_assum `Open p _ _ V {} rank pc height need tag boolean edge` mp_tac >>
        map_every (fn pat => qpat_assum pat (pure_rewrite_tac o single))
          [`Open = _`, `Control = _`, `Target = _`, `Shape = _`, `Flow = _`, `Inherit = _`] >>
        CONV_TAC (REDEPTH_CONV (REWR_CONV LET_THM ORELSEC BETA_CONV)) >>
        DISCH_THEN ACCEPT_TAC) >>
    conj_tac >- (simp[Abbr `Keep`] >> metis_tac[]) >>
    conj_tac >- first_assum ACCEPT_TAC >>
    qpat_assum `if take then Target p pc tag u w else _` mp_tac >>
    qpat_assum `Target = _` (pure_rewrite_tac o single) >>
    CONV_TAC (REDEPTH_CONV BETA_CONV) >> DISCH_THEN ACCEPT_TAC)) >>
  disch_then (qx_choose_then `y` (map_every assume_tac o CONJUNCTS)) >> qexists `y` >>
  map_every (fn pat => qpat_assum pat
    (pure_rewrite_tac o single o REWRITE_RULE [markerTheory.Abbrev_def]))
    [`Abbrev (Move = _)`, `Abbrev (Keep = _)`, `Abbrev (pcQ = _)`] >>
  map_every (fn pat => qpat_assum pat (pure_rewrite_tac o single))
    [`Target = _`, `Flow = _`, `Inherit = _`] >>
  CONV_TAC (REDEPTH_CONV (REWR_CONV LET_THM ORELSEC BETA_CONV)) >>
  conj_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  ntac 2 (conj_tac >- first_assum ACCEPT_TAC) >>
  reverse conj_tac >- (conj_tac >> first_assum ACCEPT_TAC) >>
  Cases_on `take` >> pure_rewrite_tac[COND_CLAUSES, combinTheory.o_THM]
  >- (qpat_assum `T ==> ?l i off. _` mp_tac >> simp_tac bool_ss []) >>
  qpat_assum `if F then _ else _` mp_tac >> simp_tac bool_ss []
QED

Resume prune_jump_cut_rows[rooted]:
  `!u. u IN A <=> Keep u /\ Reach R z u` by
    simp[Abbr `A`, numberTheory.equiv_class_element] >>
  `z IN A` by (simp[] >> qexistsl [`0`,`\k. z`] >> simp[]) >>
  `!u take w y. Move u take w y ==>
       Keep y /\ rank y < rank u /\ height y = height w /\
       (if take then Target q pcQ tag u y else pcQ y = pcQ u + 1) /\
       (!k l. tag y k = SOME (l,b) ==> ?h. tag u h = SOME (l,b)) /\
       (!rho. (!l. rho l (pc u) = r (pc u)) ==>
          Flow q pcQ height (\h k. OPTION_MAP (\(l,i). (l,rho l i)) (tag h k)) boolean u y)` by
    (qpat_assum `Abbrev (Move = _)`
       (pure_rewrite_tac o single o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     BETA_TAC >> simp_tac bool_ss []) >>
  `!u y. R u y ==>
       (EL (pc u) p <> AsmOp "JUMP" /\ (?w. edge u w /\ pc w = pc u + 1 /\ Move u F w y)) \/
       ((EL (pc u) p = AsmOp "JUMP" \/ EL (pc u) p = AsmOp "JUMPI") /\
        ?w. edge u w /\ Target p pc tag u w /\ Move u T w y)` by
    (qpat_assum `Abbrev (R = _)`
       (pure_rewrite_tac o single o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     BETA_TAC >> simp_tac bool_ss []) >>
  `!u y. R u y ==> Keep y /\ rank y < rank u` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `!u y. R u y ==> _` (drule_then strip_assume_tac) >>
     qpat_assum `!u take w y. Move u take w y ==> _` (drule_then strip_assume_tac) >> simp[]) >>
  `!u y. E u y <=> u IN A /\ R u y` by simp[Abbr `E`] >>
  `!u y. E u y ==> y IN A` by
    (map_every qx_gen_tac [`u`,`y`] >> disch_tac >>
     `Keep y /\ R u y /\ Reach R z u` by metis_tac[] >>
     simp[] >> qpat_x_assum `Reach R z u` mp_tac >>
     simp[] >>
     disch_then (qx_choose_then `n` (qx_choose_then `path` strip_assume_tac)) >>
     qexistsl [`SUC n`,`\k. if k = SUC n then y else path k`] >>
     simp[] >> qx_gen_tac `k` >> disch_tac >> Cases_on `k=n`
     >- (`n <> SUC n` by decide_tac >> simp[]) >>
     `k < n /\ k <> SUC n` by decide_tac >> simp[]) >>
  `!u y k l. R u y /\ tag y k = SOME (l,b) ==> ?h. tag u h = SOME (l,b)` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!u y. R u y ==> _ \/ _` (drule_then strip_assume_tac) >>
     qpat_assum `!u take w y. Move u take w y ==> _` (drule_then strip_assume_tac) >>
     qpat_assum `!k l. tag y k = SOME (l,b) ==> _` (drule_then ACCEPT_TAC)) >>
  `!l. (?u k. u IN A /\ tag u k = SOME (l,b)) ==>
       ?i. i < LENGTH q /\ (EL i q = AsmPushLabel l \/ EL i q = AsmPushOfst l 0)` by
    (qx_gen_tac `l` >> disch_then (qx_choose_then `u` (qx_choose_then `k` strip_assume_tac)) >>
     `Reach R z u` by metis_tac[] >>
     qpat_x_assum `Reach R z u` mp_tac >>
     qpat_assum `Reach = _` (pure_rewrite_tac o single) >> BETA_TAC >>
     disch_then (qx_choose_then `m` (qx_choose_then `path` strip_assume_tac)) >>
     `!i. tag z i = SOME (l,b) ==> i < LENGTH v.sym_stack /\ EL i v.sym_stack = Lab l 0` by
       (qpat_assum `Demand tag boolean z v.sym_stack` mp_tac >> simp[] >> metis_tac[]) >>
     match_mp_tac (INST_TYPE [alpha |-> ``:num``] prune_jump_deleted_origin_producer) >>
     qexistsl [`R`,`tag`,`b`,`z`,`u`,`m`,`path`,`eq`,`j`,
       `s with as_code := assemble q ++ data`,`v`,`k`] >>
     rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE metis_tac[])) >>
  qabbrev_tac `pick = \l. @i. i < LENGTH q /\ (EL i q = AsmPushLabel l \/ EL i q = AsmPushOfst l 0)` >>
  `!l. (?u k. u IN A /\ tag u k = SOME (l,b)) ==>
       pick l < LENGTH q /\ (EL (pick l) q = AsmPushLabel l \/ EL (pick l) q = AsmPushOfst l 0)` by
    (qx_gen_tac `l` >> disch_tac >>
     qpat_assum `Abbrev (pick = _)`
       (pure_rewrite_tac o single o REWRITE_RULE [markerTheory.Abbrev_def]) >> BETA_TAC >>
     qpat_assum `!l. (?u k. _) ==> ?i. i < LENGTH q /\ _`
       (drule_then (ACCEPT_TAC o SELECT_RULE))) >>
  qabbrev_tac `reloc = \l i. if i = b then pick l else r i` >>
  qabbrev_tac `tagQ = \u k. OPTION_MAP (\(l,i). (l,reloc l i)) (tag u k)` >>
  `!u. u IN A ==> u IN V /\ pc u <> b /\ pc u <> b+1` by
    (gen_tac >> disch_tac >> `Keep u` by metis_tac[] >>
     qpat_assum `Keep u` mp_tac >> simp[Abbr `Keep`] >>
     metis_tac[Abbr `Keep`]) >>
  `!u. u IN A ==> !l. reloc l (pc u) = r (pc u)` by
    (rpt strip_tac >> `pc u <> b` by metis_tac[] >> simp[Abbr `reloc`]) >>
  `!u k. (tagQ u k = NONE <=> tag u k = NONE)` by
    (rpt gen_tac >> simp[Abbr `tagQ`] >> Cases_on `tag u k` >> simp[]) >>
  `!u k l i. tagQ u k = SOME (l,i) <=>
      ?org. tag u k = SOME (l,org) /\ i = reloc l org` by
    (rpt gen_tac >> simp[Abbr `tagQ`, optionTheory.OPTION_MAP_EQ_SOME, pairTheory.EXISTS_PROD]) >>
  `!i. i < LENGTH p /\ i <> b /\ i <> b+1 ==>
       r i < LENGTH q /\ EL (r i) q = EL i p` by
    (mp_tac (prune_specialize prune_jump_layout) >>
     map_every (fn pat => qpat_assum pat (fn th =>
         pure_rewrite_tac[GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]))
       [`(p:asm_inst list) = _`, `(q:asm_inst list) = _`,
        `Abbrev (b = LENGTH pre)`, `Abbrev (r = splice_pc b 2 0)`] >>
     (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >> first_assum ACCEPT_TAC) >>
  `!l old dest. FLOOKUP (SND(compute_label_offsets p)) l = SOME old /\
      FLOOKUP (build_offset_to_pc p) old = SOME dest ==>
      ?off. FLOOKUP (SND(compute_label_offsets q)) l = SOME off /\
         off < dimword(:256) /\ FLOOKUP (build_offset_to_pc q) off = SOME (r dest)` by
    (rpt gen_tac >> strip_tac >>
     mp_tac (prune_specialize prune_jump_taken_layout) >>
     map_every (fn pat => qpat_assum pat (fn th =>
         pure_rewrite_tac[GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]))
       [`(p:asm_inst list) = _`, `(q:asm_inst list) = _`,
        `Abbrev (b = LENGTH pre)`, `Abbrev (r = splice_pc b 2 0)`] >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >> disch_then ACCEPT_TAC) >>
  `EL (b+1) p = AsmOp "JUMP"` by
    (qpat_assum `(p:asm_inst list) = _` (fn th => pure_rewrite_tac[th]) >>
     simp[Abbr `b`, listTheory.EL_APPEND_EQN, EL, GSYM ADD1]) >>
  `!u. u IN A ==> Slots q t.as_call_ctx height need tagQ boolean u` by suspend "slotsQ" >>
  `!u. u IN A ==> pcQ u < LENGTH q /\ EL (pcQ u) q = EL (pc u) p` by suspend "fetchQ" >>
  `!u y. Target q pcQ tag u y <=> Target q pcQ tagQ u y` by suspend "targetQ" >>
  `!u y. E u y ==> y IN A /\ rank y < rank u /\
      Flow q pcQ height tagQ boolean u y /\ Control q pcQ tagQ u y` by suspend "edgesQ" >>
  `!u. u IN A ==> Row q t.as_call_ctx pcQ height tagQ E u` by suspend "rowQ" >>
  `Shape q t.as_call_ctx t.as_requests pcQ height need tagQ boolean z t /\
   Demand tagQ boolean z v.sym_stack` by suspend "rootQ" >>
  suspend "package"
QED

Resume prune_jump_cut_rows[slotsQ]:
  gen_tac >> disch_tac >>
  `u IN V` by metis_tac[] >>
  `Slots p a.as_call_ctx height need tag boolean u` by
    (qpat_assum `Rows p _ V {} rank pc height need tag boolean edge` mp_tac >> qpat_assum `Rows = _` (fn th => pure_rewrite_tac[th]) >>
     BETA_TAC >> strip_tac >> first_assum (drule_then ACCEPT_TAC)) >>
  qpat_x_assum `Slots p a.as_call_ctx height need tag boolean u` mp_tac >>
  qpat_assum `Slots = _` (fn th => pure_rewrite_tac[th]) >> BETA_TAC >>
  qpat_assum `t.as_call_ctx = a.as_call_ctx` (fn th => pure_rewrite_tac[th]) >>
  strip_tac >> conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (gen_tac >> disch_tac >> first_assum (drule_then strip_assume_tac) >> simp[]) >>
  rpt gen_tac >> disch_tac >>
  qpat_assum `!u k l i. tagQ u k = SOME(l,i) <=> _`
    (drule_then (qx_choose_then `org` strip_assume_tac) o iffLR) >>
  qpat_assum `!k l i. tag u k = SOME(l,i) ==> _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  `i < LENGTH q /\ (EL i q = AsmPushLabel l \/ EL i q = AsmPushOfst l 0)` by
    (qpat_assum `i = reloc l org` SUBST1_TAC >>
     qpat_assum `Abbrev (reloc = _)`
       (pure_rewrite_tac o single o REWRITE_RULE [markerTheory.Abbrev_def]) >> BETA_TAC >>
     Cases_on `org = b`
     >- (qpat_assum `org = b` (simp_tac bool_ss o single) >>
         qpat_assum `!l. (?u k. u IN A /\ tag u k = SOME(l,b)) ==> _` irule >>
         qexistsl [`u`,`k`] >> asm_rewrite_tac[]) >>
     `org <> b+1` by (disch_then SUBST_ALL_TAC >>
       qpat_assum `EL (b+1) p = _ \/ _` mp_tac >> simp[]) >>
     qpat_assum `!i. i < LENGTH p /\ i <> b /\ i <> b+1 ==> _`
       (drule_all_then (map_every assume_tac o CONJUNCTS)) >>
     qpat_assum `org <> b` (fn h1 =>
       qpat_assum `r org < LENGTH q` (fn h2 =>
         qpat_assum `EL (r org) q = EL org p` (fn h3 =>
           qpat_assum `EL org p = AsmPushLabel l \/ EL org p = AsmPushOfst l 0`
             (fn h4 => simp_tac bool_ss [h1,h2,h3,h4]))))) >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  (conj_tac >- FIRST_PROVE [disj1_tac >> first_assum ACCEPT_TAC,
                           disj2_tac >> first_assum ACCEPT_TAC]) >>
  qpat_x_assum `?off dest. FLOOKUP (SND(compute_label_offsets p)) l = SOME off /\ _`
    (qx_choose_then `old` (qx_choose_then `dest` strip_assume_tac)) >>
  qpat_assum `!l old dest. FLOOKUP _ l = SOME old /\ _ ==> _`
    (drule_all_then (qx_choose_then `off` strip_assume_tac)) >>
  qexistsl [`off`,`r dest`] >> asm_rewrite_tac[]
QED

Resume prune_jump_cut_rows[fetchQ]:
  gen_tac >> disch_tac >>
  `u IN V /\ pc u <> b /\ pc u <> b+1` by metis_tac[] >>
  `Row p a.as_call_ctx pc height tag edge u` by
    (qpat_assum `Rows p _ V {} rank pc height need tag boolean edge` mp_tac >> qpat_assum `Rows = _` (pure_rewrite_tac o single) >>
     simp_tac bool_ss [DIFF_EMPTY] >> strip_tac >> first_assum (drule_then ACCEPT_TAC)) >>
  `pc u < LENGTH p` by
    (qpat_assum `Row p a.as_call_ctx pc height tag edge u` mp_tac >>
     qpat_assum `Row = _` (pure_rewrite_tac o single) >> simp_tac bool_ss []) >>
  qpat_assum `!i. i < LENGTH p /\ i <> b /\ i <> b+1 ==> _`
    (drule_all_then (fn th =>
       qpat_assum `Abbrev (pcQ = _)` (fn h =>
         simp_tac bool_ss [th, combinTheory.o_THM,
                           REWRITE_RULE [markerTheory.Abbrev_def] h])))
QED

Resume prune_jump_cut_rows[targetQ]:
  rpt gen_tac >>
  qpat_assum `Target = _` (pure_rewrite_tac o single) >> BETA_TAC >>
  qpat_assum `!u k l i. tagQ u k = SOME(l,i) <=> _` (pure_rewrite_tac o single) >>
  eq_tac
  >- (disch_then (qx_choose_then `l` (qx_choose_then `i` (qx_choose_then `off` strip_assume_tac))) >>
      qexistsl [`l`,`reloc l i`,`off`] >> simp[] >> qexists `i` >> simp[]) >>
  disch_then (qx_choose_then `l` (qx_choose_then `i` (qx_choose_then `off` strip_assume_tac))) >>
  qexistsl [`l`,`org`,`off`] >> simp[]
QED

Resume prune_jump_cut_rows[edgesQ]:
  rpt gen_tac >> disch_tac >>
  `u IN A /\ R u y /\ y IN A /\ rank y < rank u` by metis_tac[] >>
  `EL (pcQ u) q = EL (pc u) p` by metis_tac[] >>
  `!l. reloc l (pc u) = r (pc u)` by metis_tac[] >>
  (conj_tac >- first_assum ACCEPT_TAC) >> (conj_tac >- first_assum ACCEPT_TAC) >>
  qpat_assum `!u y. R u y ==> _ \/ _` (drule_then strip_assume_tac) >>
  qpat_assum `!u take w y. Move u take w y ==> _`
    (drule_then (map_every assume_tac o CONJUNCTS o SIMP_RULE bool_ss [])) >>
  (conj_tac
   >- (qpat_assum `!rho. _ ==> Flow _ _ _ _ _ _ _` (qspec_then `reloc` mp_tac) >>
       (impl_tac >- first_assum ACCEPT_TAC) >>
       qpat_assum `Abbrev (tagQ = _)`
         (pure_rewrite_tac o single o REWRITE_RULE [markerTheory.Abbrev_def]) >>
       disch_then ACCEPT_TAC))
  >> qpat_assum `Control = _` (pure_rewrite_tac o single) >> BETA_TAC
  >> qpat_assum `EL (pcQ u) q = EL (pc u) p` (pure_rewrite_tac o single)
  >> qpat_assum `!u y. Target q pcQ tag u y <=> Target q pcQ tagQ u y`
       (pure_rewrite_tac o single o GSYM)
  >> FIRST_PROVE
       [qpat_assum `EL (pc u) p <> AsmOp "JUMP"` (fn opcode =>
          qpat_assum `pcQ y = pcQ u + 1` (fn arm => simp_tac bool_ss [opcode,arm])),
        qpat_assum `EL (pc u) p = AsmOp "JUMP"` (fn opcode =>
          qpat_assum `Target q pcQ tag u y` (fn arm => simp_tac bool_ss [opcode,arm])),
        qpat_assum `EL (pc u) p = AsmOp "JUMPI"` (fn opcode =>
          qpat_assum `Target q pcQ tag u y` (fn arm => simp[NoAsms,opcode,arm]))]
QED

Resume prune_jump_cut_rows[rowQ]:
  gen_tac >> disch_tac >>
  `Keep u /\ u IN V` by (simp[Abbr `Keep`] >> metis_tac[]) >>
  `Row p a.as_call_ctx pc height tag edge u` by
    (qpat_assum `Rows p _ V {} rank pc height need tag boolean edge` mp_tac >>
     qpat_assum `Rows = _` (pure_rewrite_tac o single) >>
     simp_tac bool_ss [DIFF_EMPTY] >> strip_tac >> first_assum (drule_then ACCEPT_TAC)) >>
  qpat_assum `!u. u IN A ==> pcQ u < LENGTH q /\ _`
    (drule_then (map_every assume_tac o CONJUNCTS)) >>
  qabbrev_tac `ins = EL (pc u) (p:asm_inst list)` >>
  `MEM ins q` by (qpat_assum `EL (pcQ u) q = _` (pure_rewrite_tac o single o GSYM) >>
    qpat_assum `Abbrev (ins = _)` (pure_rewrite_tac o single o REWRITE_RULE[markerTheory.Abbrev_def]) >>
    metis_tac[EL_MEM]) >>
  qabbrev_tac `U = \a. !k. k<a ==> tag u k=NONE` >>
  qabbrev_tac `resolved = \l. IS_SOME (FLOOKUP (SND(compute_label_offsets q)) l)` >>
  `!l. (ins = AsmPushLabel l \/ (?d. ins = AsmPushOfst l d)) ==> resolved l` by
    (gen_tac >> disch_tac >>
     `MEM l (asm_label_refs q)` by
       (simp[NoAsms,asm_label_refs_def,MEM_FLAT,MEM_MAP,PULL_EXISTS] >>
        qexists `ins` >> conj_tac >- first_assum ACCEPT_TAC >>
        qpat_x_assum `ins = AsmPushLabel l \/ _` strip_assume_tac >>
        pop_assum (fn th => simp[NoAsms,th])) >>
     `MEM (AsmLabel l) q \/ MEM (AsmDataHeader l) q` by
       (qpat_assum `asm_static_wf q` (mp_tac o REWRITE_RULE[asm_static_wf_def]) >>
        strip_tac >> first_assum (drule_then ACCEPT_TAC)) >>
     `l IN FDOM (SND (compute_label_offsets q))` by
       (pure_rewrite_tac [symbolResolveTheory.compute_label_offsets_def,
                          asmToBytecodeProofsTheory.clo_step_eq] >>
        irule clo_FDOM >> simp[NoAsms] >>
        FIRST_PROVE [disj1_tac >> first_assum ACCEPT_TAC,
                     disj2_tac >> first_assum ACCEPT_TAC]) >>
     simp[Abbr `resolved`, finite_mapTheory.FLOOKUP_DEF]) >>
  qabbrev_tac `fall = \w. pc w=pc u+1` >>
  qabbrev_tac `taken = Target p pc tag u` >>
  qabbrev_tac `fallQ = \y. pcQ y=pcQ u+1` >>
  qabbrev_tac `takenQ = Target q pcQ tagQ u` >>
  `!y. takenQ y <=> Target q pcQ tag u y` by simp[Abbr `takenQ`] >>
  `Check ins (height u) U (tag u 1=NONE) a.as_call_ctx.cc_static resolved
      (edge u) height fall taken` by
    (qpat_assum `Row p a.as_call_ctx pc height tag edge u` mp_tac >>
     qpat_assum `Row = _` (pure_rewrite_tac o single) >> BETA_TAC >>
     map_every (fn pat => qpat_assum pat
       (pure_rewrite_tac o single o GSYM o REWRITE_RULE[markerTheory.Abbrev_def]))
       [`Abbrev (ins = _)`, `Abbrev (U = _)`, `Abbrev (fall = _)`, `Abbrev (taken = _)`] >>
     qpat_assum `Check = _` (pure_rewrite_tac o single) >>
     CONV_TAC (REDEPTH_CONV (REWR_CONV LET_THM ORELSEC BETA_CONV)) >>
     qpat_assum `!l. (ins = AsmPushLabel l \/ _) ==> resolved l` mp_tac >>
     POP_ASSUM_LIST kall_tac >> Cases_on `ins` >> simp_tac (srw_ss()) []) >>
  `!w y. Move u F w y ==> height y = height w /\ fallQ y` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `!u take w y. Move u take w y ==> _`
       (drule_then (mp_tac o CONJUNCT2 o CONJUNCT2)) >>
     pure_rewrite_tac [COND_CLAUSES] >>
     qpat_assum `Abbrev (fallQ = _)` (pure_rewrite_tac o single o REWRITE_RULE[markerTheory.Abbrev_def]) >>
     BETA_TAC >> strip_tac >> conj_tac >> first_assum ACCEPT_TAC) >>
  `!w y. Move u T w y ==> height y = height w /\ takenQ y` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `!u take w y. Move u take w y ==> _`
       (drule_then (mp_tac o CONJUNCT2 o CONJUNCT2)) >>
     pure_rewrite_tac [COND_CLAUSES] >> strip_tac >> conj_tac >- first_assum ACCEPT_TAC >>
     qpat_assum `!y. takenQ y <=> _` (pure_rewrite_tac o single) >> first_assum ACCEPT_TAC) >>
  `E u = (\y. (ins <> AsmOp "JUMP" /\
                 ?w. edge u w /\ fall w /\ Move u F w y /\ height y = height w /\ fallQ y) \/
              ((ins = AsmOp "JUMP" \/ ins = AsmOp "JUMPI") /\
                 ?w. edge u w /\ taken w /\ Move u T w y /\ height y = height w /\ takenQ y))` by
    (simp_tac bool_ss [FUN_EQ_THM] >> gen_tac >>
     map_every (fn pat => qpat_assum pat
       (pure_rewrite_tac o single o REWRITE_RULE[markerTheory.Abbrev_def]))
       [`Abbrev (E = _)`, `Abbrev (R = _)`, `Abbrev (fall = _)`] >> BETA_TAC >>
     map_every (fn pat => qpat_assum pat
       (pure_rewrite_tac o single o GSYM o REWRITE_RULE[markerTheory.Abbrev_def]))
       [`Abbrev (ins = _)`, `Abbrev (taken = _)`] >>
     qpat_assum `u IN A` (pure_rewrite_tac o single) >>
     map_every (fn pat => qpat_assum pat mp_tac)
       [`!w y. Move u F w y ==> _`,`!w y. Move u T w y ==> _`] >>
     POP_ASSUM_LIST kall_tac >> metis_tac[]) >>
  `!take w. edge u w /\ (if take then taken w else fall w) ==> ?y. Move u take w y` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!u take w. Keep u /\ edge u w /\ _ ==> _` irule >>
     rpt (conj_tac >- first_assum ACCEPT_TAC) >>
     qpat_assum `if take then taken w else fall w` mp_tac >>
     map_every (fn pat => qpat_assum pat
       (pure_rewrite_tac o single o REWRITE_RULE[markerTheory.Abbrev_def]))
       [`Abbrev (taken = _)`, `Abbrev (fall = _)`] >> BETA_TAC >> simp[]) >>
  `Check ins (height u) U (tag u 1=NONE) a.as_call_ctx.cc_static resolved
       (E u) height fallQ takenQ` by
    (qpat_assum `Check ins _ U _ _ resolved (edge u) _ fall taken` mp_tac >>
     qpat_assum `E u = _` (pure_rewrite_tac o single) >>
     qpat_assum `Check = _` (pure_rewrite_tac o single) >>
     CONV_TAC (REDEPTH_CONV (REWR_CONV LET_THM ORELSEC BETA_CONV)) >>
     disch_tac >>
     irule (prune_specialize
       (Q.ISPECL [`edge u : (num#num)->bool`, `Move u : bool->(num#num)->(num#num)->bool`]
         prune_jump_retained_row_arms)) >>
     (conj_tac >- (
         gen_tac >> strip_tac >>
         qpat_assum `!take w. edge u w /\ _ ==> _`
           (qspecl_then [`F`,`w`] (mp_tac o SIMP_RULE bool_ss [])) >>
         (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
         disch_then (qx_choose_then `y` assume_tac) >> qexists `y` >>
         qpat_assum `!w y. Move u F w y ==> _` (drule_then strip_assume_tac) >>
         rpt conj_tac >> first_assum ACCEPT_TAC) >>
       conj_tac >- (
         gen_tac >> disch_then (CONJUNCTS_THEN2 assume_tac strip_assume_tac) >>
         qpat_assum `!take w. edge u w /\ _ ==> _`
           (qspecl_then [`T`,`w`] (mp_tac o SIMP_RULE bool_ss [])) >>
         (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
         disch_then (qx_choose_then `y` assume_tac) >> qexists `y` >>
         qpat_assum `!w y. Move u T w y ==> _` (drule_then strip_assume_tac) >>
         rpt conj_tac >> first_assum ACCEPT_TAC) >>
       first_assum ACCEPT_TAC)) >>
  qpat_assum `Row = _` (pure_rewrite_tac o single) >> BETA_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  map_every (fn pat => qpat_assum pat (pure_rewrite_tac o single))
    [`EL (pcQ u) q = _`, `t.as_call_ctx = _`, `!u k. tagQ u k = NONE <=> _`] >>
  map_every (fn pat => qpat_assum pat
    (pure_rewrite_tac o single o GSYM o REWRITE_RULE[markerTheory.Abbrev_def]))
    [`Abbrev (ins = _)`, `Abbrev (U = _)`, `Abbrev (resolved = _)`,
     `Abbrev (fallQ = _)`, `Abbrev (takenQ = _)`] >>
  first_assum ACCEPT_TAC
QED

Resume prune_jump_cut_rows[rootQ]:
  reverse conj_asm2_tac
  >- (qpat_assum `Demand tag boolean z v.sym_stack` mp_tac >>
      qpat_assum `Demand = _` (pure_rewrite_tac o single) >> BETA_TAC >>
      qpat_assum `!u k l i. tagQ u k = SOME(l,i) <=> _` (pure_rewrite_tac o single) >>
      disch_then (CONJUNCTS_THEN2 (mk_asm "oldLabel") assume_tac) >>
      reverse conj_tac >- first_assum ACCEPT_TAC >>
      rpt gen_tac >> disch_then (qx_choose_then `org` strip_assume_tac) >>
      asm "oldLabel" (drule_then ACCEPT_TAC)) >>
  qpat_assum `asm_sym_rel q eq t v`
    (CONJUNCTS_THEN2 (CONJUNCTS_THEN2 assume_tac (mk_asm "stackWords")) kall_tac o
     BETA_RULE o REWRITE_RULE [asm_sym_rel_def, LIST_REL_EL_EQN]) >>
  qpat_assum `Demand tagQ boolean z v.sym_stack` mp_tac >>
  qpat_assum `Demand = _` (pure_rewrite_tac o single) >> BETA_TAC >>
  disch_then (CONJUNCTS_THEN2 (mk_asm "labelDemand") (mk_asm "boolDemand")) >>
  `Slots q t.as_call_ctx height need tagQ boolean z` by
    first_assum (drule_then ACCEPT_TAC) >>
  qpat_assum `Slots q _ height need tagQ boolean z` mp_tac >>
  qpat_assum `Slots = _` (pure_rewrite_tac o single) >> BETA_TAC >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 (mk_asm "boolSlot") (mk_asm "labelSlot"))) >>
  qpat_assum `Shape = _` (pure_rewrite_tac o single) >> BETA_TAC >>
  (conj_tac >- simp[Abbr `pcQ`]) >>
  (conj_tac >- simp[]) >> simp_tac bool_ss [] >>
  (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac
  >- (rpt gen_tac >> disch_tac >>
      asm "labelSlot" (drule_then (map_every assume_tac o CONJUNCTS)) >>
      asm "labelDemand" (drule_then strip_assume_tac) >>
      ntac 2 (conj_tac >- first_assum ACCEPT_TAC) >>
      (conj_tac >- (
        qpat_assum `EL i q = AsmPushLabel l \/ EL i q = AsmPushOfst l 0`
          (DISJ_CASES_THEN assume_tac)
        >- (disj1_tac >> first_assum ACCEPT_TAC) >>
        disj2_tac >> disj1_tac >> qexists `0` >> first_assum ACCEPT_TAC)) >>
      qpat_x_assum `?off dest. FLOOKUP _ l = SOME off /\ _`
        (qx_choose_then `off` (qx_choose_then `dest` strip_assume_tac)) >>
      qexistsl [`off`,`dest`] >> ntac 3 (conj_tac >- first_assum ACCEPT_TAC) >>
      asm "stackWords" (drule_then mp_tac) >>
      qpat_assum `EL k v.sym_stack = Lab l 0` SUBST1_TAC >>
      rewrite_tac[sval_conc_def] >>
      qpat_assum `FLOOKUP (SND(compute_label_offsets q)) l = SOME off` SUBST1_TAC >>
      simp[NoAsms, EQ_IMP_THM]) >>
  gen_tac >> disch_tac >>
  asm "boolSlot" (drule_then strip_assume_tac) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  asm "boolDemand" (drule_then strip_assume_tac) >>
  asm "stackWords" (drule_then mp_tac) >>
  qpat_assum `EL k v.sym_stack = Val _` SUBST1_TAC >>
  simp[NoAsms, sval_conc_def, EQ_IMP_THM]
QED

Resume prune_jump_cut_rows[package]:
  `FINITE V` by
    (qpat_assum `Open p _ _ V {} rank pc height need tag boolean edge` mp_tac >>
     qpat_assum `Open = _` (pure_rewrite_tac o single) >>
     CONV_TAC (REDEPTH_CONV (REWR_CONV LET_THM ORELSEC BETA_CONV)) >>
     disch_then (ACCEPT_TAC o CONJUNCT1)) >>
  `FINITE A` by
    (irule SUBSET_FINITE >> qexists `V` >>
     (conj_tac >- first_assum ACCEPT_TAC) >>
     rewrite_tac[SUBSET_DEF] >> gen_tac >> disch_tac >>
     qpat_assum `!u. u IN A ==> u IN V /\ _`
       (drule_then (ACCEPT_TAC o CONJUNCT1))) >>
  `Rows q t.as_call_ctx A {} rank pcQ height need tagQ boolean E` by
    (qpat_assum `Rows = _` (pure_rewrite_tac o single) >> simp_tac bool_ss [DIFF_EMPTY] >>
     (conj_tac >- first_assum ACCEPT_TAC) >>
     reverse conj_tac >- first_assum ACCEPT_TAC >>
     rpt gen_tac >> disch_tac >>
     rename1 `E u y` >>
     (conj_tac >- (qpat_assum `!u y. E u y <=> _` (qspecl_then [`u`,`y`] mp_tac) >>
                   simp_tac bool_ss [] >> metis_tac[])) >>
     qpat_assum `!u y. E u y ==> _ /\ _ /\ Flow q pcQ height tagQ boolean u y /\ _`
       (drule_then (map_every assume_tac o CONJUNCTS)) >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `!u y. E u y ==> Flow q pcQ height tagQ boolean u y /\ Control q pcQ tagQ u y` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `!u y. E u y ==> _ /\ _ /\ Flow q pcQ height tagQ boolean u y /\ _`
       (drule_then (ACCEPT_TAC o CONJUNCT2 o CONJUNCT2))) >>
  qabbrev_tac `liveSet = {u | u IN A /\ Reach E z u}` >>
  qabbrev_tac `liveEdge = \u y. u IN liveSet /\ E u y` >>
  qexistsl [`liveSet`,`z`,`rank`,`pcQ`,`height`,`need`,`tagQ`,`boolean`,`liveEdge`] >>
  map_every (fn pat => qpat_x_assum pat SUBST_ALL_TAC)
    [`Rows = _`,`Slots = _`,`Row = _`,`Check = _`,`Open = _`,`Shape = _`,
     `Demand = _`,`Reach = _`,`Control = _`,`Target = _`,`Flow = _`,`Inherit = _`] >>
  (let
     val normalize = TOP_DEPTH_CONV (FIRST_CONV
       [BETA_CONV, REWR_CONV LET_THM, REWR_CONV DIFF_EMPTY,
        REWR_CONV ratTheory.RAT_OF_NUM_LES, HO_REWR_CONV check_case_presentation])
   in
     rule_assum_tac (CONV_RULE normalize) >> CONV_TAC normalize >>
     mp_tac (CONV_RULE normalize (prune_specialize
       (Q.SPECL [`q`,`v`,`t`,`A`,`z`,`\u. rat$rat_of_num (rank u)`,
                  `pcQ`,`height`,`need`,`tagQ`,`boolean`,`E`] pending_rows_rooted_package)))
   end) >>
  (impl_tac >- (
    ntac 4 (conj_tac >- first_assum ACCEPT_TAC) >>
    conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac
      (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac kall_tac)))) >>
  map_every (fn pat => qpat_assum pat
    (pure_rewrite_tac o single o REWRITE_RULE[markerTheory.Abbrev_def]))
    [`Abbrev (liveEdge = _)`, `Abbrev (liveSet = _)`] >>
  BETA_TAC >>
  ntac 4 (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >> first_assum ACCEPT_TAC
QED

Finalise prune_jump_cut_rows


(* Transfer a protected terminal observation at the actual bytes on each
   side. The backward bridge provides the destination concrete count. *)
Theorem prune_jump_terminal_transport[local]:
  !p. p = pre ++ [AsmPushLabel x; AsmOp "JUMP"; AsmLabel x] ++ tail ==>
  !q. q = pre ++ [AsmLabel x] ++ tail ==>
  !sp. sp = (s with as_code := assemble p ++ data) ==>
  !sq. sq = (s with as_code := assemble q ++ data) ==>
  !env. env = asm_data_env p sp.as_code ==>
  !runAsm. runAsm = (\r. asm_steps (SND(compute_label_offsets r)) (build_offset_to_pc r) r) ==>
  s.as_pc = 0 /\ asm_static_wf p /\ asm_static_wf q /\
  asm_data_env q sq.as_code = env /\
  (runAsm p n sp = AsmRevert out \/ runAsm p n sp = AsmFault out) /\
  sym_terminal (sym_steps p env n (sym_init s)) ==>
  ?j t. (runAsm q j sq = AsmRevert t \/ runAsm q j sq = AsmFault t) /\
    sym_terminal (sym_steps q env j (sym_init s)) /\ t.as_requests = out.as_requests
Proof
  prune_introduce [`p`,`q`,`sp`,`sq`,`env`,`runAsm`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `asm_refines p q` by
    (map_every (fn pat => qpat_assum pat SUBST1_TAC) [`p = _`, `q = _`] >>
     mp_tac (Q.INST [`pat` |-> `[AsmPushLabel x; AsmOp "JUMP"]`,
                     `repl` |-> `[]`, `pfx` |-> `pre`, `sfx` |-> `AsmLabel x :: tail`]
                     asm_splice_window_refines) >>
     (impl_tac >- simp[NoAsms, asm_splice_ok_def, is_data_inst_def,
                       asm_label_refs_def, symbolResolveTheory.asm_inst_size_def,
                       asmOptPruneJumpsTheory.jump_to_next_window_refines]) >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >> disch_then ACCEPT_TAC) >>
  `sym_init sp = sym_init s /\ sym_init sq = sym_init s /\
   sp.as_pc = 0 /\ sq.as_pc = 0` by
    simp[sym_init_def, asm_state_component_equality] >>
  `asm_data_env_ok p env sp.as_code /\ asm_data_env_ok q env sq.as_code` by
    metis_tac[asm_data_env_ok_asm_data_env] >>
  `sym_terminal (sym_run p env n (sym_init s))` by
    (drule_then (qspec_then `0` mp_tac) codegenSymRelTheory.sym_steps_terminal_run >>
     simp_tac bool_ss [ADD_CLAUSES] >> disch_then SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  qpat_assum `asm_refines p q` (drule_then
    (qspecl_then [`env`,`s`,`n`] mp_tac o CONJUNCT2 o CONJUNCT2) o REWRITE_RULE[asm_refines_def]) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> disch_then (qx_choose_then `fuelQ` assume_tac) >>
  `sym_terminal (sym_run q env fuelQ (sym_init s))` by
    ((qpat_assum `sym_result_rel _ _` mp_tac >>
     Cases_on `sym_run p env n (sym_init s)` >> Cases_on `sym_run q env fuelQ (sym_init s)` >>
     simp[sym_result_rel_def,sym_terminal_def] >> (gvs[sym_result_rel_def, sym_terminal_def]))) >>
  `?i. sym_result_rel (sym_run p env n (sym_init s)) (asm_result_sym (runAsm p i sp))` by
    (qpat_assum `runAsm = _` SUBST1_TAC >> BETA_TAC >>
     qpat_assum `sym_init sp = sym_init s` (once_rewrite_tac o single o GSYM) >>
     irule asm_sym_backward >> rpt conj_tac >>
     (first_assum ACCEPT_TAC ORELSE
       (qpat_assum `sym_init sp = sym_init s` SUBST1_TAC >> first_assum ACCEPT_TAC))) >>
  `sym_terminal (asm_result_sym (runAsm p i sp))` by
    metis_tac[finalizerContractTheory.sym_result_rel_terminal] >>
  `runAsm p (n+i) sp = runAsm p n sp /\ runAsm p (i+n) sp = runAsm p i sp` by
    (conj_tac
     >- (qpat_assum `runAsm p n sp = _ \/ _` strip_assume_tac >>
         qpat_assum `runAsm = _` SUBST_ALL_TAC >> rule_assum_tac BETA_RULE >> BETA_TAC >>
         (once_rewrite_tac[stackOpSimTheory.asm_steps_add]) >>
         qpat_assum `asm_steps _ _ _ n sp = _` SUBST1_TAC >> simp[NoAsms]) >>
     Cases_on `runAsm p i sp` >>
     qpat_assum `sym_terminal (asm_result_sym _)` mp_tac >>
     simp[NoAsms, asm_result_sym_def,sym_terminal_def] >>
     qpat_assum `runAsm = _` SUBST_ALL_TAC >> rule_assum_tac BETA_RULE >> BETA_TAC >>
     once_rewrite_tac[stackOpSimTheory.asm_steps_add] >>
     qpat_assum `asm_steps _ _ _ i sp = _` SUBST1_TAC >> simp[NoAsms]) >>
  `runAsm p i sp = runAsm p n sp` by metis_tac[ADD_COMM] >>
  `?j. sym_result_rel (sym_run q env fuelQ (sym_init s)) (asm_result_sym (runAsm q j sq))` by
    (qpat_assum `runAsm = _` SUBST1_TAC >> BETA_TAC >>
     qpat_assum `sym_init sq = sym_init s` (once_rewrite_tac o single o GSYM) >>
     irule asm_sym_backward >> rpt conj_tac >>
     (first_assum ACCEPT_TAC ORELSE
       (qpat_assum `sym_init sq = sym_init s` SUBST1_TAC >> first_assum ACCEPT_TAC))) >>
  `asm_sym_rel q env sq (sym_init s)` by
    (qpat_assum `sym_init sq = sym_init s` (once_rewrite_tac o single o GSYM) >>
     irule asm_sym_rel_init >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  `!v. sym_steps q env j (sym_init s) <> SymOK v` by
    (gen_tac >> disch_tac >>
     drule_all codegenSymRelTheory.asm_sym_steps_lockstep >>
     disch_then (qx_choose_then `vC` (assume_tac o CONJUNCT1)) >>
     `runAsm q j sq = AsmOK vC` by
       (qpat_assum `runAsm = _` SUBST1_TAC >> BETA_TAC >> first_assum ACCEPT_TAC) >>
     qpat_assum `sym_result_rel (sym_run q _ _ _) _` mp_tac >>
     qpat_assum `runAsm q j sq = AsmOK vC` SUBST1_TAC >>
     Cases_on `sym_run q env fuelQ (sym_init s)` >> simp[NoAsms, asm_result_sym_def, sym_result_rel_def]) >>
  `sym_terminal (sym_steps q env j (sym_init s))` by
    (qpat_assum `sym_terminal (sym_run q _ _ _)`
       (mp_tac o CONJUNCT2 o MATCH_MP (Q.SPEC `j` asmSpliceTheory.sym_run_terminal_steps)) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     disch_then (once_rewrite_tac o single o GSYM) >> first_assum ACCEPT_TAC) >>
  `sym_result_rel (asm_result_sym (runAsm p n sp)) (asm_result_sym (runAsm q j sq))` by
    (`sym_result_rel (asm_result_sym (runAsm p n sp)) (sym_run p env n (sym_init s))` by
       (qpat_assum `sym_result_rel (sym_run p _ _ _) _` mp_tac >>
        qpat_assum `runAsm p i sp = runAsm p n sp` SUBST1_TAC >>
        Cases_on `asm_result_sym (runAsm p n sp)` >> Cases_on `sym_run p env n (sym_init s)` >>
        simp[NoAsms,sym_result_rel_def, EQ_SYM_EQ]) >>
     metis_tac[finalizerContractTheory.sym_result_rel_trans]) >>
  qexists `j` >>
  qpat_assum `sym_terminal (sym_steps q env j (sym_init s))` (pure_rewrite_tac o single) >>
  qpat_assum `sym_result_rel (asm_result_sym _) (asm_result_sym _)` mp_tac >>
  qpat_assum `runAsm p n sp = _ \/ _` (DISJ_CASES_THEN SUBST1_TAC) >>
  Cases_on `runAsm q j sq` >>
  simp[NoAsms, asm_result_sym_def, sym_result_rel_def] >>
  disch_then (mp_tac o AP_TERM ``\a:asm_state. a.as_requests``) >>
  simp[NoAsms, sym_obs_def, sym_init_def, EQ_SYM_EQ]
QED


Theorem prune_inefficient_jumps_abort_certificate:
  !orig s data req_bound.
  !Shape. Shape = (\p cc req pc height need tag boolean i (t:asm_state).
    t.as_pc = pc i /\ LENGTH t.as_stack = height i /\
    t.as_call_ctx = cc /\ t.as_requests = req /\
    (need i ==> t.as_call_ctx.cc_static) /\
    (!k l origin. tag i k = SOME(l,origin) ==>
       k < height i /\ origin < LENGTH p /\
       (EL origin p = AsmPushLabel l \/
        (?d. EL origin p = AsmPushOfst l d) \/ EL origin p = AsmDataLabel l) /\
       ?off dest.
         FLOOKUP (SND(compute_label_offsets p)) l = SOME off /\
         off < dimword(:256) /\
         FLOOKUP (build_offset_to_pc p) off = SOME dest /\
         EL k t.as_stack = (n2w off:bytes32)) /\
    (!k. boolean i k ==> k < height i /\
       (EL k t.as_stack = 0w \/ EL k t.as_stack = 1w))) ==>
  !target. target = (\p pc tag (x:num#num) (y:num#num).
    ?l origin off. tag x 0 = SOME(l,origin) /\
      FLOOKUP (SND(compute_label_offsets p)) l = SOME off /\
      off < dimword(:256) /\ FLOOKUP (build_offset_to_pc p) off = SOME(pc y)) ==>
  !Flow. Flow = (\p pc height tag boolean (x:num#num) (y:num#num).
    !hi. hi = height x ==>
    !hj. hj = height y ==>
    !ins. ins = EL (pc x) p ==>
    !inherit. inherit =
      (\(src:num -> num option)
        (fresh:num -> (string#num)option) (bnew:num -> bool).
        (!k l origin. tag y k = SOME(l,origin) ==>
           k < hj /\ (fresh k = SOME(l,origin) \/
             ?a. src k = SOME a /\ a < hi /\ tag x a = SOME(l,origin))) /\
        (!k. boolean y k ==> k < hj /\
           (bnew k \/ ?a. src k = SOME a /\ a < hi /\ boolean x a))) ==>
    case ins of
      AsmLabel l => hj = hi /\ inherit (\k. SOME k) (\k. NONE) (\k. F)
    | AsmPush bs => hj = hi+1 /\
        inherit (\k. if k=0 then NONE else SOME(k-1)) (\k. NONE)
          (\k. k=0 /\ !t u.
            asm_step (SND(compute_label_offsets p)) (build_offset_to_pc p)
              (AsmPush bs) t = AsmOK u ==>
            (EL 0 u.as_stack = 0w \/ EL 0 u.as_stack = 1w))
    | AsmPushLabel l => hj = hi+1 /\
        inherit (\k. if k=0 then NONE else SOME(k-1))
          (\k. if k=0 then SOME(l,pc x) else NONE) (\k. F)
    | AsmPushOfst l d => hj = hi+1 /\
        inherit (\k. if k=0 then NONE else SOME(k-1))
          (\k. if k=0 /\ d=0 then SOME(l,pc x) else NONE) (\k. F)
    | AsmOp name =>
        (case ALOOKUP dup_table name of
           SOME n => n < hi /\ hj = hi+1 /\
             inherit (\k. SOME(if k=0 then n else k-1)) (\k. NONE) (\k. F)
         | NONE => case ALOOKUP swap_table name of
             SOME n => 0 < n /\ n < hi /\ hj = hi /\
               inherit (\k. SOME(if k=0 then n else if k=n then 0 else k))
                 (\k. NONE) (\k. F)
           | NONE =>
               !a. a = asm_op_arity name ==>
               !m. m = hj + a - hi ==>
               a <= hi /\ hj = m+(hi-a) /\
               ((name="JUMP" \/ name="JUMPI") ==> m=0) /\
               inherit (\k. if k<m then NONE else SOME(k-m+a)) (\k. NONE)
                 (\k. k=0 /\ m=1 /\ asm_returns_zero_or_one ins /\
                   !t u. LENGTH t.as_stack=hi /\
                     asm_step (SND(compute_label_offsets p)) (build_offset_to_pc p)
                       ins t=AsmOK u ==>
                     (EL 0 u.as_stack=0w \/ EL 0 u.as_stack=1w)))
    | _ => F) ==>
  !Rows. Rows = (\p cc V rank pc height need tag boolean edge.
    !lo. lo = SND (compute_label_offsets p) ==>
    (!x. x IN V ==>
      (need x ==> cc.cc_static) /\
      (!k. boolean x k ==> k < height x /\ tag x k=NONE) /\
      (!k l origin. tag x k = SOME(l,origin) ==>
         k < height x /\ origin < LENGTH p /\
         (EL origin p = AsmPushLabel l \/ EL origin p = AsmPushOfst l 0) /\
         ?off dest. FLOOKUP lo l = SOME off /\ off < dimword(:256) /\
                    FLOOKUP (build_offset_to_pc p) off = SOME dest)) /\
    (!x y. edge x y ==> x IN V /\ y IN V /\ rank y < rank x /\ Flow p pc height tag boolean x y) /\
    (!x. x IN V ==>
      pc x < LENGTH p /\
      (!h. h = height x ==>
      !fall. fall = (\y. pc y = pc x+1) ==>
      !arm. arm = (\P n. ?y. edge x y /\ P y /\ height y = n) ==>
      !legal. legal = (\P n. !y. edge x y ==> P y /\ height y = n) ==>
      !next. next = (\n. arm fall n /\ legal fall n) ==>
      !untagged. untagged = (\a. !k. k<a ==> tag x k=NONE) ==>
      !stop. stop = (\a. a<=h /\ untagged a /\ !y. ~edge x y) ==>
      case EL (pc x) p of
        AsmLabel l => next h
      | AsmPush bs => next (h+1)
      | AsmPushLabel l => IS_SOME (FLOOKUP lo l) /\ next (h+1)
      | AsmPushOfst l d => IS_SOME (FLOOKUP lo l) /\ next (h+1)
      | AsmOp name =>
          if name="INVALID" then stop 0
          else if name="REVERT" then stop 2
          else if MEM name ["SSTORE";"TSTORE";"LOG0";"LOG1";"LOG2";"LOG3";"LOG4"]
               then cc.cc_static /\ stop (asm_op_arity name)
          else
            (case ALOOKUP dup_table name of
               SOME n => n<h /\ next (h+1)
             | NONE => case ALOOKUP swap_table name of
                 SOME n => 0<n /\ n<h /\ next h
               | NONE =>
                   if name="JUMP" then
                      1<=h /\ arm (target p pc tag x) (h-1) /\ legal (target p pc tag x) (h-1)
                   else if name="JUMPI" then
                      2<=h /\ tag x 1=NONE /\ arm fall (h-2) /\ arm (target p pc tag x) (h-2) /\
                      legal (\y. fall y \/ target p pc tag x y) (h-2)
                   else
                      ?m. static_abort_straight name m /\ asm_op_arity name <= h /\
                          untagged (asm_op_arity name) /\ next (h-asm_op_arity name+m))
      | _ => F))) ==>
  !Open. Open = (\p cc req (V:(num#num)->bool) X rank pc height need
    (tag:(num#num)->num->(string#num)option)
    (boolean:(num#num)->num->bool) edge.
    !S. S = Shape p cc req pc height need tag boolean ==>
    FINITE V /\ X SUBSET V /\
    (!x. x IN V ==> ?t. S x t) /\
    (!x. x IN V DIFF X ==> pc x < LENGTH p) /\
    (!x y. edge x y ==>
       x IN V DIFF X /\ y IN V /\ rank y < rank x /\
       Flow p pc height tag boolean x y /\
       (if EL (pc x) p = AsmOp "JUMP" then target p pc tag x y
        else if EL (pc x) p = AsmOp "JUMPI" then pc y = pc x+1 \/ target p pc tag x y
        else pc y = pc x+1)) /\
    (!x t. x IN V DIFF X /\ S x t ==>
       (?u. (asm_steps (SND(compute_label_offsets p)) (build_offset_to_pc p)
                    p 1 t = AsmRevert u \/
              asm_steps (SND(compute_label_offsets p)) (build_offset_to_pc p)
                    p 1 t = AsmFault u) /\ u.as_requests=req) \/
       (?y u. edge x y /\
          asm_steps (SND(compute_label_offsets p)) (build_offset_to_pc p)
            p 1 t = AsmOK u /\ S y u))) ==>
  !Reach. Reach = (\(edge:(num#num)->(num#num)->bool) e x.
    ?n (path:num->num#num).
      path 0=e /\ path n=x /\ !k. k<n ==> edge (path k) (path(SUC k))) ==>
  !bytes. bytes = (\p. assemble p ++ data) ==>
  !env0. env0 = asm_data_env orig (bytes orig) ==>
  !M_R. M_R = (\p.
    !start. start = (s with as_code := bytes p) ==>
    !run. run = asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p ==>
    s.as_pc = 0 /\ s.as_code = bytes orig /\
    asm_static_wf orig /\ asm_static_wf p /\
    FILTER is_data_inst p = FILTER is_data_inst orig /\
    ((?n out.
        (run n start = AsmRevert out \/ run n start = AsmFault out) /\
        sym_terminal (sym_steps p env0 n (sym_init s)) /\
        out.as_requests <<= req_bound) \/
     (?j t u cc req (V:(num#num)->bool) e (rank:(num#num)->num)
         pc height need tag boolean edge.
        run j start = AsmOK t /\
        sym_steps p env0 j (sym_init s) = SymOK u /\
        asm_sym_rel p (asm_data_env p (bytes p)) t u /\
        t.as_pc = u.sym_base.as_pc /\ LENGTH t.as_stack = LENGTH u.sym_stack /\
        t.as_call_ctx = u.sym_base.as_call_ctx /\ t.as_requests = u.sym_base.as_requests /\
        t.as_call_ctx = cc /\ t.as_requests = req /\ req <<= req_bound /\
        Rows p cc V rank pc height need tag boolean edge /\
        Open p cc req V {} rank pc height need tag boolean edge /\
        e IN V /\ (!x. x IN V ==> Reach edge e x) /\
        Shape p cc req pc height need tag boolean e t /\
        (!k l origin. tag e k = SOME(l,origin) ==>
           k < LENGTH u.sym_stack /\ EL k u.sym_stack = Lab l 0) /\
        (!k. boolean e k ==>
           k < LENGTH u.sym_stack /\ (EL k u.sym_stack = Val 0w \/ EL k u.sym_stack = Val 1w))))) ==>
  !p. M_R p ==> M_R (FST (prune_inefficient_jumps p))
Proof
  ntac 4 gen_tac >>
  prune_introduce [`Shape`,`target`,`Flow`,`Rows`,`Open`,`Reach`,`bytes`,`env0`,`M_R`] >>
  match_mp_tac (Q.INST [`P` |-> `M_R`] prune_jumps_walk_preserves_contextual) >> rpt gen_tac >>
  disch_then (CONJUNCTS_THEN2 mp_tac assume_tac) >>
  Cases_on `a` >> simp[NoAsms, asm_jump_to_next_def] >>
  Cases_on `c` >> simp[NoAsms] >>
  disch_then (CONJUNCTS_THEN SUBST_ALL_TAC) >>
  rename1 `M_R (pre ++ [AsmLabel x] ++ tail)` >>
  qabbrev_tac `p = pre ++ [AsmPushLabel x; AsmOp "JUMP"; AsmLabel x] ++ tail` >>
  qabbrev_tac `q = pre ++ [AsmLabel x] ++ tail` >>
  qpat_x_assum `M_R p` mp_tac >>
  qpat_assum `M_R = _` (pure_rewrite_tac o single) >>
  CONV_TAC (TOP_DEPTH_CONV (REWR_CONV LET_THM ORELSEC BETA_CONV)) >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac
      (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac mp_tac))))) >>
  `asm_static_wf q /\ FILTER is_data_inst q = FILTER is_data_inst p` by
    (mp_tac (prune_specialize prune_jump_layout) >>
     qpat_assum `asm_static_wf p` mp_tac >>
     simp[NoAsms, Abbr `p`, Abbr `q`]) >>
  `FILTER is_data_inst q = FILTER is_data_inst orig` by metis_tac[] >>
  `asm_data_env p (bytes p) = env0 /\ asm_data_env q (bytes q) = env0` by
    (qpat_assum `env0 = _` SUBST1_TAC >> qpat_assum `bytes = _` SUBST1_TAC >> BETA_TAC >>
     conj_tac >> sym_tac >> irule asm_data_env_agree >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_tac >> ntac 5 (conj_tac >- first_assum ACCEPT_TAC) >>
  pop_assum (DISJ_CASES_THEN (REPEAT_TCL CHOOSE_THEN (map_every assume_tac o CONJUNCTS)))
  >- (disj1_tac >>
      qmatch_asmsub_rename_tac `sym_terminal (sym_steps p env0 n (sym_init s))` >>
      qmatch_asmsub_rename_tac `out.as_requests <<= req_bound` >>
      mp_tac (Q.INST [`n` |-> `n`, `out` |-> `out`]
        (prune_specialize prune_jump_terminal_transport)) >>
      CONV_TAC (TOP_DEPTH_CONV (REWR_CONV LET_THM ORELSEC BETA_CONV)) >>
      map_every (fn pat => qpat_assum pat (pure_rewrite_tac o single o GSYM o REWRITE_RULE[markerTheory.Abbrev_def]))
        [`Abbrev (p = _)`, `Abbrev (q = _)`] >>
      qpat_assum `bytes = _` SUBST_ALL_TAC >> rule_assum_tac BETA_RULE >> BETA_TAC >>
      simp[NoAsms] >>
      map_every (fn pat => qpat_assum pat (pure_rewrite_tac o single))
        [`asm_data_env p _ = env0`, `asm_data_env q _ = env0`] >>
      (impl_tac >- (rpt conj_tac >> simp[])) >>
      disch_then (qx_choose_then `j` (qx_choose_then `t` (map_every assume_tac o CONJUNCTS))) >>
      qexistsl [`j`, `t`] >> rpt conj_tac >> (first_assum ACCEPT_TAC ORELSE simp[])) >>
  disj2_tac >>
  qmatch_asmsub_rename_tac `sym_steps p env0 j (sym_init s) = SymOK u` >>
  qmatch_asmsub_rename_tac `asm_sym_rel p _ t u` >>
  qmatch_asmsub_rename_tac `Rows p cc V rank pc height need tag boolean edge` >>
  qmatch_asmsub_rename_tac `Shape p cc req pc height need tag boolean e t` >>
  `!code. sym_init (s with as_code := code) = sym_init s` by simp[sym_init_def] >>
  mp_tac (Q.INST [`s` |-> `s with as_code := bytes (p:asm_inst list)`, `n` |-> `j`,
                  `a` |-> `t`, `ss` |-> `u`] (prune_specialize prune_jump_cut_rows)) >>
  CONV_TAC (TOP_DEPTH_CONV (REWR_CONV LET_THM ORELSEC BETA_CONV)) >>
  map_every (fn pat => qpat_assum pat (pure_rewrite_tac o single o GSYM o REWRITE_RULE[markerTheory.Abbrev_def]))
    [`Abbrev (p = _)`, `Abbrev (q = _)`] >>
  qpat_x_assum `t.as_call_ctx = cc` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `t.as_requests = req` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `M_R = _` kall_tac >>
  map_every (fn pat => qpat_x_assum pat SUBST_ALL_TAC)
    [`bytes = _`, `Rows = _`, `Open = _`, `Shape = _`, `Reach = _`, `Flow = _`, `target = _`] >>
  (let
     val normalize = TOP_DEPTH_CONV (FIRST_CONV
       [BETA_CONV, REWR_CONV LET_THM, REWR_CONV DIFF_EMPTY,
        HO_REWR_CONV check_case_presentation])
   in
     rule_assum_tac (CONV_RULE normalize) >> CONV_TAC normalize
   end) >>
  qpat_assum `!code. sym_init _ = _` (fn th =>
    pure_rewrite_tac[asm_state_accfupds, asm_state_fupdfupds, combinTheory.K_THM,
                     combinTheory.K_o_THM, th]) >>
  map_every (fn pat => qpat_assum pat (fn th =>
      rule_assum_tac (PURE_REWRITE_RULE [th]) >> pure_rewrite_tac[th]))
    [`asm_data_env p _ = env0`, `asm_data_env q _ = env0`] >>
  (impl_tac >- (
    ntac 5 (conj_tac >- (first_assum ACCEPT_TAC ORELSE REFL_TAC)) >>
    qexistsl [`V`, `e`, `rank`, `pc`, `height`, `need`, `tag`, `boolean`, `edge`] >>
    rpt (conj_tac >- first_assum ACCEPT_TAC) >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choose_then `k` (qx_choose_then `v` (qx_choose_then `w`
    (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac
     (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac
      (CONJUNCTS_THEN2 assume_tac mp_tac)))))))) >>
  disch_then (mk_asm "destination_table") >>
  qpat_assum `!code. sym_init _ = _` (fn th =>
    map_every (fn pat => qpat_x_assum pat (assume_tac o
      REWRITE_RULE [combinTheory.K_o_THM, th]))
      [`sym_steps q env0 k _ = SymOK v`, `asm_steps _ _ q k _ = AsmOK w`]) >>
  `w.as_pc = v.sym_base.as_pc /\ LENGTH w.as_stack = LENGTH v.sym_stack` by
    (qpat_assum `asm_sym_rel q env0 w v` (mp_tac o MATCH_MP asm_sym_rel_pc) >> simp[]) >>
  `w.as_call_ctx = v.sym_base.as_call_ctx /\ w.as_requests = v.sym_base.as_requests` by
    (qpat_assum `asm_sym_rel q env0 w v` (mp_tac o REWRITE_RULE [asm_sym_rel_def]) >>
     strip_tac >> simp[]) >>
  `w.as_requests <<= req_bound` by
    (qpat_assum `w.as_requests = t.as_requests` SUBST1_TAC >> first_assum ACCEPT_TAC) >>
  qexistsl [`k`,`w`,`v`,`w.as_call_ctx`,`w.as_requests`] >>
  (* Discharge only the fixed endpoint conjuncts, leaving the table intact. *)
  ASSUM_LIST (fn facts =>
    let
      val known = FIRST_CONV (map (REWR_CONV o EQT_INTRO) facts @ [REWR_CONV REFL_CLAUSE])
      val peel = LAND_CONV known THENC REWR_CONV (CONJUNCT1 (SPEC_ALL AND_CLAUSES))
    in
      CONV_TAC (STRIP_QUANT_CONV (EVERY_CONV (List.tabulate (10, fn _ => peel))))
    end) >>
  asm "destination_table" ACCEPT_TAC
QED
