Theory staticAbortOptPruneUnreachableActualRoot
Ancestors
  codegenSymRel asmSymOwnCode
  staticAbortOptPruneUnreachablePrefix staticAbortOptPruneUnreachableLayout
  staticAbortOptPruneUnreachableZeroOrigin staticAbortProtectedActualPrefix
  staticAbortOptMergeJumpdestsLayout staticAbortProtectedTraceCoverage
  asmOptPruneUnreachable asmSymBridge asmSymPc asmSymSem asmSem
  finite_map list option words arithmetic

(* p0 fixes the entry bytes and the data environment for the entire walk.
   Only the current program p and its stopped PC are relocated here. *)
Theorem prune_one_actual_root_mode:
  !Shape p q d r tagQ env0 ssQ.
  Shape = (\p cc req pc height need tag boolean (v:num#num) (a:asm_state).
      a.as_pc = pc v /\ LENGTH a.as_stack = height v /\
      a.as_call_ctx = cc /\ a.as_requests = req /\
      (need v ==> a.as_call_ctx.cc_static) /\
      (!k l origin. tag v k = SOME(l,origin) ==>
         k < height v /\ origin < LENGTH p /\
         (EL origin p = AsmPushLabel l \/
          (?d. EL origin p = AsmPushOfst l d) \/ EL origin p = AsmDataLabel l) /\
         ?off dest.
           FLOOKUP (SND(compute_label_offsets p)) l = SOME off /\
           off < dimword(:256) /\
           FLOOKUP (build_offset_to_pc p) off = SOME dest /\
           EL k a.as_stack = (n2w off:bytes32)) /\
      (!k. boolean v k ==> k < height v /\
         (EL k a.as_stack = 0w \/ EL k a.as_stack = 1w))) ==>
  p = pre ++ [t;x] ++ tail ==> q = pre ++ [t] ++ tail ==>
  d = LENGTH pre + 1 ==> r = (\i. if i < d then i else i-1) ==>
  tagQ = (\v k. OPTION_MAP (\(l,i). (l,if i=d then
    (@j. j < LENGTH q /\ (EL j q = AsmPushLabel l \/ EL j q = AsmPushOfst l 0))
    else r i)) (tag v k)) ==>
  env0 = asm_data_env p0 (assemble p0 ++ data) ==>
  ssQ = sym_with_pc (r ss.sym_base.as_pc) ss ==>
    asm_terminal_op t /\ ~asm_reachable_marker x /\
    s.as_pc = 0 /\ s.as_code = assemble p0 ++ data /\
    asm_static_wf p0 /\ asm_static_wf p /\ FILTER is_data_inst p = FILTER is_data_inst p0 /\
    sym_steps_mode allow_own p env0 s.as_code n (sym_init s) = SymOK ss /\
    (if allow_own then asm_sym_rel_own (lo_reloc p p0) p env0 s.as_code
     else asm_sym_rel p (asm_data_env p (assemble p ++ data))) a ss /\
    Shape p cc req pc height need tag boolean e a /\
    (!k l origin. tag e k = SOME(l,origin) ==>
       k < LENGTH ss.sym_stack /\ EL k ss.sym_stack = Lab l 0) /\
    (!k. boolean e k ==> k < LENGTH ss.sym_stack /\
       (EL k ss.sym_stack = Val 0w \/ EL k ss.sym_stack = Val 1w)) ==>
    sym_steps_mode allow_own q env0 s.as_code n (sym_init s) = SymOK ssQ /\
    ?u. asm_steps (if allow_own then lo_reloc q p0 else SND(compute_label_offsets q)) (build_offset_to_pc q) q n
          (if allow_own then s else (s with as_code := assemble q ++ data)) = AsmOK u /\
        (if allow_own then asm_sym_rel_own (lo_reloc q p0) q env0 s.as_code
     else asm_sym_rel q (asm_data_env q (assemble q ++ data))) u ssQ /\
        u.as_pc = ssQ.sym_base.as_pc /\ LENGTH u.as_stack = LENGTH ssQ.sym_stack /\
        u.as_call_ctx = ssQ.sym_base.as_call_ctx /\ u.as_requests = ssQ.sym_base.as_requests /\
        Shape q cc req (r o pc) height need tagQ boolean e u /\
        (!k l origin. tagQ e k = SOME(l,origin) ==>
           k < LENGTH ssQ.sym_stack /\ EL k ssQ.sym_stack = Lab l 0) /\
        (!k. boolean e k ==> k < LENGTH ssQ.sym_stack /\
           (EL k ssQ.sym_stack = Val 0w \/ EL k ssQ.sym_stack = Val 1w))
Proof
  rpt gen_tac >>
  ntac 8 (disch_then (assume_tac o ONCE_REWRITE_RULE [GSYM markerTheory.Abbrev_def])) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `Z = \l j. j < LENGTH q /\ (EL j q = AsmPushLabel l \/ EL j q = AsmPushOfst l 0)` >>
  `p = pre ++ [t;x] ++ tail /\ q = pre ++ [t] ++ tail`
    by simp[Abbr `p`, Abbr `q`] >>
  `sym_steps_mode allow_own q env0 s.as_code n (sym_init s) = SymOK ssQ` by
    (drule_all (BETA_RULE (SIMP_RULE (pure_ss ++ boolSimps.UNWIND_ss) []
                           prune_one_stopped_prefix_mode)) >>
     disch_then (mp_tac o cj 2) >>
     simp[NoAsms, Abbr `ssQ`, Abbr `r`, Abbr `d`]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  `asm_refines p q` by
    (qpat_assum `p = _` SUBST1_TAC >> qpat_assum `q = _` SUBST1_TAC >>
     pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >> irule prune_one_refines >> simp[]) >>
  qpat_x_assum `p = _` kall_tac >> qpat_x_assum `q = _` kall_tac >>
  qpat_x_assum `asm_refines p q` (mp_tac o REWRITE_RULE[asm_refines_def]) >>
  impl_tac >- first_assum ACCEPT_TAC >>
  disch_then (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac kall_tac)) >>
  `FILTER is_data_inst q = FILTER is_data_inst p0` by metis_tac[] >>
  `?u. asm_steps (if allow_own then lo_reloc q p0 else SND (compute_label_offsets q))
      (build_offset_to_pc q) q n (if allow_own then s else (s with as_code := assemble q ++ data)) =
      AsmOK u /\
      (if allow_own then asm_sym_rel_own (lo_reloc q p0) q env0 s.as_code
       else asm_sym_rel q (asm_data_env q (assemble q ++ data))) u ssQ /\
      u.as_pc = ssQ.sym_base.as_pc /\ LENGTH u.as_stack = LENGTH ssQ.sym_stack /\
      u.as_call_ctx = ssQ.sym_base.as_call_ctx /\ u.as_requests = ssQ.sym_base.as_requests` by
    (qunabbrev_tac `env0` >>
     mp_tac (Q.INST [`p` |-> `p0`, `q` |-> `q`, `ss` |-> `ssQ`, `n` |-> `n`]
       stopped_symbolic_prefix_mode) >>
     (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
     qpat_assum `s.as_code = assemble p0 ++ data` (pure_rewrite_tac o single) >>
     disch_then ACCEPT_TAC) >>
  rename1 `asm_steps _ _ q n _ = AsmOK u` >>
  qexists `u` >> simp[] >>
  `ssQ.sym_stack = ss.sym_stack /\ ssQ.sym_base.as_pc = r ss.sym_base.as_pc /\
   ssQ.sym_base.as_call_ctx = ss.sym_base.as_call_ctx /\
   ssQ.sym_base.as_requests = ss.sym_base.as_requests`
    by simp[Abbr `ssQ`, sym_with_pc_def] >>
  `!k l j. tagQ e k = SOME(l,j) ==>
      ?i. tag e k = SOME(l,i) /\ j = (if i=d then (@j. Z l j) else r i)` by
    (simp[Abbr `tagQ`, Abbr `Z`, pairTheory.EXISTS_PROD] >> metis_tac[]) >>
  `!k l i. tagQ e k = SOME(l,i) ==>
      k < LENGTH ssQ.sym_stack /\ EL k ssQ.sym_stack = Lab l 0` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `!k l j. tagQ e k = _ ==> _` (drule_then strip_assume_tac) >> simp[]) >>
  simp[] >>
  (* Only the actual stopped endpoint is interpreted as a destination Shape. *)
  suspend "endpoint_shape"
QED

Resume prune_one_actual_root_mode[endpoint_shape]:
  `ss.sym_base.as_pc = a.as_pc /\ ss.sym_base.as_call_ctx = a.as_call_ctx /\
   ss.sym_base.as_requests = a.as_requests /\ LENGTH ss.sym_stack = LENGTH a.as_stack` by
    (qpat_assum `(if allow_own then asm_sym_rel_own _ _ _ _ else asm_sym_rel _ _) a ss` mp_tac >>
     Cases_on `allow_own` >> PURE_REWRITE_TAC [COND_CLAUSES, asm_sym_rel_def, asm_sym_rel_own_def] >>
     strip_tac >> fs[LIST_REL_EL_EQN]) >>
  qabbrev_tac `loQ = if allow_own then lo_reloc q p0 else SND (compute_label_offsets q)` >>
  `!k. k < LENGTH ssQ.sym_stack ==>
       sval_conc loQ (EL k ssQ.sym_stack) = SOME (EL k u.as_stack)` by
    (qpat_assum `(if allow_own then asm_sym_rel_own _ _ _ _ else asm_sym_rel _ _) u ssQ` mp_tac >>
     Cases_on `allow_own` >> PURE_REWRITE_TAC [COND_CLAUSES, asm_sym_rel_def, asm_sym_rel_own_def] >>
     simp[LIST_REL_EL_EQN, Abbr `loQ`]) >>
  qpat_x_assum `Shape p _ _ _ _ _ _ _ e a` mp_tac >>
  Q.UNABBREV_TAC `Shape` >> BETA_TAC >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  rewrite_tac[combinTheory.o_THM] >>
  ntac 5 (conj_tac >- metis_tac[]) >>
  conj_tac
  >- (rpt gen_tac >> disch_tac >>
      qpat_assum `!k l j. tagQ e k = _ ==> ?i. _`
        (drule_then (qx_choose_then `i` strip_assume_tac)) >>
      qpat_assum `!k l i. tag e k = _ ==> _ /\ _ /\ _ /\ ?off dest. _`
        (drule_then (map_every assume_tac o CONJUNCTS)) >>
      `i = d ==> Z l ((@j. Z l j))` by
        (disch_tac >>
         `MEM (Lab l 0) ssQ.sym_stack` by metis_tac[EL_MEM] >>
         `?j. Z l j` suffices_by
           (disch_then (mp_tac o SELECT_RULE) >> simp[]) >>
         drule_all (Q.INST [`q` |-> `q`, `ss` |-> `ssQ`, `env` |-> `env0`]
           stopped_lab_zero_producer_mode) >> simp[Abbr `Z`] >> metis_tac[]) >>
      `origin < LENGTH q /\ (EL origin q = AsmPushLabel l \/
        (?delta. EL origin q = AsmPushOfst l delta) \/ EL origin q = AsmDataLabel l)` by
        (qspecl_then [`pre`,`t`,`x`,`tail`] mp_tac (SIMP_RULE bool_ss [] prune_one_canonical_layout) >>
         pure_rewrite_tac[LET_THM] >> BETA_TAC >>
         map_every Q.UNABBREV_TAC [`r`,`d`,`p`,`q`] >>
         rule_assum_tac BETA_RULE >>
         impl_tac >- simp[] >>
         disch_then (qspecl_then [`l`,`i`,`\l. @j. Z l j`] mp_tac o cj 2) >>
         (impl_tac >-
           (conj_tac >- metis_tac[] >> disch_tac >>
            qpat_x_assum `i = LENGTH pre + 1 ==> _` (drule_then mp_tac) >>
            simp[Abbr `Z`] >> metis_tac[])) >>
         qpat_assum `origin = _` SUBST1_TAC >> simp[]) >>
      qpat_x_assum `?off dest. _`
        (qx_choose_then `off` (qx_choose_then `dest` (map_every assume_tac o CONJUNCTS))) >>
      `?fresh. FLOOKUP (SND(compute_label_offsets q)) l = SOME fresh /\
          fresh < dimword(:256) /\ FLOOKUP (build_offset_to_pc q) fresh = SOME (r dest)` by
        (qspecl_then [`pre`,`t`,`x`,`tail`] mp_tac (SIMP_RULE bool_ss [] prune_one_canonical_layout) >>
         pure_rewrite_tac[LET_THM] >> BETA_TAC >>
         map_every Q.UNABBREV_TAC [`r`,`d`,`p`,`q`] >> BETA_TAC >>
         impl_tac >- simp[] >>
         disch_then (qspecl_then [`l`,`off`,`dest`] mp_tac o cj 1) >>
         impl_tac >- simp[] >>
         disch_then (mp_tac o cj 6) >> simp[]) >>
      qpat_assum `!k l i. tagQ e k = _ ==> _ /\ _` (drule_then strip_assume_tac) >>
      simp[] >>
      qpat_assum `!n. n < LENGTH ssQ.sym_stack ==> sval_conc _ _ = _`
        (drule_then mp_tac) >>
      qpat_assum `EL k ssQ.sym_stack = Lab l 0` SUBST1_TAC >>
      rewrite_tac[sval_conc_def] >>
      `FLOOKUP loQ l = SOME fresh` by
        (Cases_on `allow_own` >> simp[Abbr `loQ`] >>
         metis_tac[canonical_jump_binding_relocated]) >>
      qpat_assum `FLOOKUP loQ l = SOME fresh` SUBST1_TAC >>
      simp[NoAsms, EQ_IMP_THM]) >>
  gen_tac >> disch_tac >>
  conj_tac >- metis_tac[] >>
  qpat_assum `!k. boolean e k ==> _ /\ (EL k ss.sym_stack = _ \/ _)`
    (drule_then strip_assume_tac) >>
  `k < LENGTH ssQ.sym_stack` by simp[] >>
  qpat_assum `!n. n < LENGTH ssQ.sym_stack ==> sval_conc _ _ = _`
    (drule_then mp_tac) >>
  qpat_assum `ssQ.sym_stack = ss.sym_stack` SUBST1_TAC >>
  qpat_assum `EL k ss.sym_stack = Val _` SUBST1_TAC >>
  simp[NoAsms, sval_conc_def] >> metis_tac[]
QED

Finalise prune_one_actual_root_mode

Theorem prune_one_actual_root:
  !Shape p q d r tagQ env0 ssQ.
  Shape = (\p cc req pc height need tag boolean (v:num#num) (a:asm_state).
      a.as_pc = pc v /\ LENGTH a.as_stack = height v /\
      a.as_call_ctx = cc /\ a.as_requests = req /\
      (need v ==> a.as_call_ctx.cc_static) /\
      (!k l origin. tag v k = SOME(l,origin) ==>
         k < height v /\ origin < LENGTH p /\
         (EL origin p = AsmPushLabel l \/
          (?d. EL origin p = AsmPushOfst l d) \/ EL origin p = AsmDataLabel l) /\
         ?off dest.
           FLOOKUP (SND(compute_label_offsets p)) l = SOME off /\
           off < dimword(:256) /\
           FLOOKUP (build_offset_to_pc p) off = SOME dest /\
           EL k a.as_stack = (n2w off:bytes32)) /\
      (!k. boolean v k ==> k < height v /\
         (EL k a.as_stack = 0w \/ EL k a.as_stack = 1w))) ==>
  p = pre ++ [t;x] ++ tail ==> q = pre ++ [t] ++ tail ==>
  d = LENGTH pre + 1 ==> r = (\i. if i < d then i else i-1) ==>
  tagQ = (\v k. OPTION_MAP (\(l,i). (l,if i=d then
    (@j. j < LENGTH q /\ (EL j q = AsmPushLabel l \/ EL j q = AsmPushOfst l 0))
    else r i)) (tag v k)) ==>
  env0 = asm_data_env p0 (assemble p0 ++ data) ==>
  ssQ = sym_with_pc (r ss.sym_base.as_pc) ss ==>
    asm_terminal_op t /\ ~asm_reachable_marker x /\
    s.as_pc = 0 /\ s.as_code = assemble p0 ++ data /\
    asm_static_wf p0 /\ asm_static_wf p /\ FILTER is_data_inst p = FILTER is_data_inst p0 /\
    sym_steps p env0 n (sym_init s) = SymOK ss /\
    asm_sym_rel p (asm_data_env p (assemble p ++ data)) a ss /\
    Shape p cc req pc height need tag boolean e a /\
    (!k l origin. tag e k = SOME(l,origin) ==>
       k < LENGTH ss.sym_stack /\ EL k ss.sym_stack = Lab l 0) /\
    (!k. boolean e k ==> k < LENGTH ss.sym_stack /\
       (EL k ss.sym_stack = Val 0w \/ EL k ss.sym_stack = Val 1w)) ==>
    sym_steps q env0 n (sym_init s) = SymOK ssQ /\
    ?u. asm_steps (SND(compute_label_offsets q)) (build_offset_to_pc q) q n
          (s with as_code := assemble q ++ data) = AsmOK u /\
        asm_sym_rel q (asm_data_env q (assemble q ++ data)) u ssQ /\
        u.as_pc = ssQ.sym_base.as_pc /\ LENGTH u.as_stack = LENGTH ssQ.sym_stack /\
        u.as_call_ctx = ssQ.sym_base.as_call_ctx /\ u.as_requests = ssQ.sym_base.as_requests /\
        Shape q cc req (r o pc) height need tagQ boolean e u /\
        (!k l origin. tagQ e k = SOME(l,origin) ==>
           k < LENGTH ssQ.sym_stack /\ EL k ssQ.sym_stack = Lab l 0) /\
        (!k. boolean e k ==> k < LENGTH ssQ.sym_stack /\
           (EL k ssQ.sym_stack = Val 0w \/ EL k ssQ.sym_stack = Val 1w))
Proof
  MATCH_ACCEPT_TAC (Q.INST [`allow_own` |-> `F`] prune_one_actual_root_mode
    |> PURE_REWRITE_RULE [sym_steps_mode_def, COND_CLAUSES])
QED
