Theory staticAbortOptConditionalJumpsEndpoint
Ancestors
  staticAbortOptConditionalJumpsStopped staticAbortProtectedActualPrefix
  staticAbortProtectedFetch staticAbortProtectedTraceCoverage asmSymPcOwn asmSymOwnCode
  staticAbortOptPruneUnreachableZeroOrigin staticAbortOptPruneUnreachableLayout
  asmSplice asmSymBridge asmSymPc asmDataEnv codegenSymRel asmOptimizer
  asmSymSem asmSem asmWf asmIR finite_map rich_list list arithmetic words

(* Only successful strict prefixes of the old window are inspected here.
   In particular, stopping just after the c-push says nothing about the
   value or kind of the condition beneath it. *)
Theorem strict_jump_stop_stack_mode[local]:
  h.sym_base.as_pc = b /\ b+4 < LENGTH p /\
  EL b p = AsmPushLabel c /\ EL (b+1) p = AsmOp "JUMPI" /\
  EL (b+2) p = AsmPushLabel x /\ EL (b+4) p = AsmLabel c /\ INDEX_OF (AsmLabel c) p = SOME (b+4) /\
  0 < d /\ d < 4 /\ ss.sym_base.as_pc = b+d /\
  sym_steps_mode allow_own p env own d h = SymOK ss ==>
  h.sym_base.as_call_ctx = ss.sym_base.as_call_ctx /\
  h.sym_base.as_requests = ss.sym_base.as_requests /\
  (if d=1 then ss.sym_stack = Lab c 0::h.sym_stack else
     ?stk. h.sym_stack = Val 0w::stk /\
           ss.sym_stack = if d=2 then stk else Lab x 0::stk)
Proof
  strip_tac >>
  qabbrev_tac `h1 = h with <| sym_base := asm_next h.sym_base;
                             sym_stack := Lab c 0::h.sym_stack |>` >>
  `h1.sym_base.as_pc=b+1 /\ h1.sym_stack=Lab c 0::h.sym_stack` by
    simp[Abbr `h1`, asm_next_def] >>
  `b < LENGTH p /\ b+1 < LENGTH p /\ b+2 < LENGTH p` by decide_tac >>
  `sym_steps_mode allow_own p env own d h = sym_steps_mode allow_own p env own (d-1) h1` by
    simp[IgnAsm `sym_steps_mode allow_own p env own d h = _`, Once protected_mode_fetch_pos,
         sym_step_own_eq, sym_step_push_label, Abbr `h1`] >>
  Cases_on `d=1`
  >- gvs[sym_steps_mode_zero, Abbr `h1`, asm_next_def] >>
  `?w stk. h.sym_stack = Val w::stk` by (
    `0 < d-1` by decide_tac >>
    `sym_steps_mode allow_own p env own (d-1) h1 = SymOK ss` by metis_tac[] >>
    pop_assum mp_tac >> simp[Once protected_mode_fetch_pos, sym_step_own_eq] >>
    Cases_on `h.sym_stack` >- simp[sym_step_def, sym_step_op_def, sym_jumpi_def] >>
    rename1 `h.sym_stack = v::stk` >> Cases_on `v` >>
    simp[sym_step_def, sym_step_op_def, sym_jumpi_def]) >>
  `h1.sym_stack = Lab c 0::Val w::stk` by simp[] >>
  drule_then (qspecl_then [`p`, `env`] assume_tac) sym_step_jumpi_label >>
  `sym_steps_mode allow_own p env own (d-1) h1 = SymOK ss` by metis_tac[] >>
  pop_assum mp_tac >> Cases_on `d=2`
  >- (Cases_on `w=0w` >> simp[Once protected_mode_fetch_pos, sym_step_own_eq] >>
      simp[sym_steps_mode_zero, Abbr `h1`, asm_next_def] >>
      strip_tac >> gvs[] >> decide_tac) >>
  `d=3` by decide_tac >>
  Cases_on `w=0w` >> simp[Once protected_mode_fetch_pos, sym_step_own_eq] >>
  simp[Once protected_mode_fetch_pos, sym_step_own_eq, asm_next_def] >>
  simp[sym_steps_mode_zero, sym_step_own_eq, sym_step_push_label, Abbr `h1`, asm_next_def,
       sym_step_def, sym_lift_def, asm_step_def] >>
  strip_tac >> gvs[] >> decide_tac
QED

(* With zero on the earlier head, the replacement takes its x arm.
   This uses the q label index, never a concrete step at the old cut. *)
Theorem strict_jump_destination_taken_mode[local]:
  h.sym_base.as_pc=b /\ h.sym_stack=Val 0w::stk /\
  b+2<LENGTH q /\ EL b q=AsmOp "ISZERO" /\
  EL (b+1) q=AsmPushLabel x /\ EL (b+2) q=AsmOp "JUMPI" /\
  INDEX_OF (AsmLabel x) q=SOME dest ==>
  ?u. sym_steps_mode allow_own q env own 3 h = SymOK u /\ u.sym_base.as_pc=dest /\
      u.sym_stack=stk /\ u.sym_base.as_call_ctx=h.sym_base.as_call_ctx /\
      u.sym_base.as_requests=h.sym_base.as_requests
Proof
  strip_tac >>
  `b < LENGTH q /\ b+1 < LENGTH q` by decide_tac >>
  drule_then (qspecl_then [`q`, `env`] assume_tac) sym_step_iszero_val >>
  qmatch_asmsub_abbrev_tac `sym_step q env (AsmOp "ISZERO") h = SymOK h1` >>
  qabbrev_tac `h2 = h1 with <| sym_base := asm_next h1.sym_base;
                              sym_stack := Lab x 0::h1.sym_stack |>` >>
  `h1.sym_base.as_pc=b+1 /\ h2.sym_base.as_pc=b+2 /\
   h2.sym_stack=Lab x 0::Val 1w::stk /\
   sym_step q env (AsmPushLabel x) h1 = SymOK h2` by
    simp[Abbr `h2`, Abbr `h1`, asm_next_def, sym_step_push_label] >>
  drule_then (qspecl_then [`q`, `env`] assume_tac) sym_step_jumpi_label >>
  `(1w:bytes32) <> 0w` by simp[n2w_11, ONE_LT_dimword] >>
  simp[protected_mode_fetch_three, protected_mode_fetch_two, protected_mode_fetch_one] >>
  simp[Abbr `h2`, Abbr `h1`, asm_next_def]
QED

Theorem conditional_jump_endpoint_prefix_mode[local]:
  !b. b = LENGTH pre ==>
  !d. d = ss.sym_base.as_pc ==>
  !A. A = (d=b+1) ==>
  !B. B = (d=b+2) ==>
  !D. D = (d=b+3) ==>
  !idx. idx = (\k. if A \/ D then k+1 else k) ==>
  p = pre ++ [AsmPushLabel c; AsmOp "JUMPI"; AsmPushLabel x;
              AsmOp "JUMP"; AsmLabel c] ++ tail /\
  q = pre ++ [AsmOp "ISZERO"; AsmPushLabel x; AsmOp "JUMPI"; AsmLabel c] ++ tail /\
  asm_static_wf p /\ s.as_pc=0 /\
  sym_steps_mode allow_own p env own n (sym_init s)=SymOK ss ==>
  (A ==> EL 0 ss.sym_stack = Lab c 0) /\
  (D ==> EL 0 ss.sym_stack = Lab x 0) /\
  !dest. ((B \/ D) ==> INDEX_OF (AsmLabel x) q = SOME dest) ==>
    ?j u. sym_steps_mode allow_own q env own j (sym_init s) = SymOK u /\
      u.sym_base.as_pc = (if A then b else if B \/ D then dest else splice_pc b 4 3 d) /\
      LENGTH u.sym_stack = (if A \/ D then LENGTH ss.sym_stack-1 else LENGTH ss.sym_stack) /\
      u.sym_base.as_call_ctx = ss.sym_base.as_call_ctx /\
      u.sym_base.as_requests = ss.sym_base.as_requests /\
      (!k. (A ==> k<>0) /\ idx k < LENGTH ss.sym_stack ==>
           k < LENGTH u.sym_stack /\ EL k u.sym_stack = EL (idx k) ss.sym_stack)
Proof
  CONV_TAC (TOP_DEPTH_CONV (HO_REWR_CONV UNWIND_FORALL_THM2) THENC
            REDEPTH_CONV BETA_CONV) >> strip_tac >>
  qabbrev_tac `b = LENGTH (pre:asm_inst list)` >>
  qabbrev_tac `d = ss.sym_base.as_pc` >>
  `p = pre ++ [AsmPushLabel c; AsmOp "JUMPI"; AsmPushLabel x; AsmOp "JUMP"] ++
       AsmLabel c::tail /\
   q = pre ++ [AsmOp "ISZERO"; AsmPushLabel x; AsmOp "JUMPI"] ++ AsmLabel c::tail`
    by simp[] >>
  `~MEM (AsmLabel c) pre` by
    (qpat_assum `asm_static_wf p` (mp_tac o CONJUNCT1 o REWRITE_RULE[asm_static_wf_def]) >>
     qpat_assum `p = pre ++ [AsmPushLabel c; AsmOp "JUMPI"; AsmPushLabel x;
                            AsmOp "JUMP"; AsmLabel c] ++ tail` SUBST1_TAC >>
     pure_rewrite_tac[GSYM APPEND_ASSOC] >>
     disch_then (mp_tac o MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO]
                                     asm_labels_unique_append_not_mem)) >>
     disch_then (qspec_then `c` mp_tac) >> simp[]) >>
  `b+4 < LENGTH p /\ EL b p=AsmPushLabel c /\ EL (b+1) p=AsmOp "JUMPI" /\
   EL (b+2) p=AsmPushLabel x /\ EL (b+4) p=AsmLabel c /\
   INDEX_OF (AsmLabel c) p=SOME(b+4) /\
   b+2 < LENGTH q /\ EL b q=AsmOp "ISZERO" /\
   EL (b+1) q=AsmPushLabel x /\ EL (b+2) q=AsmOp "JUMPI"` by
    simp[Abbr `b`, EL_APPEND_EQN, INDEX_OF_APPEND, INDEX_OF_CONS] >>
  drule_all (CONV_RULE (TOP_DEPTH_CONV (HO_REWR_CONV UNWIND_FORALL_THM2) THENC
                       REDEPTH_CONV BETA_CONV) conditional_jump_one_stopped_prefix_mode) >>
  simp[IgnAsm `p = _`, IgnAsm `q = _`] >>
  qpat_x_assum `p = _` kall_tac >> qpat_x_assum `p = _` kall_tac >>
  qpat_x_assum `q = _` kall_tac >> qpat_x_assum `q = _` kall_tac >>
  Cases_on `b<d /\ d<b+4`
  >- suspend "strict" >>
  `d<>b+1 /\ d<>b+2 /\ d<>b+3` by decide_tac >>
  simp[] >> strip_tac >> qexistsl [`j`,`sym_with_pc (splice_pc b 4 3 d) ss`] >>
  simp[sym_with_pc_def]
QED

Resume conditional_jump_endpoint_prefix_mode[strict]:
  simp[] >> strip_tac >>
  `0 < d-b /\ d-b < 4 /\ ss.sym_base.as_pc=b+(d-b)` by
    (qpat_assum `Abbrev (d = _)` (mp_tac o REWRITE_RULE[markerTheory.Abbrev_def]) >> decide_tac) >>
  drule_all strict_jump_stop_stack_mode >> disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `d=b+1`
  >- (`d-b=1 /\ d<>b+2 /\ d<>b+3` by decide_tac >>
      qpat_x_assum `if d-b=1 then _ else _` mp_tac >> simp[] >> strip_tac >>
      simp[] >> qexistsl [`j`,`h`] >> simp[GSYM ADD1]) >>
  `d-b<>1` by decide_tac >>
  Cases_on `d=b+2` >>
  `d=b+3 <=> d<>b+2` by (simp[] >> decide_tac) >>
  `d-b=2 <=> d=b+2` by (simp[] >> decide_tac) >>
  qpat_x_assum `if d-b=1 then _ else _` mp_tac >> simp[] >> strip_tac >>
  simp[] >> rpt gen_tac >> strip_tac >>
  drule_all strict_jump_destination_taken_mode >>
  disch_then (qspecl_then [`own`, `env`, `allow_own`]
    (qx_choose_then `u` strip_assume_tac)) >>
  qexistsl [`j+3`,`u`] >> simp[sym_steps_mode_add, GSYM ADD1]
QED

Finalise conditional_jump_endpoint_prefix_mode

(* The strict-cut names are available before selecting any ports.  The port
   then determines the concrete endpoint, but its producer translation can
   be chosen later: the producer and Shape clauses refer to the same t. *)
Theorem conditional_jump_actual_endpoint_mode:
  !Shape. Shape =
    (\p cc req pc height need tag boolean (i:num#num) (t:asm_state).
      t.as_pc = pc i /\ LENGTH t.as_stack = height i /\
      t.as_call_ctx = cc /\ t.as_requests = req /\
      (need i ==> t.as_call_ctx.cc_static) /\
      (!k l origin. tag i k = SOME(l,origin) ==>
         k < height i /\ origin < LENGTH p /\
         (EL origin p = AsmPushLabel l \/
          (?delta. EL origin p = AsmPushOfst l delta) \/ EL origin p = AsmDataLabel l) /\
         ?off dest.
           FLOOKUP (SND(compute_label_offsets p)) l = SOME off /\
           off < dimword(:256) /\
           FLOOKUP (build_offset_to_pc p) off = SOME dest /\
           EL k t.as_stack = (n2w off:bytes32)) /\
      (!k. boolean i k ==> k < height i /\
         (EL k t.as_stack = 0w \/ EL k t.as_stack = 1w))) ==>
  !rootJust. rootJust = (\u tg bl.
    (!k l i. tg k=SOME(l,i) ==> k<LENGTH u.sym_stack /\ EL k u.sym_stack=Lab l 0) /\
    (!k. bl k ==> k<LENGTH u.sym_stack /\
                  (EL k u.sym_stack=Val 0w \/ EL k u.sym_stack=Val 1w))) ==>
  !C. C = (\p l d. ?off. FLOOKUP (SND(compute_label_offsets p)) l=SOME off /\
                        off<dimword(:256) /\ FLOOKUP (build_offset_to_pc p) off=SOME d) ==>
  !b. b = LENGTH pre ==>
  !d. d = pc e ==>
  !r. r = splice_pc b 4 3 ==>
  !A. A = (d=b+1) ==>
  !B. B = (d=b+2) ==>
  !D. D = (d=b+3) ==>
  !src. src = (\k. if A \/ D then k+1 else k) ==>
  !envp. envp = (if allow_own then asm_data_env orig (assemble orig ++ data) else asm_data_env p (assemble p ++ data)) ==>
  !envq. envq = (if allow_own then asm_data_env orig (assemble orig ++ data) else asm_data_env q (assemble q ++ data)) ==>
  p = pre ++ [AsmPushLabel c; AsmOp "JUMPI"; AsmPushLabel x;
              AsmOp "JUMP"; AsmLabel c] ++ tail /\
  q = pre ++ [AsmOp "ISZERO"; AsmPushLabel x; AsmOp "JUMPI"; AsmLabel c] ++ tail /\
  asm_static_wf orig /\ asm_static_wf p /\ asm_static_wf q /\
  FILTER is_data_inst p = FILTER is_data_inst orig /\
  FILTER is_data_inst q = FILTER is_data_inst p /\
  (!l v. C p l v ==> C q l (r v)) /\
  s.as_pc=0 /\ s.as_code=assemble orig ++ data /\
  sym_steps_mode allow_own p envp s.as_code n (sym_init s)=SymOK ss /\ (if allow_own then asm_sym_rel_own (lo_reloc p orig) p (asm_data_env orig s.as_code) s.as_code
       else asm_sym_rel p envp) cut ss /\
  Shape p cc req pc height need tag boolean e cut /\ rootJust ss (tag e) (boolean e) /\
  req <<= req_bound /\
  ((A \/ D) ==> ?l i. tag e 0=SOME(l,i)) ==>
  (A ==> ?i. tag e 0=SOME(c,i)) /\
  (D ==> ?i. tag e 0=SOME(x,i)) /\
  !z root rootPC rootH rootNeed raw bl.
    rootPC root = (if B \/ D then r (pc z) else r d) /\
    rootH root = (if A \/ D then height e-1 else height e) /\
    ((B \/ D) ==> C p x (pc z)) /\
    (!k l i. raw k=SOME(l,i) ==> (A ==> k<>0) /\ tag e (src k)=SOME(l,i)) /\
    (!k. bl root k ==> (A ==> k<>0) /\ boolean e (src k)) ==>
    ?j u t.
      sym_steps_mode allow_own q envq s.as_code j (sym_init s)=SymOK u /\
      asm_steps (if allow_own then lo_reloc q orig else SND(compute_label_offsets q))
        (build_offset_to_pc q) q j
        (if allow_own then s else (s with as_code := assemble q ++ data))=AsmOK t /\
      (if allow_own then asm_sym_rel_own (lo_reloc q orig) q (asm_data_env orig s.as_code) s.as_code
       else asm_sym_rel q envq) t u /\
      t.as_pc=u.sym_base.as_pc /\ LENGTH t.as_stack=LENGTH u.sym_stack /\
      t.as_call_ctx=u.sym_base.as_call_ctx /\ t.as_requests=u.sym_base.as_requests /\
      t.as_pc=rootPC root /\ LENGTH t.as_stack=rootH root /\
      t.as_call_ctx=cc /\ t.as_requests=req /\ t.as_requests <<= req_bound /\
      rootJust u raw (bl root) /\
      (!k l i. raw k=SOME(l,i) ==>
        ?m v. m<j /\ sym_steps_mode allow_own q envq s.as_code m (sym_init s)=SymOK v /\
              v.sym_base.as_pc<LENGTH q /\
              (EL v.sym_base.as_pc q=AsmPushLabel l \/
               EL v.sym_base.as_pc q=AsmPushOfst l 0)) /\
      !rho.
        !T. T = (\w k. OPTION_MAP (\(l,i). (l,rho l i)) (raw k)) ==>
        (rootNeed root ==> cc.cc_static) /\
        (!k l i. T root k=SOME(l,i) ==>
           i<LENGTH q /\ (EL i q=AsmPushLabel l \/ EL i q=AsmPushOfst l 0) /\ ?v. C q l v) ==>
        Shape q cc req rootPC rootH rootNeed T bl root t /\ rootJust u (T root) (bl root)
Proof
  map_every (fn v => qx_gen_tac v >>
    disch_then (assume_tac o CONV_RULE (REWR_CONV (GSYM markerTheory.Abbrev_def))))
    [`Shape`, `rootJust`, `C`] >>
  CONV_TAC (TOP_DEPTH_CONV (HO_REWR_CONV UNWIND_FORALL_THM2) THENC
            REDEPTH_CONV BETA_CONV) >>
  qabbrev_tac `b = LENGTH (pre:asm_inst list)` >>
  qabbrev_tac `d = (pc:(num#num)->num) e` >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `ss.sym_base.as_pc=d /\ LENGTH ss.sym_stack=height e /\
   ss.sym_base.as_call_ctx=cc /\ ss.sym_base.as_requests=req` by (
    qpat_assum `Shape p _ _ _ _ _ _ _ e cut` mp_tac >>
    simp[NoAsms, Abbr `Shape`] >>
    disch_then (map_every assume_tac o CONJUNCTS) >>
    drule_then strip_assume_tac protected_cut_relation_context >>
    drule_then strip_assume_tac protected_cut_relation_pc >> simp[Abbr `d`]) >>
  drule_all (CONV_RULE (TOP_DEPTH_CONV (HO_REWR_CONV UNWIND_FORALL_THM2) THENC
                       REDEPTH_CONV BETA_CONV) conditional_jump_endpoint_prefix_mode) >>
  disch_then (map_every assume_tac o CONJUNCTS o BETA_RULE) >>
  qpat_x_assum `p = _` kall_tac >> qpat_x_assum `q = _` kall_tac >>
  `!l. EL 0 ss.sym_stack=Lab l 0 ==> ((d=b+1 \/ d=b+3) ==> ?i. tag e 0=SOME(l,i))` by (
    rpt gen_tac >> disch_tac >> disch_tac >>
    `?l' i. tag e 0=SOME(l',i)` by metis_tac[] >>
    qpat_assum `rootJust ss _ _` mp_tac >>
    simp[NoAsms, Abbr `rootJust`] >>
    disch_then (qspecl_then [`0`, `l'`, `i`] mp_tac o CONJUNCT1) >> simp[]) >>
  conj_tac >- (strip_tac >> first_x_assum irule >> simp[Abbr `b`]) >>
  conj_tac >- (strip_tac >> first_x_assum irule >> simp[Abbr `b`]) >>
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  suspend "realize"
QED

Resume conditional_jump_actual_endpoint_mode[realize]:
  `d=b+2 \/ d=b+3 ==> INDEX_OF (AsmLabel x) q = SOME (splice_pc b 4 3 (pc z))` by (
    disch_tac >> `C p x (pc z)` by metis_tac[] >>
    `C q x (splice_pc b 4 3 (pc z))` by metis_tac[] >>
    pop_assum mp_tac >> simp[NoAsms, Abbr `C`] >> strip_tac >>
    irule lookup_pair_code_label_index >> simp[] >> goal_assum drule) >>
  qpat_x_assum `!dest. _ ==> ?j u. _`
    (qspec_then `splice_pc b 4 3 (pc z)` mp_tac) >>
  simp[Abbr `b`] >> (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then strip_assume_tac >>
  `FILTER is_data_inst q = FILTER is_data_inst orig` by metis_tac[] >>
  `(if allow_own then asm_data_env orig (assemble orig ++ data)
        else asm_data_env p (assemble p ++ data)) = asm_data_env orig (assemble orig ++ data) /\
    (if allow_own then asm_data_env orig (assemble orig ++ data)
        else asm_data_env q (assemble q ++ data)) = asm_data_env orig (assemble orig ++ data)` by
      (Cases_on `allow_own` >> simp[NoAsms] >>
       conj_tac >> irule asm_data_env_agree >> simp[]) >>
  `sym_steps_mode allow_own q (asm_data_env orig (assemble orig ++ data)) s.as_code j (sym_init s)=SymOK u` by
    (qpat_assum `s.as_code = assemble orig ++ data` (fn code =>
     qpat_assum `(if allow_own then _ else asm_data_env p _) = asm_data_env orig _` (fn env =>
       PURE_REWRITE_TAC [code] >>
       first_assum (ACCEPT_TAC o PURE_REWRITE_RULE [env,code])))) >>
  mp_tac (Q.INST [`p` |-> `orig`, `q` |-> `q`, `n` |-> `j`, `ss` |-> `u`]
    stopped_symbolic_prefix_mode) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choose_then `t` strip_assume_tac) >>
  `d=LENGTH pre+1 ==> splice_pc (LENGTH pre) 4 3 d=LENGTH pre` by
    (strip_tac >> simp[splice_pc_def]) >>
  `u.sym_base.as_pc=rootPC root` by
    (Cases_on `d=LENGTH pre+1` >> simp[] >> decide_tac) >>
  `rootJust u raw (bl root)` by (
    qpat_assum `rootJust ss _ _` mp_tac >>
    simp[NoAsms, Abbr `rootJust`] >> strip_tac >>
    rule_assum_tac BETA_RULE >> conj_tac >> rpt gen_tac >> strip_tac
    >- (qpat_assum `!k l i. raw k=SOME(l,i) ==> _` drule >> strip_tac >>
        qpat_assum `!k l i. tag e k=SOME(l,i) ==> _` drule >> strip_tac >>
        qpat_assum `!k. _ ==> k<LENGTH u.sym_stack /\ _` (qspec_then `k` mp_tac) >> simp[]) >>
    qpat_assum `!k. bl root k ==> _` drule >> strip_tac >>
    qpat_assum `!k. boolean e k ==> _` drule >> strip_tac >>
    qpat_assum `!k. _ ==> k<LENGTH u.sym_stack /\ _` (qspec_then `k` mp_tac) >> simp[]) >>
  qpat_assum `rootJust u _ _` mp_tac >> simp[NoAsms, Abbr `rootJust`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qexistsl_tac [`j`, `u`, `t`] >>
  qpat_assum `(if allow_own then _ else asm_data_env q _) = asm_data_env orig _`
    (pure_rewrite_tac o single) >>
  qpat_assum `s.as_code = assemble orig ++ data`
    (rule_assum_tac o PURE_REWRITE_RULE o single) >>
  simp[] >>
  conj_tac >- (
    rpt gen_tac >> disch_tac >>
    qpat_assum `!k l i. raw k=SOME(l,i) ==> _` drule >> strip_tac >>
    irule stopped_lab_zero_producer_mode >>
    simp[] >> metis_tac[EL_MEM]) >>
  qx_gen_tac `translate` >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `!k l i. (?v. raw k = SOME v /\ (l,i) = (\(a,j). (a,translate a j)) v) ==>
     k<LENGTH u.sym_stack /\ EL k u.sym_stack=Lab l 0` by (
    rpt gen_tac >> strip_tac >> PairCases_on `v` >>
    qpat_x_assum `(l,i) = _` mp_tac >> simp[NoAsms] >>
    disch_then (SUBST1_TAC o CONJUNCT1) >>
    qpat_assum `!k l i. raw k=SOME(l,i) ==> _` drule >> simp[]) >>
  simp[Abbr `Shape`] >>
  drule_then assume_tac protected_cut_relation_slots >>
  reverse conj_tac >- (
    rpt gen_tac >> disch_tac >>
    qpat_assum `!k l i. _ ==> k<LENGTH u.sym_stack /\ _ = Lab l 0`
      (qspecl_then [`k`, `l`, `i`] mp_tac) >> simp[]) >>
  conj_tac >- (
    rpt gen_tac >> disch_tac >>
    qpat_assum `!k l i. _ ==> k<LENGTH u.sym_stack /\ _ = Lab l 0`
      (qspecl_then [`k`, `l`, `origin`] mp_tac) >> simp[] >> strip_tac >>
    qpat_assum `!k l i. _ ==> i<LENGTH q /\ _`
      (qspecl_then [`k`, `l`, `origin`] mp_tac) >> simp[Abbr `C`] >> strip_tac >>
    `EL k t.as_stack = (n2w off:bytes32)` by (
      qpat_assum `!k. k < LENGTH u.sym_stack ==> _` (qspec_then `k` mp_tac) >>
      (impl_tac >- simp[]) >>
      disch_then (qspecl_then [`l`,`off`,`v`] mp_tac o CONJUNCT2) >>
      simp[]) >>
    metis_tac[]) >>
  rpt gen_tac >> disch_tac >>
  qpat_assum `!k. bl root k ==> k<LENGTH u.sym_stack /\ _` drule >> strip_tac >>
  qpat_assum `!k. k < LENGTH u.sym_stack ==> _` (qspec_then `k` mp_tac) >>
  (impl_tac >- simp[]) >> metis_tac[]
QED

Finalise conditional_jump_actual_endpoint_mode


Theorem conditional_jump_actual_endpoint:
  !Shape. Shape =
    (\p cc req pc height need tag boolean (i:num#num) (t:asm_state).
      t.as_pc = pc i /\ LENGTH t.as_stack = height i /\
      t.as_call_ctx = cc /\ t.as_requests = req /\
      (need i ==> t.as_call_ctx.cc_static) /\
      (!k l origin. tag i k = SOME(l,origin) ==>
         k < height i /\ origin < LENGTH p /\
         (EL origin p = AsmPushLabel l \/
          (?delta. EL origin p = AsmPushOfst l delta) \/ EL origin p = AsmDataLabel l) /\
         ?off dest.
           FLOOKUP (SND(compute_label_offsets p)) l = SOME off /\
           off < dimword(:256) /\
           FLOOKUP (build_offset_to_pc p) off = SOME dest /\
           EL k t.as_stack = (n2w off:bytes32)) /\
      (!k. boolean i k ==> k < height i /\
         (EL k t.as_stack = 0w \/ EL k t.as_stack = 1w))) ==>
  !rootJust. rootJust = (\u tg bl.
    (!k l i. tg k=SOME(l,i) ==> k<LENGTH u.sym_stack /\ EL k u.sym_stack=Lab l 0) /\
    (!k. bl k ==> k<LENGTH u.sym_stack /\
                  (EL k u.sym_stack=Val 0w \/ EL k u.sym_stack=Val 1w))) ==>
  !C. C = (\p l d. ?off. FLOOKUP (SND(compute_label_offsets p)) l=SOME off /\
                        off<dimword(:256) /\ FLOOKUP (build_offset_to_pc p) off=SOME d) ==>
  !b. b = LENGTH pre ==>
  !d. d = pc e ==>
  !r. r = splice_pc b 4 3 ==>
  !A. A = (d=b+1) ==>
  !B. B = (d=b+2) ==>
  !D. D = (d=b+3) ==>
  !src. src = (\k. if A \/ D then k+1 else k) ==>
  !envp. envp = asm_data_env p (assemble p ++ data) ==>
  !envq. envq = asm_data_env q (assemble q ++ data) ==>
  p = pre ++ [AsmPushLabel c; AsmOp "JUMPI"; AsmPushLabel x;
              AsmOp "JUMP"; AsmLabel c] ++ tail /\
  q = pre ++ [AsmOp "ISZERO"; AsmPushLabel x; AsmOp "JUMPI"; AsmLabel c] ++ tail /\
  asm_static_wf orig /\ asm_static_wf p /\ asm_static_wf q /\
  FILTER is_data_inst p = FILTER is_data_inst orig /\
  FILTER is_data_inst q = FILTER is_data_inst p /\
  (!l v. C p l v ==> C q l (r v)) /\
  s.as_pc=0 /\ s.as_code=assemble orig ++ data /\
  sym_steps p envp n (sym_init s)=SymOK ss /\ asm_sym_rel p envp cut ss /\
  Shape p cc req pc height need tag boolean e cut /\ rootJust ss (tag e) (boolean e) /\
  req <<= req_bound /\
  ((A \/ D) ==> ?l i. tag e 0=SOME(l,i)) ==>
  (A ==> ?i. tag e 0=SOME(c,i)) /\
  (D ==> ?i. tag e 0=SOME(x,i)) /\
  !z root rootPC rootH rootNeed raw bl.
    rootPC root = (if B \/ D then r (pc z) else r d) /\
    rootH root = (if A \/ D then height e-1 else height e) /\
    ((B \/ D) ==> C p x (pc z)) /\
    (!k l i. raw k=SOME(l,i) ==> (A ==> k<>0) /\ tag e (src k)=SOME(l,i)) /\
    (!k. bl root k ==> (A ==> k<>0) /\ boolean e (src k)) ==>
    ?j u t.
      sym_steps q envq j (sym_init s)=SymOK u /\
      asm_steps (SND(compute_label_offsets q)) (build_offset_to_pc q) q j
        (s with as_code := assemble q ++ data)=AsmOK t /\
      asm_sym_rel q envq t u /\
      t.as_pc=u.sym_base.as_pc /\ LENGTH t.as_stack=LENGTH u.sym_stack /\
      t.as_call_ctx=u.sym_base.as_call_ctx /\ t.as_requests=u.sym_base.as_requests /\
      t.as_pc=rootPC root /\ LENGTH t.as_stack=rootH root /\
      t.as_call_ctx=cc /\ t.as_requests=req /\ t.as_requests <<= req_bound /\
      rootJust u raw (bl root) /\
      (!k l i. raw k=SOME(l,i) ==>
        ?m v. m<j /\ sym_steps q envq m (sym_init s)=SymOK v /\
              v.sym_base.as_pc<LENGTH q /\
              (EL v.sym_base.as_pc q=AsmPushLabel l \/
               EL v.sym_base.as_pc q=AsmPushOfst l 0)) /\
      !rho.
        !T. T = (\w k. OPTION_MAP (\(l,i). (l,rho l i)) (raw k)) ==>
        (rootNeed root ==> cc.cc_static) /\
        (!k l i. T root k=SOME(l,i) ==>
           i<LENGTH q /\ (EL i q=AsmPushLabel l \/ EL i q=AsmPushOfst l 0) /\ ?v. C q l v) ==>
        Shape q cc req rootPC rootH rootNeed T bl root t /\ rootJust u (T root) (bl root)
Proof
  MATCH_ACCEPT_TAC (Q.INST [`allow_own` |-> `F`] conditional_jump_actual_endpoint_mode
    |> PURE_REWRITE_RULE [sym_steps_mode_def, COND_CLAUSES])
QED
