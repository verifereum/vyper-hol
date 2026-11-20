Theory staticAbortOptUnusedLabelsRoot
Ancestors
  codegenSymRel staticAbortOptMergeJumpdestsLayout
  staticAbortOptUnusedLabelsSource staticAbortOptUnusedLabelsStopped
  staticAbortProtectedActualPrefix asmSplice asmSymPc asmSymBridge asmDataEnv
  asmWf asmIR asmSem asmSymSem asmOptimizer asmToBytecodeProofs
  finite_map pred_set rich_list list words arithmetic

Theorem unused_label_one_actual_root_mode:
  !orig p pre l tail data s n ss cut cc req req_bound
    V e (rank:(num#num)->rat) pc height need tag boolean edge.
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
  !d. d = LENGTH pre ==>
  !q. q = pre ++ tail ==>
  !r. r = splice_pc d 1 0 ==>
  !P. P = OPTION_MAP (\(n,j). (n,r j)) ==>
  !T. T = (\x k. P (tag x k)) ==>
  !C. C = (\s n w. ?off. FLOOKUP (SND (compute_label_offsets s)) n = SOME off /\
                      off < dimword(:256) /\ FLOOKUP (build_offset_to_pc s) off = SOME w) ==>
  !ssQ. ssQ = sym_with_pc (r ss.sym_base.as_pc) ss ==>
  p = pre ++ [AsmLabel l] ++ tail /\ ~MEM l (asm_label_refs p) /\
  s.as_pc = 0 /\ s.as_code = assemble orig ++ data /\
  asm_static_wf orig /\ asm_static_wf p /\ asm_static_wf q /\
  FILTER is_data_inst p = FILTER is_data_inst orig /\
  sym_steps_mode allow_own p (asm_data_env orig (assemble orig ++ data)) s.as_code n (sym_init s) = SymOK ss /\
  (if allow_own then asm_sym_rel_own (lo_reloc p orig) p (asm_data_env orig s.as_code) s.as_code
   else asm_sym_rel p (asm_data_env p (assemble p ++ data))) cut ss /\
  Shape p cc req pc height need tag boolean e cut /\ req <<= req_bound /\
  (!k l j. tag e k = SOME(l,j) ==>
      k < LENGTH ss.sym_stack /\ EL k ss.sym_stack = Lab l 0) /\
  (!k. boolean e k ==>
      k < LENGTH ss.sym_stack /\ (EL k ss.sym_stack = Val 0w \/ EL k ss.sym_stack = Val 1w)) /\
  (!S. S = Shape p cc req pc height need tag boolean ==>
   !target. target = (\x y.
      ?l origin off. tag x 0 = SOME(l,origin) /\
        FLOOKUP (SND(compute_label_offsets p)) l = SOME off /\
        off < dimword(:256) /\
        FLOOKUP (build_offset_to_pc p) off = SOME(pc y)) ==>
   FINITE V /\
   (!x. x IN V ==> ?t. S x t) /\
   (!x. x IN V ==> pc x < LENGTH p) /\
   (!x y. edge x y ==>
    x IN V /\ y IN V /\ rank y < rank x /\
    (!hi. hi = height x ==>
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
     | _ => F) /\
    (if EL (pc x) p = AsmOp "JUMP" then target x y
     else if EL (pc x) p = AsmOp "JUMPI" then pc y = pc x+1 \/ target x y
     else pc y = pc x+1)) /\
   (!x t. x IN V /\ S x t ==>
    (?u. (asm_steps (SND(compute_label_offsets p)) (build_offset_to_pc p)
                 p 1 t = AsmRevert u \/
           asm_steps (SND(compute_label_offsets p)) (build_offset_to_pc p)
                 p 1 t = AsmFault u) /\ u.as_requests=req) \/
    (?y u. edge x y /\
       asm_steps (SND(compute_label_offsets p)) (build_offset_to_pc p)
                 p 1 t = AsmOK u /\ S y u))) /\
  e IN V /\ (!x. x IN V ==> ?n (path:num->num#num).
    path 0=e /\ path n=x /\ !k. k<n ==> edge (path k) (path(SUC k))) /\
  (!x. x IN V ==>
     (need x ==> cc.cc_static) /\
     (!k. boolean x k ==> k < height x /\ tag x k = NONE) /\
     (!k n j. tag x k = SOME(n,j) ==>
       k < height x /\ j < LENGTH p /\
       (EL j p = AsmPushLabel n \/ EL j p = AsmPushOfst n 0) /\ ?w. C p n w)) /\
  (!x k n j. x IN V /\ tag x k = SOME(n,j) ==>
      j <> d /\ j < LENGTH p /\ r j < LENGTH q /\ EL (r j) q = EL j p /\
      T x k = SOME(n,r j) /\
      !w. C p n w ==> w <> d /\ INDEX_OF (AsmLabel n) p = SOME w /\
        INDEX_OF (AsmLabel n) q = SOME(r w) /\ C q n (r w)) ==>
  ?j t eQ.
    sym_steps_mode allow_own q
      (if allow_own then asm_data_env orig s.as_code else asm_data_env q (assemble q ++ data))
      s.as_code j (sym_init s) = SymOK ssQ /\
    asm_steps (if allow_own then lo_reloc q orig else SND (compute_label_offsets q))
      (build_offset_to_pc q) q j (if allow_own then s else (s with as_code := assemble q ++ data)) = AsmOK t /\
    (if allow_own then asm_sym_rel_own (lo_reloc q orig) q (asm_data_env orig s.as_code) s.as_code
     else asm_sym_rel q (asm_data_env q (assemble q ++ data))) t ssQ /\
    t.as_pc = ssQ.sym_base.as_pc /\ LENGTH t.as_stack = LENGTH ssQ.sym_stack /\
    t.as_call_ctx = ssQ.sym_base.as_call_ctx /\ t.as_requests = ssQ.sym_base.as_requests /\
    t.as_call_ctx = cc /\ t.as_requests = req /\ t.as_requests <<= req_bound /\
    eQ IN {x | x IN V /\ pc x <> d} /\
    (if pc e <> d then eQ = e else
       edge e eQ /\ pc eQ = d+1 /\ height eQ = height e /\
       (!k n j. tag eQ k = SOME(n,j) ==> tag e k = SOME(n,j)) /\
       (!k. boolean eQ k ==> boolean e k)) /\
    Shape q cc req (r o pc) height need T boolean eQ t /\
    (!k n j. T eQ k = SOME(n,j) ==>
       k < LENGTH ssQ.sym_stack /\ EL k ssQ.sym_stack = Lab n 0) /\
    (!k. boolean eQ k ==>
       k < LENGTH ssQ.sym_stack /\ (EL k ssQ.sym_stack = Val 0w \/ EL k ssQ.sym_stack = Val 1w))
Proof
  map_every qx_gen_tac [`orig`,`p`,`pre`,`l`,`tail`,`data`,`s`,`n`,`ss`,`cut`,`cc`,
    `req`,`req_bound`,`V`,`e`,`rank`,`pc`,`height`,`need`,`tag`,`boolean`,`edge`] >>
  map_every (fn name => qx_gen_tac name >>
    disch_then (assume_tac o CONV_RULE (REWR_CONV (GSYM markerTheory.Abbrev_def))))
    [`Shape`,`d`,`q`,`r`,`P`,`tags`,`C`,`ssQ`] >>
  qabbrev_tac `pcQ = r o pc` >>
  qabbrev_tac `env = asm_data_env orig (assemble orig ++ data)` >>
  qpat_x_assum `Abbrev (Shape = _)` (fn th =>
    CONV_TAC (SCONV [REWRITE_RULE [markerTheory.Abbrev_def] th, UNWIND_FORALL_THM2])) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all (CONV_RULE
    (DEPTH_CONV (HO_REWR_CONV UNWIND_FORALL_THM2) THENC
     STRIP_QUANT_CONV (LAND_CONV (SCONV []) THENC RAND_CONV (SCONV [])))
    unused_label_source_contraction) >>
  qpat_assum `Abbrev (d = _)` (fn th =>
    disch_then (mp_tac o cj 3 o REWRITE_RULE [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)])) >>
  disch_then (qspec_then `e` mp_tac) >> simp[] >> strip_tac >>
  `?eQ. eQ IN V /\ pc eQ <> d /\ pcQ eQ = r (pc e) /\
        height eQ = height e /\
        (!k a j. tag eQ k = SOME(a,j) ==> tag e k = SOME(a,j)) /\
        (!k. boolean eQ k ==> boolean e k) /\
        (if pc e <> d then eQ = e else edge e eQ /\ pc eQ = d+1)` by
    (Cases_on `pc e = d`
     >- (qpat_assum `pc e = d ==> ?y. _` drule >> strip_tac >>
         qexists `y` >> simp[Abbr `pcQ`, Abbr `r`, splice_pc_def]) >>
     qexists `e` >> simp[Abbr `pcQ`]) >>
  `FILTER is_data_inst q = FILTER is_data_inst orig` by
    (qpat_assum `p = pre ++ [AsmLabel l] ++ tail` (fn th =>
       qpat_assum `FILTER is_data_inst p = _` (mp_tac o REWRITE_RULE [th])) >>
     simp[Abbr `q`, FILTER_APPEND, is_data_inst_def]) >>
  `?j. sym_steps_mode allow_own q env s.as_code j (sym_init s) = SymOK ssQ` by
    (simp[Abbr `ssQ`, Abbr `r`, Abbr `d`, Abbr `q`] >>
     metis_tac[CONV_RULE (HO_REWR_CONV UNWIND_FORALL_THM2) unused_label_one_stopped_prefix_mode]) >>
  rename1 `sym_steps_mode allow_own q env s.as_code j (sym_init s) = SymOK ssQ` >>
  `sym_steps_mode allow_own q (asm_data_env orig (assemble orig ++ data)) s.as_code j (sym_init s) = SymOK ssQ` by
    fs[Abbr `env`] >>
  drule_all (Q.INST [`p` |-> `orig`, `q` |-> `q`] stopped_symbolic_prefix_mode) >>
  disch_then (qx_choose_then `t` strip_assume_tac) >>
  `ss.sym_base.as_pc = pc e /\ LENGTH ss.sym_stack = height e /\
    ss.sym_base.as_call_ctx = cc /\ ss.sym_base.as_requests = req` by
    (qpat_assum `(if allow_own then asm_sym_rel_own _ _ _ _ else asm_sym_rel _ _) cut ss` mp_tac >>
     Cases_on `allow_own` >> PURE_REWRITE_TAC [COND_CLAUSES, asm_sym_rel_def, asm_sym_rel_own_def] >>
     strip_tac >> simp[LIST_REL_EL_EQN] >> fs[LIST_REL_EL_EQN]) >>
  `ssQ.sym_base.as_pc = pcQ eQ /\ ssQ.sym_stack = ss.sym_stack /\
    ssQ.sym_base.as_call_ctx = cc /\ ssQ.sym_base.as_requests = req` by
    simp[Abbr `ssQ`, sym_with_pc_def] >>
  qpat_x_assum `pc e = d ==> ?y. _` kall_tac >>
  `sym_steps_mode allow_own q
      (if allow_own then asm_data_env orig s.as_code else asm_data_env q (assemble q ++ data))
      s.as_code j (sym_init s) = SymOK ssQ` by
    (`(if allow_own then asm_data_env orig s.as_code else asm_data_env q (assemble q ++ data)) =
        asm_data_env orig (assemble orig ++ data)` by
       (Cases_on `allow_own` >> PURE_REWRITE_TAC [COND_CLAUSES] >>
        metis_tac[asm_data_env_agree]) >>
     pop_assum (pure_rewrite_tac o single) >> first_assum ACCEPT_TAC) >>
  qabbrev_tac `loQ = if allow_own then lo_reloc q orig else SND (compute_label_offsets q)` >>
  `!k. k < LENGTH ssQ.sym_stack ==>
       sval_conc loQ (EL k ssQ.sym_stack) =
         SOME (EL k t.as_stack)` by
    (qpat_assum `(if allow_own then asm_sym_rel_own _ _ _ _ else asm_sym_rel _ _) t ssQ` mp_tac >>
     Cases_on `allow_own` >> PURE_REWRITE_TAC [COND_CLAUSES, asm_sym_rel_def, asm_sym_rel_own_def] >>
     simp[LIST_REL_EL_EQN, Abbr `loQ`]) >>
  `!k a loc. tags eQ k = SOME(a,loc) ==>
     ?origin. tag eQ k = SOME(a,origin) /\ loc = r origin` by
    (rpt gen_tac >> simp[Abbr `tags`, Abbr `P`] >>
     strip_tac >> PairCases_on `z` >> gvs[] >> metis_tac[]) >>
  `!k a loc. tags eQ k = SOME(a,loc) ==>
     k < LENGTH ssQ.sym_stack /\ EL k ssQ.sym_stack = Lab a 0` by
    (rpt strip_tac >>
     qpat_assum `!k a loc. tags eQ k = SOME(a,loc) ==> ?origin. _`
       (drule_then strip_assume_tac) >>
     qpat_assum `!k a j. tag eQ k = SOME(a,j) ==> tag e k = SOME(a,j)`
       (drule_then assume_tac) >>
     qpat_assum `!k a j. tag e k = SOME(a,j) ==> _`
       (drule_then strip_assume_tac) >> simp[]) >>
  qunabbrev_tac `env` >>
  qexistsl_tac [`j`, `t`, `eQ`] >>
  conj_tac
  >- (qpat_assum `s.as_code = _` (pure_rewrite_tac o single o GSYM) >>
      first_assum ACCEPT_TAC) >>
  conj_tac
  >- (qpat_assum `Abbrev (loQ = _)`
        (pure_rewrite_tac o single o GSYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
      first_assum ACCEPT_TAC) >>
  conj_tac
  >- (qpat_assum `s.as_code = _` (pure_rewrite_tac o single o GSYM) >>
      first_assum ACCEPT_TAC) >>
  qpat_x_assum `s.as_code = _` kall_tac >> simp[] >>
  conj_tac
  >- (qpat_assum `!x. x IN V ==> (need x ==> _) /\ _`
        (qspec_then `eQ` (mp_tac o cj 1)) >> simp[]) >>
  conj_tac
  >- (rpt gen_tac >> rename1 `tags eQ k = SOME(a,loc) ==> _` >> disch_tac >>
      qpat_assum `!k a loc. tags eQ k = SOME(a,loc) ==> ?origin. _`
        (drule_then strip_assume_tac) >>
      qpat_assum `!x. x IN V ==> (need x ==> _) /\ _`
        (qspec_then `eQ` (mp_tac o cj 3)) >>
      impl_tac >- simp[] >>
      disch_then (drule_then strip_assume_tac) >>
      qpat_assum `!x k a loc. x IN V /\ tag x k = SOME(a,loc) ==> _`
        (drule_all_then strip_assume_tac) >>
      qpat_assum `!w. C p _ w ==> _` (drule_then strip_assume_tac) >>
      qpat_assum `Abbrev (C = _)` (fn eq =>
        qpat_assum `C q _ _`
          (qx_choose_then `off` strip_assume_tac o BETA_RULE o
           PURE_REWRITE_RULE [REWRITE_RULE [markerTheory.Abbrev_def] eq])) >>
      qpat_assum `!k a loc. tags eQ k = SOME(a,loc) ==> k < _ /\ _`
        (drule_then strip_assume_tac) >>
      `FLOOKUP loQ a = SOME off` by
        (Cases_on `allow_own` >> simp[Abbr `loQ`] >>
         irule canonical_jump_binding_relocated >>
         conj_tac >- first_assum ACCEPT_TAC >>
         conj_tac >- first_assum ACCEPT_TAC >>
         qexists_tac `r w` >> first_assum ACCEPT_TAC) >>
      `EL k t.as_stack = n2w off` by
        (qpat_assum `!k. k < LENGTH ssQ.sym_stack ==> sval_conc _ _ = _`
           (drule_then mp_tac) >>
         qpat_assum `EL k ssQ.sym_stack = Lab _ 0` (rewrite_tac o single) >>
         simp[sval_conc_def] >> metis_tac[]) >>
      simp[] >> qexists `off` >> simp[]) >>
  gen_tac >> disch_tac >>
  `boolean e k` by metis_tac[] >>
  qpat_assum `!k. boolean e k ==> k < LENGTH ss.sym_stack /\ _`
    (drule_then strip_assume_tac) >>
  `k < LENGTH ssQ.sym_stack` by simp[] >>
  qpat_assum `!k. k < LENGTH ssQ.sym_stack ==> sval_conc _ _ = _`
    (drule_then mp_tac) >>
  qpat_assum `ssQ.sym_stack = ss.sym_stack` (rewrite_tac o single) >>
  qpat_assum `EL k ss.sym_stack = Val _` (rewrite_tac o single) >>
  simp[sval_conc_def] >> metis_tac[]
QED

Theorem unused_label_one_actual_root:
  !orig p pre l tail data s n ss cut cc req req_bound
    V e (rank:(num#num)->rat) pc height need tag boolean edge.
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
  !d. d = LENGTH pre ==>
  !q. q = pre ++ tail ==>
  !r. r = splice_pc d 1 0 ==>
  !P. P = OPTION_MAP (\(n,j). (n,r j)) ==>
  !T. T = (\x k. P (tag x k)) ==>
  !C. C = (\s n w. ?off. FLOOKUP (SND (compute_label_offsets s)) n = SOME off /\
                      off < dimword(:256) /\ FLOOKUP (build_offset_to_pc s) off = SOME w) ==>
  !ssQ. ssQ = sym_with_pc (r ss.sym_base.as_pc) ss ==>
  p = pre ++ [AsmLabel l] ++ tail /\ ~MEM l (asm_label_refs p) /\
  s.as_pc = 0 /\ s.as_code = assemble orig ++ data /\
  asm_static_wf orig /\ asm_static_wf p /\ asm_static_wf q /\
  FILTER is_data_inst p = FILTER is_data_inst orig /\
  sym_steps p (asm_data_env orig (assemble orig ++ data)) n (sym_init s) = SymOK ss /\
  asm_sym_rel p (asm_data_env p (assemble p ++ data)) cut ss /\
  Shape p cc req pc height need tag boolean e cut /\ req <<= req_bound /\
  (!k l j. tag e k = SOME(l,j) ==>
      k < LENGTH ss.sym_stack /\ EL k ss.sym_stack = Lab l 0) /\
  (!k. boolean e k ==>
      k < LENGTH ss.sym_stack /\ (EL k ss.sym_stack = Val 0w \/ EL k ss.sym_stack = Val 1w)) /\
  (!S. S = Shape p cc req pc height need tag boolean ==>
   !target. target = (\x y.
      ?l origin off. tag x 0 = SOME(l,origin) /\
        FLOOKUP (SND(compute_label_offsets p)) l = SOME off /\
        off < dimword(:256) /\
        FLOOKUP (build_offset_to_pc p) off = SOME(pc y)) ==>
   FINITE V /\
   (!x. x IN V ==> ?t. S x t) /\
   (!x. x IN V ==> pc x < LENGTH p) /\
   (!x y. edge x y ==>
    x IN V /\ y IN V /\ rank y < rank x /\
    (!hi. hi = height x ==>
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
     | _ => F) /\
    (if EL (pc x) p = AsmOp "JUMP" then target x y
     else if EL (pc x) p = AsmOp "JUMPI" then pc y = pc x+1 \/ target x y
     else pc y = pc x+1)) /\
   (!x t. x IN V /\ S x t ==>
    (?u. (asm_steps (SND(compute_label_offsets p)) (build_offset_to_pc p)
                 p 1 t = AsmRevert u \/
           asm_steps (SND(compute_label_offsets p)) (build_offset_to_pc p)
                 p 1 t = AsmFault u) /\ u.as_requests=req) \/
    (?y u. edge x y /\
       asm_steps (SND(compute_label_offsets p)) (build_offset_to_pc p)
                 p 1 t = AsmOK u /\ S y u))) /\
  e IN V /\ (!x. x IN V ==> ?n (path:num->num#num).
    path 0=e /\ path n=x /\ !k. k<n ==> edge (path k) (path(SUC k))) /\
  (!x. x IN V ==>
     (need x ==> cc.cc_static) /\
     (!k. boolean x k ==> k < height x /\ tag x k = NONE) /\
     (!k n j. tag x k = SOME(n,j) ==>
       k < height x /\ j < LENGTH p /\
       (EL j p = AsmPushLabel n \/ EL j p = AsmPushOfst n 0) /\ ?w. C p n w)) /\
  (!x k n j. x IN V /\ tag x k = SOME(n,j) ==>
      j <> d /\ j < LENGTH p /\ r j < LENGTH q /\ EL (r j) q = EL j p /\
      T x k = SOME(n,r j) /\
      !w. C p n w ==> w <> d /\ INDEX_OF (AsmLabel n) p = SOME w /\
        INDEX_OF (AsmLabel n) q = SOME(r w) /\ C q n (r w)) ==>
  ?j t eQ.
    sym_steps q (asm_data_env q (assemble q ++ data)) j (sym_init s) = SymOK ssQ /\
    asm_steps (SND (compute_label_offsets q)) (build_offset_to_pc q) q j
      (s with as_code := assemble q ++ data) = AsmOK t /\
    asm_sym_rel q (asm_data_env q (assemble q ++ data)) t ssQ /\
    t.as_pc = ssQ.sym_base.as_pc /\ LENGTH t.as_stack = LENGTH ssQ.sym_stack /\
    t.as_call_ctx = ssQ.sym_base.as_call_ctx /\ t.as_requests = ssQ.sym_base.as_requests /\
    t.as_call_ctx = cc /\ t.as_requests = req /\ t.as_requests <<= req_bound /\
    eQ IN {x | x IN V /\ pc x <> d} /\
    (if pc e <> d then eQ = e else
       edge e eQ /\ pc eQ = d+1 /\ height eQ = height e /\
       (!k n j. tag eQ k = SOME(n,j) ==> tag e k = SOME(n,j)) /\
       (!k. boolean eQ k ==> boolean e k)) /\
    Shape q cc req (r o pc) height need T boolean eQ t /\
    (!k n j. T eQ k = SOME(n,j) ==>
       k < LENGTH ssQ.sym_stack /\ EL k ssQ.sym_stack = Lab n 0) /\
    (!k. boolean eQ k ==>
       k < LENGTH ssQ.sym_stack /\ (EL k ssQ.sym_stack = Val 0w \/ EL k ssQ.sym_stack = Val 1w))
Proof
  MATCH_ACCEPT_TAC (Q.INST [`allow_own` |-> `F`] unused_label_one_actual_root_mode
    |> PURE_REWRITE_RULE [sym_steps_mode_def, COND_CLAUSES])
QED
