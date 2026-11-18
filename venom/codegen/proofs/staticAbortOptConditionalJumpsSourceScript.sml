Theory staticAbortOptConditionalJumpsSource
Ancestors
  asmSymBridge asmSplice asmSymSem asmWf asmIR asmSem stackOpAsmSim
  finite_map pred_set list arithmetic words

(* Select a graph occurrence by the concrete one-step result, not just by
   the existence of an outgoing edge in the certificate. *)
Theorem conditional_source_step[local]:
  (!v t. v IN V /\ shape v t ==>
    (?u. (asm_steps lo otp p 1 t = AsmRevert u \/
          asm_steps lo otp p 1 t = AsmFault u) /\ u.as_requests = req) \/
    (?z u. edge v z /\ asm_steps lo otp p 1 t = AsmOK u /\ shape z u)) ==>
  !y t k r. y IN V /\ shape y t /\ t.as_pc = k /\ k < LENGTH p /\
    asm_step lo otp (EL k p) t = r /\
    (!u. r <> AsmRevert u /\ r <> AsmFault u) ==>
    ?z u. edge y z /\ r = AsmOK u /\ shape z u
Proof
  rpt strip_tac >>
  qpat_x_assum `t.as_pc = k` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `!v t. _` (qspecl_then [`y`,`t`] mp_tac) >>
  rewrite_tac[numLib.num_CONV ``1:num``, asm_steps_def] >>
  Cases_on `r` >> gvs[asm_steps_def]
QED

(* The label at the end of the window is the unique code label c. *)
Theorem conditional_source_label[local]:
  p = pre ++ [AsmPushLabel c; AsmOp "JUMPI"; AsmPushLabel x;
              AsmOp "JUMP"; AsmLabel c] ++ tail /\ asm_static_wf p ==>
  ?off. FLOOKUP (SND (compute_label_offsets p)) c = SOME off /\
    off < dimword(:256) /\
    FLOOKUP (build_offset_to_pc p) off = SOME (LENGTH pre + 4)
Proof
  strip_tac >>
  `~MEM (AsmLabel c) pre` by
    (irule asm_labels_unique_append_not_mem >>
     qexists `[AsmPushLabel c; AsmOp "JUMPI"; AsmPushLabel x;
               AsmOp "JUMP"; AsmLabel c] ++ tail` >> gvs[asm_static_wf_def]) >>
  `INDEX_OF (AsmLabel c) p = SOME (LENGTH pre + 4)` by
    simp[INDEX_OF_APPEND, INDEX_OF_CONS] >>
  drule_all asm_static_wf_code_label >> strip_tac >>
  qexists `off` >> simp[] >>
  `65536 < dimword(:256)` by simp[dimword_def] >> decide_tac
QED

Theorem conditional_source_arity[local]:
  ALOOKUP dup_table "JUMPI" = NONE /\ ALOOKUP swap_table "JUMPI" = NONE /\
  ALOOKUP dup_table "JUMP" = NONE /\ ALOOKUP swap_table "JUMP" = NONE /\
  asm_op_arity "JUMPI" = 2 /\ asm_op_arity "JUMP" = 1
Proof
  EVAL_TAC
QED

Theorem conditional_jump_source_paths:
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
         (EL k t.as_stack = 0w \/ EL k t.as_stack = 1w))
    ) ==>
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
    | _ => F
    ) ==>
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
  !S. S = Shape p cc req pc height need tag boolean ==>
  !b. b = LENGTH pre ==>
  !lo. lo = SND (compute_label_offsets p) ==>
  !D. D = (\w. (!l org. tag v 0 = SOME(l,org) ==>
                    ?off. FLOOKUP lo l = SOME off /\ w = (n2w off:bytes32)) /\
                  (boolean v 0 ==> w = 0w \/ w = 1w)) ==>
  !Tail. Tail = (\z. z IN V /\ rank z < rank v /\ height v = height z + 1 /\
                (!k l org. tag z k = SOME(l,org) ==> tag v (k+1) = SOME(l,org)) /\
                (!k. boolean z k ==> boolean v (k+1)) /\
                (!t. S v t ==> S z (t with <|as_pc := pc z;
                                            as_stack := TL t.as_stack|>))) ==>
  p = pre ++ [AsmPushLabel c; AsmOp "JUMPI"; AsmPushLabel x;
              AsmOp "JUMP"; AsmLabel c] ++ tail /\ asm_static_wf p /\
  Open p cc req V {} rank pc height need tag boolean edge /\ v IN V /\ pc v = b ==>
  0 < height v /\ (!w. D w <=> ?t stk. S v t /\ t.as_stack = w::stk) /\
  (D 0w ==> ?j h i z off. edge v j /\ pc j=b+1 /\ edge j h /\ pc h=b+2 /\
    edge h i /\ pc i=b+3 /\ tag i 0=SOME(x,b+2) /\ edge i z /\
    FLOOKUP lo x=SOME off /\ off<dimword(:256) /\ FLOOKUP (build_offset_to_pc p) off=SOME(pc z) /\ Tail z) /\
  ((?w. D w /\ w <> 0w) ==> ?j a z. edge v j /\ pc j=b+1 /\
    tag j 0=SOME(c,b) /\ edge j a /\ pc a=b+4 /\ Tail a /\
    edge a z /\ pc z=b+5 /\ Tail z)
Proof
  map_every (fn v => qx_gen_tac v >>
    disch_then (assume_tac o CONV_RULE (RAND_CONV
      (TOP_DEPTH_CONV (HO_REWR_CONV UNWIND_FORALL_THM2)) THENC
      REWR_CONV (GSYM markerTheory.Abbrev_def)))) [`Shape`, `Flow`, `Open`] >>
  CONV_TAC (TOP_DEPTH_CONV (HO_REWR_CONV UNWIND_FORALL_THM2)) >>
  simp_tac std_ss [] >>
  disch_then (CONJUNCTS_THEN2 (mk_asm "window") strip_assume_tac) >>
  qpat_x_assum `Open _ _ _ _ _ _ _ _ _ _ _ _` mp_tac >>
  simp[NoAsms, Abbr `Open`, LET_THM, DIFF_EMPTY] >> strip_tac >>
  qabbrev_tac `shape = Shape p cc req pc height need tag boolean` >>
  qabbrev_tac `b = LENGTH pre` >>
  qabbrev_tac `lo = SND (compute_label_offsets p)` >>
  qabbrev_tac `o2pc = build_offset_to_pc p` >>
  qabbrev_tac `D = \w. (!l org. tag v 0 = SOME(l,org) ==>
                  ?off. FLOOKUP lo l = SOME off /\ w = (n2w off:bytes32)) /\
                       (boolean v 0 ==> w = 0w \/ w = 1w)` >>
  `!y t. shape y t ==> t.as_pc = pc y /\ LENGTH t.as_stack = height y`
    by simp[NoAsms, Abbr `shape`, Abbr `Shape`] >>
  `!y t r. y IN V /\ shape y t /\
        asm_step lo o2pc (EL (pc y) p) t = r /\
        (!u. r <> AsmRevert u /\ r <> AsmFault u) ==>
        ?z u. edge y z /\ r = AsmOK u /\ shape z u` by
    (drule conditional_source_step >> rpt strip_tac >>
     first_x_assum (qspecl_then [`y`,`t`,`pc y`,`r`] mp_tac) >>
     (impl_tac >- metis_tac[]) >> simp[NoAsms]) >>
  pop_assum $ mk_asm "step" >>
  `?oc. FLOOKUP lo c = SOME oc /\ oc < dimword(:256) /\
        FLOOKUP o2pc oc = SOME (b+4)` by
    (simp[Abbr `lo`, Abbr `o2pc`, Abbr `b`, NoAsms] >>
     asm "window" assume_tac >> drule_all conditional_source_label >> simp[NoAsms]) >>
  `EL b p = AsmPushLabel c /\ EL (b+1) p = AsmOp "JUMPI" /\
   EL (b+2) p = AsmPushLabel x /\ EL (b+3) p = AsmOp "JUMP" /\
   EL (b+4) p = AsmLabel c` by
    (asm "window" SUBST1_TAC >>
     once_rewrite_tac [GSYM listTheory.APPEND_ASSOC] >>
     simp[Abbr `b`, EL_APPEND_EQN]) >>
  `!y t u. y IN V /\ shape y t /\
        asm_step lo o2pc (EL (pc y) p) t = AsmOK u ==>
        ?j. edge y j /\ shape j u /\ u.as_pc = pc j /\
            LENGTH u.as_stack = height j` by
    (rpt strip_tac >> asm "step" (qspecl_then [`y`,`t`,`AsmOK u`] mp_tac) >>
     simp[IgnAsm `p = _`] >> strip_tac >> rename1 `edge y j` >>
     qexists `j` >> simp[] >>
     qpat_assum `!y t. shape y t ==> _` (qspecl_then [`j`,`u`] mp_tac) >> simp[]) >>
  pop_assum $ mk_asm "ok" >>
  `!y l off t. y IN V /\ shape y t /\ EL (pc y) p = AsmPushLabel l /\
                FLOOKUP lo l = SOME off ==>
     ?j u. edge y j /\ shape j u /\ pc j = pc y + 1 /\
           u.as_stack = n2w off :: t.as_stack` by
    (rpt strip_tac >>
     asm "ok" (qspecl_then [`y`,`t`,`asm_next (t with as_stack := n2w off :: t.as_stack)`] mp_tac) >>
     simp[asm_step_pushlabel_ok] >> strip_tac >> rename1 `edge y j` >>
     qexistsl [`j`,`asm_next (t with as_stack := n2w off :: t.as_stack)`] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     simp[NoAsms, asm_next_def] >>
     qpat_assum `(asm_next _).as_pc = pc j` mp_tac >>
     simp[NoAsms, asm_next_def] >> metis_tac[]) >>
  pop_assum $ mk_asm "push" >>
  `!t. shape v t ==> t.as_stack <> []` by
    (qx_gen_tac `cur` >> DISCH_TAC >> strip_tac >>
     asm "push" (qspecl_then [`v`,`c`,`oc`,`cur`] mp_tac) >>
     (impl_tac >- simp[IgnAsm `p = _`]) >> strip_tac >>
     rename1 `edge v j` >> rename1 `shape j u` >>
     `j IN V` by (qpat_assum `!a b. edge a b ==> _`
         (qspecl_then [`v`,`j`] mp_tac) >> simp[NoAsms] >> metis_tac[]) >>
     asm "step" (qspecl_then [`j`,`u`,`AsmError "jumpi: stack underflow"`] mp_tac) >>
     simp[asm_step_jumpi, asm_jumpi_def]) >>
  `?orig. shape v orig` by metis_tac[] >>
  rename1 `shape v orig` >>
  `?hd stk. orig.as_stack = hd::stk` by
    (Cases_on `orig.as_stack` >> simp[] >> metis_tac[]) >>
  `0 < height v` by
    (`LENGTH orig.as_stack = height v` by metis_tac[] >>
     Cases_on `height v` >> simp[NoAsms] >> metis_tac[LENGTH_NIL]) >>
  (* E0277: tagged-head replacement, superseded by the untagged update.
  `!w. D w <=> ?t stk. shape v t /\ t.as_stack = w::stk` by
    (qx_gen_tac `w` >> eq_tac
     >- (strip_tac >>
         qexistsl [`orig with as_stack := w::stk`,`stk`] >>
         qpat_x_assum `shape v orig` mp_tac >>
         qpat_x_assum `D w` mp_tac >>
         simp[NoAsms, Abbr `D`, Abbr `shape`, Abbr `Shape`, Abbr `lo`] >>
         ntac 2 strip_tac >> simp[IgnAsm `p = _`] >>
         (conj_tac >-
          (qpat_assum `orig.as_stack = hd::stk` (fn st_eq =>
             qpat_assum `LENGTH orig.as_stack = height v`
               (ACCEPT_TAC o REWRITE_RULE [st_eq,LENGTH])))) >>
         (conj_tac >-
          (qpat_assum `orig.as_call_ctx = cc` (fn ctx_eq =>
             qpat_assum `need v ==> _`
               (ACCEPT_TAC o REWRITE_RULE [ctx_eq])))) >>
         conj_tac
         >- (qx_gen_tac `k` >> Cases_on `k`
             >- (map_every qx_gen_tac [`l`,`origin`] >> DISCH_TAC >>
                 qpat_assum `!k l org. tag v k = SOME(l,org) ==> _`
                   (qspecl_then [`0`,`l`,`origin`] mp_tac) >>
                 (impl_tac >- first_assum ACCEPT_TAC) >>
                 disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
                 qpat_assum `?off dest. _ /\ _ /\ _ /\ _`
                   (qx_choose_then `oldoff` (qx_choose_then `dest` strip_assume_tac)) >>
                 qpat_assum `!l org. tag v 0 = SOME(l,org) ==> _`
                   (qspecl_then [`l`,`origin`] mp_tac) >>
                 (impl_tac >- first_assum ACCEPT_TAC) >>
                 disch_then (qx_choose_then `newoff` strip_assume_tac) >>
                 `oldoff = newoff` by
                   (qpat_assum `FLOOKUP _ l = SOME oldoff` mp_tac >>
                    qpat_assum `FLOOKUP _ l = SOME newoff` (fn th => simp[NoAsms, th])) >>
                 conj_tac >- simp[IgnAsm `p = _`] >>
                 conj_tac >- first_assum ACCEPT_TAC >>
                 qexistsl [`oldoff`,`dest`] >>
                 qpat_assum `FLOOKUP o2pc oldoff = SOME dest` mp_tac >>
                 simp[IgnAsm `p = _`]) >>
             map_every qx_gen_tac [`l`,`origin`] >> DISCH_TAC >>
             qpat_assum `!k l org. tag v k = SOME(l,org) ==> _`
               (qspecl_then [`SUC n`,`l`,`origin`] mp_tac) >>
             simp[IgnAsm `p = _`]) >>
         qx_gen_tac `k` >> Cases_on `k`
         >- (DISCH_TAC >> qpat_assum `boolean v 0 ==> _` mp_tac >>
             simp[IgnAsm `p = _`]) >>
         DISCH_TAC >> qpat_assum `!k. boolean v k ==> _`
           (qspec_then `SUC n` mp_tac) >> simp[IgnAsm `p = _`]) >>
     strip_tac >>
     rename1 `shape v cur` >>
     qpat_assum `shape v cur` mp_tac >>
     simp[Abbr `D`, Abbr `shape`, Abbr `Shape`, Abbr `lo`, IgnAsm `p = _`] >>
     metis_tac[EL]) >>
  *)
  `!t h xs. shape v t /\ t.as_stack = h::xs ==> D h` by
    (simp[NoAsms, Abbr `shape`, Abbr `Shape`, Abbr `D`, Abbr `lo`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt gen_tac >> strip_tac >>
     conj_tac
     >- (map_every qx_gen_tac [`l`,`org`] >> DISCH_TAC >>
         qpat_assum `!k l org. tag v k = SOME(l,org) ==> _`
           (qspecl_then [`0`,`l`,`org`] mp_tac) >>
         (impl_tac >- first_assum ACCEPT_TAC) >>
         disch_then (MAP_EVERY assume_tac o CONJUNCTS) >>
         qpat_assum `?off dest. _ /\ _ /\ _ /\ _`
           (qx_choose_then `off` (qx_choose_then `dest` strip_assume_tac)) >>
         qexists `off` >> conj_tac >- first_assum ACCEPT_TAC >>
         pop_assum mp_tac >>
         qpat_assum `t.as_stack = h::xs` (fn st => simp[NoAsms, st, EL])) >>
     DISCH_TAC >>
     qpat_assum `!k. boolean v k ==> _` (qspec_then `0` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     qpat_assum `t.as_stack = h::xs` (fn st => simp[NoAsms, st, EL])) >>
  pop_assum $ mk_asm "head" >>
  `!t h xs w. shape v t /\ t.as_stack = h::xs /\ tag v 0 = NONE /\
       (boolean v 0 ==> w = 0w \/ w = 1w) ==>
       shape v (t with as_stack := w::xs)` by
    (simp[NoAsms, Abbr `shape`, Abbr `Shape`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> rpt gen_tac >>
     strip_tac >>
     (* Normalize the call context and the common length before splitting slots. *)
     gvs[] >>
     conj_tac
     >- (qx_gen_tac `k` >> Cases_on `k`
         >- simp[] >>
         (* E0286: once-specialized contextual simp lost the witness:
            (qspec_then `SUC n` mp_tac) >> simp[EL] >> metis_tac[] *)
         map_every qx_gen_tac [`l`,`org`] >> DISCH_TAC >>
         qpat_assum `!k l org. tag v k = SOME(l,org) ==> _`
           (qspecl_then [`SUC n`,`l`,`org`] mp_tac) >>
         (impl_tac >- first_assum ACCEPT_TAC) >>
         simp[NoAsms, EL]) >>
     qx_gen_tac `k` >> Cases_on `k`
     >- (DISCH_TAC >> simp[EL]) >>
     DISCH_TAC >>
     qpat_assum `!k. boolean v k ==> _` (qspec_then `SUC n` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> simp[NoAsms, EL]) >>
  pop_assum $ mk_asm "untagged" >>
  `!w. D w <=> ?t xs. shape v t /\ t.as_stack = w::xs` by
    (qx_gen_tac `w` >> eq_tac
     >- (DISCH_TAC >>
         Cases_on `tag v 0`
         >- (qexistsl [`orig with as_stack := w::stk`,`stk`] >>
             simp[] >>
             asm "untagged" (qspecl_then [`orig`,`hd`,`stk`,`w`] mp_tac) >>
             (impl_tac >- (simp[] >> qpat_assum `D w` mp_tac >>
                            simp[NoAsms, Abbr `D`])) >>
             disch_then ACCEPT_TAC) >>
         rename1 `tag v 0 = SOME ann` >> PairCases_on `ann` >>
         `D hd` by (asm "head" (qspecl_then [`orig`,`hd`,`stk`] mp_tac) >>
                    (impl_tac >- simp[]) >> disch_then ACCEPT_TAC) >>
         `!word. D word ==> ?off. FLOOKUP lo ann0 = SOME off /\ word = n2w off` by
           (qx_gen_tac `word` >>
            simp[NoAsms, Abbr `D`] >>
            disch_then (CONJUNCTS_THEN2 (qspecl_then [`ann0`,`ann1`] mp_tac) (K ALL_TAC)) >>
            (impl_tac >- first_assum ACCEPT_TAC) >> disch_then ACCEPT_TAC) >>
         `w = hd` by
           (pop_assum (fn th => mp_tac (Q.SPEC `w` th) >> mp_tac (Q.SPEC `hd` th)) >>
            (impl_tac >- first_assum ACCEPT_TAC) >> DISCH_TAC >>
            (impl_tac >- first_assum ACCEPT_TAC) >>
            pop_assum mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >>
            metis_tac[optionTheory.SOME_11]) >>
         qexistsl [`orig`,`stk`] >> simp[]) >>
     disch_then (qx_choose_then `cur` (qx_choose_then `xs` strip_assume_tac)) >>
     asm "head" (qspecl_then [`cur`,`w`,`xs`] mp_tac) >>
     (impl_tac >- simp[]) >> disch_then ACCEPT_TAC) >>
  pop_assum $ mk_asm "feasible" >>
  (* First select occurrences for the two instructions shared by both paths. *)
  `!w. D w ==> ?j y dst xs. edge v j /\ pc j = b+1 /\ edge j y /\
          pc y = (if w = 0w then b+2 else b+4) /\
          shape y dst /\ dst.as_stack = xs` by
    (qx_gen_tac `w` >> DISCH_TAC >>
     asm "feasible" (qspec_then `w` (mp_tac o iffLR)) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     disch_then (qx_choose_then `cur` (qx_choose_then `xs` strip_assume_tac)) >>
     asm "push" (qspecl_then [`v`,`c`,`oc`,`cur`] mp_tac) >>
     (impl_tac >- simp[IgnAsm `p = _`]) >>
     disch_then (qx_choose_then `j` (qx_choose_then `u` strip_assume_tac)) >>
     `j IN V` by (qpat_assum `!a b. edge a b ==> _`
         (qspecl_then [`v`,`j`] mp_tac) >> simp[NoAsms] >> metis_tac[]) >>
     qabbrev_tac `dst = u with <|as_stack := xs;
                           as_pc := if w = 0w then b+2 else b+4|>` >>
     (* Earlier simp-only projections did not close the PC equation. *)
     `u.as_pc = b+1` by metis_tac[IgnAsm `p = _`] >>
     `asm_step lo o2pc (EL (pc j) p) u = AsmOK dst` by
       (Cases_on `w = 0w` >>
        simp[IgnAsm `p = _`, asm_step_jumpi, asm_jumpi_def, Abbr `dst`,
             w2n_n2w, LESS_MOD, asm_next_def]) >>
     asm "ok" (qspecl_then [`j`,`u`,`dst`] mp_tac) >>
     (impl_tac >- simp[IgnAsm `p = _`]) >>
     disch_then (qx_choose_then `y` strip_assume_tac) >>
     `pc y = (if w = 0w then b+2 else b+4)` by
       (qpat_assum `dst.as_pc = pc y` (mp_tac o SYM) >> simp[NoAsms, Abbr `dst`]) >>
     qexistsl [`j`,`y`,`dst`,`xs`] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- simp[IgnAsm `p = _`] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     simp[NoAsms, Abbr `dst`]) >>
  pop_assum $ mk_asm "common" >>
  `!y z. edge y z ==> y IN V /\ z IN V /\ rank z < rank y /\
                        Flow p pc height tag boolean y z` by metis_tac[] >>
  pop_assum $ mk_asm "edge_flow" >>
  `!y z l. edge y z /\ EL (pc y) p = AsmPushLabel l /\ tag z 0 <> NONE ==>
           tag z 0 = SOME(l,pc y)` by
    (rpt strip_tac >> asm "edge_flow" (qspecl_then [`y`,`z`] mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     disch_then (mp_tac o cj 4) >>
     qpat_assum `EL (pc y) p = AsmPushLabel l`
       (fn ins => simp[NoAsms, ins, Abbr `Flow`, LET_THM]) >> strip_tac >>
     Cases_on `tag z 0` >- metis_tac[] >>
     rename1 `tag z 0 = SOME ann` >> PairCases_on `ann` >>
     qpat_assum `!k l origin. tag z k = SOME(l,origin) ==> _`
       (qspecl_then [`0`,`ann0`,`ann1`] mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     simp[NoAsms] >> metis_tac[]) >>
  pop_assum $ mk_asm "fresh" >>
  `D 0w ==> ?j h i z off. edge v j /\ pc j=b+1 /\ edge j h /\ pc h=b+2 /\
      edge h i /\ pc i=b+3 /\ tag i 0=SOME(x,b+2) /\ edge i z /\
      FLOOKUP lo x=SOME off /\ off<dimword(:256) /\ FLOOKUP o2pc off=SOME(pc z)` by
    (DISCH_TAC >> asm "common" (qspec_then `0w:bytes32` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> simp[NoAsms] >>
     disch_then (qx_choose_then `j` (qx_choose_then `h`
        (qx_choose_then `dst` strip_assume_tac))) >>
     `h IN V` by (asm "edge_flow" mp_tac >> metis_tac[]) >>
     `?ox. FLOOKUP lo x = SOME ox` by
       (Cases_on `FLOOKUP lo x` >> simp[NoAsms] >>
        asm "step" (qspecl_then [`h`,`dst`,`AsmError ("unknown label: " ++ x)`] mp_tac) >>
        simp[IgnAsm `p = _`, asm_step_def]) >>
     asm "push" (qspecl_then [`h`,`x`,`ox`,`dst`] mp_tac) >>
     (impl_tac >- simp[IgnAsm `p = _`]) >>
     disch_then (qx_choose_then `i` (qx_choose_then `u` strip_assume_tac)) >>
     `pc i = b+3` by metis_tac[DECIDE ``(b+2)+1=b+3:num``] >>
     `i IN V` by (asm "edge_flow" mp_tac >> metis_tac[]) >>
     `?z out. edge i z /\ shape z out` by
       (asm "step" (qspecl_then [`i`,`u`,`asm_jump o2pc u`] mp_tac) >>
        (impl_tac >-
          (simp[IgnAsm `p = _`, asm_step_jump, asm_jump_def] >>
           Cases_on `FLOOKUP o2pc (ox MOD dimword(:256))` >> simp[])) >>
        metis_tac[]) >>
     (* Project the original edge's control clause, not the shorter edge_flow. *)
     qpat_assum `!a b. edge a b ==> _ /\ _ /\ _ /\ _ /\ if _ then _ else _`
       (qspecl_then [`i`,`z`] mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> disch_then (mp_tac o cj 5) >>
     `EL (pc i) p = AsmOp "JUMP"` by simp[IgnAsm `p = _`] >>
     qpat_assum `EL (pc i) p = AsmOp "JUMP"` (fn th => simp[NoAsms,th]) >>
     disch_then (qx_choose_then `l` (qx_choose_then `org` (qx_choose_then `off` strip_assume_tac))) >>
     `tag i 0 = SOME(x,b+2)` by
       (asm "fresh" (qspecl_then [`h`,`i`,`x`] mp_tac) >>
        (impl_tac >- simp[IgnAsm `p = _`]) >> simp[IgnAsm `p = _`]) >>
     `l = x` by metis_tac[optionTheory.SOME_11, pairTheory.PAIR_EQ] >>
     qexistsl [`j`,`h`,`i`,`z`,`off`] >> metis_tac[]) >>
  (* The nonzero branch lands on c, then advances past its label. *)
  `(?w. D w /\ w <> 0w) ==> ?j a z. edge v j /\ pc j=b+1 /\
      tag j 0=SOME(c,b) /\ edge j a /\ pc a=b+4 /\ edge a z /\ pc z=b+5` by
    (disch_then (qx_choose_then `w` strip_assume_tac) >>
     asm "common" (qspec_then `w` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     simp[IgnAsm `p = _`] >>
     disch_then (qx_choose_then `j` (qx_choose_then `a`
        (qx_choose_then `dst` strip_assume_tac))) >>
     `a IN V` by (asm "edge_flow" mp_tac >> metis_tac[]) >>
     `EL (pc j) p = AsmOp "JUMPI"` by simp[IgnAsm `p = _`] >>
     `pc a <> pc j + 1` by
       (simp[IgnAsm `p = _`] >> decide_tac) >>
     qpat_assum `!a b. edge a b ==> _ /\ _ /\ _ /\ _ /\ if _ then _ else _`
       (qspecl_then [`j`,`a`] mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> disch_then (mp_tac o cj 5) >>
     (* Contextual simp discharged the whole projected antecedent. *)
     qpat_assum `EL (pc j) p = AsmOp "JUMPI"` (fn ins =>
       qpat_assum `pc a <> pc j + 1` (fn nofall => simp[NoAsms, ins, nofall])) >>
     disch_then (qx_choose_then `l` (qx_choose_then `org`
        (qx_choose_then `off` strip_assume_tac))) >>
     `tag j 0 = SOME(c,b)` by
       (asm "fresh" (qspecl_then [`v`,`j`,`c`] mp_tac) >>
        (impl_tac >- simp[IgnAsm `p = _`]) >> simp[IgnAsm `p = _`]) >>
     asm "ok" (qspecl_then [`a`,`dst`,`asm_next dst`] mp_tac) >>
     (impl_tac >- simp[IgnAsm `p = _`, asm_step_label_ok]) >>
     disch_then (qx_choose_then `z` strip_assume_tac) >>
     `dst.as_pc = pc a` by metis_tac[] >>
     `pc z = b+5` by
       ((* Contextual simp did not retain the PC equation for arithmetic. *)
        qpat_assum `(asm_next dst).as_pc = pc z` (mp_tac o SYM) >>
        qpat_assum `dst.as_pc = pc a` (fn st =>
          qpat_assum `pc a = b+4` (fn atc =>
            simp[NoAsms, asm_next_def, st, atc, ADD_ASSOC]))) >>
     qexistsl [`j`,`a`,`z`] >> simp[IgnAsm `p = _`]) >>
  (* Read the demand projections off Flow; do not replay another branch
     when transporting a demand to an arbitrary entry stack. *)
  qabbrev_tac `backs = \y z src dst.
    (!l org. tag z dst = SOME(l,org) ==> tag y src = SOME(l,org)) /\
    (boolean z dst ==> boolean y src)` >>
  `!y z l. edge y z /\ EL (pc y) p = AsmPushLabel l ==>
     height z = height y + 1 /\ !k. backs y z k (k+1)` by
    (rpt gen_tac >> strip_tac >>
     asm "edge_flow" (qspecl_then [`y`,`z`] mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> disch_then (mp_tac o cj 4) >>
     qpat_assum `EL (pc y) p = AsmPushLabel l` (fn ins =>
       simp[NoAsms, ins, Abbr `Flow`, Abbr `backs`, LET_THM]) >>
     (* The normalized antecedent has already discharged the height. *)
     strip_tac >> qx_gen_tac `k` >> conj_tac
     >- (map_every qx_gen_tac [`l'`,`org`] >> DISCH_TAC >>
         qpat_assum `!k l org. tag z k = SOME(l,org) ==> _`
           (qspecl_then [`k+1`,`l'`,`org`] mp_tac) >>
         (impl_tac >- first_assum ACCEPT_TAC) >> simp[NoAsms]) >>
     DISCH_TAC >> qpat_assum `!k. boolean z k ==> _`
       (qspec_then `k+1` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> simp[NoAsms]) >>
  pop_assum $ mk_asm "push_back" >>
  `!y z l. edge y z /\ EL (pc y) p = AsmLabel l ==>
     height z = height y /\ !k. backs y z k k` by
    (rpt gen_tac >> strip_tac >>
     asm "edge_flow" (qspecl_then [`y`,`z`] mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> disch_then (mp_tac o cj 4) >>
     qpat_assum `EL (pc y) p = AsmLabel l` (fn ins =>
       simp[NoAsms, ins, Abbr `Flow`, Abbr `backs`, LET_THM]) >>
     metis_tac[]) >>
  pop_assum $ mk_asm "label_back" >>
  `!y z n. edge y z /\
     (EL (pc y) p = AsmOp "JUMP" /\ n = 1 \/
      EL (pc y) p = AsmOp "JUMPI" /\ n = 2) ==>
     height y = height z + n /\ !k. backs y z (k+n) k` by
    (rpt gen_tac >> strip_tac >>
     asm "edge_flow" (qspecl_then [`y`,`z`] mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> disch_then (mp_tac o cj 4) >>
     qpat_assum `EL (pc y) p = AsmOp _` (fn ins =>
       simp[NoAsms, ins, Abbr `Flow`, Abbr `backs`, LET_THM,
            conditional_source_arity]) >>
     strip_tac >>
     `height y = height z + n` by decide_tac >>
     (conj_tac >- simp[]) >>
     (* A broad Metis call here timed out on the unspecialized slot clauses. *)
     qx_gen_tac `k` >> (conj_tac
     >- (map_every qx_gen_tac [`lbl`,`org`] >> DISCH_TAC >>
         qpat_assum `!k l org. tag z k = SOME(l,org) ==> _`
           (qspecl_then [`k`,`lbl`,`org`] mp_tac) >>
         (impl_tac >- first_assum ACCEPT_TAC) >>
         qpat_assum `height y = height z + n` (fn ht =>
           qpat_assum `n = _` (fn ar => simp[NoAsms, ht, ar])))) >>
     DISCH_TAC >> qpat_assum `!k. boolean z k ==> _` (qspec_then `k` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     qpat_assum `height y = height z + n` (fn ht =>
       qpat_assum `n = _` (fn ar => simp[NoAsms, ht, ar]))) >>
  pop_assum $ mk_asm "jump_back" >>
  (* Inhabitation of z supplies its static-field guard at the common cc.
     The slot demands and length then suffice for every entry state. *)
  `!z. z IN V /\ height v = height z+1 /\ (!k. backs v z (k+1) k) ==>
     !t. shape v t ==> shape z (t with <|as_pc := pc z;
                                          as_stack := TL t.as_stack|>)` by
    (qx_gen_tac `z` >> strip_tac >>
     `?other. shape z other` by metis_tac[] >>
     `(need z ==> cc.cc_static)` by
       (qpat_assum `shape z other` mp_tac >>
        simp[NoAsms, Abbr `shape`, Abbr `Shape`] >> strip_tac >>
        metis_tac[IgnAsm `p = _`]) >>
     qx_gen_tac `cur` >> DISCH_TAC >>
     `?w xs. cur.as_stack = w::xs` by
       (Cases_on `cur.as_stack` >> simp[NoAsms] >> metis_tac[]) >>
     `LENGTH xs = height z` by
       (`LENGTH cur.as_stack = height v` by metis_tac[] >>
        qpat_assum `LENGTH cur.as_stack = height v` mp_tac >>
        qpat_assum `cur.as_stack = w::xs` (fn st =>
          qpat_assum `height v = height z+1` (fn ht =>
            simp[NoAsms, st, ht, LENGTH, ADD1]))) >>
     qpat_assum `shape v cur` mp_tac >>
     qpat_assum `!k. backs v z (k+1) k` mp_tac >>
     simp[NoAsms, Abbr `shape`, Abbr `Shape`, Abbr `backs`] >>
     strip_tac >> strip_tac >>
     simp[IgnAsm `p = _`, IgnAsm `!k. _`] >>
     conj_tac
     >- (map_every qx_gen_tac [`k`,`lbl`,`org`] >> DISCH_TAC >>
         `tag v (k+1) = SOME(lbl,org)` by
           (qpat_assum `!k. (!l org. tag z k = SOME(l,org) ==> _) /\ _`
              (qspec_then `k` (mp_tac o cj 1)) >> metis_tac[]) >>
         qpat_assum `!k l org. tag v k = SOME(l,org) ==> _`
           (qspecl_then [`k+1`,`lbl`,`org`] mp_tac) >>
         (impl_tac >- first_assum ACCEPT_TAC) >>
         qpat_assum `cur.as_stack = w::xs` (fn st =>
           qpat_assum `height v = height z+1` (fn ht =>
             simp[NoAsms, st, ht, GSYM ADD1, EL, Abbr `lo`, Abbr `o2pc`]))) >>
     qx_gen_tac `k` >> DISCH_TAC >>
     `boolean v (k+1)` by
       (qpat_assum `!k. (!l org. tag z k = SOME(l,org) ==> _) /\ _`
          (qspec_then `k` (mp_tac o cj 2)) >> metis_tac[]) >>
     qpat_assum `!k. boolean v k ==> _` (qspec_then `k+1` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     qpat_assum `cur.as_stack = w::xs` (fn st =>
       qpat_assum `height v = height z+1` (fn ht =>
         simp[NoAsms, st, ht, GSYM ADD1, EL]))) >>
  pop_assum $ mk_asm "tail_shape" >>
  `!u y z r s t. backs u y r s /\ backs y z s t ==> backs u z r t` by
    (simp[NoAsms, Abbr `backs`] >> metis_tac[]) >>
  pop_assum $ mk_asm "backs_trans" >>
  `!z. z IN V /\ rank z < rank v /\ height v = height z+1 /\
       (!k. backs v z (k+1) k) ==>
       z IN V /\ rank z < rank v /\ height v = height z+1 /\
       (!k l org. tag z k = SOME(l,org) ==> tag v (k+1) = SOME(l,org)) /\
       (!k. boolean z k ==> boolean v (k+1)) /\
       (!t. shape v t ==> shape z (t with <|as_pc := pc z;
                                           as_stack := TL t.as_stack|>))` by
    (qx_gen_tac `z` >> strip_tac >>
     asm "tail_shape" (qspec_then `z` mp_tac) >>
     (impl_tac >- simp[IgnAsm `p = _`]) >>
     qpat_assum `!k. backs v z (k+1) k` mp_tac >>
     simp[NoAsms, Abbr `backs`, FORALL_AND_THM] >> metis_tac[]) >>
  pop_assum $ mk_asm "tail_intro" >>
  (* Restore the lexical names after the simplifier substituted the window. *)
  asm "window" (SUBST1_TAC o SYM) >>
  qpat_assum `Abbrev (lo = _)` (SUBST1_TAC o SYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  qpat_assum `Abbrev (o2pc = _)` (SUBST1_TAC o SYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  qpat_assum `Abbrev (shape = _)` (SUBST1_TAC o SYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >-
    (asm "feasible" mp_tac >> simp[NoAsms, Abbr `D`]) >>
  (* Both paths begin with PUSH c and JUMPI, which consume one net slot. *)
  `!j y. edge v j /\ pc j = b+1 /\ edge j y ==>
       y IN V /\ rank y < rank v /\ height v = height y+1 /\
       !k. backs v y (k+1) k` by
    (rpt gen_tac >> strip_tac >>
     asm "edge_flow" (qspecl_then [`j`,`y`] mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
     asm "edge_flow" (qspecl_then [`v`,`j`] mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
     asm "push_back" (qspecl_then [`v`,`j`,`c`] mp_tac) >>
     (impl_tac >- simp[IgnAsm `p = _`]) >> strip_tac >>
     asm "jump_back" (qspecl_then [`j`,`y`,`2`] mp_tac) >>
     (impl_tac >- simp[IgnAsm `p = _`]) >> strip_tac >>
     (conj_tac >- first_assum ACCEPT_TAC) >>
     (* E0321 diagnostic (before the explicit natural-rank annotation):
        qpat_assum `rank y < rank j` mp_tac >>
        qpat_assum `rank j < rank v` mp_tac >>
        (fn (asl,g) =>
           let
             val (p1,g') = boolSyntax.dest_imp g
             val (p2,p3) = boolSyntax.dest_imp g'
             fun parts t =
               let val (f,rhs) = Term.dest_comb t
                   val (h,lhs) = Term.dest_comb f
               in (h,lhs,rhs) end
             fun describe t =
               let val (h,lhs,rhs) = parts t
                   val {Thy,Name,...} = Term.dest_thy_const h
                   fun operand a = Parse.term_to_string a ^ " : " ^
                                   Parse.type_to_string (Term.type_of a)
               in Thy ^ "$" ^ Name ^ " at " ^ operand lhs ^ ", " ^ operand rhs end
             val (_,mid1,_) = parts p1
             val (_,_,mid2) = parts p2
           in FAIL_TAC (String.concatWith " | " (map describe [p1,p2,p3]) ^
                         " | middle aconv = " ^ Bool.toString (Term.aconv mid1 mid2))
                (asl,g) end)
        This found rat$rat_les and identical middle operands. *)
     (conj_tac >- (Q_TAC (TRANS_TAC LESS_TRANS) `rank j` >>
                   conj_tac >> first_assum ACCEPT_TAC)) >>
     (conj_tac >- (qpat_assum `height j = height v+1` mp_tac >>
                   qpat_assum `height j = height y+2` mp_tac >> POP_ASSUM_LIST (K numLib.ARITH_TAC))) >>
     qx_gen_tac `k` >>
     asm "backs_trans" (qspecl_then [`v`,`j`,`y`,`k+1`,`k+2`,`k`] mp_tac) >>
     (impl_tac >-
       (conj_tac >-
         (qpat_assum `!n. backs v j n (n+1)` (qspec_then `k+1` mp_tac) >>
          simp[NoAsms, GSYM ADD_ASSOC]) >> simp[])) >>
     simp[NoAsms]) >>
  pop_assum $ mk_asm "prefix_back" >>
  conj_tac
  >- (DISCH_TAC >>
      `D 0w` by (simp[NoAsms, Abbr `D`] >> first_assum ACCEPT_TAC) >>
      qpat_assum `D 0w ==> _` mp_tac >>
      (impl_tac >- first_assum ACCEPT_TAC) >>
      disch_then (qx_choose_then `j` (qx_choose_then `h` (qx_choose_then `i`
                   (qx_choose_then `z` (qx_choose_then `off` strip_assume_tac))))) >>
      asm "prefix_back" (qspecl_then [`j`,`h`] mp_tac) >>
      (impl_tac >- simp[IgnAsm `p = _`]) >> strip_tac >>
      asm "push_back" (qspecl_then [`h`,`i`,`x`] mp_tac) >>
      (impl_tac >- simp[IgnAsm `p = _`]) >> strip_tac >>
      asm "jump_back" (qspecl_then [`i`,`z`,`1`] mp_tac) >>
      (impl_tac >- simp[IgnAsm `p = _`]) >> strip_tac >>
      asm "edge_flow" (qspecl_then [`h`,`i`] mp_tac) >>
      (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
      asm "edge_flow" (qspecl_then [`i`,`z`] mp_tac) >>
      (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
      `!k. backs h z k k` by
        (qx_gen_tac `k` >>
         asm "backs_trans" (qspecl_then [`h`,`i`,`z`,`k`,`k+1`,`k`] mp_tac) >>
         (impl_tac >- simp[]) >> simp[NoAsms]) >>
      `!k. backs v z (k+1) k` by
        (qx_gen_tac `k` >>
         asm "backs_trans" (qspecl_then [`v`,`h`,`z`,`k+1`,`k`,`k`] mp_tac) >>
         (impl_tac >- simp[]) >> simp[NoAsms]) >>
      asm "tail_intro" (qspec_then `z` mp_tac) >>
      (impl_tac >-
        ((conj_tac >- first_assum ACCEPT_TAC) >>
         (* Before fixing the rank type, the staged closer was
            POP_ASSUM_LIST (K (metis_tac[LESS_TRANS, WORD_LESS_TRANS])). *)
         (conj_tac >- (Q_TAC (TRANS_TAC LESS_TRANS) `rank h` >>
                       (conj_tac >- (Q_TAC (TRANS_TAC LESS_TRANS) `rank i` >>
                                     conj_tac >> first_assum ACCEPT_TAC)) >>
                       first_assum ACCEPT_TAC)) >>
         (conj_tac >- (qpat_assum `height i = height h+1` mp_tac >>
                       qpat_assum `height i = height z+1` mp_tac >>
                       qpat_assum `height v = height h+1` mp_tac >> POP_ASSUM_LIST (K numLib.ARITH_TAC))) >>
         first_assum ACCEPT_TAC)) >>
      (* Both `simp[IgnAsm p, th]` and `rewrite_tac [th] >> simp[...]`
         left the universal Shape clause. Normalize the Tail facts, then
         use the implication at the chosen state. *)
      disch_then (strip_assume_tac o SRULE []) >>
      qexistsl [`j`,`h`,`i`,`z`,`off`] >> simp[IgnAsm `p = _`] >>
      qx_gen_tac `cur` >> DISCH_TAC >>
      qpat_assum `!t. shape v t ==> shape z _` (qspec_then `cur` mp_tac) >>
      (impl_tac >- first_assum ACCEPT_TAC) >> simp[NoAsms]) >>
  DISCH_TAC >>
  `?w. D w /\ w <> 0w` by (simp[NoAsms, Abbr `D`] >> first_assum ACCEPT_TAC) >>
  qpat_assum `(?w. D w /\ w <> 0w) ==> _` mp_tac >>
  (* The preceding `by` strips the existential, so use its witness explicitly
     rather than attempting `first_assum ACCEPT_TAC` on the existential. *)
  (impl_tac >- (qexists `w` >> simp[])) >>
  disch_then (qx_choose_then `j` (qx_choose_then `a` (qx_choose_then `z` strip_assume_tac))) >>
  asm "prefix_back" (qspecl_then [`j`,`a`] mp_tac) >>
  (impl_tac >- simp[IgnAsm `p = _`]) >> strip_tac >>
  asm "label_back" (qspecl_then [`a`,`z`,`c`] mp_tac) >>
  (impl_tac >- simp[IgnAsm `p = _`]) >> strip_tac >>
  asm "edge_flow" (qspecl_then [`a`,`z`] mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  `!k. backs v z (k+1) k` by
    (qx_gen_tac `k` >>
     asm "backs_trans" (qspecl_then [`v`,`a`,`z`,`k+1`,`k`,`k`] mp_tac) >>
     (impl_tac >- simp[]) >> simp[NoAsms]) >>
  asm "tail_intro" (qspec_then `a` mp_tac) >>
  (impl_tac >- simp[IgnAsm `p = _`]) >>
  disch_then (strip_assume_tac o SRULE []) >>
  asm "tail_intro" (qspec_then `z` mp_tac) >>
  (impl_tac >-
    ((conj_tac >- first_assum ACCEPT_TAC) >>
     (conj_tac >- (Q_TAC (TRANS_TAC LESS_TRANS) `rank a` >>
                   conj_tac >> first_assum ACCEPT_TAC)) >>
     (conj_tac >- simp[]) >> first_assum ACCEPT_TAC)) >>
  disch_then (strip_assume_tac o SRULE []) >>
  qexistsl [`j`,`a`,`z`] >> simp[IgnAsm `p = _`] >>
  rpt conj_tac >> gen_tac >> DISCH_TAC >>
  first_assum (fn th => MATCH_MP_TAC th >> first_assum ACCEPT_TAC)
QED
