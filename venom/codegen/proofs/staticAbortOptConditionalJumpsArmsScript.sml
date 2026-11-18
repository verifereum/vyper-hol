Theory staticAbortOptConditionalJumpsArms
Ancestors
  staticAbortOptConditionalJumpsSource staticAbortRoleStep staticAbortStraight
  asmOptimizer asmSplice asmIR asmSem stackOpAsmSim finite_map pred_set list
  arithmetic words

(* The only tag that may be erased is the condition before the c-push.
   A demanded push successor slot cannot read it: the slot would be 1. *)
Theorem visit_erase_inherit[local]:
  !weak. weak = (\(u:num#num) (k:num). if u = v /\ k = 0 then NONE
                   else (tag u k : (string#num)option)) ==>
  (!k l i. tag y k = SOME(l,i) ==>
      k < hj /\ (fresh k = SOME(l,i) \/
        ?a. src k = SOME a /\ a < hi /\ tag u a = SOME(l,i))) /\
  (u = v ==> tag y 1 = NONE /\ src 0 = NONE /\
             (!k. src k = SOME 0 ==> k = 1)) ==>
  !k l i. weak y k = SOME(l,i) ==>
      k < hj /\ (fresh k = SOME(l,i) \/
        ?a. src k = SOME a /\ a < hi /\ weak u a = SOME(l,i))
Proof
  CONV_TAC (TOP_DEPTH_CONV (HO_REWR_CONV UNWIND_FORALL_THM2)) >> BETA_TAC >> strip_tac >> rpt gen_tac >> DISCH_TAC >>
  `tag y k = SOME(l,i)` by (Cases_on `y = v /\ k = 0` >> gvs[]) >>
  simp[] >> metis_tac[optionTheory.NOT_SOME_NONE]
QED

Theorem conditional_jump_whole_visit_rows:
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
  !TagFlow. TagFlow = (\tag u y hi hj src fresh.
    !k l origin. tag y k = SOME(l,origin) ==>
      k < hj /\ (fresh k = SOME(l,origin) \/
      ?a. src k = SOME a /\ a < hi /\ tag u a = SOME(l,origin))) ==>
  !Flow. Flow =
    (\p pc height tag boolean (u:num#num) (y:num#num).
    !hi. hi = height u ==>
    !hj. hj = height y ==>
    !ins. ins = EL (pc u) p ==>
    !inherit. inherit =
      (\(src:num -> num option)
        (fresh:num -> (string#num)option) (bnew:num -> bool).
        TagFlow tag u y hi hj src fresh /\
        (!k. boolean y k ==> k < hj /\
           (bnew k \/ ?a. src k = SOME a /\ a < hi /\ boolean u a))) ==>
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
    !target. target = (\u y.
      ?l origin off. tag u 0 = SOME(l,origin) /\
        FLOOKUP (SND(compute_label_offsets p)) l = SOME off /\
        off < dimword(:256) /\
        FLOOKUP (build_offset_to_pc p) off = SOME(pc y)) ==>
      FINITE V /\ X SUBSET V /\
      (!u. u IN V ==> ?t. S u t) /\
      (!u. u IN V DIFF X ==> pc u < LENGTH p) /\
      (!u y. edge u y ==>
         u IN V DIFF X /\ y IN V /\ rank y < rank u /\
         Flow p pc height tag boolean u y /\
         (if EL (pc u) p = AsmOp "JUMP" then target u y
          else if EL (pc u) p = AsmOp "JUMPI"
               then pc y = pc u+1 \/ target u y
          else pc y = pc u+1)) /\
      (!u t. u IN V DIFF X /\ S u t ==>
         (?s. (asm_steps (SND(compute_label_offsets p)) (build_offset_to_pc p)
                      p 1 t = AsmRevert s \/
                asm_steps (SND(compute_label_offsets p)) (build_offset_to_pc p)
                      p 1 t = AsmFault s) /\ s.as_requests=req) \/
         (?y s. edge u y /\
            asm_steps (SND(compute_label_offsets p)) (build_offset_to_pc p)
              p 1 t = AsmOK s /\ S y s))) ==>
  !b. b = LENGTH pre ==>
  !r. r = splice_pc b 4 3 ==>
  !H. H = height v ==>
  !C. C = (\s l d. ?off. FLOOKUP (SND(compute_label_offsets s)) l = SOME off /\
                         off < dimword(:256) /\
                         FLOOKUP (build_offset_to_pc s) off = SOME d) ==>
  !Tail. Tail = (\z. z IN V /\ rank z < rank v /\ H = height z + 1 /\
    (!k l i. tag z k = SOME(l,i) ==> tag v (k+1) = SOME(l,i)) /\
    (!k. boolean z k ==> boolean v (k+1))) ==>
  p = pre ++ [AsmPushLabel c; AsmOp "JUMPI"; AsmPushLabel x;
              AsmOp "JUMP"; AsmLabel c] ++ tail /\
  q = pre ++ [AsmOp "ISZERO"; AsmPushLabel x; AsmOp "JUMPI"; AsmLabel c] ++ tail /\
  asm_static_wf p /\ Open p cc req V {} rank pc height need tag boolean edge /\
  v IN V /\ pc v = b /\ IS_SOME (FLOOKUP (SND(compute_label_offsets p)) c) /\
  (?j. edge v j /\ pc j = b+1) /\ (!j. edge v j ==> tag j 1 = NONE) /\
  (!u k. u IN V /\ boolean u k ==> tag u k = NONE) ==>
  0 < H /\
  ?j0 h i z0 j1 a z1.
    edge v j0 /\ pc j0=b+1 /\ edge j0 h /\ pc h=b+2 /\
    edge h i /\ pc i=b+3 /\ tag i 0=SOME(x,b+2) /\ edge i z0 /\ C p x (pc z0) /\
    edge v j1 /\ pc j1=b+1 /\ tag j1 0=SOME(c,b) /\ edge j1 a /\ pc a=b+4 /\
    edge a z1 /\ pc z1=b+5 /\ Tail z0 /\ Tail z1 /\
    !rho:string->num->num.
      !raw. raw = (\k. case tag z0 k of NONE => tag z1 k | SOME u => SOME u) ==>
      !translate. translate = OPTION_MAP (\(l,i). (l,rho l i)) ==>
      !U. U = (\k. translate (raw k)) ==>
      !UB. UB = (\k. boolean z0 k \/ boolean z1 k) ==>
      !I. I = (0:num,0:num) ==>
      !P. P = (1:num,0:num) ==>
      !J. J = (2:num,0:num) ==>
      !L. L = (3:num,0:num) ==>
      !E0. E0 = (4:num,0:num) ==>
      !E1. E1 = (5:num,0:num) ==>
      !W. W = {I;P;J;L;E0;E1} ==>
      !pcq. pcq = (\u. if u=I then b else if u=P then b+1 else
            if u=J then b+2 else if u=L then b+3 else
            if u=E0 then r (pc z0) else r (pc z1)) ==>
      !hq. hq = (\u. if u=I \/ u=P then H else if u=J then H+1 else H-1) ==>
      !rq. rq = (\u. if u=I then 4*rank v+3 else if u=P then 4*rank v+2 else
            if u=J then 4*rank v+1 else if u=L then 4*rank v else
            if u=E0 then 4*rank z0+3 else 4*rank z1+3) ==>
      !tq. tq = (\u k. if u=I \/ u=P then (if k=0 then NONE else U (k-1)) else
            if u=J then (if k=0 then SOME(x,b+1) else
                         if k=1 then NONE else U (k-2)) else
            if u=E0 then translate (tag z0 k) else translate (tag z1 k)) ==>
      !bq. bq = (\u k. if u=I then k<>0 /\ UB (k-1) else
            if u=P then k=0 \/ UB (k-1) else
            if u=J then k=1 \/ (2<=k /\ UB (k-2)) else
            if u=E0 then boolean z0 k else boolean z1 k) ==>
      !edges. edges = (\u y. (u=I /\ y=P) \/ (u=P /\ y=J) \/
            (u=J /\ y=E0) \/ (u=J /\ y=L) \/ (u=L /\ y=E1)) ==>
      (!k t s. tag z0 k=SOME t /\ tag z1 k=SOME s ==> t=s) /\
      (!k l i. raw k=SOME(l,i) ==> k<H-1 /\
        translate (tag v (k+1))=SOME(l,rho l i)) /\
      (!k. UB k ==> k<H-1 /\ boolean v (k+1) /\ U k=NONE) /\
      (!u. u IN W ==> (((u=E0 /\ need z0) \/ (u=E1 /\ need z1)) ==> cc.cc_static) /\
         (!k. bq u k ==> k<hq u /\ tq u k=NONE) /\
         (!k l i. tq u k=SOME(l,i) ==> k<hq u)) /\
      (!u. u IN {I;P;J;L} ==> pcq u < LENGTH q) /\
      EL (pcq I) q = AsmOp "ISZERO" /\ static_abort_straight "ISZERO" 1 /\
      EL (pcq P) q = AsmPushLabel x /\ EL (pcq J) q = AsmOp "JUMPI" /\
      EL (pcq L) q = AsmLabel c /\
      (!u y. edges u y ==> rq y < rq u /\ Flow q pcq hq tq bq u y) /\
      (C q x (r (pc z0)) /\
       (!z k l i. (z=z0 \/ z=z1) /\ tag z k=SOME(l,i) ==>
          rho l i < LENGTH q /\
          (EL (rho l i) q=AsmPushLabel l \/ EL (rho l i) q=AsmPushOfst l 0) /\
          ?d. C q l d) ==>
       (!u k l i. u IN W /\ tq u k=SOME(l,i) ==>
          i < LENGTH q /\
          (EL i q=AsmPushLabel l \/ EL i q=AsmPushOfst l 0) /\ ?d. C q l d) /\
       IS_SOME (FLOOKUP (SND(compute_label_offsets q)) x) /\
       edges I P /\ pcq P = pcq I+1 /\ edges P J /\ pcq J = pcq P+1 /\
       edges J E0 /\ tq J 0=SOME(x,pcq P) /\ C q x (pcq E0) /\
       edges J L /\ pcq L = pcq J+1 /\
       edges L E1 /\ pcq E1 = pcq L+1 /\ pcq E1 = b+4 /\
       (!t w stk. t.as_stack=w::stk ==>
         asm_step (SND(compute_label_offsets q)) (build_offset_to_pc q)
           (EL (pcq I) q) t =
         AsmOK (asm_next (t with as_stack := (if w=0w then 1w else 0w)::stk))) /\
       (!off w stk t.
          FLOOKUP (SND(compute_label_offsets q)) x=SOME off /\
          t.as_pc=pcq J /\ t.as_stack=n2w off::(if w=0w then 1w else 0w)::stk ==>
          asm_step (SND(compute_label_offsets q)) (build_offset_to_pc q)
            (EL (pcq J) q) t =
          AsmOK (t with <|as_pc := if w=0w then pcq E0 else pcq L;
                           as_stack := stk|>)))
Proof
  map_every (fn name => qx_gen_tac name >>
    disch_then (assume_tac o CONV_RULE
      (RAND_CONV (REDEPTH_CONV (HO_REWR_CONV UNWIND_FORALL_THM2)) THENC
       REWR_CONV (GSYM markerTheory.Abbrev_def))))
    [`Shape`, `TagFlow`, `Flow`, `Open`] >>
  CONV_TAC (TOP_DEPTH_CONV (HO_REWR_CONV UNWIND_FORALL_THM2)) >>
  strip_tac >> BETA_TAC >>
  qpat_x_assum `p = _` (mk_asm "p_window") >>
  qpat_x_assum `q = _` (mk_asm "q_window") >>
  `EL (pc v) p = AsmPushLabel c` by
    (asm "p_window" SUBST1_TAC >>
     once_rewrite_tac [GSYM APPEND_ASSOC] >> simp[EL_APPEND_EQN]) >>
  qabbrev_tac `weak = \u k. if u = v /\ k = 0 then NONE else tag u k` >>
  qpat_assum `Abbrev (Open = _)` (fn eq =>
    qpat_assum `Open p cc req V {} rank pc height need tag boolean edge`
      (mp_tac o REWRITE_RULE [REWRITE_RULE [markerTheory.Abbrev_def] eq])) >>
  simp[NoAsms, LET_THM, DIFF_EMPTY] >> strip_tac >>
  `!u t. Shape p cc req pc height need tag boolean u t ==>
         Shape p cc req pc height need weak boolean u t` by
    (rpt gen_tac >> simp[NoAsms, Abbr `Shape`, Abbr `weak`] >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
  pop_assum $ mk_asm "weaken" >>
  `Open p cc req V {} rank pc height need weak boolean edge` by
    (simp[Abbr `Open`, LET_THM, DIFF_EMPTY] >>
     conj_tac >- (asm "weaken" mp_tac >> metis_tac[]) >>
     conj_asm1_tac >- suspend "weak_edges" >> suspend "weak_step") >>
  suspend "select_paths"
QED

Resume conditional_jump_whole_visit_rows[weak_edges]:
  map_every qx_gen_tac [`u`,`y`] >> DISCH_TAC >>
  qpat_assum `!u y. edge u y ==> _` (qspecl_then [`u`,`y`] mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  conj_tac >- first_assum ACCEPT_TAC >> conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (Cases_on `u = v`
      >- (qpat_x_assum `u = v` SUBST_ALL_TAC >>
          `TagFlow tag v y (height v) (height y)
              (\k. if k=0 then NONE else SOME(k-1))
              (\k. if k=0 then SOME(c,pc v) else NONE) ==>
           TagFlow weak v y (height v) (height y)
              (\k. if k=0 then NONE else SOME(k-1))
              (\k. if k=0 then SOME(c,pc v) else NONE)` by
            (qpat_assum `!j. edge v j ==> _` (qspec_then `y` mp_tac) >>
             (impl_tac >- first_assum ACCEPT_TAC) >> DISCH_TAC >>
             mp_tac (Q.INST [`u` |-> `v`, `src` |-> `\k. if k=0 then NONE else SOME(k-1)`,
                             `fresh` |-> `\k. if k=0 then SOME(c,pc v) else NONE`,
                             `hi` |-> `height v`, `hj` |-> `height y`]
                      visit_erase_inherit) >>
             CONV_TAC (TOP_DEPTH_CONV (HO_REWR_CONV UNWIND_FORALL_THM2)) >>
             simp[Abbr `TagFlow`, Abbr `weak`]) >>
          qpat_assum `Flow p pc height tag boolean v y` mp_tac >>
          qpat_assum `Abbrev (Flow = _)` (fn eq =>
            rewrite_tac [REWRITE_RULE [markerTheory.Abbrev_def] eq]) >>
          qpat_assum `EL (pc v) p = AsmPushLabel c` (fn fetch =>
            simp_tac std_ss [LET_THM, fetch, asmIRTheory.asm_inst_case_def]) >>
          strip_tac >>
          qpat_assum `height y = height v + 1` (rewrite_tac o single o SYM) >>
          conj_tac
          >- (qpat_assum `TagFlow tag v y _ _ _ _ ==> _` irule >>
              first_assum ACCEPT_TAC) >>
          qx_gen_tac `k` >> DISCH_TAC >>
          qpat_assum `!k. boolean y k ==> _` (qspec_then `k` mp_tac) >> simp[]) >>
      `!hi hj src fresh. TagFlow tag u y hi hj src fresh ==>
                        TagFlow weak u y hi hj src fresh` by
        (simp[Abbr `TagFlow`, Abbr `weak`, NoAsms] >>
         qpat_assum `u <> v` mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >>
         metis_tac[optionTheory.NOT_SOME_NONE]) >>
      qpat_assum `!hi hj src fresh. TagFlow tag u y hi hj src fresh ==> _`
        (fn mono => qpat_assum `Abbrev (Flow = _)` (fn def =>
          qpat_assum `Flow p pc height tag boolean u y` (fn old =>
            let
              val row_ss = [REWRITE_RULE [markerTheory.Abbrev_def] def,
                            LET_THM, asmIRTheory.asm_inst_case_def,
                            optionTheory.option_case_def]
            in
              POP_ASSUM_LIST (K ALL_TAC) >>
              Cases_on `EL (pc u) p` >> ASM_SIMP_TAC std_ss row_ss >>
              rpt (CASE_TAC >> ASM_SIMP_TAC std_ss row_ss) >>
              ASSUM_LIST (fn cases => mp_tac old >>
                CONV_TAC (LAND_CONV (SIMP_CONV std_ss (cases @ row_ss)))) >>
              strip_tac >> rpt conj_tac >>
              (first_assum ACCEPT_TAC ORELSE
               (irule mono >> first_assum ACCEPT_TAC))
            end)))) >>
  qpat_assum `if EL (pc u) p = _ then _ else _` mp_tac >>
  Cases_on `u=v`
  >- (qpat_x_assum `u=v` SUBST_ALL_TAC >>
      qpat_assum `EL (pc v) p = AsmPushLabel c` (fn fetch =>
        simp[NoAsms, fetch])) >>
  simp[Abbr `weak`]
QED

Resume conditional_jump_whole_visit_rows[weak_step]:
  map_every qx_gen_tac [`u`,`t`] >> strip_tac >>
  reverse (Cases_on `u = v`)
  >- (`Shape p cc req pc height need tag boolean u t` by
        (qpat_assum `Shape p cc req pc height need weak boolean u t` (fn shaped =>
         qpat_assum `Abbrev (Shape = _)` (fn sd =>
           qpat_assum `Abbrev (weak = _)` (fn wd =>
             qpat_assum `u <> v` (fn ne =>
               let val rules = ne :: map (REWRITE_RULE [markerTheory.Abbrev_def]) [sd,wd]
               in simp_tac std_ss rules >> ACCEPT_TAC (SIMP_RULE std_ss rules shaped) end))))) >>
      qpat_assum `!u t. u IN V /\ Shape p cc req pc height need tag boolean u t ==> _`
        (qspecl_then [`u`,`t`] mp_tac) >>
      (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
      disch_then (DISJ_CASES_THEN2 (fn boom => disj1_tac >> ACCEPT_TAC boom)
        (qx_choose_then `y` (qx_choose_then `s` strip_assume_tac))) >>
      disj2_tac >> qexistsl [`y`,`s`] >> asm_rewrite_tac[] >>
      asm "weaken" irule >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `u = v` SUBST_ALL_TAC >>
  qpat_assum `Abbrev (Shape = _)` (fn def =>
    pure_rewrite_tac [REWRITE_RULE [markerTheory.Abbrev_def] def]) >> BETA_TAC >>
  match_mp_tac (CONV_RULE (REDEPTH_CONV (FIRST_CONV [REWR_CONV LET_THM, BETA_CONV]))
    (Q.INST [`x` |-> `v`, `tag` |-> `weak`] pending_role_step)) >>
  conj_tac >- (qpat_assum `!u. u IN V ==> pc u < LENGTH p` irule >>
               first_assum ACCEPT_TAC) >>
  conj_tac
  >- (qpat_assum `Abbrev (Shape = _)` (fn def =>
      qpat_assum `Shape p cc req pc height need weak boolean v t`
        (ACCEPT_TAC o BETA_RULE o PURE_REWRITE_RULE
          [REWRITE_RULE [markerTheory.Abbrev_def] def]))) >>
  reverse conj_tac
  >- (qpat_assum `EL (pc v) p = AsmPushLabel c` (fn fetch =>
        simp_tac std_ss [fetch, asmIRTheory.asm_inst_case_def]) >>
      conj_tac >- first_assum ACCEPT_TAC >> qexists `j` >> asm_rewrite_tac[]) >>
  qx_gen_tac `y` >> DISCH_TAC >>
  qpat_assum `!u y. edge u y ==> _ /\ _ /\ Flow p pc height weak boolean u y /\ _`
    (qspecl_then [`v`,`y`] mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  conj_tac
  >- (qpat_assum `EL (pc v) p = AsmPushLabel c` (fn fetch =>
      qpat_assum `Abbrev (Flow = _)` (fn fd =>
      qpat_assum `Abbrev (TagFlow = _)` (fn td =>
      qpat_assum `Flow p pc height weak boolean v y` (fn row =>
        let val rules = [fetch, LET_THM, asmIRTheory.asm_inst_case_def] @
                         map (REWRITE_RULE [markerTheory.Abbrev_def]) [fd,td]
        in simp_tac std_ss rules >> ACCEPT_TAC (SIMP_RULE std_ss rules row) end))))) >>
  qpat_assum `!u. u IN V ==> ?t. Shape p cc req pc height need tag boolean u t`
    (qspec_then `y` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (qx_choose_then `ty` assume_tac) >>
  `Shape p cc req pc height need weak boolean y ty` by
    (asm "weaken" irule >> first_assum ACCEPT_TAC) >>
  qpat_assum `Abbrev (Shape = _)` (fn def =>
    qpat_assum `Shape p cc req pc height need weak boolean y ty`
      (strip_assume_tac o BETA_RULE o PURE_REWRITE_RULE
        [REWRITE_RULE [markerTheory.Abbrev_def] def])) >>
  conj_tac >- (asm_rewrite_tac[] >> (gvs[])) >>
  map_every qx_gen_tac [`k`,`l`,`origin`] >> DISCH_TAC >>
  qpat_assum `!k l origin. weak y k = SOME (l,origin) ==> _`
    (qspecl_then [`k`,`l`,`origin`] mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]
QED

Resume conditional_jump_whole_visit_rows[select_paths]:
  qpat_assum `Abbrev (Open = _)` (fn od =>
    qpat_assum `Abbrev (Flow = _)` (fn fd =>
    qpat_assum `Abbrev (TagFlow = _)` (fn td =>
    qpat_assum `Abbrev (Shape = _)` (fn sd =>
    qpat_assum `Open p cc req V {} rank pc height need weak boolean edge` (fn opn =>
      let
        val norm = CONV_RULE (REDEPTH_CONV
          (FIRST_CONV [HO_REWR_CONV UNWIND_FORALL_THM2, BETA_CONV]))
        val source = norm (Q.INST [`tag` |-> `weak`] conditional_jump_source_paths)
        val expanded = norm (PURE_REWRITE_RULE
             (map (REWRITE_RULE [markerTheory.Abbrev_def]) [od,fd,td,sd]) opn)
      in
        mp_tac source >> (impl_tac >-
          (conj_tac >- asm "p_window" ACCEPT_TAC >>
           conj_tac >- first_assum ACCEPT_TAC >>
           conj_tac >- ACCEPT_TAC expanded >> asm_rewrite_tac[]))
      end))))) >>
  disch_then (fn selected =>
    assume_tac (CONJUNCT1 selected) >> mp_tac (cj 3 selected) >> mp_tac (cj 4 selected)) >>
  `weak v 0 = NONE` by simp[Abbr `weak`] >>
  (impl_tac >- (qexists `1w:bytes32` >> simp[])) >>
  disch_then (qx_choose_then `j1` (qx_choose_then `a` (qx_choose_then `z1`
    strip_assume_tac))) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choose_then `j0` (qx_choose_then `h` (qx_choose_then `i`
    (qx_choose_then `z0` (qx_choose_then `off0` strip_assume_tac))))) >>
  `z0 <> v /\ z1 <> v /\ i <> v /\ j1 <> v` by
    (rpt conj_tac >> DISCH_THEN SUBST_ALL_TAC >> simp[]) >>
  `tag i 0 = SOME(x,LENGTH pre+2) /\ tag j1 0 = SOME(c,LENGTH pre)` by
    (qpat_assum `Abbrev (weak = _)` (fn wd =>
      conj_tac
      >- (qpat_assum `i <> v` (fn ne =>
          qpat_assum `weak i 0 = SOME _`
            (ACCEPT_TAC o SIMP_RULE std_ss
              [ne, REWRITE_RULE [markerTheory.Abbrev_def] wd]))) >>
      qpat_assum `j1 <> v` (fn ne =>
        qpat_assum `weak j1 0 = SOME _`
          (ACCEPT_TAC o SIMP_RULE std_ss
            [ne, REWRITE_RULE [markerTheory.Abbrev_def] wd])))) >>
  `!k. weak z0 k = tag z0 k` by simp[Abbr `weak`] >>
  `!k. weak z1 k = tag z1 k` by simp[Abbr `weak`] >>
  `!k. weak v (k+1) = tag v (k+1)` by simp[Abbr `weak`] >>
  qpat_assum `!k. weak v (k+1) = _` (fn shift =>
    qpat_assum `!k. weak z0 k = _` (fn unweak =>
      qpat_x_assum `!k l org. weak z0 k = SOME(l,org) ==> _`
        (assume_tac o PURE_REWRITE_RULE [unweak,shift])) >>
    qpat_assum `!k. weak z1 k = _` (fn unweak =>
      qpat_x_assum `!k l org. weak z1 k = SOME(l,org) ==> _`
        (assume_tac o PURE_REWRITE_RULE [unweak,shift]))) >>
  `!z. z IN V ==>
     (need z ==> cc.cc_static) /\
     (!k l org. tag z k = SOME(l,org) ==> k < height z) /\
     (!k. boolean z k ==> k < height z)` by
    (qx_gen_tac `z` >> DISCH_TAC >>
     qpat_assum `!u. u IN V ==> ?t. Shape p cc req pc height need tag boolean u t`
       (qspec_then `z` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     qpat_assum `Abbrev (Shape = _)` (fn sd =>
       pure_rewrite_tac [REWRITE_RULE [markerTheory.Abbrev_def] sd]) >>
     BETA_TAC >> POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl [`j0`,`h`,`i`,`z0`,`j1`,`a`,`z1`] >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  (conj_tac >- (qexists `off0` >> asm_rewrite_tac[])) >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  (conj_tac >- (asm_rewrite_tac[] >> metis_tac[])) >>
  (conj_tac >- (asm_rewrite_tac[] >> metis_tac[])) >>
  qx_gen_tac `reloc` >>
  qabbrev_tac `raw = \k. case tag z0 k of NONE => tag z1 k | SOME u => SOME u` >>
  `!k t s. tag z0 k = SOME t /\ tag z1 k = SOME s ==> t = s` by
    (rpt gen_tac >> strip_tac >> PairCases_on `t` >> PairCases_on `s` >>
     `tag v (k+1) = SOME(t0,t1)` by
       (qpat_assum `!k l org. tag z0 k = SOME(l,org) ==> _` irule >>
        first_assum ACCEPT_TAC) >>
     `tag v (k+1) = SOME(s0,s1)` by
       (qpat_assum `!k l org. tag z1 k = SOME(l,org) ==> _` irule >>
        first_assum ACCEPT_TAC) >>
     qpat_assum `tag v (k+1) = SOME(t0,t1)` (fn left =>
       qpat_assum `tag v (k+1) = SOME(s0,s1)` (fn right =>
         mp_tac left >> simp[NoAsms, right]))) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  suspend "destination"
QED

Resume conditional_jump_whole_visit_rows[destination]:
  `!k. (case tag z0 k of NONE => tag z1 k | SOME u => SOME u) = raw k` by
    simp[NoAsms, Abbr `raw`] >>
  pop_assum (pure_rewrite_tac o single) >>
  `height z0 = height v-1 /\ height z1 = height v-1` by decide_tac >>
  `!k l org. raw k = SOME(l,org) ==>
       tag z0 k = SOME(l,org) \/ tag z1 k = SOME(l,org)` by
    (rpt gen_tac >> simp[NoAsms, Abbr `raw`] >>
     Cases_on `tag z0 k` >> simp[NoAsms]) >>
  `!k l org. raw k = SOME(l,org) ==>
       tag v (k+1) = SOME(l,org)` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `!k l org. raw k = SOME(l,org) ==> _` drule >>
     disch_then DISJ_CASES_TAC
     >- (qpat_assum `!k l org. tag z0 k = SOME(l,org) ==> _` irule >>
         first_assum ACCEPT_TAC) >>
     qpat_assum `!k l org. tag z1 k = SOME(l,org) ==> _` irule >>
     first_assum ACCEPT_TAC) >>
  `!k (payload:string#num). raw k = SOME payload ==>
       tag v (k+1) = SOME payload` by
    (map_every qx_gen_tac [`k`,`payload`] >> PairCases_on `payload` >>
     first_assum MATCH_ACCEPT_TAC) >>
  `!k. boolean z0 k \/ boolean z1 k ==> boolean v (k+1)` by
    (qx_gen_tac `k` >> strip_tac >> simp[]) >>
  `!k. boolean z0 k \/ boolean z1 k ==>
       boolean v (k+1) /\ raw k = NONE` by
    (qx_gen_tac `k` >> disch_tac >>
     `boolean v (k+1)` by
       (qpat_assum `!k. boolean z0 k \/ boolean z1 k ==> boolean v (k+1)`
          (qspec_then `k` mp_tac) >> impl_tac >- first_assum ACCEPT_TAC >>
        disch_then ACCEPT_TAC) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     `tag v (k+1) = NONE` by
       (qpat_assum `!u k. u IN V /\ boolean u k ==> tag u k = NONE` irule >> simp[]) >>
     Cases_on `raw k` >- simp[NoAsms] >>
     qpat_assum `!j (payload:string#num). raw j = SOME payload ==>
                  tag v (j+1) = SOME payload` drule >>
     qpat_assum `tag v (k+1) = NONE` (fn th => simp[NoAsms,th])) >>
  conj_asm1_tac >- suspend "raw_bounds" >>
  conj_asm1_tac >- suspend "boolean_bounds" >>
  conj_asm1_tac >- suspend "metadata" >>
  conj_tac >- suspend "fetch_bounds" >>
  `EL (LENGTH pre) q = AsmOp "ISZERO" /\
   EL (LENGTH pre + 1) q = AsmPushLabel x /\
   EL (LENGTH pre + 2) q = AsmOp "JUMPI" /\
   EL (LENGTH pre + 3) q = AsmLabel c` by
    simp[NoAsms, markerLib.L "q_window", EL_APPEND_EQN] >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  `static_abort_straight "ISZERO" 1` by EVAL_TAC >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >- suspend "rank_flow" >>
  suspend "control"
QED

Resume conditional_jump_whole_visit_rows[raw_bounds]:
  map_every qx_gen_tac [`k`,`l`,`org`] >> disch_tac >>
  qpat_assum `!k l org. raw k = SOME(l,org) ==> tag v (k+1) = _`
    (drule_then assume_tac) >>
  reverse conj_tac >- (qexists `(l,org)` >> simp[]) >>
  `k+1 < height v` by
    (qpat_assum `!z. z IN V ==> (need z ==> cc.cc_static) /\ _`
      (qspec_then `v` mp_tac) >> simp[] >> strip_tac >>
     qpat_assum `!k l org. tag v k = SOME(l,org) ==> _` irule >>
     first_assum ACCEPT_TAC) >>
  decide_tac
QED

Resume conditional_jump_whole_visit_rows[boolean_bounds]:
  qx_gen_tac `k` >> disch_tac >>
  qpat_assum `!k. boolean z0 k \/ boolean z1 k ==>
                  boolean v (k+1) /\ raw k = NONE` (qspec_then `k` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  `k+1 < height v` by
    (qpat_assum `!z. z IN V ==> (need z ==> cc.cc_static) /\ _`
      (qspec_then `v` mp_tac) >> simp[] >> strip_tac >>
     qpat_assum `!k. boolean v k ==> _` irule >> first_assum ACCEPT_TAC) >>
  conj_tac >- decide_tac >> conj_tac >> first_assum ACCEPT_TAC
QED

Resume conditional_jump_whole_visit_rows[metadata]:
  `!k (a:string#num). raw k = SOME a ==> k < height v-1` by
    (map_every qx_gen_tac [`k`,`payload`] >> PairCases_on `payload` >> disch_tac >>
     qpat_assum `!k l i. raw k = SOME(l,i) ==> _ /\ _`
       (drule_then (ACCEPT_TAC o CONJUNCT1))) >>
  `!z. z IN V ==> (need z ==> cc.cc_static) /\
    (!k. boolean z k ==> k < height z /\ tag z k = NONE) /\
    (!k (payload:string#num). tag z k = SOME payload ==> k < height z)` by
    (qx_gen_tac `z` >> disch_tac >>
     qpat_assum `!z. z IN V ==> (need z ==> cc.cc_static) /\ _`
       (drule_then strip_assume_tac) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac
     >- (qx_gen_tac `k` >> disch_tac >> conj_tac >- simp[] >>
         qpat_assum `!u k. u IN V /\ boolean u k ==> tag u k = NONE` irule >> simp[]) >>
     map_every qx_gen_tac [`k`,`payload`] >> PairCases_on `payload` >>
     first_assum MATCH_ACCEPT_TAC) >>
  qpat_assum `!z. z IN V ==> (need z ==> cc.cc_static) /\
                              (!k. boolean z k ==> _ /\ _) /\ _`
    (fn th => map_every (fn z => qspec_then z mp_tac th >>
      (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac) [`z0`,`z1`]) >>
  `!k. (boolean z0 k \/ boolean z1 k) ==> k < height v-1 /\ raw k = NONE` by
    (qx_gen_tac `k` >> disch_tac >>
     qpat_assum `!k. (boolean z0 k \/ boolean z1 k) ==> _ /\ _ /\ _`
       (fn th => drule_then strip_assume_tac th) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  qx_gen_tac `u` >> disch_then (REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) >>
  simp[NoAsms] >>
  TRY (conj_tac >- first_assum ACCEPT_TAC) >>
  (conj_tac >-
    (qx_gen_tac `k` >> rpt (COND_CASES_TAC >> simp[NoAsms]) >> TRY strip_tac >>
     FIRST_PROVE
       [decide_tac,
        qpat_assum `!j. boolean z0 j ==> _ /\ _` (drule_then strip_assume_tac) >>
          conj_tac >- decide_tac >> first_assum ACCEPT_TAC,
        qpat_assum `!j. boolean z1 j ==> _ /\ _` (drule_then strip_assume_tac) >>
          conj_tac >- decide_tac >> first_assum ACCEPT_TAC,
        qpat_assum `!j. (boolean z0 j \/ boolean z1 j) ==> _ /\ raw j = NONE`
          (fn th => FIRST_PROVE
            (map (fn idx => qspec_then idx mp_tac th >>
               (impl_tac >- (first_assum ACCEPT_TAC ORELSE
                 (disj1_tac >> first_assum ACCEPT_TAC) ORELSE
                 (disj2_tac >> first_assum ACCEPT_TAC))) >> strip_tac >>
               conj_tac >- decide_tac >> first_assum ACCEPT_TAC)
             [`k-1`,`k-2`]))])) >>
  rpt gen_tac >> rpt (COND_CASES_TAC >> simp[NoAsms]) >> strip_tac >>
  FIRST_PROVE
    [decide_tac,
     qpat_assum `!j a. raw j = SOME a ==> _` (drule_then assume_tac) >> decide_tac,
     qpat_assum `!j a. tag z0 j = SOME a ==> _` (drule_then assume_tac) >> decide_tac,
     qpat_assum `!j a. tag z1 j = SOME a ==> _` (drule_then assume_tac) >> decide_tac]
QED

Resume conditional_jump_whole_visit_rows[fetch_bounds]:
  qx_gen_tac `u` >> simp[NoAsms, markerLib.L "q_window"] >>
  disch_then (REPEAT_TCL DISJ_CASES_THEN SUBST1_TAC) >>
  simp[NoAsms] >> decide_tac
QED

Resume conditional_jump_whole_visit_rows[rank_flow]:
  qmatch_goalsub_abbrev_tac `Flow q pcq _ _ _ _ _` >>
  qmatch_goalsub_abbrev_tac `Flow q pcq hq _ _ _ _` >>
  qmatch_goalsub_abbrev_tac `Flow q pcq hq tq _ _ _` >>
  qmatch_goalsub_abbrev_tac `Flow q pcq hq tq bq _ _` >>
  Q.SUBGOAL_THEN
    `EL (pcq (0,0)) q = AsmOp "ISZERO" /\ EL (pcq (1,0)) q = AsmPushLabel x /\
     EL (pcq (2,0)) q = AsmOp "JUMPI" /\ EL (pcq (3,0)) q = AsmLabel c /\
     pcq (1,0) = LENGTH pre+1` (markerLib.mk_asm "fetch")
  >- simp[NoAsms, Abbr `pcq`, markerLib.L "q_window", EL_APPEND_EQN] >>
  Q.SUBGOAL_THEN
    `hq (0,0) = height v /\ hq (1,0) = height v /\ hq (2,0) = height v+1 /\
     hq (3,0) = height v-1 /\ hq (4,0) = height v-1 /\ hq (5,0) = height v-1`
    (markerLib.mk_asm "heights")
  >- simp[NoAsms, Abbr `hq`] >>
  Q.SUBGOAL_THEN
    `ALOOKUP dup_table "ISZERO" = NONE /\ ALOOKUP swap_table "ISZERO" = NONE /\
     ALOOKUP dup_table "JUMPI" = NONE /\ ALOOKUP swap_table "JUMPI" = NONE /\
     asm_op_arity "ISZERO" = 1 /\ asm_op_arity "JUMPI" = 2 /\
     asm_returns_zero_or_one (AsmOp "ISZERO")` (markerLib.mk_asm "ops")
  >- EVAL_TAC >>
  Q.SUBGOAL_THEN
    `height v + 1 - height v = 1 /\ height v - 1 + 2 - (height v + 1) = 0`
    (markerLib.mk_asm "deltas")
  >- decide_tac >>
  `!u. u=(0,0) \/ u=(1,0) \/ u=(2,0) \/ u=(3,0) \/ u=(4,0) \/ u=(5,0) ==>
      (!k l i. tq u k=SOME(l,i) ==> k<hq u) /\ (!k. bq u k ==> k<hq u)` by
    (gen_tac >> disch_tac >>
     qpat_assum `Abbrev (tq = _)` (fn td => qpat_assum `Abbrev (bq = _)` (fn bd =>
       qpat_assum `Abbrev (hq = _)` (fn hd =>
         pure_rewrite_tac (map (REWRITE_RULE [markerTheory.Abbrev_def]) [td,bd,hd])))) >>
     BETA_TAC >>
     qpat_assum `!u. _ ==> (_ ==> cc.cc_static) /\ _` (qspec_then `u` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >>
     disch_then (fn th => assume_tac (cj 2 th) >> assume_tac (cj 3 th)) >>
     conj_tac >- first_assum ACCEPT_TAC >> rpt strip_tac >>
     first_x_assum (drule_then (ACCEPT_TAC o CONJUNCT1))) >>
  `!k a. tag z0 k = SOME a \/ tag z1 k = SOME a ==> raw k = SOME a` by
    (rpt gen_tac >> Cases_on `tag z0 k` >> simp[NoAsms, Abbr `raw`] >>
     qpat_assum `!k t s. tag z0 k = SOME t /\ tag z1 k = SOME s ==> t=s`
       (qspec_then `k` mp_tac) >>
     pop_assum (fn e => simp[NoAsms,e]) >> metis_tac[]) >>
  `!k a. OPTION_MAP (\(l,i). (l,reloc l i)) (tag z0 k) = SOME a \/
         OPTION_MAP (\(l,i). (l,reloc l i)) (tag z1 k) = SOME a ==>
         OPTION_MAP (\(l,i). (l,reloc l i)) (raw k) = SOME a` by
    (simp[NoAsms] >> qpat_assum `!k a. tag z0 k = SOME a \/ _ ==> _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
  Q.SUBGOAL_THEN
    `!t u. LENGTH t.as_stack = height v /\
       asm_step (SND (compute_label_offsets q)) (build_offset_to_pc q)
         (AsmOp "ISZERO") t = AsmOK u ==>
       EL 0 u.as_stack = 0w \/ EL 0 u.as_stack = 1w`
    (markerLib.mk_asm "iszero_bit")
  >- (POP_ASSUM_LIST (K ALL_TAC) >> rpt gen_tac >>
      namedCases_on `t.as_stack` ["", "w stk"] >>
      simp[asm_step_iszero, asm_unop_def, asm_next_def] >>
      Cases_on `w = (0w:bytes32)` >> simp[] >> strip_tac >> gvs[]) >>
  rpt gen_tac >> disch_then (REPEAT_TCL DISJ_CASES_THEN (CONJUNCTS_THEN SUBST1_TAC)) >>
  (conj_tac >- (simp[NoAsms] >> decide_tac)) >>
  goal_term (fn g =>
    qpat_assum `!u. _ ==> (!k l i. tq u k = _ ==> _) /\ _`
      (mp_tac o SPEC (rand g))) >>
  (impl_tac >- simp[NoAsms]) >>
  disch_then (strip_assume_tac o SIMP_RULE std_ss [markerLib.L "heights"]) >>
  qpat_assum `Abbrev (Flow = _)` (fn fd =>
    pure_rewrite_tac[REWRITE_RULE[markerTheory.Abbrev_def] fd]) >>
  simp_tac std_ss [LET_THM, asmIRTheory.asm_inst_case_def,
    markerLib.L "fetch", markerLib.L "heights", markerLib.L "ops", markerLib.L "deltas"] >>
  qpat_assum `Abbrev (TagFlow = _)` (fn fd =>
    pure_rewrite_tac[REWRITE_RULE[markerTheory.Abbrev_def] fd]) >> BETA_TAC >>
  qpat_assum `!k l i. tq _ k = SOME(l,i) ==> _` (fn tag_bound =>
    qpat_assum `!k. bq _ k ==> _` (fn bit_bound =>
      simp[NoAsms, tag_bound, bit_bound, markerLib.L "iszero_bit"])) >>
  simp[NoAsms, Abbr `tq`, Abbr `bq`, markerLib.L "fetch", Excl "OPTION_MAP_EQ_SOME"] >>
  qpat_assum `0 < height v` (fn pos =>
    qpat_assum `!k l i. raw k = SOME(l,i) ==> _ /\ _` (fn raw_bound =>
    qpat_assum `!k. (boolean z0 k \/ boolean z1 k) ==> _ /\ _ /\ _` (fn boolean_bound =>
    qpat_assum `!k a. OPTION_MAP _ (tag z0 k) = SOME a \/ _ ==> _` (fn port =>
    qpat_assum `height v = height z0 + 1` (fn h0 =>
    qpat_assum `height v = height z1 + 1` (fn h1 =>
      asm "iszero_bit" (fn bit =>
        POP_ASSUM_LIST (K ALL_TAC) >>
        map_every assume_tac [pos, raw_bound, boolean_bound, port, h0, h1, bit]))))))) >>
  `!k a. OPTION_MAP (\(l,i). (l,reloc l i)) (raw k) = SOME a ==>
         k < height v - 1` by
    (simp[NoAsms, optionTheory.OPTION_MAP_EQ_SOME] >> rpt strip_tac >>
     rename1 `raw k = SOME payload` >> PairCases_on `payload` >>
     qpat_assum `!k l i. raw k = SOME(l,i) ==> _` (drule_then (ACCEPT_TAC o CONJUNCT1))) >>
  rpt (conj_tac >- decide_tac)
  >- (conj_tac
      >- (rpt strip_tac >>
          qpat_assum `!k a. OPTION_MAP _ (raw k) = SOME a ==> _` (drule_then assume_tac) >>
          decide_tac) >>
      gen_tac >> Cases_on `k=0`
      >- (qpat_assum `!t u. _ /\ asm_step _ _ (AsmOp "ISZERO") t = AsmOK u ==> _` mp_tac >> simp[]) >>
      simp[] >> disch_tac >>
      qpat_assum `!k. boolean z0 k \/ boolean z1 k ==> _` (drule_then strip_assume_tac) >> decide_tac)
  >- (conj_tac
      >- (rpt gen_tac >> Cases_on `k=0` >> simp[Excl "OPTION_MAP_EQ_SOME"] >>
          Cases_on `k=1` >> simp[Excl "OPTION_MAP_EQ_SOME"] >>
          disch_tac >>
          qpat_assum `!k a. OPTION_MAP _ (raw k) = SOME a ==> _` (drule_then assume_tac) >>
          simp[] >> decide_tac) >>
      gen_tac >> Cases_on `k=1` >> simp[] >> strip_tac >>
      qpat_assum `!k. boolean z0 k \/ boolean z1 k ==> _` (qspec_then `k-2` mp_tac) >>
      (impl_tac >- simp[]) >> strip_tac >> decide_tac) >>
  (conj_tac
   >- (rpt gen_tac >> disch_tac >>
       `OPTION_MAP (\(l,i). (l,reloc l i)) (raw k) = SOME(l,origin)` by
         (qpat_assum `!k a. OPTION_MAP _ (tag z0 k) = SOME a \/ _ ==> _` irule >>
          simp[Excl "OPTION_MAP_EQ_SOME"]) >>
       qpat_assum `!k a. OPTION_MAP _ (raw k) = SOME a ==> _` (drule_then assume_tac) >>
       rpt (conj_tac >- decide_tac) >> (first_assum ACCEPT_TAC ORELSE decide_tac)) >>
   gen_tac >> disch_tac >>
   qpat_assum `!k. boolean z0 k \/ boolean z1 k ==> _` (qspec_then `k` mp_tac) >>
   (impl_tac >- simp[]) >> strip_tac >> decide_tac)
QED

Resume conditional_jump_whole_visit_rows[control]:
  strip_tac >>
  Q.SUBGOAL_THEN
    `EL (LENGTH pre) q = AsmOp "ISZERO" /\
     EL (LENGTH pre+1) q = AsmPushLabel x /\ LENGTH pre+1 < LENGTH q /\
     EL (LENGTH pre+2) q = AsmOp "JUMPI"` (mk_asm "control_fetch")
  >- (simp[NoAsms, markerLib.L "q_window", EL_APPEND_EQN] >> decide_tac) >>
  reverse conj_tac
  >- (conj_tac
      >- (qpat_assum `FLOOKUP (SND (compute_label_offsets q)) x = SOME _`
            (fn th => simp[NoAsms,th])) >>
      `splice_pc (LENGTH pre) 4 3 (pc z1) = LENGTH pre+4` by
        (qpat_assum `pc z1 = LENGTH pre+5` (fn th => simp[NoAsms,th,splice_pc_def])) >>
      ntac 2 (conj_tac >- first_assum ACCEPT_TAC) >>
      conj_tac
      >- (asm "control_fetch" (fn th => simp[NoAsms,th,asm_step_iszero]) >>
          POP_ASSUM_LIST (K ALL_TAC) >> rpt gen_tac >> disch_tac >>
          Cases_on `w = (0w:bytes32)` >> simp[asm_unop_def]) >>
      asm "control_fetch" (fn th => simp[NoAsms,th,asm_step_jumpi]) >>
      qpat_assum `FLOOKUP (SND (compute_label_offsets q)) x = SOME off`
        (fn label => qpat_assum `off < dimword(:256)` (fn bound =>
          qpat_assum `FLOOKUP (build_offset_to_pc q) off = SOME _` (fn dest =>
            POP_ASSUM_LIST (K ALL_TAC) >> map_every assume_tac [label,bound,dest]))) >>
      rpt gen_tac >> strip_tac >> gvs[] >>
      Cases_on `w = 0w` >>
      simp[asm_jumpi_def, asm_next_def, w2n_n2w_compute]) >>
  qabbrev_tac `valid = \l i. i < LENGTH q /\
    (EL i q = AsmPushLabel l \/ EL i q = AsmPushOfst l 0) /\
    ?d off. FLOOKUP (SND (compute_label_offsets q)) l = SOME off /\
            off < dimword(:256) /\ FLOOKUP (build_offset_to_pc q) off = SOME d` >>
  `valid x (LENGTH pre+1)` by
    (asm "control_fetch" (fn th => simp[Abbr `valid`, th]) >> metis_tac[]) >>
  `!z k l i. (z=z0 \/ z=z1) /\
       OPTION_MAP (\(l,i). (l,reloc l i)) (tag z k) = SOME(l,i) ==> valid l i` by
    (qpat_assum `!z k l i. (z=z0 \/ z=z1) /\ tag z k = SOME(l,i) ==> _`
       (fn layout => qpat_assum `Abbrev (valid = _)` (fn vdef =>
         POP_ASSUM_LIST (K ALL_TAC) >> map_every assume_tac [layout,vdef])) >>
     simp[optionTheory.OPTION_MAP_EQ_SOME] >> rpt strip_tac >>
     rename1 `tag _ k = SOME payload` >> PairCases_on `payload` >>
     gvs[Abbr `valid`] >> metis_tac[]) >>
  `!k l i. OPTION_MAP (\(l,i). (l,reloc l i)) (raw k) = SOME(l,i) ==> valid l i` by
    (qpat_assum `!z k l i. _ /\ OPTION_MAP _ (tag z k) = SOME(l,i) ==> valid l i`
       (fn layout => qpat_assum `Abbrev (raw = _)` (fn rdef =>
         POP_ASSUM_LIST (K ALL_TAC) >> map_every assume_tac [layout,rdef])) >>
     rpt gen_tac >> disch_tac >>
     `OPTION_MAP (\(l,i). (l,reloc l i)) (tag z0 k) = SOME(l,i) \/
      OPTION_MAP (\(l,i). (l,reloc l i)) (tag z1 k) = SOME(l,i)` by
       (Cases_on `tag z0 k` >> gvs[Abbr `raw`, Excl "OPTION_MAP_EQ_SOME"]) >>
     metis_tac[]) >>
  map_every qx_gen_tac [`row`,`slot`,`lab`,`origin`] >> disch_tac >>
  `valid lab origin` suffices_by simp[NoAsms, Abbr `valid`] >>
  qpat_assum `!k l i. OPTION_MAP _ (raw k) = SOME(l,i) ==> valid l i` (fn from_raw =>
    qpat_assum `!z k l i. _ /\ OPTION_MAP _ (tag z k) = SOME(l,i) ==> valid l i` (fn from_port =>
      qpat_assum `valid x (LENGTH pre+1)` (fn fresh =>
        pop_assum (fn row => POP_ASSUM_LIST (K ALL_TAC) >>
          map_every assume_tac [from_raw,from_port,fresh] >>
          strip_assume_tac row)))) >>
  gvs[Excl "OPTION_MAP_EQ_SOME"] >>
  Cases_on `slot = 0` >> Cases_on `slot = 1` >>
  gvs[Excl "OPTION_MAP_EQ_SOME"] >>
  FIRST [first_assum ACCEPT_TAC,
    qpat_assum `!k l i. OPTION_MAP _ (raw k) = SOME(l,i) ==> _`
      (drule_then ACCEPT_TAC),
    qpat_assum `!z k l i. _ /\ OPTION_MAP _ (tag z k) = SOME(l,i) ==> _`
      (drule_at (Pat `OPTION_MAP _ _ = SOME _`)) >> simp[]]
QED

Finalise conditional_jump_whole_visit_rows
