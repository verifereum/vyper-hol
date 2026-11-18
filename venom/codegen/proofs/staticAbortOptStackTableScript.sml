(* Reindex whole stack-rewrite visits without identifying occurrences at a PC. *)
Theory staticAbortOptStackTable
Ancestors
  asmSplice asmIR asmSem asmOptimizer staticAbortStraight
  pred_set arithmetic pair list words finite_map alist

(* Keep the lexical interfaces abstract until their projections are needed. *)
fun let_vars names = map_every (fn name =>
  CONV_TAC (REWR_CONV combinTheory.LET_FORALL_ELIM THENC
    SIMP_CONV bool_ss [combinTheory.S_DEF, combinTheory.o_THM, combinTheory.C_DEF]) >>
  qx_gen_tac name >> disch_tac) names;

(* Prefixes of a path witness also witness membership in its rooted restriction. *)
Theorem stack_restrict_paths[local]:
  !(A:'a set) (E:'a->'a->bool) e.
  let reach = \x. ?n (path:num->'a). path 0=e /\ path n=x /\
                      !i. i<n ==> E (path i) (path(SUC i)) in
  let V = {x | x IN A /\ reach x} in
  let R = \x y. x IN V /\ E x y in
  FINITE A /\ e IN A /\ (!x y. E x y ==> x IN A /\ y IN A) ==>
  ?W T. FINITE W /\ e IN W /\ W SUBSET A /\
  (!x y. T x y ==> x IN W /\ y IN W) /\
  (!x. x IN W ==> ?n path. path 0=e /\ path n=x /\
                          !i. i<n ==> T (path i) (path(SUC i))) /\
  (!x y. T x y <=> x IN W /\ E x y)
Proof
  rpt gen_tac >> let_vars [`reach`,`V`,`R`] >>
  strip_tac >>
  `e IN V` by (simp[Abbr `V`, Abbr `reach`] >> qexistsl [`0`,`\i. e`] >> simp[]) >>
  `V SUBSET A` by simp[SUBSET_DEF, Abbr `V`] >>
  qexistsl [`V`,`R`] >>
  conj_tac >- metis_tac[SUBSET_FINITE] >>
  simp[Abbr `R`] >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> simp[Abbr `V`] >>
      `y IN A /\ reach x` by (fs[] >> metis_tac[]) >>
      simp[] >> qpat_x_assum `reach x` mp_tac >> simp[Abbr `reach`] >>
      disch_then (qx_choose_then `n` (qx_choose_then `path` strip_assume_tac)) >>
      qexistsl [`SUC n`, `\i. if i <= n then path i else y`] >>
      simp[] >> qx_gen_tac `i` >> disch_tac >> Cases_on `i < n`
      >- (`SUC i <= n` by decide_tac >> simp[]) >>
      `i = n` by decide_tac >> simp[]) >>
  qx_gen_tac `x` >> simp[Abbr `V`] >> strip_tac >>
  qpat_x_assum `reach x` mp_tac >> simp[Abbr `reach`] >>
  disch_then (qx_choose_then `n` (qx_choose_then `path` strip_assume_tac)) >>
  qexistsl [`n`, `path`] >> simp[] >> qx_gen_tac `i` >> disch_tac >>
  `E (path i) (path (SUC i))` by metis_tac[] >> simp[] >>
  `path i IN A` by metis_tac[] >> simp[] >>
  qexistsl [`i`, `path`] >> simp[] >> rpt strip_tac >>
  `i' < n` by decide_tac >> metis_tac[]
QED

(* Available vertices have one of three disjoint encodings. Only the image
   of a head (not its old PC) is used as the target of a lifted edge. *)
Theorem stack_port_incidence[local]:
  !(keep:(num#num)set) D old z n init j start copy phase first image next e.
  Abbrev (copy = (\v. (SUC (pair_to_num v),0:num))) ==>
  Abbrev (phase = (\v i. (SUC (pair_to_num v),SUC i))) ==>
  Abbrev (first = (0:num,0:num)) ==>
  Abbrev (image = (\v. if v IN keep then copy v
                       else if n=0 then copy (z v) else phase v 0)) ==>
  Abbrev (next = (\v i. if SUC i = n then copy (z v) else phase v (SUC i))) ==>
  Abbrev (e = if init then first else image start) ==>
  FINITE keep /\ FINITE D /\ DISJOINT keep D /\
  (!x y. x IN keep /\ old x y ==> y IN keep UNION D) /\
  (!v. v IN D ==> z v IN keep) /\ (if init then j IN keep else start IN keep UNION D) ==>
  ?W R.
    FINITE W /\ e IN W /\
    (!x. x IN W ==> ?l path. path 0=e /\ path l=x /\
                            !i. i<l ==> R (path i) (path(SUC i))) /\
    (!x y. R x y ==> x IN W /\ y IN W) /\
    (!x. x IN W ==>
       (?v. v IN keep /\ x=copy v) \/
       (?v i. v IN D /\ i<n /\ x=phase v i) \/ (init /\ x=first)) /\
    (!v. copy v IN W ==> !y. R (copy v) y <=> ?u. old v u /\ y=image u) /\
    (!v i. phase v i IN W ==> !y. R (phase v i) y <=> y=next v i) /\
    (first IN W ==> !y. R first y <=> y=copy j)
Proof
  qx_gen_tac `keep` >> rpt gen_tac >> rpt strip_tac >>
  qabbrev_tac `A = IMAGE copy keep UNION
      IMAGE (\(v,i). phase v i) (D CROSS count n) UNION (if init then {first} else {})` >>
  qabbrev_tac `E = \x y.
      (?v. v IN keep /\ x=copy v /\ ?u. old v u /\ y=image u) \/
      (?v i. v IN D /\ i<n /\ x=phase v i /\ y=next v i) \/
      (init /\ x=first /\ y=copy j)` >>
  `!x. x IN A <=> (?v. v IN keep /\ x=copy v) \/
       (?v i. v IN D /\ i<n /\ x=phase v i) \/ (init /\ x=first)` by
    (Cases_on `init` >> simp[Abbr `A`, IN_IMAGE, EXISTS_PROD, IN_CROSS] >> metis_tac[]) >>
  pop_assum (mk_asm "kinds") >>
  `!v. v IN keep ==> copy v IN A` by
    (rpt strip_tac >> asm "kinds" (simp o single) >> disj1_tac >> qexists `v` >> simp[]) >>
  `!v i. v IN D /\ i<n ==> phase v i IN A` by
    (rpt strip_tac >> asm "kinds" (simp o single) >> disj2_tac >> disj1_tac >> qexistsl [`v`,`i`] >> simp[]) >>
  `!v. v IN keep UNION D ==> image v IN A` by
    (qx_gen_tac `v` >> simp[IN_UNION, Abbr `image`] >>
     Cases_on `v IN keep` >> simp[] >> disch_tac >> Cases_on `n=0` >> simp[NOT_ZERO_LT_ZERO]) >>
  `!v i. v IN D /\ i<n ==> next v i IN A` by
    (rpt strip_tac >> Cases_on `SUC i=n` >> simp[Abbr `next`]
     >> `SUC i<n` by decide_tac >> metis_tac[]) >>
  `FINITE A` by (Cases_on `init` >> simp[Abbr `A`, FINITE_CROSS]) >>
  `e IN A` by
    (Cases_on `init` >> simp[Abbr `e`]
     >- asm "kinds" (simp o single) >> fs[]) >>
  `!x y. E x y ==> x IN A /\ y IN A` by
    (rpt gen_tac >> simp[Abbr `E`] >> metis_tac[]) >>
  qspecl_then [`A`,`E`,`e`] mp_tac stack_restrict_paths >> simp[LET_THM] >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  `!a b. pair_to_num a = pair_to_num b <=> a = b` by
    (metis_tac[pair_to_num_inv']) >>
  qexistsl [`W'`,`T'`] >>
  ntac 4 (conj_tac >- first_assum ACCEPT_TAC) >>
  `!x. x IN W' ==> x IN A` by fs[SUBSET_DEF] >>
  conj_tac >- (rpt strip_tac >> asm "kinds" (fn th => rewrite_tac[GSYM th]) >> simp[]) >>
  conj_tac >- suspend "copies" >>
  conj_tac >- suspend "phases" >> suspend "initial"
QED

Resume stack_port_incidence[copies]:
  rpt strip_tac >>
  `copy v IN A` by simp[] >>
  `v IN keep` by
    (asm "kinds" (qspec_then `copy v` mp_tac) >>
     simp[Abbr `copy`, Abbr `phase`, Abbr `first`]) >>
  simp[Abbr `E`, Abbr `copy`, Abbr `phase`, Abbr `first`]
QED

Resume stack_port_incidence[phases]:
  rpt strip_tac >>
  `phase v i IN A` by simp[] >>
  `v IN D /\ i<n` by
    (asm "kinds" (qspec_then `phase v i` mp_tac) >>
     simp[Abbr `copy`, Abbr `phase`, Abbr `first`]) >>
  simp[Abbr `E`, Abbr `copy`, Abbr `phase`, Abbr `first`]
QED

Resume stack_port_incidence[initial]:
  rpt strip_tac >>
  `first IN A` by simp[] >>
  `init` by (asm "kinds" (qspec_then `first` mp_tac) >>
             simp[Abbr `copy`, Abbr `phase`, Abbr `first`]) >>
  simp[Abbr `E`, Abbr `copy`, Abbr `phase`, Abbr `first`]
QED

Finalise stack_port_incidence

(* A row packet supplies the outgoing role for one explicitly given set of
   successors. Wiring does not strengthen the packet to a global q table:
   retained rows, replacement phases and the initial row supply it separately. *)
Theorem stack_selected_port_table:
  !q cc req (V:(num#num)set) old pc height rank need tag boolean
   b m n z ph_h ph_r ph_t ph_b ih ir it ib init j start.
  let f = splice_pc b m n in
  let keep = {v | v IN V /\ (pc v < b \/ b+m <= pc v)};
      D = {v | v IN V /\ pc v=b} in
  let copy = \v. (SUC (pair_to_num v),0:num);
      phase = \v i. (SUC (pair_to_num v),SUC i);
      first = (0:num,0:num) in
  let image = \v. if v IN keep then copy v
                  else if n=0 then copy (z v) else phase v 0;
      next = \v i. if SUC i=n then copy (z v) else phase v (SUC i) in
  let e = if init then first else image start in
  let trans = \v k. OPTION_MAP (\(l:string,o'). (l,f o')) (tag v k) in
  let cdata = \v. (f (pc v),height v,rank v,need v,trans v,boolean v);
      pdata = \v i. (b+i,ph_h v i,ph_r v i,F,ph_t v i,ph_b v i);
      idata = (b,ih,ir,F,it,ib) in
  let data = \x.
    if FST x=0 then idata else
    let v = num_to_pair (PRE (FST x)) in
    if SND x=0 then cdata v else pdata v (PRE (SND x)) in
  let Pc = \x. FST (data x);
      H = \x. FST (SND (data x));
      Rk = \x. FST (SND (SND (data x)));
      Need = \x. FST (SND (SND (SND (data x))));
      Tag = \x. FST (SND (SND (SND (SND (data x)))));
      Bool = \x. SND (SND (SND (SND (SND (data x))))) in
  let lo = SND (compute_label_offsets q); otp = build_offset_to_pc q in
  let Canon = \l d. ?off. FLOOKUP lo l = SOME off /\ off < dimword(:256) /\
                          FLOOKUP otp off = SOME d in
  let target = \x y. ?l orig. Tag x 0 = SOME(l,orig) /\ Canon l (Pc y) in
  let Slots = \x.
    (Need x ==> cc.cc_static) /\
    (!k. Bool x k ==> k < H x /\ Tag x k=NONE) /\
    (!k l orig. Tag x k = SOME(l,orig) ==>
      k < H x /\ orig < LENGTH q /\
      (EL orig q = AsmPushLabel l \/ EL orig q = AsmPushOfst l 0) /\
      ?d. Canon l d) in
  let Shape = \x (t:asm_state).
    t.as_pc=Pc x /\ LENGTH t.as_stack=H x /\ t.as_call_ctx=cc /\
    t.as_requests=req /\ (Need x ==> t.as_call_ctx.cc_static) /\
    (!k l orig. Tag x k=SOME(l,orig) ==>
      k < H x /\ orig < LENGTH q /\
      (EL orig q=AsmPushLabel l \/ (?d. EL orig q=AsmPushOfst l d) \/
       EL orig q=AsmDataLabel l) /\
      ?off d. FLOOKUP lo l=SOME off /\ off < dimword(:256) /\
              FLOOKUP otp off=SOME d /\ EL k t.as_stack=(n2w off:bytes32)) /\
    (!k. Bool x k ==> k < H x /\ (EL k t.as_stack=0w \/ EL k t.as_stack=1w)) in
  let Flow = \x y.
    let hi = H x; hj = H y; ins = EL (Pc x) q in
    let inherit = \(src:num->num option) (fresh:num->(string#num)option) bnew.
      (!k l orig. Tag y k=SOME(l,orig) ==>
        k < hj /\ (fresh k=SOME(l,orig) \/
          ?a. src k=SOME a /\ a < hi /\ Tag x a=SOME(l,orig))) /\
      (!k. Bool y k ==> k < hj /\
        (bnew k \/ ?a. src k=SOME a /\ a < hi /\ Bool x a)) in
    case ins of
      AsmLabel l => hj=hi /\ inherit (\k. SOME k) (\k. NONE) (\k. F)
    | AsmPush bs => hj=hi+1 /\
        inherit (\k. if k=0 then NONE else SOME(k-1)) (\k. NONE)
          (\k. k=0 /\ !t u. asm_step lo otp (AsmPush bs) t=AsmOK u ==>
            (EL 0 u.as_stack=0w \/ EL 0 u.as_stack=1w))
    | AsmPushLabel l => hj=hi+1 /\
        inherit (\k. if k=0 then NONE else SOME(k-1))
          (\k. if k=0 then SOME(l,Pc x) else NONE) (\k. F)
    | AsmPushOfst l d => hj=hi+1 /\
        inherit (\k. if k=0 then NONE else SOME(k-1))
          (\k. if k=0 /\ d=0 then SOME(l,Pc x) else NONE) (\k. F)
    | AsmOp name =>
        (case ALOOKUP dup_table name of
           SOME a => a < hi /\ hj=hi+1 /\
             inherit (\k. SOME(if k=0 then a else k-1)) (\k. NONE) (\k. F)
         | NONE => case ALOOKUP swap_table name of
             SOME a => 0 < a /\ a < hi /\ hj=hi /\
               inherit (\k. SOME(if k=0 then a else if k=a then 0 else k))
                 (\k. NONE) (\k. F)
           | NONE =>
               let a = asm_op_arity name; c = hj + asm_op_arity name - hi in
               a <= hi /\ hj=c+(hi-a) /\
               ((name="JUMP" \/ name="JUMPI") ==> c=0) /\
               inherit (\k. if k<c then NONE else SOME(k-c+a)) (\k. NONE)
                 (\k. k=0 /\ c=1 /\ asm_returns_zero_or_one ins /\
                   !t u. LENGTH t.as_stack=hi /\ asm_step lo otp ins t=AsmOK u ==>
                     (EL 0 u.as_stack=0w \/ EL 0 u.as_stack=1w)))
    | _ => F in
  let EdgeOK = \x y. Flow x y /\
    (if EL (Pc x) q=AsmOp "JUMP" then target x y
     else if EL (Pc x) q=AsmOp "JUMPI" then Pc y=Pc x+1 \/ target x y
     else Pc y=Pc x+1) in
  let Dispatch = \x S.
    Pc x < LENGTH q /\
    let h = H x in
    let fall = \y. Pc y=Pc x+1 in
    let arm = \P a. ?y. S y /\ P y /\ H y=a in
    let legal = \P a. !y. S y ==> P y /\ H y=a in
    let normal = \a. arm fall a /\ legal fall a in
    let clear = \a. !k. k<a ==> Tag x k=NONE in
    let stop = \a. a<=h /\ clear a /\ !y. ~S y in
    case EL (Pc x) q of
      AsmLabel l => normal h
    | AsmPush bs => normal (h+1)
    | AsmPushLabel l => IS_SOME (FLOOKUP lo l) /\ normal (h+1)
    | AsmPushOfst l d => IS_SOME (FLOOKUP lo l) /\ normal (h+1)
    | AsmOp name =>
        if name="INVALID" then stop 0
        else if name="REVERT" then stop 2
        else if MEM name ["SSTORE";"TSTORE";"LOG0";"LOG1";"LOG2";"LOG3";"LOG4"]
             then cc.cc_static /\ stop (asm_op_arity name)
        else (case ALOOKUP dup_table name of
           SOME a => a<h /\ normal (h+1)
         | NONE => case ALOOKUP swap_table name of
             SOME a => 0<a /\ a<h /\ normal h
           | NONE =>
               if name="JUMP" then
                 1<=h /\ arm (target x) (h-1) /\ legal (target x) (h-1)
               else if name="JUMPI" then
                 2<=h /\ Tag x 1=NONE /\ arm fall (h-2) /\ arm (target x) (h-2) /\
                 legal (\y. fall y \/ target x y) (h-2)
               else ?c. static_abort_straight name c /\ asm_op_arity name<=h /\
                        clear (asm_op_arity name) /\ normal (h-asm_op_arity name+c))
    | _ => F in
  let Rows = \W R.
    (!x. x IN W ==> Slots x) /\
    (!x y. R x y ==> x IN W /\ y IN W /\ Rk y < Rk x /\ Flow x y) /\
    (!x. x IN W ==> Dispatch x (R x)) in
  let Local = \x S. Slots x /\ Dispatch x S /\
    (!y. S y ==> Rk y < Rk x /\ EdgeOK x y) in
  let lift = \v y. ?u. old v u /\ y=image u in
  let head = \v.
    Pc (image v)=b /\ H (image v)=height v /\
    (if n=0 then Rk (image v)<rank v else Rk (image v)=rank v) /\
    (!k l orig. Tag (image v) k=SOME(l,orig) ==> trans v k=SOME(l,orig)) /\
    (!k. Bool (image v) k ==> boolean v k) in
  FINITE V /\ 0<m /\
  (!v u. v IN keep /\ old v u ==> u IN keep UNION D) /\
  (!v. v IN D ==> z v IN keep /\ pc (z v)=b+m /\ rank (z v)<rank v /\ head v) /\
  (if init then j IN keep else start IN keep UNION D) /\
  (!v. v IN keep ==> Local (copy v) (lift v)) /\
  (!v i. v IN D /\ i<n ==> Local (phase v i) (\y. y=next v i)) /\
  (init ==> Local first (\y. y=copy j)) ==>
  ?W R.
    e IN W /\ (!x. x IN W ==> ?l path. path 0=e /\ path l=x /\
                                      !i. i<l ==> R (path i) (path(SUC i))) /\
    Rows W R /\ FINITE W /\ (!x. x IN W ==> ?t. Shape x t) /\
    (!x. x IN W ==> Pc x < LENGTH q) /\
    (!x y. R x y ==> x IN W /\ y IN W /\ Rk y < Rk x /\ EdgeOK x y) /\
    (init ==> e=first /\ data e=idata) /\
    (~init /\ start IN keep ==> e=copy start /\ data e=cdata start) /\
    (~init /\ start IN D ==> head start /\
      if n=0 then e=copy (z start) /\ data e=cdata (z start)
      else e=phase start 0 /\ data e=pdata start 0)
Proof
  rpt gen_tac >>
  let_vars [`f`,`keep`,`D`,`copy`,`phase`,`first`,`image`,`next`,`e`,
    `trans`,`cdata`,`pdata`,`idata`,`data`,`Pc`,`H`,`Rk`,`Need`,`Tag`,`Bool`,
    `lo`,`otp`,`Canon`,`target`,`Slots`,`Shape`,`Flow`,`EdgeOK`,`Dispatch`,
    `Rows`,`Local`,`lift`,`head`] >> strip_tac >>
  `FINITE keep /\ FINITE D /\ DISJOINT keep D` by
    (conj_tac >- (irule SUBSET_FINITE_I >> qexists `V` >> simp[SUBSET_DEF, Abbr `keep`]) >>
     conj_tac >- (irule SUBSET_FINITE_I >> qexists `V` >> simp[SUBSET_DEF, Abbr `D`]) >>
     simp[Abbr `keep`, Abbr `D`, DISJOINT_DEF, EXTENSION, IN_INTER]) >>
  qspecl_then [`keep`,`D`,`old`,`z`,`n`,`init`,`j`,`start`,
    `copy`,`phase`,`first`,`image`,`next`,`e`] mp_tac stack_port_incidence >>
  ntac 6 (impl_tac >- first_assum ACCEPT_TAC) >>
  (impl_tac >-
    (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     rpt strip_tac >> qpat_assum `!v. v IN D ==> _` (drule_then strip_assume_tac) >> simp[])) >>
  disch_then (qx_choose_then `live` (qx_choose_then `rel` strip_assume_tac)) >>
  qexistsl [`live`,`rel`] >>
  ntac 2 (conj_tac >- first_assum ACCEPT_TAC) >>
  `!x. x IN live ==> Local x (rel x)` by suspend "local_rows" >>
  `!x. x IN live ==> Slots x /\ Dispatch x (rel x) /\
    !y. rel x y ==> Rk y < Rk x /\ EdgeOK x y` by
    fs[Abbr `Local`] >>
  `!x y. rel x y ==> x IN live /\ y IN live /\ Rk y < Rk x /\ EdgeOK x y` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `!x y. rel x y ==> x IN live /\ y IN live` (drule_then strip_assume_tac) >>
     simp[] >> qpat_assum `!x. x IN live ==> Local x (rel x)` (drule_then mp_tac) >>
     simp[Abbr `Local`]) >>
  conj_tac >- suspend "rows" >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- suspend "inhabit" >>
  conj_tac >- (rpt strip_tac >> qpat_assum `!x. x IN live ==> Slots x /\ _`
    (drule_then strip_assume_tac) >> fs[Abbr `Dispatch`]) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  suspend "root"
QED

Resume stack_selected_port_table[local_rows]:
  qx_gen_tac `x` >> disch_tac >>
  qpat_assum `!x. x IN live ==> (?v. v IN keep /\ x = copy v) \/ _`
    (drule_then strip_assume_tac)
  >- (qpat_x_assum `x=copy v` SUBST_ALL_TAC >>
      `rel (copy v) = lift v` by simp[FUN_EQ_THM, Abbr `lift`] >> simp[])
  >- (qpat_x_assum `x=phase v i` SUBST_ALL_TAC >>
      `rel (phase v i) = (\y. y=next v i)` by simp[FUN_EQ_THM] >> simp[]) >>
  qpat_x_assum `x=first` SUBST_ALL_TAC >>
  `rel first = (\y. y=copy j)` by simp[FUN_EQ_THM] >> simp[]
QED

Resume stack_selected_port_table[rows]:
  simp[Abbr `Rows`] >> rpt gen_tac >> disch_tac >>
  qpat_assum `!x y. rel x y ==> _ /\ _ /\ _ /\ EdgeOK x y`
    (drule_then strip_assume_tac) >> fs[Abbr `EdgeOK`]
QED

Resume stack_selected_port_table[inhabit]:
  qx_gen_tac `x` >> disch_tac >>
  `Slots x` by simp[] >>
  qpat_x_assum `Slots x` mp_tac >>
  simp[NoAsms, Abbr `Slots`, Abbr `Canon`] >> strip_tac >>
  qexists `(ARB:asm_state) with
    <|as_pc := Pc x; as_call_ctx := cc; as_requests := req;
      as_stack := GENLIST (\k. case Tag x k of NONE => 0w
         | SOME lr => n2w (THE (FLOOKUP lo (FST lr)))) (H x)|>` >>
  simp[Abbr `Shape`] >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `!k l orig. Tag x k = SOME(l,orig) ==> _`
    (drule_then strip_assume_tac) >> simp[] >> metis_tac[]
QED

Resume stack_selected_port_table[root]:
  conj_tac >- simp[Abbr `e`, Abbr `data`, Abbr `first`] >>
  conj_tac >- simp[Abbr `e`, Abbr `data`, Abbr `image`, Abbr `copy`] >>
  strip_tac >>
  `start NOTIN keep` by (fs[Abbr `D`] >> simp[Abbr `keep`]) >>
  `head start` by (qpat_assum `!v. v IN D ==> _` (drule_then strip_assume_tac) >> simp[]) >>
  simp[Abbr `e`, Abbr `image`, Abbr `data`, Abbr `copy`, Abbr `phase`] >>
  Cases_on `n=0` >> simp[]
QED

Finalise stack_selected_port_table
