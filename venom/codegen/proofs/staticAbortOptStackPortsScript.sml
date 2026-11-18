Theory staticAbortOptStackPorts
Ancestors
  staticAbortOptStackFixedRows staticAbortOptStackCommRow
  staticAbortOptStackFixedSource staticAbortOptStackGuardedSource
  staticAbortStraight asmOptimizer asmSplice asmSem asmIR asmSymSem
  arithmetic list pair option pred_set words finite_map combin alist

(* Throughout this script these quotations are syntax, not new constants. *)
val flow_at = ``
  \ins (opins:string->asm_inst) p pc height tag boolean (x:num#num) (y:num#num).
  let hi = height x; hj = height y in
  let inherit =
    \(src:num -> num option)
      (fresh:num -> (string#num)option) (bnew:num -> bool).
      (!k l origin. tag y k = SOME(l,origin) ==>
         k < hj /\ (fresh k = SOME(l,origin) \/
         ?a. src k = SOME a /\ a < hi /\ tag x a = SOME(l,origin))) /\
      (!k. boolean y k ==> k < hj /\
         (bnew k \/ ?a. src k = SOME a /\ a < hi /\ boolean x a))
  in
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
           let a = asm_op_arity name; m = hj + asm_op_arity name - hi in
           a <= hi /\ hj = m+(hi-a) /\
           ((name="JUMP" \/ name="JUMPI") ==> m=0) /\
           inherit (\k. if k<m then NONE else SOME(k-m+a)) (\k. NONE)
             (\k. k=0 /\ m=1 /\ asm_returns_zero_or_one (opins name) /\
               !t u. LENGTH t.as_stack=hi /\
                 asm_step (SND(compute_label_offsets p)) (build_offset_to_pc p)
                   (opins name) t = AsmOK u ==>
                 (EL 0 u.as_stack=0w \/ EL 0 u.as_stack=1w)))
  | _ => F``;

Triviality flow_presentations:
  !ins. ^flow_at ins (\name. ins) p pc height tag boolean x y =
        ^flow_at ins AsmOp p pc height tag boolean x y
Proof
  Cases >> SIMP_TAC bool_ss [LET_THM, asm_inst_case_def]
QED

val flow = ``\p pc height tag boolean x y.
  ^flow_at (EL (pc x) p) (\name. EL (pc x) p) p pc height tag boolean x y``;
val fixed_flow = ``\p pc height tag boolean x y.
  ^flow_at (EL (pc x) p) AsmOp p pc height tag boolean x y``;

val canon = ``\p l dest. ?off.
  FLOOKUP (SND(compute_label_offsets p)) l = SOME off /\
  off < dimword(:256) /\ FLOOKUP (build_offset_to_pc p) off = SOME dest``;

val target = ``\p pc (tag:num#num->num->(string#num)option) (x:num#num) (y:num#num).
  ?l origin off. tag x 0 = SOME(l,origin) /\
    FLOOKUP (SND(compute_label_offsets p)) l = SOME off /\
    off < dimword(:256) /\ FLOOKUP (build_offset_to_pc p) off = SOME(pc y)``;

val closed_open_with = ``
  \F p cc req (V:(num#num)->bool) (rank:(num#num)->num) pc height need tag boolean edge.
  let S = \i (t:asm_state).
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
       (EL k t.as_stack = 0w \/ EL k t.as_stack = 1w)) in
    FINITE V /\ {} SUBSET V /\
    (!x. x IN V ==> ?t. S x t) /\
    (!x. x IN V DIFF {} ==> pc x < LENGTH p) /\
    (!x y. edge x y ==>
       x IN V DIFF {} /\ y IN V /\ rank y < rank x /\
       F p pc height tag boolean x y /\
       (if EL (pc x) p = AsmOp "JUMP" then ^target p pc tag x y
        else if EL (pc x) p = AsmOp "JUMPI"
             then pc y = pc x+1 \/ ^target p pc tag x y
        else pc y = pc x+1)) /\
    (!x t. x IN V DIFF {} /\ S x t ==>
       (?u. (asm_steps (SND(compute_label_offsets p)) (build_offset_to_pc p)
                    p 1 t = AsmRevert u \/
              asm_steps (SND(compute_label_offsets p)) (build_offset_to_pc p)
                    p 1 t = AsmFault u) /\ u.as_requests=req) \/
       (?y u. edge x y /\
          asm_steps (SND(compute_label_offsets p)) (build_offset_to_pc p)
            p 1 t = AsmOK u /\ S y u))``;

val closed_open = ``^closed_open_with ^flow``;
val fixed_closed_open = ``^closed_open_with ^fixed_flow``;

Triviality open_presentations:
  ^fixed_closed_open p cc req V rank pc height need tag boolean edge =
  ^closed_open p cc req V rank pc height need tag boolean edge
Proof
  SIMP_TAC bool_ss [LET_THM, GSYM (SIMP_RULE bool_ss [LET_THM] flow_presentations)]
QED

val producer = ``\p l origin.
  EL origin p = AsmPushLabel l \/ EL origin p = AsmPushOfst l 0``;

val slots = ``\p cc (h:num) need (g:num->(string#num)option) B.
  (need ==> cc.cc_static) /\
  (!k. B k ==> k<h /\ g k=NONE) /\
  (!k l origin. g k=SOME(l,origin) ==>
    k<h /\ origin<LENGTH p /\ ^producer p l origin /\ ?j. ^canon p l j)``;

val rows = ``
  \p cc (V:(num#num)->bool) X (rank:num#num->num) pc height need tag boolean edge.
    let lo = SND(compute_label_offsets p) in
    (!x. x IN V ==> ^slots p cc (height x) (need x) (tag x) (boolean x)) /\
    (!x y. edge x y ==>
       x IN V DIFF X /\ y IN V /\ rank y < rank x /\
       ^flow p pc height tag boolean x y) /\
    (!x. x IN V DIFF X ==>
       pc x < LENGTH p /\
       let h = height x in
       let fall = \y. pc y = pc x + 1 in
       let arm = \P n. ?y. edge x y /\ P y /\ height y = n in
       let legal = \P n. !y. edge x y ==> P y /\ height y = n in
       let next = \n. arm fall n /\ legal fall n in
       let untagged = \a. !k. k<a ==> tag x k=NONE in
       let stop = \a. a<=h /\ untagged a /\ !y. ~edge x y in
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
           else (case ALOOKUP dup_table name of
                   SOME n => n<h /\ next (h+1)
                 | NONE => case ALOOKUP swap_table name of
                     SOME n => 0<n /\ n<h /\ next h
                   | NONE =>
                       if name="JUMP" then
                         1<=h /\ arm (^target p pc tag x) (h-1) /\
                         legal (^target p pc tag x) (h-1)
                       else if name="JUMPI" then
                         2<=h /\ tag x 1=NONE /\ arm fall (h-2) /\
                         arm (^target p pc tag x) (h-2) /\
                         legal (\y. fall y \/ ^target p pc tag x y) (h-2)
                       else ?m. static_abort_straight name m /\ asm_op_arity name <= h /\
                                untagged (asm_op_arity name) /\ next (h-asm_op_arity name+m))
       | _ => F)``;

val layout = ``\p q f.
  (!l org. org<LENGTH p /\ ^producer p l org ==>
     f org<LENGTH q /\ EL (f org) q=EL org p) /\
  (!l j. ^canon p l j ==> ^canon q l (f j))``;

val relocate = ``\(f:num->num) (g:num->(string#num)option) k.
  OPTION_MAP (\(l,org). (l,f org)) (g k)``;
val mask_tag = ``\m (g:num->(string#num)option) k. if k<m then NONE else g k``;
val mask_bool = ``\m (B:num->bool) k. m<=k /\ B k``;
val swap1 = ``\k:num. if k=0 then 1 else if k=1 then 0 else k``;

(* Translation never relies on numerical equality of two different origins. *)
Triviality relocate_masked_slots:
  ^layout p q f /\ ^slots p cc h need g B /\ (need' ==> need) /\
  (!k. m<=k /\ src k<h ==> k<out) ==>
  ^slots q cc out need'
    (\k. if k<m then NONE else ^relocate f g (src k))
    (\k. m<=k /\ B (src k))
Proof
  BETA_TAC >> strip_tac >> conj_tac >- metis_tac[] >>
  conj_tac >-
    (simp[] >> rpt strip_tac >> qpat_assum `!j. B j ==> _` (drule_then strip_assume_tac) >>
     simp[] >> metis_tac[]) >>
  rpt gen_tac >> Cases_on `k<m` >> simp[] >>
  Cases_on `g (src k)` >> simp[] >> PairCases_on `x` >> simp[] >>
  strip_tac >> gvs[] >>
  qpat_assum `!j l org. g j = SOME (l,org) ==> _` (drule_then strip_assume_tac) >>
  `f x1 < LENGTH q /\ EL (f x1) q = EL x1 p` by metis_tac[] >>
  simp[] >> qexists `f j` >> metis_tac[]
QED

val erase_fixed = ``[AsmOp "DUP1"; AsmOp "SWAP1"; AsmOp "POP"]``;
val swap_old = ``[AsmOp "DUP1"; AsmOp "SWAP2"; AsmOp "SWAP1"]``;
val pop_old = ``[AsmOp "SWAP1"; AsmOp "POP"; AsmOp "POP"]``;
val dup_old = ``[AsmOp "DUP1"; AsmOp "SWAP1"]``;
val fixed_positive = ``\w d.
  (w=^swap_old /\ d=[AsmOp "SWAP1";AsmOp "DUP2"]) \/
  (w=^pop_old /\ d=[AsmOp "POP";AsmOp "POP"]) \/
  (w=^dup_old /\ d=[AsmOp "DUP1"])``;
val guarded_erase = ``\w. ?a. asm_swap_op a /\ w=[a;a]``;
val guarded_positive = ``\w d. ?a. asm_commutative_op a /\ w=[AsmOp "SWAP1";a] /\ d=[a]``;

val exit_packet = ``\(V:(num#num)->bool) (pc:num#num->num) (rank:num#num->num) b m v z.
  z IN V /\ pc z=b+m /\ rank z<rank v``;
val same_demands = ``\(height:num#num->num) (g:(num#num)->num->(string#num)option) (B:num#num->num->bool) v z.
  height z=height v /\
  (!k l org. g z k=SOME(l,org) ==> g v k=SOME(l,org)) /\
  (!k. B z k ==> B v k)``;

val port_norm = SIMP_RULE bool_ss [LET_THM];
val fixed_paths = REWRITE_RULE [port_norm open_presentations]
  (port_norm stack_fixed_source_demand_paths);

Triviality erase_fixed_port:
  ^closed_open p cc req V rank pc height need tag boolean edge /\
  v IN V /\ pc v=LENGTH pre /\ p=pre ++ ^erase_fixed ++ tail ==>
  ?z. ^exit_packet V pc rank (LENGTH pre) 3 v z /\
      ^same_demands height tag boolean v z
Proof
  SIMP_TAC bool_ss [LET_THM] >>
  disch_then (CONJUNCTS_THEN2 (mk_asm "open") strip_assume_tac) >>
  (* The former in-window edge adapter failed before constructor reduction:
     mp_tac (cj 2 (port_norm stack_fixed_source_demand_paths)) >>
     impl_tac >-
       (asm "open" strip_assume_tac >>
        rpt (FIRST [first_assum ACCEPT_TAC, conj_tac]) >>
        rpt gen_tac >> disch_tac >>
        qpat_x_assum `p = pre ++ _` kall_tac >>
        qpat_assum `!x y. edge x y ==> _` (qspecl_then [`x`,`y`] mp_tac) >>
        impl_tac >- first_assum ACCEPT_TAC >>
        Cases_on `EL (pc x) p` >> pure_asm_rewrite_tac [asm_inst_case_def] >>
        disch_then ACCEPT_TAC) >>
     disch_then (qspecl_then [`^erase_fixed`,`tail`] mp_tac) >> simp[MAP]
  *)
  asm "open" assume_tac >>
  mp_tac (cj 2 fixed_paths) >>
  impl_tac >- rpt (FIRST [first_assum ACCEPT_TAC, conj_tac]) >>
  disch_then (qspec_then `tail` mp_tac) >>
  SIMP_TAC bool_ss [MAP, LENGTH, DECIDE ``SUC (SUC (SUC 0)) = 3``] >>
  impl_tac >- first_assum ACCEPT_TAC >>
  disch_then (CONJUNCTS_THEN2 assume_tac (qx_choose_then `path` strip_assume_tac)) >>
  qpat_assum `!i. i<=3 ==> _` (qspec_then `3` strip_assume_tac o SRULE[]) >>
  qpat_assum `path 0=v` (fn root =>
    qpat_x_assum `!i. i<3 ==> _` (fn th =>
      map_every (fn i => qspec_then i (strip_assume_tac o SRULE[root,ADD1]) th) [`0`,`1`,`2`])) >>
  `rank (path 3) < rank v` by
    (irule LESS_TRANS >> qexists `rank (path 2)` >> simp[] >>
     irule LESS_TRANS >> qexists `rank (path 1)` >> simp[]) >>
  qexists `path 3` >> simp[] >>
  qpat_assum `!k. (!l org. tag (path 3) k = _ ==> _) /\ _`
    (mp_tac o SIMP_RULE bool_ss [combinTheory.I_THM, FORALL_AND_THM]) >>
  simp[]
QED

Triviality erase_guarded_port:
  ^closed_open p cc req V rank pc height need tag boolean edge /\
  v IN V /\ pc v=LENGTH pre /\ asm_static_wf p /\ asm_swap_op a /\
  p=pre++[a;a]++tail ==>
  ?z. ^exit_packet V pc rank (LENGTH pre) 2 v z /\
      ^same_demands height tag boolean v z
Proof
  SIMP_TAC bool_ss [LET_THM] >>
  disch_then (CONJUNCTS_THEN2 (mk_asm "open") strip_assume_tac) >>
  asm "open" assume_tac >>
  (* The original drule_all on the flattened guarded antecedent did not match. *)
  mp_tac (cj 1 (port_norm
      (Q.INST [`w` |-> `[a;a]`] (SPEC_ALL stack_guarded_source_demand_paths)))) >>
  impl_tac >- rpt (FIRST [first_assum ACCEPT_TAC, conj_tac]) >>
  SIMP_TAC bool_ss [LENGTH, DECIDE ``SUC (SUC 0) = 2``] >>
  impl_tac >- rpt (FIRST [first_assum ACCEPT_TAC, conj_tac]) >>
  disch_then (qx_choose_then `name` (qx_choose_then `n` (qx_choose_then `path` strip_assume_tac))) >>
  qpat_assum `!i. i<=2 ==> _` (qspec_then `2` (strip_assume_tac o SRULE[])) >>
  qpat_assum `path 0=v` (fn root =>
    qpat_x_assum `!i. i<2 ==> _` (fn th =>
      map_every (fn i => qspec_then i (strip_assume_tac o SRULE[root,ADD1]) th) [`0`,`1`])) >>
  `rank (path 2) < rank v` by
    (irule LESS_TRANS >> qexists `rank (path 1)` >> simp[]) >>
  qexists `path 2` >> simp[] >>
  qpat_assum `!k. (!l org. tag (path 2) k = _ ==> _) /\ _`
    (mp_tac o SIMP_RULE bool_ss [FORALL_AND_THM]) >>
  simp[]
QED

(* The executable guards of the replacement rows, independent of the source path. *)
val fall_guard = ``\ins hi hj (G:num->(string#num)option).
  ?name. ins = AsmOp name /\
    (case ALOOKUP dup_table name of
       SOME j => j<hi /\ hj=hi+1
     | NONE => case ALOOKUP swap_table name of
         SOME j => 0<j /\ j<hi /\ hj=hi
       | NONE => ?r. static_abort_straight name r /\ asm_op_arity name<=hi /\
           (!k. k<asm_op_arity name ==> G k=NONE) /\ hj=hi-asm_op_arity name+r)``;

val fixed_guard = ``\ins hi hj (G:num->(string#num)option) (B:num->bool).
    (?j name. ins=AsmOp name /\ ALOOKUP dup_table name=SOME j /\ j<hi /\ hj=hi+1) \/
    (?j name. ins=AsmOp name /\ ALOOKUP swap_table name=SOME j /\ 0<j /\ j<hi /\ hj=hi) \/
    (ins=AsmOp "POP" /\ static_abort_straight "POP" 0 /\ asm_op_arity "POP"=1 /\
     1<=hi /\ hj=hi-1 /\ G 0=NONE /\ ~B 0)``;

Triviality port_lookups:
  ALOOKUP dup_table "DUP1" = SOME 0 /\ ALOOKUP swap_table "DUP1" = NONE /\
  ALOOKUP dup_table "DUP2" = SOME 1 /\ ALOOKUP swap_table "DUP2" = NONE /\
  ALOOKUP dup_table "SWAP1" = NONE /\ ALOOKUP swap_table "SWAP1" = SOME 1 /\
  ALOOKUP dup_table "POP" = NONE /\ ALOOKUP swap_table "POP" = NONE
Proof
  EVAL_TAC
QED

Triviality fixed_fall_guard:
  MEM ins [AsmOp "DUP1";AsmOp "DUP2";AsmOp "SWAP1";AsmOp "POP"] /\
  ^fixed_guard ins hi hj G B ==> ^fall_guard ins hi hj G
Proof
  simp[MEM] >> rpt strip_tac >> gvs[port_lookups] >> qexists `0` >> simp[]
QED

val positive_port = ``
  \q cc (b:num) (f:num->num) d (height:(num#num)->num) need
     (rank:(num#num)->num) tag boolean (v:num#num) (z:num#num).
  let n = LENGTH d in
  ?(H:(num#num)->num) (R:(num#num)->num)
   (G:(num#num)->num->(string#num)option) (B:(num#num)->num->bool).
    let P = \x:num#num. b+FST x in
    H (0,0) = height v /\ H (n,0) = height z /\
    R (0,0) = rank v /\ R (n,0) = rank z /\
    (!k l org. G (0,0) k = SOME(l,org) ==> ^relocate f (tag v) k = SOME(l,org)) /\
    (!k. B (0,0) k ==> boolean v k) /\
    (!k. G (n,0) k = ^relocate f (tag z) k /\ (B (n,0) k <=> boolean z k)) /\
    (!i. i<=n ==> ^slots q cc (H (i,0)) (i=n /\ need z) (G (i,0)) (B (i,0))) /\
    (!i. i<n ==>
       P (i,0)<LENGTH q /\ EL (P (i,0)) q = EL i d /\ P (SUC i,0) = P (i,0)+1 /\
       R (SUC i,0) < R (i,0) /\
       ^flow q P H G B (i,0) (SUC i,0) /\
       ^fall_guard (EL i d) (H (i,0)) (H (SUC i,0)) (G (i,0)))``;

(* Present the fixed-row witness tables without choosing a second exit. *)
val fixed_H = ``\w n (h:num) hz (x:num#num).
  if FST x=n then hz else if w=^pop_old then h-FST x else h``;
val fixed_G = ``\w (n:num) f (g:num->(string#num)option) gz (x:num#num) k.
  ^relocate f (\j. if FST x=n then gz j else
    if w=^pop_old then ^mask_tag 2 g (FST x+j) else
    if FST x=0 then g j else g (^swap1 j)) k``;
val fixed_B = ``\w (n:num) (B:num->bool) Bz (x:num#num) k.
  if FST x=n then Bz k else
    if w=^pop_old then ^mask_bool 2 B (FST x+k) else
    if FST x=0 then B k else B (^swap1 k)``;
val fixed_R = ``\(rank:num#num->num) path (m:num) (n:num) (x:num#num).
  rank (path (if FST x=n then m else FST x))``;

(* All four transfers are instances of relocate_masked_slots; in particular,
   moving a sparse annotation never changes the identity of its producer. *)
Triviality slot_transfers:
  ^layout p q f /\ ^slots p cc h need g B ==>
  ^slots q cc h need (^relocate f g) B /\
  (!m. ^slots q cc h F (\k. if k<m then NONE else ^relocate f g k) (^mask_bool m B)) /\
  (!i. ^slots q cc (h-i) F
        (\k. if i+k<2 then NONE else ^relocate f g (i+k)) (\k. ^mask_bool 2 B (i+k))) /\
  (2<=h ==> ^slots q cc h F (\k. ^relocate f g (^swap1 k)) (\k. B (^swap1 k)))
Proof
  BETA_TAC >> strip_tac >>
  conj_tac >-
    (mp_tac (BETA_RULE (Q.INST [`src` |-> `\k:num. k`, `out` |-> `h:num`,
                              `m` |-> `0:num`, `need'` |-> `need:bool`] relocate_masked_slots)) >>
     impl_tac >- (rpt (FIRST [first_assum ACCEPT_TAC, conj_tac]) >> simp[]) >> simp[]) >>
  conj_tac >-
    (gen_tac >>
     mp_tac (BETA_RULE (Q.INST [`src` |-> `\k:num. k`, `out` |-> `h:num`,
                               `need'` |-> `F`] relocate_masked_slots)) >>
     impl_tac >- (rpt (FIRST [first_assum ACCEPT_TAC, conj_tac]) >> simp[]) >> simp[]) >>
  conj_tac >-
    (gen_tac >>
     mp_tac (BETA_RULE (Q.INST [`src` |-> `\k:num. i+k`, `out` |-> `h-i`,
                               `m` |-> `2-i`, `need'` |-> `F`] relocate_masked_slots)) >>
     impl_tac >- (rpt (FIRST [first_assum ACCEPT_TAC, conj_tac]) >> decide_tac) >>
     `!k. k<2-i <=> i+k<2` by decide_tac >>
     `!k. 2-i<=k <=> 2<=i+k` by decide_tac >>
     simp[] >> disch_then (ACCEPT_TAC o CONJUNCT2)) >>
  strip_tac >>
  mp_tac (BETA_RULE (Q.INST [`src` |-> `^swap1`, `out` |-> `h:num`,
                            `m` |-> `0:num`, `need'` |-> `F`] relocate_masked_slots)) >>
  impl_tac >-
    (rpt (FIRST [first_assum ACCEPT_TAC, conj_tac]) >> simp[] >>
     gen_tac >> Cases_on `k=0` >> Cases_on `k=1` >> simp[]) >>
  simp[] >> disch_then (ACCEPT_TAC o CONJUNCT2)
QED

(* The fixed producer's witness tables are used unchanged; the only added
   guarantees are layout bounds, Slots and the consumer-facing guard. *)
Theorem fixed_positive_port[local]:
  let b = LENGTH pre; m = LENGTH w; n = LENGTH d in
  let f = splice_pc b m n in
  p=pre++w++tail /\ q=pre++d++tail /\ ^fixed_positive w d /\
  ^layout p q f /\ ^rows p cc V {} rank pc height need tag boolean edge /\
  ^closed_open p cc req V rank pc height need tag boolean edge /\
  v IN V /\ pc v=b ==>
  ?z. ^exit_packet V pc rank b m v z /\
      ^positive_port q cc b f d height need rank tag boolean v z
Proof
  SIMP_TAC bool_ss [LET_THM] >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 (mk_asm "literal")
      (CONJUNCTS_THEN2 (mk_asm "layout") (CONJUNCTS_THEN2 (mk_asm "rows")
        (CONJUNCTS_THEN2 (mk_asm "open") strip_assume_tac)))))) >>
  mp_tac (port_norm stack_fixed_replacement_rows) >>
  impl_tac >-
    (asm "literal" assume_tac >> asm "open" assume_tac >>
     rpt (FIRST [first_assum ACCEPT_TAC, conj_tac])) >>
  asm_x "open" kall_tac >>
  disch_then (qx_choose_then `path` (fn th =>
    let val cs = CONJUNCTS th in
      map_every assume_tac (List.take(cs,10)) >> mk_asm "phase" (List.nth(cs,10))
    end)) >>
  qabbrev_tac `z = path (LENGTH w)` >>
  `rank z < rank v` by
    (unabbrev_all_tac >> asm "literal" strip_assume_tac >>
     qpat_assum `path 0=v` (fn root =>
       qpat_x_assum `!i. i<LENGTH w ==> _` (fn th =>
         map_every (fn i => qspec_then i (strip_assume_tac o SRULE[root,ADD1]) th)
           [`0`,`1`,`2`])) >>
     simp[] >> irule LESS_TRANS >> qexists `rank (path 1)` >> simp[] >>
     irule LESS_TRANS >> qexists `rank (path 2)` >> simp[]) >>
  qexists `z` >> conj_tac >- simp[] >>
  qexistsl [`^fixed_H w (LENGTH d) (height v) (height z)`,
            `^fixed_R rank path (LENGTH w) (LENGTH d)`,
            `^fixed_G w (LENGTH d) (splice_pc (LENGTH pre) (LENGTH w) (LENGTH d)) (tag v) (tag z)`,
            `^fixed_B w (LENGTH d) (boolean v) (boolean z)`] >>
  suspend "fixed_package"
QED

Resume fixed_positive_port[fixed_package]:
  SIMP_TAC bool_ss [LET_THM] >>
  `0 <> LENGTH d` by (asm "literal" strip_assume_tac >> simp[]) >>
  ntac 4 (conj_tac >- simp[]) >>
  conj_tac >-
    (gen_tac >> Cases_on `w = ^pop_old` >> Cases_on `k<2` >> simp[]) >>
  conj_tac >- simp[] >> conj_tac >- simp[] >>
  conj_tac >- suspend "fixed_slots" >>
  suspend "fixed_fall"
QED

Resume fixed_positive_port[fixed_slots]:
  asm "layout" (fn layout_th => asm "rows" (fn th =>
    map_every (fn (x,label) =>
      qspec_then x mp_tac (CONJUNCT1 th) >>
      (impl_tac >- first_assum ACCEPT_TAC) >>
      disch_then (mk_asm label o MATCH_MP (BETA_RULE slot_transfers) o CONJ layout_th))
    [(`v`,"head_slots"),(`z`,"exit_slots")])) >>
  qabbrev_tac `f = splice_pc (LENGTH pre) (LENGTH w) (LENGTH d)` >>
  asm_x "rows" kall_tac >> asm_x "layout" kall_tac >>
  `w=^swap_old ==> 2<=height v` by
    (strip_tac >>
     `d=[AsmOp "SWAP1";AsmOp "DUP2"]` by
       (asm "literal" strip_assume_tac >> fs[]) >>
     asm "phase" (qspec_then `0` mp_tac o underAIs (List.last o CONJUNCTS)) >>
     simp[port_lookups]) >>
  asm_x "phase" kall_tac >>
  gen_tac >> disch_tac >> Cases_on `i=LENGTH d`
  >- (asm "exit_slots" (mp_tac o CONJUNCT1) >> simp[] >> metis_tac[]) >>
  asm "literal" strip_assume_tac
  >- (Cases_on `i=0`
      >- (asm "head_slots" (mp_tac o CONJUNCT1) >> simp[] >> metis_tac[]) >>
      `i<>2` by fs[] >>
      asm "head_slots" (mp_tac o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) >>
      simp[] >> metis_tac[])
  >- (`i<>2` by fs[] >>
      asm "head_slots" (qspec_then `i` mp_tac o CONJUNCT1 o CONJUNCT2 o CONJUNCT2) >>
      simp[Q.ISPEC `OPTION_MAP (\(l:string,org:num). (l,f org))` COND_RAND] >>
      metis_tac[]) >>
  `i=0` by fs[] >> asm "head_slots" (mp_tac o CONJUNCT1) >> simp[] >> metis_tac[]
QED

Resume fixed_positive_port[fixed_fall]:
  gen_tac >> disch_tac >>
  conj_tac >- simp[] >>
  asm_x "phase" (qspec_then `i` mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >>
  qpat_x_assum `Abbrev (z = _)` (SUBST_ALL_TAC o REWRITE_RULE[markerTheory.Abbrev_def]) >>
  asm_x "layout" kall_tac >> asm_x "rows" kall_tac >>
  PURE_REWRITE_TAC [FST] >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac
      (CONJUNCTS_THEN2 (mk_asm "flow") (mk_asm "guard"))))) >>
  ntac 3 (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >- asm "flow" ACCEPT_TAC >>
  asm_x "flow" kall_tac >>
  `MEM (EL i d) [AsmOp "DUP1";AsmOp "DUP2";AsmOp "SWAP1";AsmOp "POP"]` by
    (`MEM (EL i d) d` by (PURE_REWRITE_TAC [MEM_EL] >> qexists `i` >> simp[]) >>
     asm "literal" strip_assume_tac >>
     qpat_x_assum `d = _` SUBST_ALL_TAC >>
     qpat_x_assum `MEM _ _` (strip_assume_tac o REWRITE_RULE [MEM]) >>
     simp[MEM]) >>
  asm_x "guard" mp_tac >> qpat_x_assum `MEM _ _` mp_tac >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  Q.SPEC_TAC (`EL i d`, `ins`) >> gen_tac >>
  simp[MEM] >> disch_then strip_assume_tac >>
  qpat_x_assum `ins = _` SUBST1_TAC >>
  (simp[port_lookups])
QED

Finalise fixed_positive_port


Triviality comm_positive_port:
  let b = LENGTH pre in
  let f = splice_pc b 2 1 in
  asm_static_wf p /\ asm_commutative_op a /\
  p=pre++[AsmOp "SWAP1";a]++tail /\ q=pre++[a]++tail /\
  ^layout p q f /\ ^rows p cc V {} rank pc height need tag boolean edge /\
  ^closed_open p cc req V rank pc height need tag boolean edge /\
  v IN V /\ pc v=b ==>
  ?z. ^exit_packet V pc rank b 2 v z /\
      ^positive_port q cc b f [a] height need rank tag boolean v z
Proof
  SIMP_TAC bool_ss [LET_THM,LENGTH,GSYM ONE] >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac
      (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 (mk_asm "layout")
        (CONJUNCTS_THEN2 (mk_asm "rows")
          (CONJUNCTS_THEN2 (mk_asm "open") strip_assume_tac))))))) >>
  mp_tac (SIMP_RULE bool_ss [LET_THM,FST] (SPEC_ALL stack_comm_replacement_row)) >>
  impl_tac >-
    (asm "open" assume_tac >> rpt (FIRST [first_assum ACCEPT_TAC, conj_tac])) >>
  asm_x "open" kall_tac >>
  disch_then (qx_choose_then `name` (qx_choose_then `path` (fn th =>
    let val cs = CONJUNCTS th in
      map_every assume_tac (List.take(cs,18)) >> mk_asm "flow" (List.last cs)
    end))) >>
  `!x y. edge x y ==> rank y < rank x` by
    (rpt gen_tac >> disch_tac >>
     asm "rows" (drule_then (ACCEPT_TAC o CONJUNCT1 o CONJUNCT2 o CONJUNCT2)
       o CONJUNCT1 o CONJUNCT2)) >>
  `rank (path 2) < rank v` by
    (irule LESS_TRANS >> qexists `rank (path 1)` >>
     conj_tac >> first_assum irule >> first_assum ACCEPT_TAC) >>
  qexists `path 2` >> conj_tac >- simp[] >>
  qabbrev_tac `f = splice_pc (LENGTH pre) 2 1` >>
  qexistsl [`\x:num#num. if FST x=0 then height v else height (path 2)`,
            `\x:num#num. if FST x=0 then rank v else rank (path 2)`,
            `\x:num#num. if FST x=0 then ^mask_tag 2 (^relocate f (tag v))
                         else ^relocate f (tag (path 2))`,
            `\x:num#num. if FST x=0 then ^mask_bool 2 (boolean v)
                         else boolean (path 2)`] >>
  SIMP_TAC bool_ss [LET_THM,FST,EVAL ``(1:num) = 0``] >>
  conj_tac >- simp[] >>
  conj_tac >- suspend "comm_slots" >> suspend "comm_fall"
QED

Resume comm_positive_port[comm_slots]:
  asm "layout" (fn layout_th => asm "rows" (fn th =>
    map_every (fn (x,label) =>
      qspec_then x mp_tac (CONJUNCT1 th) >>
      (impl_tac >- first_assum ACCEPT_TAC) >>
      disch_then (mk_asm label o MATCH_MP (BETA_RULE slot_transfers) o CONJ layout_th))
    [(`v`,"head_slots"),(`path 2`,"exit_slots")])) >>
  asm_x "rows" kall_tac >> asm_x "layout" kall_tac >>
  qpat_assum `q = pre++[a]++tail` (SUBST1_TAC o SYM) >>
  gen_tac >> disch_tac >> Cases_on `i=0`
  >- (qpat_x_assum `i=0` SUBST1_TAC >>
      asm "head_slots" (qspec_then `2` mp_tac o CONJUNCT1 o CONJUNCT2) >>
      PURE_REWRITE_TAC [EVAL ``(0:num) = 1``,COND_CLAUSES,REFL_CLAUSE] >>
      simp[NoAsms] >> disch_then (ACCEPT_TAC o CONJUNCT2)) >>
  `i=1` by decide_tac >> qpat_x_assum `i=1` SUBST1_TAC >>
  asm "exit_slots" (mp_tac o CONJUNCT1) >>
  PURE_REWRITE_TAC [EVAL ``(1:num) = 0``,COND_CLAUSES,REFL_CLAUSE] >>
  simp[NoAsms] >> disch_then (ACCEPT_TAC o CONJUNCT2 o CONJUNCT2)
QED

Resume comm_positive_port[comm_fall]:
  gen_tac >> disch_tac >> `i=0` by decide_tac >>
  qpat_x_assum `i=0` SUBST1_TAC >>
  asm_x "rows" kall_tac >> asm_x "layout" kall_tac >>
  asm "flow" mp_tac >>
  qpat_assum `Abbrev (f = _)` (SUBST1_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  SIMP_TAC bool_ss [GSYM ONE, EVAL ``(1:num) = 0``, ADD_CLAUSES, EL, HD] >>
  simp[NoAsms, EL_APPEND_EQN, ADD1] >> disch_tac >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexists `name` >>
  qpat_assum `a = AsmOp name` (fn fetch =>
  qpat_assum `ALOOKUP dup_table name = NONE` (fn dup =>
  qpat_assum `ALOOKUP swap_table name = NONE` (fn swap =>
  qpat_assum `asm_op_arity name = 2` (fn arity =>
    simp[NoAsms, fetch, dup, swap, arity])))) >>
  qexists `1` >> conj_tac >- first_assum ACCEPT_TAC >> decide_tac
QED

Finalise comm_positive_port

(* One exit is shared by the phase packet and the selected source path. *)
Theorem stack_whole_visit_port:
  let b = LENGTH pre; m = LENGTH w; n = LENGTH d in
  let f = splice_pc b m n in
  asm_static_wf p /\ p=pre++w++tail /\ q=pre++d++tail /\
  ((d=[] /\ (w=^erase_fixed \/ ^guarded_erase w)) \/
   ^fixed_positive w d \/ ^guarded_positive w d) /\
  ^layout p q f /\ ^rows p cc V {} rank pc height need tag boolean edge /\
  ^closed_open p cc req V rank pc height need tag boolean edge /\
  v IN V /\ pc v=b ==>
  ?z. ^exit_packet V pc rank b m v z /\
      (if n=0 then ^same_demands height tag boolean v z
       else ^positive_port q cc b f d height need rank tag boolean v z)
Proof
  SIMP_TAC bool_ss [LET_THM] >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac
      (CONJUNCTS_THEN2 (mk_asm "window") (CONJUNCTS_THEN2 assume_tac
        (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac strip_assume_tac))))))) >>
  asm_x "window" (DISJ_CASES_THEN2 strip_assume_tac
    (DISJ_CASES_THEN2 (mk_asm "fixed") (qx_choose_then `a` strip_assume_tac)))
  >- suspend "erase_fixed"
  >- suspend "erase_guarded"
  >- suspend "fixed"
  >> suspend "comm"
QED

Resume stack_whole_visit_port[erase_fixed]:
  qpat_x_assum `d=[]` SUBST_ALL_TAC >>
  qpat_x_assum `w=^erase_fixed` SUBST_ALL_TAC >>
  SIMP_TAC bool_ss [LENGTH, DECIDE ``SUC (SUC (SUC 0)) = 3``] >>
  mp_tac (port_norm erase_fixed_port) >>
  (impl_tac >- rpt (FIRST [first_assum ACCEPT_TAC, conj_tac])) >>
  SIMP_TAC bool_ss [LENGTH, DECIDE ``SUC (SUC (SUC 0)) = 3``]
QED

Resume stack_whole_visit_port[erase_guarded]:
  qpat_x_assum `d=[]` SUBST_ALL_TAC >>
  qpat_x_assum `w=[a;a]` SUBST_ALL_TAC >>
  SIMP_TAC bool_ss [LENGTH, DECIDE ``SUC (SUC 0) = 2``] >>
  mp_tac (port_norm erase_guarded_port) >>
  (impl_tac >- rpt (FIRST [first_assum ACCEPT_TAC, conj_tac])) >>
  disch_then ACCEPT_TAC
QED

Resume stack_whole_visit_port[fixed]:
  `LENGTH d <> 0` by
    (asm "fixed" strip_assume_tac >> simp[]) >>
  pop_assum (fn th => PURE_REWRITE_TAC [th,COND_CLAUSES]) >>
  asm_x "fixed" assume_tac >>
  mp_tac (port_norm fixed_positive_port) >>
  (impl_tac >- rpt (FIRST [first_assum ACCEPT_TAC, conj_tac])) >>
  disch_then ACCEPT_TAC
QED

Resume stack_whole_visit_port[comm]:
  qpat_x_assum `w=[AsmOp "SWAP1";a]` SUBST_ALL_TAC >>
  qpat_x_assum `d=[a]` SUBST_ALL_TAC >>
  RULE_ASSUM_TAC (SIMP_RULE bool_ss [LENGTH, GSYM ONE, DECIDE ``SUC 1 = 2``]) >>
  SIMP_TAC bool_ss [LENGTH, GSYM ONE, DECIDE ``SUC 1 = 2``, EVAL ``(1:num) = 0``] >>
  mp_tac (SIMP_RULE bool_ss [LET_THM,LENGTH,GSYM ONE] comm_positive_port) >>
  (impl_tac >- rpt (FIRST [first_assum ACCEPT_TAC, conj_tac])) >>
  disch_then ACCEPT_TAC
QED

Finalise stack_whole_visit_port
