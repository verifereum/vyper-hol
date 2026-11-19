Theory staticAbortOptStackFixedRows
Ancestors
  staticAbortOptStackFixedSource asmSplice staticAbortStraight
  asmSem asmIR asmSymSem list pair arithmetic pred_set finite_map words option
Libs
  BasicProvers

val swap1_slot = ``\k:num. if k=0 then 1 else if k=1 then 0 else k``;
val dup_slot = ``\n k:num. if k=0 then n else k-1``;
val mask_tag = ``\(t:num -> (string#num) option) k. if k<2 then NONE else t k``;
val mask_bool = ``\(b:num -> bool) k. 2<=k /\ b k``;
val relocate = ``\(f:num->num) (t:num -> (string#num) option) k.
  OPTION_MAP (\(l,o'). (l,f o')) (t k)``;

val demand_copy = ``
  \(hi:num) (hj:num) (ti:num -> (string#num)option) tj bi bj (src:num->num).
    !k. (!l org. tj k = SOME(l,org) ==>
                  k < hj /\ src k < hi /\ ti (src k) = SOME(l,org)) /\
        (bj k ==> k < hj /\ src k < hi /\ bi (src k))``;

val rows_flow = ``
  \p pc height tag boolean (x:num#num) (y:num#num).
  !hi. hi = height x ==>
  !hj. hj = height y ==>
  !ins. ins = EL (pc x) p ==>
  !inherit. inherit = (
    \(src:num -> num option)
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
  | _ => F``;

val rows_open = ``
  \p cc req (V:(num#num)->bool) (rank:(num#num)->num) pc height need tag boolean edge.
  !S. S = (\i (t:asm_state).
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
  !target. target = (\x y.
    ?l origin off. tag x 0 = SOME(l,origin) /\
      FLOOKUP (SND(compute_label_offsets p)) l = SOME off /\
      off < dimword(:256) /\
      FLOOKUP (build_offset_to_pc p) off = SOME(pc y)) ==>
    FINITE V /\ {} SUBSET V /\
    (!x. x IN V ==> ?t. S x t) /\
    (!x. x IN V DIFF {} ==> pc x < LENGTH p) /\
    (!x y. edge x y ==>
       x IN V DIFF {} /\ y IN V /\ rank y < rank x /\
       ^rows_flow p pc height tag boolean x y /\
       (if EL (pc x) p = AsmOp "JUMP" then target x y
        else if EL (pc x) p = AsmOp "JUMPI"
             then pc y = pc x+1 \/ target x y
        else pc y = pc x+1)) /\
    (!x t. x IN V DIFF {} /\ S x t ==>
       (?u. (asm_steps (SND(compute_label_offsets p)) (build_offset_to_pc p)
                    p 1 t = AsmRevert u \/
              asm_steps (SND(compute_label_offsets p)) (build_offset_to_pc p)
                    p 1 t = AsmFault u) /\ u.as_requests=req) \/
       (?y u. edge x y /\
          asm_steps (SND(compute_label_offsets p)) (build_offset_to_pc p)
            p 1 t = AsmOK u /\ S y u))``;

Triviality relocated_copy:
  ^demand_copy hi hj ti tj bi bj src ==>
  ^demand_copy hi hj (^relocate f ti) (^relocate f tj) bi bj src
Proof
  BETA_TAC >> strip_tac >> qx_gen_tac `k` >>
  first_x_assum (qspec_then `k` strip_assume_tac) >> simp[] >>
  rpt strip_tac >> PairCases_on `z` >> gvs[] >> metis_tac[]
QED

val row_guard = ``
  \ins hi hj (ti:num->(string#num)option) (bi:num->bool).
    (?j. ?name. ins=AsmOp name /\ ALOOKUP dup_table name=SOME j /\
                 j<hi /\ hj=hi+1) \/
    (?j. ?name. ins=AsmOp name /\ ALOOKUP swap_table name=SOME j /\
                 0<j /\ j<hi /\ hj=hi) \/
    (ins=AsmOp "POP" /\ static_abort_straight "POP" 0 /\
     asm_op_arity "POP"=1 /\ 1<=hi /\ hj=hi-1 /\ ti 0=NONE /\ ~bi 0)``;

Triviality destination_lookups:
  ALOOKUP dup_table "DUP1" = SOME 0 /\
  ALOOKUP dup_table "DUP2" = SOME 1 /\
  ALOOKUP dup_table "SWAP1" = NONE /\
  ALOOKUP swap_table "SWAP1" = SOME 1 /\
  ALOOKUP dup_table "POP" = NONE /\
  ALOOKUP swap_table "POP" = NONE /\
  asm_op_arity "POP" = 1 /\ static_abort_straight "POP" 0
Proof
  EVAL_TAC
QED

val row_demand = ``
  \ins hi hj (ti:num->(string#num)option) tj bi bj.
    ((ins=AsmOp "DUP1" /\ 0<hi /\ hj=hi+1 /\
      ^demand_copy hi hj ti tj bi bj (^dup_slot 0)) \/
     (ins=AsmOp "DUP2" /\ 1<hi /\ hj=hi+1 /\
      ^demand_copy hi hj ti tj bi bj (^dup_slot 1)) \/
     (ins=AsmOp "SWAP1" /\ 1<hi /\ hj=hi /\
      ^demand_copy hi hj ti tj bi bj ^swap1_slot) \/
     (ins=AsmOp "POP" /\ 1<=hi /\ hj=hi-1 /\ ti 0=NONE /\ ~bi 0 /\
      ^demand_copy hi hj ti tj bi bj (\k. k+1)))``;

Triviality destination_row:
  ^row_demand (EL (P x) q) (H x) (H y) (U x) (U y) (B x) (B y) ==>
  ^rows_flow q P H (\z. ^relocate f (U z)) B x y /\
  ^row_guard (EL (P x) q) (H x) (H y) (^relocate f (U x)) (B x)
Proof
  BETA_TAC >> strip_tac >>
  drule (BETA_RULE relocated_copy) >> disch_then (qspec_then `f` mp_tac) >>
  CONV_TAC (TOP_DEPTH_CONV (HO_REWR_CONV UNWIND_FORALL_THM2)) >>
  (* Reduce the case split before normalizing the quantifiers in inherit. *)
  ASM_REWRITE_TAC [LET_THM, asm_inst_case_def, destination_lookups,
                   optionTheory.option_case_def] >>
  TRY (`H x - 1 + 1 - H x = 0` by (qpat_assum `1 <= H x` mp_tac >> decide_tac)) >>
  ASM_REWRITE_TAC [] >>
  SIMP_TAC (srw_ss()) [FORALL_AND_THM, destination_lookups,
                       Excl "OPTION_MAP_EQ_SOME"] >>
  TRY (qpat_assum `!k. (!l org. U y k = SOME (l,org) ==> _) /\ _`
    (mp_tac o SIMP_RULE bool_ss [FORALL_AND_THM] o BETA_RULE) >> simp[])
  >- gvs[]
  >- gvs[]
  >- gvs[]
  >> metis_tac[]
QED

val swap_old = ``[AsmOp "DUP1"; AsmOp "SWAP2"; AsmOp "SWAP1"]``;
val swap_new = ``[AsmOp "SWAP1"; AsmOp "DUP2"]``;
val pop_old = ``[AsmOp "SWAP1"; AsmOp "POP"; AsmOp "POP"]``;
val pop_new = ``[AsmOp "POP"; AsmOp "POP"]``;
val dup_old = ``[AsmOp "DUP1"; AsmOp "SWAP1"]``;
val dup_new = ``[AsmOp "DUP1"]``;
val literals = ``\w d.
  (w = ^swap_old /\ d = ^swap_new) \/
  (w = ^pop_old /\ d = ^pop_new) \/
  (w = ^dup_old /\ d = ^dup_new)``;
val output_height = ``\w (h:num). if w = ^pop_old then h-2 else h+1``;
val input_min = ``\w. if w = ^dup_old then 1:num else 2``;
val slots_to_head = ``\w (k:num).
  if w = ^pop_old then k+2 else
  if w = ^dup_old then ^dup_slot 0 k else
  if k<2 then k else if k=2 then 0 else k-1``;

(* Tables before label-origin relocation. The last phase uses precisely the
   old continuation demands, not the full image of the head's demands. *)
val phase_height = ``\w (n:num) (h:num) (hz:num) i.
  if i=n then hz else if w = ^pop_old then h-i else h``;
val phase_tag = ``\w (n:num) (t:num -> (string#num)option) tz i k.
  if i=n then tz k else
  if w = ^pop_old then ^mask_tag t (i+k) else
  if i=0 then t k else t (^swap1_slot k)``;
val phase_bool = ``\w (n:num) (b:num -> bool) bz i k.
  if i=n then bz k else
  if w = ^pop_old then ^mask_bool b (i+k) else
  if i=0 then b k else b (^swap1_slot k)``;

Triviality swap_slot_facts:
  (2<=h ==> !k. (^swap1_slot k < h <=> k < h)) /\
  (!k. ^swap1_slot (^dup_slot 1 k) = ^slots_to_head ^swap_old k)
Proof
  conj_tac >> rpt strip_tac >> simp[] >>
  Cases_on `k=0` >> Cases_on `k=1` >> Cases_on `k=2` >> gvs[]
QED

val bounds = ``\h (t:num -> (string#num)option) (b:num->bool).
  (!k l org. t k = SOME (l,org) ==> k<h) /\ (!k. b k ==> k<h)``;

(* Retarget the input slots without inspecting any demanded value. *)
Triviality demand_copy_retarget:
  ^demand_copy h hz ti tz bi bz src ==>
  (!k. tm (g k) = ti (src k) /\ bm (g k) = bi (src k) /\
       (src k < h ==> g k < hm)) ==>
  ^demand_copy hm hz tm tz bm bz g
Proof
  BETA_TAC >> ntac 2 disch_tac >> qx_gen_tac `k` >>
  qpat_assum `!j. tm _ = _ /\ _` (qspec_then `k` strip_assume_tac) >>
  qpat_assum `!j. (!l org. tz j = _ ==> _) /\ _`
    (qspec_then `k` strip_assume_tac) >>
  metis_tac[]
QED

Triviality literal_rows:
  !n. n = LENGTH d ==>
  !H. H = ^phase_height w n h hz ==>
  !U. U = ^phase_tag w n ti tz ==>
  !B. B = ^phase_bool w n bi bz ==>
  ^literals w d /\ ^input_min w <= h /\ hz = ^output_height w h /\
  ^bounds h ti bi /\ ^demand_copy h hz ti tz bi bz (^slots_to_head w) ==>
  !i. i<n ==> ^row_demand (EL i d) (H i) (H (SUC i))
                             (U i) (U (SUC i)) (B i) (B (SUC i))
Proof
  SIMP_TAC bool_ss [LET_THM] >> strip_tac
  >- (qx_gen_tac `i` >> disch_tac >> `i=0 \/ i=1` by gs[] >>
      pop_assum strip_assume_tac >>
      gvs[EL, swap_slot_facts, FORALL_AND_THM]
      >- metis_tac[EL, swap_slot_facts, FORALL_AND_THM]
      >> mp_tac (BETA_RULE (Q.INST
           [`src` |-> `^slots_to_head ^swap_old`, `g` |-> `^dup_slot 1`,
            `tm` |-> `\j. ti (^swap1_slot j)`, `bm` |-> `\j. bi (^swap1_slot j)`,
            `hm` |-> `h:num`, `hz` |-> `h+1`] demand_copy_retarget)) >>
      impl_tac >- simp[FORALL_AND_THM] >>
      impl_tac >-
        (gen_tac >> drule (BETA_RULE (CONJUNCT1 swap_slot_facts)) >>
         disch_then (qspec_then `^dup_slot 1 k` mp_tac) >> BETA_TAC >>
         rewrite_tac [BETA_RULE (CONJUNCT2 swap_slot_facts)] >>
         POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
      simp[FORALL_AND_THM])
  >- (qx_gen_tac `i` >> disch_tac >> `i=0 \/ i=1` by gs[] >>
      pop_assum strip_assume_tac >>
      `h-1-1 = h-2` by decide_tac >> gvs[EL, FORALL_AND_THM, ADD_ASSOC]
      >- (`!k:num. 1+k=k+1` by decide_tac >>
          pop_assum (fn th => rewrite_tac [th]) >>
          conj_tac >> qx_gen_tac `k` >> Cases_on `k+1<2` >> simp[] >>
          rpt strip_tac >> res_tac >> decide_tac)
      >> mp_tac (BETA_RULE (Q.INST
           [`src` |-> `\k:num. k+2`, `g` |-> `\k:num. k+1`,
            `tm` |-> `\j. ^mask_tag ti (1+j)`, `bm` |-> `\j. ^mask_bool bi (1+j)`,
            `hm` |-> `h-1`, `hz` |-> `h-2`] demand_copy_retarget)) >>
      impl_tac >- simp[FORALL_AND_THM] >>
      impl_tac >-
        (qx_gen_tac `k` >> `1+(k+1) = k+2 /\ 2<=k+2 /\ ~(k+2<2)` by decide_tac >>
         simp[] >> decide_tac) >>
      simp[FORALL_AND_THM, AC ADD_ASSOC ADD_COMM])
  >> gvs[EL]
QED

(* Prior resisting literal_rows proof:
  SIMP_TAC bool_ss [LET_THM] >> strip_tac
  >- (qx_gen_tac `i` >> disch_tac >> `i=0 \/ i=1` by gs[] >>
      pop_assum strip_assume_tac >>
      gvs[EL, swap_slot_facts, FORALL_AND_THM]
      >- metis_tac[EL, swap_slot_facts, FORALL_AND_THM]
      >> conj_tac
      >- (qx_gen_tac `k` >> qx_gen_tac `ell` >> qx_gen_tac `org` >>
          disch_then (fn th => assume_tac th >>
            qpat_assum `!j a b. tz j = SOME (a,b) ==> _`
              (qspecl_then [`k`,`ell`,`org`] (strip_assume_tac o C MP th))) >>
          Cases_on `k=0` >> Cases_on `k=1` >> Cases_on `k=2` >> gvs[])
      >> qx_gen_tac `k` >>
      disch_then (fn th => assume_tac th >>
        qpat_assum `!j. bz j ==> _` (qspec_then `k` (strip_assume_tac o C MP th))) >>
      Cases_on `k=0` >> Cases_on `k=1` >> Cases_on `k=2` >> gvs[])
  >- (qx_gen_tac `i` >> disch_tac >> `i=0 \/ i=1` by gs[] >>
      pop_assum strip_assume_tac >>
      `h-1-1 = h-2` by decide_tac >> gvs[EL, FORALL_AND_THM, ADD_ASSOC] >>
      rpt strip_tac >> gvs[] >> metis_tac[])
  >> gvs[EL]
QED
*)

(* Specialize the integrated source-path theorem and keep just the annotations
   and path geometry needed to construct the destination phases. *)
Triviality select_literal_path:
  !m. m = LENGTH w ==>
  p = pre++w++tail /\
  ^rows_open p cc req V rank pc height need tag boolean edge /\
  v IN V /\ pc v = LENGTH pre /\ ^literals w d ==>
  ^input_min w <= height v /\ ^bounds (height v) (tag v) (boolean v) /\
  ?path. path 0 = v /\ (!i. i<=m ==> path i IN V /\ pc (path i) = LENGTH pre+i) /\
         (!i. i<m ==> edge (path i) (path(SUC i)) /\ rank(path(SUC i)) < rank(path i)) /\
         height(path m) = ^output_height w (height v) /\
         ^demand_copy (height v) (height(path m)) (tag v) (tag(path m))
                      (boolean v) (boolean(path m)) (^slots_to_head w)
Proof
  SIMP_TAC bool_ss [LET_THM] >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 (mk_asm "open")
       (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac (mk_asm "literal"))))) >>
  `^bounds (height v) (tag v) (boolean v)` by
    (asm "open" (qspec_then `v` mp_tac o cj 3) >>
     impl_tac >- first_assum ACCEPT_TAC >>
     strip_tac >> BETA_TAC >> metis_tac[]) >>
  mp_tac (SIMP_RULE bool_ss [LET_THM] stack_fixed_source_demand_paths) >>
  impl_tac >-
    (qpat_x_assum `p = _` kall_tac >>
     asm_x "open" strip_assume_tac >> asm_rewrite_tac [] >>
     qx_gen_tac `x` >> qx_gen_tac `y` >> disch_tac >>
     qpat_assum `!x y. edge x y ==> _` (qspecl_then [`x`,`y`] mp_tac) >>
     impl_tac >- first_assum ACCEPT_TAC >>
     Cases_on `EL (pc x) p` >> asm_rewrite_tac [asm_inst_case_def] >>
     BETA_TAC >> rewrite_tac []) >>
  asm_x "open" kall_tac >>
  disch_then (CONJUNCTS_THEN2 (mk_asm "swap")
    (CONJUNCTS_THEN2 kall_tac (CONJUNCTS_THEN2 (mk_asm "pop") (mk_asm "dup")))) >>
  asm "literal" strip_assume_tac
  >- (asm "swap" (qspec_then `tail` mp_tac) >>
      impl_tac >- simp[MAP] >>
      disch_then (CONJUNCTS_THEN2 assume_tac
        (qx_choose_then `path` strip_assume_tac)) >>
      gvs[MAP, FORALL_AND_THM] >> qexists `path` >> simp[])
  >- (asm "pop" (qspec_then `tail` mp_tac) >>
      impl_tac >- simp[MAP] >>
      disch_then (CONJUNCTS_THEN2 assume_tac
        (qx_choose_then `path` strip_assume_tac)) >>
      gvs[MAP, FORALL_AND_THM] >> qexists `path` >> simp[])
  >> asm "dup" (qspec_then `tail` mp_tac) >>
     impl_tac >- simp[MAP] >>
     disch_then (CONJUNCTS_THEN2 assume_tac
       (qx_choose_then `path` strip_assume_tac)) >>
     gvs[MAP, FORALL_AND_THM] >> qexists `path` >> simp[]

  (* Earlier packaging attempt: simp[MAP] >> strip_tac >>
     qexists `path` >> simp[]; this left nonexistential conjuncts. *)
QED

Triviality path_rank_lt:
  (!i. i<m ==> (r (SUC i):num) < r i) ==>
  !j i. i<j /\ j<=m ==> r j < r i
Proof
  strip_tac >> Induct >> simp[] >> rpt strip_tac >>
  `j<m` by decide_tac >>
  qpat_assum `!i. i<m ==> r (SUC i) < r i` (qspec_then `j` mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
  Cases_on `i=j` >- simp[] >>
  `r j < r i` by
    (qpat_assum `!i. i<j /\ j<=m ==> _` irule >> decide_tac) >>
  decide_tac
QED

Theorem stack_fixed_replacement_rows:
  !b. b = LENGTH pre ==>
  !m. m = LENGTH w ==>
  !n. n = LENGTH d ==>
  !f. f = splice_pc b m n ==>
  p = pre ++ w ++ tail /\ q = pre ++ d ++ tail /\
  ^rows_open p cc req V rank pc height need tag boolean edge /\
  v IN V /\ pc v = b /\ ^literals w d ==>
  ?path.
    !z. z = path m ==>
    !P. P = (\x:num#num. b + FST x) ==>
    !H. H = (\x:num#num. ^phase_height w n (height v) (height z) (FST x)) ==>
    !B. B = (\x:num#num. ^phase_bool w n (boolean v) (boolean z) (FST x)) ==>
    !R. R = (\x:num#num. rank (path (if FST x = n then m else FST x))) ==>
    !T. T = (\x:num#num. ^relocate f (^phase_tag w n (tag v) (tag z) (FST x))) ==>
    path 0 = v /\ z IN V /\ pc z = b+m /\
    (!i. i<=m ==> path i IN V /\ pc (path i) = b+i) /\
    (!i. i<m ==> edge (path i) (path (SUC i)) /\
                 rank (path (SUC i)) < rank (path i)) /\
    H (0,0) = height v /\ H (n,0) = height z /\
    R (0,0) = rank v /\ R (n,0) = rank z /\
    (!k. T (0,0) k = (if w = ^pop_old /\ k<2 then NONE
                       else ^relocate f (tag v) k) /\
         (B (0,0) k <=> (w <> ^pop_old \/ 2<=k) /\ boolean v k) /\
         T (n,0) k = ^relocate f (tag z) k /\
         (B (n,0) k <=> boolean z k)) /\
    !i. i<n ==>
      EL (P (i,0)) q = EL i d /\ P (SUC i,0) = P (i,0)+1 /\
      R (SUC i,0) < R (i,0) /\
      ^rows_flow q P H T B (i,0) (SUC i,0) /\
      ^row_guard (EL i d) (H (i,0)) (H (SUC i,0)) (T (i,0)) (B (i,0))
Proof
  SIMP_TAC bool_ss [LET_THM] >>
  disch_then (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac
       (CONJUNCTS_THEN2 assume_tac (mk_asm "literal")))))) >>
  mp_tac (SIMP_RULE bool_ss [LET_THM] select_literal_path) >>
  impl_tac >-
    (asm "literal" assume_tac >> rpt (FIRST [first_assum ACCEPT_TAC, conj_tac])) >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac (qx_choose_then `path` strip_assume_tac))) >>
  qpat_x_assum `FINITE V /\ _` kall_tac >>
  `0 < LENGTH d /\ LENGTH d <= LENGTH w` by
    (asm "literal" strip_assume_tac >> simp[]) >>
  `path (LENGTH w) IN V /\ pc (path (LENGTH w)) = LENGTH pre + LENGTH w` by
    (qpat_assum `!i. i<=LENGTH w ==> _` (qspec_then `LENGTH w` mp_tac) >> simp[]) >>
  (* Backward matching on the expanded phase terms resisted both irule and
     MATCH_MP_TAC (E0473). Match the head/exit packet instead. *)
  qsuff_tac `^literals w d /\ ^input_min w <= height v /\
   height (path (LENGTH w)) = ^output_height w (height v) /\
   ^bounds (height v) (tag v) (boolean v) /\
   ^demand_copy (height v) (height (path (LENGTH w)))
     (tag v) (tag (path (LENGTH w))) (boolean v) (boolean (path (LENGTH w)))
     (^slots_to_head w)`
  >- (disch_then (mk_asm "rows" o MATCH_MP (SIMP_RULE bool_ss [LET_THM] literal_rows)
                                o SIMP_RULE bool_ss [LET_THM]) >>
      `LENGTH d <> 0` by decide_tac >>
      qexists `path` >>
      rpt (FIRST [first_assum ACCEPT_TAC, conj_tac])
      >- simp[]
      >- simp[]
      >- simp[]
      >- simp[]
      >- (Cases_on `w = ^pop_old` >> simp[GSYM NOT_LESS] >>
          gen_tac >> Cases_on `k < 2` >> simp[])
      >> qx_gen_tac `i` >> disch_tac >>
      `EL (LENGTH pre + i) (pre ++ d ++ tail) = EL i d` by simp[EL_APPEND_EQN] >>
      `rank (path (if SUC i = LENGTH d then LENGTH w else SUC i)) < rank (path i)` by
        (irule (BETA_RULE (Q.INST [`r` |-> `\k. rank (path k)`] path_rank_lt)) >>
         conj_tac >- (IF_CASES_TAC >> decide_tac) >>
         qexists `LENGTH w` >>
         reverse conj_tac >- (IF_CASES_TAC >> decide_tac) >>
         qx_gen_tac `k` >> disch_tac >>
         qpat_assum `!j. j<LENGTH w ==> _` (qspec_then `k` mp_tac) >> simp[]) >>
      PURE_REWRITE_TAC [FST] >>
      conj_tac >- first_assum ACCEPT_TAC >>
      conj_tac >- decide_tac >>
      conj_tac >- simp[] >>
      qpat_assum `EL (LENGTH pre+i) (pre ++ d ++ tail) = EL i d` (fn fetch =>
        SIMP_TAC bool_ss [fetch] >>
        mp_tac (SIMP_RULE bool_ss [LET_THM,FST,fetch] (Q.INST
          [`q` |-> `pre ++ d ++ tail`, `P` |-> `\x:num#num. LENGTH (pre:asm_inst list) + FST x`,
           `H` |-> `\x:num#num. ^phase_height w (LENGTH (d:asm_inst list)) (height (v:num#num))
                                 (height (path (LENGTH w))) (FST x)`,
           `U` |-> `\x:num#num. ^phase_tag w (LENGTH (d:asm_inst list)) (tag (v:num#num))
                                 (tag (path (LENGTH w))) (FST x)`,
           `B` |-> `\x:num#num. ^phase_bool w (LENGTH (d:asm_inst list)) (boolean (v:num#num))
                                 (boolean (path (LENGTH w))) (FST x)`,
           `f` |-> `splice_pc (LENGTH (pre:asm_inst list)) (LENGTH (w:asm_inst list))
                              (LENGTH (d:asm_inst list))`,
           `x` |-> `(i,0:num)`, `y` |-> `(SUC i,0:num)`] destination_row))) >>
      impl_tac
      >- (asm "rows" (qspec_then `i` mp_tac) >>
          impl_tac >- first_assum ACCEPT_TAC >>
          qpat_assum `height (path (LENGTH w)) = _` (fn th => rewrite_tac [th])) >>
      disch_then ACCEPT_TAC) >>
  SIMP_TAC bool_ss [LET_THM] >> asm "literal" assume_tac >>
  rpt (FIRST [first_assum ACCEPT_TAC, conj_tac])
QED
