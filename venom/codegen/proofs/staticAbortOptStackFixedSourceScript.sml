Theory staticAbortOptStackFixedSource
Ancestors
  asmSem asmIR asmSymSem asmOptimizer list rich_list pair arithmetic pred_set
  finite_map words
Libs
  BasicProvers

val fixed_rows = ``
  [("DUP1",1:num,(\h:num. h+1),(\k:num. if k=0 then 0 else k-1));
   ("SWAP1",2,I,(\k. if k=0 then 1 else if k=1 then 0 else k));
   ("SWAP2",3,I,(\k. if k=0 then 2 else if k=2 then 0 else k));
   ("POP",1,(\h. h-1),(\k. k+1))]``;

val pull_demands = ``
  \(height:(num#num) -> num) (tag:(num#num) -> num -> (string#num)option)
    (boolean:(num#num) -> num -> bool) x y (f:num -> num).
    !k. (!l org. tag y k = SOME(l,org) ==>
                k < height y /\ f k < height x /\ tag x (f k) = SOME(l,org)) /\
        (boolean y k ==> k < height y /\ f k < height x /\ boolean x (f k))``;

(* Resolve only the four fixed opcodes. In particular no outcome consumer
   or external-call executor is unfolded. *)
Triviality fixed_dispatch:
  asm_step lo opcs (AsmOp "DUP1") t = asm_dup 0 t /\
  asm_step lo opcs (AsmOp "SWAP1") t = asm_swap 1 t /\
  asm_step lo opcs (AsmOp "SWAP2") t = asm_swap 2 t /\
  asm_step lo opcs (AsmOp "POP") t = asm_pop t
Proof
  simp[asm_step_def, asm_step_op_def, asm_step_arith_def,
       asm_step_compare_def, asm_step_bitwise_def, asm_step_memory_def,
       asm_step_control_def, asm_step_extcall_def, asm_step_copy_def,
       asm_step_context_def, dup_table_def, swap_table_def]
QED

(* Each row records its minimum height, height transformer and backwards
   slot map. Failing the minimum is an error, not a pending exception. *)
Triviality fixed_step_projection:
  MEM (name,m,H,f)
    [("DUP1",1,(\h. h+1),(\k. if k=0 then 0 else k-1));
     ("SWAP1",2,I,(\k. if k=0 then 1 else if k=1 then 0 else k));
     ("SWAP2",3,I,(\k. if k=0 then 2 else if k=2 then 0 else k));
     ("POP",1,(\h. h-1),(\k. k+1))] ==>
  !lo opcs t.
  !h. h = LENGTH t.as_stack ==>
  !r. r = asm_step lo opcs (AsmOp name) t ==>
    ((?u. r = AsmOK u) \/ (?msg. r = AsmError msg)) /\
    ((!u. r = AsmOK u ==> m <= h) /\
     (m <= h ==> ?u. r = AsmOK u)) /\
    !u. r = AsmOK u ==>
      u.as_pc = t.as_pc + 1 /\ LENGTH u.as_stack = H h /\
      u.as_call_ctx = t.as_call_ctx /\ u.as_requests = t.as_requests /\
      !k. k < H h ==> EL k u.as_stack = EL (f k) t.as_stack
Proof
  simp[] >> strip_tac >> rpt gen_tac >> gvs[fixed_dispatch, asm_dup_def, asm_swap_def,
                              asm_next_def, EL_LUPDATE] >-
   (IF_CASES_TAC >> simp[] >> gen_tac >> Cases_on `k` >> simp[]) >-
   (IF_CASES_TAC >> simp[EL_LUPDATE] >> rpt strip_tac >>
    Cases_on `k = 0` >> Cases_on `k = 1` >> gvs[EL_LUPDATE]) >-
   (IF_CASES_TAC >> simp[EL_LUPDATE] >> rpt strip_tac >>
    Cases_on `k = 0` >> Cases_on `k = 2` >> gvs[EL_LUPDATE]) >>
  Cases_on `t.as_stack` >> simp[asm_pop_def, asm_next_def, EL_CONS, GSYM ADD1]
QED

val fixed_shape = ``
  \p cc req (pc:(num#num) -> num) height need tag boolean i (t:asm_state).
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
       (EL k t.as_stack = 0w \/ EL k t.as_stack = 1w))``;

val op_flow = ``
  \p name (hi:num) (hj:num) (ti:num -> (string#num) option) tj bi bj.
  !inherit. inherit =
    (\(src:num -> num option)
      (fresh:num -> (string#num)option) (bnew:num -> bool).
      (!k l origin. tj k = SOME(l,origin) ==>
         k < hj /\ (fresh k = SOME(l,origin) \/
         ?a. src k = SOME a /\ a < hi /\ ti a = SOME(l,origin))) /\
      (!k. bj k ==> k < hj /\
         (bnew k \/ ?a. src k = SOME a /\ a < hi /\ bi a))
    ) ==>
  case ALOOKUP dup_table name of
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
          (\k. k=0 /\ m=1 /\ asm_returns_zero_or_one (AsmOp name) /\
            !t u. LENGTH t.as_stack=hi /\
              asm_step (SND(compute_label_offsets p)) (build_offset_to_pc p)
                (AsmOp name) t = AsmOK u ==>
              (EL 0 u.as_stack=0w \/ EL 0 u.as_stack=1w))``;

Theorem fixed_lookups[local]:
  ALOOKUP dup_table "DUP1" = SOME 0 /\
  ALOOKUP dup_table "SWAP1" = NONE /\
  ALOOKUP dup_table "SWAP2" = NONE /\
  ALOOKUP dup_table "POP" = NONE /\
  ALOOKUP swap_table "SWAP1" = SOME 1 /\
  ALOOKUP swap_table "SWAP2" = SOME 2 /\
  ALOOKUP swap_table "POP" = NONE /\ asm_op_arity "POP" = 1
Proof
  EVAL_TAC
QED

Theorem fixed_flow_projection[local]:
  MEM (name,m,H,f) ^fixed_rows /\ m <= height x /\
  height y = H (height x) /\
  ^op_flow p name (height x) (height y) (tag x) (tag y) (boolean x) (boolean y)
  ==> ^pull_demands height tag boolean x y f
Proof
  simp[] >> strip_tac >> gvs[fixed_lookups] >> metis_tac[]
QED

Triviality fixed_shape_replay:
  !(S:(num#num) -> asm_state -> bool).
  S = (^fixed_shape p cc req pc height need tag boolean) ==>
  !x y t u f.
  S x t /\ (need y ==> cc.cc_static) /\
  u.as_pc = pc y /\ LENGTH u.as_stack = height y /\
  u.as_call_ctx = t.as_call_ctx /\ u.as_requests = t.as_requests /\
  (!k. k < height y ==> EL k u.as_stack = EL (f k) t.as_stack) /\
  ^pull_demands height tag boolean x y f ==>
  S y u
Proof
  gen_tac >> disch_then SUBST1_TAC >> rpt gen_tac >>
  simp[] >> strip_tac >> simp[] >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `!j. (!l org. tag y j = SOME(l,org) ==> _) /\ _`
    (qspec_then `k` strip_assume_tac) >>
  `tag x (f k) = SOME(l,origin)` by fs[] >>
  qpat_x_assum `!j l org. tag x j = SOME(l,org) ==> _`
    (qspecl_then [`f k`,`l`,`origin`] mp_tac) >> simp[]
QED

Theorem fixed_fetch[local]:
  t.as_pc < LENGTH p ==>
  asm_steps lo opcs p 1 t = asm_step lo opcs (EL t.as_pc p) t
Proof
  rewrite_tac[numLib.num_CONV ``1:num``] >> strip_tac >> simp[asm_steps_def] >>
  Cases_on `asm_step lo opcs (EL t.as_pc p) t` >> simp[asm_steps_def]
QED

Theorem fixed_source_next[local]:
  !shp. shp = (^fixed_shape p cc req pc height need tag boolean) ==>
  !runstep. runstep = asm_steps (SND(compute_label_offsets p)) (build_offset_to_pc p) p 1 ==>
  MEM (name,m,H,f) ^fixed_rows /\ x IN V /\ pc x < LENGTH p /\
  EL (pc x) p = AsmOp name /\ (?t. shp x t) /\
  (!t. shp x t ==>
       (?u. (runstep t = AsmRevert u \/ runstep t = AsmFault u) /\ u.as_requests=req) \/
       (?y u. edge x y /\ runstep t = AsmOK u /\ shp y u)) /\
  (!y. edge x y ==> y IN V /\ (rank:(num#num)->num) y < rank x /\
        ^op_flow p name (height x) (height y) (tag x) (tag y) (boolean x) (boolean y))
  ==>
  m <= height x /\
  ?y. edge x y /\ y IN V /\ rank y < rank x /\ pc y = pc x+1 /\
      height y = H (height x) /\ ^pull_demands height tag boolean x y f /\
      !t. shp x t ==> ?u. runstep t = AsmOK u /\ shp y u
Proof
  CONV_TAC (REPEATC (HO_REWR_CONV UNWIND_FORALL_THM2)) >>
  qabbrev_tac `shp = ^fixed_shape p cc req pc height need tag boolean` >>
  qabbrev_tac `runstep = asm_steps (SND(compute_label_offsets p))
                                     (build_offset_to_pc p) p 1` >>
  BETA_TAC >> strip_tac >>
  `!z t. shp z t ==> t.as_pc = pc z /\ LENGTH t.as_stack = height z /\
                     (need z ==> cc.cc_static)` by (simp[Abbr `shp`] >> (metis_tac[Abbr `shp`])) >>
  `!t. shp x t ==> runstep t = asm_step (SND(compute_label_offsets p))
                           (build_offset_to_pc p) (AsmOp name) t`
    by (qx_gen_tac `cur` >> strip_tac >>
        `cur.as_pc < LENGTH p /\ EL cur.as_pc p = AsmOp name` by metis_tac[] >>
        simp[Abbr `runstep`, fixed_fetch]) >>
  `!t. shp x t ==> ((?u. runstep t = AsmOK u) \/ (?msg. runstep t = AsmError msg)) /\
          ((!u. runstep t = AsmOK u ==> m <= height x) /\
           (m <= height x ==> ?u. runstep t = AsmOK u)) /\
          !u. runstep t = AsmOK u ==>
            u.as_pc = pc x+1 /\ LENGTH u.as_stack = H (height x) /\
            u.as_call_ctx = t.as_call_ctx /\ u.as_requests = t.as_requests /\
            !k. k < H (height x) ==> EL k u.as_stack = EL (f k) t.as_stack`
    by (qx_gen_tac `cur` >> strip_tac >>
        `LENGTH cur.as_stack = height x /\ cur.as_pc = pc x` by metis_tac[] >>
        drule fixed_step_projection >>
        disch_then (qspecl_then [`SND(compute_label_offsets p)`,
                                 `build_offset_to_pc p`, `cur`] mp_tac) >> simp[])
  >> `?y u. edge x y /\ runstep t = AsmOK u /\ shp y u`
    by (qpat_x_assum `!t. shp x t ==> (?u. _ /\ _) \/ _`
          (qspec_then `t` mp_tac) >>
        qpat_assum `!t. shp x t ==> (_ \/ _) /\ _` (qspec_then `t` mp_tac) >>
        simp[] >> metis_tac[asm_result_distinct]) >>
  `m <= height x /\ pc y = pc x+1 /\ height y = H (height x) /\
      (need y ==> cc.cc_static)` by metis_tac[] >>
  qpat_x_assum `!y. edge x y ==> _` (qspec_then `y` mp_tac) >>
  impl_tac >- simp[] >> strip_tac >>
  `^pull_demands height tag boolean x y f` by
    (rewrite_tac[LET_THM] >> irule (REWRITE_RULE [LET_THM] fixed_flow_projection) >>
     qexistsl [`H`,`m`,`name`,`p`] >> BETA_TAC >> gvs[]) >>
  conj_tac >- simp[] >> qexists `y` >>
  BETA_TAC >> RULE_ASSUM_TAC BETA_RULE >>
  rpt (conj_tac >- asm_rewrite_tac[]) >>
  qx_gen_tac `cur` >> strip_tac >>
  `?out. runstep cur = AsmOK out` by metis_tac[] >>
  qexists `out` >> conj_tac >- metis_tac[] >>
  `out.as_pc = pc y /\ LENGTH out.as_stack = height y /\
   out.as_call_ctx = cur.as_call_ctx /\ out.as_requests = cur.as_requests /\
   (!k. k < height y ==> EL k out.as_stack = EL (f k) cur.as_stack)`
    by metis_tac[] >>
  qpat_assum `Abbrev (shp = _)`
    (qspecl_then [`x`,`y`,`cur`,`out`,`f`] mp_tac o
     MATCH_MP (BETA_RULE fixed_shape_replay) o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  simp[]
QED

val fixed_flow = ``
  \p pc height tag boolean (x:num#num) (y:num#num).
  !hi. hi = height x ==>
  !hj. hj = height y ==>
  !inherit. inherit =
    (\(src:num -> num option)
      (fresh:num -> (string#num)option) (bnew:num -> bool).
      (!k l origin. tag y k = SOME(l,origin) ==>
         k < hj /\ (fresh k = SOME(l,origin) \/
         ?a. src k = SOME a /\ a < hi /\ tag x a = SOME(l,origin))) /\
      (!k. boolean y k ==> k < hj /\
         (bnew k \/ ?a. src k = SOME a /\ a < hi /\ boolean x a))
    ) ==>
  case EL (pc x) p of
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
  | AsmOp name => ^op_flow p name hi hj (tag x) (tag y) (boolean x) (boolean y)
  | _ => F``;

val fixed_open = ``
  \p cc req (V:(num#num)->bool) X (rank:(num#num)->num) pc height need tag boolean edge.
  !shp. shp = (^fixed_shape p cc req pc height need tag boolean) ==>
  !target. target = (\x y.
    ?l origin off. tag x 0 = SOME(l,origin) /\
      FLOOKUP (SND(compute_label_offsets p)) l = SOME off /\
      off < dimword(:256) /\
      FLOOKUP (build_offset_to_pc p) off = SOME(pc y)) ==>
    FINITE V /\ X SUBSET V /\
    (!x. x IN V ==> ?t. shp x t) /\
    (!x. x IN V DIFF X ==> pc x < LENGTH p) /\
    (!x y. edge x y ==>
       x IN V DIFF X /\ y IN V /\ rank y < rank x /\
       ^fixed_flow p pc height tag boolean x y /\
       (if EL (pc x) p = AsmOp "JUMP" then target x y
        else if EL (pc x) p = AsmOp "JUMPI"
             then pc y = pc x+1 \/ target x y
        else pc y = pc x+1)) /\
    (!x t. x IN V DIFF X /\ shp x t ==>
       (?u. (asm_steps (SND(compute_label_offsets p)) (build_offset_to_pc p)
                    p 1 t = AsmRevert u \/
              asm_steps (SND(compute_label_offsets p)) (build_offset_to_pc p)
                    p 1 t = AsmFault u) /\ u.as_requests=req) \/
       (?y u. edge x y /\
          asm_steps (SND(compute_label_offsets p)) (build_offset_to_pc p)
            p 1 t = AsmOK u /\ shp y u))``;

val fixed_next = ``
  \(V:(num#num) -> bool) (rank:(num#num) -> num) (pc:(num#num) -> num) height tag boolean edge
    (shp:(num#num) -> asm_state -> bool) runstep x m H f.
    m <= height x /\
    ?y. edge x y /\ y IN V /\ rank y < rank x /\ pc y = pc x+1 /\
        height y = H (height x) /\ ^pull_demands height tag boolean x y f /\
        !t. shp x t ==> ?u. runstep t = AsmOK u /\ shp y u``;

Triviality fixed_open_next:
  !shp. shp = (^fixed_shape p cc req pc height need tag boolean) ==>
  !runstep. runstep = asm_steps (SND(compute_label_offsets p)) (build_offset_to_pc p) p 1 ==>
    ^fixed_open p cc req V {} rank pc height need tag boolean edge ==>
    !name m H f x.
      MEM (name,m,H,f) ^fixed_rows /\ x IN V /\ EL (pc x) p = AsmOp name ==>
      ^fixed_next V rank pc height tag boolean edge shp runstep x m H f
Proof
  SIMP_TAC bool_ss [LET_THM, DIFF_EMPTY] >> strip_tac >> rpt gen_tac >> strip_tac >>
  MATCH_MP_TAC (SIMP_RULE bool_ss [LET_THM] fixed_source_next) >>
  simp[] >> conj_tac >-
    (gen_tac >> disch_tac >>
     qpat_assum `!v t. v IN V /\ _ ==> _` (qspecl_then [`x`,`t`] mp_tac) >>
     impl_tac >- (conj_tac >> first_assum ACCEPT_TAC) >> disch_then ACCEPT_TAC) >>
  gen_tac >> disch_tac >>
  qpat_assum `!v w. edge v w ==> _` (qspecl_then [`x`,`y`] mp_tac) >>
  impl_tac >- first_assum ACCEPT_TAC >>
  disch_then (strip_assume_tac o REWRITE_RULE [asm_inst_case_def]) >> gvs[]
QED

val fixed_visit = ``
  \(V:(num#num)->bool) (rank:(num#num)->num) (pc:(num#num)->num)
    edge (shp:(num#num)->asm_state->bool) runstep v b n path.
    path 0 = v /\ (!i. i<=n ==> path i IN V /\ pc(path i)=b+i) /\
    (!i. i<n ==> edge (path i) (path(SUC i)) /\ rank(path(SUC i)) < rank(path i)) /\
    (!t. shp v t ==> ?run. run 0=t /\ !i. i<n ==>
      runstep (run i) = AsmOK(run(SUC i)) /\ shp (path(SUC i)) (run(SUC i)))``;

(* Record the height transitions along the selected path. This retains the
   intermediate minima needed by windows with more than one stack action. *)
val fixed_height_trace = ``
  \(height:(num#num)->num) path
    (rows:(string#num#(num->num)#(num->num)) list).
    !i. i < LENGTH rows ==>
      FST(SND(EL i rows)) <= height(path i) /\
      height(path(SUC i)) = FST(SND(SND(EL i rows))) (height(path i))``;

val fixed_compose_slots = ``
  FOLDR (\(r:string#num#(num->num)#(num->num)) g. SND(SND(SND r)) o g) I``;

Triviality fixed_walk_rows:
  (!x. x IN V ==> ^pull_demands height tag boolean x x I) /\
  (!name m H f x.
    MEM (name,m,H,f) ^fixed_rows /\ x IN V /\ EL (pc x) p = AsmOp name ==>
    ^fixed_next V rank pc height tag boolean edge shp runstep x m H f) ==>
  !rows x b.
    EVERY (\r. MEM r ^fixed_rows) rows /\ x IN V /\ pc x=b /\
    (!i. i<LENGTH rows ==> EL (b+i) p=AsmOp (FST (EL i rows))) ==>
    ?path. ^fixed_visit V rank pc edge shp runstep x b (LENGTH rows) path /\
           ^fixed_height_trace height path rows /\
           ^pull_demands height tag boolean x (path (LENGTH rows)) (^fixed_compose_slots rows)
Proof
  SIMP_TAC bool_ss [] >> strip_tac >> Induct
  >- (simp[] >> rpt gen_tac >> strip_tac >> qexists `\i. x` >> simp[] >>
      rpt strip_tac >> qexists `\i. t` >> simp[])
  >> qx_gen_tac `h` >> PairCases_on `h` >>
  SIMP_TAC bool_ss [LENGTH, EVERY_DEF, FOLDR, FST, SND] >> rpt gen_tac >> strip_tac >>
  `EL (pc x) p = AsmOp h0` by
    (qpat_assum `!i. i < SUC (LENGTH rows) ==> _`
       (qspec_then `0:num` (ACCEPT_TAC o SIMP_RULE bool_ss [ADD_CLAUSES, prim_recTheory.LESS_0, EL, HD, FST]))) >>
  qpat_assum `!name m H f x. _ ==> _`
    (qspecl_then [`h0`,`h1`,`h2`,`h3`,`x`] mp_tac) >>
  impl_tac >- asm_rewrite_tac [] >> strip_tac >>
  qpat_x_assum `!x. _ ==> ?path. _` (qspec_then `y` mp_tac) >>
  impl_tac >-
    (asm_rewrite_tac [] >> gen_tac >> disch_tac >>
     `pc x + 1 + i = pc x + SUC i` by decide_tac >>
     pop_assum SUBST1_TAC >>
     qpat_assum `!i. i < SUC (LENGTH rows) ==> _`
       (qspec_then `SUC i` (mp_tac o SIMP_RULE bool_ss [LESS_MONO_EQ, EL, TL])) >>
     asm_rewrite_tac []) >>
  BETA_TAC >> strip_tac >>
  qexists `\i. if i=0 then x else path (PRE i)` >>
  simp[] >> conj_tac >-
    (conj_tac >-
       (gen_tac >> Cases_on `i` >- simp[] >>
        ASM_SIMP_TAC bool_ss [SUC_NOT_ZERO, prim_recTheory.PRE, LESS_EQ_MONO] >> disch_tac >>
        qpat_assum `!i. i <= LENGTH rows ==> _` (qspec_then `n` mp_tac) >>
        impl_tac >- first_assum ACCEPT_TAC >> strip_tac >>
        asm_rewrite_tac [] >> decide_tac) >>
     conj_tac >-
       (gen_tac >> Cases_on `i` >- simp[] >>
        ASM_SIMP_TAC bool_ss [SUC_NOT_ZERO, prim_recTheory.PRE, LESS_MONO_EQ] >>
        first_assum ACCEPT_TAC) >>
     gen_tac >> disch_tac >>
     qpat_assum `!t. shp x t ==> _` (drule_then strip_assume_tac) >>
     qpat_assum `!t. shp y t ==> _`
       (drule_then (qx_choose_then `suffix` strip_assume_tac)) >>
     qexists `\i. if i=0 then t else suffix (PRE i)` >> simp[] >>
     gen_tac >> Cases_on `i` >- simp[] >>
     ASM_SIMP_TAC bool_ss [SUC_NOT_ZERO, prim_recTheory.PRE, LESS_MONO_EQ] >>
     first_assum ACCEPT_TAC) >>
  conj_tac >-
    (gen_tac >> Cases_on `i` >- simp[EL] >>
     ASM_SIMP_TAC bool_ss [SUC_NOT_ZERO, prim_recTheory.PRE, LESS_MONO_EQ, EL, TL] >>
     first_assum ACCEPT_TAC) >>
  rpt strip_tac >>
  qpat_assum `!k. ( (!l org. tag (path (LENGTH rows)) k = _ ==> _) /\ _)`
    (qspec_then `k` strip_assume_tac) >>
  qmatch_asmsub_abbrev_tac `tag y j = SOME (l,org)` >>
  qpat_assum `!k. ((!l org. tag y k = _ ==> _) /\ _)`
    (qspec_then `j` strip_assume_tac) >>
  metis_tac[]
QED

(* Supply the path induction with Open's identity and single-edge cases,
   and fetch each row from its occurrence in the source window. *)
Triviality fixed_walk_window:
  !shp. shp = (^fixed_shape p cc req pc height need tag boolean) ==>
  !runstep. runstep = asm_steps (SND(compute_label_offsets p)) (build_offset_to_pc p) p 1 ==>
    ^fixed_open p cc req V {} rank pc height need tag boolean edge ==>
    !rows v pre tail.
      EVERY (\r. MEM r ^fixed_rows) rows /\ v IN V /\ pc v=LENGTH pre /\
      p=pre++MAP (AsmOp o FST) rows++tail ==>
      ?path. ^fixed_visit V rank pc edge shp runstep v (LENGTH pre) (LENGTH rows) path /\
             ^fixed_height_trace height path rows /\
             ^pull_demands height tag boolean v (path (LENGTH rows)) (^fixed_compose_slots rows)
Proof
  SIMP_TAC bool_ss [LET_THM] >>
  disch_then (fn th => assume_tac th >>
    assume_tac (MATCH_MP (SIMP_RULE bool_ss [LET_THM] fixed_open_next) th)) >>
  `!x. x IN V ==> ^pull_demands height tag boolean x x I` by
    (BETA_TAC >> gen_tac >> disch_tac >>
     qpat_assum `FINITE V /\ _`
       (qspec_then `x` mp_tac o cj 3) >>
     impl_tac >- first_assum ACCEPT_TAC >>
     disch_then strip_assume_tac >>
     qpat_x_assum `FINITE V /\ _` kall_tac >>
     simp[combinTheory.I_THM] >> metis_tac[]) >>
  qpat_x_assum `FINITE V /\ _` kall_tac >>
  rpt gen_tac >> strip_tac >>
  mp_tac (BETA_RULE (Q.INST
    [`shp` |-> `^fixed_shape p cc req pc height need tag boolean`,
     `runstep` |-> `asm_steps (SND(compute_label_offsets p)) (build_offset_to_pc p) p 1`]
    fixed_walk_rows)) >>
  impl_tac >-
    (conj_tac >- (RULE_ASSUM_TAC (SIMP_RULE bool_ss []) >> asm_rewrite_tac []) >>
     BETA_TAC >> first_assum ACCEPT_TAC) >>
  disch_then (qspecl_then [`rows`,`v`,`LENGTH pre`] mp_tac) >>
  impl_tac >-
    (asm_rewrite_tac [] >> gen_tac >> disch_tac >>
     simp[EL_APPEND_EQN, EL_MAP]) >>
  (simp[])
QED

val fixed_window_result = ``
  \p pre V rank pc height tag boolean edge shp runstep v names minH Hout f.
    !w tail. w = MAP AsmOp names /\ p = pre ++ w ++ tail ==>
      minH <= height v /\
      ?path. ^fixed_visit V rank pc edge shp runstep v (LENGTH pre) (LENGTH w) path /\
             height (path (LENGTH w)) = Hout /\
             ^pull_demands height tag boolean v (path (LENGTH w)) f``;

val dup_swap2_swap1_rows = ``
  [("DUP1",1:num,(\h:num. h+1),(\k:num. if k=0 then 0 else k-1));
   ("SWAP2",3,I,(\k. if k=0 then 2 else if k=2 then 0 else k));
   ("SWAP1",2,I,(\k. if k=0 then 1 else if k=1 then 0 else k))]``;

Theorem stack_fixed_source_demand_paths:
  !shp. shp = (^fixed_shape p cc req pc height need tag boolean) ==>
  !runstep. runstep = asm_steps (SND(compute_label_offsets p)) (build_offset_to_pc p) p 1 ==>
  !result. result = (^fixed_window_result p pre V rank pc height tag boolean edge shp runstep v) ==>
  !h. h = height v ==>
    ^fixed_open p cc req V {} rank pc height need tag boolean edge /\
    v IN V /\ pc v = LENGTH pre ==>
    result ["DUP1";"SWAP2";"SWAP1"] 2 (h+1)
      (\k. if k<2 then k else if k=2 then 0 else k-1) /\
    result ["DUP1";"SWAP1";"POP"] 1 h I /\
    result ["SWAP1";"POP";"POP"] 2 (h-2) (\k. k+2) /\
    result ["DUP1";"SWAP1"] 1 (h+1) (\k. if k=0 then 0 else k-1)
Proof
  SIMP_TAC bool_ss [LET_THM] >>
  disch_then (CONJUNCTS_THEN2
    (assume_tac o MATCH_MP (SIMP_RULE bool_ss [LET_THM] fixed_walk_window))
    strip_assume_tac) >>
  conj_tac >-
  (qx_gen_tac `tail` >> disch_tac >>
   qpat_assum `!rows v pre tail. EVERY _ rows /\ _ ==> ?path. _`
     (qspecl_then [`^dup_swap2_swap1_rows`,`v`,`pre`,`tail`] mp_tac) >>
   impl_tac >- simp[EVERY_DEF, MAP, MEM, combinTheory.o_DEF] >>
   disch_then (qx_choose_then `path`
     (CONJUNCTS_THEN2 (mk_asm "visit")
       (CONJUNCTS_THEN2 (mk_asm "trace") (mk_asm "pull")))) >>
   map_every (fn i => asm "trace" (qspec_then i
     (strip_assume_tac o SIMP_RULE (boss_ss()) [EL, EL_CONS, ADD1])))
     [`0:num`,`1:num`,`2:num`] >>
   asm "visit" (assume_tac o CONJUNCT1) >>
   conj_tac >-
     (qpat_x_assum `3 <= height (path 1)` mp_tac >> simp[] >> decide_tac) >>
   qexists `path` >>
   conj_tac >-
     (SIMP_TAC (boss_ss()) [MAP, combinTheory.o_DEF] >>
      asm "visit" (ACCEPT_TAC o SIMP_RULE (boss_ss()) [MAP, combinTheory.o_DEF])) >>
   conj_tac >- simp[] >>
   `^fixed_compose_slots ^dup_swap2_swap1_rows =
      (\k. if k<2 then k else if k=2 then 0 else k-1)` by
     (POP_ASSUM_LIST (K ALL_TAC) >>
      simp[FUN_EQ_THM, FOLDR, combinTheory.o_DEF, combinTheory.I_THM] >>
      qx_gen_tac `k` >>
      rpt (COND_CASES_TAC >> fs[]) >>
      POP_ASSUM_LIST (map_every mp_tac) >> decide_tac) >>
   asm "pull" (mp_tac o ASM_REWRITE_RULE []) >> simp[]) >>
  conj_tac >-
  (qx_gen_tac `tail` >> disch_tac >>
   qpat_assum `!rows v pre tail. EVERY _ rows /\ _ ==> ?path. _`
     (qspecl_then [`[("DUP1",1:num,(\h:num. h+1),(\k:num. if k=0 then 0 else k-1));
                     ("SWAP1",2,I,(\k. if k=0 then 1 else if k=1 then 0 else k));
                     ("POP",1,(\h. h-1),(\k. k+1))]`,`v`,`pre`,`tail`] mp_tac) >>
   impl_tac >- simp[EVERY_DEF, MAP, MEM, combinTheory.o_DEF] >>
   disch_then (qx_choose_then `path`
     (CONJUNCTS_THEN2 (mk_asm "visit")
       (CONJUNCTS_THEN2 (mk_asm "trace") (mk_asm "pull")))) >>
   map_every (fn i => asm "trace" (qspec_then i
     (strip_assume_tac o SIMP_RULE (boss_ss()) [EL, EL_CONS, ADD1])))
     [`0:num`,`1:num`,`2:num`] >>
   asm "visit" (assume_tac o CONJUNCT1) >>
   conj_tac >-
     (qpat_x_assum `path 0 = v` SUBST_ALL_TAC >> first_assum ACCEPT_TAC) >>
   qexists `path` >>
   conj_tac >-
     (SIMP_TAC (boss_ss()) [MAP, combinTheory.o_DEF] >>
      asm "visit" (ACCEPT_TAC o SIMP_RULE (boss_ss()) [MAP, combinTheory.o_DEF])) >>
   conj_tac >- simp[] >>
   `^fixed_compose_slots
      [("DUP1",1:num,(\h:num. h+1),(\k:num. if k=0 then 0 else k-1));
       ("SWAP1",2,I,(\k. if k=0 then 1 else if k=1 then 0 else k));
       ("POP",1,(\h. h-1),(\k. k+1))] = I` by
     (POP_ASSUM_LIST (K ALL_TAC) >>
      simp[FUN_EQ_THM, FOLDR, combinTheory.o_DEF, combinTheory.I_THM] >>
      qx_gen_tac `k` >>
      rpt (COND_CASES_TAC >> fs[]) >>
      POP_ASSUM_LIST (map_every mp_tac) >> decide_tac) >>
   asm "pull" (mp_tac o ASM_REWRITE_RULE []) >> simp[]) >>
  conj_tac >-
  (qx_gen_tac `tail` >> disch_tac >>
   qpat_assum `!rows v pre tail. EVERY _ rows /\ _ ==> ?path. _`
     (qspecl_then [`[("SWAP1",2:num,I:num->num,(\k:num. if k=0 then 1 else if k=1 then 0 else k));
                     ("POP",1,(\h. h-1),(\k. k+1));
                     ("POP",1,(\h. h-1),(\k. k+1))]`,`v`,`pre`,`tail`] mp_tac) >>
   impl_tac >- simp[EVERY_DEF, MAP, MEM, combinTheory.o_DEF] >>
   disch_then (qx_choose_then `path`
     (CONJUNCTS_THEN2 (mk_asm "visit")
       (CONJUNCTS_THEN2 (mk_asm "trace") (mk_asm "pull")))) >>
   map_every (fn i => asm "trace" (qspec_then i
     (strip_assume_tac o SIMP_RULE (boss_ss()) [EL, EL_CONS, ADD1])))
     [`0:num`,`1:num`,`2:num`] >>
   asm "visit" (assume_tac o CONJUNCT1) >>
   conj_tac >-
     (qpat_x_assum `path 0 = v` SUBST_ALL_TAC >> first_assum ACCEPT_TAC) >>
   qexists `path` >>
   conj_tac >-
     (SIMP_TAC (boss_ss()) [MAP, combinTheory.o_DEF] >>
      asm "visit" (ACCEPT_TAC o SIMP_RULE (boss_ss()) [MAP, combinTheory.o_DEF])) >>
   conj_tac >-
     (`!h:num. (h-1)-1 = h-2` by decide_tac >> simp[]) >>
   `^fixed_compose_slots
      [("SWAP1",2:num,I:num->num,(\k:num. if k=0 then 1 else if k=1 then 0 else k));
       ("POP",1,(\h. h-1),(\k. k+1));
       ("POP",1,(\h. h-1),(\k. k+1))] = (\k. k+2)` by
     (POP_ASSUM_LIST (K ALL_TAC) >>
      simp[FUN_EQ_THM, FOLDR, combinTheory.o_DEF, combinTheory.I_THM, ADD_ASSOC]) >>
   asm "pull" (mp_tac o ASM_REWRITE_RULE []) >> simp[]) >>
  qx_gen_tac `tail` >> disch_tac >>
  qpat_assum `!rows v pre tail. EVERY _ rows /\ _ ==> ?path. _`
    (qspecl_then [`[("DUP1",1:num,(\h:num. h+1),(\k:num. if k=0 then 0 else k-1));
                    ("SWAP1",2,I,(\k. if k=0 then 1 else if k=1 then 0 else k))]`,
                  `v`,`pre`,`tail`] mp_tac) >>
  impl_tac >- simp[EVERY_DEF, MAP, MEM, combinTheory.o_DEF] >>
  disch_then (qx_choose_then `path`
    (CONJUNCTS_THEN2 (mk_asm "visit")
      (CONJUNCTS_THEN2 (mk_asm "trace") (mk_asm "pull")))) >>
  map_every (fn i => asm "trace" (qspec_then i
    (strip_assume_tac o SIMP_RULE (boss_ss()) [EL, EL_CONS, ADD1])))
    [`0:num`,`1:num`] >>
  asm "visit" (assume_tac o CONJUNCT1) >>
  conj_tac >-
    (qpat_x_assum `path 0 = v` SUBST_ALL_TAC >> first_assum ACCEPT_TAC) >>
  qexists `path` >>
  conj_tac >-
    (SIMP_TAC (boss_ss()) [MAP, combinTheory.o_DEF] >>
     asm "visit" (ACCEPT_TAC o SIMP_RULE (boss_ss()) [MAP, combinTheory.o_DEF])) >>
  conj_tac >- simp[] >>
  `^fixed_compose_slots
     [("DUP1",1:num,(\h:num. h+1),(\k:num. if k=0 then 0 else k-1));
      ("SWAP1",2,I,(\k. if k=0 then 1 else if k=1 then 0 else k))] =
     (\k. if k=0 then 0 else k-1)` by
    (POP_ASSUM_LIST (K ALL_TAC) >>
     simp[FUN_EQ_THM, FOLDR, combinTheory.o_DEF, combinTheory.I_THM] >>
     qx_gen_tac `k` >>
     rpt (COND_CASES_TAC >> fs[]) >>
     POP_ASSUM_LIST (map_every mp_tac) >> decide_tac) >>
  asm "pull" (mp_tac o ASM_REWRITE_RULE []) >> simp[]
QED
