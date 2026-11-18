Theory staticAbortOptStackCommCut
Ancestors
  staticAbortOptStackStopped staticAbortOptStackCommRow asmOptPeephole
  staticAbortOptPruneUnreachableLayout asmSymBridge asmWf asmSplice
  staticAbortStraight asmOptimizer asmSymSem asmSem asmIR symbolResolve
  vyperArith alist list rich_list pred_set arithmetic words pair option finite_map

(* The interior stop uses the shared head; the only executed source
   instruction between that head and the cut is SWAP1. *)
Theorem commcut_replay_head[local]:
  let p = pre ++ [AsmOp "SWAP1";a] ++ tail;
      q = pre ++ [a] ++ tail; b = LENGTH pre in
  asm_static_wf p /\ asm_commutative_op a /\ s.as_pc=0 /\
  sym_steps p env n (sym_init s) = SymOK ss /\ ss.sym_base.as_pc=b+1 ==>
  ?j u. sym_steps q env j (sym_init s)=SymOK u /\ u.sym_base.as_pc=b /\
    u.sym_base.as_call_ctx=ss.sym_base.as_call_ctx /\
    u.sym_base.as_requests=ss.sym_base.as_requests /\
    LENGTH u.sym_stack=LENGTH ss.sym_stack /\ 2<=LENGTH u.sym_stack /\
    !k. 2<=k ==> EL k u.sym_stack=EL k ss.sym_stack
Proof
  SIMP_TAC bool_ss [LET_THM] >> strip_tac >>
  mp_tac (Q.SPECL [`pre`,`[AsmOp "SWAP1";a]`,`[a]`,`tail`,`env`,`s`,`n`,`ss`]
                   stack_peephole_one_stopped_prefix) >>
  simp[] >> rpt strip_tac >>
  qexistsl [`j`,`u`] >> simp[] >>
  qpat_x_assum `sym_steps _ _ 1 u = _` mp_tac >>
  `u.sym_base.as_pc < LENGTH (pre ++ [AsmOp "SWAP1";a] ++ tail) /\
   EL u.sym_base.as_pc (pre ++ [AsmOp "SWAP1";a] ++ tail) = AsmOp "SWAP1"`
    by simp[EL_APPEND_EQN] >>
  `sym_step (pre ++ [AsmOp "SWAP1";a] ++ tail) env (AsmOp "SWAP1") u =
     sym_swap 1 u` by simp[sym_step_def, sym_step_op_def, dup_table_def, swap_table_def] >>
  simp[sym_steps_pos, sym_steps_def, sym_swap_def] >>
  namedCases_on `u.sym_stack` ["", "x stk"] >> simp[] >>
  namedCases_on `stk` ["", "y rest"] >>
  simp[sym_set_stack_def, asm_next_def, LUPDATE_compute] >> rpt strip_tac >> gvs[] >>
  `?i. k=SUC (SUC i)` by (qexists `k-2` >> decide_tac) >> gvs[]
QED

Theorem commcut_swap1_step[local]:
  t.as_pc < LENGTH p /\ EL t.as_pc p = AsmOp "SWAP1" /\
  t.as_stack = x::y::stk ==>
  asm_steps lo opcs p 1 t =
    AsmOK (t with <|as_pc := t.as_pc+1; as_stack := y::x::stk|>)
Proof
  strip_tac >> rewrite_tac[numLib.num_CONV ``1:num``] >>
  `asm_step lo opcs (AsmOp "SWAP1") t = asm_swap 1 t` by
    CONV_TAC (computeLib.RESTR_EVAL_CONV [``asm_swap``]) >>
  simp[asm_steps_def, asm_swap_def, asm_next_def, LUPDATE_compute, asm_state_fupdcanon]
QED

Theorem commcut_relocate_slot[local]:
  let b = LENGTH pre; p = pre ++ [AsmOp "SWAP1";a] ++ tail;
      q = pre ++ [a] ++ tail in
  let f = splice_pc b 2 1 in
  asm_static_wf p /\ asm_commutative_op a /\ org < LENGTH p /\
  (EL org p=AsmPushLabel l \/ EL org p=AsmPushOfst l 0) /\
  FLOOKUP (SND (compute_label_offsets p)) l = SOME old /\
  FLOOKUP (build_offset_to_pc p) old = SOME dest ==>
  f org < LENGTH q /\
  (EL (f org) q=AsmPushLabel l \/ EL (f org) q=AsmPushOfst l 0) /\
  ?off dest'. FLOOKUP (SND (compute_label_offsets q)) l = SOME off /\
    off < dimword(:256) /\ FLOOKUP (build_offset_to_pc q) off = SOME dest'
Proof
  simp[LET_THM] >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `?nm. a=AsmOp nm` by (Cases_on `a` >> fs[asm_commutative_op_def]) >> gvs[] >>
  qabbrev_tac `p = pre ++ [AsmOp "SWAP1";AsmOp nm] ++ tail` >>
  qabbrev_tac `q = pre ++ [AsmOp nm] ++ tail` >>
  `org <> LENGTH pre /\ org <> LENGTH pre+1` by
    (rpt strip_tac >> gvs[Abbr `p`, EL_APPEND_EQN]) >>
  `splice_pc (LENGTH pre) 2 1 org < LENGTH q /\
   EL (splice_pc (LENGTH pre) 2 1 org) q = EL org p` by
    (mp_tac (Q.INST [`pfx` |-> `pre`, `pat` |-> `[AsmOp "SWAP1";AsmOp nm]`,
                    `repl` |-> `[AsmOp nm]`, `sfx` |-> `tail`, `i` |-> `org`]
              (INST_TYPE [alpha |-> ``:asm_inst``] splice_fetch)) >>
     simp[Abbr `p`, Abbr `q`] >> decide_tac) >>
  `LENGTH q = LENGTH pre + (LENGTH tail + 1)` by simp[Abbr `q`] >>
  simp[] >>
  `asm_static_wf q` by
    (mp_tac (Q.INST [`pfx` |-> `pre`, `pat` |-> `[AsmOp "SWAP1";AsmOp nm]`,
                    `repl` |-> `[AsmOp nm]`, `sfx` |-> `tail`] asm_splice_static_wf) >>
     simp[Abbr `p`, Abbr `q`, asm_splice_ok_def, is_data_inst_def, asm_inst_size_def,
          asm_label_refs_def]) >>
  drule_all lookup_pair_code_label_index >> strip_tac >>
  `MEM (AsmLabel l) p` by metis_tac[INDEX_OF_eq_NONE, optionTheory.NOT_NONE_SOME] >>
  `MEM (AsmLabel l) q` by fs[Abbr `p`, Abbr `q`] >>
  Cases_on `INDEX_OF (AsmLabel l) q` >> fs[INDEX_OF_eq_NONE] >>
  drule_all (Q.INST [`p` |-> `q`] asm_static_wf_code_label) >> strip_tac >>
  `off < dimword(:256)` by
    (irule lt_dimword_256 >> qexists `16` >> simp[]) >>
  qexistsl [`off`,`x`] >> simp[]
QED

Theorem commcut_swap_slots[local]:
  EL k (y::x::stk) = EL (if k=0 then 1 else if k=1 then 0 else k) (x::y::stk)
Proof
  namedCases_on `k` ["", "n"] >> simp[] >> Cases_on `n` >> simp[]
QED

Theorem commcut_split_two[local]:
  2 <= LENGTH stk ==> ?x y rest. stk = x::y::rest
Proof
  namedCases_on `stk` ["", "x xs"] >> simp[] >> Cases_on `xs` >> simp[]
QED

Theorem commcut_fresh_vertex[local]:
  FINITE (V:(num#num)->bool) ==> ?v. v NOTIN V
Proof
  strip_tac >> qexists `(SUC (MAX_SET (IMAGE FST V)),0)` >> strip_tac >>
  `SUC (MAX_SET (IMAGE FST V)) IN IMAGE FST V` by
    (simp[IN_IMAGE] >> qexists `(SUC (MAX_SET (IMAGE FST V)),0)` >> simp[]) >>
  `FINITE (IMAGE FST V)` by simp[] >>
  drule_all (MP_CANON MAX_SET_PROPERTY) >> simp[]
QED

Theorem stack_comm_strict_endpoint_row:
!pre a tail env s n ss cc req V rank pc height need tag boolean edge e.
let p = pre ++ [AsmOp "SWAP1";a] ++ tail;
    q = pre ++ [a] ++ tail; b = LENGTH pre in
let Shape =
  \p cc req pc height need tag boolean i (t:asm_state).
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
in
let Flow =
  \p pc height tag boolean (x:num#num) (y:num#num).
  let hi = height x; hj = height y; ins = EL (pc x) p in
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
             (\k. k=0 /\ m=1 /\ asm_returns_zero_or_one ins /\
               !t u. LENGTH t.as_stack=hi /\
                 asm_step (SND(compute_label_offsets p)) (build_offset_to_pc p)
                   ins t = AsmOK u ==>
                 (EL 0 u.as_stack=0w \/ EL 0 u.as_stack=1w)))
  | _ => F
in
let Open =
  \p cc req (V:(num#num)->bool) X (rank:(num#num)->num) pc height need
    (tag:(num#num)->num->(string#num)option)
    (boolean:(num#num)->num->bool) edge.
  let LiveShape = Shape p cc req pc height need tag boolean in
  let target = \x y.
    ?l origin off. tag x 0 = SOME(l,origin) /\
      FLOOKUP (SND(compute_label_offsets p)) l = SOME off /\
      off < dimword(:256) /\
      FLOOKUP (build_offset_to_pc p) off = SOME(pc y)
  in
    FINITE V /\ X SUBSET V /\
    (!x. x IN V ==> ?t. LiveShape x t) /\
    (!x. x IN V DIFF X ==> pc x < LENGTH p) /\
    (!x y. edge x y ==>
       x IN V DIFF X /\ y IN V /\ rank y < rank x /\
       Flow p pc height tag boolean x y /\
       (if EL (pc x) p = AsmOp "JUMP" then target x y
        else if EL (pc x) p = AsmOp "JUMPI"
             then pc y = pc x+1 \/ target x y
        else pc y = pc x+1)) /\
    (!x t. x IN V DIFF X /\ LiveShape x t ==>
       (?u. (asm_steps (SND(compute_label_offsets p)) (build_offset_to_pc p)
                    p 1 t = AsmRevert u \/
              asm_steps (SND(compute_label_offsets p)) (build_offset_to_pc p)
                    p 1 t = AsmFault u) /\ u.as_requests=req) \/
       (?y u. edge x y /\
          asm_steps (SND(compute_label_offsets p)) (build_offset_to_pc p)
            p 1 t = AsmOK u /\ LiveShape y u))
in
let J0 = \ss tag boolean (e:num#num).
  (!k l origin. tag e k=SOME(l,origin) ==>
     k<LENGTH ss.sym_stack /\ EL k ss.sym_stack=Lab l 0) /\
  (!k. boolean e k ==>
     k<LENGTH ss.sym_stack /\ (EL k ss.sym_stack=Val 0w \/ EL k ss.sym_stack=Val 1w))
in
let Slots = \p height tag boolean (e:num#num).
  (!k. boolean e k ==> k < height e /\ tag e k=NONE) /\
  (!k l origin. tag e k = SOME(l,origin) ==>
     k < height e /\ origin < LENGTH p /\
     (EL origin p = AsmPushLabel l \/ EL origin p = AsmPushOfst l 0) /\
     ?off dest. FLOOKUP (SND(compute_label_offsets p)) l = SOME off /\
       off < dimword(:256) /\ FLOOKUP (build_offset_to_pc p) off = SOME dest)
in
let f = splice_pc b 2 1 in
let Tg = \x k. OPTION_MAP (\(l,org). (l,f org)) (tag x k) in
asm_static_wf p /\ asm_commutative_op a /\ s.as_pc=0 /\
sym_steps p env n (sym_init s)=SymOK ss /\ e IN V /\
pc e=ss.sym_base.as_pc /\ pc e=b+1 /\
LENGTH ss.sym_stack=height e /\ ss.sym_base.as_call_ctx=cc /\ ss.sym_base.as_requests=req /\
Open p cc req V {} rank pc height need tag boolean edge /\
J0 ss tag boolean e /\ Slots p height tag boolean e ==>
?j u z name.
  let P = \x:num#num. b+FST x in
  let H = \x:num#num. if FST x=0 then height e else height z in
  let Tag = \x:num#num k. if FST x=0 then (if k<2 then NONE else Tg e k) else Tg z k in
  let Bool = \x:num#num k. if FST x=0 then (2<=k /\ boolean e k) else boolean z k in
  sym_steps q env j (sym_init s)=SymOK u /\ u.sym_base.as_pc=b /\
  u.sym_base.as_call_ctx=cc /\ u.sym_base.as_requests=req /\
  LENGTH u.sym_stack=height e /\ 2<=height e /\
  J0 u Tag Bool (0,0) /\ Slots q H Tag Bool (0,0) /\
  a=AsmOp name /\ edge e z /\ z IN V /\ pc z=b+2 /\ rank z<rank e /\
  height z=height e-1 /\ P (0,0)<LENGTH q /\
  EL (P (0,0)) q=AsmOp name /\ P (1,0)=P (0,0)+1 /\ P (1,0)=f (pc z) /\
  ALOOKUP dup_table name=NONE /\ ALOOKUP swap_table name=NONE /\
  static_abort_straight name 1 /\ asm_op_arity name=2 /\
  Flow q P H Tag Bool (0,0) (1,0) /\
  (!e' t. asm_sym_rel q e' t u /\ t.as_call_ctx=cc /\ t.as_requests=req ==>
       Shape q cc req P H (\x. F) Tag Bool (0,0) t)
Proof
  rpt gen_tac >>
  map_every (fn name =>
    CONV_TAC (REWR_CONV combinTheory.LET_FORALL_ELIM THENC
      SIMP_CONV bool_ss [combinTheory.S_DEF, combinTheory.o_THM, combinTheory.C_DEF]) >>
    qx_gen_tac name >> disch_tac)
    [`p`,`q`,`b`,`Shape`,`Flow`,`Open`,`J0`,`Slots`,`f`,`Tg`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `?j u. sym_steps q env j (sym_init s)=SymOK u /\ u.sym_base.as_pc=b /\
        u.sym_base.as_call_ctx=cc /\ u.sym_base.as_requests=req /\
        LENGTH u.sym_stack=height e /\ 2<=height e /\
        !k. 2<=k ==> EL k u.sym_stack=EL k ss.sym_stack` by
    suspend "prefix" >>
  `b < LENGTH p /\ EL b p = AsmOp "SWAP1"`
    by simp[Abbr `p`, Abbr `b`, EL_APPEND_EQN] >>
  qpat_assum `Abbrev (Open = _)` (fn ab =>
    qpat_assum `Open p cc req V {} rank pc height need tag boolean edge`
      (mp_tac o SIMP_RULE bool_ss [REWRITE_RULE [markerTheory.Abbrev_def] ab,
                                  LET_THM, DIFF_EMPTY, EMPTY_SUBSET])) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule commcut_fresh_vertex >> disch_then (qx_choose_then `v` assume_tac) >>
  qabbrev_tac `src = \k:num. if k=0 then 1 else if k=1 then 0 else k` >>
  qabbrev_tac `pc1 = \x. if x=v then b else pc x` >>
  qabbrev_tac `h1 = \x. if x=v then height e else height x` >>
  qabbrev_tac `n1 = \x. x<>v /\ need x` >>
  qabbrev_tac `tag1 = \x k. if x=v then tag e (src k) else tag x k` >>
  qabbrev_tac `B1 = \x k. if x=v then boolean e (src k) else boolean x k` >>
  qabbrev_tac `r1 = \x. if x=v then SUC (rank e) else rank x` >>
  qabbrev_tac `E1 = \x y. edge x y \/ (x=v /\ y=e)` >>
  qabbrev_tac `S1 = Shape p cc req pc1 h1 n1 tag1 B1` >>
  qabbrev_tac `S0 = Shape p cc req pc height need tag boolean` >>
  `e<>v` by metis_tac[] >>
  `!k. src (src k)=k /\ (src k < height e <=> k<height e)` by
    (gen_tac >> Cases_on `k=0` >> Cases_on `k=1` >> simp[Abbr `src`]) >>
  `!k x y stk. EL k (y::x::stk:bytes32 list) = EL (src k) (x::y::stk)`
    by (rpt gen_tac >>
        qpat_assum `Abbrev (src = _)` (SUBST1_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
        BETA_TAC >> MATCH_ACCEPT_TAC commcut_swap_slots) >>
  pop_assum (mk_asm "swap_slots") >>
  `!x t. x<>v ==> (S1 x t <=> S0 x t)` by
    simp[Abbr `S1`, Abbr `S0`, Abbr `Shape`, Abbr `pc1`, Abbr `h1`,
         Abbr `n1`, Abbr `tag1`, Abbr `B1`] >>
  `!x y. x<>v /\ y<>v ==>
        (Flow p pc1 h1 tag1 B1 x y <=> Flow p pc height tag boolean x y)` by
    (rpt gen_tac >> strip_tac >>
     ASM_SIMP_TAC bool_ss [LET_THM, Abbr `Flow`, Abbr `pc1`, Abbr `h1`, Abbr `tag1`, Abbr `B1`]) >>
  `?t. S0 e t` by (first_assum irule >> simp[]) >>
  `?t. S1 v t` by suspend "inhabit" >>
  `!t. S1 v t ==> ?t'.
        asm_steps (SND(compute_label_offsets p)) (build_offset_to_pc p) p 1 t = AsmOK t' /\
        S0 e t'` by suspend "step" >>
  `Open p cc req (v INSERT V) {} r1 pc1 h1 n1 tag1 B1 E1` by suspend "augment" >>
  `?z name.
     let P = \x:num#num. b+FST x in
     let H = \x:num#num. if FST x=0 then height e else height z in
     let Tag = \x:num#num k. if FST x=0 then (if k<2 then NONE else Tg e k) else Tg z k in
     let Bool = \x:num#num k. if FST x=0 then (2<=k /\ boolean e k) else boolean z k in
     a=AsmOp name /\ edge e z /\ z IN V /\ pc z=b+2 /\ rank z<rank e /\
     height z=height e-1 /\ P (0,0)<LENGTH q /\
     EL (P (0,0)) q=AsmOp name /\ P (1,0)=P (0,0)+1 /\
     ALOOKUP dup_table name=NONE /\ ALOOKUP swap_table name=NONE /\
     static_abort_straight name 1 /\ asm_op_arity name=2 /\
     Flow q P H Tag Bool (0,0) (1,0)` by suspend "row" >>
  suspend "root"
QED

Resume stack_comm_strict_endpoint_row[prefix]:
  `ss.sym_base.as_pc = LENGTH pre + 1` by
    (qpat_assum `pc e = ss.sym_base.as_pc` (SUBST1_TAC o SYM) >> simp[Abbr `b`]) >>
  qpat_x_assum `Abbrev (p = _)` (SUBST_ALL_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  drule_all (MP_CANON (SIMP_RULE bool_ss [LET_THM] commcut_replay_head)) >>
  simp[Abbr `q`, Abbr `b`] >>
  disch_then (qx_choosel_then [`j`,`u`] strip_assume_tac) >>
  qexistsl [`j`,`u`] >> simp[]
QED

Resume stack_comm_strict_endpoint_row[inhabit]:
  qpat_x_assum `S0 e t` mp_tac >>
  ASM_SIMP_TAC bool_ss [Abbr `S0`, Abbr `Shape`] >> strip_tac >>
  `2 <= LENGTH t.as_stack` by simp[] >>
  drule commcut_split_two >> disch_then (qx_choosel_then [`x`,`y`,`stk`] assume_tac) >>
  `LENGTH (y::x::stk) = height e` by
    (qpat_assum `t.as_stack = _` (fn eq =>
       qpat_assum `LENGTH t.as_stack = _` (mp_tac o REWRITE_RULE [eq])) >>
     SIMP_TAC bool_ss [LENGTH]) >>
  qexists `t with <|as_pc := b; as_stack := y::x::stk|>` >>
  simp[Abbr `S1`, Abbr `pc1`, Abbr `h1`, Abbr `n1`, Abbr `tag1`, Abbr `B1`] >>
  conj_tac
  >- (rpt gen_tac >> disch_tac >>
      qpat_assum `!k l origin. tag e k = _ ==> _`
        (qspecl_then [`src k`,`l`,`origin`] mp_tac) >>
      asm "swap_slots" (qspecl_then [`k`,`x`,`y`,`stk`] SUBST1_TAC) >>
      qpat_assum `t.as_stack = _` SUBST1_TAC >>
      simp[]) >>
  gen_tac >> disch_tac >>
  qpat_assum `!k. boolean e k ==> _` (qspec_then `src k` mp_tac) >>
  asm "swap_slots" (qspecl_then [`k`,`x`,`y`,`stk`] SUBST1_TAC) >>
  qpat_assum `t.as_stack = _` SUBST1_TAC >>
  simp[]
QED

Resume stack_comm_strict_endpoint_row[step]:
  `need e ==> cc.cc_static` by
    (qpat_assum `S0 e _` mp_tac >>
     SIMP_TAC bool_ss [Abbr `S0`, Abbr `Shape`] >>
     disch_then (map_every assume_tac o CONJUNCTS) >>
     disch_tac >> `t.as_call_ctx.cc_static` by (first_x_assum irule >> simp[]) >>
     qpat_assum `t.as_call_ctx = cc` SUBST_ALL_TAC >> simp[]) >>
  qx_gen_tac `w` >>
  simp[Abbr `S1`, Abbr `Shape`, Abbr `pc1`, Abbr `h1`, Abbr `n1`,
       Abbr `tag1`, Abbr `B1`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `2 <= LENGTH w.as_stack` by simp[] >>
  drule commcut_split_two >> disch_then (qx_choosel_then [`x`,`y`,`stk`] assume_tac) >>
  `LENGTH (y::x::stk) = height e` by
    (qpat_assum `w.as_stack = _` (fn eq =>
       qpat_assum `LENGTH w.as_stack = _` (mp_tac o REWRITE_RULE [eq])) >>
     SIMP_TAC bool_ss [LENGTH]) >>
  qexists `w with <|as_pc := w.as_pc+1; as_stack := y::x::stk|>` >>
  conj_tac >- (irule commcut_swap1_step >> simp[]) >>
  simp[Abbr `S0`] >>
  conj_tac
  >- (rpt gen_tac >> disch_tac >>
      qpat_assum `!k l origin. tag e (src k) = _ ==> _`
        (qspecl_then [`src k`,`l`,`origin`] mp_tac) >>
      asm "swap_slots" (qspecl_then [`k`,`x`,`y`,`stk`] SUBST1_TAC) >>
      qpat_assum `w.as_stack = _` SUBST1_TAC >> simp[]) >>
  gen_tac >> disch_tac >>
  qpat_assum `!k. boolean e (src k) ==> _` (qspec_then `src k` mp_tac) >>
  asm "swap_slots" (qspecl_then [`k`,`x`,`y`,`stk`] SUBST1_TAC) >>
  qpat_assum `w.as_stack = _` SUBST1_TAC >> simp[]
QED

Resume stack_comm_strict_endpoint_row[augment]:
  SIMP_TAC bool_ss [Abbr `Open`, LET_THM, DIFF_EMPTY, EMPTY_SUBSET, FINITE_INSERT] >>
  qpat_assum `Abbrev (S1 = _)`
    (rewrite_tac o single o GSYM o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  simp[] >>
  conj_tac
  >- (qx_gen_tac `x` >> Cases_on `x=v` >> simp[]
      >- (HINT_EXISTS_TAC >> simp[]) >>
      strip_tac >>
      qpat_assum `!x. x IN V ==> ?t. S0 x t` (drule_then (qx_choose_then `w` assume_tac)) >>
      qexists `w` >> simp[]) >>
  conj_tac
  >- (qx_gen_tac `x` >> Cases_on `x=v` >> simp[Abbr `pc1`]) >>
  conj_tac
  >- (rpt gen_tac >> simp[Abbr `E1`] >> strip_tac
      >- (qpat_assum `!x y. edge x y ==> _` (drule_then strip_assume_tac) >>
          `x<>v /\ y<>v` by (conj_tac >> strip_tac >> fs[]) >>
          simp[Abbr `pc1`, Abbr `r1`, Abbr `tag1`]) >>
      gvs[] >>
      simp[Abbr `pc1`, Abbr `r1`] >>
      `ALOOKUP dup_table "SWAP1" = NONE /\ ALOOKUP swap_table "SWAP1" = SOME 1`
        by EVAL_TAC >>
      qpat_assum `Abbrev (Flow = _)`
        (SUBST1_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
      qpat_assum `EL _ p = AsmOp "SWAP1"` (fn fetch =>
        qpat_assum `ALOOKUP dup_table "SWAP1" = NONE` (fn dup =>
          qpat_assum `ALOOKUP swap_table "SWAP1" = SOME 1` (fn swap =>
            SIMP_TAC bool_ss [LET_THM, fetch, dup, swap,
                              asm_inst_case_def, optionTheory.option_case_def]))) >>
      map_every (fn pat => qpat_assum pat
        (SUBST1_TAC o REWRITE_RULE [markerTheory.Abbrev_def]))
        [`Abbrev (h1 = _)`, `Abbrev (tag1 = _)`, `Abbrev (B1 = _)`] >>
      qpat_assum `e<>v` (fn diff => SIMP_TAC bool_ss [diff]) >>
      `!k. (if k=0 then 1 else if k=1 then 0 else k) = src k`
        by simp[Abbr `src`] >>
      qpat_assum `!k. (if k=0 then 1 else if k=1 then 0 else k) = src k`
        (rewrite_tac o single) >>
      qpat_assum `Abbrev (Slots = _)` (fn ab =>
        qpat_assum `Slots p height tag boolean e`
          (strip_assume_tac o SIMP_RULE bool_ss [REWRITE_RULE [markerTheory.Abbrev_def] ab])) >>
      conj_tac >- decide_tac >> conj_tac >- decide_tac >>
      conj_tac
      >- (rpt gen_tac >> strip_tac >>
          qpat_assum `!k l org. tag e k = SOME(l,org) ==> _`
            (drule_then strip_assume_tac) >> simp[]) >>
      gen_tac >> strip_tac >>
      qpat_assum `!k. boolean e k ==> _` (drule_then strip_assume_tac) >> simp[]) >>
  qx_gen_tac `x` >> qx_gen_tac `w` >> Cases_on `x=v` >> simp[]
  >- (strip_tac >>
      qpat_assum `!t. S1 v t ==> _` (drule_then (qx_choose_then `out` strip_assume_tac)) >>
      disj2_tac >> qexistsl [`e`,`out`] >> simp[Abbr `E1`]) >>
  strip_tac >>
  qpat_assum `!x t. x IN V /\ S0 x t ==> _`
    (qspecl_then [`x`,`w`] mp_tac) >>
  impl_tac >- simp[] >>
  disch_then (DISJ_CASES_THEN2
    (qx_choose_then `out` (CONJUNCTS_THEN2 DISJ_CASES_TAC assume_tac))
    (qx_choose_then `next` (qx_choose_then `out` strip_assume_tac)))
  >- (disj1_tac >> qexists `out` >> simp[])
  >- (disj1_tac >> qexists `out` >> simp[]) >>
  `next<>v` by metis_tac[] >>
  disj2_tac >> qexistsl [`next`,`out`] >> simp[Abbr `E1`]
QED

Resume stack_comm_strict_endpoint_row[row]:
  mp_tac (Q.SPECL [`p`,`q`,`cc`,`req`,`v INSERT V`,`r1`,`pc1`,`h1`,`n1`,
                   `tag1`,`B1`,`E1`,`v`,`pre`,`tail`,`a`]
                  stack_comm_replacement_row) >>
  SIMP_TAC bool_ss [LET_THM] >>
  impl_tac >-
    (conj_tac >- simp[] >> conj_tac >-
      (qpat_assum `Abbrev (Open = _)` (fn opn =>
         qpat_assum `Abbrev (Shape = _)` (fn shp =>
           qpat_assum `Abbrev (Flow = _)` (fn fl =>
             qpat_assum `Open p cc req (v INSERT V) {} r1 pc1 h1 n1 tag1 B1 E1`
               (ACCEPT_TAC o SIMP_RULE bool_ss
                 (LET_THM :: map (REWRITE_RULE [markerTheory.Abbrev_def]) [opn,shp,fl])))))) >>
     simp[Abbr `pc1`, Abbr `b`, Abbr `p`, Abbr `q`]) >>
  disch_then (qx_choose_then `name` (qx_choose_then `path` (map_every assume_tac o CONJUNCTS))) >>
  pop_assum (mk_asm "replacement_flow") >>
  `path 1=e` by
    (qpat_assum `E1 v (path 1)` mp_tac >> simp[Abbr `E1`] >> metis_tac[]) >>
  `path 2 IN V /\ edge e (path 2)` by
    (qpat_assum `E1 (path 1) (path 2)` mp_tac >> simp[Abbr `E1`] >> metis_tac[]) >>
  `path 2<>v` by metis_tac[] >>
  `rank (path 2)<rank e` by
    (qpat_assum `!x y. edge x y ==> _` (drule_then strip_assume_tac) >> simp[]) >>
  `!k. 2<=k ==> src k=k` by (simp[Abbr `src`] >> decide_tac) >>
  qexistsl [`path 2`,`name`] >>
  conj_tac >- simp[] >> conj_tac >- simp[] >> conj_tac >- simp[] >>
  conj_tac >-
    (qpat_x_assum `pc1 (path 2) = _` mp_tac >> simp[Abbr `pc1`, Abbr `b`]) >>
  conj_tac >- simp[] >> conj_tac >-
    (qpat_x_assum `h1 (path 2) = _` mp_tac >> simp[Abbr `h1`]) >>
  simp[Abbr `b`, LET_THM] >>
  `!k. (if k<2 then NONE else
          OPTION_MAP (\(l,org). (l,splice_pc (LENGTH pre) 2 1 org)) (tag1 v k)) =
        (if k<2 then NONE else Tg e k)` by
    (gen_tac >> Cases_on `k<2` >> simp[Abbr `Tg`, Abbr `f`, Abbr `tag1`]) >>
  `!k. (2<=k /\ B1 v k) <=> (2<=k /\ boolean e k)` by
    (gen_tac >> Cases_on `2<=k` >> simp[Abbr `B1`]) >>
  `tag1 (path 2) = tag (path 2) /\ B1 (path 2) = boolean (path 2)` by
    simp[FUN_EQ_THM, Abbr `tag1`, Abbr `B1`] >>
  `LENGTH pre < LENGTH q /\ EL (LENGTH pre) q = AsmOp name` by
    simp[Abbr `q`, EL_APPEND_EQN] >>
  `height (path 2) = height e-1` by
    (qpat_x_assum `h1 (path 2) = h1 v - 1` mp_tac >> simp[Abbr `h1`]) >>
  `h1 v = height e /\ h1 (path 2) = height (path 2)` by
    simp[Abbr `h1`, IgnAsm `h1 (path 2) = h1 v - 1`] >>
  asm_x "replacement_flow" mp_tac >>
  simp[] >>
  qpat_x_assum `Abbrev (Flow = _)`
    (SUBST1_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  qpat_assum `EL (LENGTH pre) q = AsmOp name` (fn fetch =>
    qpat_assum `ALOOKUP dup_table name = NONE` (fn dup =>
      qpat_assum `ALOOKUP swap_table name = NONE` (fn swap =>
        SIMP_TAC std_ss [LET_THM, fetch, dup, swap, asm_inst_case_def]))) >>
  simp[]
QED

Resume stack_comm_strict_endpoint_row[root]:
  qpat_x_assum `let P = _ in _`
    (map_every assume_tac o CONJUNCTS o SIMP_RULE std_ss [LET_THM]) >>
  `f (pc z) = b+1` by simp[Abbr `f`, splice_pc_def] >>
  `!k l dest. (if k<2 then NONE else Tg e k) = SOME (l,dest) ==>
      2<=k /\ ?org. tag e k = SOME (l,org) /\ dest=f org` by
    (rpt gen_tac >> Cases_on `k<2` >> simp[Abbr `Tg`] >>
     namedCases_on `tag e k` ["", "lo"] >> simp[] >> PairCases_on `lo` >> simp[]) >>
  qpat_assum `Abbrev (J0 = _)` (fn ab =>
    qpat_assum `J0 ss tag boolean e`
      (strip_assume_tac o SIMP_RULE bool_ss [REWRITE_RULE [markerTheory.Abbrev_def] ab])) >>
  qpat_assum `Abbrev (Slots = _)` (fn ab =>
    qpat_assum `Slots p height tag boolean e`
      (strip_assume_tac o SIMP_RULE bool_ss [REWRITE_RULE [markerTheory.Abbrev_def] ab])) >>
  `!k l dest. (if k<2 then NONE else Tg e k) = SOME (l,dest) ==>
      k<LENGTH u.sym_stack /\ EL k u.sym_stack=Lab l 0` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!k l dest. _ ==> 2<=k /\ _` (drule_then strip_assume_tac) >>
     qpat_assum `!k l org. tag e k = _ ==> _ /\ EL k ss.sym_stack = _`
       (drule_then strip_assume_tac) >> simp[]) >>
  `!k. 2<=k /\ boolean e k ==> k<LENGTH u.sym_stack /\
       (EL k u.sym_stack=Val 0w \/ EL k u.sym_stack=Val 1w)` by
    (gen_tac >> strip_tac >>
     qpat_assum `!k. boolean e k ==> _ /\ (EL k ss.sym_stack = _ \/ _)`
       (drule_then strip_assume_tac) >> simp[]) >>
  `!k l dest. (if k<2 then NONE else Tg e k) = SOME (l,dest) ==>
      k<height e /\ dest<LENGTH q /\
      (EL dest q=AsmPushLabel l \/ EL dest q=AsmPushOfst l 0) /\
      ?off dest'. FLOOKUP (SND (compute_label_offsets q)) l = SOME off /\
        off < dimword(:256) /\ FLOOKUP (build_offset_to_pc q) off = SOME dest'` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!k l dest. _ ==> 2<=k /\ _` (drule_then strip_assume_tac) >>
     qpat_assum `!k l org. tag e k = _ ==> _ /\ org < LENGTH p /\ _`
       (drule_then strip_assume_tac) >>
     qpat_assum `dest=f org` SUBST1_TAC >>
     (conj_tac >- simp[]) >>
     map_every (fn pat => qpat_x_assum pat
       (SUBST_ALL_TAC o REWRITE_RULE [markerTheory.Abbrev_def]))
       [`Abbrev (f = _)`, `Abbrev (b = _)`, `Abbrev (p = _)`, `Abbrev (q = _)`] >>
     mp_tac (Q.INST [`old` |-> `off`, `dest` |-> `dest'`]
              (SIMP_RULE bool_ss [LET_THM] commcut_relocate_slot)) >> simp[]) >>
  qexistsl [`j`,`u`,`z`,`name`] >>
  simp[LET_THM, Abbr `J0`, Abbr `Slots`, SF CONJ_ss] >>
  conj_tac >-
    (conj_tac >-
      (rpt strip_tac >>
       qpat_assum `!k. boolean e k ==> _ /\ tag e k = NONE`
         (drule_then strip_assume_tac) >> simp[Abbr `Tg`]) >>
     rpt strip_tac >>
     `(if k<2 then NONE else Tg e k) = SOME (l,origin)` by simp[] >>
     qpat_assum `!k l dest. _ ==> _ /\ dest < LENGTH q /\ _`
       (drule_then strip_assume_tac) >>
     simp[] >> qexistsl [`off`,`dest'`] >> simp[]) >>
  qx_gen_tac `env1` >> qx_gen_tac `w` >> strip_tac >>
  drule_then strip_assume_tac asm_sym_rel_pc >>
  qpat_assum `asm_sym_rel q env1 w u`
    (assume_tac o CONJUNCT2 o SIMP_RULE bool_ss [LIST_REL_EL_EQN] o
      CONJUNCT1 o REWRITE_RULE [asm_sym_rel_def]) >>
  simp[Abbr `Shape`] >>
  conj_tac >-
    (rpt strip_tac >>
     `(if k<2 then NONE else Tg e k) = SOME (l,origin)` by simp[] >>
     qpat_assum `!k l dest. _ ==> _ /\ EL k u.sym_stack = _`
       (drule_then strip_assume_tac) >>
     qpat_assum `!k l dest. _ ==> _ /\ dest < LENGTH q /\ _`
       (drule_then strip_assume_tac) >>
     `EL k w.as_stack = (n2w off:bytes32)` by
       (qpat_x_assum `!k. _ ==> sval_conc _ (EL k u.sym_stack) = _`
          (qspec_then `k` mp_tac) >>
        (impl_tac >- simp[]) >> simp[sval_conc_def, EQ_SYM_EQ]) >>
     simp[]) >>
  gen_tac >> strip_tac >>
  qpat_assum `!k. 2<=k /\ boolean e k ==> _ /\ (EL k u.sym_stack = _ \/ _)`
    (drule_all_then strip_assume_tac) >>
  qpat_x_assum `!k. _ ==> sval_conc _ (EL k u.sym_stack) = _`
    (qspec_then `k` mp_tac) >> simp[sval_conc_def]
QED

Finalise stack_comm_strict_endpoint_row
