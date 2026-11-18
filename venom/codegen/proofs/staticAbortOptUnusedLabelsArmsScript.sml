Theory staticAbortOptUnusedLabelsArms
Ancestors arithmetic[qualified,ignore_grammar]
  staticAbortOptUnusedLabelsSource asmSplice asmSymBridge asmToBytecodeProofs
  asmEncodeParse codegenEncodingWf codegenRel asmWf asmSymSem asmSem asmIR
  symbolResolve asmOptimizer list rich_list finite_map pred_set words

Theorem unused_label_one_retained_arms:
  !p pre l tail cc req V e rank pc height need tag boolean edge
    u src fresh bnew H legal (taken:'a -> bool) v.
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
    \p cc req (V:(num#num)->bool) X rank pc height need
      (tag:(num#num)->num->(string#num)option)
      (boolean:(num#num)->num->bool) edge.
    let S = Shape p cc req pc height need tag boolean in
    let target = \x y.
      ?l origin off. tag x 0 = SOME(l,origin) /\
        FLOOKUP (SND(compute_label_offsets p)) l = SOME off /\
        off < dimword(:256) /\
        FLOOKUP (build_offset_to_pc p) off = SOME(pc y)
    in
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
              p 1 t = AsmOK u /\ S y u))
  in
  let Reach = \(edge:(num#num)->(num#num)->bool) e x.
    ?n (path:num->num#num).
      path 0=e /\ path n=x /\ !k. k<n ==> edge (path k) (path(SUC k))
  in
  p=pre++[AsmLabel l]++tail /\ asm_static_wf p /\
  ~MEM l (asm_label_refs p) /\ Open p cc req V {} rank pc height need tag boolean edge /\
  e IN V /\ (!x. x IN V ==> Reach edge e x) ==>
  let d = LENGTH pre in
  let q = pre++tail in
  let r = splice_pc d 1 0 in
  let C = \s n w. ?off. FLOOKUP (SND (compute_label_offsets s)) n = SOME off /\
                     off < dimword(:256) /\ FLOOKUP (build_offset_to_pc s) off = SOME w in
  let P = OPTION_MAP (\(n,j). (n,r j)) in
  let T = \x k. P (tag x k) in
  let I = \tg fr w.
    (!k n j. tg w k = SOME(n,j) ==> k < height w /\
       (fr k = SOME(n,j) \/ ?h. src k = SOME h /\ h < height u /\ tg u h = SOME(n,j))) /\
    (!k. boolean w k ==> k < height w /\
       (bnew k \/ ?h. src k = SOME h /\ h < height u /\ boolean u h))
  in
  u IN V /\ pc u <> d /\
  (!a. legal a ==> edge u (v a) /\ height (v a) = H /\ I tag fresh (v a) /\
       (if taken a then ?n j. tag u 0 = SOME(n,j) /\ C p n (pc(v a))
        else pc(v a) = pc u+1)) ==>
  (!x k n j. x IN V /\ tag x k = SOME(n,j) ==>
      j <> d /\ j < LENGTH p /\ r j < LENGTH q /\ EL (r j) q = EL j p /\
      T x k = SOME(n,r j) /\
      !w. C p n w ==> w <> d /\ INDEX_OF (AsmLabel n) p = SOME w /\
        INDEX_OF (AsmLabel n) q = SOME(r w) /\ C q n (r w)) /\
  (?z. !a. legal a ==>
      z a IN V /\ pc(z a) <> d /\ rank(z a) < rank u /\ height(z a) = H /\
      I T (P o fresh) (z a) /\
      (if pc(v a) = d then
         ~taken a /\ edge (v a) (z a) /\ pc(z a) = d+1 /\ height(z a) = height(v a) /\
         (!k n j. tag (z a) k = SOME(n,j) ==> tag (v a) k = SOME(n,j)) /\
         (!k. boolean (z a) k ==> boolean (v a) k)
       else z a = v a) /\
      (~taken a ==> r(pc(z a)) = r(pc u)+1) /\
      (taken a ==> z a = v a /\ ?n j. tag u 0 = SOME(n,j) /\ T u 0 = SOME(n,r j) /\
          EL (pc(z a)) p = AsmLabel n /\ EL (r(pc(z a))) q = AsmLabel n /\
          C q n (r(pc(z a)))))
Proof
  rpt gen_tac >>
  ntac 4 (CONV_TAC (REWR_CONV LET_THM THENC BETA_CONV)) >>
  (* Normalize only the source hypotheses, leaving the layout abbreviations lexical. *)
  CONV_TAC (LAND_CONV (SCONV [])) >> strip_tac >>
  drule_all (CONV_RULE
    (STRIP_QUANT_CONV (REPEATC (REWR_CONV LET_THM THENC BETA_CONV) THENC
                       LAND_CONV (SCONV []) THENC RAND_CONV (SCONV [])))
    unused_label_source_contraction) >>
  strip_tac >>
  qpat_x_assum `LET _ _` (mp_tac o SIMP_RULE (boss_ss()) [LET_THM]) >>
  strip_tac >>
  map_every (fn pat => qmatch_goalsub_abbrev_tac pat >>
      CONV_TAC (REWR_CONV LET_THM THENC BETA_CONV))
    [`LET _ d`, `LET _ q`, `LET _ r`, `LET _ C`, `LET _ P`, `LET _ tags`, `LET _ inherits`] >>
  strip_tac >>
  `!x j k n. x IN V /\ tag x k = SOME(n,j) ==> j < LENGTH p` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `!x. x IN V ==> ?t:asm_state. _` (qspec_then `x` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
     qpat_assum `!k l origin. tag x k = SOME(l,origin) ==> _`
       (qspecl_then [`k`,`n`,`j`] mp_tac) >> simp[]) >>
  qpat_x_assum `!x. x IN V ==> ?t:asm_state. _` kall_tac >>
  qpat_x_assum `!x t. _ ==> (?u. _) \/ (?y u. _)` kall_tac >>
  qpat_x_assum `!x y. edge x y ==> _`
    (fn th => map_every assume_tac [cj 2 th, cj 3 th]) >>
  `!j. j < LENGTH p /\ j <> d ==> r j < LENGTH q /\ EL (r j) q = EL j p` by
    (rpt gen_tac >> strip_tac >>
     mp_tac (Q.INST [`pfx` |-> `pre`, `sfx` |-> `tail`,
                      `pat` |-> `[AsmLabel l]`, `repl` |-> `[]`, `i` |-> `j`]
                      (INST_TYPE [alpha |-> ``:asm_inst``] splice_fetch)) >>
     simp[Abbr `q`, Abbr `r`, Abbr `d`] >> gvs[]) >>
  `asm_label_refs q = asm_label_refs p` by
    simp[Abbr `q`, asm_label_refs_def] >>
  `asm_static_wf q` by
    (mp_tac (Q.INST [`pfx` |-> `pre`, `sfx` |-> `tail`,
                      `pat` |-> `[AsmLabel l]`, `repl` |-> `[]`] asm_splice_static_wf) >>
     `asm_label_refs [] = []` by simp[asm_label_refs_def] >>
     simp[asm_splice_ok_def, is_data_inst_def] >> gvs[Abbr `q`]) >>
  conj_asm1_tac >- suspend "layout" >>
  suspend "arms"
QED

Resume unused_label_one_retained_arms[layout]:
  rpt gen_tac >> strip_tac >>
  qpat_assum `!x k a j. _ ==> a <> l /\ _`
    (qspecl_then [`x`,`k`,`n`,`j`] mp_tac) >>
  (impl_tac >- simp[]) >> strip_tac >>
  `j < LENGTH p` by metis_tac[] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  `r j < LENGTH q /\ EL (r j) q = EL j p` by metis_tac[] >>
  ntac 2 (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >- simp[Abbr `tags`, Abbr `P`] >>
  qx_gen_tac `w` >>
  qpat_assum `Abbrev (C = _)`
    (fn th => CONV_TAC (LAND_CONV (SCONV [REWRITE_RULE [markerTheory.Abbrev_def] th]))) >>
  strip_tac >>
  `w <> d` by metis_tac[] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  `w < LENGTH p /\ asm_pc_to_offset p w = off` by
    (drule offset_to_pc_reverse >> simp[]) >>
  `?m. EL w p = AsmLabel m` by (drule offset_to_pc_label >> simp[]) >>
  `MEM (AsmLabel n) p` by
    (CCONTR_TAC >>
     `!i. i < LENGTH (TAKE (SUC w) p) ==>
        EL i (TAKE (SUC w) p) <> AsmLabel n /\
        (!m. EL i (TAKE (SUC w) p) <> AsmDataHeader m)` by
       (rpt gen_tac >> strip_tac >>
        `i <= w /\ i < LENGTH p` by
          (fs[LENGTH_TAKE_EQ] >> (bossLib.gvs [])) >>
        simp[EL_TAKE, IgnAsm `p = _`] >> conj_tac
        >- metis_tac[MEM_EL] >>
        rpt strip_tac >>
        `asm_data_at_end p` by metis_tac[asm_static_wf_def] >>
        qpat_assum `asm_data_at_end p`
          (qspec_then `i` mp_tac o REWRITE_RULE [asm_data_at_end_def]) >>
        simp[IgnAsm `p = _`] >> qexists `w` >>
        simp[is_data_inst_def, arithmeticTheory.GREATER_EQ, IgnAsm `p = _`]) >>
     `FLOOKUP (SND (compute_label_offsets (TAKE (SUC w) p))) n = NONE` by
       (qspecl_then [`TAKE (SUC w) p`,`0`,`FEMPTY`,`n`] mp_tac clo_preserves_label >>
        (impl_tac >- metis_tac[]) >>
        simp[compute_label_offsets_def, clo_step_eq, IgnAsm `p = _`]) >>
     `off < FST (compute_label_offsets (TAKE (SUC w) p))` by
       ((simp[compute_label_offsets_bound] >>
        `TAKE (SUC w) p = SNOC (EL w p) (TAKE w p)` by
          metis_tac[TAKE_EL_SNOC, arithmeticTheory.ADD1] >>
        fs[asm_pc_to_offset_def, SNOC_APPEND, SUM_APPEND, asm_inst_size_def] >> (gvs[compute_label_offsets_bound, TAKE_EL_SNOC, arithmeticTheory.ADD1, asm_pc_to_offset_def, SNOC_APPEND, SUM_APPEND, asm_inst_size_def]))) >>
     qpat_x_assum `FLOOKUP (SND (compute_label_offsets p)) n = SOME off` mp_tac >>
     `TAKE (SUC w) p ++ DROP (SUC w) p = p` by simp[] >>
     pop_assum (fn th => CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [GSYM th]))) >>
     rewrite_tac[compute_label_offsets_def, clo_step_eq, FOLDL_APPEND] >>
     qmatch_goalsub_abbrev_tac `FOLDL clostep _ _` >>
     `!xs acc. off < FST acc /\ FLOOKUP (SND acc) n <> SOME off ==>
            FLOOKUP (SND (FOLDL clostep acc xs)) n <> SOME off` by
       (qpat_assum `Abbrev (clostep = _)`
          (fn th => POP_ASSUM_LIST (K ALL_TAC) >> assume_tac th) >>
        Induct >> simp[] >> qx_gen_tac `ins` >> qx_gen_tac `acc` >> strip_tac >>
        first_x_assum irule >> PairCases_on `acc` >> fs[] >>
        Cases_on `ins` >> simp[Abbr `clostep`, FLOOKUP_UPDATE] >>
        TRY (COND_CASES_TAC >> simp[]) >> decide_tac) >>
     first_x_assum irule >>
     fs[Abbr `clostep`, compute_label_offsets_def, clo_step_eq, IgnAsm `p = _`]) >>
  Cases_on `INDEX_OF (AsmLabel n) p` >- fs[INDEX_OF_eq_NONE] >>
  rename1 `INDEX_OF (AsmLabel n) p = SOME i` >>
  drule_all asm_static_wf_code_label >> strip_tac >>
  `i = w` by metis_tac[optionTheory.SOME_11] >>
  qpat_x_assum `i = w` SUBST_ALL_TAC >>
  `INDEX_OF (AsmLabel n) q = SOME (r w)` by
    (mp_tac (Q.INST [`pfx` |-> `pre`, `sfx` |-> `tail`, `pat` |-> `[AsmLabel l]`,
                     `repl` |-> `[]`, `l` |-> `n`] splice_index_of_label) >>
     qpat_assum `INDEX_OF (AsmLabel n) p = SOME w`
       (fn th => qpat_assum `p = _` (fn eq => assume_tac (REWRITE_RULE [eq] th))) >>
     simp[Abbr `q`, Abbr `r`, Abbr `d`]) >>
  simp[Abbr `C`, IgnAsm `p = _`] >>
  `?offq. FLOOKUP (SND (compute_label_offsets q)) n = SOME offq /\
          offq < 65536 /\ FLOOKUP (build_offset_to_pc q) offq = SOME (r w)` by
    (irule asm_static_wf_code_label >> simp[]) >>
  qexists `offq` >> simp[] >>
  `65536 < dimword(:256)` by
    (rewrite_tac[dimword_def, fcpLib.INDEX_CONV ``dimindex(:256)``] >> EVAL_TAC) >>
  decide_tac
QED

Resume unused_label_one_retained_arms[arms]:
  (* Transfer only demands at the retained endpoint, using equality of heights. *)
  `!b w. inherits tag fresh b /\ height w = height b /\
         (!k n j. tag w k = SOME(n,j) ==> tag b k = SOME(n,j)) /\
         (!k. boolean w k ==> boolean b k) ==>
         inherits tags (P o fresh) w` by
    (qpat_assum `Abbrev (inherits = _)` (fn hi =>
       qpat_assum `Abbrev (tags = _)` (fn ht =>
         qpat_assum `Abbrev (P = _)` (fn hp =>
           POP_ASSUM_LIST (K ALL_TAC) >> map_every assume_tac [hi,ht,hp]))) >>
     rpt gen_tac >> strip_tac >>
     fs[Abbr `inherits`, Abbr `tags`, Abbr `P`, pairTheory.EXISTS_PROD] >>
     rpt strip_tac >> metis_tac[]) >>
  CONV_TAC (HO_REWR_CONV (GSYM SKOLEM_THM)) >> qx_gen_tac `a` >>
  reverse (Q_TAC ASM_CASES_TAC `legal a`) >- (qexists `v a` >> simp[]) >>
  qpat_assum `legal a` (fn th => rewrite_tac[th]) >>
  qpat_assum `!a. legal a ==> _` (qspec_then `a` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  `v a IN V /\ rank (v a) < rank u` by metis_tac[] >>
  `inherits tags (P o fresh) (v a)` by
    (qpat_assum `!b w. _ ==> inherits tags (P o fresh) w`
       (qspecl_then [`v a`, `v a`] irule) >> simp[]) >>
  (Q_TAC ASM_CASES_TAC `taken a` >-
    (qpat_assum `taken a` (fn th =>
       qpat_x_assum `if taken a then _ else _`
         (qx_choose_then `n` (qx_choose_then `j` strip_assume_tac) o REWRITE_RULE [th])) >>
     qpat_assum `!x k n j. _ ==> _ /\ _ /\ _ /\ _ /\ tags x k = _ /\ _`
       (qspecl_then [`u`, `0`, `n`, `j`] mp_tac) >>
     (impl_tac >- simp[]) >> strip_tac >>
     qpat_x_assum `!w. C p n w ==> _` (qspec_then `pc (v a)` mp_tac) >>
     (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
     `EL (pc (v a)) p = AsmLabel n /\ EL (r (pc (v a))) q = AsmLabel n` by
       metis_tac[INDEX_OF_eq_SOME] >>
     qexists `v a` >> simp[IgnAsm `p = _`] >> qexistsl [`n`,`j`] >> simp[])) >>
  `pc (v a) = pc u + 1` by
    (qpat_assum `~taken a` (fn th =>
       qpat_x_assum `if taken a then _ else _` (ACCEPT_TAC o REWRITE_RULE [th]))) >>
  reverse (Q_TAC ASM_CASES_TAC `pc (v a) = d`) >-
    (qexists `v a` >> simp[] >>
     simp[Abbr `r`, splice_pc_def] >> rpt COND_CASES_TAC >> decide_tac) >>
  qpat_x_assum `!x. x IN V /\ pc x = d ==> ?y. edge x y /\ _`
    (qspec_then `v a` mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choose_then `w`
    (fn th => map_every assume_tac (List.take (CONJUNCTS th, 7)))) >>
  `inherits tags (P o fresh) w` by
    (qpat_assum `!b w. _ ==> inherits tags (P o fresh) w`
       (qspecl_then [`v a`, `w`] irule) >> metis_tac[]) >>
  `rank w < rank u /\ pc w <> d /\ height w = H` by
    (conj_tac >-
       (Q_TAC (TRANS_TAC ratTheory.RAT_LES_TRANS) `rank (v a)` >>
        conj_tac >> first_assum ACCEPT_TAC) >>
     simp[GSYM arithmeticTheory.ADD1]) >>
  `pc u + 1 = d` by
    (qpat_assum `pc (v a) = pc u + 1` (SUBST1_TAC o SYM) >>
     first_assum ACCEPT_TAC) >>
  `pc u <= d` by
    (qpat_assum `pc u + 1 = d` mp_tac >> numLib.ARITH_TAC) >>
  `r (pc w) = r (pc u) + 1` by simp[Abbr `r`, splice_pc_def] >>
  qexists `w` >> simp[]
QED

Finalise unused_label_one_retained_arms
