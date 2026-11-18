Theory staticAbortOptUnusedLabelsRoot
Ancestors
  staticAbortOptUnusedLabelsSource staticAbortOptUnusedLabelsStopped
  staticAbortProtectedActualPrefix asmSplice asmSymPc asmSymBridge asmDataEnv
  asmWf asmIR asmSem asmSymSem asmOptimizer asmToBytecodeProofs
  finite_map pred_set rich_list list words arithmetic

Theorem unused_label_one_actual_root:
  !orig p pre l tail data s n ss cut cc req req_bound
    V e (rank:(num#num)->rat) pc height need tag boolean edge.
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
  let d = LENGTH pre; q = pre ++ tail in
  let r = splice_pc d 1 0 in
  let pcQ = r o pc; P = OPTION_MAP (\(n,j). (n,r j)) in
  let T = \x k. P (tag x k);
      K = {x | x IN V /\ pc x <> d};
      C = \s n w. ?off. FLOOKUP (SND (compute_label_offsets s)) n = SOME off /\
                      off < dimword(:256) /\ FLOOKUP (build_offset_to_pc s) off = SOME w;
      ssQ = sym_with_pc (r ss.sym_base.as_pc) ss;
      env = asm_data_env orig (assemble orig ++ data) in
  p = pre ++ [AsmLabel l] ++ tail /\ ~MEM l (asm_label_refs p) /\
  s.as_pc = 0 /\ s.as_code = assemble orig ++ data /\
  asm_static_wf orig /\ asm_static_wf p /\ asm_static_wf q /\
  FILTER is_data_inst p = FILTER is_data_inst orig /\
  sym_steps p env n (sym_init s) = SymOK ss /\
  asm_sym_rel p (asm_data_env p (assemble p ++ data)) cut ss /\
  Shape p cc req pc height need tag boolean e cut /\ req <<= req_bound /\
  (!k l j. tag e k = SOME(l,j) ==>
      k < LENGTH ss.sym_stack /\ EL k ss.sym_stack = Lab l 0) /\
  (!k. boolean e k ==>
      k < LENGTH ss.sym_stack /\ (EL k ss.sym_stack = Val 0w \/ EL k ss.sym_stack = Val 1w)) /\
  Open p cc req V {} rank pc height need tag boolean edge /\
  e IN V /\ (!x. x IN V ==> Reach edge e x) /\
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
    eQ IN K /\
    (if pc e <> d then eQ = e else
       edge e eQ /\ pc eQ = d+1 /\ height eQ = height e /\
       (!k n j. tag eQ k = SOME(n,j) ==> tag e k = SOME(n,j)) /\
       (!k. boolean eQ k ==> boolean e k)) /\
    Shape q cc req pcQ height need T boolean eQ t /\
    (!k n j. T eQ k = SOME(n,j) ==>
       k < LENGTH ssQ.sym_stack /\ EL k ssQ.sym_stack = Lab n 0) /\
    (!k. boolean eQ k ==>
       k < LENGTH ssQ.sym_stack /\ (EL k ssQ.sym_stack = Val 0w \/ EL k ssQ.sym_stack = Val 1w))
Proof
  rpt gen_tac >>
  ntac 4 (CONV_TAC (REWR_CONV LET_THM THENC BETA_CONV)) >>
  map_every (fn pat => qmatch_goalsub_abbrev_tac pat >>
      CONV_TAC (REWR_CONV LET_THM THENC BETA_CONV))
    [`LET _ d`, `LET _ q`, `LET _ r`, `LET _ pcQ`, `LET _ P`,
     `LET _ tags`, `LET _ retained`, `LET _ C`, `LET _ ssQ`, `LET _ env`] >>
  CONV_TAC (LAND_CONV (SCONV [])) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all (CONV_RULE
    (STRIP_QUANT_CONV (REPEATC (REWR_CONV LET_THM THENC BETA_CONV) THENC
                       LAND_CONV (SCONV []) THENC RAND_CONV (SCONV [])))
    unused_label_source_contraction) >>
  disch_then (mp_tac o cj 3) >>
  disch_then (qspec_then `e` mp_tac) >> simp[] >> strip_tac >>
  qpat_x_assum `let S = _ in _` kall_tac >>
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
  `?j. sym_steps q env j (sym_init s) = SymOK ssQ` by
    (simp[Abbr `ssQ`, Abbr `r`, Abbr `d`, Abbr `q`] >>
     metis_tac[BETA_RULE (REWRITE_RULE [LET_THM] unused_label_one_stopped_prefix)]) >>
  rename1 `sym_steps q env j (sym_init s) = SymOK ssQ` >>
  `sym_steps q (asm_data_env orig (assemble orig ++ data)) j (sym_init s) = SymOK ssQ` by
    fs[Abbr `env`] >>
  drule_all (Q.INST [`p` |-> `orig`, `q` |-> `q`] stopped_symbolic_prefix_actual_code) >>
  disch_then (qx_choose_then `t` strip_assume_tac) >>
  `env = asm_data_env q (assemble q ++ data)` by
    (simp[Abbr `env`] >> irule asm_data_env_agree >> simp[]) >>
  `ss.sym_base.as_pc = pc e /\ LENGTH ss.sym_stack = height e /\
    ss.sym_base.as_call_ctx = cc /\ ss.sym_base.as_requests = req` by
    (qpat_assum `asm_sym_rel p _ cut ss`
       (strip_assume_tac o REWRITE_RULE [asm_sym_rel_def, LIST_REL_EL_EQN]) >>
     simp[]) >>
  `ssQ.sym_base.as_pc = pcQ eQ /\ ssQ.sym_stack = ss.sym_stack /\
    ssQ.sym_base.as_call_ctx = cc /\ ssQ.sym_base.as_requests = req` by
    simp[Abbr `ssQ`, sym_with_pc_def] >>
  qpat_x_assum `pc e = d ==> ?y. _` kall_tac >>
  `sym_steps q (asm_data_env q (assemble q ++ data)) j (sym_init s) = SymOK ssQ` by
    metis_tac[] >>
  `!k. k < LENGTH ssQ.sym_stack ==>
       sval_conc (SND (compute_label_offsets q)) (EL k ssQ.sym_stack) =
         SOME (EL k t.as_stack)` by
    (qpat_assum `asm_sym_rel q _ t ssQ`
       (strip_assume_tac o BETA_RULE o REWRITE_RULE [asm_sym_rel_def, LIST_REL_EL_EQN]) >>
     first_assum ACCEPT_TAC) >>
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
  qexistsl_tac [`j`, `t`, `eQ`] >>
  simp[Abbr `retained`] >>
  conj_tac
  >- (qpat_assum `!x. x IN V ==> (need x ==> _) /\ _`
        (qspec_then `eQ` (mp_tac o cj 1)) >> simp[]) >>
  conj_tac
  >- (rpt gen_tac >> disch_tac >>
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
