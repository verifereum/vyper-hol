Theory staticAbortOptMergeJumpdestsBypass
Ancestors
  asmSymBridge asmSplice asmWf asmSymSem asmSem stackOpAsmSim stackOpSim
  spillWordBounds asmToBytecodeProofs symbolResolve words list arithmetic
  pred_set finite_map

(* Open the naming equations only when exposing the underlying predicates. *)
val expand_bypass_names =
  TOP_DEPTH_CONV (Unwind.UNWIND_FORALL_CONV ORELSEC BETA_CONV)

Theorem merge_rename_root_bypass:
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
           !m. m = hj + asm_op_arity name - hi ==>
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
!Reach. Reach = (\(edge:(num#num)->(num#num)->bool) e x.
  ?n (path:num->num#num).
    path 0=e /\ path n=x /\ !k. k<n ==> edge (path k) (path(SUC k))) ==>
!S'. S' = Shape p cc req pc height need tag boolean ==>
!L. L = SND(compute_label_offsets p) ==>
!B. B = build_offset_to_pc p ==>
asm_static_wf p /\ p = pre ++ [AsmLabel x;next;third] ++ tail /\
((next = AsmLabel y /\ y <> x) \/
 (next = AsmPushLabel y /\ third = AsmOp "JUMP")) /\
Open p cc req V {} rank pc height need tag boolean edge /\
v IN V /\ pc v = LENGTH pre ==>
?z off. z IN V /\ Reach edge v z /\ rank z < rank v /\
  height z = height v /\ FLOOKUP L y = SOME off /\ off < dimword(:256) /\
  FLOOKUP B off = SOME(pc z) /\
  (!k l o'. tag z k = SOME(l,o') ==> tag v k = SOME(l,o')) /\
  (!k. boolean z k ==> boolean v k) /\
  (!t. S' v t ==> asm_steps L B p (if next = AsmLabel y then 1 else 3) t =
                  AsmOK(t with as_pc := pc z) /\ S' z (t with as_pc := pc z)) /\
  (!W. W = {a | a IN V /\ Reach edge z a} ==>
   !E. E = (\a b. a IN W /\ edge a b) ==>
    z IN W /\ Open p cc req W {} rank pc height need tag boolean E /\
    (!a. a IN W ==> Reach E z a))
Proof
  ntac 7 (gen_tac >> disch_then assume_tac) >>
  disch_tac >>
  pop_assum (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac
      (CONJUNCTS_THEN2 (mk_asm "site") STRIP_ASSUME_TAC))) >>
  qpat_x_assum `Shape = _` (mk_asm "shape") >>
  qpat_x_assum `Flow = _` (mk_asm "flow") >>
  qpat_x_assum `Reach = _` (mk_asm "reach") >>
  qpat_x_assum `Open = _` (mk_asm "open") >>
  qpat_x_assum `S' = _` (mk_asm "foldS") >>
  qpat_x_assum `L = SND (compute_label_offsets p)` (mk_asm "offsetmap") >>
  qpat_x_assum `B = build_offset_to_pc p` (mk_asm "pcmap") >>
  qpat_x_assum `p = pre ++ [AsmLabel x;next;third] ++ tail` (mk_asm "program") >>
  qabbrev_tac `d:num = if next = AsmLabel y then 1 else 3` >>
  qpat_x_assum `Abbrev (d = _)`
    (mk_asm "stepcount" o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  qpat_x_assum `Open p cc req V {} rank pc height need tag boolean edge`
    (fn th => asm "open" (fn opth =>
      assume_tac (SIMP_RULE (srw_ss()) [EMPTY_SUBSET,DIFF_EMPTY]
        (CONV_RULE expand_bypass_names (REWRITE_RULE [opth] th))))) >>
  pop_assum (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 (mk_asm "inhabited")
      (CONJUNCTS_THEN2 (mk_asm "bounds")
        (CONJUNCTS_THEN2 (mk_asm "edges") (mk_asm "progress"))))) >>
  sg `?z off. z IN V /\ Reach edge v z /\ rank z < rank v /\
      height z = height v /\ FLOOKUP L y = SOME off /\ off < dimword(:256) /\
      FLOOKUP B off = SOME(pc z) /\
      (!k l o'. tag z k = SOME(l,o') ==> tag v k = SOME(l,o')) /\
      (!k. boolean z k ==> boolean v k) /\
      !t:asm_state. t.as_pc = pc v ==>
        asm_steps L B p d t = AsmOK (t with as_pc := pc z)`
  >- suspend "extract" >>
  qexistsl [`z`,`off`] >> simp[] >> conj_tac
  >- suspend "uniform" >>
  suspend "restrict"
QED

Resume merge_rename_root_bypass[extract]:
  asm "offsetmap" SUBST1_TAC >> asm "pcmap" SUBST1_TAC >>
  qpat_x_assum `pc v = LENGTH pre` (mk_asm "rootpc") >>
  `EL (pc v) p = AsmLabel x /\ pc v < LENGTH p` by
    (asm "program" (fn th => asm "rootpc" (fn pt => simp[th,pt,EL_APPEND_EQN]))) >>
  sg `!t:asm_state. t.as_pc = pc v ==>
      asm_steps (SND(compute_label_offsets p)) (build_offset_to_pc p) p 1 t =
      AsmOK (t with as_pc := pc v+1)`
  >- (rpt strip_tac >> rewrite_tac[numLib.num_CONV ``1:num``] >>
      simp[asm_steps_def, asm_step_def, asm_next_def]) >>
  asm "inhabited" (qspec_then `v` mp_tac) >> simp[] >>
  disch_then (qx_choose_then `t0` assume_tac) >>
  `t0.as_pc = pc v` by
    (qpat_x_assum `Shape p cc req pc height need tag boolean v t0` mp_tac >>
     asm "shape" (fn th => simp[th, LET_THM])) >>
  asm "progress" (qspecl_then [`v`,`t0`] mp_tac) >> simp[] >>
  disch_then (qx_choose_then `v1` strip_assume_tac) >>
  asm "edges" (qspecl_then [`v`,`v1`] mp_tac) >> simp[] >>
  disch_then strip_assume_tac >>
  qpat_x_assum `Flow p pc height tag boolean v v1` mp_tac >>
  asm "flow" (fn th => rewrite_tac[th] >> CONV_TAC expand_bypass_names >> simp[]) >> strip_tac >>
  asm "site" (DISJ_CASES_THEN strip_assume_tac)
  >- suspend "adjacent" >>
  suspend "stub"
QED

Resume merge_rename_root_bypass[adjacent]:
  `~MEM (AsmLabel y) pre` by
    (irule asm_labels_unique_append_not_mem >>
     qexists_tac `[AsmLabel x;next;third] ++ tail` >>
     asm "program" (fn th => simp[GSYM th, asm_static_wf_def]) >>
     asm "program" (fn th => fs[th, asm_static_wf_def])) >>
  `INDEX_OF (AsmLabel y) p = SOME (pc v1)` by
    (asm "program" (fn th => asm "rootpc" (fn pt =>
       simp[th, pt, INDEX_OF_APPEND, INDEX_OF_CONS]))) >>
  drule_all asm_static_wf_code_label >>
  disch_then (qx_choose_then `off` strip_assume_tac) >>
  `off < dimword(:256)` by (fs[dimword_def]) >>
  qexistsl [`v1`, `off`] >> asm "stepcount" (fn th => simp[th]) >>
  asm "reach" (fn th => simp[th]) >>
  qexistsl [`1`, `\k. if k = 0 then v else v1`] >> simp[]
QED

Resume merge_rename_root_bypass[stub]:
  `EL (pc v1) p = AsmPushLabel y /\ pc v1 < LENGTH p` by
    (asm "program" (fn th => asm "rootpc" (fn pt =>
       simp[th,pt,EL_APPEND_EQN]))) >>
  sg `!t:asm_state. t.as_pc = pc v1 ==>
    asm_steps (SND(compute_label_offsets p)) (build_offset_to_pc p) p 1 t =
    case FLOOKUP (SND(compute_label_offsets p)) y of
      NONE => AsmError ("unknown label: " ++ y)
    | SOME off => AsmOK (t with <|as_pc := pc v1+1;
                                 as_stack := n2w off::t.as_stack|>)`
  >- (rpt strip_tac >> rewrite_tac[numLib.num_CONV ``1:num``] >>
      gvs[asm_steps_def, asm_step_def] >>
      Cases_on `FLOOKUP (SND(compute_label_offsets p)) y` >> simp[asm_next_def]) >>
  pop_assum (mk_asm "pushstep") >>
  asm "pushstep" (qspec_then `t0 with as_pc := pc v+1` mp_tac) >>
  simp[] >>
  disch_then (fn th => asm "progress"
    (qspecl_then [`v1`,`t0 with as_pc := pc v+1`] (mp_tac o REWRITE_RULE [th]))) >>
  Cases_on `FLOOKUP (SND(compute_label_offsets p)) y` >> simp[] >>
  rename1 `FLOOKUP _ y = SOME off` >>
  disch_then (qx_choose_then `v2` strip_assume_tac) >>
  asm "edges" (qspecl_then [`v1`,`v2`] mp_tac) >> simp[] >> disch_then strip_assume_tac >>
  qpat_x_assum `Flow p pc height tag boolean v1 v2` mp_tac >>
  asm "flow" (fn th => rewrite_tac[th] >> CONV_TAC expand_bypass_names >> simp[]) >> strip_tac >>
  `pc v2 = pc v + 2` by decide_tac >>
  `EL (pc v2) p = AsmOp "JUMP" /\ pc v2 < LENGTH p` by
    (asm "program" (fn th => asm "rootpc" (fn pt =>
      simp[th,pt,EL_APPEND_EQN]))) >>
  `LENGTH (encode_num_bytes off) <= 2` by
    (fs[asm_static_wf_def, asm_encoding_wf_def, pairTheory.UNCURRY, symbol_size_def] >>
     qpat_x_assum `!lbl off'. FLOOKUP _ lbl = SOME off' ==> _`
       (qspecl_then [`y`, `off`] mp_tac) >> simp[]) >>
  `off < dimword(:256)` by
    (drule encode_num_bytes_length_bound >> simp[dimword_def]) >>
  sg `!t:asm_state. t.as_pc = pc v2 ==>
      asm_steps (SND(compute_label_offsets p)) (build_offset_to_pc p) p 1
        (t with as_stack := n2w off::t.as_stack) =
      case FLOOKUP (build_offset_to_pc p) off of
        NONE => AsmError "jump: invalid destination"
      | SOME dest => AsmOK (t with as_pc := dest)`
  >- (rpt strip_tac >> rewrite_tac[numLib.num_CONV ``1:num``] >>
      gvs[asm_steps_def, asm_step_jump, asm_jump_def, w2n_n2w, LESS_MOD] >>
      Cases_on `FLOOKUP (build_offset_to_pc p) off` >> simp[asm_state_component_equality]) >>
  pop_assum (mk_asm "jumpstep") >>
  asm "jumpstep" (qspec_then `t0 with as_pc := pc v+2` mp_tac) >> simp[] >>
  disch_then (fn th => asm "progress" (qspecl_then
    [`v2`,`t0 with <|as_stack := n2w off::t0.as_stack; as_pc := pc v+2|>`]
    (mp_tac o SIMP_RULE (srw_ss()) [th]))) >>
  Cases_on `FLOOKUP (build_offset_to_pc p) off` >> simp[] >>
  rename1 `FLOOKUP _ off = SOME dest` >>
  disch_then (qx_choose_then `z` strip_assume_tac) >>
  `dest = pc z` by
    (qpat_x_assum `Shape p cc req pc height need tag boolean z _` mp_tac >>
     asm "shape" (fn th => simp[th, LET_THM])) >>
  asm "edges" (qspecl_then [`v2`,`z`] mp_tac) >> simp[] >> disch_then strip_assume_tac >>
  `ALOOKUP dup_table "JUMP" = NONE /\ ALOOKUP swap_table "JUMP" = NONE /\
   asm_op_arity "JUMP" = 1` by EVAL_TAC >>
  qpat_x_assum `Flow p pc height tag boolean v2 z` mp_tac >>
  asm "flow" (fn th => rewrite_tac[th] >> CONV_TAC expand_bypass_names >> simp[]) >> strip_tac >>
  `height z = height v` by decide_tac >>
  `!k l o'. tag z k = SOME(l,o') ==> tag v k = SOME(l,o')` by
    (map_every qx_gen_tac [`j`,`lab`,`org`] >> strip_tac >>
     `tag v2 (j+1) = SOME(lab,org)` by
       (qpat_x_assum `!k l origin. tag z k = SOME(l,origin) ==> _`
          (qspecl_then [`j`,`lab`,`org`] mp_tac) >> simp[]) >>
     `tag v1 j = SOME(lab,org)` by
       (qpat_x_assum `!k l origin. tag v2 k = SOME(l,origin) ==> _`
          (qspecl_then [`j+1`,`lab`,`org`] mp_tac) >> simp[]) >>
     qpat_x_assum `!k l origin. tag v1 k = SOME(l,origin) ==> _`
       (qspecl_then [`j`,`lab`,`org`] mp_tac) >> simp[]) >>
  `!k. boolean z k ==> boolean v k` by
    (rpt strip_tac >> `boolean v2 (k+1)` by
       (qpat_x_assum `!k. boolean z k ==> _` (qspec_then `k` mp_tac) >> simp[]) >>
     `boolean v1 k` by
       (qpat_x_assum `!k. boolean v2 k ==> _` (qspec_then `k+1` mp_tac) >> simp[]) >>
     qpat_x_assum `!k. boolean v1 k ==> _` (qspec_then `k` mp_tac) >> simp[]) >>
  `rank z < rank v` by
    (Q_TAC (TRANS_TAC arithmeticTheory.LESS_TRANS) `rank v2` >> simp[] >>
     Q_TAC (TRANS_TAC arithmeticTheory.LESS_TRANS) `rank v1` >> simp[]) >>
  qexists_tac `z` >> asm "stepcount" (fn th => simp[th]) >> conj_tac
  >- (asm "reach" (fn th => simp[th]) >>
      qexistsl [`3`, `\k. if k=0 then v else if k=1 then v1 else if k=2 then v2 else z`] >>
      simp[] >> gen_tac >> `k < 3 ==> k=0 \/ k=1 \/ k=2` by decide_tac >>
      disch_tac >>
      qpat_x_assum `k < 3 ==> _` (fn th => drule_then STRIP_ASSUME_TAC th) >> simp[]) >>
  rpt strip_tac >>
  `asm_steps (SND(compute_label_offsets p)) (build_offset_to_pc p) p 1 t =
   AsmOK (t with as_pc := pc v+1)` by simp[] >>
  pop_assum (fn th => SUBST1_TAC (SIMP_RULE (srw_ss()) []
    (Q.SPEC `2` (MATCH_MP asm_steps_add_ok th)))) >>
  `asm_steps (SND(compute_label_offsets p)) (build_offset_to_pc p) p 1
     (t with as_pc := pc v+1) =
   AsmOK (t with <|as_pc := pc v+2; as_stack := n2w off::t.as_stack|>)` by
    (asm "pushstep" (qspec_then `t with as_pc := pc v+1` mp_tac) >>
     simp[asm_state_component_equality]) >>
  pop_assum (fn th => SUBST1_TAC (SIMP_RULE (srw_ss()) []
    (Q.SPEC `1` (MATCH_MP asm_steps_add_ok th)))) >>
  asm "jumpstep" (qspec_then `t with as_pc := pc v+2` mp_tac) >>
  simp[asm_state_component_equality, asm_state_fupdcanon]
QED

Resume merge_rename_root_bypass[uniform]:
  `need z ==> cc.cc_static` by
    (asm "inhabited" (qspec_then `z` mp_tac) >> simp[] >>
     disch_then (qx_choose_then `tz` mp_tac) >>
     asm "shape" (fn th => simp[th, LET_THM]) >>
     disch_then STRIP_ASSUME_TAC >>
     qpat_assum `tz.as_call_ctx = cc` (fn ctx =>
       qpat_assum `need z ==> tz.as_call_ctx.cc_static`
         (ACCEPT_TAC o REWRITE_RULE [ctx]))) >>
  qx_gen_tac `t` >> disch_then (fn th =>
    asm "foldS" (fn sf => asm "shape" (fn sh =>
      strip_assume_tac (BETA_RULE (REWRITE_RULE [sf,sh,LET_THM] th)) >>
      simp[sf,sh,LET_THM]))) >>
  map_every qx_gen_tac [`j`,`lab`,`org`] >> disch_tac >>
  `tag v j = SOME(lab,org)` by simp[] >>
  qpat_assum `!k l origin. tag v k = SOME(l,origin) ==> k < height v /\ _`
    (qspecl_then [`j`,`lab`,`org`] (drule_then ACCEPT_TAC))
QED

Resume merge_rename_root_bypass[restrict]:
  CONV_TAC expand_bypass_names >>
  conj_tac
  >- (asm "reach" (fn th => simp[th]) >> qexistsl [`0`, `\j. z`] >> simp[]) >>
  qabbrev_tac `live = equiv_class (Reach edge) V z` >>
  `!a. a IN live <=> a IN V /\ Reach edge z a` by simp[Abbr `live`] >>
  `!a b. Reach edge z a /\ edge a b ==> Reach edge z b` by
    (asm "reach" (fn th => rewrite_tac[th]) >> BETA_TAC >>
     map_every qx_gen_tac [`a`,`b`] >>
     disch_then (CONJUNCTS_THEN2
       (qx_choose_then `n` (qx_choose_then `path` strip_assume_tac)) assume_tac) >>
     qexistsl [`SUC n`, `\j. if j = SUC n then b else path j`] >>
     simp[] >> qx_gen_tac `k` >> strip_tac >>
     Cases_on `k = n` >- simp[] >>
     `k < n /\ k <> SUC n` by decide_tac >> simp[]) >>
  conj_tac >- suspend "restricted_open" >>
  qx_gen_tac `a` >> strip_tac >>
  qpat_x_assum `Reach edge z a` mp_tac >> asm "reach" (fn th => rewrite_tac[th]) >> BETA_TAC >>
  disch_then (qx_choose_then `n` (qx_choose_then `path` strip_assume_tac)) >>
  qexistsl [`n`,`path`] >> simp[] >> qx_gen_tac `k` >> disch_tac >>
  `edge (path k) (path (SUC k))` by simp[] >>
  `path k IN V` by (asm "edges" (qspecl_then [`path k`,`path (SUC k)`] mp_tac) >> simp[]) >>
  simp[] >> qexistsl [`k`,`path`] >> simp[] >> qx_gen_tac `j` >> disch_tac >>
  `j < n` by decide_tac >> simp[]
QED

Resume merge_rename_root_bypass[restricted_open]:
  asm "open" (fn th => rewrite_tac[th]) >>
  CONV_TAC expand_bypass_names >>
  SIMP_TAC bool_ss [EMPTY_SUBSET, DIFF_EMPTY] >>
  conj_tac
  >- (irule SUBSET_FINITE_I >> qexists_tac `V` >> simp[SUBSET_DEF]) >>
  `!a. a IN live ==> a IN V` by
    (qx_gen_tac `a` >> disch_tac >>
     qpat_assum `!a. a IN live <=> _` (qspec_then `a` mp_tac) >>
     asm_rewrite_tac[] >> strip_tac) >>
  conj_tac >- (rpt strip_tac >> first_assum (drule_then assume_tac) >>
               asm "inhabited" (drule_then ACCEPT_TAC)) >>
  conj_tac >- (rpt strip_tac >> first_assum (drule_then assume_tac) >>
               asm "bounds" (drule_then ACCEPT_TAC)) >>
  conj_tac
  >- (map_every qx_gen_tac [`a`,`b`] >> strip_tac >>
      asm "edges" (qspecl_then [`a`,`b`] (drule_then strip_assume_tac)) >>
      `Reach edge z b` by
        (qpat_assum `!a b. Reach edge z a /\ edge a b ==> Reach edge z b`
          (qspecl_then [`a`,`b`] mp_tac) >> simp[]) >>
      simp[]) >>
  map_every qx_gen_tac [`a`,`t`] >> strip_tac >>
  asm "progress" (qspecl_then [`a`,`t`] mp_tac) >>
  (impl_tac >- fs[]) >>
  disch_then (DISJ_CASES_THEN2 assume_tac
    (qx_choose_then `b` (qx_choose_then `u` strip_assume_tac)))
  >- (disj1_tac >> first_assum ACCEPT_TAC) >>
  disj2_tac >> qexistsl [`b`,`u`] >> fs[] >> gvs[]
QED

Finalise merge_rename_root_bypass
