Theory staticAbortOptMergeJumpdestsResidual
Ancestors
  staticAbortProtectedActualPrefix asmSymOwnCode codegenSymRel
  staticAbortOptMergeJumpdestsPrefix staticAbortOptMergeJumpdestsBypass
  asmOptMergeJumpdests asmSymPc asmSymBridge asmWf asmSymSem asmSem asmOptimizer
  stackOpAsmSim words list rich_list arithmetic finite_map pred_set

(* There can be no exceptional result from either of the two instructions
   that remain after an interior stop in the stub. *)
Theorem residual_stub_not_exceptional[local]:
  s.as_pc < LENGTH p /\
  (EL s.as_pc p = AsmPushLabel y \/ EL s.as_pc p = AsmOp "JUMP") ==>
  ~(asm_steps lo b p 1 s = AsmRevert u \/
    asm_steps lo b p 1 s = AsmFault u)
Proof
  strip_tac >> rewrite_tac[numLib.num_CONV ``1:num``] >>
  simp[asm_steps_def, asm_step_jump, asm_jump_def] >-
    (simp[asm_step_def] >> Cases_on `FLOOKUP lo y` >> simp[]) >>
  Cases_on `s.as_stack` >> simp[] >> Cases_on `FLOOKUP b (w2n h)` >> simp[]
QED

val residual_names_conv =
  TOP_DEPTH_CONV (Unwind.UNWIND_FORALL_CONV ORELSEC BETA_CONV)

Theorem merge_rename_short_root_mode:
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
!q. q = MAP (rename_push_label x y) p ==>
!I'. I' = EL a.sym_base.as_pc p ==>
!named. named = (\prog l j.
  ?off. FLOOKUP (SND(compute_label_offsets prog)) l = SOME off /\
        off < dimword(:256) /\ FLOOKUP (build_offset_to_pc prog) off = SOME j) ==>
asm_static_wf p /\ p = pre ++ [AsmLabel x; next; third] ++ tail /\
((next = AsmLabel y /\ y <> x) \/
 (next = AsmPushLabel y /\ third = AsmOp "JUMP")) /\
x <> y /\ rn_rel x y a b /\ a.sym_base.as_pc < LENGTH p /\
a.sym_stack = Lab x 0 :: stk /\ b.sym_stack = Lab y 0 :: stk' /\
(I' = AsmOp "JUMP" \/ (I' = AsmOp "JUMPI" /\ ?c rest. stk = Val c :: rest /\ c <> 0w)) /\
sym_steps_mode allow_own p env own (SUC r) a = SymOK e /\ r < (if next = AsmLabel y then 1 else 3) /\
Open p cc req V {} rank pc height need tag boolean edge /\
w IN V /\ Shape p cc req pc height need tag boolean w cut /\
(if allow_own then asm_sym_rel_own (lo_reloc p installed) p env own else asm_sym_rel p env) cut e /\
(!k l o'. tag w k = SOME(l,o') ==> k < LENGTH e.sym_stack /\ EL k e.sym_stack = Lab l 0) /\
(!k. boolean w k ==> k < LENGTH e.sym_stack /\
       (EL k e.sym_stack = Val 0w \/ EL k e.sym_stack = Val 1w)) /\
(!l j. (named p l j <=> INDEX_OF (AsmLabel l) p = SOME j) /\
       (named q l j <=> INDEX_OF (AsmLabel l) p = SOME j)) ==>
?j z f. INDEX_OF (AsmLabel y) p = SOME j /\ sym_steps_mode allow_own q env own 1 b = SymOK f /\
  z IN V /\ Reach edge w z /\ pc z = j /\ f.sym_base.as_pc = j /\
  height z = LENGTH f.sym_stack /\ f.sym_base.as_requests = cut.as_requests /\
  f.sym_base.as_call_ctx = cut.as_call_ctx /\
  (!k l o'. tag z k = SOME(l,o') ==> k < LENGTH f.sym_stack /\
     ?l'. EL k f.sym_stack = Lab l' 0 /\ (l' = l \/ (l = x /\ l' = y))) /\
  (!k. boolean z k ==> k < LENGTH f.sym_stack /\
       (EL k f.sym_stack = Val 0w \/ EL k f.sym_stack = Val 1w))
Proof
  ntac 7 (gen_tac >> disch_then assume_tac) >>
  qabbrev_tac `d:num = if next = AsmLabel y then 1 else 3` >>
  qpat_x_assum `Abbrev (d = _)`
    (assume_tac o REWRITE_RULE [markerTheory.Abbrev_def]) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qpat_x_assum `p = _` (mk_asm "site") >>
  qpat_x_assum `(next = AsmLabel y /\ _) \/ _` (mk_asm "redex") >>
  qpat_x_assum `Shape = _` (mk_asm "shape") >>
  qpat_x_assum `Flow = _` (mk_asm "flow") >>
  qpat_x_assum `Open = _` (mk_asm "open") >>
  qpat_x_assum `Reach = _` (mk_asm "reach") >>
  qpat_x_assum `q = MAP _ _` (mk_asm "mapped") >>
  qpat_x_assum `d = if _ then _ else _` (mk_asm "distance") >>
  qpat_x_assum `named = _` (mk_asm "named") >>
  qpat_x_assum `I' = _` (mk_asm "fetch") >>
  qabbrev_tac `h = LENGTH pre` >>
  Q.SUBGOAL_THEN `?t. t.sym_base.as_pc = h /\
      (!j. INDEX_OF (AsmLabel y) p = SOME j ==>
           ?f. sym_steps_mode allow_own q env own 1 b = SymOK f /\ f.sym_base.as_pc = j /\
               rn_rel x y (sym_with_pc j t) f) /\
      ((r = 0 /\ e = t) \/
       (d = 3 /\ r = 1 /\ e = sym_with_pc (h+1) t) \/
       (d = 3 /\ r = 2 /\ e = (sym_with_pc (h+2) t with
                                 sym_stack := Lab y 0 :: t.sym_stack)))`
    (qx_choose_then `t` (CONJUNCTS_THEN2 assume_tac
      (CONJUNCTS_THEN2 assume_tac (mk_asm "residual"))))
  >- suspend "prefix" >>
  `e.sym_base.as_pc = pc w /\ LENGTH e.sym_stack = height w /\
   e.sym_base.as_requests = cut.as_requests /\ e.sym_base.as_call_ctx = cut.as_call_ctx`
    by (asm "shape" (fn sh =>
          qpat_assum `Shape p cc req pc height need tag boolean w cut`
            (map_every assume_tac o List.take o (fn th => (CONJUNCTS (SIMP_RULE bool_ss [sh] th),4)))) >>
        qpat_assum `(if allow_own then _ else asm_sym_rel p env) cut e` (fn th =>
          assume_tac (MATCH_MP protected_cut_relation_pc th) >>
          assume_tac (MATCH_MP protected_cut_relation_context th)) >>
        fs[]) >>
  sg `?z. z IN V /\ Reach edge w z /\ (?off. FLOOKUP (SND (compute_label_offsets p)) y = SOME off /\
             off < dimword(:256) /\ FLOOKUP (build_offset_to_pc p) off = SOME (pc z)) /\
     height z = LENGTH t.sym_stack /\
     (!k l o'. tag z k = SOME(l,o') ==> k < LENGTH t.sym_stack /\ EL k t.sym_stack = Lab l 0) /\
     (!k. boolean z k ==> k < LENGTH t.sym_stack /\
          (EL k t.sym_stack = Val 0w \/ EL k t.sym_stack = Val 1w))`
  >- suspend "select" >>
  `t.sym_base.as_requests = cut.as_requests /\ t.sym_base.as_call_ctx = cut.as_call_ctx`
    by (asm "residual" (DISJ_CASES_THEN strip_assume_tac) >> gvs[sym_with_pc_def]) >>
  `INDEX_OF (AsmLabel y) p = SOME (pc z)` by (
    asm "named" (fn eq =>
      qpat_assum `!l j. (_ <=> INDEX_OF (AsmLabel l) p = SOME j) /\ _`
        (qspecl_then [`y`,`pc z`]
          (irule o SIMP_RULE bool_ss [eq] o iffLR o CONJUNCT1))) >>
    qexists `off` >> simp[]) >>
  qpat_x_assum `!j. INDEX_OF (AsmLabel y) p = SOME j ==> _`
    (drule_then (qx_choose_then `f` strip_assume_tac)) >>
  qexistsl [`pc z`,`z`,`f`] >> simp[] >>
  qpat_x_assum `rn_rel x y (sym_with_pc _ t) f` mp_tac >>
  simp[rn_rel_def, sym_with_pc_def, LIST_REL_EL_EQN] >>
  strip_tac >> simp[] >>
  conj_tac >- (
    rpt strip_tac >>
    `k < LENGTH t.sym_stack /\ EL k t.sym_stack = Lab l 0` by metis_tac[] >>
    qpat_x_assum `!n. n < LENGTH t.sym_stack ==> _` (qspec_then `k` mp_tac) >>
    simp[sv_rel_def] >> metis_tac[]) >>
  rpt strip_tac >>
  `k < LENGTH t.sym_stack` by metis_tac[] >>
  qpat_x_assum `!n. n < LENGTH t.sym_stack ==> _` (qspec_then `k` mp_tac) >>
  qpat_x_assum `!k. boolean z k ==> _` (qspec_then `k` mp_tac) >>
  simp[] >> metis_tac[sv_rel_val]
QED

Resume merge_rename_short_root_mode[prefix]:
  asm "site" assume_tac >> asm "redex" assume_tac >>
  asm "fetch" (fn th => qpat_x_assum `I' = _ \/ _` (assume_tac o REWRITE_RULE [th])) >>
  drule_all_then (qx_choose_then `t` (map_every assume_tac o CONJUNCTS))
    (CONV_RULE residual_names_conv merge_rename_protected_redirect_cut_mode) >>
  qexists `t` >> conj_tac >- simp[Abbr `h`] >> conj_tac
  >- (asm "site" (fn site => asm "mapped" (fn mapped =>
        qpat_assum `!j. INDEX_OF (AsmLabel y) _ = SOME j ==> _`
          (ACCEPT_TAC o REWRITE_RULE [GSYM mapped] o REWRITE_RULE [GSYM site])))) >>
  `r < (if next = AsmLabel y then 1 else 3)` by
    (qpat_assum `r < d` mp_tac >> asm "distance" (fn th => rewrite_tac[th])) >>
  qpat_assum `r < (if _ then _ else _) ==> _` (drule_then mp_tac) >>
  simp[markerLib.L "distance", Abbr `h`]
QED

Resume merge_rename_short_root_mode[select]:
  Cases_on `r = 0`
  >- suspend "at_label" >>
  sg `next = AsmPushLabel y /\ third = AsmOp "JUMP" /\ h+2 < LENGTH p /\
      EL (h+1) p = AsmPushLabel y /\ EL (h+2) p = AsmOp "JUMP"`
  >- (asm "redex" (DISJ_CASES_THEN strip_assume_tac)
      >- (`d = 1` by (asm "distance" mp_tac >> simp[]) >>
          qpat_assum `r < d` mp_tac >> qpat_assum `r <> 0` mp_tac >> simp[] >> (gvs[])) >>
      asm "site" (fn th => simp[th, Abbr `h`, APPEND, EL_APPEND_EQN])) >>
  qpat_assum `Open p cc req V {} rank pc height need tag boolean edge`
    (fn th => asm "open" (fn opth =>
      assume_tac (SIMP_RULE (srw_ss()) [EMPTY_SUBSET, DIFF_EMPTY]
        (CONV_RULE residual_names_conv (REWRITE_RULE [opth] th))))) >>
  pop_assum (CONJUNCTS_THEN2 kall_tac
    (CONJUNCTS_THEN2 (mk_asm "inhabited")
      (CONJUNCTS_THEN2 (mk_asm "bounds")
        (CONJUNCTS_THEN2 (mk_asm "edges") (mk_asm "progress"))))) >>
  sg `!s. s IN V /\
      (EL (pc s) p = AsmPushLabel y \/ EL (pc s) p = AsmOp "JUMP") ==>
      ?v. edge s v`
  >- suspend "successor" >>
  pop_assum (mk_asm "successor") >>
  Q.SUBGOAL_THEN `?v. v IN V /\ pc v = h+2 /\ (edge w v \/ v = w) /\
      height v = LENGTH t.sym_stack + 1 /\
      (!l o'. tag v 0 = SOME(l,o') ==> l = y) /\
      (!k l o'. tag v (k+1) = SOME(l,o') ==>
         k < LENGTH t.sym_stack /\ EL k t.sym_stack = Lab l 0) /\
      (!k. boolean v (k+1) ==> k < LENGTH t.sym_stack /\
         (EL k t.sym_stack = Val 0w \/ EL k t.sym_stack = Val 1w))`
    (qx_choose_then `v` (map_every assume_tac o CONJUNCTS))
  >- suspend "before_jump" >>
  suspend "after_jump"
QED

Resume merge_rename_short_root_mode[at_label]:
  sg `e = t /\ pc w = LENGTH pre`
  >- (asm "residual" (DISJ_CASES_THEN strip_assume_tac) >> gvs[Abbr `h`]) >>
  sg `?z off. z IN V /\ Reach edge w z /\ height z = height w /\
       FLOOKUP (SND(compute_label_offsets p)) y = SOME off /\ off < dimword(:256) /\
       FLOOKUP (build_offset_to_pc p) off = SOME (pc z) /\
       (!k l o'. tag z k = SOME(l,o') ==> tag w k = SOME(l,o')) /\
       (!k. boolean z k ==> boolean w k)`
  >- suspend "bypass" >>
  qpat_x_assum `e = t` SUBST_ALL_TAC >>
  qexists `z` >> simp[] >> metis_tac[]
QED

Resume merge_rename_short_root_mode[bypass]:
  asm "site" assume_tac >> asm "redex" assume_tac >>
  asm "shape" (fn sh => asm "flow" (fn fl => asm "open" (fn opth =>
    qpat_assum `Open p cc req V {} rank pc height need tag boolean edge`
      (map_every assume_tac o CONJUNCTS o
       SIMP_RULE bool_ss [pairTheory.UNCURRY_DEF] o
       CONV_RULE residual_names_conv o REWRITE_RULE [opth, sh, fl])))) >>
  drule_all_then (qx_choose_then `z` (qx_choose_then `off`
      (map_every assume_tac o CONJUNCTS)))
    (SIMP_RULE bool_ss [pairTheory.UNCURRY_DEF]
      (CONV_RULE residual_names_conv merge_rename_root_bypass)) >>
  qexistsl [`z`,`off`] >> asm "reach" (fn th => simp[th])
QED

Resume merge_rename_short_root_mode[successor]:
  qx_gen_tac `s` >>
  disch_then (CONJUNCTS_THEN2 assume_tac (mk_asm "instruction")) >>
  asm "inhabited" (drule_then (qx_choose_then `st` assume_tac)) >>
  `st.as_pc = pc s` by (
    asm "shape" (fn sh =>
      qpat_assum `Shape p cc req pc height need tag boolean s st`
        (ACCEPT_TAC o CONJUNCT1 o SIMP_RULE bool_ss [sh]))) >>
  `st.as_pc < LENGTH p` by (asm "bounds" (drule_then mp_tac) >> simp[]) >>
  Q.SUBGOAL_THEN `EL st.as_pc p = AsmPushLabel y \/ EL st.as_pc p = AsmOp "JUMP"`
    assume_tac
  >- (asm "instruction" mp_tac >> simp[]) >>
  asm "progress" (qspecl_then [`s`,`st`] mp_tac) >> simp[] >>
  disch_then (DISJ_CASES_THEN2 (qx_choose_then `u` mp_tac)
    (qx_choose_then `v` (qx_choose_then `u` strip_assume_tac)))
  >- (drule_all residual_stub_not_exceptional >> simp[]) >>
  qexists `v` >> first_assum ACCEPT_TAC
QED

Resume merge_rename_short_root_mode[before_jump]:
  Cases_on `r = 1` >- suspend "at_push" >>
  `e.sym_base.as_pc = h+2 /\ e.sym_stack = Lab y 0 :: t.sym_stack`
    by (asm "residual" (DISJ_CASES_THEN strip_assume_tac) >> gvs[sym_with_pc_def]) >>
  `height w = LENGTH t.sym_stack + 1`
    by gvs[] >>
  qexists `w` >> simp[] >>
  conj_tac
  >- (rpt strip_tac >>
      qpat_assum `!k l origin. tag w k = SOME(l,origin) ==> _` drule >>
      gvs[]) >>
  conj_tac >- (
    rpt gen_tac >> disch_tac >>
    qpat_assum `!k l origin. tag w k = SOME(l,origin) ==> _` drule >>
    gvs[GSYM ADD1]) >>
  rpt gen_tac >> disch_tac >>
  qpat_assum `!k. boolean w k ==> _` drule >> gvs[GSYM ADD1]
QED

Resume merge_rename_short_root_mode[at_push]:
  `pc w = h+1 /\ e.sym_stack = t.sym_stack` by (
    asm "residual" (DISJ_CASES_THEN strip_assume_tac)
    >- gvs[sym_with_pc_def] >> simp[sym_with_pc_def]) >>
  asm "successor" (qspec_then `w` mp_tac) >> simp[] >>
  disch_then (qx_choose_then `v` assume_tac) >>
  asm "edges" (qspecl_then [`w`,`v`] (drule_then mp_tac)) >>
  asm "flow" (fn th => rewrite_tac[th] >> CONV_TAC residual_names_conv >> simp[]) >>
  strip_tac >>
  `height w = LENGTH t.sym_stack` by gvs[] >>
  qexists `v` >> simp[] >>
  conj_tac >- (
    rpt gen_tac >> disch_tac >>
    metisTools.METIS_TAC []) >>
  conj_tac >- (
    qx_gen_tac `k` >> qx_gen_tac `l` >> qx_gen_tac `o'` >> disch_tac >>
    qpat_assum `!k l origin. tag v k = SOME(l,origin) ==> _`
      (qspecl_then [`k+1`,`l`,`o'`]
        (drule_then (strip_assume_tac o SIMP_RULE (srw_ss()) [GSYM ADD1]))) >>
    qpat_assum `e.sym_stack = t.sym_stack` (fn eq =>
      qpat_assum `!k l origin. tag w k = SOME(l,origin) ==> _`
        (qspecl_then [`k`,`l`,`o'`] (drule_then (mp_tac o REWRITE_RULE [eq])))) >>
    simp[NoAsms]) >>
  qx_gen_tac `k` >> disch_tac >>
  qpat_assum `!k. boolean v k ==> _`
    (qspec_then `k+1`
      (drule_then (strip_assume_tac o SIMP_RULE (srw_ss()) [GSYM ADD1]))) >>
  qpat_assum `e.sym_stack = t.sym_stack` (fn eq =>
    qpat_assum `!k. boolean w k ==> _`
      (qspec_then `k` (drule_then (mp_tac o REWRITE_RULE [eq])))) >>
  simp[NoAsms]
QED

Resume merge_rename_short_root_mode[after_jump]:
  asm "successor" (qspec_then `v` mp_tac) >> simp[] >>
  disch_then (qx_choose_then `z` assume_tac) >>
  `ALOOKUP dup_table "JUMP" = NONE /\ ALOOKUP swap_table "JUMP" = NONE /\
   asm_op_arity "JUMP" = 1` by EVAL_TAC >>
  asm "edges" (qspecl_then [`v`,`z`] (drule_then mp_tac)) >>
  asm "flow" (fn th =>
    CONV_TAC (LAND_CONV (REWRITE_CONV [th] THENC residual_names_conv)) >> simp[SimpLHS]) >>
  disch_then strip_assume_tac >>
  `height z = LENGTH t.sym_stack` by decide_tac >>
  qexists `z` >> simp[] >>
  conj_tac >- suspend "reach" >>
  conj_tac >- (
    `l = y` by metis_tac[] >>
    qpat_assum `l = y` (fn eq =>
      qpat_assum `FLOOKUP (SND (compute_label_offsets p)) l = SOME off`
        (assume_tac o REWRITE_RULE [eq])) >>
    qexists `off` >> simp[]) >>
  conj_tac >- (
    qx_gen_tac `k` >> qx_gen_tac `lab` >> qx_gen_tac `orig` >> disch_tac >>
    qpat_assum `height z = LENGTH t.sym_stack` (fn eq =>
      qpat_assum `!k l origin. tag z k = SOME(l,origin) ==> _`
        (qspecl_then [`k`,`lab`,`orig`]
          (drule_then (strip_assume_tac o SIMP_RULE (srw_ss()) [eq])))) >>
    qpat_assum `!k l origin. tag v (k+1) = SOME(l,origin) ==> _`
      (qspecl_then [`k`,`lab`,`orig`] (drule_then ACCEPT_TAC))) >>
  qx_gen_tac `k` >> disch_tac >>
  qpat_assum `height z = LENGTH t.sym_stack` (fn eq =>
    qpat_assum `!k. boolean z k ==> _`
      (qspec_then `k` (drule_then (strip_assume_tac o SIMP_RULE (srw_ss()) [eq])))) >>
  qpat_assum `!k. boolean v (k+1) ==> _` (qspec_then `k` (drule_then ACCEPT_TAC))
QED

Resume merge_rename_short_root_mode[reach]:
  asm "reach" (fn th => simp[th]) >>
  Cases_on `v = w`
  >- (qexistsl [`1`,`\k. if k = 0 then w else z`] >> simp[] >>
      qpat_assum `v = w` (SUBST1_TAC o SYM) >>
      qpat_assum `edge v z` ACCEPT_TAC) >>
  `edge w v` by (
    qpat_assum `edge w v \/ v = w`
      (DISJ_CASES_THEN2 ACCEPT_TAC (fn eq => fs[eq]))) >>
  qexistsl [`2`,`\k. if k = 0 then w else if k = 1 then v else z`] >>
  simp[] >> qx_gen_tac `k` >> disch_tac >>
  `k = 0 \/ k = 1` by decide_tac >> simp[]
QED

Finalise merge_rename_short_root_mode

Theorem merge_rename_short_root:
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
!q. q = MAP (rename_push_label x y) p ==>
!I'. I' = EL a.sym_base.as_pc p ==>
!named. named = (\prog l j.
  ?off. FLOOKUP (SND(compute_label_offsets prog)) l = SOME off /\
        off < dimword(:256) /\ FLOOKUP (build_offset_to_pc prog) off = SOME j) ==>
asm_static_wf p /\ p = pre ++ [AsmLabel x; next; third] ++ tail /\
((next = AsmLabel y /\ y <> x) \/
 (next = AsmPushLabel y /\ third = AsmOp "JUMP")) /\
x <> y /\ rn_rel x y a b /\ a.sym_base.as_pc < LENGTH p /\
a.sym_stack = Lab x 0 :: stk /\ b.sym_stack = Lab y 0 :: stk' /\
(I' = AsmOp "JUMP" \/ (I' = AsmOp "JUMPI" /\ ?c rest. stk = Val c :: rest /\ c <> 0w)) /\
sym_steps p env (SUC r) a = SymOK e /\ r < (if next = AsmLabel y then 1 else 3) /\
Open p cc req V {} rank pc height need tag boolean edge /\
w IN V /\ Shape p cc req pc height need tag boolean w cut /\
asm_sym_rel p env cut e /\
(!k l o'. tag w k = SOME(l,o') ==> k < LENGTH e.sym_stack /\ EL k e.sym_stack = Lab l 0) /\
(!k. boolean w k ==> k < LENGTH e.sym_stack /\
       (EL k e.sym_stack = Val 0w \/ EL k e.sym_stack = Val 1w)) /\
(!l j. (named p l j <=> INDEX_OF (AsmLabel l) p = SOME j) /\
       (named q l j <=> INDEX_OF (AsmLabel l) p = SOME j)) ==>
?j z f. INDEX_OF (AsmLabel y) p = SOME j /\ sym_steps q env 1 b = SymOK f /\
  z IN V /\ Reach edge w z /\ pc z = j /\ f.sym_base.as_pc = j /\
  height z = LENGTH f.sym_stack /\ f.sym_base.as_requests = cut.as_requests /\
  f.sym_base.as_call_ctx = cut.as_call_ctx /\
  (!k l o'. tag z k = SOME(l,o') ==> k < LENGTH f.sym_stack /\
     ?l'. EL k f.sym_stack = Lab l' 0 /\ (l' = l \/ (l = x /\ l' = y))) /\
  (!k. boolean z k ==> k < LENGTH f.sym_stack /\
       (EL k f.sym_stack = Val 0w \/ EL k f.sym_stack = Val 1w))
Proof
  MATCH_ACCEPT_TAC (Q.INST [`allow_own` |-> `F`, `own` |-> `[]`]
    merge_rename_short_root_mode |> PURE_REWRITE_RULE [sym_steps_mode_def, COND_CLAUSES])
QED
