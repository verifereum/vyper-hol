Theory staticAbortOptMergeJumpdestsAssemble
Ancestors
  staticAbortOptMergeJumpdestsReplay staticAbortOptMergeJumpdestsResidual
  staticAbortOptMergeJumpdestsLayout staticAbortOptMergeJumpdestsArms
  staticAbortOptMergeJumpdestsLift staticAbortOptPruneUnreachableZeroOrigin
  staticAbortProtectedActualPrefix staticAbortOptMergeIszeroBranchPackage staticAbortRoleStep
  asmOptMergeJumpdests asmOptimizer asmSymBridge asmSymSem asmSem asmIR
  asmToBytecodeProofs asmDataEnv staticAbortStraight rat words finite_map pred_set
  indexedLists list rich_list arithmetic alist option pair

val expand_names = TOP_DEPTH_CONV
  (Unwind.UNWIND_FORALL_CONV ORELSEC BETA_CONV ORELSEC REWR_CONV LET_THM)
fun expand_lets th = CONV_RULE expand_names th

fun bind_names names =
  map_every (fn name => gen_tac >> disch_then (mk_asm name)) names

Theorem rename_synchronized_root[local]:
  rn_rel x y e f /\ asm_sym_rel p env cut e /\
  (!k l o'. tag k = SOME(l,o') ==> k < LENGTH e.sym_stack /\ EL k e.sym_stack = Lab l 0) /\
  (!k. boolean k ==> k < LENGTH e.sym_stack /\
    (EL k e.sym_stack = Val 0w \/ EL k e.sym_stack = Val 1w)) ==>
  f.sym_base.as_pc = cut.as_pc /\ LENGTH f.sym_stack = LENGTH cut.as_stack /\
  f.sym_base.as_call_ctx = cut.as_call_ctx /\ f.sym_base.as_requests = cut.as_requests /\
  (!k l o'. tag k = SOME(l,o') ==> k < LENGTH f.sym_stack /\
     ?a. EL k f.sym_stack = Lab a 0 /\ (a = l \/ (l = x /\ a = y))) /\
  (!k. boolean k ==> k < LENGTH f.sym_stack /\
    (EL k f.sym_stack = Val 0w \/ EL k f.sym_stack = Val 1w))
Proof
  strip_tac >>
  drule_then strip_assume_tac asm_sym_rel_pc >>
  qpat_assum `asm_sym_rel p env cut e`
    (CONJUNCTS_THEN2 kall_tac (CONJUNCTS_THEN2 strip_assume_tac kall_tac) o
      REWRITE_RULE [asm_sym_rel_def]) >>
  qpat_x_assum `rn_rel x y e f` (map_every assume_tac o CONJUNCTS o REWRITE_RULE[rn_rel_def]) >>
  qpat_x_assum `LIST_REL _ _ _` (CONJUNCTS_THEN2 assume_tac (mk_asm "elts") o REWRITE_RULE[LIST_REL_EL_EQN]) >>
  gns[] >>
  rpt conj_tac >> rpt gen_tac >> disch_tac
  >- (qpat_assum `!k l o'. tag k = _ ==> _` (drule_then strip_assume_tac) >>
      asm "elts" (qspec_then `k` mp_tac) >>
      simp[sv_rel_def] >> metis_tac[]) >>
  qpat_assum `!k. boolean k ==> _` (drule_then strip_assume_tac) >>
  asm "elts" (qspec_then `k` mp_tac) >>
  simp[sv_rel_val]
QED

(* Select a producer using the value in the actual stopped stack, not the
   old origin or the numeric offset.  The projection may drop a data label. *)
Theorem rename_root_choices[local]:
  !C. C = (\l j. ?off. FLOOKUP (SND (compute_label_offsets q)) l = SOME off /\
    off < dimword(:256) /\ FLOOKUP (build_offset_to_pc q) off = SOME j) ==>
  !Prod. Prod = (\i a. i < LENGTH q /\
    (EL i q = AsmPushLabel a \/ EL i q = AsmPushOfst a 0)) ==>
  !G. G = (\old choice. case old of NONE => choice = NONE
    | SOME (l,o') => ?i a. choice = SOME i /\ Prod i a /\ (a = l \/ l = x /\ a = y)) ==>
  !E. E = (\u. case u of NONE => NONE
    | SOME i => if ?a j. Prod i a /\ C a j
                then SOME((@a. Prod i a),i) else NONE) ==>
  sym_steps q env n (sym_init s) = SymOK f /\ LENGTH f.sym_stack = h /\
  (!k l o'. tag k = SOME(l,o') ==> k < LENGTH f.sym_stack /\
     ?a. EL k f.sym_stack = Lab a 0 /\ (a = l \/ (l = x /\ a = y))) ==>
  ?D. LENGTH D = h /\ (!k. k < h ==> G (tag k) (EL k D)) /\
    (!k a i. (if k < h then E (EL k D) else NONE) = SOME(a,i) ==>
      k < LENGTH f.sym_stack /\ EL k f.sym_stack = Lab a 0)
Proof
  bind_names ["canon", "prod", "admit", "expose"] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!k l o'. tag k = SOME(l,o') ==>
    ?i a. Prod i a /\ EL k f.sym_stack = Lab a 0 /\ (a = l \/ l = x /\ a = y)` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `!k l o'. tag k = _ ==> _` (drule_then strip_assume_tac) >>
     `MEM (Lab a 0) f.sym_stack` by metis_tac[EL_MEM] >>
     drule_all stopped_lab_zero_producer >> strip_tac >>
     qexistsl [`u.sym_base.as_pc`,`a`] >> simp[markerLib.L "prod"]) >>
  `!i a b. Prod i a /\ Prod i b ==> a = b` by
    (simp[markerLib.L "prod"] >> metis_tac[asm_inst_11, asm_inst_distinct]) >>
  qabbrev_tac `Choice = \k. case tag k of NONE => NONE
     | SOME (l,o') => SOME (@i. ?a. Prod i a /\ EL k f.sym_stack = Lab a 0 /\
                                      (a = l \/ l = x /\ a = y))` >>
  `!k l o'. tag k = SOME(l,o') ==> ?i a. Choice k = SOME i /\ Prod i a /\
     EL k f.sym_stack = Lab a 0 /\ (a = l \/ l = x /\ a = y)` by
    (rpt gen_tac >> disch_tac >>
     qpat_assum `!k l o'. tag k = _ ==> ?i a. _` (drule_then (mp_tac o SELECT_RULE)) >>
     simp[Abbr `Choice`]) >>
  qexists `GENLIST Choice h` >> simp[] >> conj_tac
  >- (rpt strip_tac >> Cases_on `tag k`
      >- simp[Abbr `Choice`, markerLib.L "admit"] >>
      PairCases_on `x'` >>
      qpat_assum `!k l o'. tag k = _ ==> ?i a. Choice k = _ /\ _`
        (drule_then (qx_choose_then `i` (qx_choose_then `a` (map_every assume_tac o CONJUNCTS)))) >>
      simp[markerLib.L "admit"] >> qexists `a` >> simp[]) >>
  rpt gen_tac >> Cases_on `k < h` >> simp[] >> disch_tac >>
  Cases_on `tag k` >- gns[Abbr `Choice`, markerLib.L "expose"] >>
  PairCases_on `x'` >>
  qpat_assum `!k l o'. tag k = _ ==> ?i a. Choice k = _ /\ _`
    (drule_then (qx_choose_then `j` (qx_choose_then `b` (map_every assume_tac o CONJUNCTS)))) >>
  `(@c. Prod j c) = b` by (SELECT_ELIM_TAC >> metis_tac[]) >>
  qpat_x_assum `E (Choice k) = _` mp_tac >> simp[markerLib.L "expose"]
QED

Theorem rename_protected_endpoint[local]:
  !Shape. Shape = (\p cc req pc height need tag boolean (i:num#num) (t:asm_state).
    t.as_pc = pc i /\ LENGTH t.as_stack = height i /\
    t.as_call_ctx = cc /\ t.as_requests = req /\
    (need i ==> t.as_call_ctx.cc_static) /\
    (!k l origin. tag i k = SOME(l,origin) ==>
       k < height i /\ origin < LENGTH p /\
       (EL origin p = AsmPushLabel l \/
        (?d. EL origin p = AsmPushOfst l d) \/ EL origin p = AsmDataLabel l) /\
       ?off dest. FLOOKUP (SND(compute_label_offsets p)) l = SOME off /\
       off < dimword(:256) /\ FLOOKUP (build_offset_to_pc p) off = SOME dest /\
       EL k t.as_stack = (n2w off:bytes32)) /\
    (!k. boolean i k ==> k < height i /\
       (EL k t.as_stack = 0w \/ EL k t.as_stack = 1w))) ==>
  !Flow. Flow = (\p pc height tag boolean (x:num#num) (y:num#num).
    !hi. hi = height x ==>
    !hj. hj = height y ==>
    !ins. ins = EL (pc x) p ==>
    !inherit. inherit = (\(src:num -> num option) (fresh:num -> (string#num)option) (bnew:num -> bool).
      (!k l origin. tag y k = SOME(l,origin) ==>
         k < hj /\ (fresh k = SOME(l,origin) \/
         ?a. src k = SOME a /\ a < hi /\ tag x a = SOME(l,origin))) /\
      (!k. boolean y k ==> k < hj /\
         (bnew k \/ ?a. src k = SOME a /\ a < hi /\ boolean x a))) ==>
    case ins of
      AsmLabel l => hj = hi /\ inherit (\k. SOME k) (\k. NONE) (\k. F)
    | AsmPush bs => hj = hi+1 /\
        inherit (\k. if k=0 then NONE else SOME(k-1)) (\k. NONE)
          (\k. k=0 /\ !t u.
            asm_step (SND(compute_label_offsets p)) (build_offset_to_pc p)
              (AsmPush bs) t = AsmOK u ==>
            (EL 0 u.as_stack = 0w \/ EL 0 u.as_stack = 1w))
    | AsmPushLabel l => hj = hi+1 /\
        inherit (\k. if k=0 then NONE else SOME(k-1))
          (\k. if k=0 then SOME(l,pc x) else NONE) (\k. F)
    | AsmPushOfst l d => hj = hi+1 /\
        inherit (\k. if k=0 then NONE else SOME(k-1))
          (\k. if k=0 /\ d=0 then SOME(l,pc x) else NONE) (\k. F)
    | AsmOp name =>
        (case ALOOKUP dup_table name of
           SOME n => n < hi /\ hj = hi+1 /\
             inherit (\k. SOME(if k=0 then n else k-1)) (\k. NONE) (\k. F)
         | NONE => case ALOOKUP swap_table name of
             SOME n => 0 < n /\ n < hi /\ hj = hi /\
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
  !Open. Open = (\p cc req (V:(num#num)->bool) X (rank:(num#num)->num) pc height need
    (tag:(num#num)->num->(string#num)option) (boolean:(num#num)->num->bool) edge.
    !S. S = Shape p cc req pc height need tag boolean ==>
    !target. target = (\x y. ?l origin off. tag x 0 = SOME(l,origin) /\
      FLOOKUP (SND(compute_label_offsets p)) l = SOME off /\ off < dimword(:256) /\
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
       (?y u. edge x y /\ asm_steps (SND(compute_label_offsets p)) (build_offset_to_pc p)
            p 1 t = AsmOK u /\ S y u))) ==>
  !q. q = MAP (rename_push_label x y) p ==>
  asm_static_wf p /\ p = pre ++ [AsmLabel x; next; third] ++ tail /\
  ((next = AsmLabel y /\ y <> x) \/ (next = AsmPushLabel y /\ third = AsmOp "JUMP")) /\
  sym_steps p env n (sym_init s) = SymOK e /\
  Open p cc req V {} rank pc height need tag boolean edge /\
  w IN V /\ Shape p cc req pc height need tag boolean w cut /\ asm_sym_rel p env cut e /\
  (!k l o'. tag w k = SOME(l,o') ==> k < LENGTH e.sym_stack /\ EL k e.sym_stack = Lab l 0) /\
  (!k. boolean w k ==> k < LENGTH e.sym_stack /\
     (EL k e.sym_stack = Val 0w \/ EL k e.sym_stack = Val 1w)) ==>
  ?m z f. sym_steps q env m (sym_init s) = SymOK f /\ z IN V /\
    f.sym_base.as_pc = pc z /\ LENGTH f.sym_stack = height z /\
    f.sym_base.as_call_ctx = cc /\ f.sym_base.as_requests = req /\
    (!k l o'. tag z k = SOME(l,o') ==> k < LENGTH f.sym_stack /\
       ?a. EL k f.sym_stack = Lab a 0 /\ (a = l \/ (l = x /\ a = y))) /\
    (!k. boolean z k ==> k < LENGTH f.sym_stack /\
       (EL k f.sym_stack = Val 0w \/ EL k f.sym_stack = Val 1w))
Proof
  bind_names ["shape", "flow", "open", "mapped"] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  asm "shape" (fn sh =>
    qpat_assum `Shape p cc req pc height need tag boolean w cut`
      (map_every assume_tac o CONJUNCTS o BETA_RULE o
       PURE_REWRITE_RULE [REWRITE_RULE [markerTheory.label_def] sh])) >>
  `rn_rel x y (sym_init s) (sym_init s)` by
    simp[rn_rel_def, sym_init_def, ml_rel_def, mem_blocks_ok_def] >>
  drule_all (expand_lets merge_rename_stopped_replay) >>
  asm "mapped" (pure_rewrite_tac o single o GSYM o REWRITE_RULE [markerTheory.label_def]) >>
  disch_then (DISJ_CASES_THEN2
    (qx_choose_then `m` (qx_choose_then `f` strip_assume_tac))
    (qx_choose_then `i` (qx_choose_then `m` (qx_choose_then `r`
      (qx_choose_then `u` (qx_choose_then `v` (qx_choose_then `stk`
        (qx_choose_then `stk'` (map_every assume_tac o CONJUNCTS)))))))))
  >- suspend "sync" >>
  suspend "short"
QED

Resume rename_protected_endpoint[sync]:
  drule_all rename_synchronized_root >> disch_then (map_every assume_tac o CONJUNCTS) >>
  qexistsl [`m`,`w`,`f`] >> simp[]
QED

Resume rename_protected_endpoint[short]:
  `!l j.
    ((?off. FLOOKUP (SND(compute_label_offsets p)) l = SOME off /\
            off < dimword(:256) /\ FLOOKUP (build_offset_to_pc p) off = SOME j) <=>
       INDEX_OF (AsmLabel l) p = SOME j) /\
    ((?off. FLOOKUP (SND(compute_label_offsets q)) l = SOME off /\
            off < dimword(:256) /\ FLOOKUP (build_offset_to_pc q) off = SOME j) <=>
       INDEX_OF (AsmLabel l) p = SOME j)` by
      (qspecl_then [`p`,`x`,`y`] mp_tac (expand_lets merge_rename_named_layout) >>
       impl_tac
       >- (conj_tac >- metis_tac[] >> first_assum ACCEPT_TAC) >>
       asm "mapped" (pure_rewrite_tac o single o GSYM o REWRITE_RULE [markerTheory.label_def]) >>
       disch_tac >> first_assum ACCEPT_TAC) >>
  asm "mapped" (fn ma => asm "open" (fn opn =>
    asm "flow" (fn fl => asm "shape" (fn sh =>
      let val eqs = map (REWRITE_RULE [markerTheory.label_def]) [opn,fl,sh,ma]
      in qpat_assum `Open p cc req V {} rank pc height need tag boolean edge`
           (assume_tac o expand_lets o PURE_REWRITE_RULE eqs) >>
         qpat_assum `!l j. (_ <=> INDEX_OF _ p = _) /\ _`
           (assume_tac o PURE_REWRITE_RULE eqs)
      end)))) >>
  mp_tac (Q.INST [`a` |-> `u`, `b` |-> `v`] (expand_lets merge_rename_short_root)) >>
  impl_tac >- (rpt (FIRST [first_assum ACCEPT_TAC, conj_tac])) >>
  asm "mapped" (pure_rewrite_tac o single o GSYM o REWRITE_RULE [markerTheory.label_def]) >>
  disch_then (qx_choose_then `j` (qx_choose_then `z` (qx_choose_then `f`
     (map_every assume_tac o CONJUNCTS)))) >>
  qexistsl [`m+1`,`z`,`f`] >>
  once_rewrite_tac[codegenSymRelTheory.sym_steps_add] >> simp[]
QED

Finalise rename_protected_endpoint

Theorem rename_actual_root[local]:
  !lo. lo = SND (compute_label_offsets q) ==>
  !otp. otp = build_offset_to_pc q ==>
  asm_sym_rel q env t f /\ t.as_pc = i /\ LENGTH t.as_stack = h /\
  t.as_call_ctx = cc /\ t.as_requests = req /\ (need ==> cc.cc_static) /\
  (!k l orig. tag k = SOME(l,orig) ==>
    k < h /\ orig < LENGTH q /\
    (EL orig q = AsmPushLabel l \/ EL orig q = AsmPushOfst l 0) /\
    ?off j. FLOOKUP lo l = SOME off /\ off < dimword(:256) /\ FLOOKUP otp off = SOME j) /\
  (!k l orig. tag k = SOME(l,orig) ==> k < LENGTH f.sym_stack /\ EL k f.sym_stack = Lab l 0) /\
  (!k. boolean k ==> k < LENGTH f.sym_stack /\
    (EL k f.sym_stack = Val 0w \/ EL k f.sym_stack = Val 1w)) ==>
  t.as_pc = i /\ LENGTH t.as_stack = h /\ t.as_call_ctx = cc /\
  t.as_requests = req /\ (need ==> t.as_call_ctx.cc_static) /\
  (!k l orig. tag k = SOME(l,orig) ==>
    k < h /\ orig < LENGTH q /\
    (EL orig q = AsmPushLabel l \/ (?d. EL orig q = AsmPushOfst l d) \/ EL orig q = AsmDataLabel l) /\
    ?off j. FLOOKUP lo l = SOME off /\ off < dimword(:256) /\ FLOOKUP otp off = SOME j /\
           EL k t.as_stack = (n2w off:bytes32)) /\
  (!k. boolean k ==> k < h /\ (EL k t.as_stack = 0w \/ EL k t.as_stack = 1w))
Proof
  CONV_TAC expand_names >> strip_tac >> simp[] >>
  qpat_x_assum `asm_sym_rel q env t f`
    (CONJUNCTS_THEN2 (CONJUNCTS_THEN2 assume_tac (mk_asm "slots") o
                     REWRITE_RULE[LIST_REL_EL_EQN]) kall_tac o REWRITE_RULE[asm_sym_rel_def]) >>
  conj_tac
  >- (rpt gen_tac >> disch_tac >>
      qpat_assum `!k l orig. _ ==> k < h /\ _` (drule_then strip_assume_tac) >>
      qpat_assum `!k l orig. _ ==> k < LENGTH f.sym_stack /\ _` (drule_then strip_assume_tac) >>
      asm "slots" (qspec_then `k` mp_tac) >> simp[sval_conc_def] >>
      metis_tac[]) >>
  rpt gen_tac >> disch_tac >>
  first_x_assum (drule_then strip_assume_tac) >>
  asm "slots" (qspec_then `k` mp_tac) >> simp[sval_conc_def]
QED

(* The arm table specifies the image of the edge relation.  Use uniqueness
   of a canonical destination to turn the jump obligations in either direction. *)
Theorem rename_arm_image[local]:
  !i (H:num#num->num) (Pc:num#num->num) R (P:num->bool) h.
    (!j k. P j /\ P k ==> j=k) ==>
    ((?j. P j) /\ (!j hj. (?v. R v /\ Pc v=j /\ H v=hj) <=> (j=i \/ P j) /\ hj=h) <=>
     (?v. R v /\ Pc v=i /\ H v=h) /\
     (?v. R v /\ P (Pc v) /\ H v=h) /\
     (!v. R v ==> (Pc v=i \/ P (Pc v)) /\ H v=h))
Proof
  rpt gen_tac >> disch_tac >> eq_tac >> metis_tac[]
QED

Theorem rename_row_dispatch[local]:
  !lo. lo = SND (compute_label_offsets p) ==>
  !otp. otp = build_offset_to_pc p ==>
  !Dest. Dest = (\j. ?l (orig:num). tag 0 = SOME(l,orig) /\
       ?off. FLOOKUP lo l = SOME off /\ off < dimword(:256) /\ FLOOKUP otp off = SOME j) ==>
  !A. A = (\j hj. ?v:num#num. R v /\ Pc v=j /\ H v=hj) ==>
  !fall. fall = (\j. j=i+1) ==>
  !clear. clear = (\n. !k. k<n ==> tag k=NONE) ==>
  !arm. arm = (\P h. ?v. R v /\ P (Pc v) /\ H v=h) ==>
  !legal. legal = (\P h. !v. R v ==> P (Pc v) /\ H v=h) ==>
  !next. next = (\h. arm fall h /\ legal fall h) ==>
  !stop. stop = (\n. n<=h /\ clear n /\ !v. ~R v) ==>
  !term. term = (\name. MEM name ["SSTORE";"TSTORE";"LOG0";"LOG1";"LOG2";"LOG3";"LOG4"]) ==>
  ((case EL i p of
    AsmLabel l => (!j hj. A j hj <=> fall j /\ hj=h)
  | AsmPush bs => (!j hj. A j hj <=> fall j /\ hj=h+1)
  | AsmPushLabel l => IS_SOME (FLOOKUP lo l) /\ (!j hj. A j hj <=> fall j /\ hj=h+1)
  | AsmPushOfst l d => IS_SOME (FLOOKUP lo l) /\ (!j hj. A j hj <=> fall j /\ hj=h+1)
  | AsmOp name =>
      (name="INVALID" \/ (name="REVERT" /\ 2<=h /\ clear 2) \/
       (term name /\ asm_op_arity name<=h /\ clear (asm_op_arity name) /\ cc.cc_static)) /\
      (!j hj. ~A j hj) \/
      (case ALOOKUP dup_table name of
         SOME n => n<h /\ (!j hj. A j hj <=> fall j /\ hj=h+1)
       | NONE => case ALOOKUP swap_table name of
           SOME n => 0<n /\ n<h /\ (!j hj. A j hj <=> fall j /\ hj=h)
         | NONE =>
             if name="JUMP" then 1<=h /\ (?j. Dest j) /\
               (!j hj. A j hj <=> Dest j /\ hj=h-1)
             else if name="JUMPI" then 2<=h /\ tag 1=NONE /\ (?j. Dest j) /\
               (!j hj. A j hj <=> (fall j \/ Dest j) /\ hj=h-2)
             else ?m. static_abort_straight name m /\ asm_op_arity name<=h /\
               clear (asm_op_arity name) /\
               (!j hj. A j hj <=> fall j /\ hj=h-asm_op_arity name+m))
  | _ => F) <=>
  (case EL i p of
    AsmLabel l => next h
  | AsmPush bs => next (h+1)
  | AsmPushLabel l => IS_SOME (FLOOKUP lo l) /\ next (h+1)
  | AsmPushOfst l d => IS_SOME (FLOOKUP lo l) /\ next (h+1)
  | AsmOp name =>
      if name="INVALID" then stop 0
      else if name="REVERT" then stop 2
      else if term name then cc.cc_static /\ stop (asm_op_arity name)
      else (case ALOOKUP dup_table name of
              SOME n => n<h /\ next (h+1)
            | NONE => case ALOOKUP swap_table name of
                SOME n => 0<n /\ n<h /\ next h
              | NONE =>
                if name="JUMP" then 1<=h /\ arm Dest (h-1) /\ legal Dest (h-1)
                else if name="JUMPI" then 2<=h /\ tag 1=NONE /\
                  arm fall (h-2) /\ arm Dest (h-2) /\ legal (\j. fall j \/ Dest j) (h-2)
                else ?m. static_abort_straight name m /\ asm_op_arity name<=h /\
                         clear (asm_op_arity name) /\ next (h-asm_op_arity name+m))
  | _ => F))
Proof
  bind_names [".lo",".otp","target","image",".fall",".clear",".arm",".legal",".next",".stop",".term"] >>
  `!j k. Dest j /\ Dest k ==> j=k` by (simp[markerLib.L "target"] >> metis_tac[SOME_11, pairTheory.PAIR_EQ]) >>
  `!n. (!j hj. A j hj <=> fall j /\ hj=n) <=> next n` by
    (simp[markerLib.L "image", markerLib.L ".next", markerLib.L ".fall",
          markerLib.L ".arm", markerLib.L ".legal"] >> metis_tac[]) >>
  `(!j hj. ~A j hj) <=> !v. ~R v` by (simp[markerLib.L "image"] >> metis_tac[]) >>
  `!n. (?j. Dest j) /\ (!j hj. A j hj <=> Dest j /\ hj=n) <=> arm Dest n /\ legal Dest n` by
    (simp[markerLib.L "image", markerLib.L ".arm", markerLib.L ".legal"] >> metis_tac[]) >>
  `!n. (?j. Dest j) /\ (!j hj. A j hj <=> (fall j \/ Dest j) /\ hj=n) <=>
       arm fall n /\ arm Dest n /\ legal (\j. fall j \/ Dest j) n` by
    (simp[markerLib.L "image", markerLib.L ".arm", markerLib.L ".legal", markerLib.L ".fall"] >>
     metis_tac[rename_arm_image]) >>
  Cases_on `EL i p` >> simp[] >> rename1 `AsmOp name` >>
  Cases_on `name="INVALID"` >> simp[markerLib.L ".stop"]
  >- gvs[dup_table_def, swap_table_def, static_abort_straight_def, markerLib.L ".clear"]
  >> Cases_on `name="REVERT"` >> simp[markerLib.L ".stop"]
  >- gvs[dup_table_def, swap_table_def, static_abort_straight_def, markerLib.L ".term", CONJ_ASSOC]
  >> Cases_on `term name` >> simp[markerLib.L ".stop"]
  >- (qpat_x_assum `term name` mp_tac >> simp[markerLib.L ".term"] >>
      strip_tac >> gvs[dup_table_def, swap_table_def, static_abort_straight_def, AC CONJ_ASSOC CONJ_COMM])
  >> Cases_on `ALOOKUP dup_table name` >> simp[] >>
  Cases_on `ALOOKUP swap_table name` >> simp[] >>
  Cases_on `name="JUMP"` >> simp[AC CONJ_ASSOC CONJ_COMM] >>
  Cases_on `name="JUMPI"` >> simp[AC CONJ_ASSOC CONJ_COMM]
QED

Theorem rename_rank_compress[local]:
  FINITE V ==>
  ?N. !a b. a IN V /\ b IN V /\ rat$rat_les (r a) (r b) ==> (N a:num) < N b
Proof
  strip_tac >> qabbrev_tac `L = \a. {v | v IN V /\ rat$rat_les (r v) (r a)}` >>
  qexists `\a. CARD (L a)` >> rpt strip_tac >> BETA_TAC >> irule CARD_PSUBSET >>
  conj_tac
  >- (irule SUBSET_FINITE_I >> qexists `V` >> simp[Abbr `L`, SUBSET_DEF]) >>
  simp[PSUBSET_MEMBER] >> conj_tac
  >- (simp[Abbr `L`, SUBSET_DEF] >> metis_tac[RAT_LES_TRANS]) >>
  qexists `a` >> simp[Abbr `L`, RAT_LES_REF]
QED

Theorem rename_site_wf[local]:
  asm_static_wf p /\ p = pre ++ [AsmLabel x; next; third] ++ tail /\
  ((next = AsmLabel y /\ y <> x) \/ (next = AsmPushLabel y /\ third = AsmOp "JUMP")) ==>
  asm_static_wf (MAP (rename_push_label x y) p)
Proof
  strip_tac >> irule rename_static_wf >> simp[] >>
  qpat_x_assum `p = _` SUBST1_TAC >> simp[asm_label_refs_def, MAP_APPEND, FLAT_APPEND]
QED

(* These proof-side rewrites keep the common lexical certificate folded except
   at the boundary of a consumed helper theorem. *)
fun named_equations [] k = k []
  | named_equations (label::labels) k =
      asm label (fn th => named_equations labels
        (fn rest => k (REWRITE_RULE [markerTheory.label_def] th::rest)))

fun unfold_named labels = named_equations labels
  (fn eqs => pure_rewrite_tac eqs >> BETA_TAC)

fun unfold_fact labels pat ttac = named_equations labels
  (fn eqs => qpat_assum pat (ttac o expand_lets o PURE_REWRITE_RULE eqs))

Theorem merge_rename_covered_cut:
  !C. C = (\r l j. ?off. FLOOKUP (SND (compute_label_offsets r)) l = SOME off /\
    off < dimword(:256) /\ FLOOKUP (build_offset_to_pc r) off = SOME j) ==>
  !Target. Target = (\r tags j. ?l orig off. tags 0 = SOME(l,orig) /\
    FLOOKUP (SND (compute_label_offsets r)) l = SOME off /\
    off < dimword(:256) /\ FLOOKUP (build_offset_to_pc r) off = SOME j) ==>
  !Shape. Shape = (\r cc req pc height need tag boolean (v:num#num) (t:asm_state).
    t.as_pc = pc v /\ LENGTH t.as_stack = height v /\
    t.as_call_ctx = cc /\ t.as_requests = req /\ (need v ==> t.as_call_ctx.cc_static) /\
    (!k l orig. tag v k = SOME(l,orig) ==>
       k < height v /\ orig < LENGTH r /\
       (EL orig r = AsmPushLabel l \/ (?d. EL orig r = AsmPushOfst l d) \/ EL orig r = AsmDataLabel l) /\
       ?off j. FLOOKUP (SND (compute_label_offsets r)) l = SOME off /\
         off < dimword(:256) /\ FLOOKUP (build_offset_to_pc r) off = SOME j /\
         EL k t.as_stack = (n2w off:bytes32)) /\
    (!k. boolean v k ==> k < height v /\ (EL k t.as_stack = 0w \/ EL k t.as_stack = 1w))) ==>
  !Flow. Flow = (\r pc height tag boolean (a:num#num) (b:num#num).
    !hi. hi = height a ==>
    !hj. hj = height b ==>
    !ins. ins = EL (pc a) r ==>
    !inherit. inherit = (\(src:num->num option) (fresh:num->(string#num)option) (bnew:num->bool).
      (!k l orig. tag b k = SOME(l,orig) ==>
        k<hj /\ (fresh k = SOME(l,orig) \/ ?j. src k = SOME j /\ j<hi /\ tag a j = SOME(l,orig))) /\
      (!k. boolean b k ==> k<hj /\ (bnew k \/ ?j. src k = SOME j /\ j<hi /\ boolean a j))) ==>
    case ins of
      AsmLabel l => hj=hi /\ inherit (\k. SOME k) (\k. NONE) (\k. F)
    | AsmPush bs => hj=hi+1 /\
        inherit (\k. if k=0 then NONE else SOME(k-1)) (\k. NONE)
          (\k. k=0 /\ !t u. asm_step (SND (compute_label_offsets r)) (build_offset_to_pc r)
                                    (AsmPush bs) t = AsmOK u ==>
                         EL 0 u.as_stack = 0w \/ EL 0 u.as_stack = 1w)
    | AsmPushLabel l => hj=hi+1 /\ inherit (\k. if k=0 then NONE else SOME(k-1))
                                         (\k. if k=0 then SOME(l,pc a) else NONE) (\k. F)
    | AsmPushOfst l d => hj=hi+1 /\ inherit (\k. if k=0 then NONE else SOME(k-1))
                                         (\k. if k=0 /\ d=0 then SOME(l,pc a) else NONE) (\k. F)
    | AsmOp name =>
        (case ALOOKUP dup_table name of
           SOME n => n<hi /\ hj=hi+1 /\
             inherit (\k. SOME(if k=0 then n else k-1)) (\k. NONE) (\k. F)
         | NONE => case ALOOKUP swap_table name of
             SOME n => 0<n /\ n<hi /\ hj=hi /\
               inherit (\k. SOME(if k=0 then n else if k=n then 0 else k)) (\k. NONE) (\k. F)
           | NONE =>
               !n. n = asm_op_arity name ==>
               !m. m = hj+asm_op_arity name-hi ==>
               n<=hi /\ hj=m+(hi-n) /\ ((name="JUMP" \/ name="JUMPI") ==> m=0) /\
               inherit (\k. if k<m then NONE else SOME(k-m+n)) (\k. NONE)
                 (\k. k=0 /\ m=1 /\ asm_returns_zero_or_one ins /\
                    !t u. LENGTH t.as_stack=hi /\
                      asm_step (SND (compute_label_offsets r)) (build_offset_to_pc r) ins t = AsmOK u ==>
                      EL 0 u.as_stack=0w \/ EL 0 u.as_stack=1w))
    | _ => F) ==>
  !EdgeOK. EdgeOK = (\r pc height tag boolean a b.
    Flow r pc height tag boolean a b /\
    (if EL (pc a) r = AsmOp "JUMP" then Target r (tag a) (pc b)
     else if EL (pc a) r = AsmOp "JUMPI" then pc b = pc a+1 \/ Target r (tag a) (pc b)
     else pc b = pc a+1)) ==>
  !Slots. Slots = (\r cc h need tag boolean.
    (need ==> cc.cc_static) /\ (!k. boolean k ==> k<h /\ tag k=NONE) /\
    (!k l orig. tag k=SOME(l,orig) ==> k<h /\ orig<LENGTH r /\
      (EL orig r=AsmPushLabel l \/ EL orig r=AsmPushOfst l 0) /\
      ?j. C r l j)) ==>
  !Dispatch. Dispatch = (\r cc i h tag (pc:num#num->num) height R.
    !fall. fall = (\v. pc v=i+1) ==>
    !arm. arm = (\P n. ?v. R v /\ P v /\ height v=n) ==>
    !legal. legal = (\P n. !v. R v ==> P v /\ height v=n) ==>
    !next. next = (\n. arm fall n /\ legal fall n) ==>
    !clear. clear = (\n. !k. k<n ==> tag k=NONE) ==>
    !stop. stop = (\n. n<=h /\ clear n /\ !v. ~R v) ==>
    !dst. dst = (\v. Target r tag (pc v)) ==>
    case EL i r of
      AsmLabel l => next h
    | AsmPush bs => next (h+1)
    | AsmPushLabel l => IS_SOME (FLOOKUP (SND (compute_label_offsets r)) l) /\ next (h+1)
    | AsmPushOfst l d => IS_SOME (FLOOKUP (SND (compute_label_offsets r)) l) /\ next (h+1)
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
               if name="JUMP" then 1<=h /\ arm dst (h-1) /\ legal dst (h-1)
               else if name="JUMPI" then 2<=h /\ tag 1=NONE /\
                 arm fall (h-2) /\ arm dst (h-2) /\ legal (\v. fall v \/ dst v) (h-2)
               else ?m. static_abort_straight name m /\ asm_op_arity name<=h /\
                    clear (asm_op_arity name) /\ next (h-asm_op_arity name+m))
    | _ => F) ==>
  !Rows. Rows = (\r cc V X (rank:num#num->num) pc height need tag boolean edge.
    (!v. v IN V ==> Slots r cc (height v) (need v) (tag v) (boolean v)) /\
    (!a b. edge a b ==> a IN V DIFF X /\ b IN V /\ rank b<rank a /\
      Flow r pc height tag boolean a b) /\
    (!v. v IN V DIFF X ==> pc v<LENGTH r /\
      Dispatch r cc (pc v) (height v) (tag v) pc height (edge v))) ==>
  !Open. Open = (\r cc req V X (rank:num#num->num) pc height need tag boolean edge.
    !S. S = Shape r cc req pc height need tag boolean ==>
    FINITE V /\ X SUBSET V /\ (!v. v IN V ==> ?t. S v t) /\
    (!v. v IN V DIFF X ==> pc v<LENGTH r) /\
    (!a b. edge a b ==> a IN V DIFF X /\ b IN V /\ rank b<rank a /\
      EdgeOK r pc height tag boolean a b) /\
    (!v t. v IN V DIFF X /\ S v t ==>
       (?u. (asm_steps (SND (compute_label_offsets r)) (build_offset_to_pc r) r 1 t = AsmRevert u \/
             asm_steps (SND (compute_label_offsets r)) (build_offset_to_pc r) r 1 t = AsmFault u) /\
             u.as_requests=req) \/
       (?w u. edge v w /\ asm_steps (SND (compute_label_offsets r)) (build_offset_to_pc r) r 1 t = AsmOK u /\ S w u))) ==>
  !Reach. Reach = (\(edge:(num#num)->(num#num)->bool) v w.
    ?n (path:num->num#num). path 0=v /\ path n=w /\ !k. k<n ==> edge (path k) (path (SUC k))) ==>
  !Root. Root = (\f tag boolean.
    (!k l orig. tag k=SOME(l,orig) ==> k<LENGTH f.sym_stack /\ EL k f.sym_stack=Lab l 0) /\
    (!k. boolean k ==> k<LENGTH f.sym_stack /\ (EL k f.sym_stack=Val 0w \/ EL k f.sym_stack=Val 1w))) ==>
  !q. q = MAP (rename_push_label x y) p ==>
  !env0. env0 = asm_data_env p0 (assemble p0 ++ data) ==>
  asm_static_wf p0 /\ asm_static_wf p /\ FILTER is_data_inst p = FILTER is_data_inst p0 /\
  s.as_pc=0 /\ s.as_code=assemble p0 ++ data /\
  p = pre ++ [AsmLabel x; next; third] ++ tail /\
  ((next = AsmLabel y /\ y <> x) \/ (next = AsmPushLabel y /\ third = AsmOp "JUMP")) /\
  sym_steps p env0 n (sym_init s) = SymOK f /\
  asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p n
    (s with as_code := assemble p ++ data) = AsmOK cut /\
  asm_sym_rel p (asm_data_env p (assemble p ++ data)) cut f /\
  Open p cc req V {} rank pc height need tag boolean edge /\
  Rows p cc V {} rank pc height need tag boolean edge /\
  e IN V /\ (!v. v IN V ==> Reach edge e v) /\
  Shape p cc req pc height need tag boolean e cut /\ Root f (tag e) (boolean e) /\
  req <<= final_req ==>
  asm_static_wf q /\ FILTER is_data_inst q = FILTER is_data_inst p0 /\
  ?m g t W z N Pc H Nd Tg B R.
    sym_steps q env0 m (sym_init s) = SymOK g /\
    asm_steps (SND (compute_label_offsets q)) (build_offset_to_pc q) q m
      (s with as_code := assemble q ++ data) = AsmOK t /\
    asm_sym_rel q (asm_data_env q (assemble q ++ data)) t g /\
    Open q cc req W {} N Pc H Nd Tg B R /\
    Rows q cc W {} N Pc H Nd Tg B R /\
    z IN W /\ (!v. v IN W ==> Reach R z v) /\
    Shape q cc req Pc H Nd Tg B z t /\ Root g (Tg z) (B z) /\ req <<= final_req
Proof
  bind_names ["canon","tgt","shape","flow","edgeOK","slots","dispatch","rows","open",
            "reach","root","mapped","env_init"] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `asm_static_wf q` by
    (unfold_named ["mapped"] >> irule rename_site_wf >>
     (conj_tac >- first_assum ACCEPT_TAC) >>
     qexistsl [`next`,`pre`,`tail`,`third`] >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `FILTER is_data_inst q = FILTER is_data_inst p0` by
    (unfold_named ["mapped"] >> rewrite_tac[rename_filter_data] >> first_assum ACCEPT_TAC) >>
  (conj_tac >- first_assum ACCEPT_TAC) >> (conj_tac >- first_assum ACCEPT_TAC) >>
  `asm_sym_rel p env0 cut f` by
    (unfold_named ["env_init"] >>
     `asm_data_env p0 (assemble p0 ++ data) = asm_data_env p (assemble p ++ data)` by
       (irule asm_data_env_agree >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
     pop_assum (pure_rewrite_tac o single) >> first_assum ACCEPT_TAC) >>
  suspend "prefix"
QED

Resume merge_rename_covered_cut[prefix]:
  unfold_fact ["root"] `Root f _ _` (map_every assume_tac o CONJUNCTS) >>
  unfold_fact ["shape"] `Shape p cc req pc height need tag boolean e cut`
    (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [GSYM CONJ_ASSOC]) >>
  mp_tac (Q.INST [`w` |-> `e`, `env` |-> `env0`]
    (Q.INST [`e` |-> `f`] (expand_lets rename_protected_endpoint))) >>
  (impl_tac >-
    (unfold_fact ["open","edgeOK","shape","flow","tgt"]
       `Open p cc req V {} rank pc height need tag boolean edge`
       (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [GSYM CONJ_ASSOC]) >>
     pure_rewrite_tac [GSYM CONJ_ASSOC] >>
     rpt (FIRST [first_assum ACCEPT_TAC, conj_tac]))) >>
  named_equations ["mapped"] (pure_rewrite_tac o map GSYM) >>
  disch_then (qx_choose_then `m` (qx_choose_then `w` (qx_choose_then `g`
    (map_every assume_tac o CONJUNCTS)))) >>
  `sym_steps q (asm_data_env p0 (assemble p0 ++ data)) m (sym_init s) = SymOK g` by
    unfold_fact ["env_init"] `sym_steps q env0 m _ = SymOK g` ACCEPT_TAC >>
  drule_all (Q.INST [`p` |-> `p0`, `q` |-> `q`] stopped_symbolic_prefix_actual_code) >>
  disch_then (qx_choose_then `t` (map_every assume_tac o CONJUNCTS)) >>
  qexistsl [`m`,`g`,`t`] >>
  qpat_assum `sym_steps q env0 m _ = SymOK g` (pure_rewrite_tac o single) >>
  qpat_assum `asm_steps _ _ q m _ = AsmOK t` (pure_rewrite_tac o single) >>
  qpat_assum `asm_sym_rel q _ t g` (rewrite_tac o single) >>
  suspend "arms"
QED

Resume merge_rename_covered_cut[arms]:
  `!l j. (C p l j <=> INDEX_OF (AsmLabel l) p = SOME j) /\
         (C q l j <=> INDEX_OF (AsmLabel l) p = SOME j)` by
    (qspecl_then [`p`,`x`,`y`] mp_tac (expand_lets merge_rename_named_layout) >>
     (impl_tac >-
       ((reverse conj_tac >- first_assum ACCEPT_TAC) >>
        qpat_x_assum `next = _ /\ _ \/ _` strip_assume_tac
        >- (disj1_tac >> qexistsl [`pre`,`third`,`tail`] >> simp[]) >>
        disj2_tac >> qexistsl [`pre`,`tail`] >> simp[])) >>
     named_equations ["mapped"] (pure_rewrite_tac o map GSYM) >>
     unfold_named ["canon"] >> simp[]) >>
  qabbrev_tac `ImageRow = \r cc i h (ts:num->(string#num) option) (arms:num->num->bool).
    let fall = \j. j = i+1 in
    let clear = \a. !k. k<a ==> ts k=NONE in
    let dest = \j. ?l orig. ts 0=SOME(l,orig) /\ C r l j in
    case EL i r of
      AsmLabel l => (!j hj. arms j hj <=> fall j /\ hj=h)
    | AsmPush bs => (!j hj. arms j hj <=> fall j /\ hj=h+1)
    | AsmPushLabel l => IS_SOME (FLOOKUP (SND (compute_label_offsets r)) l) /\
        (!j hj. arms j hj <=> fall j /\ hj=h+1)
    | AsmPushOfst l d => IS_SOME (FLOOKUP (SND (compute_label_offsets r)) l) /\
        (!j hj. arms j hj <=> fall j /\ hj=h+1)
    | AsmOp name =>
        (name="INVALID" \/ (name="REVERT" /\ 2<=h /\ clear 2) \/
         (MEM name ["SSTORE";"TSTORE";"LOG0";"LOG1";"LOG2";"LOG3";"LOG4"] /\
          asm_op_arity name<=h /\ clear (asm_op_arity name) /\ cc.cc_static)) /\
        (!j hj. ~arms j hj) \/
        (case ALOOKUP dup_table name of
           SOME n => n<h /\ (!j hj. arms j hj <=> fall j /\ hj=h+1)
         | NONE => case ALOOKUP swap_table name of
             SOME n => 0<n /\ n<h /\ (!j hj. arms j hj <=> fall j /\ hj=h)
           | NONE =>
               if name="JUMP" then 1<=h /\ (?j. dest j) /\
                 (!j hj. arms j hj <=> dest j /\ hj=h-1)
               else if name="JUMPI" then 2<=h /\ ts 1=NONE /\ (?j. dest j) /\
                 (!j hj. arms j hj <=> (fall j \/ dest j) /\ hj=h-2)
               else ?m. static_abort_straight name m /\ asm_op_arity name<=h /\
                 clear (asm_op_arity name) /\
                 (!j hj. arms j hj <=> fall j /\ hj=h-asm_op_arity name+m))
    | _ => F` >>
  `!r ts j. Target r ts j <=> ?l orig. ts 0=SOME(l,orig) /\ C r l j` by
    (unfold_named ["tgt","canon"] >> POP_ASSUM_LIST (K ALL_TAC) >>
     rpt gen_tac >> eq_tac
     >- (disch_then (qx_choose_then `l` (qx_choose_then `o'`
           (qx_choose_then `off` strip_assume_tac))) >>
         qexistsl [`l`,`o'`] >> conj_tac >- first_assum ACCEPT_TAC >>
         qexists `off` >> asm_rewrite_tac[]) >>
     disch_then (qx_choose_then `l` (qx_choose_then `o'`
       (CONJUNCTS_THEN2 assume_tac (qx_choose_then `off` strip_assume_tac)))) >>
     qexistsl [`l`,`o'`,`off`] >> asm_rewrite_tac[]) >>
  `!r cc i h ts (P:num#num->num) (H:num#num->num) S.
      ImageRow r cc i h ts (\j n. ?b. S b /\ P b=j /\ H b=n) <=>
      Dispatch r cc i h ts P H S` by
    (qpat_assum `Abbrev (ImageRow = _)`
       (pure_rewrite_tac o single o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     unfold_named ["dispatch"] >>
     qpat_assum `!r ts j. Target r ts j <=> _` (pure_rewrite_tac o single) >>
     unfold_named ["canon"] >>
     CONV_TAC expand_names >>
     MATCH_ACCEPT_TAC (expand_lets rename_row_dispatch)) >>
  mp_tac (expand_lets (Q.INST [`nr` |-> `rank:num#num->num`]
    (Q.INST [`rank` |-> `\a:num#num. (&(nr a:num):rat)`] merge_rename_decorated_arms))) >>
  rewrite_tac [RAT_OF_NUM_LES] >>
  (impl_tac >-
    (unfold_fact ["canon"] `!l j. (C p l j <=> _) /\ _` assume_tac >>
     unfold_fact ["open","edgeOK","shape","flow","tgt"]
       `Open p cc req V {} rank pc height need tag boolean edge`
       (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [DIFF_EMPTY, GSYM CONJ_ASSOC]) >>
     unfold_fact ["rows","slots","dispatch","canon","tgt","flow"]
       `Rows p cc V {} rank pc height need tag boolean edge`
       (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [DIFF_EMPTY]) >>
     named_equations ["mapped"] (pure_rewrite_tac o map GSYM) >>
     pure_rewrite_tac [GSYM CONJ_ASSOC] >>
     rpt (FIRST [first_assum ACCEPT_TAC, conj_tac])
     >- (qx_gen_tac `v` >> disch_tac >>
          qpat_assum `!a. a IN V ==> ?t. t.as_pc = pc a /\ _`
            (qspec_then `v` (drule_then assume_tac)) >>
          qpat_assum `!a. a IN V ==> (need a ==> _) /\ _`
            (qspec_then `v` (drule_then (map_every assume_tac o CONJUNCTS o PURE_REWRITE_RULE [GSYM CONJ_ASSOC]))) >>
          qpat_assum `!a. a IN V ==> pc a < LENGTH p /\ _`
            (qspec_then `v` (drule_then (map_every assume_tac o CONJUNCTS))) >>
          rpt (FIRST [first_assum ACCEPT_TAC, conj_tac]) >>
          (* E0626: the expanded generic rewrite left the case table;
             explicit six-variable Q.INST failed to parse. *)
          `Dispatch p cc (pc v) (height v) (tag v) pc height (edge v)` by
            (unfold_named ["dispatch","tgt"] >>
             CONV_TAC expand_names >>
             first_assum ACCEPT_TAC) >>
          `ImageRow p cc (pc v) (height v) (tag v)
             (\j n. ?b. edge v b /\ pc b=j /\ height b=n)` by
            (qpat_assum `!r cc i h ts P H S. ImageRow r cc i h ts _ <=> _`
               (pure_rewrite_tac o single) >> first_assum ACCEPT_TAC) >>
          named_equations ["canon"] (fn canon_eq =>
            qpat_assum `Abbrev (ImageRow = _)` (fn row_eq =>
              pop_assum (ACCEPT_TAC o expand_lets o PURE_REWRITE_RULE canon_eq o
                expand_lets o PURE_REWRITE_RULE
                  [REWRITE_RULE [markerTheory.Abbrev_def] row_eq])))) >>
     map_every qx_gen_tac [`v`,`w`] >> disch_tac >>
     unfold_fact ["tgt","canon"] `!r ts j. Target r ts j <=> _` (fn dest_eq =>
       rewrite_tac [GSYM dest_eq, CONJ_ASSOC] >>
       first_assum (qspecl_then [`v`,`w`] (drule_then
         (ACCEPT_TAC o REWRITE_RULE [CONJ_ASSOC])))))) >>
  named_equations ["mapped"] (pure_rewrite_tac o map GSYM) >>
  disch_then (qx_choose_then `rel` (mk_asm "decorated")) >>
  qabbrev_tac `Prod = \i a. i < LENGTH q /\
    (EL i q = AsmPushLabel a \/ EL i q = AsmPushOfst a 0)` >>
  qabbrev_tac `ChoiceOK = \(old:(string#num) option) choice. case old of NONE => choice = NONE
    | SOME (l,o') => ?i a. choice = SOME i /\ Prod i a /\ (a = l \/ l = x /\ a = y)` >>
  qabbrev_tac `Expose = \u. case u of NONE => NONE
    | SOME i => if ?a j. Prod i a /\ C q a j
                then SOME((@a. Prod i a),i) else NONE` >>
  qabbrev_tac `Decor = {u:((num#num)#num option list) | FST u IN V /\
    LENGTH (SND u) = height (FST u) /\
    !k. k < height (FST u) ==> ChoiceOK (tag (FST u) k) (EL k (SND u))}` >>
  qabbrev_tac `Proj = \(u:(num#num)#num option list) k.
    if k < height (FST u) then Expose (EL k (SND u)) else NONE` >>
  `?D. LENGTH D = height w /\
     (!k. k < height w ==> ChoiceOK (tag w k) (EL k D)) /\
     (!k a i. Proj (w,D) k = SOME(a,i) ==>
       k < LENGTH g.sym_stack /\ EL k g.sym_stack = Lab a 0)` by
    (map_every qunabbrev_tac [`Proj`,`Expose`,`ChoiceOK`,`Prod`] >>
     unfold_named ["canon"] >> rewrite_tac [pairTheory.FST, pairTheory.SND] >>
     irule (expand_lets rename_root_choices) >>
     goal_assum (drule_at Any) >> conj_tac
     >- first_assum ACCEPT_TAC
     >> qexistsl [`env0`,`m`,`s`] >> first_assum ACCEPT_TAC) >>
  `(w,D) IN Decor` by simp[Abbr `Decor`] >>
  `FINITE V` by
    unfold_fact ["open"] `Open p cc req V {} rank pc height need tag boolean edge`
      (ACCEPT_TAC o CONJUNCT1) >>
  qspecl_then [`q`,`cc`,`req`] (fn th =>
    qspecl_then [`V`,`\v:num#num. (&(rank v:num):rat)`,`pc`,`height`,`need`,
                 `Proj`,`boolean`,`Decor`,`(w,D)`,`rel`] mp_tac (expand_lets th))
    merge_rename_reachable_lift >>
  (impl_tac >-
    (BETA_TAC >> conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     map_every qunabbrev_tac [`Decor`,`Proj`,`Expose`,`ChoiceOK`,`Prod`] >>
     unfold_named ["canon"] >> BETA_TAC >>
     rewrite_tac [RAT_OF_NUM_LES, CONJ_ASSOC] >>
     asm "decorated" (ACCEPT_TAC o REWRITE_RULE [CONJ_ASSOC]))) >>
  disch_then (qx_choose_then `verts` (qx_choose_then `entry` (qx_choose_then `ranks`
    (qx_choose_then `pos` (qx_choose_then `ht` (qx_choose_then `needed`
      (qx_choose_then `tags` (qx_choose_then `bools` (qx_choose_then `arcs`
        (map_every assume_tac o CONJUNCTS)))))))))) >>
  `?nat_rank. !a b. a IN verts /\ b IN verts /\ rat$rat_les (ranks a) (ranks b) ==>
                    (nat_rank a:num) < nat_rank b` by
    (match_mp_tac (GEN_ALL rename_rank_compress) >> first_assum ACCEPT_TAC) >>
  suspend "package"
QED

Resume merge_rename_covered_cut[package]:
  `!a b. arcs a b ==> a IN verts /\ b IN verts /\ nat_rank b < nat_rank a /\
                      EdgeOK q pos ht tags bools a b` by
    (map_every qx_gen_tac [`a`,`b`] >> disch_tac >>
     qpat_assum `!x y. arcs x y ==> _`
       (qspecl_then [`a`,`b`] (drule_then
         (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac
           (CONJUNCTS_THEN2 assume_tac (mk_asm "lifted_edge")))))) >>
     conj_tac >- first_assum ACCEPT_TAC >> conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- (qpat_assum `!a b. _ ==> nat_rank a < nat_rank b` irule >>
                  rpt conj_tac >> first_assum ACCEPT_TAC) >>
     unfold_named ["edgeOK","flow","tgt"] >>
     CONV_TAC expand_names >>
     unfold_fact ["tgt","canon"] `!r ts j. Target r ts j <=> _` (fn dest_eq =>
       rewrite_tac [dest_eq, CONJ_ASSOC] >>
       asm "lifted_edge" (ACCEPT_TAC o REWRITE_RULE [CONJ_ASSOC]))) >>
  `!v. v IN verts ==> pos v < LENGTH q /\ Slots q cc (ht v) (needed v) (tags v) (bools v) /\
      Dispatch q cc (pos v) (ht v) (tags v) pos ht (arcs v)` by
    (qx_gen_tac `v` >> disch_tac >>
     qpat_assum `!v. v IN verts ==> pos v < LENGTH q /\ _`
       (qspec_then `v` (drule_then (CONJUNCTS_THEN2 assume_tac
         (CONJUNCTS_THEN2 assume_tac assume_tac)))) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- (unfold_named ["slots","canon"] >> first_assum ACCEPT_TAC) >>
     `ImageRow q cc (pos v) (ht v) (tags v)
        (\j n. ?b. arcs v b /\ pos b=j /\ ht b=n)` by
       (qpat_assum `Abbrev (ImageRow = _)`
          (pure_rewrite_tac o single o REWRITE_RULE [markerTheory.Abbrev_def]) >>
        unfold_named ["canon"] >>
        CONV_TAC expand_names >>
        rewrite_tac [CONJ_ASSOC] >>
        first_assum (ACCEPT_TAC o REWRITE_RULE [CONJ_ASSOC])) >>
     qpat_assum `!r cc i h ts P H S. ImageRow r cc i h ts _ <=> _`
       (pure_rewrite_tac o single o GSYM) >> first_assum ACCEPT_TAC) >>
  `Root g (tags entry) (bools entry)` by
    (unfold_named ["root"] >>
     qpat_assum `tags entry = Proj (w,D)` (pure_rewrite_tac o single) >>
     qpat_assum `bools entry = boolean (FST (w,D))`
       (fn th => pure_rewrite_tac [th, pairTheory.FST]) >>
     conj_tac >> first_assum ACCEPT_TAC) >>
  `!v. v IN verts ==> !k l orig. tags v k = SOME(l,orig) ==>
     k < ht v /\ orig < LENGTH q /\
     (EL orig q = AsmPushLabel l \/ EL orig q = AsmPushOfst l 0) /\
     ?off j. FLOOKUP (SND (compute_label_offsets q)) l = SOME off /\
             off < dimword(:256) /\ FLOOKUP (build_offset_to_pc q) off = SOME j` by
    (qx_gen_tac `v` >> disch_tac >>
     qpat_assum `!v. v IN verts ==> pos v < LENGTH q /\ Slots q cc _ _ _ _ /\ _`
       (qspec_then `v` (drule_then (assume_tac o cj 2))) >>
     unfold_fact ["slots","canon"] `Slots q cc _ (needed v) (tags v) _`
       (assume_tac o cj 3) >>
     map_every qx_gen_tac [`k`,`l`,`orig`] >> disch_tac >>
     qpat_assum `!k l orig. tags v k = SOME(l,orig) ==> _`
       (qspecl_then [`k`,`l`,`orig`] (drule_then
         (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac
           (CONJUNCTS_THEN2 assume_tac
             (qx_choose_then `dest` (qx_choose_then `offset` assume_tac))))))) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl [`offset`,`dest`] >> first_assum ACCEPT_TAC) >>
  `Slots q cc (ht entry) (needed entry) (tags entry) (bools entry)` by
    (qpat_assum `!v. v IN verts ==> pos v < LENGTH q /\ Slots q cc _ _ _ _ /\ _`
       (qspec_then `entry` (drule_then (ACCEPT_TAC o cj 2)))) >>
  `Shape q cc req pos ht needed tags bools entry t` by
    (unfold_named ["shape"] >>
     qpat_assum `asm_sym_rel q _ t g`
       (mp_then Any irule (expand_lets rename_actual_root)) >>
     unfold_fact ["root"] `Root g (tags entry) (bools entry)`
       (map_every assume_tac o CONJUNCTS) >>
     unfold_fact ["slots"] `Slots q cc _ (needed entry) (tags entry) _`
       (assume_tac o cj 1) >>
     qpat_assum `!v. v IN verts ==> !k l orig. tags v k = SOME(l,orig) ==> _`
       (qspec_then `entry` (drule_then assume_tac)) >>
     (* E0703: specializing Slots here and using metis timed out. *)
     rpt (FIRST [first_assum ACCEPT_TAC, conj_tac, (simp[pairTheory.FST] >> NO_TAC)])) >>
  qexistsl [`verts`,`entry`,`nat_rank`,`pos`,`ht`,`needed`,`tags`,`bools`,`arcs`] >>
  reverse conj_tac
  >- (conj_tac
      >- (unfold_named ["rows"] >> pure_rewrite_tac [DIFF_EMPTY] >>
          conj_tac >- (gen_tac >> disch_tac >>
            qpat_assum `!v. v IN verts ==> pos v < LENGTH q /\ Slots q cc _ _ _ _ /\ _`
              (drule_then (ACCEPT_TAC o cj 2))) >>
          conj_tac >- (map_every qx_gen_tac [`a`,`b`] >> disch_tac >>
            unfold_fact ["edgeOK"]
              `!a b. arcs a b ==> a IN verts /\ b IN verts /\ _ /\ EdgeOK q pos ht tags bools a b`
              (qspecl_then [`a`,`b`] (drule_then (map_every assume_tac o CONJUNCTS))) >>
            rpt conj_tac >> first_assum ACCEPT_TAC) >>
          gen_tac >> disch_tac >>
          qpat_assum `!v. v IN verts ==> pos v < LENGTH q /\ Slots q cc _ _ _ _ /\ _`
            (drule_then (CONJUNCTS_THEN2 assume_tac (assume_tac o CONJUNCT2))) >>
          conj_tac >> first_assum ACCEPT_TAC) >>
      unfold_named ["reach"] >> rpt (FIRST [first_assum ACCEPT_TAC, conj_tac])) >>
  unfold_named ["open"] >> CONV_TAC expand_names >> pure_rewrite_tac [DIFF_EMPTY] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (unfold_named ["shape"] >> first_assum ACCEPT_TAC) >>
  conj_tac >- (gen_tac >> disch_tac >>
    qpat_assum `!v. v IN verts ==> pos v < LENGTH q /\ Slots q cc _ _ _ _ /\ _`
      (drule_then (ACCEPT_TAC o CONJUNCT1))) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  suspend "step"
QED

Resume merge_rename_covered_cut[step]:
  map_every qx_gen_tac [`v`,`t0`] >> strip_tac >>
  qpat_assum `!v. v IN verts ==> pos v < LENGTH q /\ Slots q cc _ _ _ _ /\ _`
    (qspec_then `v` (drule_then (CONJUNCTS_THEN2 assume_tac
      (mk_asm "step_dispatch" o CONJUNCT2)))) >>
  unfold_fact ["shape"] `Shape q cc req pos ht needed tags bools v t0` assume_tac >>
  unfold_named ["shape"] >>
  match_mp_tac (GEN_ALL (expand_lets pending_role_step)) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac
  >- (qx_gen_tac `w` >> disch_tac >>
      unfold_fact ["edgeOK"]
        `!a b. arcs a b ==> a IN verts /\ b IN verts /\ _ /\ EdgeOK q pos ht tags bools a b`
        (qspecl_then [`v`,`w`] (drule_then (map_every assume_tac o CONJUNCTS))) >>
      conj_tac >- unfold_fact ["flow"] `Flow q pos ht tags bools v w` ACCEPT_TAC >>
      conj_tac
      >- (qpat_assum `!v. v IN verts ==> pos v < LENGTH q /\ Slots q cc _ _ _ _ /\ _`
            (qspec_then `w` (drule_then (assume_tac o cj 2))) >>
          unfold_fact ["slots"] `Slots q cc _ (needed w) (tags w) _`
            (ACCEPT_TAC o cj 1)) >>
      qpat_assum `!v. v IN verts ==> !k l orig. tags v k = SOME(l,orig) ==> _`
        (qspec_then `w` (drule_then mp_tac)) >>
      POP_ASSUM_LIST (K ALL_TAC) >>
      disch_tac >> map_every qx_gen_tac [`k`,`l`,`origin`] >> disch_tac >>
      qpat_x_assum `!k l orig. tags w k = SOME(l,orig) ==> _`
        (qspecl_then [`k`,`l`,`origin`] (drule_then strip_assume_tac)) >>
      metis_tac[]) >>
  asm_x "step_dispatch" (fn th => named_equations ["dispatch","tgt"]
    (fn eqs => mp_tac (expand_lets (PURE_REWRITE_RULE eqs (REWRITE_RULE [markerTheory.label_def] th))))) >>
  POP_ASSUM_LIST (K ALL_TAC) >>
  suspend "positive_dispatch"
QED

Resume merge_rename_covered_cut[positive_dispatch]:
  Cases_on `EL (pos v) q` >> pure_asm_rewrite_tac [asm_inst_case_def] >> BETA_TAC >>
  FIRST [rename1 `AsmOp name` >> suspend "op_dispatch", metis_tac[]]
QED

Resume merge_rename_covered_cut[op_dispatch]:
  Cases_on `name = "INVALID"` >- simp[] >> pure_asm_rewrite_tac [] >>
  Cases_on `name = "REVERT"` >- simp[] >> pure_asm_rewrite_tac [] >>
  Cases_on `MEM name ["SSTORE"; "TSTORE"; "LOG0"; "LOG1"; "LOG2"; "LOG3"; "LOG4"]`
  >- (pure_asm_rewrite_tac [] >> simp[]) >> pure_asm_rewrite_tac [] >>
  reverse (Cases_on `ALOOKUP dup_table name`) >>
  pure_asm_rewrite_tac [option_case_def] >- metis_tac[] >>
  reverse (Cases_on `ALOOKUP swap_table name`) >>
  pure_asm_rewrite_tac [option_case_def] >- metis_tac[] >>
  Cases_on `name = "JUMP"` >- (simp[] >> metis_tac[]) >>
  Cases_on `name = "JUMPI"` >> simp[] >> metis_tac[]
QED

Finalise merge_rename_covered_cut
