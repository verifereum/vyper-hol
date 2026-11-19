Theory staticAbortOptMergeJumpdestsArms
Ancestors
  staticAbortOptMergeJumpdestsOrigin staticAbortOptMergeJumpdestsBypass
  staticAbortStraight asmOptimizer asmSem asmSplice asmSymBridge asmSymSem
  words finite_map pred_set indexedLists rich_list list arithmetic

val arm_names_conv =
  TOP_DEPTH_CONV (Unwind.UNWIND_FORALL_CONV ORELSEC BETA_CONV)

(* Specialize a naming telescope at aliases already in the proof context. *)
fun arm_use_names names =
  map_every (fn s => asm s (fn eq =>
    disch_then (fn th =>
      let val eq = REWRITE_RULE [markerTheory.label_def] eq
      in mp_tac (MP (SPEC (lhs (concl eq)) th) eq) end))) names

(* An inherited demand has precisely the same choice as its input slot.
   Exposure can erase a choice, but never changes the chosen producer. *)
Theorem rename_arm_choose_vector[local]:
  !G (expose:num option -> (string#num) option) tag tag' src fresh fresh' h h' D.
    G NONE NONE /\ expose NONE = NONE /\ LENGTH D = h /\
    (!k. k < h ==> G (tag k) (EL k D)) /\
    (!k. fresh k <> NONE ==> ?i. G (fresh k) i /\
       (expose i <> NONE ==> expose i = fresh' k)) /\
    (!k. tag' k <> NONE ==> k < h' /\
      (fresh k = tag' k \/ ?a. src k = SOME a /\ a < h /\ tag a = tag' k)) ==>
    ?D'. LENGTH D' = h' /\ (!k. k < h' ==> G (tag' k) (EL k D')) /\
      !k. k < h' /\ expose (EL k D') <> NONE ==>
        fresh' k = expose (EL k D') \/
        ?a. src k = SOME a /\ a < h /\ expose (EL a D) = expose (EL k D')
Proof
  rpt gen_tac >> strip_tac >>
  `!k. ?z. G (tag' k) z /\
    (expose z <> NONE ==> fresh' k = expose z \/
      ?a. src k = SOME a /\ a < h /\ expose (EL a D) = expose z)` by
    (gen_tac >> Cases_on `tag' k = NONE`
     >- (qexists `NONE` >> simp[]) >>
     qpat_assum `!k. tag' k <> NONE ==> _` (qspec_then `k` mp_tac) >>
     simp[] >> (metis_tac[])) >>
  pop_assum (qx_choose_then `f` assume_tac o CONV_RULE SKOLEM_CONV) >>
  qexists `GENLIST f h'` >> simp[] >> rpt strip_tac >> gvs[EL_GENLIST] >> metis_tac[]
QED

(* Only a changed taken operand uses the bypass. A fallthrough does not
   become a taken edge merely because its PC agrees with one. *)
Theorem rename_arm_taken_geometry[local]:
  !q. q = MAP (rename_push_label x y) p ==>
  !C. C = (\r l j.
    ?off. FLOOKUP (SND(compute_label_offsets r)) l = SOME off /\
      off < dimword(:256) /\ FLOOKUP (build_offset_to_pc r) off = SOME j) ==>
  asm_static_wf p /\ p = pre ++ [AsmLabel x;next;third] ++ tail /\
  (!l j. (C p l j <=> INDEX_OF (AsmLabel l) p = SOME j) /\
         (C q l j <=> INDEX_OF (AsmLabel l) p = SOME j)) /\
  (!w. w IN (V:(num#num)->bool) /\ pc w = LENGTH pre ==>
    ?z. z IN V /\ (rank z:num) < rank w /\ height z = height w /\ C p y (pc z) /\
        (!k. tag z k <> NONE ==> tag z k = tag w k) /\
        (!k. boolean z k ==> boolean w k)) /\
  w IN V /\ C p l (pc w) /\ (a = l \/ l = x /\ a = y) ==>
  ?z. z IN V /\ rank z <= rank w /\ height z = height w /\ C q a (pc z) /\
      (!k. tag z k <> NONE ==> tag z k = tag w k) /\
      (!k. boolean z k ==> boolean w k)
Proof
  qx_gen_tac `q` >> disch_then (mk_asm "program") >>
  qx_gen_tac `C'` >> disch_then (mk_asm "canonical") >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 (mk_asm "site")
     (CONJUNCTS_THEN2 (mk_asm "layout")
      (CONJUNCTS_THEN2 (mk_asm "bypass")
       (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac assume_tac)))))) >>
  `!l j. C' p l j ==> C' q l j` by (asm "layout" mp_tac >> metis_tac[]) >>
  Cases_on `a = l`
  >- (qexists `w` >> simp[] >> metis_tac[]) >>
  `l = x /\ a = y` by metis_tac[] >>
  `INDEX_OF (AsmLabel x) p = SOME (LENGTH pre)` by
    (`~MEM (AsmLabel x) pre` by
       (irule asm_labels_unique_append_not_mem >>
        qexists `[AsmLabel x;next;third] ++ tail` >>
        asm "site" (fn th => simp[GSYM APPEND_ASSOC, GSYM th]) >>
        fs[asm_static_wf_def]) >>
     asm "site" (fn th => simp[th, INDEX_OF_APPEND, INDEX_OF_CONS])) >>
  `pc w = LENGTH pre` by (asm "layout" mp_tac >> metis_tac[optionTheory.SOME_11]) >>
  asm "bypass" (qspec_then `w` mp_tac) >> simp[] >> strip_tac >>
  qexists `z` >> simp[] >> metis_tac[LESS_IMP_LESS_OR_EQ]
QED

Theorem rename_arm_reference_fetch[local]:
  !q. q = MAP (rename_push_label x y) p ==>
  p = pre ++ [AsmLabel x;next;third] ++ tail /\
  ((next = AsmLabel y /\ y <> x) \/
   (next = AsmPushLabel y /\ third = AsmOp "JUMP")) /\
  asm_static_wf p /\ i < LENGTH p ==>
  (!l. (EL i q = AsmPushLabel l \/ (?d. EL i q = AsmPushOfst l d)) ==>
       ?off. FLOOKUP (SND(compute_label_offsets q)) l = SOME off)
Proof
  CONV_TAC Unwind.UNWIND_FORALL_CONV >>
  disch_then (CONJUNCTS_THEN2 (mk_asm "site")
    (CONJUNCTS_THEN2 (mk_asm "guard") STRIP_ASSUME_TAC)) >>
  `!s. EL i p = AsmPushLabel s \/ (?d. EL i p = AsmPushOfst s d) ==>
     ?off. FLOOKUP (SND(compute_label_offsets (MAP (rename_push_label x y) p)))
       (if EL i p = AsmPushLabel x then y else s) = SOME off` by
    (rpt gen_tac >> disch_tac >>
     qspecl_then [`p`,`pre`,`x`,`y`,`next`,`third`,`tail`,`i`,`s`] mp_tac
       merge_rename_reference_step >> CONV_TAC arm_names_conv >>
     impl_tac >- (asm "site" assume_tac >> asm "guard" assume_tac >> metis_tac[]) >>
     metis_tac[]) >>
  `EL i (MAP (rename_push_label x y) p) = rename_push_label x y (EL i p)` by simp[EL_MAP] >>
  pop_assum SUBST1_TAC >> Cases_on `EL i p` >> simp[rename_push_label_def] >>
  Cases_on `s = x` >> fs[] >> metis_tac[]
QED

(* Literal pushes and non-branch operations do not depend on the maps.
   In the branch cases Flow's zero output count forbids a fresh Boolean. *)
Theorem rename_arm_boolean_maps[local]:
  asm_step lo b (AsmPush bs) s = asm_step lo' b' (AsmPush bs) s /\
  (name <> "JUMP" /\ name <> "JUMPI" ==>
   asm_step lo b (AsmOp name) s = asm_step lo' b' (AsmOp name) s)
Proof
  simp[asm_step_def, asm_step_op_def, asm_step_control_def]
QED

Theorem rename_arm_inherit[local]:
  J = (\h h' (tag:num->(string#num)option) tag' b b'
         (src:num->num option) (fresh:num->(string#num)option) bnew.
     (!k l o'. tag' k = SOME(l,o') ==>
         k < h' /\ (fresh k = SOME(l,o') \/
            ?a. src k = SOME a /\ a < h /\ tag a = SOME(l,o'))) /\
     (!k. b' k ==> k < h' /\ (bnew k \/ ?a. src k = SOME a /\ a < h /\ b a))) /\
  P = (\h (D:num option list) k. if k<h then E (EL k D) else NONE) /\
  G NONE NONE /\ E NONE = NONE /\ LENGTH D = h /\
  (!k. k < h ==> G (tag k) (EL k D)) /\
  (!k. tagz k <> NONE ==> tagz k = tagw k) /\
  (!k. bz k ==> bw k) /\ J h h' tag tagw b bw src fresh bnew /\
  (!k. fresh k <> NONE ==> ?i. G (fresh k) i /\ (E i <> NONE ==> E i = fresh' k)) /\
  (!k. bnew k ==> bnew' k) ==>
  ?Dz. LENGTH Dz = h' /\ (!k. k < h' ==> G (tagz k) (EL k Dz)) /\
       J h h' (P h D) (P h' Dz) b bz src fresh' bnew'
Proof
  disch_then (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac mp_tac)) >>
  simp[] >> strip_tac >>
  `!k. tagz k <> NONE ==> k < h' /\
     (fresh k = tagz k \/ ?a. src k = SOME a /\ a < h /\ tag a = tagz k)` by
     (gen_tac >> Cases_on `tagz k` >> simp[] >>
      PairCases_on `x` >>
      qpat_assum `!k. tagz k <> NONE ==> _` (qspec_then `k` mp_tac) >>
      simp[] >> disch_then (assume_tac o SYM) >>
      qpat_assum `!k l o'. tagw k = SOME(l,o') ==> _`
        (qspecl_then [`k`,`x0`,`x1`] mp_tac) >> simp[]) >>
  `?Dz. LENGTH Dz = h' /\ (!k. k < h' ==> G (tagz k) (EL k Dz)) /\
       !k. k < h' /\ E (EL k Dz) <> NONE ==>
          fresh' k = E (EL k Dz) \/
          ?a. src k = SOME a /\ a < h /\ E (EL a D) = E (EL k Dz)` by
    ((irule rename_arm_choose_vector >> simp[] >> map_every qexists [`fresh`,`tag`] >> simp[] >> (gvs[rename_arm_choose_vector]))) >>
  qexists `Dz` >> simp[] >>
  conj_tac >- (rpt gen_tac >> Cases_on `k < h'` >> simp[] >> metis_tac[optionTheory.NOT_NONE_SOME]) >>
  metis_tac[]
QED

(* Transfer along one instruction, possibly restricting its output demands
   to those of the endpoint of a covered bypass. *)
Theorem rename_arm_flow[local]:
  !I. I = (\hi hj (tag:num->(string#num)option) tag' b b'
      (src:num->num option) (fresh:num->(string#num)option) bnew.
      (!k l o'. tag' k = SOME(l,o') ==>
         k < hj /\ (fresh k = SOME(l,o') \/
            ?a. src k = SOME a /\ a < hi /\ tag a = SOME(l,o'))) /\
      (!k. b' k ==> k < hj /\ (bnew k \/ ?a. src k = SOME a /\ a < hi /\ b a))) ==>
  !Flow. Flow = (\r i ins hi hj (tag:num->(string#num)option) tag' b b'.
    !inherit. inherit = I hi hj tag tag' b b' ==>
    case ins of
      AsmLabel l => hj = hi /\ inherit (\k. SOME k) (\k. NONE) (\k. F)
    | AsmPush bs => hj = hi+1 /\ inherit (\k. if k=0 then NONE else SOME(k-1))
        (\k. NONE) (\k. k=0 /\ !t u.
          asm_step (SND(compute_label_offsets r)) (build_offset_to_pc r)
            (AsmPush bs) t = AsmOK u ==> (EL 0 u.as_stack=0w \/ EL 0 u.as_stack=1w))
    | AsmPushLabel l => hj = hi+1 /\ inherit (\k. if k=0 then NONE else SOME(k-1))
        (\k. if k=0 then SOME(l,i) else NONE) (\k. F)
    | AsmPushOfst l d => hj = hi+1 /\ inherit (\k. if k=0 then NONE else SOME(k-1))
        (\k. if k=0 /\ d=0 then SOME(l,i) else NONE) (\k. F)
    | AsmOp name =>
        (case ALOOKUP dup_table name of
           SOME n => n < hi /\ hj = hi+1 /\
             inherit (\k. SOME(if k=0 then n else k-1)) (\k. NONE) (\k. F)
         | NONE => case ALOOKUP swap_table name of
             SOME n => 0<n /\ n<hi /\ hj=hi /\
               inherit (\k. SOME(if k=0 then n else if k=n then 0 else k)) (\k. NONE) (\k. F)
           | NONE =>
               !a. a = asm_op_arity name ==>
               !m. m = hj + a - hi ==>
               a <= hi /\ hj = m+(hi-a) /\ ((name="JUMP" \/ name="JUMPI") ==> m=0) /\
               inherit (\k. if k<m then NONE else SOME(k-m+a)) (\k. NONE)
                 (\k. k=0 /\ m=1 /\ asm_returns_zero_or_one ins /\
                   !t u. LENGTH t.as_stack=hi /\
                     asm_step (SND(compute_label_offsets r)) (build_offset_to_pc r)
                       ins t = AsmOK u ==> (EL 0 u.as_stack=0w \/ EL 0 u.as_stack=1w)))
    | _ => F) ==>
  !P. P = (\h (D:num option list) k. if k<h then E (EL k D) else NONE) ==>
  G NONE NONE /\ E NONE = NONE /\ LENGTH D = hi /\
  (!k. k < hi ==> G (tag k) (EL k D)) /\
  (!l. ins = AsmPushLabel l ==>
      G (SOME(l,i)) (SOME i) /\
      (E (SOME i) = NONE \/ E (SOME i) = SOME(if l=x then y else l,i))) /\
  (!l. ins = AsmPushOfst l 0 ==>
      G (SOME(l,i)) (SOME i) /\ (E (SOME i) = NONE \/ E (SOME i) = SOME(l,i))) /\
  (!k. tagz k <> NONE ==> tagz k = tagw k) /\ (!k. bz k ==> bw k) /\
  Flow p i ins hi hj tag tagw b bw ==>
  ?Dz. LENGTH Dz = hj /\ (!k. k < hj ==> G (tagz k) (EL k Dz)) /\
       Flow q i (rename_push_label x y ins) hi hj (P hi D) (P hj Dz) b bz
Proof
  qx_gen_tac `I'` >> disch_then (mk_asm "inherit") >>
  gen_tac >> disch_then (mk_asm "flow" o CONV_RULE arm_names_conv) >>
  gen_tac >> disch_then (mk_asm "project") >>
  strip_tac >>
  `!src f f' bn bn'.
     I' hi hj tag tagw b bw src f bn /\
     (!k. f k <> NONE ==> ?u. G (f k) u /\ (E u <> NONE ==> E u = f' k)) /\
     (!k. bn k ==> bn' k) ==>
     ?Dz. LENGTH Dz = hj /\ (!k. k < hj ==> G (tagz k) (EL k Dz)) /\
          I' hi hj (P hi D) (P hj Dz) b bz src f' bn'` by
    (rpt gen_tac >> strip_tac >>
     asm "inherit" assume_tac >> asm "project" assume_tac >>
     drule_all_then ACCEPT_TAC rename_arm_inherit) >>
  pop_assum (mk_asm "transfer") >>
  namedCases_on `ins` ["name","bs","l","l d","l","l","bs","l"]
  >- (Cases_on `ALOOKUP dup_table name` >>
      (Cases_on `ALOOKUP swap_table name` >>
      asm "flow" (fn f =>
        qpat_assum `ALOOKUP dup_table name = _` (fn dt =>
        qpat_assum `ALOOKUP swap_table name = _` (fn st =>
        qpat_x_assum `Flow p i (AsmOp name) hi hj tag tagw b bw`
          (STRIP_ASSUME_TAC o SIMP_RULE bool_ss
            [f,LET_THM,asmIRTheory.asm_inst_case_def,optionTheory.option_case_def,dt,st])))))
      >- (asm "transfer" (fn th =>
             qpat_assum `I' hi hj tag tagw b bw _ _ _`
               (mp_then Any (qspecl_then [`\k. NONE`,
                 `\k. k = 0 /\ hj + asm_op_arity name - hi = 1 /\
                      asm_returns_zero_or_one (AsmOp name) /\
                      !t u. LENGTH t.as_stack = hi /\
                        asm_step (SND (compute_label_offsets q)) (build_offset_to_pc q)
                          (AsmOp name) t = AsmOK u ==>
                        (EL 0 u.as_stack = 0w \/ EL 0 u.as_stack = 1w)`]
                 (mp_tac o BETA_RULE)) th)) >>
           (impl_tac >-
             (SIMP_TAC bool_ss [] >> strip_tac >>
              `name <> "JUMP" /\ name <> "JUMPI"` by
                (qpat_assum `_ \/ _ ==> hj + asm_op_arity name - hi = 0` mp_tac >> simp[]) >>
              rpt gen_tac >> disch_tac >>
              `asm_step (SND (compute_label_offsets p)) (build_offset_to_pc p)
                 (AsmOp name) t =
               asm_step (SND (compute_label_offsets q)) (build_offset_to_pc q)
                 (AsmOp name) t` by
                (irule (CONJUNCT2 rename_arm_boolean_maps) >> simp[]) >>
              qpat_assum `!t u. LENGTH t.as_stack = hi /\ _ ==> _`
                (qspecl_then [`t`,`u`] mp_tac) >> simp[]) >>
            disch_then (qx_choose_then `Dz` STRIP_ASSUME_TAC) >> qexists `Dz` >>
            asm "flow" (fn f =>
              qpat_assum `ALOOKUP dup_table name = NONE` (fn dt =>
              qpat_assum `ALOOKUP swap_table name = NONE` (fn st =>
                SIMP_TAC bool_ss [f,LET_THM,asmIRTheory.asm_inst_case_def,
                  optionTheory.option_case_def,rename_push_label_def,dt,st]))) >>
            rpt conj_tac >> first_assum ACCEPT_TAC)) >>
      asm "transfer" (fn th =>
        qpat_assum `I' hi hj tag tagw b bw _ _ _`
          (mp_then Any (qspecl_then [`\k. NONE`,`\k. F`] (mp_tac o BETA_RULE)) th)) >>
      (impl_tac >- SIMP_TAC bool_ss []) >>
      disch_then (qx_choose_then `Dz` STRIP_ASSUME_TAC) >> qexists `Dz` >>
      asm "flow" (fn f =>
        qpat_assum `ALOOKUP dup_table name = _` (fn dt =>
        qpat_assum `ALOOKUP swap_table name = _` (fn st =>
          SIMP_TAC bool_ss [f,LET_THM,asmIRTheory.asm_inst_case_def,
            optionTheory.option_case_def,rename_push_label_def,dt,st]))) >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  (asm "flow" (fn f =>
    qpat_x_assum `Flow p i _ hi hj tag tagw b bw`
      (STRIP_ASSUME_TAC o SIMP_RULE bool_ss [f,LET_THM,asmIRTheory.asm_inst_case_def])))
  >- (asm "transfer" (fn th =>
        qpat_assum `I' hi hj tag tagw b bw _ _ _`
          (mp_then Any (qspecl_then [`\k. NONE`,
            `\k. k = 0 /\ !t u.
                 asm_step (SND (compute_label_offsets q)) (build_offset_to_pc q)
                   (AsmPush bs) t = AsmOK u ==> (EL 0 u.as_stack=0w \/ EL 0 u.as_stack=1w)`]
            (mp_tac o BETA_RULE)) th)) >>
      (impl_tac >- (SIMP_TAC bool_ss [] >> metis_tac[CONJUNCT1 rename_arm_boolean_maps])) >>
      disch_then (qx_choose_then `Dz` STRIP_ASSUME_TAC) >> qexists `Dz` >>
      asm "flow" (fn f => SIMP_TAC bool_ss
        [f,LET_THM,asmIRTheory.asm_inst_case_def,rename_push_label_def]) >>
      rpt conj_tac >> first_assum ACCEPT_TAC)
  >- (`rename_push_label x y (AsmPushLabel l) =
        AsmPushLabel (if l = x then y else l)` by
        (Cases_on `l = x` >> simp[rename_push_label_def]) >>
      pop_assum SUBST1_TAC >>
      asm "transfer" (fn th =>
        qpat_assum `I' hi hj tag tagw b bw _ _ _`
          (mp_then Any (qspecl_then [`\k. if k = 0 then SOME (if l = x then y else l,i) else NONE`,
              `\k. F`] (mp_tac o BETA_RULE)) th)) >>
      (impl_tac >-
        (rpt strip_tac >> Cases_on `k = 0` >> fs[] >> qexists `SOME i` >> simp[] >> metis_tac[])) >>
      disch_then (qx_choose_then `Dz` STRIP_ASSUME_TAC) >> qexists `Dz` >>
      asm "flow" (fn f => SIMP_TAC bool_ss [f,LET_THM,asmIRTheory.asm_inst_case_def]) >>
      rpt conj_tac >> first_assum ACCEPT_TAC)
  >- (asm "transfer" (fn th =>
        qpat_assum `I' hi hj tag tagw b bw _ _ _`
          (mp_then Any (qspecl_then [`\k. if k = 0 /\ d = 0 then SOME (l,i) else NONE`,
              `\k. F`] (mp_tac o BETA_RULE)) th)) >>
      (impl_tac >-
        (Cases_on `d = 0` >> simp[] >> rpt strip_tac >> Cases_on `k = 0` >> fs[] >>
         qexists `SOME i` >> simp[] >> metis_tac[])) >>
      disch_then (qx_choose_then `Dz` STRIP_ASSUME_TAC) >> qexists `Dz` >>
      asm "flow" (fn f => SIMP_TAC bool_ss
        [f,LET_THM,asmIRTheory.asm_inst_case_def,rename_push_label_def]) >>
      rpt conj_tac >> first_assum ACCEPT_TAC) >>
  asm "transfer" (fn th =>
    qpat_assum `I' hi hj tag tagw b bw _ _ _`
      (mp_then Any (qspecl_then [`\k. NONE`,`\k. F`] (mp_tac o BETA_RULE)) th)) >>
  (impl_tac >- SIMP_TAC bool_ss []) >>
  disch_then (qx_choose_then `Dz` STRIP_ASSUME_TAC) >> qexists `Dz` >>
  asm "flow" (fn f => SIMP_TAC bool_ss
    [f,LET_THM,asmIRTheory.asm_inst_case_def,rename_push_label_def]) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

(* A decoration stores an occurrence even when its word is not a code
   address. Only the projected tag asks for a code destination. *)
Theorem rename_arm_choices[local]:
  !q. q = MAP (rename_push_label x y) p ==>
  !C. C = (\r l j. ?off. FLOOKUP (SND (compute_label_offsets r)) l = SOME off /\
     off < dimword(:256) /\ FLOOKUP (build_offset_to_pc r) off = SOME j) ==>
  !Prod. Prod = (\i a. i < LENGTH q /\
      (EL i q = AsmPushLabel a \/ EL i q = AsmPushOfst a 0)) ==>
  !G. G = (\old choice. case old of NONE => choice = NONE
    | SOME (l,o') => ?i a. choice = SOME i /\ Prod i a /\ (a = l \/ l = x /\ a = y)) ==>
  !E. E = (\u. case u of NONE => NONE
    | SOME i => if ?a j. Prod i a /\ C q a j
                then SOME((@a. Prod i a),i) else NONE) ==>
  G NONE NONE /\ E NONE = NONE /\
  (!u. G NONE u ==> u = NONE) /\
  (!old i. G old (SOME i) ==> i < LENGTH q) /\
  (!u a i. E u = SOME(a,i) ==> Prod i a /\ ?j. C q a j) /\
  (!l o' u. G (SOME(l,o')) u ==>
     ?i a. u = SOME i /\ Prod i a /\ (a = l \/ l = x /\ a = y) /\
           (!j. C q a j ==> E u = SOME(a,i))) /\
  (!i l. i < LENGTH p /\ EL i p = AsmPushLabel l ==>
     G (SOME(l,i)) (SOME i) /\
     (E (SOME i) = NONE \/ E (SOME i) = SOME(if l=x then y else l,i))) /\
  (!i l. i < LENGTH p /\ EL i p = AsmPushOfst l 0 ==>
     G (SOME(l,i)) (SOME i) /\ (E (SOME i) = NONE \/ E (SOME i) = SOME(l,i)))
Proof
  qx_gen_tac `q` >> disch_then (mk_asm "program") >>
  qx_gen_tac `C'` >> disch_then (mk_asm "canonical") >>
  map_every (fn s => gen_tac >> disch_then (mk_asm s))
    ["prod", "choose", "expose"] >>
  `!i a b. Prod i a /\ Prod i b ==> a = b` by
    (simp[markerLib.L "prod"] >> metis_tac[asmIRTheory.asm_inst_11,asmIRTheory.asm_inst_distinct]) >>
  `!i a. Prod i a ==> (@b. Prod i b) = a` by
    (rpt strip_tac >> SELECT_ELIM_TAC >> metis_tac[]) >>
  `!i a. Prod i a ==>
     ((E (SOME i) = SOME(a,i) <=> ?j. C' q a j) /\
      (E (SOME i) = NONE \/ E (SOME i) = SOME(a,i)))` by
    (rpt gen_tac >> strip_tac >> simp[markerLib.L "expose"] >>
     Cases_on `?a j. Prod i a /\ C' q a j` >> simp[] >> metis_tac[]) >>
  `E NONE = NONE` by simp[markerLib.L "expose"] >>
  `!u a i. E u = SOME(a,i) ==> Prod i a /\ ?j. C' q a j` by
    (rpt gen_tac >> Cases_on `u` >> simp[] >> rename1 `E (SOME n)` >>
     Cases_on `?b j. Prod n b /\ C' q b j` >>
     simp[markerLib.L "expose"] >> metis_tac[]) >>
  `!i a. Prod i a ==> i < LENGTH q` by simp[markerLib.L "prod"] >>
  `!old i. G old (SOME i) ==> i < LENGTH q` by
    (Cases_on `old` >> simp[markerLib.L "choose"] >> PairCases_on `x'` >>
     simp[markerLib.L "choose", PULL_EXISTS] >> metis_tac[]) >>
  `!l o' u. G (SOME(l,o')) u ==>
     ?i a. u = SOME i /\ Prod i a /\ (a = l \/ l = x /\ a = y) /\
           (!j. C' q a j ==> E u = SOME(a,i))` by
    (simp[markerLib.L "choose", PULL_EXISTS] >> rpt strip_tac >> metis_tac[]) >>
  `!i. i < LENGTH p ==> i < LENGTH q /\
      EL i q = rename_push_label x y (EL i p)` by simp[markerLib.L "program", EL_MAP] >>
  rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
  TRY (simp[markerLib.L "choose"] >> NO_TAC)
  >- (rpt strip_tac >>
      `Prod i (if l=x then y else l)` by
        (simp[markerLib.L "prod"] >> Cases_on `l = x` >> simp[rename_push_label_def]) >>
      simp[markerLib.L "choose", PULL_EXISTS] >>
      qexists `if l=x then y else l` >> Cases_on `l=x` >> simp[])
  >- (rpt strip_tac >>
      `Prod i l` by simp[markerLib.L "prod", rename_push_label_def] >>
      simp[markerLib.L "choose", PULL_EXISTS] >> metis_tac[])
QED

Theorem merge_rename_decorated_arms:
  !q. q = MAP (rename_push_label x y) p ==>
  !C. C = (\r l j. ?off. FLOOKUP (SND (compute_label_offsets r)) l = SOME off /\
     off < dimword(:256) /\ FLOOKUP (build_offset_to_pc r) off = SOME j) ==>
  !Prod. Prod = (\i a. i < LENGTH q /\
      (EL i q = AsmPushLabel a \/ EL i q = AsmPushOfst a 0)) ==>
  !G. G = (\old choice. case old of NONE => choice = NONE
    | SOME (l,o') => ?i a. choice = SOME i /\ Prod i a /\ (a = l \/ l = x /\ a = y)) ==>
  !E. E = (\u. case u of NONE => NONE
    | SOME i => if ?a j. Prod i a /\ C q a j
                then SOME((@a. Prod i a),i) else NONE) ==>
  !A. A = {u:((num#num)#num option list) | FST u IN V /\
     LENGTH (SND u) = height (FST u) /\
     !k. k < height (FST u) ==> G (tag (FST u) k) (EL k (SND u))} ==>
  !proj. proj = (\u k. if k < height (FST u) then E (EL k (SND u)) else NONE) ==>
  !Target. Target = (\r tag j. ?l o'. tag 0 = SOME(l,o') /\ C r l j) ==>
  !Slots. Slots = (\r h need tag boolean.
    (need ==> cc.cc_static) /\
    (!k. boolean k ==> k < h /\ tag k = NONE) /\
    (!k l orig. tag k = SOME(l,orig) ==>
      k < h /\ orig < LENGTH r /\
      (EL orig r = AsmPushLabel l \/ EL orig r = AsmPushOfst l 0) /\
      ?j. C r l j)) ==>
  !Row. Row = (\r i h tag (arms:num->num->bool).
    !fall. fall = (\j. j = i+1) ==>
    !clear. clear = (\a. !k. k < a ==> tag k = NONE) ==>
    case EL i r of
      AsmLabel l => (!j hj. arms j hj <=> fall j /\ hj = h)
    | AsmPush bs => (!j hj. arms j hj <=> fall j /\ hj = h+1)
    | AsmPushLabel l =>
        IS_SOME (FLOOKUP (SND (compute_label_offsets r)) l) /\
        (!j hj. arms j hj <=> fall j /\ hj = h+1)
    | AsmPushOfst l d =>
        IS_SOME (FLOOKUP (SND (compute_label_offsets r)) l) /\
        (!j hj. arms j hj <=> fall j /\ hj = h+1)
    | AsmOp name =>
        (name = "INVALID" \/ (name = "REVERT" /\ 2 <= h /\ clear 2) \/
         (MEM name ["SSTORE"; "TSTORE"; "LOG0"; "LOG1"; "LOG2"; "LOG3"; "LOG4"] /\
          asm_op_arity name <= h /\ clear (asm_op_arity name) /\ cc.cc_static)) /\
        (!j hj. ~arms j hj) \/
        (case ALOOKUP dup_table name of
           SOME n => n < h /\ (!j hj. arms j hj <=> fall j /\ hj = h+1)
         | NONE => case ALOOKUP swap_table name of
             SOME n => 0 < n /\ n < h /\ (!j hj. arms j hj <=> fall j /\ hj = h)
           | NONE =>
               if name = "JUMP" then
                 1 <= h /\ (?j. Target r tag j) /\
                 (!j hj. arms j hj <=> Target r tag j /\ hj = h-1)
               else if name = "JUMPI" then
                 2 <= h /\ tag 1 = NONE /\ (?j. Target r tag j) /\
                 (!j hj. arms j hj <=> (fall j \/ Target r tag j) /\ hj = h-2)
               else
                 ?m. static_abort_straight name m /\ asm_op_arity name <= h /\
                   clear (asm_op_arity name) /\
                   (!j hj. arms j hj <=> fall j /\ hj = h-asm_op_arity name+m))
    | _ => F) ==>
  !Flow. Flow = (\r i ins hi hj tx ty bx by'.
    !inherit. inherit = (\(src:num -> num option)
                  (fresh:num -> (string#num) option) (bnew:num -> bool).
      (!k l orig. ty k = SOME(l,orig) ==>
         k < hj /\ (fresh k = SOME(l,orig) \/
         ?a. src k = SOME a /\ a < hi /\ tx a = SOME(l,orig))) /\
      (!k. by' k ==> k < hj /\
         (bnew k \/ ?a. src k = SOME a /\ a < hi /\ bx a))) ==>
    case ins of
      AsmLabel l => hj = hi /\ inherit (\k. SOME k) (\k. NONE) (\k. F)
    | AsmPush bs =>
        hj = hi+1 /\
        inherit (\k. if k=0 then NONE else SOME(k-1)) (\k. NONE)
          (\k. k=0 /\ !t u.
            asm_step (SND (compute_label_offsets r)) (build_offset_to_pc r)
              (AsmPush bs) t = AsmOK u ==>
            (EL 0 u.as_stack=0w \/ EL 0 u.as_stack=1w))
    | AsmPushLabel l =>
        hj = hi+1 /\ inherit (\k. if k=0 then NONE else SOME(k-1))
          (\k. if k=0 then SOME(l,i) else NONE) (\k. F)
    | AsmPushOfst l d =>
        hj = hi+1 /\ inherit (\k. if k=0 then NONE else SOME(k-1))
          (\k. if k=0 /\ d=0 then SOME(l,i) else NONE) (\k. F)
    | AsmOp name =>
        (case ALOOKUP dup_table name of
           SOME n => n < hi /\ hj = hi+1 /\
             inherit (\k. SOME(if k=0 then n else k-1)) (\k. NONE) (\k. F)
         | NONE => case ALOOKUP swap_table name of
             SOME n => 0 < n /\ n < hi /\ hj = hi /\
               inherit (\k. SOME(if k=0 then n else if k=n then 0 else k)) (\k. NONE) (\k. F)
           | NONE =>
               !a. a = asm_op_arity name ==>
               !m. m = hj + a - hi ==>
               a <= hi /\ hj = m+(hi-a) /\
               ((name="JUMP" \/ name="JUMPI") ==> m=0) /\
               inherit (\k. if k<m then NONE else SOME(k-m+a)) (\k. NONE)
                 (\k. k=0 /\ m=1 /\ asm_returns_zero_or_one ins /\
                   !t u. LENGTH t.as_stack = hi /\
                     asm_step (SND (compute_label_offsets r)) (build_offset_to_pc r)
                       ins t = AsmOK u ==>
                     (EL 0 u.as_stack=0w \/ EL 0 u.as_stack=1w)))
    | _ => F) ==>
  !Control. Control = (\r i j tag.
    if EL i r = AsmOp "JUMP" then Target r tag j
    else if EL i r = AsmOp "JUMPI" then j = i+1 \/ Target r tag j
    else j = i+1) ==>
  !Shape. Shape = (\v (t:asm_state).
    t.as_pc = pc v /\ LENGTH t.as_stack = height v /\ t.as_call_ctx = cc /\
    t.as_requests = req /\ (need v ==> t.as_call_ctx.cc_static) /\
    (!k l orig. tag v k = SOME(l,orig) ==>
      k < height v /\ orig < LENGTH p /\
      (EL orig p = AsmPushLabel l \/ (?d. EL orig p = AsmPushOfst l d) \/
       EL orig p = AsmDataLabel l) /\
      ?off j. FLOOKUP (SND (compute_label_offsets p)) l = SOME off /\
              off < dimword(:256) /\ FLOOKUP (build_offset_to_pc p) off = SOME j /\
              EL k t.as_stack = (n2w off:bytes32)) /\
    (!k. boolean v k ==> k < height v /\ (EL k t.as_stack = 0w \/ EL k t.as_stack = 1w))) ==>
  asm_static_wf p /\ p = pre ++ [AsmLabel x;next;third] ++ tail /\
  ((next = AsmLabel y /\ y <> x) \/ (next = AsmPushLabel y /\ third = AsmOp "JUMP")) /\
  (!l j. (C p l j <=> INDEX_OF (AsmLabel l) p = SOME j) /\
         (C q l j <=> INDEX_OF (AsmLabel l) p = SOME j)) /\
  FINITE V /\
  (!v. v IN V ==> pc v < LENGTH p /\ (?t. Shape v t) /\
      Slots p (height v) (need v) (tag v) (boolean v) /\
      Row p (pc v) (height v) (tag v)
        (\j hj. ?w. edge v w /\ pc w = j /\ height w = hj)) /\
  (!v w. edge v w ==> v IN V /\ w IN V /\ rank w < rank v /\
      Flow p (pc v) (EL (pc v) p) (height v) (height w) (tag v) (tag w)
        (boolean v) (boolean w) /\ Control p (pc v) (pc w) (tag v)) /\
  (!v t. v IN V /\ Shape v t ==>
      (?u. (asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p 1 t = AsmRevert u \/
            asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p 1 t = AsmFault u) /\
           u.as_requests = req) \/
      (?w u. edge v w /\
         asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p 1 t = AsmOK u /\
         Shape w u)) ==>
  ?R.
    (!u. u IN A ==> FST u IN V /\ LENGTH (SND u) = height (FST u) /\
      !i. MEM (SOME i) (SND u) ==> i < LENGTH q) /\
    (!u. u IN A ==> pc (FST u) < LENGTH q /\
      Slots q (height (FST u)) (need (FST u)) (proj u) (boolean (FST u)) /\
      Row q (pc (FST u)) (height (FST u)) (proj u)
        (\j hj. ?v. v IN A /\ R u v /\ pc (FST v) = j /\ height (FST v) = hj)) /\
    (!u v. u IN A /\ v IN A /\ R u v ==>
      rank (FST v) < rank (FST u) /\
      Flow q (pc (FST u)) (EL (pc (FST u)) q) (height (FST u)) (height (FST v))
        (proj u) (proj v) (boolean (FST u)) (boolean (FST v)) /\
      Control q (pc (FST u)) (pc (FST v)) (proj u))
Proof
  qx_gen_tac `q` >> disch_then (mk_asm "program") >>
  qx_gen_tac `C'` >> disch_then (mk_asm "canonical") >>
  map_every (fn s => gen_tac >> disch_then (mk_asm s))
    ["prod", "choose", "expose", "admissible", "project", "target", "slots"] >>
  map_every (fn s => gen_tac >> disch_then (mk_asm s o CONV_RULE arm_names_conv))
    ["row", "flow"] >>
  map_every (fn s => gen_tac >> disch_then (mk_asm s)) ["control", "shape"] >>
  qabbrev_tac `Arms = \v (j:num) (hj:num). ?w. edge v w /\ pc w = j /\ height w = hj` >>
  disch_then (CONJUNCTS_THEN2 (mk_asm "wf")
    (CONJUNCTS_THEN2 (mk_asm "site")
    (CONJUNCTS_THEN2 (mk_asm "guard")
    (CONJUNCTS_THEN2 (mk_asm "layout")
    (CONJUNCTS_THEN2 (mk_asm "finite")
    (CONJUNCTS_THEN2 (mk_asm "vertices")
    (CONJUNCTS_THEN2 (mk_asm "edges") (mk_asm "progress")))))))) >>
  mp_tac rename_arm_choices >>
  arm_use_names ["program", "canonical", "prod", "choose", "expose"] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!u. u IN A <=> FST u IN V /\ LENGTH (SND u) = height (FST u) /\
    !k. k < height (FST u) ==> G (tag (FST u) k) (EL k (SND u))` by
    simp[markerLib.L "admissible"] >>
  pop_assum (mk_asm "membership") >>
  `!u. u IN A ==> FST u IN V /\ LENGTH (SND u) = height (FST u) /\
     !i. MEM (SOME i) (SND u) ==> i < LENGTH q` by
    (simp[markerLib.L "membership", MEM_EL] >> metis_tac[]) >>
  pop_assum (mk_asm "bounded") >>
  `!u k. u IN A /\ tag (FST u) k = NONE ==> proj u k = NONE` by
    (rpt gen_tac >> disch_then (CONJUNCTS_THEN2 (mk_asm "hu") (mk_asm "hnone")) >>
     reverse (Cases_on `k < height (FST u)`)
     >- simp[markerLib.L "project"] >>
     asm "membership" (qspec_then `u` (fn mem =>
       asm "hu" (fn hu =>
       asm "hnone" (fn hn =>
       qpat_assum `k < height (FST u)` (fn hk =>
       qpat_assum `!w. G NONE w ==> w = NONE` (fn ch =>
         let val slots = CONJUNCT2 (CONJUNCT2 (MP (iffLR mem) hu))
             val gn = REWRITE_RULE [hn] (MP (SPEC (rand (lhs (concl hn))) slots) hk)
             val slot = MP (SPEC (rand (concl gn)) ch) gn
         in simp[markerLib.L "project",hk,slot] end))))))) >>
  pop_assum (mk_asm "clear") >>
  `!u. u IN A ==> pc (FST u) < LENGTH p /\ pc (FST u) < LENGTH q /\
      Slots q (height (FST u)) (need (FST u)) (proj u) (boolean (FST u))` by
    (rpt gen_tac >> disch_tac >>
     (* fs[L "membership"] did not apply the implication to membership. *)
     asm "bounded" (qspec_then `u` (drule_then strip_assume_tac)) >>
     asm "vertices" (qspec_then `FST u` (drule_then strip_assume_tac)) >>
     `pc (FST u) < LENGTH q` by simp[markerLib.L "program"] >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
     qpat_x_assum `Slots p _ _ _ _` (fn hs =>
       asm "slots" (fn eq => STRIP_ASSUME_TAC (BETA_RULE (REWRITE_RULE [eq] hs)))) >>
     simp[markerLib.L "slots"] >>
     rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
     >- (rpt gen_tac >> disch_then (fn hb =>
           qpat_assum `!j. boolean (FST u) j ==> j < height (FST u) /\ tag (FST u) j = NONE`
             (STRIP_ASSUME_TAC o (fn h => MP (SPEC (rand (concl hb)) h) hb))) >>
         asm "clear" (qspecl_then [`u`,`k`] (fn th => simp[th]))) >>
     rpt gen_tac >> reverse (Cases_on `k < height (FST u)`)
     >- simp[markerLib.L "project"] >>
     simp[markerLib.L "project"] >>
     disch_then (fn h =>
       qpat_assum `!w a i. E w = SOME (a,i) ==> _`
         (strip_assume_tac o C MATCH_MP h)) >>
     qpat_x_assum `Prod _ _` (fn hp =>
       asm "prod" (fn eq => mp_tac (BETA_RULE (REWRITE_RULE [eq] hp)))) >>
     simp[] >> metis_tac[]) >>
  pop_assum (mk_asm "destslots") >>
  (* The export compares rational ranks, whereas the bypass consumes a
     natural rank. Count strictly lower vertices; ties need not be broken. *)
  qabbrev_tac `lower = \a. {w | w IN V /\ rat$rat_les (rank w) (rank a)}` >>
  qabbrev_tac `N = \a. CARD (lower a)` >>
  `!a. FINITE (lower a)` by
    (gen_tac >> irule SUBSET_FINITE_I >> qexists `V` >>
     asm "finite" assume_tac >> simp[Abbr `lower`, SUBSET_DEF]) >>
  `!a b. a IN V /\ rat$rat_les (rank a) (rank b) ==> N a < N b` by
    (rpt gen_tac >> strip_tac >> simp[Abbr `N`] >> irule CARD_PSUBSET >>
     simp[PSUBSET_MEMBER] >> conj_tac
     >- (simp[Abbr `lower`, SUBSET_DEF] >> metis_tac[ratTheory.RAT_LES_TRANS]) >>
     qexists `a` >> simp[Abbr `lower`, ratTheory.RAT_LES_REF]) >>
  pop_assum (mk_asm "rank_inc") >>
  `!a b. a IN V /\ b IN V ==>
      (N a < N b <=> rat$rat_les (rank a) (rank b))` by
    (rpt gen_tac >> strip_tac >> eq_tac
     >- (disch_tac >> spose_not_then assume_tac >>
         `rank a = rank b \/ rat$rat_les (rank b) (rank a)` by
           metis_tac[ratTheory.RAT_LES_TOTAL]
         >- (qpat_assum `N a < N b` mp_tac >>
             simp[Abbr `N`, Abbr `lower`] >> gvs[]) >>
         `N b < N a` by (asm "rank_inc" irule >> simp[]) >> decide_tac) >>
     disch_tac >> asm "rank_inc" irule >> simp[]) >>
  pop_assum (mk_asm "rank_order") >>
  `!r tx j. (?l orig off. tx 0 = SOME(l,orig) /\
        FLOOKUP (SND (compute_label_offsets r)) l = SOME off /\
        off < dimword(:256) /\ FLOOKUP (build_offset_to_pc r) off = SOME j)
      <=> Target r tx j` by
    (simp[markerLib.L "target", markerLib.L "canonical"] >>
     rpt gen_tac >> eq_tac
     >- (strip_tac >> qexistsl [`l`,`orig`] >> simp[] >> qexists `off` >> simp[]) >>
     strip_tac >> qexistsl [`l`,`o'`,`off`] >> simp[]) >>
  pop_assum (mk_asm "target_flat") >>
  `!v. v IN V /\ pc v = LENGTH pre ==>
     ?z. z IN V /\ N z < N v /\ height z = height v /\ C' p y (pc z) /\
         (!k. tag z k <> NONE ==> tag z k = tag v k) /\
         (!k. boolean z k ==> boolean v k)` by
    (qx_gen_tac `v` >> strip_tac >>
     mp_tac (Q.INST [`rank:num#num -> num` |-> `N:num#num -> num`]
       (SPEC_ALL (CONV_RULE arm_names_conv merge_rename_root_bypass))) >>
     SIMP_TAC bool_ss [EMPTY_SUBSET, DIFF_EMPTY] >>
     (impl_tac >-
       (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
        TRY (MAP_FIRST (fn s => asm s ACCEPT_TAC) ["wf","site","guard","finite"]) >>
        TRY (asm "shape" (fn sh => asm "progress"
          (ACCEPT_TAC o BETA_RULE o REWRITE_RULE [sh])))
        >- (gen_tac >> disch_tac >> asm "vertices" (drule_then strip_assume_tac) >>
            qexists `t` >> asm "shape" (fn sh => qpat_assum `Shape _ t`
              (ACCEPT_TAC o BETA_RULE o REWRITE_RULE [sh])))
        >- (gen_tac >> disch_tac >> asm "vertices" (drule_then strip_assume_tac) >>
            first_assum ACCEPT_TAC) >>
        qx_gen_tac `a` >> qx_gen_tac `b` >> disch_tac >>
        asm "edges" (qspecl_then [`a`,`b`] (drule_then strip_assume_tac)) >>
        rpt conj_tac >> TRY (first_assum ACCEPT_TAC)
        >- (asm "rank_inc" irule >> simp[])
        >- (asm "flow" (fn fl => qpat_assum `Flow p _ _ _ _ _ _ _ _`
              (ACCEPT_TAC o SIMP_RULE bool_ss [fl,LET_THM]))) >>
        asm "target_flat" (fn tf => SIMP_TAC bool_ss [tf,SF ETA_ss]) >>
        asm "control" (fn ct => qpat_assum `Control p _ _ _`
          (ACCEPT_TAC o SIMP_RULE bool_ss [ct])))) >>
     disch_then (qx_choose_then `z` (qx_choose_then `off` strip_assume_tac)) >>
     qexists `z` >> simp[markerLib.L "canonical"] >>
     conj_tac
     >- (qexists `off` >> asm "site" (fn th => simp[th])) >>
     gen_tac >> Cases_on `tag z k` >> simp[] >>
     PairCases_on `x'` >> metis_tac[]) >>
  pop_assum (mk_asm "bypass") >>
  `!u w. u IN A /\ w IN V /\ Target p (tag (FST u)) (pc w) ==>
     ?z. z IN V /\ N z <= N w /\ height z = height w /\ Target q (proj u) (pc z) /\
         (!k. tag z k <> NONE ==> tag z k = tag w k) /\
         (!k. boolean z k ==> boolean w k)` by
    (rpt gen_tac >> simp[markerLib.L "target"] >> strip_tac >>
     asm "membership" (drule_then strip_assume_tac o iffLR) >>
     asm "vertices" (qspecl_then [`FST u`] (drule_then strip_assume_tac)) >>
     qpat_assum `Slots p _ _ _ _` (fn hs => asm "slots"
       (fn eq => STRIP_ASSUME_TAC (BETA_RULE (REWRITE_RULE [eq] hs)))) >>
     `0 < height (FST u)` by
       (qpat_assum `!k l orig. tag (FST u) k = SOME (l,orig) ==> _`
          (drule_then strip_assume_tac) >> simp[]) >>
     `G (SOME (l,o')) (EL 0 (SND u))` by
       (qpat_assum `tag (FST u) 0 = SOME (l,o')` (SUBST1_TAC o SYM) >>
        qpat_assum `!k. k < height (FST u) ==> G (tag (FST u) k) _`
          (qspec_then `0` irule) >> first_assum ACCEPT_TAC) >>
     qpat_assum `!l o' u. G (SOME (l,o')) u ==> _`
       (drule_then (qx_choose_then `i` (qx_choose_then `a`
          (map_every assume_tac o CONJUNCTS)))) >>
     mp_tac (Q.INST [`rank:num#num -> num` |-> `N:num#num -> num`]
       (INST_TYPE
         [``:'a`` |-> ``:num``, ``:'b`` |-> ``:num``,
          ``:'c`` |-> ``:string#num``, ``:'d`` |-> ``:num``]
         rename_arm_taken_geometry)) >>
     arm_use_names ["program","canonical"] >>
     (impl_tac >-
       (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
        MAP_FIRST (fn s => asm s ACCEPT_TAC) ["wf","site","layout","bypass"])) >>
     disch_then (qx_choose_then `z` strip_assume_tac) >>
     qpat_assum `!j. C' q a j ==> _`
       (qspec_then `pc z` (drule_then assume_tac)) >>
     `E (SOME i) = SOME (a,i)` by
       (qpat_assum `EL 0 (SND u) = SOME i` (fn eq =>
          qpat_assum `E (EL 0 (SND u)) = SOME (a,i)`
            (ACCEPT_TAC o PURE_REWRITE_RULE [eq]))) >>
     qexists `z` >> simp[markerLib.L "project"] >>
     qexistsl [`a`,`i`] >> simp[]) >>
  pop_assum (mk_asm "taken") >>
  `!u w z. u IN A /\ edge (FST u) w /\ z IN V /\ height z = height w /\
      (!k. tag z k <> NONE ==> tag z k = tag w k) /\
      (!k. boolean z k ==> boolean w k) ==>
      ?v. v IN A /\ FST v = z /\
          Flow q (pc (FST u)) (EL (pc (FST u)) q) (height (FST u)) (height z)
            (proj u) (proj v) (boolean (FST u)) (boolean z)` by
    (rpt gen_tac >> strip_tac >>
     asm "membership" (drule_then strip_assume_tac o iffLR) >>
     asm "vertices" (qspecl_then [`FST u`] (drule_then strip_assume_tac)) >>
     asm "edges" (qspecl_then [`FST u`,`w`] (drule_then strip_assume_tac)) >>
     `EL (pc (FST u)) q = rename_push_label x y (EL (pc (FST u)) p)` by
       simp[markerLib.L "program", EL_MAP] >>
     simp[markerLib.L "membership", markerLib.L "project", PULL_EXISTS] >>
     `?Dz. LENGTH Dz = height w /\
         (!k. k < height w ==> G (tag z k) (EL k Dz)) /\
         Flow q (pc (FST u)) (rename_push_label x y (EL (pc (FST u)) p))
           (height (FST u)) (height w)
           (\k. if k < height (FST u) then E (EL k (SND u)) else NONE)
           (\k. if k < height w then E (EL k Dz) else NONE)
           (boolean (FST u)) (boolean z)` by
       ((* BETA_TAC alone leaves redexes created by specializing the
            inherited slot maps. Normalize both interfaces to a fixed point. *)
        let val canon = REDEPTH_CONV BETA_CONV in
          asm "flow" (fn f => PURE_REWRITE_TAC [f,LET_THM] >> CONV_TAC canon >>
            qpat_assum `Flow p _ _ _ _ _ _ _ _`
              (assume_tac o CONV_RULE canon o REWRITE_RULE [f,LET_THM])) >>
          match_mp_tac (rename_arm_flow |> CONV_RULE arm_names_conv |> GEN_ALL)
        end >>
        qexistsl [`tag w`,`tag (FST u)`,`p`,`boolean w`] >>
        rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
        FIRST [rpt gen_tac >> disch_tac >> first_assum (irule_at Any) >> simp[] >> NO_TAC,
               gvs[]]) >>
     qexists `(z,Dz)` >> simp[]) >>
  pop_assum (mk_asm "lift") >>
  `!u. u IN A ==>
      EL (pc (FST u)) q = rename_push_label x y (EL (pc (FST u)) p)` by
    (gen_tac >> disch_tac >> asm "destslots" (drule_then strip_assume_tac) >>
     simp[markerLib.L "program",EL_MAP]) >>
  pop_assum (mk_asm "fetch") >>
  `!u name. u IN A ==>
      (EL (pc (FST u)) q = AsmOp name <=> EL (pc (FST u)) p = AsmOp name)` by
    (rpt gen_tac >> disch_tac >> asm "fetch" (drule_then SUBST1_TAC) >>
     Cases_on `EL (pc (FST u)) p` >> simp[rename_push_label_def] >>
     IF_CASES_TAC >> simp[]) >>
  pop_assum (mk_asm "opcode") >>
  `!u. u IN A ==> !l.
      (EL (pc (FST u)) q = AsmPushLabel l \/ (?d. EL (pc (FST u)) q = AsmPushOfst l d)) ==>
      IS_SOME (FLOOKUP (SND(compute_label_offsets q)) l)` by
    (gen_tac >> disch_tac >> asm "destslots" (drule_then strip_assume_tac) >>
     mp_tac (Q.INST [`i` |-> `(pc:num#num -> num) (FST (u:(num#num)#num option list))`] rename_arm_reference_fetch) >>
     arm_use_names ["program"] >>
     (impl_tac >-
       (rpt conj_tac >> TRY (first_assum ACCEPT_TAC) >>
        MAP_FIRST (fn s => asm s ACCEPT_TAC) ["site","guard","wf"])) >>
     simp[optionTheory.IS_SOME_EXISTS]) >>
  pop_assum (mk_asm "reference") >>
  (* Preserve the source arm's output height, including the success arm of
     an operation that can also fault. Only taken arms use a different PC. *)
  qabbrev_tac `R = \u v.
    rank (FST v) < rank (FST u) /\
    Flow q (pc (FST u)) (EL (pc (FST u)) q) (height (FST u)) (height (FST v))
      (proj u) (proj v) (boolean (FST u)) (boolean (FST v)) /\
    ?w. edge (FST u) w /\ height w = height (FST v) /\
      ((EL (pc (FST u)) q <> AsmOp "JUMP" /\
        pc w = pc (FST u)+1 /\ pc (FST v) = pc w) \/
       ((EL (pc (FST u)) q = AsmOp "JUMP" \/ EL (pc (FST u)) q = AsmOp "JUMPI") /\
        Target p (tag (FST u)) (pc w) /\ Target q (proj u) (pc (FST v))))` >>
  qabbrev_tac `DArms = \u j hj.
    ?v. v IN A /\ R u v /\ pc (FST v) = j /\ height (FST v) = hj` >>
  `!u j j'. Target q (proj u) j /\ Target q (proj u) j' ==> j = j'` by
    (simp[markerLib.L "target",markerLib.L "canonical",PULL_EXISTS] >> rpt strip_tac >> gvs[]) >>
  pop_assum (mk_asm "unique") >>
  `!u w. u IN A /\ edge (FST u) w ==> N w < N (FST u)` by
    (rpt gen_tac >> strip_tac >> asm "edges" (drule_then strip_assume_tac) >>
     asm "rank_inc" irule >> simp[]) >>
  pop_assum (mk_asm "edge_rank") >>
  `!u w. u IN A /\ edge (FST u) w /\ EL (pc (FST u)) q <> AsmOp "JUMP" /\
     pc w = pc (FST u) + 1 ==> DArms u (pc w) (height w)` by
    (rpt gen_tac >> strip_tac >> asm "edges" (drule_then strip_assume_tac) >>
     asm "lift" (qspecl_then [`u`,`w`,`w`] mp_tac) >> simp[] >> strip_tac >>
     simp[Abbr `DArms`,Abbr `R`] >> qexists `v` >> simp[] >>
     qexists `w` >> simp[]) >>
  pop_assum (mk_asm "arm_fall") >>
  `!u w. u IN A /\ edge (FST u) w /\ Target p (tag (FST u)) (pc w) /\
      (EL (pc (FST u)) q = AsmOp "JUMP" \/ EL (pc (FST u)) q = AsmOp "JUMPI") ==>
      ?j. Target q (proj u) j /\ DArms u j (height w)` by
    (rpt gen_tac >> strip_tac >> asm "edges" (drule_then strip_assume_tac) >>
     asm "edge_rank" (drule_all_then assume_tac) >>
     asm "taken" (drule_all_then (qx_choose_then `z` strip_assume_tac)) >>
     `N z < N (FST u)` by decide_tac >>
     `rank z < rank (FST u)` by
       (asm "rank_order" (qspecl_then [`z`,`FST u`] mp_tac) >> simp[]) >>
     asm "lift" (qspecl_then [`u`,`w`,`z`] mp_tac) >> simp[] >> strip_tac >>
     qexists `pc z` >> simp[Abbr `DArms`,Abbr `R`] >>
     qexists `v` >> simp[] >> qexists `w` >> simp[]) >>
  pop_assum (mk_asm "arm_taken") >>
  `!u j hj. DArms u j hj ==>
     ?v. v IN A /\ R u v /\ pc (FST v) = j /\ height (FST v) = hj` by
    simp[Abbr `DArms`] >>
  pop_assum (mk_asm "dest_arm_elim") >>
  `!u v. R u v ==>
     ?w. edge (FST u) w /\ height w = height (FST v) /\
       ((EL (pc (FST u)) q <> AsmOp "JUMP" /\
         pc w = pc (FST u)+1 /\ pc (FST v) = pc w) \/
        ((EL (pc (FST u)) q = AsmOp "JUMP" \/ EL (pc (FST u)) q = AsmOp "JUMPI") /\
         Target p (tag (FST u)) (pc w) /\ Target q (proj u) (pc (FST v))))` by
    simp[Abbr `R`] >>
  pop_assum (mk_asm "edge_elim") >>
  `!v j hj. Arms v j hj <=> ?w. edge v w /\ pc w = j /\ height w = hj` by
    simp[Abbr `Arms`] >>
  pop_assum (mk_asm "source_arm") >>
  `!u j hj. u IN A ==>
     (DArms u j hj <=>
       (EL (pc (FST u)) q <> AsmOp "JUMP" /\ j = pc (FST u)+1 /\ Arms (FST u) j hj) \/
       ((EL (pc (FST u)) q = AsmOp "JUMP" \/ EL (pc (FST u)) q = AsmOp "JUMPI") /\
        Target q (proj u) j /\ ?j'. Target p (tag (FST u)) j' /\ Arms (FST u) j' hj))` by
    (rpt gen_tac >> disch_tac >> eq_tac
     >- (disch_tac >> asm "dest_arm_elim" (drule_then (qx_choose_then `v` strip_assume_tac)) >>
         asm "edge_elim" (drule_then (qx_choose_then `w`
           (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac
             (DISJ_CASES_THEN (map_every assume_tac o CONJUNCTS))))))
         >- (disj1_tac >> conj_tac >- first_assum ACCEPT_TAC >>
             conj_tac >- simp[SF SFY_ss] >>
             simp[NoAsms, markerLib.L "source_arm"] >> qexists `w` >> simp[]) >>
         disj2_tac >> conj_tac >- first_assum ACCEPT_TAC >>
         conj_tac >- metis_tac[] >> qexists `pc w` >>
         conj_tac >- first_assum ACCEPT_TAC >>
         simp[NoAsms, markerLib.L "source_arm"] >> qexists `w` >> simp[]) >>
     disch_then (DISJ_CASES_THEN (map_every assume_tac o CONJUNCTS))
     >- (asm "source_arm" (drule_then (qx_choose_then `w` strip_assume_tac) o iffLR) >>
         `DArms u (pc w) (height w)` suffices_by metis_tac[] >>
         asm "arm_fall" irule >> metis_tac[]) >>
     qpat_x_assum `?j'. _ /\ Arms _ j' _` (qx_choose_then `j'` strip_assume_tac) >>
     asm "source_arm" (drule_then (qx_choose_then `w` strip_assume_tac) o iffLR) >>
     `?k. Target q (proj u) k /\ DArms u k (height w)` by
       (asm "arm_taken" irule >> simp[]) >>
     `k = j` by (asm "unique" irule >> metis_tac[]) >> metis_tac[]) >>
  pop_assum (mk_asm "arm_spec") >>
  qexists `R` >> conj_tac >- asm "bounded" ACCEPT_TAC >>
  reverse conj_tac
  >- (simp[Abbr `R`,markerLib.L "control",PULL_EXISTS] >>
      rpt strip_tac >> simp[] >> metis_tac[]) >>
  gen_tac >> disch_tac >>
  asm "destslots" (drule_then strip_assume_tac) >> simp[] >>
  `Row q (pc (FST u)) (height (FST u)) (proj u) (DArms u)` suffices_by
    simp[Abbr `DArms`] >>
  asm "bounded" (drule_then strip_assume_tac) >>
  asm "vertices" (drule_then strip_assume_tac) >>
  asm "fetch" (drule_then assume_tac) >>
  asm "arm_spec" (qspec_then `u` (drule_then assume_tac)) >>
  `!k. tag (FST u) k = NONE ==> proj u k = NONE` by
    (rpt strip_tac >> asm "clear" irule >> simp[]) >>
  `!hj. (EL (pc (FST u)) q = AsmOp "JUMP" \/ EL (pc (FST u)) q = AsmOp "JUMPI") /\
      (?j. Target p (tag (FST u)) j /\ Arms (FST u) j hj) ==>
      ?j. Target q (proj u) j` by
    (gen_tac >> disch_then (CONJUNCTS_THEN2 assume_tac
       (qx_choose_then `j` strip_assume_tac)) >>
     asm "source_arm" (drule_then (qx_choose_then `w` strip_assume_tac) o iffLR) >>
     `?k. Target q (proj u) k /\ DArms u k (height w)` by
       (asm "arm_taken" irule >> simp[]) >>
     qexists `k` >> simp[]) >>
  pop_assum (mk_asm "row_target") >>
  `ALOOKUP dup_table "JUMP" = NONE /\ ALOOKUP swap_table "JUMP" = NONE /\
   ALOOKUP dup_table "JUMPI" = NONE /\ ALOOKUP swap_table "JUMPI" = NONE` by EVAL_TAC >>
  asm "source_arm" (fn th => qpat_x_assum `Row p _ _ _ _`
    (mp_tac o SIMP_RULE (bool_ss ++ ETA_ss) [GSYM th])) >>
  namedCases_on `EL (pc (FST u)) p` ["name","bs","l","l d","l","l","bs","l"] >>
  simp[markerLib.L "row",rename_push_label_def]
  >- (disch_then (DISJ_CASES_THEN2
        (CONJUNCTS_THEN2 (mk_asm "terminal") (mk_asm "dead")) mp_tac)
      >- (disj1_tac >> conj_tac
          >- (asm "terminal" (DISJ_CASES_THEN strip_assume_tac) >> simp[]) >>
          simp[markerLib.L "dead"]) >>
      disch_then (fn src => disj2_tac >> mp_tac src) >>
      Cases_on `name = "JUMP"`
      >- (simp[] >> strip_tac >> simp[] >> conj_tac
          >- (asm "row_target" (qspec_then `height (FST u) - 1` irule) >>
              simp[rename_push_label_def] >> metis_tac[]) >>
          simp[SF CONJ_ss,LEFT_EXISTS_AND_THM] >> metis_tac[]) >>
      Cases_on `name = "JUMPI"`
      >- (simp[] >> strip_tac >> simp[] >> conj_tac
          >- (asm "row_target" (qspec_then `height (FST u) - 2` irule) >>
              simp[rename_push_label_def] >> metis_tac[]) >>
          Q_TAC (fn tm => SUBGOAL_THEN tm
            (fn th => simp[SF CONJ_ss,LEFT_EXISTS_AND_THM,th]))
            `?j'. Target p (tag (FST u)) j'`
          >- (qexists `j` >> simp[]) >>
          rpt gen_tac >> Cases_on `hj = height (FST u) - 2` >> simp[]) >>
      Cases_on `ALOOKUP dup_table name`
      >- (Cases_on `ALOOKUP swap_table name` >> simp[]
          >- (strip_tac >> qexists `m` >> simp[]) >>
          strip_tac >> simp[]) >>
      simp[] >> strip_tac >> simp[])
  >- (Cases_on `l = x` >> simp[] >> strip_tac >> simp[] >>
      asm "reference" (qspec_then `u` (drule_then irule)) >>
      simp[rename_push_label_def]) >>
  strip_tac >> simp[] >> asm "reference" (qspec_then `u` (drule_then irule)) >>
  simp[rename_push_label_def]
QED
