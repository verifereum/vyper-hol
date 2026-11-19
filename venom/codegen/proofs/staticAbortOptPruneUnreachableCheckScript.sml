(* Preserve the positive arm witnesses and the universal row checks. *)
Theory staticAbortOptPruneUnreachableCheck
Ancestors
  asmOptimizer asmSem asmSymSem asmSymBridge asmToBytecodeProofs
  staticAbortStraight symbolResolve finite_map option words arithmetic list
  pred_set combin

(* Normalize the two literal opcode patterns without unfolding the row body. *)
Theorem check_op_dispatch[local]:
  !name (invalid:bool) revert ordinary.
    (case AsmOp name of
       AsmOp "INVALID" => invalid
     | AsmOp "REVERT" => revert
     | AsmOp opn => ordinary opn
     | _ => F) =
    (if name = "INVALID" then invalid
     else if name = "REVERT" then revert else ordinary name)
Proof
  rpt gen_tac >> simp[] >>
  rpt (qmatch_goalsub_rename_tac `list_CASE (cs:char list) _ _` >>
       Cases_on `cs` >> simp[]) >>
  rpt IF_CASES_TAC >> simp[]
  >> (gvs[])
QED

Theorem check_case_presentation:
  !ins lab push plabel pofst invalid revert ordinary.
    (case ins of
       AsmLabel l => lab l
     | AsmPush bs => push bs
     | AsmPushLabel l => plabel l
     | AsmPushOfst l d => pofst l d
     | AsmOp "INVALID" => invalid
     | AsmOp "REVERT" => revert
     | AsmOp name => ordinary name
     | _ => F) =
    (case ins of
       AsmLabel l => lab l
     | AsmPush bs => push bs
     | AsmPushLabel l => plabel l
     | AsmPushOfst l d => pofst l d
     | AsmOp name => if name = "INVALID" then invalid
                     else if name = "REVERT" then revert else ordinary name
     | _ => F)
Proof
  Cases >> SIMP_TAC bool_ss [asmIRTheory.asm_inst_case_def] >>
  rpt gen_tac >>
  MATCH_ACCEPT_TAC (SIMP_RULE bool_ss [asmIRTheory.asm_inst_case_def] check_op_dispatch)
QED

Theorem prune_one_relocated_check:
  !pre t x tail (V:(num#num)->bool) cc pc height
    (tag:(num#num)->num->(string#num)option) edge.
  !p q d r tagQ Hit Target fall taken Check.
    p = pre ++ [t;x] ++ tail ==> q = pre ++ [t] ++ tail ==>
    d = LENGTH pre+1 ==> r = (\i. if i < d then i else i-1) ==>
    tagQ = (\v k. OPTION_MAP (\(l,i). (l,if i=d then
      (@j. j < LENGTH q /\ (EL j q = AsmPushLabel l \/ EL j q = AsmPushOfst l 0))
      else r i)) (tag v k)) ==>
    Hit = (\p l j.
      ?off. FLOOKUP (SND (compute_label_offsets p)) l = SOME off /\
        off < dimword(:256) /\ FLOOKUP (build_offset_to_pc p) off = SOME j) ==>
    Target = (\p pc tag (a:num#num) (b:num#num).
      ?l i. tag a 0 = SOME(l,i) /\ Hit p l (pc b)) ==>
    fall = (\a b. edge a b /\ ~asm_terminal_op (EL (pc a) p) /\ pc b = pc a+1) ==>
    taken = (\a l b. edge a b /\
      (EL (pc a) p = AsmOp "JUMP" \/ EL (pc a) p = AsmOp "JUMPI") /\
      (?i. tag a 0 = SOME(l,i)) /\ Hit p l (pc b)) ==>
    Check = (\p cc pc height tag edge x.
      !h fall arm legal next untagged stop.
      h = height x ==> fall = (\y. pc y = pc x + 1) ==>
      arm = (\P n. ?y. edge x y /\ P y /\ height y = n) ==>
      legal = (\P n. !y. edge x y ==> P y /\ height y = n) ==>
      next = (\n. arm fall n /\ legal fall n) ==>
      untagged = (\a. !k. k<a ==> tag x k=NONE) ==>
      stop = (\a. a<=h /\ untagged a /\ !y. ~edge x y) ==>
      case EL (pc x) p of
        AsmLabel l => next h
      | AsmPush bs => next (h+1)
      | AsmPushLabel l => IS_SOME (FLOOKUP (SND (compute_label_offsets p)) l) /\ next (h+1)
      | AsmPushOfst l delta => IS_SOME (FLOOKUP (SND (compute_label_offsets p)) l) /\ next (h+1)
      | AsmOp "INVALID" => stop 0
      | AsmOp "REVERT" => stop 2
      | AsmOp name =>
          if MEM name ["SSTORE";"TSTORE";"LOG0";"LOG1";"LOG2";"LOG3";"LOG4"]
          then cc.cc_static /\ stop (asm_op_arity name)
          else
            (case ALOOKUP dup_table name of
               SOME n => n<h /\ next (h+1)
             | NONE => case ALOOKUP swap_table name of
                 SOME n => 0<n /\ n<h /\ next h
               | NONE =>
                   if name="JUMP" then
                      1<=h /\ arm (Target p pc tag x) (h-1) /\
                      legal (Target p pc tag x) (h-1)
                   else if name="JUMPI" then
                      2<=h /\ tag x 1=NONE /\ arm fall (h-2) /\
                      arm (Target p pc tag x) (h-2) /\
                      legal (\y. fall y \/ Target p pc tag x y) (h-2)
                   else
                      ?m. static_abort_straight name m /\ asm_op_arity name <= h /\
                          untagged (asm_op_arity name) /\ next (h-asm_op_arity name+m))
      | _ => F) ==>
    (!v. v IN V ==> pc v < LENGTH p /\ Check p cc pc height tag edge v) /\
    (!a b. edge a b ==> a IN V /\ b IN V) /\ asm_static_wf q /\
    (!v. v IN V ==> pc v <> d /\ r (pc v) < LENGTH q /\
      EL (r (pc v)) q = EL (pc v) p) /\
    (!a b. edge a b <=> fall a b \/ ?l. taken a l b) /\
    (!a b. fall a b ==> r (pc b) = r (pc a)+1) /\
    (!a l b. taken a l b ==> Hit q l (r (pc b))) /\
    (!a b. edge a b /\ EL (pc a) p <> AsmOp "JUMP" /\ pc b = pc a+1 ==>
      r (pc b) = r (pc a)+1) /\
    (!a b. edge a b /\
      (EL (pc a) p = AsmOp "JUMP" \/ EL (pc a) p = AsmOp "JUMPI") /\
      Target p pc tag a b ==> Target q (r o pc) tagQ a b) ==>
    !v. v IN V ==> (r o pc) v < LENGTH q /\ Check q cc (r o pc) height tagQ edge v
Proof
  rpt gen_tac >>
  ntac 9 (disch_then (assume_tac o ONCE_REWRITE_RULE [GSYM markerTheory.Abbrev_def])) >>
  disch_then (assume_tac o ONCE_REWRITE_RULE [GSYM markerTheory.Abbrev_def] o
                        SIMP_RULE (pure_ss ++ boolSimps.UNWIND_ss) []) >>
  strip_tac >> qx_gen_tac `v` >> disch_tac >>
  qpat_x_assum `!v. v IN V ==> pc v <> d /\ _`
    (drule_then strip_assume_tac) >>
  conj_tac >- simp[o_THM] >>
  qpat_x_assum `!v. v IN V ==> pc v < LENGTH p /\ _`
    (drule_then strip_assume_tac) >>
  `!k. tagQ v k = NONE <=> tag v k = NONE` by
    (gen_tac >> Cases_on `tag v k` >> simp[Abbr `tagQ`]) >>
  `!l. (EL (r (pc v)) q = AsmPushLabel l \/
        (?delta. EL (r (pc v)) q = AsmPushOfst l delta)) ==>
       IS_SOME (FLOOKUP (SND (compute_label_offsets q)) l)` by
    (gen_tac >> disch_tac >> simp[FLOOKUP_DEF, COND_RAND] >>
     simp[compute_label_offsets_def,clo_step_eq] >> irule clo_FDOM >>
     `MEM l (asm_label_refs q)` by
       (SIMP_TAC (srw_ss()) [asm_label_refs_def, MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
        qexists `EL (r (pc v)) q` >>
        conj_tac >- (irule EL_MEM >> first_assum ACCEPT_TAC) >>
        qpat_assum `_ = AsmPushLabel _ \/ _`
          (DISJ_CASES_THEN2 SUBST1_TAC (CHOOSE_THEN SUBST1_TAC)) >> simp[]) >>
     fs[asm_static_wf_def]) >>
  qpat_x_assum `!a b. edge a b /\ EL (pc a) p <> AsmOp "JUMP" /\ _ ==> _`
    (qspec_then `v:num#num` assume_tac) >>
  qpat_x_assum `!a b. edge a b /\ _ /\ Target p pc tag a b ==> _`
    (qspec_then `v:num#num` assume_tac) >>
  qpat_x_assum `!a b. edge a b <=> _` kall_tac >>
  qpat_x_assum `Check p cc pc height tag edge v` mp_tac >>
  `Check = \p cc pc height tag edge x.
      let h = height x in
      let fall = \y. pc y = pc x + 1 in
      let arm = \P n. ?y. edge x y /\ P y /\ height y = n in
      let legal = \P n. !y. edge x y ==> P y /\ height y = n in
      let next = \n. arm fall n /\ legal fall n in
      let untagged = \a. !k. k<a ==> tag x k=NONE in
      let stop = \a. a<=h /\ untagged a /\ !y. ~edge x y in
      let ordinary = \name.
        if MEM name ["SSTORE";"TSTORE";"LOG0";"LOG1";"LOG2";"LOG3";"LOG4"]
        then cc.cc_static /\ stop (asm_op_arity name)
        else
          (case ALOOKUP dup_table name of
             SOME n => n<h /\ next (h+1)
           | NONE => case ALOOKUP swap_table name of
               SOME n => 0<n /\ n<h /\ next h
             | NONE =>
                 if name="JUMP" then
                    1<=h /\ arm (Target p pc tag x) (h-1) /\
                    legal (Target p pc tag x) (h-1)
                 else if name="JUMPI" then
                    2<=h /\ tag x 1=NONE /\ arm fall (h-2) /\
                    arm (Target p pc tag x) (h-2) /\
                    legal (\y. fall y \/ Target p pc tag x y) (h-2)
                 else
                    ?m. static_abort_straight name m /\ asm_op_arity name <= h /\
                        untagged (asm_op_arity name) /\ next (h-asm_op_arity name+m))
      in
      case EL (pc x) p of
        AsmLabel l => next h
      | AsmPush bs => next (h+1)
      | AsmPushLabel l => IS_SOME (FLOOKUP (SND (compute_label_offsets p)) l) /\ next (h+1)
      | AsmPushOfst l d => IS_SOME (FLOOKUP (SND (compute_label_offsets p)) l) /\ next (h+1)
      | AsmOp name => if name = "INVALID" then stop 0
                      else if name = "REVERT" then stop 2 else ordinary name
      | _ => F` by
    (qpat_x_assum `Abbrev (Check = _)`
       (SUBST1_TAC o REWRITE_RULE [markerTheory.Abbrev_def]) >>
     ntac 7 ABS_TAC >>
     SIMP_TAC pure_ss [LET_THM] >> BETA_TAC >>
     CONV_TAC (RAND_CONV (HO_REWR_CONV (GSYM check_case_presentation))) >>
     BETA_TAC >> REFL_TAC) >>
  pop_assum SUBST1_TAC >>
  qpat_x_assum `Abbrev (Check = _)` kall_tac >>
  SIMP_TAC bool_ss [LET_THM,o_THM] >>
  qpat_assum `EL (r (pc v)) q = EL (pc v) p` (rewrite_tac o single) >>
  Cases_on `EL (pc v) p` >>
  SIMP_TAC bool_ss [asmIRTheory.asm_inst_case_def]
  >- (rename1 `EL (pc v) p = AsmOp name` >>
      Cases_on `name="INVALID"` >- fs[] >>
      Cases_on `name="REVERT"` >- fs[] >>
      Cases_on `MEM name ["SSTORE";"TSTORE";"LOG0";"LOG1";"LOG2";"LOG3";"LOG4"]`
      >- fs[] >>
      `ALOOKUP dup_table "JUMP" = NONE` by EVAL_TAC >>
      `ALOOKUP swap_table "JUMP" = NONE` by EVAL_TAC >>
      Cases_on `name="JUMP"` >- (fs[] >> metis_tac[]) >>
      Cases_on `ALOOKUP dup_table name`
      >- (Cases_on `ALOOKUP swap_table name`
          >- (Cases_on `name="JUMPI"` >- (fs[] >> metis_tac[]) >>
              fs[] >> strip_tac >> rename1 `static_abort_straight name m` >>
              qexists `m` >> metis_tac[]) >>
          fs[] >> metis_tac[]) >>
      fs[] >> metis_tac[]) >>
  fs[] >> metis_tac[]
QED
