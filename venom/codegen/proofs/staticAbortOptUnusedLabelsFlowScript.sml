(* Flow on the selected normal arms after a single unused-label deletion. *)
Theory staticAbortOptUnusedLabelsFlow
Ancestors
  staticAbortStraight asmOptimizer asmSplice asmSem asmIR
  alist arithmetic combin finite_map list option pair pred_set words

Theorem unused_label_one_selected_flow:
  !pre l tail V (pc:(num#num)->num) (height:(num#num)->num)
    tag boolean edge src fresh bnew H z.
  !p. p = pre++[AsmLabel l]++tail ==>
  !d. d = LENGTH pre ==>
  !q. q = pre++tail ==>
  !r. r = splice_pc d 1 0 ==>
  !pcQ. pcQ = r o pc ==>
  !P. P = OPTION_MAP (\(n,j). (n,r j)) ==>
  !Tags. Tags = (\x k. P (tag x k)) ==>
  !keep. keep = {u:num#num | u IN V /\ pc u<>d} ==>
  !Legal. Legal = (\u a.
    edge u (SND a) /\
    (if FST a then
       (EL (pc u) p = AsmOp "JUMP" \/ EL (pc u) p = AsmOp "JUMPI") /\
       (?n j off. tag u 0 = SOME(n,j) /\
          FLOOKUP (SND (compute_label_offsets p)) n = SOME off /\
          off < dimword(:256) /\ FLOOKUP (build_offset_to_pc p) off = SOME (pc (SND a)))
     else EL (pc u) p <> AsmOp "JUMP" /\ pc (SND a) = pc u+1)) ==>
  !Inherit. Inherit = (\u (w:num#num) tg (s:num->num option) (f:num->(string#num)option) b.
    (!k n j. tg w k = SOME(n,j) ==> k < height w /\
       (f k = SOME(n,j) \/ ?h. s k = SOME h /\ h < height u /\ tg u h = SOME(n,j))) /\
    (!k. boolean w k ==> k < height w /\
       (b k \/ ?h. s k = SOME h /\ h < height u /\ boolean u h))) ==>
  (* The numerical part of Flow, with its slot interpretation as a parameter.
     This binds the same descriptor in the source and selected-arm premises. *)
  !Row. Row = (\prog pos u hj inherit.
    !hi. hi = height u ==>
    !ins. ins = EL (pos u) prog ==>
    case ins of
      AsmLabel n => hj = hi /\ inherit (\k. SOME k) (\k. NONE) (\k. F)
    | AsmPush bs =>
        hj = hi+1 /\
        inherit (\k. if k=0 then NONE else SOME(k-1)) (\k. NONE)
          (\k. k=0 /\ !t v.
            asm_step (SND(compute_label_offsets prog)) (build_offset_to_pc prog)
              (AsmPush bs) t = AsmOK v ==>
            (EL 0 v.as_stack = 0w \/ EL 0 v.as_stack = 1w))
    | AsmPushLabel n =>
        hj = hi+1 /\
        inherit (\k. if k=0 then NONE else SOME(k-1))
          (\k. if k=0 then SOME(n,pos u) else NONE) (\k. F)
    | AsmPushOfst n delta =>
        hj = hi+1 /\
        inherit (\k. if k=0 then NONE else SOME(k-1))
          (\k. if k=0 /\ delta=0 then SOME(n,pos u) else NONE) (\k. F)
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
                 !t v. LENGTH t.as_stack=hi /\
                   asm_step (SND(compute_label_offsets prog)) (build_offset_to_pc prog)
                     ins t = AsmOK v ==>
                   (EL 0 v.as_stack=0w \/ EL 0 v.as_stack=1w)))
    | _ => F) ==>
  (!u. u IN keep ==> pcQ u < LENGTH q /\ EL (pcQ u) q = EL (pc u) p) /\
  (!u a. u IN keep /\ Legal u a ==>
    Row p pc u (H u) (\s f b. src u = s /\ fresh u = f /\ bnew u = b) /\
    (!name. EL (pc u) p = AsmOp name ==>
       IS_SOME (ALOOKUP dup_table name) \/ IS_SOME (ALOOKUP swap_table name) \/
       name="JUMP" \/ name="JUMPI" \/ (?m. static_abort_straight name m)) /\
    height (z u a) = H u /\ Inherit u (z u a) Tags (src u) (P o fresh u) (bnew u)) ==>
  !u w. (u IN keep /\ ?a. Legal u a /\ w = z u a) ==>
    Row q pcQ u (height w) (Inherit u w Tags)
Proof
  map_every qx_gen_tac [`pre`,`l`,`tail`,`V`,`pc`,`height`,`tag`,`boolean`,`edge`,
     `src`,`fresh`,`bnew`,`H`,`z`] >>
  map_every (fn name => qx_gen_tac name >>
    disch_then (assume_tac o CONV_RULE (REWR_CONV (GSYM markerTheory.Abbrev_def))))
    [`p`,`d`,`q`,`r`,`pcQ`,`P`,`Tags`,`keep`,`Legal`,`Inherit`,`Row`] >>
  strip_tac >> rpt gen_tac >> strip_tac >>
  qpat_x_assum `!u a. u IN keep /\ Legal u a ==> _` (drule_all_then strip_assume_tac) >>
  qpat_x_assum `!u. u IN keep ==> _` (drule_then strip_assume_tac) >>
  qpat_x_assum `w = z u a` SUBST_ALL_TAC >>
  `!s g bq. src u = s /\ P o fresh u = g /\
             (!k. bnew u k ==> bq k) ==> Inherit u (z u a) Tags s g bq` by
    (rpt gen_tac >> strip_tac >>
     qpat_x_assum `Inherit _ _ _ _ _ _` mp_tac >>
     gvs[Abbr `Inherit`] >> metis_tac[]) >>
  pop_assum (mk_asm "inherit") >>
  qpat_x_assum `!name. _ = AsmOp name ==> _` (mk_asm "classification") >>
  `!bs t. asm_step (SND (compute_label_offsets q)) (build_offset_to_pc q) (AsmPush bs) t =
           asm_step (SND (compute_label_offsets p)) (build_offset_to_pc p) (AsmPush bs) t` by
    simp[asm_step_def] >>
  `!n t. (?m. static_abort_straight n m) /\ asm_returns_zero_or_one (AsmOp n) ==>
      asm_step (SND (compute_label_offsets q)) (build_offset_to_pc q) (AsmOp n) t =
      asm_step (SND (compute_label_offsets p)) (build_offset_to_pc p) (AsmOp n) t` by
    (rpt strip_tac >> drule static_abort_straight_known >> strip_tac >>
     `MEM n ["LT";"GT";"SLT";"SGT";"EQ";"ISZERO"]` by gvs[asm_returns_zero_or_one_def] >>
     pop_assum mp_tac >> simp[] >> strip_tac >>
     simp[asm_step_def,asm_step_op_def,asm_step_arith_def,asm_step_compare_def]) >>
  qpat_x_assum `Row p _ _ _ _` mp_tac >>
  simp[Abbr `Row`] >>
  Cases_on `EL (pc u) p` >> fs[] >>
  TRY (rename1 `ALOOKUP dup_table name` >>
       Cases_on `ALOOKUP dup_table name` >> fs[] >>
       TRY (qpat_assum `ALOOKUP dup_table name = NONE` kall_tac >>
            Cases_on `ALOOKUP swap_table name` >> fs[])) >>
  strip_tac >> rpt (conj_tac >- metis_tac[]) >>
  asm "inherit" irule >>
  simp[FUN_EQ_THM,Abbr `P`,Abbr `pcQ`] >>
  TRY (gen_tac >> IF_CASES_TAC >> simp[] >> NO_TAC) >>
  asm_x "classification" (qspec_then `name` mp_tac) >> simp[] >>
  strip_tac
  >- gvs[asm_returns_zero_or_one_def]
  >- gvs[asm_returns_zero_or_one_def] >>
  rpt strip_tac >>
  `?m. static_abort_straight name m` by (qexists `m` >> simp[]) >>
  qpat_assum `!n t. _ ==> asm_step _ _ (AsmOp n) t = _`
    (qspecl_then [`name`,`t`] mp_tac) >> simp[] >>
  (metis_tac[])
QED
