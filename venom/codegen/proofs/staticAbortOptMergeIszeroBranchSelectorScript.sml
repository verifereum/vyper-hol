(* Choose retained source occurrences after the erased branch tests. *)
Theory staticAbortOptMergeIszeroBranchSelector
Ancestors
  staticAbortOptMergeIszeroLive asmSem asmSymSem asmIR asmOptimizer
  finite_map words list pred_set arithmetic alist rat

Theorem merge_iszero_branch_selector:
  !p cc req (V:(num#num)->bool) (nrank:(num#num)->num) pc height need
     tag boolean edge b.
  !keep. keep = (\i. i < b \/ b+2 <= i) ==>
  !lo. lo = SND (compute_label_offsets p) ==>
  !otp. otp = build_offset_to_pc p ==>
  !Shape. Shape = (\(x:num#num) (s:asm_state).
    s.as_pc = pc x /\ LENGTH s.as_stack = height x /\
    s.as_call_ctx = cc /\ s.as_requests = req /\
    (need x ==> s.as_call_ctx.cc_static) /\
    (!k l origin. tag x k = SOME(l,origin) ==>
       k < height x /\ origin < LENGTH p /\
       (EL origin p = AsmPushLabel l \/
        (?d. EL origin p = AsmPushOfst l d) \/ EL origin p = AsmDataLabel l) /\
       ?off dest. FLOOKUP lo l = SOME off /\ off < dimword(:256) /\
         FLOOKUP otp off = SOME dest /\ EL k s.as_stack = (n2w off:bytes32)) /\
    (!k. boolean x k ==> k < height x /\
       (EL k s.as_stack = 0w \/ EL k s.as_stack = 1w))) ==>
  !Target. Target = (\(x:num#num) (y:num#num).
    ?l origin off. tag x 0 = SOME(l,origin) /\ FLOOKUP lo l = SOME off /\
      off < dimword(:256) /\ FLOOKUP otp off = SOME(pc y)) ==>
  (FINITE V /\ (!x. x IN V ==> ?s. Shape x s) /\
   (!x. x IN V ==> pc x < LENGTH p) /\
   (!x y. edge x y ==> x IN V /\ y IN V /\ nrank y < nrank x /\
     (!hi. hi = height x ==>
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
      | AsmPush bs => hj = hi+1 /\
          inherit (\k. if k=0 then NONE else SOME(k-1)) (\k. NONE)
            (\k. k=0 /\ !s v. asm_step lo otp (AsmPush bs) s = AsmOK v ==>
                    (EL 0 v.as_stack = 0w \/ EL 0 v.as_stack = 1w))
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
                 !m. m = hj + a - hi ==>
                 a <= hi /\ hj = m+(hi-a) /\
                 ((name="JUMP" \/ name="JUMPI") ==> m=0) /\
                 inherit (\k. if k<m then NONE else SOME(k-m+a)) (\k. NONE)
                   (\k. k=0 /\ m=1 /\ asm_returns_zero_or_one ins /\
                     !s v. LENGTH s.as_stack=hi /\ asm_step lo otp ins s=AsmOK v ==>
                       (EL 0 v.as_stack=0w \/ EL 0 v.as_stack=1w)))
      | _ => F) /\
     (if EL (pc x) p = AsmOp "JUMP" then Target x y
      else if EL (pc x) p = AsmOp "JUMPI" then pc y = pc x+1 \/ Target x y
      else pc y = pc x+1)) /\
   (!x s. x IN V /\ Shape x s ==>
      (?v. (asm_steps lo otp p 1 s = AsmRevert v \/
            asm_steps lo otp p 1 s = AsmFault v) /\ v.as_requests=req) \/
      (?y v. edge x y /\ asm_steps lo otp p 1 s = AsmOK v /\ Shape y v))) /\
  (!i. i=b \/ i=b+1 ==> asm_block_at p i (REPLICATE (b+2-i) (AsmOp "ISZERO"))) ==>
  ?next. !x. x IN V ==>
    next x IN V /\ keep (pc (next x)) /\ height (next x)=height x /\
    (if keep (pc x) then next x=x
     else pc (next x)=b+2 /\ nrank (next x)<nrank x) /\
    (!k nm org. 0<k /\ tag (next x) k=SOME(nm,org) ==> tag x k=SOME(nm,org)) /\
    (!k. 0<k /\ boolean (next x) k ==> boolean x k)
Proof
  ntac 12 gen_tac >>
  CONV_TAC (TOP_DEPTH_CONV (HO_REWR_CONV UNWIND_FORALL_THM2 ORELSEC BETA_CONV)) >>
  disch_then (CONJUNCTS_THEN2 (mk_asm "open") (mk_asm "suffix")) >>
  qabbrev_tac `R = \x z. z IN V /\ pc z=b+2 /\ height z=height x /\
    nrank z<nrank x /\
    (!k nm org. 0<k /\ tag z k=SOME(nm,org) ==> tag x k=SOME(nm,org)) /\
    (!k. 0<k /\ boolean z k ==> boolean x k)` >>
  qexists `\x. if pc x < b \/ b+2 <= pc x then x else @z. R x z` >>
  qx_gen_tac `x` >> disch_tac >>
  Cases_on `pc x < b \/ b+2 <= pc x` >- simp[] >>
  `?z. R x z` suffices_by
    (disch_then (mp_tac o SELECT_RULE) >> BETA_TAC >> simp[] >>
     qpat_abbrev_tac `w = @z. R x z` >>
     simp[Abbr `R`] >> strip_tac >> simp[]) >>
  `asm_block_at p (pc x) (REPLICATE (b+2-pc x) (AsmOp "ISZERO"))` by
    (asm "suffix" irule >> decide_tac) >>
  (let
     val expand = TOP_DEPTH_CONV (HO_REWR_CONV UNWIND_FORALL_THM2 ORELSEC BETA_CONV)
     val normalize = SIMP_RULE bool_ss [RAT_OF_NUM_LES, EMPTY_SUBSET, DIFF_EMPTY]
                     o CONV_RULE expand
     val live = merge_iszero_pending_root_contraction |> CONV_RULE expand |> SPEC_ALL |>
       Q.INST [`rank` |-> `\z:num#num. rat_of_num (nrank z)`] |>
       normalize |> ONCE_REWRITE_RULE [GSYM AND_IMP_INTRO] |>
       Q.INST [`v` |-> `x`, `d` |-> `b+2-pc x`]
   in asm "open" (fn source => mp_tac (MATCH_MP live (normalize source))) end) >>
  (impl_tac >- (simp[] >> decide_tac)) >>
  disch_then (qx_choose_then `z` strip_assume_tac) >>
  qexists `z` >> `pc z = b+2` by decide_tac >> simp[Abbr `R`] >> metis_tac[]
QED

(* E0537: the reverse-Skolem proof was stopped before the Live comparison.
  let
    val expand = REDEPTH_CONV (BETA_CONV ORELSEC REWR_CONV LET_THM)
    val normalize = SIMP_RULE bool_ss [RAT_OF_NUM_LES, EMPTY_SUBSET, DIFF_EMPTY]
                    o CONV_RULE expand
    val live = merge_iszero_pending_root_contraction |> SPEC_ALL |>
      Q.INST [`rank` |-> `\z:num#num. rat_of_num (nrank z)`] |>
      normalize |> ONCE_REWRITE_RULE [GSYM AND_IMP_INTRO]
  in
    rpt gen_tac >> CONV_TAC expand >>
    disch_then (CONJUNCTS_THEN2 (mk_asm "open") assume_tac) >>
    CONV_TAC (HO_REWR_CONV (GSYM SKOLEM_THM)) >>
    qx_gen_tac `x` >> simp[GSYM RIGHT_EXISTS_IMP_THM] >> disch_tac >>
    Cases_on `pc x < b \/ b+2 <= pc x`
    >- (qexists `x` >> simp[]) >>
    `asm_block_at p (pc x) (REPLICATE (b+2-pc x) (AsmOp "ISZERO"))` by
      (first_x_assum irule >> decide_tac) >>
    asm "open" (fn source =>
      mp_tac (MATCH_MP
        (Q.INST [`v` |-> `x`, `d` |-> `b+2-pc x`] live) (normalize source))) >>
    (impl_tac >- (simp[] >> decide_tac)) >>
    disch_then (qx_choose_then `z` strip_assume_tac) >>
    qexists `z` >> `pc z = b+2` by decide_tac >> simp[] >> metis_tac[]
  end
*)
