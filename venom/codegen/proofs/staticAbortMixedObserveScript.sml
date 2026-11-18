(* Observe an exceptional concrete run on the mixed certificate's own bytes. *)
Theory staticAbortMixedObserve
Ancestors
  staticAbortRequestRank staticAbortTrace staticAbortStraight asmDataEnv asmWf asmSymBridge
  asmSymSem asmSem asmIR stackOpSim symbolResolve
  pred_set finite_map alist list words arithmetic

Theorem observer_opcode_safe[local]:
  MEM name ["INVALID";"REVERT";"SSTORE";"TSTORE";"LOG0";"LOG1";"LOG2";
            "LOG3";"LOG4";"JUMP";"JUMPI"] \/
  IS_SOME (ALOOKUP dup_table name) \/ IS_SOME (ALOOKUP swap_table name) \/
  (?m. static_abort_straight name m) ==>
  IS_SOME (evm_opcode_byte name) /\
  ~MEM name ["CALL";"CALLCODE";"STATICCALL";"DELEGATECALL";
             "CREATE";"CREATE2";"SELFDESTRUCT"]
Proof
  strip_tac
  >- (fs[MEM] >> gvs[] >> EVAL_TAC)
  >- (fs[optionTheory.IS_SOME_EXISTS] >> drule ALOOKUP_MEM >>
      simp[dup_table_def, MEM] >> strip_tac >> gvs[] >> EVAL_TAC >> simp[])
  >- (fs[optionTheory.IS_SOME_EXISTS] >> drule ALOOKUP_MEM >>
      simp[swap_table_def, MEM] >> strip_tac >> gvs[] >> EVAL_TAC >> simp[]) >>
  metis_tac[static_abort_straight_known]
QED

Theorem observer_step_normal[local]:
  asm_steps lo otp p 1 a = AsmOK b /\ b.as_requests = a.as_requests /\
  static_abort_safe_at p a ==>
  static_abort_normal lo otp p 1 a b
Proof
  simp[static_abort_normal_def, static_abort_trace_def, asm_steps_def]
QED

Theorem mixed_certificate_exception:
  !orig s data req_bound q Shape.
  Shape = (\p cc req pc height need tag boolean i (t:asm_state).
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
  !target. target = (\p (pc:(num#num)->num) tag x y.
    ?l origin off. tag x 0 = SOME(l,origin) /\
      FLOOKUP (SND(compute_label_offsets p)) l = SOME off /\
      off < dimword(:256) /\ FLOOKUP (build_offset_to_pc p) off = SOME(pc y)) ==>
  !Flow. Flow = (\p pc height tag boolean (x:num#num) (y:num#num).
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
             !m. m = hj + a - hi ==>
             a <= hi /\ hj = m+(hi-a) /\
             ((name="JUMP" \/ name="JUMPI") ==> m=0) /\
             inherit (\k. if k<m then NONE else SOME(k-m+a)) (\k. NONE)
               (\k. k=0 /\ m=1 /\ asm_returns_zero_or_one ins /\
                 !t u. LENGTH t.as_stack=hi /\
                   asm_step (SND(compute_label_offsets p)) (build_offset_to_pc p)
                     ins t = AsmOK u ==>
                   (EL 0 u.as_stack=0w \/ EL 0 u.as_stack=1w)))
    | _ => F) ==>
  !bytes. bytes = (\p. assemble p ++ data) ==>
  !env0. env0 = asm_data_env orig (bytes orig) ==>
  !start. start = (s with as_code := bytes q) ==>
  !run. run = asm_steps (SND (compute_label_offsets q)) (build_offset_to_pc q) q ==>
  (s.as_pc = 0 /\ s.as_code = bytes orig /\
  asm_static_wf orig /\ asm_static_wf q /\
  FILTER is_data_inst q = FILTER is_data_inst orig /\
  ((?n out.
      (run n start = AsmRevert out \/ run n start = AsmFault out) /\
      sym_terminal (sym_steps q env0 n (sym_init s)) /\
      out.as_requests <<= req_bound) \/
   (?j t u cc req (V:(num#num)->bool) e (rank:(num#num)->num)
       pc height need tag boolean edge.
      run j start = AsmOK t /\
      sym_steps q env0 j (sym_init s) = SymOK u /\
      asm_sym_rel q (asm_data_env q (bytes q)) t u /\
      t.as_pc = u.sym_base.as_pc /\ LENGTH t.as_stack = LENGTH u.sym_stack /\
      t.as_call_ctx = u.sym_base.as_call_ctx /\ t.as_requests = u.sym_base.as_requests /\
      t.as_call_ctx = cc /\ t.as_requests = req /\ req <<= req_bound /\
      ((!x. x IN V ==>
          (need x ==> cc.cc_static) /\
          (!k. boolean x k ==> k < height x /\ tag x k=NONE) /\
          (!k l origin. tag x k = SOME(l,origin) ==>
             k < height x /\ origin < LENGTH q /\
             (EL origin q = AsmPushLabel l \/ EL origin q = AsmPushOfst l 0) /\
             ?off dest. FLOOKUP (SND (compute_label_offsets q)) l = SOME off /\
                        off < dimword(:256) /\ FLOOKUP (build_offset_to_pc q) off = SOME dest)) /\
        (!x y. edge x y ==> x IN V /\ y IN V /\ rank y < rank x /\
           Flow q pc height tag boolean x y) /\
        (!x. x IN V ==>
          pc x < LENGTH q /\
          (!h. h = height x ==>
           !fall. fall = (\y. pc y = pc x+1) ==>
           !arm. arm = (\P n. ?y. edge x y /\ P y /\ height y = n) ==>
           !legal. legal = (\P n. !y. edge x y ==> P y /\ height y = n) ==>
           !next. next = (\n. arm fall n /\ legal fall n) ==>
           !untagged. untagged = (\a. !k. k<a ==> tag x k=NONE) ==>
           !stop. stop = (\a. a<=h /\ untagged a /\ !y. ~edge x y) ==>
           case EL (pc x) q of
             AsmLabel l => next h
           | AsmPush bs => next (h+1)
           | AsmPushLabel l => IS_SOME (FLOOKUP (SND (compute_label_offsets q)) l) /\ next (h+1)
           | AsmPushOfst l d => IS_SOME (FLOOKUP (SND (compute_label_offsets q)) l) /\ next (h+1)
           | AsmOp name =>
               if name="INVALID" then stop 0
               else if name="REVERT" then stop 2
               else if MEM name ["SSTORE";"TSTORE";"LOG0";"LOG1";"LOG2";"LOG3";"LOG4"]
                    then cc.cc_static /\ stop (asm_op_arity name)
               else
                 (case ALOOKUP dup_table name of
                    SOME n => n<h /\ next (h+1)
                  | NONE => case ALOOKUP swap_table name of
                      SOME n => 0<n /\ n<h /\ next h
                    | NONE =>
                        if name="JUMP" then
                           1<=h /\ arm (target q pc tag x) (h-1) /\ legal (target q pc tag x) (h-1)
                        else if name="JUMPI" then
                           2<=h /\ tag x 1=NONE /\ arm fall (h-2) /\ arm (target q pc tag x) (h-2) /\
                           legal (\y. fall y \/ target q pc tag x y) (h-2)
                        else
                           ?m. static_abort_straight name m /\ asm_op_arity name <= h /\
                               untagged (asm_op_arity name) /\ next (h-asm_op_arity name+m))
           | _ => F))) /\
      (!S. S = Shape q cc req pc height need tag boolean ==>
         FINITE V /\ {} SUBSET V /\
         (!x. x IN V ==> ?t. S x t) /\
         (!x. x IN V DIFF {} ==> pc x < LENGTH q) /\
         (!x y. edge x y ==>
            x IN V DIFF {} /\ y IN V /\ rank y < rank x /\
            Flow q pc height tag boolean x y /\
            (if EL (pc x) q = AsmOp "JUMP" then target q pc tag x y
             else if EL (pc x) q = AsmOp "JUMPI"
                  then pc y = pc x+1 \/ target q pc tag x y
             else pc y = pc x+1)) /\
         (!x t. x IN V DIFF {} /\ S x t ==>
            (?u. (run 1 t = AsmRevert u \/ run 1 t = AsmFault u) /\ u.as_requests=req) \/
            (?y u. edge x y /\ run 1 t = AsmOK u /\ S y u))) /\
      e IN V /\
      (!x. x IN V ==> ?n (path:num->num#num).
         path 0=e /\ path n=x /\ !k. k<n ==> edge (path k) (path(SUC k))) /\
      Shape q cc req pc height need tag boolean e t /\
      (!k l origin. tag e k = SOME(l,origin) ==>
         k < LENGTH u.sym_stack /\ EL k u.sym_stack = Lab l 0) /\
      (!k. boolean e k ==>
         k < LENGTH u.sym_stack /\ (EL k u.sym_stack = Val 0w \/ EL k u.sym_stack = Val 1w))))) ==>
  ?n ast.
    (run n start = AsmRevert ast \/ run n start = AsmFault ast) /\
    ast.as_requests <<= req_bound
Proof
  rpt gen_tac >> disch_then (mk_asm "shape_eq") >>
  ntac 2 (gen_tac >> disch_then kall_tac) >>
  ntac 4 (gen_tac >> disch_then SUBST1_TAC) >> BETA_TAC >> strip_tac
  >- (qexistsl [`n`, `out`] >> simp[])
  >- (qexistsl [`n`, `out`] >> simp[]) >>
  qpat_x_assum `t.as_call_ctx = cc` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `t.as_requests = req` (SUBST_ALL_TAC o SYM) >>
  qpat_x_assum `!S. S = Shape q _ _ _ _ _ _ _ ==> _`
    (mp_tac o Unwind.UNWIND_FORALL_RULE) >>
  simp[DIFF_EMPTY, NoAsms] >> strip_tac >>
  qabbrev_tac `shaped = Shape q t.as_call_ctx t.as_requests pc height need tag boolean` >>
  `!x a. shaped x a ==> a.as_pc = pc x /\ a.as_requests = t.as_requests` by
    asm "shape_eq" (fn th => simp[Abbr `shaped`, th]) >>
  `!x a. x IN V /\ shaped x a ==> static_abort_safe_at q a` by
    (rpt gen_tac >> strip_tac >>
     `a.as_pc = pc x` by
       (qpat_assum `!x a. shaped x a ==> _` (qspecl_then [`x`,`a`] mp_tac) >> simp[]) >>
     qpat_x_assum `!x. x IN V ==> pc x < LENGTH q /\ _` (qspec_then `x` mp_tac) >>
     (impl_tac >- simp[]) >>
     disch_then (CONJUNCTS_THEN2 assume_tac (mk_asm "row")) >>
     simp[static_abort_safe_at_def] >>
     Cases_on `EL (pc x) q` >> simp[] >>
     asm_x "row" (mp_tac o CONV_RULE
       (TOP_DEPTH_CONV (Unwind.UNWIND_FORALL_CONV ORELSEC BETA_CONV))) >> simp[] >>
     rename1 `EL (pc x) q = AsmOp name` >> strip_tac >>
     MATCH_MP_TAC (SIMP_RULE (srw_ss()) [MEM] observer_opcode_safe) >>
     spose_not_then strip_assume_tac >>
     gvs[optionTheory.IS_SOME_EQ_NOT_NONE, SF CONJ_ss]) >>
  qabbrev_tac `lo = SND (compute_label_offsets q)` >>
  qabbrev_tac `otp = build_offset_to_pc q` >>
  qabbrev_tac `cert = \r a. ?x. x IN V /\ rank x = r /\ shaped x a` >>
  `!r a. cert r a ==>
      (?n b. (asm_steps lo otp q n a = AsmRevert b \/
              asm_steps lo otp q n a = AsmFault b) /\ b.as_requests = a.as_requests) \/
      (?r' n b. r' < r /\ static_abort_normal lo otp q n a b /\ cert r' b)` by
    (rpt gen_tac >> simp[Abbr `cert`] >> strip_tac >>
     qpat_assum `!x a. x IN V /\ shaped x a ==> _ \/ _`
       (qspecl_then [`x`, `a`] mp_tac) >>
     (impl_tac >- simp[]) >> strip_tac
     >- (disj1_tac >> qexistsl [`1`, `u'`] >> simp[] >> metis_tac[])
     >- (disj1_tac >> qexistsl [`1`, `u'`] >> simp[] >> metis_tac[]) >>
     disj2_tac >> qexistsl [`rank y`, `1`, `u'`] >>
     `y IN V /\ rank y < rank x` by metis_tac[] >>
     simp[] >> conj_tac
     >- (irule observer_step_normal >> simp[] >> metis_tac[]) >>
     qexists `y` >> simp[]) >>
  drule ranked_request_silent_exception >>
  disch_then (qspecl_then [`rank e`, `t`] mp_tac) >>
  simp[Abbr `cert`] >> (impl_tac >- (qexists `e` >> simp[])) >>
  disch_then (qx_choose_then `n` (qx_choose_then `ast` strip_assume_tac)) >>
  qexistsl [`j + n`, `ast`] >>
  drule asm_steps_add_ok >>
  disch_then (qspec_then `n` SUBST1_TAC) >> simp[] >>
  qpat_x_assum `_ <<= req_bound` mp_tac >> simp[]
QED
