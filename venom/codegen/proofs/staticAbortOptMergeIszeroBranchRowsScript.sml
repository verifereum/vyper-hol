Theory staticAbortOptMergeIszeroBranchRows
Ancestors
  staticAbortOptMergeIszeroBranchTable staticAbortOptMergeIszeroBranchPackage
  asmSplice asmSymPc asmDataEnv asmOptimizer staticAbortStraight
  finite_map words alist list pred_set arithmetic rat

(* Normalize naming equalities without unfolding either certificate. *)
val branch_norm = TOP_DEPTH_CONV (FIRST_CONV
  [HO_REWR_CONV UNWIND_FORALL_THM2, BETA_CONV, REWR_CONV DIFF_EMPTY,
   REWR_CONV ratTheory.RAT_OF_NUM_LES]);

(* The table expresses required arms and outgoing heights separately.
   The package expresses them together, with each outgoing PC checked. *)
Triviality branch_dispatch_views:
  !p pc height (tag:(num#num)->num->(string#num)option) edge (cc:call_context) (x:num#num).
  !lo. lo = SND (compute_label_offsets p) ==>
  !ins. ins = EL (pc x) p ==>
  !h. h = height x ==>
  !fall. fall = (\y. pc y = pc x+1) ==>
  !target. target = (\y. ?l origin off. tag x 0=SOME(l,origin) /\
    FLOOKUP lo l=SOME off /\ off<dimword(:256) /\
    FLOOKUP (build_offset_to_pc p) off=SOME (pc y)) ==>
  !arm. arm = (\P n. ?y. edge x y /\ P y /\ height y=n) ==>
  !legal. legal = (\P n. !y. edge x y ==> P y /\ height y=n) ==>
  !next. next = (\n. arm fall n /\ legal fall n) ==>
  !out. out = (\n. !y. edge x y ==> height y=n) ==>
  !consumed. consumed = (\n. !k. k<n ==> tag x k=NONE) ==>
  !terminal. terminal = (!y. ~edge x y) ==>
  !stop. stop = (\n. n<=h /\ consumed n /\ terminal) ==>
  (!y. edge x y ==>
    if ins=AsmOp "JUMP" then target y
    else if ins=AsmOp "JUMPI" then fall y \/ target y else fall y) ==>
  ((case ins of
      AsmLabel l => next h
    | AsmPush bs => next (h+1)
    | AsmPushLabel l => IS_SOME (FLOOKUP lo l) /\ next (h+1)
    | AsmPushOfst l d => IS_SOME (FLOOKUP lo l) /\ next (h+1)
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
                    if name="JUMP" then 1<=h /\ arm target (h-1) /\ legal target (h-1)
                    else if name="JUMPI" then 2<=h /\ tag x 1=NONE /\
                         arm fall (h-2) /\ arm target (h-2) /\ legal (\y. fall y \/ target y) (h-2)
                    else ?m. static_abort_straight name m /\ asm_op_arity name<=h /\
                             consumed (asm_op_arity name) /\ next (h-asm_op_arity name+m))
    | _ => F) <=>
   (case ins of
      AsmLabel l => (?y. edge x y /\ fall y) /\ out h
    | AsmPush bs => (?y. edge x y /\ fall y) /\ out (h+1)
    | AsmPushLabel l => IS_SOME (FLOOKUP lo l) /\ (?y. edge x y /\ fall y) /\ out (h+1)
    | AsmPushOfst l d => IS_SOME (FLOOKUP lo l) /\ (?y. edge x y /\ fall y) /\ out (h+1)
    | AsmOp name =>
        (name="INVALID" /\ terminal) \/
        (name="REVERT" /\ 2<=h /\ consumed 2 /\ terminal) \/
        (MEM name ["SSTORE";"TSTORE";"LOG0";"LOG1";"LOG2";"LOG3";"LOG4"] /\
          cc.cc_static /\ asm_op_arity name<=h /\ consumed (asm_op_arity name) /\ terminal) \/
        (case ALOOKUP dup_table name of
           SOME n => n<h /\ (?y. edge x y /\ fall y) /\ out (h+1)
         | NONE => case ALOOKUP swap_table name of
             SOME n => 0<n /\ n<h /\ (?y. edge x y /\ fall y) /\ out h
           | NONE =>
               (name="JUMP" /\ 1<=h /\ (?y. edge x y /\ target y) /\ out (h-1)) \/
               (name="JUMPI" /\ 2<=h /\ tag x 1=NONE /\
                 (?y. edge x y /\ fall y) /\ (?y. edge x y /\ target y) /\ out (h-2)) \/
               (?m. static_abort_straight name m /\ asm_op_arity name<=h /\
                    consumed (asm_op_arity name) /\ (?y. edge x y /\ fall y) /\ out (h-asm_op_arity name+m)))
     | _ => F))
Proof
  ntac 7 gen_tac >> CONV_TAC branch_norm >> simp[Excl "MEM"] >>
  Cases_on `EL (pc x) p` >> simp[Excl "MEM"] >>
  TRY (metis_tac[] >> NO_TAC) >>
  rename1 `EL (pc x) p = AsmOp name` >>
  map_every (fn opn => Cases_on [QUOTE "name = ", QUOTE opn] >-
    (simp[asmSemTheory.dup_table_def,asmSemTheory.swap_table_def,static_abort_straight_def] >> metis_tac[]))
    ["\"INVALID\"","\"REVERT\"","\"SSTORE\"","\"TSTORE\"","\"LOG0\"","\"LOG1\"",
     "\"LOG2\"","\"LOG3\"","\"LOG4\"","\"JUMP\"","\"JUMPI\""] >>
  Cases_on `ALOOKUP dup_table name` >> simp[] >>
  TRY (metis_tac[] >> NO_TAC) >>
  Cases_on `ALOOKUP swap_table name` >> simp[] >> metis_tac[]
QED

fun branch_dispatch_tac prog cc =
  mp_tac (CONV_RULE branch_norm
    (Q.SPECL [prog,`pc`,`height`,`tag`,`edge`,cc,`x`] branch_dispatch_views));

(* Use the same tuple for the table and for the reachable package. *)
Theorem merge_iszero_jumpi_cut_rows:
  !Shape. Shape = (\p cc req pc height need tag boolean i (t:asm_state).
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
    !inherit. inherit = (\(src:num -> num option)
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
  !Target. Target = (\p pc tag (x:num#num) (y:num#num).
    ?l origin off. tag x 0 = SOME(l,origin) /\
      FLOOKUP (SND(compute_label_offsets p)) l = SOME off /\
      off < dimword(:256) /\
      FLOOKUP (build_offset_to_pc p) off = SOME(pc y)) ==>
  !Control. Control = (\p pc tag x y.
    if EL (pc x) p = AsmOp "JUMP" then Target p pc tag x y
    else if EL (pc x) p = AsmOp "JUMPI"
         then pc y = pc x+1 \/ Target p pc tag x y
    else pc y = pc x+1) ==>
  !Open. Open = (\p cc req (V:(num#num)->bool) X rank pc height need
        (tag:(num#num)->num->(string#num)option)
        (boolean:(num#num)->num->bool) edge.
    !S. S = Shape p cc req pc height need tag boolean ==>
      FINITE V /\ X SUBSET V /\
      (!x. x IN V ==> ?t. S x t) /\
      (!x. x IN V DIFF X ==> pc x < LENGTH p) /\
      (!x y. edge x y ==>
         x IN V DIFF X /\ y IN V /\ rank y < rank x /\
         Flow p pc height tag boolean x y /\ Control p pc tag x y) /\
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
  !Slots. Slots = (\p cc height need tag boolean (x:num#num).
    (need x ==> cc.cc_static) /\
    (!k. boolean x k ==> k < height x /\ tag x k=NONE) /\
    (!k l origin. tag x k = SOME(l,origin) ==>
       k < height x /\ origin < LENGTH p /\
       (EL origin p = AsmPushLabel l \/ EL origin p = AsmPushOfst l 0) /\
       ?off dest. FLOOKUP (SND(compute_label_offsets p)) l = SOME off /\
         off < dimword(:256) /\ FLOOKUP (build_offset_to_pc p) off = SOME dest)) ==>
  !Rows. Rows = (\p cc (V:(num#num)->bool) X (rank:num#num->num) pc height need tag boolean edge.
    !lo. lo = SND(compute_label_offsets p) ==>
    (!x. x IN V ==> Slots p cc height need tag boolean x) /\
    (!x y. edge x y ==>
       x IN V DIFF X /\ y IN V /\ rank y < rank x /\
       Flow p pc height tag boolean x y) /\
    (!x. x IN V DIFF X ==>
       pc x < LENGTH p /\
       !h. h = height x ==>
       !fall. fall = (\y. pc y = pc x + 1) ==>
       !arm. arm = (\P n. ?y. edge x y /\ P y /\ height y = n) ==>
       !legal. legal = (\P n. !y. edge x y ==> P y /\ height y = n) ==>
       !next. next = (\n. arm fall n /\ legal fall n) ==>
       !untagged. untagged = (\a. !k. k<a ==> tag x k=NONE) ==>
       !stop. stop = (\a. a<=h /\ untagged a /\ !y. ~edge x y) ==>
       case EL (pc x) p of
         AsmLabel l => next h
       | AsmPush bs => next (h+1)
       | AsmPushLabel l => IS_SOME (FLOOKUP lo l) /\ next (h+1)
       | AsmPushOfst l d => IS_SOME (FLOOKUP lo l) /\ next (h+1)
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
                       if name="JUMP" then
                         1<=h /\ arm (Target p pc tag x) (h-1) /\
                         legal (Target p pc tag x) (h-1)
                       else if name="JUMPI" then
                         2<=h /\ tag x 1=NONE /\ arm fall (h-2) /\
                         arm (Target p pc tag x) (h-2) /\
                         legal (\y. fall y \/ Target p pc tag x y) (h-2)
                       else ?m. static_abort_straight name m /\ asm_op_arity name <= h /\
                                untagged (asm_op_arity name) /\ next (h-asm_op_arity name+m))
       | _ => F)) ==>
  !Root. Root = (\p ss a pc height need tag boolean e.
    Shape p a.as_call_ctx a.as_requests pc height need tag boolean e a /\
    (!k l origin. tag e k=SOME(l,origin) ==>
       k<LENGTH ss.sym_stack /\ EL k ss.sym_stack=Lab l 0) /\
    (!k. boolean e k ==> k<LENGTH ss.sym_stack /\
       (EL k ss.sym_stack=Val 0w \/ EL k ss.sym_stack=Val 1w))) ==>
  !Cert. Cert = (\p ss a. ?V e rank pc height need tag boolean edge.
    Rows p a.as_call_ctx V {} rank pc height need tag boolean edge /\
    Open p a.as_call_ctx a.as_requests V {} rank pc height need tag boolean edge /\
    e IN V /\ (!x. x IN V ==> Reach edge e x) /\
    Root p ss a pc height need tag boolean e) ==>
  !b. b = LENGTH pre ==>
  !c. c = ss.sym_base.as_pc ==>
  p = pre ++ [AsmOp "ISZERO";AsmOp "ISZERO";AsmPushLabel l;AsmOp "JUMPI"] ++ tail /\
  q = pre ++ [AsmPushLabel l;AsmOp "JUMPI"] ++ tail /\
  asm_static_wf p /\ asm_sym_rel p (asm_data_env p (assemble p ++ data)) a ss /\ Cert p ss a /\
  asm_sym_rel q (asm_data_env q (assemble q ++ data)) t u /\
  t.as_call_ctx=a.as_call_ctx /\ t.as_requests=a.as_requests /\
  (if b<c /\ c<b+4 then
     u.sym_base.as_pc=b /\ ?w stk. u.sym_stack=Val w::stk /\
       ss.sym_stack=(if c-b=3 then [Lab l 0] else []) ++
         (Val (FUNPOW (\w:bytes32. (b2w (w=0w):bytes32)) (MIN (c-b) 2) w)::stk)
   else u=sym_with_pc (splice_pc b 4 2 c) ss) ==>
  Cert q u t
Proof
  map_every (fn name => qx_gen_tac name >> disch_then (assume_tac o
    CONV_RULE (RAND_CONV branch_norm THENC REWR_CONV (GSYM markerTheory.Abbrev_def))))
    [`Shape`,`Flow`,`Target`,`Control`,`Open`,`Reach`,`Slots`,`Rows`,`Root`,`Cert`] >>
  CONV_TAC branch_norm >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  mp_tac (CONV_RULE branch_norm merge_iszero_jumpi_cut_table) >>
  (impl_tac >- suspend "table_input") >>
  suspend "package"
QED

Resume merge_iszero_jumpi_cut_rows[table_input]:
  rpt (FIRST [first_assum ACCEPT_TAC, conj_tac]) >>
  qpat_x_assum `Cert p ss a` mp_tac >>
  map_every qunabbrev_tac
    [`Cert`,`Rows`,`Root`,`Open`,`Reach`,`Control`,`Slots`,`Flow`,`Target`,`Shape`] >>
  CONV_TAC branch_norm >>
  disch_then (REPEAT_TCL CHOOSE_THEN (map_every assume_tac o CONJUNCTS)) >>
  qexistsl [`V`,`e`,`rank`,`pc`,`height`,`need`,`tag`,`boolean`,`edge`] >>
  rpt (FIRST [first_assum ACCEPT_TAC, conj_tac]) >>
  qx_gen_tac `x` >> disch_tac >>
  qpat_assum `!x. x IN V ==> pc x < LENGTH p /\ _`
    (qspec_then `x` (drule_then (map_every assume_tac o CONJUNCTS))) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  branch_dispatch_tac `p` `a.as_call_ctx` >>
  (impl_tac >- suspend "source_control") >>
  disch_then (irule o iffLR) >> first_assum ACCEPT_TAC
QED

Resume merge_iszero_jumpi_cut_rows[package]:
  disch_then (REPEAT_TCL CHOOSE_THEN (map_every assume_tac o CONJUNCTS)) >>
  qabbrev_tac `liveSet = {x | x IN V /\ Reach edge e x}` >>
  qabbrev_tac `liveEdge = \x y. x IN liveSet /\ edge x y` >>
  qpat_x_assum `Cert p ss a` kall_tac >>
  map_every qunabbrev_tac
    [`Cert`,`Rows`,`Root`,`Open`,`Reach`,`Control`,`Slots`,`Flow`,`Target`,`Shape`] >>
  CONV_TAC branch_norm >>
  qpat_assum `q:asm_inst list = _` (pure_rewrite_tac o single o GSYM) >>
  mp_tac (CONV_RULE branch_norm
    (Q.SPECL [`q`,`u`,`t`,`V`,`e`,`\x. rat$rat_of_num (rank x)`,
               `pc`,`height`,`need`,`tag`,`boolean`,`edge`] pending_rows_rooted_package)) >>
  (impl_tac >- suspend "package_input") >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qexistsl [`liveSet`,`e`,`rank`,`pc`,`height`,`need`,`tag`,`boolean`,`liveEdge`] >>
  map_every qunabbrev_tac [`liveEdge`,`liveSet`] >> CONV_TAC branch_norm >>
  rpt (FIRST [first_assum ACCEPT_TAC, conj_tac])
QED

Resume merge_iszero_jumpi_cut_rows[package_input]:
  rpt (FIRST [first_assum ACCEPT_TAC, conj_tac])
  >- (map_every qx_gen_tac [`x`,`y`] >> disch_tac >>
      qpat_assum `!x y. edge x y ==> x IN V /\ y IN V /\ rank y < rank x /\ _`
        (qspecl_then [`x`,`y`]
          (drule_then (fn th => ACCEPT_TAC (LIST_CONJ (List.take (CONJUNCTS th,4)))))))
  >- (qx_gen_tac `x` >> disch_tac >>
      qpat_assum `!x. x IN V ==> pc x < LENGTH q /\ _`
        (qspec_then `x` (drule_then (map_every assume_tac o CONJUNCTS))) >>
      conj_tac >- first_assum ACCEPT_TAC >>
      branch_dispatch_tac `q` `t.as_call_ctx` >>
      (impl_tac >- (qx_gen_tac `y` >> disch_tac >>
        first_assum (drule_then (ACCEPT_TAC o List.last o CONJUNCTS)))) >>
      disch_then (irule o iffRL) >> first_assum ACCEPT_TAC) >>
  map_every qx_gen_tac [`x`,`y`] >> disch_tac >>
  qpat_assum `!x y. edge x y ==> x IN V /\ y IN V /\ rank y < rank x /\ _`
    (qspecl_then [`x`,`y`] (drule_then (ACCEPT_TAC o CONJUNCT2 o CONJUNCT2 o CONJUNCT2)))
QED

Resume merge_iszero_jumpi_cut_rows[source_control]:
  qx_gen_tac `y` >> disch_tac >>
  first_assum (drule_then (ACCEPT_TAC o List.last o CONJUNCTS))
QED

Finalise merge_iszero_jumpi_cut_rows
