Theory staticAbortOptStackGuardedSource
Ancestors
  asmOptimizer asmSymSem asmWf asmSem asmIR symbolResolve alist
  stackOpSim stackOpAsmSim planExec list rich_list pred_set arithmetic words

Theorem guarded_encoded_swap[local]:
  !name. asm_swap_op (AsmOp name) /\ IS_SOME (evm_opcode_byte name) ==>
    ?n. ALOOKUP swap_table name = SOME n /\ 0 < n /\ n <= 16 /\
        name = swap_name n
Proof
  `EVERY (\(name,b). asm_swap_op (AsmOp name) ==>
      IS_SOME (ALOOKUP swap_table name) /\
      0 < THE (ALOOKUP swap_table name) /\ THE (ALOOKUP swap_table name) <= 16 /\
      name = swap_name (THE (ALOOKUP swap_table name))) evm_opcode_table`
    by EVAL_TAC >>
  rpt gen_tac >> Cases_on `evm_opcode_byte name` >> simp[] >> strip_tac >>
  fs[evm_opcode_byte_def, EVERY_MEM] >>
  drule ALOOKUP_MEM >> disch_then (fn th => first_x_assum (mp_tac o C MATCH_MP th)) >>
  simp[] >> Cases_on `ALOOKUP swap_table name` >> simp[]
QED

Theorem guarded_encoded_comm[local]:
  !name. asm_commutative_op (AsmOp name) /\ IS_SOME (evm_opcode_byte name) ==>
    MEM name ["ADD";"MUL";"EQ";"AND";"OR";"XOR"]
Proof
  `EVERY (\(name,b). asm_commutative_op (AsmOp name) ==>
    MEM name ["ADD";"MUL";"EQ";"AND";"OR";"XOR"]) evm_opcode_table`
    by EVAL_TAC >>
  rpt gen_tac >> Cases_on `evm_opcode_byte name` >> simp[] >> strip_tac >>
  fs[evm_opcode_byte_def, EVERY_MEM] >>
  drule ALOOKUP_MEM >> disch_then (fn th => first_x_assum (mp_tac o C MATCH_MP th)) >>
  simp[]
QED

Theorem guarded_swap_dispatch[local]:
  !n lo op t. 0 < n /\ n <= 16 ==>
    asm_step lo op (AsmOp (swap_name n)) t = asm_swap n t
Proof
  rpt strip_tac >>
  `n < SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC 0))))))))))))))))` by decide_tac >>
  pop_assum mp_tac >>
  PURE_REWRITE_TAC[prim_recTheory.LESS_THM, prim_recTheory.NOT_LESS_0] >>
  strip_tac >> gvs[] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``asm_swap``])
QED

Theorem guarded_comm_dispatch[local]:
  !name. MEM name ["ADD";"MUL";"EQ";"AND";"OR";"XOR"] ==>
    ALOOKUP dup_table name = NONE /\ ALOOKUP swap_table name = NONE /\
    asm_op_arity name = 2 /\
    (asm_returns_zero_or_one (AsmOp name) <=> name = "EQ") /\
    ?f. (!lo op t. asm_step lo op (AsmOp name) t = asm_binop f t) /\
        (name = "EQ" ==> !a b. f a b = 0w \/ f a b = 1w)
Proof
  rpt gen_tac >> simp[] >> strip_tac >> gvs[] >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV [``asm_binop``]) >>
  FIRST [qexists `word_add` >> simp[] >> NO_TAC,
         qexists `word_mul` >> simp[] >> NO_TAC,
         qexists `word_and` >> simp[] >> NO_TAC,
         qexists `word_or` >> simp[] >> NO_TAC,
         qexists `word_xor` >> simp[] >> NO_TAC,
         qexists `\x y. b2w (x=y)` >> simp[] >> rpt gen_tac >>
         Cases_on `a=b` >> simp[]]
QED

Theorem guarded_fetch_swap[local]:
  0 < n /\ n <= 16 /\ t.as_pc < LENGTH p /\
  EL t.as_pc p = AsmOp (swap_name n) ==>
  asm_steps lo op p 1 t =
    if n < LENGTH t.as_stack then
      AsmOK (t with <|as_pc := t.as_pc+1;
        as_stack := LUPDATE (HD t.as_stack) n (LUPDATE (EL n t.as_stack) 0 t.as_stack)|>)
    else AsmError "swap: invalid"
Proof
  strip_tac >> drule_all guarded_swap_dispatch >> disch_then assume_tac >>
  rewrite_tac[numLib.num_CONV ``1:num``] >>
  Cases_on `n < LENGTH t.as_stack` >>
  simp[asm_steps_def, asm_swap_def, asm_next_def, asm_state_fupdcanon]
QED

Theorem guarded_swap_slot[local]:
  0 < n /\ n < LENGTH stk ==>
  EL k (LUPDATE (HD stk) n (LUPDATE (EL n stk) 0 stk)) =
  EL (if k=0 then n else if k=n then 0 else k) stk
Proof
  Cases_on `stk` >> Cases_on `k=0` >> Cases_on `k=n` >>
  simp[EL_LUPDATE, LENGTH_LUPDATE] >> rpt strip_tac >> gvs[]
QED

Theorem guarded_fetch_binop[local]:
  t.as_pc < LENGTH p /\ EL t.as_pc p = AsmOp name /\
  (!l o'. asm_step l o' (AsmOp name) t = asm_binop f t) ==>
  asm_steps lo op p 1 t = case t.as_stack of
    a::b::stk => AsmOK (t with <|as_pc := t.as_pc+1; as_stack := f a b::stk|>)
    | _ => AsmError "stack underflow"
Proof
  strip_tac >> rewrite_tac[numLib.num_CONV ``1:num``] >>
  Cases_on `t.as_stack` >- simp[asm_steps_def, asm_binop_def] >>
  rename1 `t.as_stack = a::stk` >> Cases_on `stk` >>
  simp[asm_steps_def, asm_binop_def, asm_next_def, asm_state_fupdcanon]
QED

Theorem guarded_binop_tail[local]:
  0 < k ==> EL k (w::stk) = EL (k+1) (a::b::stk)
Proof
  Cases_on `k` >> simp[DECIDE ``!n. SUC n + 1 = SUC (SUC n)``]
QED

(* Replaying a selected edge only needs its demanded slots.  The witness
   at y supplies the static requirement, which is independent of the stack. *)
Theorem guarded_shape_replay[local]:
  !LiveShape. LiveShape = (\i (t:asm_state).
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
  LiveShape x t /\ (need y ==> cc.cc_static) /\
  u.as_pc = pc y /\ LENGTH u.as_stack = height y /\
  u.as_call_ctx = t.as_call_ctx /\ u.as_requests = t.as_requests /\
  (!k l origin. tag y k = SOME(l,origin) ==> k < height y /\
     tag x (src k) = SOME(l,origin) /\ EL k u.as_stack = EL (src k) t.as_stack) /\
  (!k. boolean y k ==> k < height y /\
    (EL k u.as_stack = 0w \/ EL k u.as_stack = 1w \/
     (boolean x (src k) /\ EL k u.as_stack = EL (src k) t.as_stack))) ==>
  LiveShape y u
Proof
  simp[] >> strip_tac >> simp[] >> conj_tac
  >- (map_every qx_gen_tac [`k`,`lab`,`org`] >> disch_tac >>
      qpat_assum `!k l origin. tag y k = SOME(l,origin) ==> _`
        (qspecl_then [`k`,`lab`,`org`] (drule_then strip_assume_tac)) >>
      qpat_assum `!k l origin. tag x k = SOME(l,origin) ==> _`
        (qspecl_then [`src k`,`lab`,`org`] (drule_then mp_tac)) >> simp[]) >>
  qx_gen_tac `k` >> disch_tac >>
  qpat_assum `!k. boolean y k ==> _` (qspec_then `k` (drule_then strip_assume_tac)) >>
  simp[] >> qpat_assum `!k. boolean x k ==> _`
    (qspec_then `src k` (drule_then mp_tac)) >> simp[]
QED

Theorem guarded_two_visits[local]:
  !sh one V pc rank edge x y z (b:num) path.
  path = (\i:num. if i=0 then x else if i=1 then y else z) /\
  x IN V /\ y IN V /\ z IN V /\
  pc x = b /\ pc y = b+1 /\ pc z = b+2 /\
  edge x y /\ edge y z /\ (rank z:num) < rank y /\ rank y < rank x /\
  (!t. sh x t ==> ?u. one t = AsmOK u /\ sh y u) /\
  (!t. sh y t ==> ?u. one t = AsmOK u /\ sh z u) ==>
  path 0=x /\
  (!i. i<=2 ==> path i IN V /\ pc (path i)=b+i) /\
  (!i. i<2 ==> edge (path i) (path(SUC i)) /\ rank(path(SUC i)) < rank(path i)) /\
  (!t. sh x t ==> ?run. run 0=t /\ !i. i<2 ==>
      one (run i)=AsmOK(run(SUC i)) /\ sh (path(SUC i)) (run(SUC i)))
Proof
  rpt gen_tac >> disch_then (CONJUNCTS_THEN2 SUBST1_TAC strip_assume_tac) >>
  simp[NoAsms] >>
  conj_tac >- (rpt strip_tac >> `i=0 \/ i=1 \/ i=2` by decide_tac >> gvs[]) >>
  conj_tac >- (rpt strip_tac >> `i=0 \/ i=1` by decide_tac >> gvs[]) >>
  qx_gen_tac `t` >> disch_tac >>
  qpat_assum `!t. sh x t ==> _` (qspec_then `t` (drule_then (qx_choose_then `u` strip_assume_tac))) >>
  qpat_assum `!t. sh y t ==> _` (qspec_then `u` (drule_then (qx_choose_then `r` strip_assume_tac))) >>
  qexists `\i. if i=0 then t else if i=1 then u else r` >>
  simp[] >> rpt strip_tac >> `i=0 \/ i=1` by decide_tac >> gvs[]
QED

Theorem guarded_swap_name_tables[local]:
  0 < n /\ n <= 16 ==>
    ALOOKUP dup_table (swap_name n) = NONE /\
    swap_name n <> "JUMP" /\ swap_name n <> "JUMPI"
Proof
  strip_tac >>
  `n < SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC (SUC 0))))))))))))))))` by decide_tac >>
  pop_assum mp_tac >>
  PURE_REWRITE_TAC[prim_recTheory.LESS_THM, prim_recTheory.NOT_LESS_0] >>
  strip_tac >> gvs[] >> EVAL_TAC
QED

Theorem stack_guarded_source_demand_paths:
!p cc req V rank pc height need tag boolean edge v pre w tail a.
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
  !inherit. inherit = (
    \(src:num -> num option)
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
!LiveShape. LiveShape = Shape p cc req pc height need tag boolean ==>
!Step. Step = (\t. asm_steps (SND(compute_label_offsets p)) (build_offset_to_pc p) p 1 t) ==>
!Open. Open =
  (\p cc req (V:(num#num)->bool) X (rank:(num#num)->num) pc height need
    (tag:(num#num)->num->(string#num)option)
    (boolean:(num#num)->num->bool) edge.
  !LiveShape. LiveShape = Shape p cc req pc height need tag boolean ==>
  !target. target = (\x y.
    ?l origin off. tag x 0 = SOME(l,origin) /\
      FLOOKUP (SND(compute_label_offsets p)) l = SOME off /\
      off < dimword(:256) /\
      FLOOKUP (build_offset_to_pc p) off = SOME(pc y)) ==>
    FINITE V /\ X SUBSET V /\
    (!x. x IN V ==> ?t. LiveShape x t) /\
    (!x. x IN V DIFF X ==> pc x < LENGTH p) /\
    (!x y. edge x y ==>
       x IN V DIFF X /\ y IN V /\ rank y < rank x /\
       Flow p pc height tag boolean x y /\
       (if EL (pc x) p = AsmOp "JUMP" then target x y
        else if EL (pc x) p = AsmOp "JUMPI"
             then pc y = pc x+1 \/ target x y
        else pc y = pc x+1)) /\
    (!x t. x IN V DIFF X /\ LiveShape x t ==>
       (?u. (asm_steps (SND(compute_label_offsets p)) (build_offset_to_pc p)
                    p 1 t = AsmRevert u \/
              asm_steps (SND(compute_label_offsets p)) (build_offset_to_pc p)
                    p 1 t = AsmFault u) /\ u.as_requests=req) \/
       (?y u. edge x y /\
          asm_steps (SND(compute_label_offsets p)) (build_offset_to_pc p)
            p 1 t = AsmOK u /\ LiveShape y u))) ==>
!b. b = LENGTH pre ==>
!h. h = height v ==>
!Visit. Visit = (\path.
  path 0=v /\ (!i. i<=LENGTH w ==> path i IN V /\ pc(path i)=b+i) /\
  (!i. i<LENGTH w ==> edge (path i) (path(SUC i)) /\ rank(path(SUC i)) < rank(path i)) /\
  (!t. LiveShape v t ==> ?run. run 0=t /\ !i. i<LENGTH w ==>
      Step (run i)=AsmOK(run(SUC i)) /\ LiveShape (path(SUC i)) (run(SUC i)))) ==>
!Pull. Pull = (\x z k j.
  (!l org. tag z k=SOME(l,org) ==> k<height z /\ j<height x /\ tag x j=SOME(l,org)) /\
  (boolean z k ==> k<height z /\ j<height x /\ boolean x j)) ==>
asm_static_wf p /\ Open p cc req V {} rank pc height need tag boolean edge /\
v IN V /\ pc v=b ==>
 (asm_swap_op a /\ w=[a;a] /\ p=pre++w++tail ==>
    ?name n path. !z. z = path (LENGTH w) ==>
      a=AsmOp name /\ ALOOKUP swap_table name=SOME n /\ 0<n /\ n<=16 /\ n<h /\
      Visit path /\ height z=h /\ !k. Pull v z k k) /\
 (asm_commutative_op a /\ w=[AsmOp "SWAP1";a] /\ p=pre++w++tail ==>
    ?name path. !z. z = path (LENGTH w) ==>
      a=AsmOp name /\ MEM name ["ADD";"MUL";"EQ";"AND";"OR";"XOR"] /\
      2<=h /\ Visit path /\ height z+1=h /\ tag z 0=NONE /\
      (boolean z 0 ==> name="EQ") /\ !k. 0<k ==> Pull v z k (k+1))
Proof
  ntac 16 gen_tac >>
  map_every (fn q =>
    CONV_TAC (BINDER_CONV (LAND_CONV (REWR_CONV (GSYM markerTheory.Abbrev_def)))) >>
    qx_gen_tac q >> disch_tac) [`Shape`,`Flow`,`LiveShape`,`Step`,`Open`,`b`,`h`,`Visit`,`Pull`] >>
  strip_tac >>
  qpat_assum `Abbrev (LiveShape = _)` (fn shth =>
    qpat_assum `Abbrev (Step = _)` (fn stepth =>
      let
        val foldshape = GSYM (BETA_RULE (PURE_REWRITE_RULE[markerTheory.Abbrev_def, FUN_EQ_THM] shth))
        val foldstep = GSYM (BETA_RULE (PURE_REWRITE_RULE[markerTheory.Abbrev_def, FUN_EQ_THM] stepth))
      in
        qpat_assum `Abbrev (Open = _)` (fn openth =>
          qpat_x_assum `Open p cc req V {} rank pc height need tag boolean edge`
            (strip_assume_tac o SRULE[] o PURE_REWRITE_RULE[foldshape, foldstep] o
             CONV_RULE (TOP_DEPTH_CONV (HO_REWR_CONV UNWIND_FORALL_THM2)) o
             BETA_RULE o PURE_REWRITE_RULE[PURE_REWRITE_RULE[markerTheory.Abbrev_def] openth])) >>
        qpat_x_assum `Abbrev (Visit = _)` (assume_tac o PURE_REWRITE_RULE[foldshape, foldstep] o BETA_RULE)
      end)) >>
  `!x y. edge x y /\ EL (pc x) p <> AsmOp "JUMP" /\
          EL (pc x) p <> AsmOp "JUMPI" ==> pc y = pc x+1` by
    (rpt gen_tac >> strip_tac >>
     qpat_assum `EL (pc x) p <> AsmOp "JUMP"` (fn j =>
       qpat_assum `EL (pc x) p <> AsmOp "JUMPI"` (fn ji =>
         qpat_assum `!x y. edge x y ==> _`
           (qspecl_then [`x`,`y`] (drule_then
             (ACCEPT_TAC o REWRITE_RULE[j,ji] o List.last o CONJUNCTS)))))) >>
  pop_assum (mk_asm "fallthrough") >>
  `!x t. LiveShape x t ==> t.as_pc = pc x /\ LENGTH t.as_stack = height x /\
      (need x ==> cc.cc_static)` by
    (simp[Abbr `LiveShape`, Abbr `Shape`] >> rpt strip_tac >> gvs[]) >>
  `!x y t u src. LiveShape x t /\ (need y ==> cc.cc_static) /\
      u.as_pc = pc y /\ LENGTH u.as_stack = height y /\
      u.as_call_ctx = t.as_call_ctx /\ u.as_requests = t.as_requests /\
      (!k l origin. tag y k = SOME(l,origin) ==> k < height y /\
         tag x (src k) = SOME(l,origin) /\ EL k u.as_stack = EL (src k) t.as_stack) /\
      (!k. boolean y k ==> k < height y /\
         (EL k u.as_stack = 0w \/ EL k u.as_stack = 1w \/
          (boolean x (src k) /\ EL k u.as_stack = EL (src k) t.as_stack))) ==>
      LiveShape y u` by
    (rpt gen_tac >>
     qpat_assum `Abbrev (LiveShape = _)`
       (fn th => PURE_REWRITE_TAC[PURE_REWRITE_RULE[markerTheory.Abbrev_def] th]) >>
     qpat_assum `Abbrev (Shape = _)`
       (fn th => PURE_REWRITE_TAC[PURE_REWRITE_RULE[markerTheory.Abbrev_def] th]) >>
     BETA_TAC >>
     (* Helper-only LET normalization did not match the unnormalized goal. *)
     SIMP_TAC bool_ss [LET_THM] >>
     MATCH_ACCEPT_TAC (SIMP_RULE bool_ss [LET_THM] guarded_shape_replay)) >>
  pop_assum (mk_asm "replay") >>
  `!i name. i < LENGTH p /\ EL i p = AsmOp name ==> IS_SOME (evm_opcode_byte name)` by
    ((qpat_assum `asm_static_wf p` mp_tac >>
     Cases_on `compute_label_offsets p` >>
     simp[asm_static_wf_def, asm_encoding_wf_def] >> (gvs[asm_static_wf_def, asm_encoding_wf_def]))) >>
  `!x n. x IN V /\ 0 < n /\ n <= 16 /\ EL (pc x) p = AsmOp (swap_name n) ==>
     ?y. edge x y /\ y IN V /\ rank y < rank x /\ pc y=pc x+1 /\
       n < height x /\ height y=height x /\
       (!k. Pull x y k (if k=0 then n else if k=n then 0 else k)) /\
       (!t. LiveShape x t ==> ?u. Step t = AsmOK u /\ LiveShape y u)` by suspend "swap_hop" >>
  `!x name. x IN V /\ MEM name ["ADD";"MUL";"EQ";"AND";"OR";"XOR"] /\
       EL (pc x) p = AsmOp name ==>
     ?y. edge x y /\ y IN V /\ rank y < rank x /\ pc y=pc x+1 /\
       2 <= height x /\ height y+1=height x /\ tag y 0=NONE /\
       (boolean y 0 ==> name="EQ") /\ (!k. 0<k ==> Pull x y k (k+1)) /\
       (!t. LiveShape x t ==> ?u. Step t = AsmOK u /\ LiveShape y u)` by suspend "comm_hop" >>
  `!y z path. LENGTH w = 2 /\ path = (\i:num. if i=0 then v else if i=1 then y else z) /\
      y IN V /\ z IN V /\ pc y = b+1 /\ pc z = b+2 /\
      edge v y /\ edge y z /\ rank z < rank y /\ rank y < rank v /\
      (!t. LiveShape v t ==> ?u. Step t = AsmOK u /\ LiveShape y u) /\
      (!t. LiveShape y t ==> ?u. Step t = AsmOK u /\ LiveShape z u) ==>
      Visit path` by suspend "visit" >>
  pop_assum (mk_asm "visit") >>
  `!x y z i j k. Pull x y j k /\ Pull y z i j ==> Pull x z i k` by
    (simp[Abbr `Pull`] >> POP_ASSUM_LIST (K ALL_TAC) >> metis_tac[]) >>
  pop_assum (mk_asm "pull_trans") >>
  conj_tac >- suspend "pair" >> suspend "comm"
QED

Resume stack_guarded_source_demand_paths[swap_hop]:
  rpt gen_tac >> strip_tac >>
  `pc x < LENGTH p` by metis_tac[] >>
  `?s. LiveShape x s` by metis_tac[] >>
  `s.as_pc = pc x /\ LENGTH s.as_stack = height x` by metis_tac[] >>
  `!t. LiveShape x t ==> Step t = if n < height x then
     AsmOK (t with <|as_pc := pc x+1;
       as_stack := LUPDATE (HD t.as_stack) n (LUPDATE (EL n t.as_stack) 0 t.as_stack)|>)
     else AsmError "swap: invalid"` by
    (qx_gen_tac `t` >> strip_tac >>
     qpat_assum `!x t. LiveShape x t ==> _` (qspecl_then [`x`,`t`] strip_assume_tac) >>
     qpat_assum `Abbrev (Step = _)` (fn th =>
       PURE_REWRITE_TAC[PURE_REWRITE_RULE[markerTheory.Abbrev_def] th]) >> BETA_TAC >>
     mp_tac (Q.INST [`t` |-> `t`, `n` |-> `n`, `p` |-> `p`,
       `lo` |-> `SND (compute_label_offsets p)`, `op` |-> `build_offset_to_pc p`] guarded_fetch_swap) >> simp[]) >>
  pop_assum (mk_asm "swap_step") >>
  asm "swap_step" (qspec_then `s` (drule_then assume_tac)) >>
  `(?u. Step s = AsmRevert u \/ Step s = AsmFault u) \/
    (?y u. edge x y /\ Step s = AsmOK u /\ LiveShape y u)` by
     (qpat_assum `!x t. x IN V /\ LiveShape x t ==> _`
        (qspecl_then [`x`,`s`] (drule_all_then strip_assume_tac)) >> metis_tac[]) >>
  TRY (qpat_assum `Step s = AsmRevert _` (K (Cases_on `n < height x` >> gvs[])) >> NO_TAC) >>
  TRY (qpat_assum `Step s = AsmFault _` (K (Cases_on `n < height x` >> gvs[])) >> NO_TAC) >>
  `n < height x` by (spose_not_then assume_tac >> fs[]) >>
  rename1 `edge x y` >>
  `need y ==> cc.cc_static` by metis_tac[] >>
  drule_all guarded_swap_name_tables >> strip_tac >>
  `ALOOKUP swap_table (swap_name n) = SOME n` by simp[swap_table_lookup] >>
  qpat_assum `!x y. edge x y ==> _` (qspecl_then [`x`,`y`] (drule_then strip_assume_tac)) >>
  `height y=height x /\ !k. Pull x y k (if k=0 then n else if k=n then 0 else k)` by
    (qpat_x_assum `!x y. edge x y ==> _` kall_tac >>
     qpat_x_assum `Flow p pc height tag boolean x y` mp_tac >>
     simp[Abbr `Flow`, Abbr `Pull`, LET_THM] >>
     strip_tac >> simp[]) >>
  `pc y = pc x+1` by
    (asm "fallthrough" (qspecl_then [`x`,`y`] irule) >> simp[]) >>
  qexists `y` >> simp[] >>
  qx_gen_tac `t` >> strip_tac >>
  `t.as_pc = pc x /\ LENGTH t.as_stack = height x` by metis_tac[] >>
  asm "swap_step" (qspec_then `t` (drule_then assume_tac)) >> simp[] >>
  qmatch_goalsub_abbrev_tac `LiveShape y u'` >>
  qabbrev_tac `src = (\k. if k=0 then n else if k=n then 0 else k)` >>
  `!k. Pull x y k (src k)` by simp[Abbr `src`] >>
  `!k. EL k u'.as_stack = EL (src k) t.as_stack` by
    simp[Abbr `u'`, Abbr `src`, guarded_swap_slot] >>
  (* Expanding the goal and applying irule to the conjunctive replay
     conclusion did not match; use the theorem-local atomic rule. *)
  asm "replay" (qspecl_then [`x`,`y`,`t`,`u'`,`src`] MATCH_MP_TAC) >>
  simp[Abbr `u'`, LENGTH_LUPDATE] >>
  suspend "swap_replay"
QED

Resume stack_guarded_source_demand_paths[swap_replay]:
  qpat_assum `!k. Pull x y k (src k)` mp_tac >>
  simp[Abbr `Pull`] >> rpt strip_tac >> metis_tac[]
QED

Resume stack_guarded_source_demand_paths[comm_hop]:
  (* Select the edge with one live witness, then replay it uniformly. *)
  rpt gen_tac >> strip_tac >>
  `pc x < LENGTH p` by metis_tac[] >>
  `?s. LiveShape x s` by metis_tac[] >>
  drule guarded_comm_dispatch >> strip_tac >>
  `!t. LiveShape x t ==> Step t = case t.as_stack of
     a::d::stk => AsmOK (t with <|as_pc := pc x+1; as_stack := f a d::stk|>)
     | _ => AsmError "stack underflow"` by
    (qx_gen_tac `t` >> strip_tac >>
     qpat_assum `!x t. LiveShape x t ==> _` (qspecl_then [`x`,`t`] (drule_then strip_assume_tac)) >>
     qpat_assum `Abbrev (Step = _)` (fn th =>
       PURE_REWRITE_TAC[PURE_REWRITE_RULE[markerTheory.Abbrev_def] th]) >> BETA_TAC >>
     (* Use the fetch lemma backwards after aligning the fall-through PC. *)
     qpat_assum `t.as_pc = pc x` (SUBST1_TAC o SYM) >>
     irule guarded_fetch_binop >> metis_tac[]) >>
  pop_assum (mk_asm "bin_step") >>
  asm "bin_step" (qspec_then `s` (drule_then assume_tac)) >>
  `(?u. Step s = AsmRevert u \/ Step s = AsmFault u) \/
    (?y u. edge x y /\ Step s = AsmOK u /\ LiveShape y u)` by
     (qpat_assum `!x t. x IN V /\ LiveShape x t ==> _`
        (qspecl_then [`x`,`s`] (drule_all_then strip_assume_tac)) >> metis_tac[]) >>
  (* Full assumption simplification split the opcode class into six.
     Rewrite only the witness's step equation in the progress alternatives. *)
  qpat_x_assum `Step s = (case _ of [] => _ | _ => _)` mp_tac >>
  Cases_on `s.as_stack` >> simp[] >>
  rename1 `s.as_stack = av::sv` >> Cases_on `sv` >> simp[] >> strip_tac >>
  `LENGTH s.as_stack = height x /\ LENGTH u.as_stack = height y /\
    (need y ==> cc.cc_static)` by metis_tac[] >>
  `2 <= height x /\ height y+1=height x` by
    (qpat_assum `LENGTH s.as_stack = height x` mp_tac >>
     qpat_assum `LENGTH u.as_stack = height y` mp_tac >>
     qpat_assum `u = s with <|as_stack := _; as_pc := _|>` SUBST1_TAC >>
     qpat_assum `s.as_stack = av::_::_` SUBST1_TAC >>
     SIMP_TAC (srw_ss ()) [ADD1] >> decide_tac) >>
  `pc y = pc x+1` by
    (asm "fallthrough" (qspecl_then [`x`,`y`] irule) >> fs[]) >>
  qpat_assum `!x y. edge x y ==> _` (qspecl_then [`x`,`y`] (drule_then strip_assume_tac)) >>
  `height y + 2 - height x = 1` by decide_tac >>
  `tag y 0 = NONE /\ (boolean y 0 ==> name="EQ") /\
    !k. 0 < k ==> Pull x y k (k+1)` by
    ((* Keep the normalized slot clauses instead of simplifying the entire implication. *)
     qpat_assum `Abbrev (Flow = _)` (fn flow =>
       qpat_assum `EL (pc x) p = AsmOp name` (fn ins =>
       qpat_assum `ALOOKUP dup_table name = NONE` (fn dup =>
       qpat_assum `ALOOKUP swap_table name = NONE` (fn sw =>
       qpat_assum `asm_op_arity name = 2` (fn arity =>
       qpat_assum `height y + 2 - height x = 1` (fn count =>
       qpat_assum `asm_returns_zero_or_one (AsmOp name) <=> name = "EQ"` (fn eq =>
       qpat_x_assum `Flow p pc height tag boolean x y`
         (strip_assume_tac o SRULE[REWRITE_RULE[markerTheory.Abbrev_def] flow,
                                   LET_THM, ins, dup, sw, arity, count, eq])))))))) >>
     conj_tac >-
       (Cases_on `tag y 0` >> simp[] >> rename1 `tag y 0 = SOME pr` >>
        Cases_on `pr` >> rename1 `tag y 0 = SOME(l,org)` >>
        qpat_assum `!k l org. tag y k = SOME(l,org) ==> _`
          (qspecl_then [`0`,`l`,`org`] (drule_then (mp_tac o SRULE[]))) >> simp[]) >>
     conj_tac >-
       (disch_tac >> qpat_assum `!k. boolean y k ==> _`
          (qspec_then `0` (drule_then (mp_tac o SRULE[]))) >> simp[]) >>
     qx_gen_tac `k` >> strip_tac >>
     `k <> 0 /\ k - 1 + 2 = k + 1` by decide_tac >>
     simp[Abbr `Pull`] >>
     qpat_assum `k - 1 + 2 = k + 1` (fn slot =>
       conj_tac >-
         (map_every qx_gen_tac [`l`,`org`] >> disch_tac >>
          qpat_assum `!k l org. tag y k = SOME(l,org) ==> _`
            (qspecl_then [`k`,`l`,`org`]
               (drule_then (strip_assume_tac o PURE_REWRITE_RULE[slot]))) >> simp[]) >>
       disch_tac >> qpat_assum `k <> 0` (fn nz =>
         qpat_assum `!k. boolean y k ==> _`
           (qspec_then `k` (drule_then (strip_assume_tac o SRULE[nz,slot])))) >> simp[])) >>
  qexists `y` >> simp[] >>
  suspend "comm_replay"
QED

Resume stack_guarded_source_demand_paths[comm_replay]:
  qx_gen_tac `t0` >> strip_tac >>
  `LENGTH t0.as_stack = height x` by metis_tac[] >>
  `height x = SUC (SUC (height x - 2))` by decide_tac >>
  qpat_assum `LENGTH t0.as_stack = height x` (fn len =>
    qpat_assum `height x = SUC (SUC (height x - 2))` (fn hlen =>
      let val inv = iffLR (CONJUNCT1 (CONJUNCT2 LENGTH_EQ_NUM)) in
        strip_assume_tac (MATCH_MP inv (TRANS len hlen))
      end)) >>
  qpat_x_assum `LENGTH _ = SUC (height x - 2)`
    (strip_assume_tac o MATCH_MP (iffLR (CONJUNCT1 (CONJUNCT2 LENGTH_EQ_NUM)))) >>
  `?aa dd stk. t0.as_stack = aa::dd::stk` by metis_tac[] >>
  asm "bin_step" (qspec_then `t0` (drule_then assume_tac)) >> simp[] >>
  qmatch_goalsub_abbrev_tac `LiveShape y u'` >>
  `LENGTH u'.as_stack = height y` by
    (qpat_assum `t0.as_stack = aa::dd::stk` (fn stack =>
       qpat_assum `LENGTH t0.as_stack = height x`
         (assume_tac o SRULE[stack, ADD1])) >>
     simp[Abbr `u'`, ADD1] >> decide_tac) >>
  `!k. 0<k ==> EL k u'.as_stack = EL (k+1) t0.as_stack` by
    simp[Abbr `u'`, guarded_binop_tail] >>
  asm "replay" (qspecl_then [`x`,`y`,`t0`,`u'`,`\k. k+1`] MATCH_MP_TAC) >>
  simp[Abbr `u'`] >>
  conj_tac >-
    (map_every qx_gen_tac [`k`,`lab`,`org`] >> disch_tac >>
     `0 < k` by (Cases_on `k` >> fs[]) >>
     qpat_assum `!k. 0<k ==> Pull x y k (k+1)`
       (qspec_then `k` (drule_then (fn th =>
         qpat_assum `Abbrev (Pull = _)` (fn pull =>
           qspecl_then [`lab`,`org`] (drule_then strip_assume_tac)
             (CONJUNCT1 (SRULE[REWRITE_RULE[markerTheory.Abbrev_def] pull] th)))))) >>
     simp[guarded_binop_tail]) >>
  qx_gen_tac `k` >> disch_tac >> Cases_on `k=0` >-
    ((`0 < height y` by decide_tac >>
     `name = "EQ"` by fs[] >> simp[] >> (metis_tac[]))) >>
  `0 < k` by decide_tac >>
  qpat_assum `!k. 0<k ==> Pull x y k (k+1)`
    (qspec_then `k` (drule_then (fn th =>
      qpat_assum `Abbrev (Pull = _)` (fn pull =>
        drule_then strip_assume_tac
          (CONJUNCT2 (SRULE[REWRITE_RULE[markerTheory.Abbrev_def] pull] th)))))) >>
  simp[guarded_binop_tail]
QED

Resume stack_guarded_source_demand_paths[visit]:
  rpt gen_tac >> strip_tac >>
  qpat_assum `Abbrev (Visit = _)` (fn th =>
    PURE_REWRITE_TAC[REWRITE_RULE[markerTheory.Abbrev_def] th]) >> BETA_TAC >>
  qpat_assum `LENGTH w = 2` SUBST1_TAC >>
  MATCH_MP_TAC guarded_two_visits >> qexistsl [`y`,`z`] >> simp[]
QED

Resume stack_guarded_source_demand_paths[pair]:
  strip_tac >>
  `?name. a = AsmOp name` by (Cases_on `a` >> fs[asm_swap_op_def]) >>
  `EL b p = a /\ EL (b+1) p = a /\ b < LENGTH p` by
    simp[Abbr `b`, EL_APPEND_EQN] >>
  qpat_x_assum `p = pre ++ w ++ tail` kall_tac >>
  `IS_SOME (evm_opcode_byte name)` by
    (qpat_assum `!i name. i < LENGTH p /\ _ ==> _`
      (qspecl_then [`b`,`name`] MATCH_MP_TAC) >> simp[]) >>
  `?n. ALOOKUP swap_table name = SOME n /\ 0 < n /\ n <= 16 /\
       name = swap_name n` by (irule guarded_encoded_swap >> fs[]) >>
  qpat_assum `!x n. x IN V /\ 0<n /\ _ ==> _`
    (qspecl_then [`v`,`n`] mp_tac) >>
  impl_tac >- simp[] >> disch_then (qx_choose_then `y` strip_assume_tac) >>
  qpat_assum `!x n. x IN V /\ 0<n /\ _ ==> _`
    (qspecl_then [`y`,`n`] mp_tac) >>
  impl_tac >- simp[] >> disch_then (qx_choose_then `z` strip_assume_tac) >>
  `pc z = b+2` by decide_tac >>
  qabbrev_tac `path = (\i:num. if i=0 then v else if i=1 then y else z)` >>
  `Visit path` by
    (asm "visit" (qspecl_then [`y`,`z`,`path`] MATCH_MP_TAC) >>
     simp[Abbr `path`]) >>
  `path 2 = z` by simp[Abbr `path`] >>
  qexistsl [`name`,`n`,`path`] >> simp[Abbr `h`] >> qx_gen_tac `k` >>
  qabbrev_tac `src = (\i:num. if i=0 then n else if i=n then 0 else i)` >>
  `src (src k) = k` by
    (Cases_on `k=0` >- simp[Abbr `src`] >>
     Cases_on `k=n` >> simp[Abbr `src`]) >>
  (* Unfolding src when specializing the double SWAP hid the involution.
     Fold the two universal Pull clauses first, then select their slots. *)
  qpat_assum `Abbrev (src = _)` (fn th =>
    let val fold = GSYM (BETA_RULE (PURE_REWRITE_RULE
                         [markerTheory.Abbrev_def, FUN_EQ_THM] th)) in
      qpat_x_assum `!i. Pull v y i _` (assume_tac o PURE_REWRITE_RULE[fold]) >>
      qpat_x_assum `!i. Pull y z i _` (assume_tac o PURE_REWRITE_RULE[fold])
    end) >>
  asm "pull_trans" MATCH_MP_TAC >> qexistsl [`y`,`src k`] >> conj_tac >-
    (qpat_assum `src (src k) = k` (fn inv =>
       qpat_assum `!i. Pull v y i (src i)`
         (qspec_then `src k` (ACCEPT_TAC o PURE_REWRITE_RULE[inv])))) >>
  qpat_assum `!i. Pull y z i (src i)` (qspec_then `k` ACCEPT_TAC)
QED

Resume stack_guarded_source_demand_paths[comm]:
  strip_tac >>
  `?name. a = AsmOp name` by (Cases_on `a` >> fs[asm_commutative_op_def]) >>
  `swap_name 1 = "SWAP1"` by EVAL_TAC >>
  `EL b p = AsmOp "SWAP1" /\ EL (b+1) p = a /\ b+1 < LENGTH p` by
    simp[Abbr `b`, EL_APPEND_EQN] >>
  qpat_x_assum `p = pre ++ w ++ tail` kall_tac >>
  `IS_SOME (evm_opcode_byte name)` by
    (qpat_assum `!i name. i < LENGTH p /\ _ ==> _`
      (qspecl_then [`b+1`,`name`] MATCH_MP_TAC) >> simp[]) >>
  `MEM name ["ADD";"MUL";"EQ";"AND";"OR";"XOR"]` by
    (MATCH_MP_TAC (Q.SPEC `name` guarded_encoded_comm) >> fs[]) >>
  qpat_assum `!x n. x IN V /\ 0<n /\ _ ==> _`
    (qspecl_then [`v`,`1`] mp_tac) >>
  impl_tac >- simp[] >> disch_then (qx_choose_then `y` strip_assume_tac) >>
  qpat_assum `!x name. x IN V /\ MEM name _ /\ _ ==> _`
    (qspecl_then [`y`,`name`] mp_tac) >>
  impl_tac >- simp[] >> disch_then (qx_choose_then `z` strip_assume_tac) >>
  `pc z = b+2` by decide_tac >>
  qabbrev_tac `path = (\i:num. if i=0 then v else if i=1 then y else z)` >>
  `Visit path` by
    (asm "visit" (qspecl_then [`y`,`z`,`path`] MATCH_MP_TAC) >>
     simp[Abbr `path`]) >>
  `path 2 = z` by simp[Abbr `path`] >>
  qexistsl [`name`,`path`] >> simp[Abbr `h`] >>
  qx_gen_tac `k` >> disch_tac >>
  `k+1 <> 0 /\ k+1 <> 1` by decide_tac >>
  `Pull y z k (k+1)` by
    (qpat_assum `!i. 0<i ==> Pull y z i (i+1)` (qspec_then `k` MATCH_MP_TAC) >>
     simp[]) >>
  `Pull v y (k+1) (k+1)` by
    (qpat_assum `k+1 <> 0` (fn nz =>
       qpat_assum `k+1 <> 1` (fn no =>
         qpat_assum `!i. Pull v y i _`
           (qspec_then `k+1` (ACCEPT_TAC o SIMP_RULE bool_ss [nz,no]))))) >>
  asm "pull_trans" MATCH_MP_TAC >> qexistsl [`y`,`k+1`] >>
  conj_tac >> first_assum ACCEPT_TAC
QED

Finalise stack_guarded_source_demand_paths
