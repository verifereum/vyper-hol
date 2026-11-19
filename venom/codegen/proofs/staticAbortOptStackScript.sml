Theory staticAbortOptStack
Ancestors rat[qualified,ignore_grammar]
  asmOptPeephole asmDataEnv codegenSymRel asmSymBridge asmSplice asmSymSem asmSem
  asmIR asmOptimizer staticAbortStraight list words finite_map alist pred_set option pair
  staticAbortProtectedActualPrefix staticAbortOptStackLayout
  staticAbortOptStackPorts staticAbortOptStackRetained staticAbortOptStackTable
  staticAbortOptStackStopped staticAbortOptStackShuffleCut staticAbortOptStackCommCut
  staticAbortOptStackWalk staticAbortOptMergeIszeroBranchPackage

Theorem stack_terminal_steps_lockstep[local]:
  !n cs ss. asm_static_wf p /\ asm_sym_rel p env cs ss /\
    sym_terminal (sym_steps p env n ss) ==>
    sym_result_rel (sym_steps p env n ss)
      (asm_result_sym (asm_steps (SND (compute_label_offsets p))
        (build_offset_to_pc p) p n cs))
Proof
  Induct >- simp[sym_steps_def, sym_terminal_def] >>
  rpt gen_tac >> strip_tac >>
  drule asm_sym_rel_pc >> strip_tac >>
  reverse (Cases_on `cs.as_pc < LENGTH p`)
  >- gvs[sym_steps_def, sym_terminal_def] >>
  drule_all asm_sym_step >>
  Cases_on `sym_step p env (EL cs.as_pc p) ss` >>
  gvs[sym_steps_def, sym_terminal_def, asm_sym_step_rel_def] >>
  rpt strip_tac >>
  gvs[asm_steps_def, asm_result_sym_def, sym_result_rel_def] >>
  metis_tac[]
QED

Theorem stack_terminal_certificate_transfer[local]:
  !orig s data req_bound p q ch n out.
    !bytes. bytes = (\p. assemble p ++ data) ==>
    !env0. env0 = asm_data_env orig (bytes orig) ==>
    !run. run = (\p j. asm_steps (SND (compute_label_offsets p))
      (build_offset_to_pc p) p j (s with as_code := bytes p)) ==>
    s.as_pc = 0 /\ s.as_code = bytes orig /\
    asm_static_wf orig /\ asm_static_wf p /\
    FILTER is_data_inst p = FILTER is_data_inst orig /\
    stack_peephole_opts p = SOME(q,ch) /\
    (run p n = AsmRevert out \/ run p n = AsmFault out) /\
    sym_terminal (sym_steps p env0 n (sym_init s)) /\
    out.as_requests <<= req_bound ==>
    asm_static_wf q /\ FILTER is_data_inst q = FILTER is_data_inst orig /\
    ?j a. (run q j = AsmRevert a \/ run q j = AsmFault a) /\
          sym_terminal (sym_steps q env0 j (sym_init s)) /\
          a.as_requests <<= req_bound
Proof
  ntac 9 gen_tac >> simp[UNWIND_FORALL_THM2] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  qabbrev_tac `env = asm_data_env orig (assemble orig ++ data)` >>
  qabbrev_tac `sp = s with as_code := assemble p ++ data` >>
  qabbrev_tac `sq = s with as_code := assemble q ++ data` >>
  drule stack_peephole_opts_refines >> simp[asm_refines_def] >> strip_tac >>
  `!v. asm_static_wf v /\ FILTER is_data_inst v = FILTER is_data_inst orig ==>
       asm_sym_rel v env (s with as_code := assemble v ++ data) (sym_init s)` by
    (gen_tac >> strip_tac >>
     `asm_data_env orig (assemble orig ++ data) =
        asm_data_env v (assemble v ++ data)` by (irule asm_data_env_agree >> simp[]) >>
     `sym_init s = sym_init (s with as_code := assemble v ++ data)` by simp[sym_init_def] >>
     pop_assum SUBST1_TAC >> simp[Abbr `env`] >>
     irule asm_sym_rel_init >> simp[asm_data_env_ok_asm_data_env]) >>
  `asm_sym_rel p env sp (sym_init s) /\ asm_sym_rel q env sq (sym_init s)` by
    simp[Abbr `sp`, Abbr `sq`] >>
  drule_then (qspec_then `0` assume_tac) sym_steps_terminal_run >>
  `sym_run p env n (sym_init s) = sym_steps p env n (sym_init s)` by fs[] >>
  qpat_x_assum `!env s fuel. _` (qspecl_then [`env`,`s`,`n`] mp_tac) >>
  simp[] >> disch_then (qx_choose_then `j` assume_tac) >>
  `sym_terminal (sym_run q env j (sym_init s))` by
    (Cases_on `sym_steps p env n (sym_init s)` >>
     Cases_on `sym_run q env j (sym_init s)` >>
     gvs[sym_terminal_def, sym_result_rel_def]) >>
  `sym_run q env j (sym_init s) = sym_steps q env j (sym_init s)` by
    (drule_then (qspec_then `j` mp_tac) sym_run_terminal_steps >> simp[]) >>
  `sym_terminal (sym_steps q env j (sym_init s))` by fs[] >>
  `sym_result_rel (sym_steps p env n (sym_init s))
     (asm_result_sym (asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p n sp))` by
    (irule stack_terminal_steps_lockstep >> simp[]) >>
  `sym_result_rel (sym_steps q env j (sym_init s))
     (asm_result_sym (asm_steps (SND (compute_label_offsets q)) (build_offset_to_pc q) q j sq))` by
    (irule stack_terminal_steps_lockstep >> simp[]) >>
  qexists_tac `j` >>
  qabbrev_tac `r = asm_steps (SND (compute_label_offsets q)) (build_offset_to_pc q) q j sq` >>
  qpat_x_assum `_ = AsmRevert out \/ _ = AsmFault out` strip_assume_tac >>
  Cases_on `r` >> Cases_on `sym_steps p env n (sym_init s)` >>
  Cases_on `sym_steps q env j (sym_init s)` >>
  gvs[sym_terminal_def, asm_result_sym_def, sym_result_rel_def,
      sym_obs_def, sym_init_def, asm_state_component_equality] >>
  metis_tac[]
QED

(* Shared lexical certificate interfaces; no logical constants are added. *)
val Canon = ``\p l dest. ?off.
  FLOOKUP (SND(compute_label_offsets p)) l = SOME off /\
  off < dimword(:256) /\ FLOOKUP (build_offset_to_pc p) off = SOME dest``;

val Shape = ``\p cc req pc height need tag boolean (i:num#num) (t:asm_state).
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
     (EL k t.as_stack = 0w \/ EL k t.as_stack = 1w))``;

val target = ``\p (pc:(num#num)->num) (tag:(num#num)->num->(string#num)option) x y.
  ?l origin off. tag x 0 = SOME(l,origin) /\
    FLOOKUP (SND(compute_label_offsets p)) l = SOME off /\
    off < dimword(:256) /\ FLOOKUP (build_offset_to_pc p) off = SOME(pc y)``;

val Flow = ``\p pc height tag boolean (x:num#num) (y:num#num).
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
  | _ => F``;

val Slots = ``\p cc h need (g:num->(string#num)option) (B:num->bool).
  (need ==> cc.cc_static) /\
  (!k. B k ==> k < h /\ g k = NONE) /\
  (!k l origin. g k = SOME(l,origin) ==>
     k < h /\ origin < LENGTH p /\
     (EL origin p = AsmPushLabel l \/ EL origin p = AsmPushOfst l 0) /\
     ?off dest. FLOOKUP (SND(compute_label_offsets p)) l = SOME off /\
       off < dimword(:256) /\ FLOOKUP (build_offset_to_pc p) off = SOME dest)``;

val Dispatch = ``\p cc (pc:(num#num)->num) height (tag:(num#num)->num->(string#num)option) x S.
  pc x < LENGTH p /\
  (!h. h = height x ==>
  !fall. fall = (\y. pc y = pc x+1) ==>
  !arm. arm = (\P n. ?y. S y /\ P y /\ height y = n) ==>
  !legal. legal = (\P n. !y. S y ==> P y /\ height y = n) ==>
  !next. next = (\n. arm fall n /\ legal fall n) ==>
  !untagged. untagged = (\a. !k. k<a ==> tag x k=NONE) ==>
  !stop. stop = (\a. a<=h /\ untagged a /\ !y. ~S y) ==>
  case EL (pc x) p of
    AsmLabel l => next h
  | AsmPush bs => next (h+1)
  | AsmPushLabel l => IS_SOME (FLOOKUP (SND(compute_label_offsets p)) l) /\ next (h+1)
  | AsmPushOfst l d => IS_SOME (FLOOKUP (SND(compute_label_offsets p)) l) /\ next (h+1)
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
                  1<=h /\ arm (^target p pc tag x) (h-1) /\ legal (^target p pc tag x) (h-1)
               else if name="JUMPI" then
                  2<=h /\ tag x 1=NONE /\ arm fall (h-2) /\ arm (^target p pc tag x) (h-2) /\
                  legal (\y. fall y \/ ^target p pc tag x y) (h-2)
               else
                  ?m. static_abort_straight name m /\ asm_op_arity name <= h /\
                      untagged (asm_op_arity name) /\ next (h-asm_op_arity name+m))
  | _ => F)``;

val Rows = ``\p cc (V:(num#num)->bool) (rank:(num#num)->num) pc height need tag boolean edge.
  (!x. x IN V ==> ^Slots p cc (height x) (need x) (tag x) (boolean x)) /\
  (!x y. edge x y ==> x IN V /\ y IN V /\ rank y < rank x /\
     ^Flow p pc height tag boolean x y) /\
  (!x. x IN V ==> ^Dispatch p cc pc height tag x (edge x))``;

val EdgeOK = ``\p pc height tag boolean x y.
  ^Flow p pc height tag boolean x y /\
  (if EL (pc x) p = AsmOp "JUMP" then ^target p pc tag x y
   else if EL (pc x) p = AsmOp "JUMPI" then pc y = pc x+1 \/ ^target p pc tag x y
   else pc y = pc x+1)``;

val Open = ``\p cc req (V:(num#num)->bool) X (rank:(num#num)->num) pc height need tag boolean edge.
  !S. S = ^Shape p cc req pc height need tag boolean ==>
  FINITE V /\ X SUBSET V /\
  (!x. x IN V ==> ?t. S x t) /\
  (!x. x IN V DIFF X ==> pc x < LENGTH p) /\
  (!x y. edge x y ==> x IN V DIFF X /\ y IN V /\ rank y < rank x /\
     ^EdgeOK p pc height tag boolean x y) /\
  (!x t. x IN V DIFF X /\ S x t ==>
     (?u. (asm_steps (SND(compute_label_offsets p)) (build_offset_to_pc p)
                  p 1 t = AsmRevert u \/
           asm_steps (SND(compute_label_offsets p)) (build_offset_to_pc p)
                  p 1 t = AsmFault u) /\ u.as_requests=req) \/
     (?y u. edge x y /\ asm_steps (SND(compute_label_offsets p)) (build_offset_to_pc p)
                  p 1 t = AsmOK u /\ S y u))``;

val Reach = ``\(edge:(num#num)->(num#num)->bool) e x.
  ?n (path:num->num#num).
    path 0=e /\ path n=x /\ !k. k<n ==> edge (path k) (path(SUC k))``;

val Just = ``\u (tag:(num#num)->num->(string#num)option) boolean e.
  (!k l origin. tag e k = SOME(l,origin) ==>
    k < LENGTH u.sym_stack /\ EL k u.sym_stack = Lab l 0) /\
  (!k. boolean e k ==>
    k < LENGTH u.sym_stack /\ (EL k u.sym_stack = Val 0w \/ EL k u.sym_stack = Val 1w))``;

val Entry = ``\orig s data p.
  s.as_pc = 0 /\ s.as_code = assemble orig ++ data /\
  asm_static_wf orig /\ asm_static_wf p /\ FILTER is_data_inst p = FILTER is_data_inst orig``;

val Pending = ``\orig s data req_bound p.
  ?j t u cc req (V:(num#num)->bool) e (rank:(num#num)->num)
      pc height need tag boolean edge.
    asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p j
      (s with as_code := assemble p ++ data) = AsmOK t /\
    sym_steps p (asm_data_env orig (assemble orig ++ data)) j (sym_init s) = SymOK u /\
    asm_sym_rel p (asm_data_env p (assemble p ++ data)) t u /\
    t.as_pc = u.sym_base.as_pc /\ LENGTH t.as_stack = LENGTH u.sym_stack /\
    t.as_call_ctx = u.sym_base.as_call_ctx /\ t.as_requests = u.sym_base.as_requests /\
    t.as_call_ctx = cc /\ t.as_requests = req /\ req <<= req_bound /\
    ^Rows p cc V rank pc height need tag boolean edge /\
    ^Open p cc req V {} rank pc height need tag boolean edge /\
    e IN V /\ (!x. x IN V ==> ^Reach edge e x) /\
    ^Shape p cc req pc height need tag boolean e t /\ ^Just u tag boolean e``;

val Terminal = ``\orig s data req_bound p.
  ?n out.
    (asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p n
       (s with as_code := assemble p ++ data) = AsmRevert out \/
     asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p n
       (s with as_code := assemble p ++ data) = AsmFault out) /\
    sym_terminal (sym_steps p (asm_data_env orig (assemble orig ++ data)) n (sym_init s)) /\
    out.as_requests <<= req_bound``;

(* Finish a pending certificate from the already selected rooted table and
   the symbolic endpoint of the actual protected prefix. *)
Theorem stack_selected_table_restart[local]:
  !orig s data req_bound q j u cc req V e rank pc height need tag boolean edge.
  ^Entry orig s data q /\
  sym_steps q (asm_data_env orig (assemble orig ++ data)) j (sym_init s) = SymOK u /\
  u.sym_base.as_pc = pc e /\ LENGTH u.sym_stack = height e /\
  u.sym_base.as_call_ctx = cc /\ u.sym_base.as_requests = req /\ req <<= req_bound /\
  FINITE V /\ e IN V /\ (!x. x IN V ==> ^Reach edge e x) /\
  ^Rows q cc V rank pc height need tag boolean edge /\
  (!x y. edge x y ==> ^EdgeOK q pc height tag boolean x y) /\
  ^Just u tag boolean e ==>
  ^Pending orig s data req_bound q
Proof
  rpt gen_tac >> BETA_TAC >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_all stopped_symbolic_prefix_actual_code >>
  disch_then (qx_choose_then `t` (map_every assume_tac o CONJUNCTS)) >>
  `^Shape q cc req pc height need tag boolean e t` by suspend "root" >>
  `^Open q cc req V {} rank pc height need tag boolean edge` by suspend "open" >>
  qexistsl [`j`,`t`,`u`,`cc`,`req`,`V`,`e`,`rank`,`pc`,`height`,`need`,`tag`,`boolean`,`edge`] >>
  RULE_ASSUM_TAC BETA_RULE >> BETA_TAC >>
  rpt (FIRST [first_assum ACCEPT_TAC, conj_tac]) >> simp[]
QED

Resume stack_selected_table_restart[root]:
  `^Slots q cc (height e) (need e) (tag e) (boolean e)` by
    (BETA_TAC >> first_assum irule >> first_assum ACCEPT_TAC) >>
  pop_assum (map_every assume_tac o CONJUNCTS o BETA_RULE) >>
  qpat_assum `asm_sym_rel q _ t u`
    (strip_assume_tac o SRULE[LIST_REL_EL_EQN] o CONJUNCT1 o REWRITE_RULE[asm_sym_rel_def]) >>
  map_every (fn pat => qpat_assum pat mp_tac)
    [`t.as_pc = _`, `LENGTH t.as_stack = _`, `t.as_call_ctx = _`, `t.as_requests = _`,
     `u.sym_base.as_pc = _`, `LENGTH u.sym_stack = height e`,
     `u.sym_base.as_call_ctx = _`, `u.sym_base.as_requests = _`,
     `need e ==> cc.cc_static`,
     `!k l o'. tag e k = SOME(l,o') ==> k < height e /\ o' < LENGTH q /\ _`,
     `!k l o'. tag e k = SOME(l,o') ==> k < LENGTH u.sym_stack /\ EL k u.sym_stack = Lab l 0`,
     `!k. boolean e k ==> k < LENGTH u.sym_stack /\ (_ = Val 0w \/ _ = Val 1w)`,
     `!i. i < LENGTH u.sym_stack ==> sval_conc _ _ = SOME _`] >>
  POP_ASSUM_LIST (K ALL_TAC) >> ntac 13 disch_tac >>
  BETA_TAC >> ntac 5 (conj_tac >- simp[]) >>
  `!k. k < LENGTH u.sym_stack ==> EL k t.as_stack =
         THE (sval_conc (SND (compute_label_offsets q)) (EL k u.sym_stack))` by
    (rpt strip_tac >>
     qpat_assum `!i. i<LENGTH u.sym_stack ==> sval_conc _ _ = SOME _`
       (qspec_then `k` (drule_then (ACCEPT_TAC o SYM o
         REWRITE_RULE[THE_DEF] o AP_TERM ``THE:bytes32 option -> bytes32``)))) >>
  conj_tac
  >- (rpt gen_tac >> disch_tac >>
      qpat_assum `!k l o'. tag e k=SOME(l,o') ==> k<height e /\ o'<LENGTH q /\ _`
        (drule_then (CONJUNCTS_THEN2 assume_tac
           (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac
             (qx_choose_then `off` (qx_choose_then `dest` strip_assume_tac)))))) >>
      qpat_assum `!k l o'. tag e k=SOME(l,o') ==> k<LENGTH u.sym_stack /\ EL k u.sym_stack=Lab l 0`
        (drule_then strip_assume_tac) >>
      `EL k t.as_stack = (n2w off:bytes32)` by
        (qpat_assum `!i. i<LENGTH u.sym_stack ==> EL i t.as_stack = THE _`
           (qspec_then `k` (drule_then SUBST1_TAC)) >>
         qpat_assum `EL k u.sym_stack = Lab l 0` SUBST1_TAC >>
         qpat_assum `FLOOKUP (SND (compute_label_offsets q)) l = SOME off`
           (fn hit => SIMP_TAC std_ss [hit,sval_conc_def,THE_DEF])) >>
      simp[] >>
      qpat_x_assum `EL origin q = AsmPushLabel l \/ EL origin q = AsmPushOfst l 0`
        strip_assume_tac >> simp[] >> qexists `0` >> simp[]) >>
  rpt gen_tac >> disch_tac >>
  qpat_assum `!k. boolean e k ==> k<LENGTH u.sym_stack /\ (_=Val 0w \/ _=Val 1w)`
    (drule_then strip_assume_tac) >>
  (conj_tac >-
     (qpat_assum `LENGTH u.sym_stack = height e` (SUBST1_TAC o SYM) >>
      first_assum ACCEPT_TAC)) >>
  qpat_assum `!i. i<LENGTH u.sym_stack ==> EL i t.as_stack = THE _`
    (qspec_then `k` (drule_then SUBST1_TAC)) >>
  qpat_assum `EL k u.sym_stack = Val _` SUBST1_TAC >>
  SIMP_TAC std_ss [sval_conc_def,THE_DEF]
QED

Resume stack_selected_table_restart[open]:
  ` {x | x IN V /\ ^Reach edge e x} = V` by
    (simp[EXTENSION] >> BETA_TAC >> gen_tac >>
     eq_tac >- simp[] >> disch_tac >> conj_tac >- first_assum ACCEPT_TAC >>
     qpat_assum `!x. x IN V ==> ?n path. path 0 = e /\ path n = x /\ _`
       (qspec_then `x` (drule_then ACCEPT_TAC))) >>
  `!x y. (x IN V /\ edge x y) = edge x y` by
    (rpt gen_tac >> eq_tac >- (strip_tac >> first_assum ACCEPT_TAC) >>
     disch_tac >> conj_tac >- (
       qpat_assum `!x y. edge x y ==> x IN V /\ y IN V /\ _`
         (qspecl_then [`x`,`y`] (drule_then (ACCEPT_TAC o CONJUNCT1)))) >>
     first_assum ACCEPT_TAC) >>
  `t.as_call_ctx = cc` by
    (qpat_assum `t.as_call_ctx = u.sym_base.as_call_ctx` SUBST1_TAC >>
     first_assum ACCEPT_TAC) >>
  `t.as_requests = req` by
    (qpat_assum `t.as_requests = u.sym_base.as_requests` SUBST1_TAC >>
     first_assum ACCEPT_TAC) >>
  (let
     val normalize = TOP_DEPTH_CONV (FIRST_CONV
       [BETA_CONV, REWR_CONV LET_THM, HO_REWR_CONV UNWIND_FORALL_THM2,
        REWR_CONV ratTheory.RAT_OF_NUM_LES])
   in
     rule_assum_tac (CONV_RULE normalize) >> CONV_TAC normalize >>
     qpat_assum `t.as_call_ctx = cc` (fn ctx_eq =>
       qpat_assum `t.as_requests = req` (fn req_eq =>
         let val rewrite = PURE_REWRITE_RULE [ctx_eq,req_eq] in
           rule_assum_tac rewrite >>
           mp_tac (rewrite (CONV_RULE normalize
             (Q.SPECL [`q`,`u`,`t`,`V`,`e`,`\x. rat$rat_of_num (rank x)`,
                       `pc`,`height`,`need`,`tag`,`boolean`,`edge`]
               pending_rows_rooted_package)))
         end))
   end) >>
  (impl_tac >- (rpt (FIRST [first_assum ACCEPT_TAC, conj_tac]))) >>
  disch_then (mp_tac o CONJUNCT1 o CONJUNCT2 o CONJUNCT2 o CONJUNCT2) >>
  qpat_assum `{x | x IN V /\ _} = V` (pure_rewrite_tac o single) >>
  qpat_assum `!x y. (x IN V /\ edge x y) = edge x y`
    (pure_rewrite_tac o single) >>
  disch_then ACCEPT_TAC
QED

Finalise stack_selected_table_restart

val erase = ``[AsmOp "DUP1"; AsmOp "SWAP1"; AsmOp "POP"]``;
val fixed = ``\w d.
  (w=[AsmOp "DUP1";AsmOp "SWAP2";AsmOp "SWAP1"] /\ d=[AsmOp "SWAP1";AsmOp "DUP2"]) \/
  (w=[AsmOp "SWAP1";AsmOp "POP";AsmOp "POP"] /\ d=[AsmOp "POP";AsmOp "POP"]) \/
  (w=[AsmOp "DUP1";AsmOp "SWAP1"] /\ d=[AsmOp "DUP1"])``;
val comm = ``\w d. ?a. asm_commutative_op a /\ w=[AsmOp "SWAP1";a] /\ d=[a]``;
val guarded = ``\w. ?a. asm_swap_op a /\ w=[a;a]``;
val window = ``\w d. (d=[] /\ (w=^erase \/ ^guarded w)) \/ ^fixed w d \/ ^comm w d``;
val tr = ``\(f:num->num) (tag:(num#num)->num->(string#num)option) v k.
  OPTION_MAP (\(l,i). (l,f i)) (tag v k)``;
val port_layout = ``\p q f.
  (!l i. i < LENGTH p /\ (EL i p = AsmPushLabel l \/ EL i p = AsmPushOfst l 0) ==>
      f i < LENGTH q /\ EL (f i) q = EL i p) /\
  (!l j. ^Canon p l j ==> ^Canon q l (f j))``;
val same_demands = ``\(height:num#num->num) (tag:(num#num)->num->(string#num)option) (boolean:num#num->num->bool) v z.
  height z=height v /\
  (!k l i. tag z k=SOME(l,i) ==> tag v k=SOME(l,i)) /\
  (!k. boolean z k ==> boolean v k)``;
val guard = ``\ins hi hj (G:num->(string#num)option).
  ?name. ins = AsmOp name /\
    (case ALOOKUP dup_table name of
       SOME j => j<hi /\ hj=hi+1
     | NONE => case ALOOKUP swap_table name of
         SOME j => 0<j /\ j<hi /\ hj=hi
       | NONE => ?r. static_abort_straight name r /\ asm_op_arity name<=hi /\
           (!k. k<asm_op_arity name ==> G k=NONE) /\ hj=hi-asm_op_arity name+r)``;
val phases = ``\q cc b f d (height:num#num->num) need (rank:num#num->num) tag boolean v z
  (H:num#num->num) (R:num#num->num) (G:(num#num)->num->(string#num)option) (B:(num#num)->num->bool).
  !n. n = LENGTH d ==>
  !P. P = (\x:num#num. b+FST x) ==>
  H (0,0) = height v /\ H (n,0) = height z /\
  R (0,0) = rank v /\ R (n,0) = rank z /\
  (!k l i. G (0,0) k = SOME(l,i) ==> ^tr f tag v k = SOME(l,i)) /\
  (!k. B (0,0) k ==> boolean v k) /\
  (!k. G (n,0) k = ^tr f tag z k /\ (B (n,0) k <=> boolean z k)) /\
  (!i. i<=n ==> ^Slots q cc (H (i,0)) (i=n /\ need z) (G (i,0)) (B (i,0))) /\
  (!i. i<n ==>
     P (i,0)<LENGTH q /\ EL (P (i,0)) q = EL i d /\ P (SUC i,0) = P (i,0)+1 /\
     R (SUC i,0) < R (i,0) /\
     ^Flow q P H G B (i,0) (SUC i,0) /\
     ^guard (EL i d) (H (i,0)) (H (SUC i,0)) (G (i,0)))``;

val stack_norm = SIMP_RULE bool_ss [LET_THM, UNWIND_FORALL_THM2, DIFF_EMPTY, EMPTY_SUBSET, CONJ_ASSOC];
val stack_norm_tac = SIMP_TAC bool_ss [LET_THM, UNWIND_FORALL_THM2, DIFF_EMPTY, EMPTY_SUBSET, CONJ_ASSOC];

Theorem stack_select_ports[local]:
  !pre w d tail p q cc req V rank pc height need tag boolean edge.
  !b. b = LENGTH pre ==>
  !m. m = LENGTH w ==>
  !n. n = LENGTH d ==>
  !f. f = splice_pc b m n ==>
  asm_static_wf p /\ p=pre++w++tail /\ q=pre++d++tail /\ ^window w d /\
  ^port_layout p q f /\ ^Rows p cc V rank pc height need tag boolean edge /\
  ^Open p cc req V {} rank pc height need tag boolean edge ==>
  ?z H R G B. !v. v IN V /\ pc v=b ==>
    z v IN V /\ pc (z v)=b+m /\ rank (z v)<rank v /\
    (if n=0 then ^same_demands height tag boolean v (z v)
     else ^phases q cc b f d height need rank tag boolean v (z v)
                  (H v) (R v) (G v) (B v))
Proof
  ntac 16 gen_tac >> stack_norm_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `!A (P:(num#num)->(num#num)->((num#num)->num)->((num#num)->num)->
         ((num#num)->num->(string#num)option)->((num#num)->num->bool)->bool).
      (!v. A v ==> ?z h r g a. P v z h r g a) ==>
      ?Z H R G B. !v. A v ==> P v (Z v) (H v) (R v) (G v) (B v)` by
    (rpt gen_tac >> disch_tac >>
     qabbrev_tac `packet = \v t. P v (FST t) (FST (SND t))
           (FST (SND (SND t))) (FST (SND (SND (SND t))))
           (SND (SND (SND (SND t))))` >>
     qabbrev_tac `pick = \v. @t. packet v t` >>
     `!v. A v ==> packet v (pick v)` by
       (gen_tac >> disch_tac >>
        qpat_assum `!v. A v ==> _` (drule_then strip_assume_tac) >>
        Q.SUBGOAL_THEN `?t. packet v t` (mp_tac o SELECT_RULE)
        >- (qexists `(z,h,r,g,a)` >> simp[Abbr `packet`]) >>
        simp[Abbr `pick`]) >>
     qexistsl [`\v. FST (pick v)`,`\v. FST (SND (pick v))`,
       `\v. FST (SND (SND (pick v)))`,`\v. FST (SND (SND (SND (pick v))))`,
       `\v. SND (SND (SND (SND (pick v))))`] >>
     qpat_x_assum `!v. A v ==> packet v (pick v)` mp_tac >> simp[Abbr `packet`]) >>
  pop_assum (qspecl_then [`\v. v IN V /\ pc v=LENGTH pre`,
    `\v z H R G B. z IN V /\ pc z=LENGTH pre+LENGTH w /\ rank z<rank v /\
      (if LENGTH d=0 then ^same_demands height tag boolean v z
       else ^phases q cc (LENGTH pre) (splice_pc (LENGTH pre) (LENGTH w) (LENGTH d))
                    d height need rank tag boolean v z H R G B)`]
    (mp_tac o stack_norm)) >>
  (impl_tac >- suspend "pointwise_port") >> (simp[])
QED

val PortSlots = ``\p cc h need (g:num->(string#num)option) (B:num->bool).
  (need ==> cc.cc_static) /\
  (!k. B k ==> k < h /\ g k = NONE) /\
  (!k l origin. g k = SOME(l,origin) ==>
    k < h /\ origin < LENGTH p /\
    (EL origin p = AsmPushLabel l \/ EL origin p = AsmPushOfst l 0) /\
    ?j. ^Canon p l j)``;

Theorem stack_ports_slots[local]:
  !a c h N g B. ^Slots a c h N g B <=> ^PortSlots a c h N g B
Proof
  rpt gen_tac >> BETA_TAC >> eq_tac >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  ASM_SIMP_TAC bool_ss [] >> rpt gen_tac >> disch_tac >>
  qpat_assum `!k l i. g k = SOME(l,i) ==> _` (drule_then strip_assume_tac) >>
  ASM_SIMP_TAC bool_ss [] >>
  rename1 `FLOOKUP (build_offset_to_pc a) off = SOME dest` >>
  FIRST (map (fn ws => qexistsl ws >> ASM_SIMP_TAC bool_ss [] >> NO_TAC)
    [[`dest`,`off`], [`off`,`dest`]])
QED

Resume stack_select_ports[pointwise_port]:
  qx_gen_tac `v` >> disch_then (map_every assume_tac o CONJUNCTS) >>
  assume_tac stack_ports_slots >>
  `!x. x IN V ==> ^PortSlots p cc (height x) (need x) (tag x) (boolean x)` by
    (gen_tac >> disch_tac >>
     qpat_assum `!a c h N g B. _ <=> _` (fn th => PURE_REWRITE_TAC [GSYM th]) >>
     stack_norm_tac >> first_assum (drule_then ACCEPT_TAC)) >>
  pop_assum (assume_tac o stack_norm) >>
  mp_tac (stack_norm stack_whole_visit_port) >>
  (impl_tac >- rpt (FIRST [first_assum ACCEPT_TAC, conj_tac])) >>
  disch_then (qx_choose_then `z` mp_tac) >>
  disch_tac >> qexists `z` >> pop_assum mp_tac >> Cases_on `LENGTH d = 0` >>
  qpat_assum `!a c h N g B. _ <=> _` (fn th => PURE_REWRITE_TAC [GSYM (stack_norm th)]) >>
  ASM_SIMP_TAC bool_ss [LEFT_EXISTS_AND_THM, RIGHT_EXISTS_AND_THM, CONJ_ASSOC]
QED

Finalise stack_select_ports

val rule_form = ``\w d.
  (w=[AsmOp "DUP1";AsmOp "SWAP2";AsmOp "SWAP1"] /\ d=[AsmOp "SWAP1";AsmOp "DUP2"]) \/
  (w=^erase /\ d=[]) \/
  (w=[AsmOp "SWAP1";AsmOp "POP";AsmOp "POP"] /\ d=[AsmOp "POP";AsmOp "POP"]) \/
  (?a. asm_swap_op a /\ w=[a;a] /\ d=[]) \/
  (?a. asm_commutative_op a /\ w=[AsmOp "SWAP1";a] /\ d=[a]) \/
  (w=[AsmOp "DUP1";AsmOp "SWAP1"] /\ d=[AsmOp "DUP1"])``;

Theorem stack_window_rule_form[local]:
  !w d. (^window w d <=> ^rule_form w d) /\ (^window w d ==> 0<LENGTH w)
Proof
  rpt gen_tac >> BETA_TAC >> conj_tac
  >- (eq_tac >> strip_tac >> simp[] >> metis_tac[]) >>
  strip_tac >> simp[]
QED

val Kept = ``\(b:num) m pc (V:(num#num)set). {v | v IN V /\ (pc v < b \/ b+m <= pc v)}``;
val Heads = ``\(b:num) pc (V:(num#num)set). {v | v IN V /\ pc v=b}``;
val Layout = ``\p q b m n.
  !f. f = splice_pc b m n ==>
  asm_static_wf q /\ FILTER is_data_inst q = FILTER is_data_inst p /\
  (!i. i < LENGTH p /\ (i < b \/ b+m <= i) ==> f i < LENGTH q /\ EL (f i) q = EL i p) /\
  ^port_layout p q f /\
  (!l. IS_SOME (FLOOKUP (SND (compute_label_offsets p)) l) ==>
       IS_SOME (FLOOKUP (SND (compute_label_offsets q)) l)) /\
  (!l i. ^Canon p l i ==> i < b \/ b+m <= i) /\
  f b=b /\ f (b+m)=b+n /\
  (!i. i < LENGTH p /\ (i < b \/ b+m <= i) ==> f (i+1)=f i+1)``;

Theorem stack_window_layout[local]:
  !pre w d tail.
  ^window w d /\ asm_static_wf (pre++w++tail) ==>
  ^Layout (pre++w++tail) (pre++d++tail) (LENGTH pre) (LENGTH w) (LENGTH d)
Proof
  rpt gen_tac >> BETA_TAC >> disch_tac >>
  qspecl_then [`pre`,`w`,`d`,`tail`] (mp_tac o stack_norm) stack_peephole_one_layout >>
  (impl_tac >- fs[stack_window_rule_form]) >>
  disch_then (map_every assume_tac o CONJUNCTS) >> stack_norm_tac >>
  rpt (FIRST [first_assum ACCEPT_TAC, conj_tac])
  >- (map_every qx_gen_tac [`l`,`i`] >> strip_tac >>
      qpat_assum `!i l. _ ==> _` (qspecl_then [`i`,`l`] mp_tac) >>
      (impl_tac >- simp[]) >> simp[]) >>
  map_every qx_gen_tac [`l`,`j`] >>
  disch_then (qx_choose_then `off` (map_every assume_tac o CONJUNCTS)) >>
  qpat_assum `!l off j. _ ==> _` (qspecl_then [`l`,`off`,`j`] mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (map_every strip_assume_tac o CONJUNCTS) >>
  FIRST [simp[] >> NO_TAC, qexists `off'` >> simp[]]
QED

val Motion = ``\p pc tag (x:num#num) y.
  if EL (pc x) p = AsmOp "JUMP" then ^target p pc tag x y
  else if EL (pc x) p = AsmOp "JUMPI" then pc y = pc x+1 \/ ^target p pc tag x y
  else pc y = pc x+1``;

Theorem stack_dispatch_motion[local]:
  !p cc pc height tag x S y.
  ^Dispatch p cc pc height tag x S /\ S y ==> ^Motion p pc tag x y
Proof
  rpt gen_tac >> stack_norm_tac >>
  Cases_on `EL (pc x) p` >> simp[] >> rpt strip_tac >> gvs[] >>
  rename1 `EL (pc x) p = AsmOp name` >>
  Cases_on `name="JUMP"` >- (gvs[dup_table_def,swap_table_def] >> res_tac) >>
  Cases_on `name="JUMPI"` >- (gvs[dup_table_def,swap_table_def] >> res_tac) >>
  Cases_on `name="INVALID"` >- gvs[] >>
  Cases_on `name="REVERT"` >- gvs[] >>
  Cases_on `name="SSTORE" \/ name="TSTORE" \/ name="LOG0" \/ name="LOG1" \/
            name="LOG2" \/ name="LOG3" \/ name="LOG4"` >> gvs[] >>
  Cases_on `ALOOKUP dup_table name` >> gvs[] >>
  Cases_on `ALOOKUP swap_table name` >> gvs[] >> res_tac
QED

val LocalRow = ``\q cc pc height (rk:(num#num)->num) need tag boolean x S.
  ^PortSlots q cc (height x) (need x) (tag x) (boolean x) /\
  ^Dispatch q cc pc height tag x S /\
  !y. S y ==> rk y < rk x /\ ^Flow q pc height tag boolean x y /\ ^Motion q pc tag x y``;

Theorem stack_guard_singleton[local]:
  !q cc pc height tag x y.
  pc x < LENGTH q /\ pc y = pc x+1 /\
  ^guard (EL (pc x) q) (height x) (height y) (tag x) ==>
  ^Dispatch q cc pc height tag x (\z. z=y)
Proof
  rpt gen_tac >> stack_norm_tac >> strip_tac >>
  `name <> "INVALID" /\ name <> "REVERT" /\ name <> "JUMP" /\ name <> "JUMPI" /\
   ~MEM name ["SSTORE";"TSTORE";"LOG0";"LOG1";"LOG2";"LOG3";"LOG4"]` by
    (qpat_x_assum `(case ALOOKUP dup_table name of _ => _ | _ => _)` mp_tac >>
     Cases_on `name` >> simp[] >>
     Cases_on `STRING h t = "INVALID" \/ STRING h t = "REVERT" \/
               STRING h t = "JUMP" \/ STRING h t = "JUMPI" \/
               MEM (STRING h t) ["SSTORE";"TSTORE";"LOG0";"LOG1";"LOG2";"LOG3";"LOG4"]` >>
     fs[] >> rpt strip_tac >>
     gvs[dup_table_def, swap_table_def, static_abort_straight_def]) >>
  fs[] >> Cases_on `ALOOKUP dup_table name` >> fs[] >>
  Cases_on `ALOOKUP swap_table name` >> fs[] >> metis_tac[]
QED

(* A singleton edge needs only the projections at its two endpoints. *)
val FlowAt = ``\q i hi hj (gi:num->(string#num)option) gj bi bj.
  !left. left = (\x:num#num. FST x=0) ==>
  ^Flow q (\x. i) (\x. if left x then hi else hj)
          (\x. if left x then gi else gj) (\x. if left x then bi else bj)
          (0,0) (1,0)``;

Theorem stack_flow_at[local]:
  !q pc height tag boolean x y.
  ^Flow q pc height tag boolean x y <=>
  ^FlowAt q (pc x) (height x) (height y) (tag x) (tag y) (boolean x) (boolean y)
Proof
  rpt gen_tac >> BETA_TAC >>
  CONV_TAC (RAND_CONV (HO_REWR_CONV UNWIND_FORALL_THM2)) >>
  SIMP_TAC bool_ss [FST] >> simp[]
QED

Theorem stack_local_one[local]:
  !q cc pc height rk need tag boolean x y.
  ^PortSlots q cc (height x) (need x) (tag x) (boolean x) /\
  pc x < LENGTH q /\ pc y=pc x+1 /\ rk y<rk x /\
  ^guard (EL (pc x) q) (height x) (height y) (tag x) /\
  ^FlowAt q (pc x) (height x) (height y) (tag x) (tag y) (boolean x) (boolean y) ==>
  ^LocalRow q cc pc height rk need tag boolean x (\w. w=y)
Proof
  rpt gen_tac >> BETA_TAC >> disch_then (map_every assume_tac o CONJUNCTS) >>
  `^Dispatch q cc pc height tag x (\w. w=y)` by
     (irule stack_guard_singleton >> BETA_TAC >>
      rpt (FIRST [first_assum ACCEPT_TAC, conj_tac])) >>
  `^Flow q pc height tag boolean x y` by
     (irule (iffRL stack_flow_at) >> BETA_TAC >> first_assum ACCEPT_TAC) >>
  `^Motion q pc tag x y` by
     (irule stack_dispatch_motion >> qexistsl [`\w. w=y`,`cc`,`height`] >>
      ASM_SIMP_TAC bool_ss []) >>
  rule_assum_tac BETA_RULE >>
  rpt (FIRST [first_assum ACCEPT_TAC, conj_tac]) >>
  qx_gen_tac `w` >> BETA_TAC >> disch_then SUBST1_TAC >>
  rpt (FIRST [first_assum ACCEPT_TAC, conj_tac])
QED

Theorem stack_old_retained_edge[local]:
  !p (b:num) (m:num) V pc tag v u.
  0<m /\ v IN ^Kept b m pc V /\ u IN V /\
  (!l i. ^Canon p l i ==> i < b \/ b+m <= i) /\ ^Motion p pc tag v u ==>
  u IN ^Kept b m pc V UNION ^Heads b pc V
Proof
  rpt gen_tac >> stack_norm_tac >>
  simp[] >> strip_tac >>
  `pc u = pc v+1 \/ ?l. ^Canon p l (pc u)` by
    (BETA_TAC >> qpat_x_assum `(if _ then _ else _)` mp_tac >>
     simp[AllCaseEqs()] >> metis_tac[]) >>
  pop_assum (strip_assume_tac o BETA_RULE) >>
  TRY (qpat_assum `pc u = pc v+1` (K decide_tac)) >>
  qpat_assum `!l i. _ ==> i < b \/ b+m <= i` (qspecl_then [`l`,`pc u`] mp_tac) >>
  (impl_tac >- (qexists `off` >> simp[])) >> simp[]
QED

(* Transport one retained row, using the chosen image for each old successor. *)
Theorem stack_retained_local[local]:
  !p q cc V pc height rank need tag boolean edge x P H R N G B c g f.
  ^Rows p cc V rank pc height need tag boolean edge /\ x IN V /\
  P c = f (pc x) /\ P c < LENGTH q /\ EL (P c) q = EL (pc x) p /\
  H c = height x /\ R c = rank x /\ N c = need x /\ B c = boolean x /\
  (!k. G c k = ^tr f tag x k) /\
  (!y. edge x y ==> P (g y) = f (pc y) /\ H (g y) = height y /\
    R (g y) <= rank y /\ (N (g y) ==> cc.cc_static) /\
    (!k l j. G (g y) k = SOME(l,j) ==> ?i. tag y k = SOME(l,i) /\ j = f i) /\
    (!k. B (g y) k ==> boolean y k)) /\
  (!y. edge x y /\ pc y = pc x+1 ==> f (pc y) = f (pc x)+1) /\
  ^port_layout p q f /\
  (!l. IS_SOME (FLOOKUP (SND(compute_label_offsets p)) l) ==>
       IS_SOME (FLOOKUP (SND(compute_label_offsets q)) l)) ==>
  ^LocalRow q cc P H R N G B c (\u. ?y. edge x y /\ u=g y)
Proof
  rpt gen_tac >> BETA_TAC >>
  disch_then (map_every assume_tac o CONJUNCTS o stack_norm) >>
  `!v. v IN V ==> ^PortSlots p cc (height v) (need v) (tag v) (boolean v)` by
    (gen_tac >> disch_tac >>
     stack_norm_tac >> pure_rewrite_tac [GSYM (stack_norm stack_ports_slots)] >>
     first_assum (drule_then ACCEPT_TAC)) >>
  pop_assum (assume_tac o stack_norm) >>
  qspecl_then [`p`,`q`,`cc`,`f`,`pc`,`height`,`\v. rat$rat_of_num (rank v)`,
    `need`,`tag`,`boolean`,`edge`,`x`,`P`,`H`,`\v. rat$rat_of_num (R v)`,`N`,
    `G`,`B`,`\v u. ?y. edge x y /\ u = g y`,`c`,`g`]
    (mp_tac o SIMP_RULE bool_ss [ratTheory.RAT_OF_NUM_LEQ, ratTheory.RAT_OF_NUM_LES]
            o stack_norm) (stack_norm stack_splice_retained_arms) >>
  (impl_tac >- suspend "premises") >>
  disch_then (fn th =>
    case rev (CONJUNCTS th) of
      edges :: role :: slots =>
        mk_asm "retained_edges" edges >> mk_asm "retained_role" role >>
        map_every assume_tac (rev slots)
    | _ => FAIL_TAC "expected retained worker projections") >>
  `^Dispatch q cc P H G c (\u. ?y. edge x y /\ u=g y)` by suspend "dispatch" >>
  `^PortSlots q cc (H c) (N c) (G c) (B c)` by suspend "slots" >>
  rule_assum_tac BETA_RULE >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  suspend "edge"
QED

Resume stack_retained_local[premises]:
  `^PortSlots p cc (height x) (need x) (tag x) (boolean x)` by
    (stack_norm_tac >> first_assum (drule_then ACCEPT_TAC)) >>
  pop_assum (map_every assume_tac o CONJUNCTS o stack_norm) >>
  rpt (FIRST [first_assum ACCEPT_TAC, conj_tac])
  >- simp[]
  >- (qx_gen_tac `y` >> disch_tac >>
      qpat_assum `!u v. edge u v ==> _` (qspecl_then [`x`,`y`] mp_tac) >>
      simp[] >> disch_then (map_every assume_tac o CONJUNCTS) >>
      qpat_assum `!v. v IN V ==> _` (qspec_then `y` mp_tac) >>
      simp[] >> disch_then (map_every assume_tac o CONJUNCTS) >>
      qpat_assum `!v. edge x v ==> _` (qspec_then `y` mp_tac) >>
      simp[] >> disch_then (map_every assume_tac o CONJUNCTS) >>
      rpt (FIRST [first_assum ACCEPT_TAC, conj_tac])) >>
  qpat_assum `!v. v IN V ==> pc v < LENGTH p /\ _` (drule_then (mp_tac o CONJUNCT2)) >>
  CONV_TAC (DEPTH_CONV (HO_REWR_CONV (GSYM RIGHT_EXISTS_AND_THM))) >>
  SIMP_TAC bool_ss [CONJ_ASSOC]
QED

Resume stack_retained_local[dispatch]:
  stack_norm_tac >> conj_tac >- first_assum ACCEPT_TAC >>
  asm_x "retained_role" mp_tac >>
  pure_asm_rewrite_tac [] >>
  CONV_TAC (DEPTH_CONV (HO_REWR_CONV (GSYM RIGHT_EXISTS_AND_THM))) >>
  SIMP_TAC bool_ss [CONJ_ASSOC]
QED

Resume stack_retained_local[slots]:
  stack_norm_tac >>
  qpat_assum `!v. v IN V ==> ((need v ==> _) /\ (!k. _)) /\ _` (drule_then strip_assume_tac) >>
  conj_tac >- (conj_tac >> simp[]) >>
  qpat_assum `!k l i. OPTION_MAP _ (tag x k) = SOME (l,i) ==> _` mp_tac >>
  simp[]
QED

Resume stack_retained_local[edge]:
  qx_gen_tac `y` >> disch_tac >>
  asm "retained_edges" (qspec_then `y` mp_tac) >>
  (impl_tac >- (metis_tac[])) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  conj_tac >- pure_asm_rewrite_tac [] >>
  conj_tac
  >- (stack_norm_tac >> pure_asm_rewrite_tac [] >> first_assum ACCEPT_TAC) >>
  BETA_TAC >>
  qspecl_then [`q`,`cc`,`P`,`H`,`G`,`c`,`\u. ?z. edge x z /\ u=g z`,`y`]
    (mp_tac o BETA_RULE) stack_dispatch_motion >>
  BETA_TAC >> rule_assum_tac BETA_RULE >>
  (impl_tac >- rpt (FIRST [first_assum ACCEPT_TAC, conj_tac])) >>
  disch_then ACCEPT_TAC
QED

Finalise stack_retained_local

(* The table worker's occurrence encoding and its projection at each port. *)
val Copy = ``\v:num#num. (SUC (pair_to_num v),0:num)``;
val Phase = ``\v:num#num i:num. (SUC (pair_to_num v),SUC i)``;
val First = ``(0:num,0:num)``;
val Image = ``\(K:(num#num)set) (n:num) z v.
  if v IN K then ^Copy v else if n=0 then ^Copy (z v) else ^Phase v 0``;
val Next = ``\n z v i. if SUC i=n then ^Copy (z v) else ^Phase v (SUC i)``;
val CData = ``\(f:num->num) pc (height:(num#num)->num) (rank:(num#num)->num)
  (need:(num#num)->bool) tag (boolean:(num#num)->num->bool) v.
  (f (pc v),height v,rank v,need v,^tr f tag v,boolean v)``;
val PData = ``\(b:num) (ph_h:(num#num)->(num#num)->num) (ph_r:(num#num)->(num#num)->num)
  (ph_t:(num#num)->(num#num)->num->(string#num)option) (ph_b:(num#num)->(num#num)->num->bool) v i.
  (b+i,ph_h v (i,0:num),ph_r v (i,0:num),F,ph_t v (i,0:num),ph_b v (i,0:num))``;
val Data = ``\cd pd (id:num#num#num#bool#(num->(string#num)option)#(num->bool)) (x:num#num).
  if FST x=0 then id else
  (if SND x=0 then cd else combin$C pd (PRE (SND x)))
    (num_to_pair (PRE (FST x)))``;
val Pc = ``\(d:(num#num)->num#num#num#bool#(num->(string#num)option)#(num->bool)) x. FST (d x)``;
val Ht = ``\(d:(num#num)->num#num#num#bool#(num->(string#num)option)#(num->bool)) x. FST (SND (d x))``;
val Rk = ``\(d:(num#num)->num#num#num#bool#(num->(string#num)option)#(num->bool)) x. FST (SND (SND (d x)))``;
val Nd = ``\(d:(num#num)->num#num#num#bool#(num->(string#num)option)#(num->bool)) x. FST (SND (SND (SND (d x))))``;
val Tg = ``\(d:(num#num)->num#num#num#bool#(num->(string#num)option)#(num->bool)) x. FST (SND (SND (SND (SND (d x)))))``;
val Bl = ``\(d:(num#num)->num#num#num#bool#(num->(string#num)option)#(num->bool)) x. SND (SND (SND (SND (SND (d x)))))``;

Theorem stack_port_data[local]:
  (!cd pd id v. ^Data cd pd id (^Copy v) = cd v) /\
  (!cd pd id v i. ^Data cd pd id (^Phase v i) = pd v i) /\
  (!cd pd id. ^Data cd pd id ^First = id)
Proof
  simp[combinTheory.C_DEF]
QED

val PortSelection = ``\q cc b m d V pc height rank need tag boolean z H R G B.
  !n. n = LENGTH d ==>
  !f. f = splice_pc b m n ==>
  !v. v IN ^Heads b pc V ==>
    z v IN ^Kept b m pc V /\ pc (z v)=b+m /\ rank (z v)<rank v /\
    (if n=0 then ^same_demands height tag boolean v (z v)
     else ^phases q cc b f d height need rank tag boolean v (z v)
                  (H v) (R v) (G v) (B v))``;

(* Mark a defining equation as proof-local abbreviation without unfolding
   any of the row predicates under the alias. *)
val stack_alias_head = QUANT_CONV (LAND_CONV
  (REWR_CONV (GSYM markerTheory.Abbrev_def)));
fun stack_intro_aliases names = map_every (fn name =>
  CONV_TAC stack_alias_head >> qx_gen_tac name >> disch_tac) names;
fun stack_alias_rule 0 tail = tail
  | stack_alias_rule n tail = stack_alias_head THENC
      QUANT_CONV (RAND_CONV (stack_alias_rule (n-1) tail));
fun stack_aliases n conv = funpow n (fn k => QUANT_CONV k) conv;
val stack_inline_alias = HO_REWR_CONV UNWIND_FORALL_THM2 THENC DEPTH_CONV BETA_CONV;
fun stack_inline_lets 0 tail = tail
  | stack_inline_lets n tail = FIRST_CONV [stack_inline_alias,
      REWR_CONV LET_THM THENC TRY_CONV BETA_CONV] THENC stack_inline_lets (n-1) tail;

fun stack_apply_aliases [] k th = k th
  | stack_apply_aliases (pat::pats) k th =
    qpat_assum pat (fn marked =>
      let
        val alias = lhs (concl (REWRITE_RULE [markerTheory.Abbrev_def] marked))
        val normalize = REDEPTH_CONV (FIRST_CONV [REWR_CONV LET_THM,BETA_CONV])
      in
        stack_apply_aliases pats k
          (MP (CONV_RULE (LAND_CONV normalize) (SPEC alias th))
              (CONV_RULE normalize marked))
      end);

(* An incoming edge can use either a retained port or the selected head image. *)
Theorem stack_image_fields[local]:
  !q cc b m d V pc height rank need tag boolean z H R G B id v.
  !n. n = LENGTH d ==>
  !f. f = splice_pc b m n ==>
  !kept. kept = ^Kept b m pc V ==>
  !ann. ann = ^Data (^CData f pc height rank need tag boolean) (^PData b H R G B) id ==>
  !y. y = ^Image kept n z v ==>
  ^PortSelection q cc b m d V pc height rank need tag boolean z H R G B /\
  f b=b /\ f (b+m)=b+n /\
  (!x. x IN V ==> need x ==> cc.cc_static) /\
  v IN kept UNION ^Heads b pc V ==>
  ^Pc ann y=f (pc v) /\ ^Ht ann y=height v /\ ^Rk ann y<=rank v /\
  (^Nd ann y ==> cc.cc_static) /\
  (!k l o'. ^Tg ann y k=SOME(l,o') ==> ?i. tag v k=SOME(l,i) /\ o'=f i) /\
  (!k. ^Bl ann y k ==> boolean v k)
Proof
  ntac 19 gen_tac >> stack_intro_aliases [`n`,`f`,`kept`,`ann`,`y`] >> BETA_TAC >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  Cases_on `v IN kept`
  >- (`v IN V` by fs[Abbr `kept`] >>
      `ann y = ^CData f pc height rank need tag boolean v` by
        simp[Abbr `ann`, Abbr `y`, stack_port_data] >>
      simp[] >> conj_tac
      >- (qpat_assum `!x. x IN V ==> _` (qspec_then `v` mp_tac) >> simp[]) >>
      simp[AllCaseEqs(), pairTheory.EXISTS_PROD]) >>
  qpat_assum `!k. k = LENGTH d ==> _`
    (stack_apply_aliases [`Abbrev (n = _)`,`Abbrev (f = _)`]
      (qspec_then `v` mp_tac) o CONV_RULE (stack_alias_rule 2 ALL_CONV)) >>
  (impl_tac >- fs[IN_UNION]) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `z v IN kept` by simp[Abbr `kept`] >>
  `pc v=b /\ v IN V` by fs[] >>
  Cases_on `n=0`
  >- (`ann y = ^CData f pc height rank need tag boolean (z v)` by
        simp[Abbr `ann`, Abbr `y`, stack_port_data] >>
      `z v IN V` by fs[Abbr `kept`] >>
      qpat_x_assum `if n=0 then _ else _` (fn th =>
        qpat_assum `n=0` (fn h => strip_assume_tac (SIMP_RULE bool_ss [h] th))) >>
      simp[] >> conj_tac
      >- (qpat_assum `!x. x IN V ==> _` (qspec_then `z v` mp_tac) >> simp[]) >>
      simp[AllCaseEqs(), pairTheory.EXISTS_PROD] >> metis_tac[]) >>
  `ann y = ^PData b H R G B v 0` by simp[Abbr `ann`, Abbr `y`, stack_port_data] >>
  qpat_x_assum `if n=0 then _ else _` (fn th =>
    qpat_assum `n<>0` (fn h =>
      map_every assume_tac (CONJUNCTS (SIMP_RULE bool_ss [h, LET_THM] th)))) >>
  simp[] >>
  rpt gen_tac >> disch_tac >>
  qpat_assum `!k l i. G v (0,0) k = SOME(l,i) ==> _` drule >>
  simp[NoAsms, Abbr `f`, AllCaseEqs(), pairTheory.EXISTS_PROD, EQ_SYM_EQ]
QED

(* Retained incidences and rows use the very same image of each successor. *)
Theorem stack_selected_retained[local]:
  !p q cc b m d V pc height rank need tag boolean edge z H R G B id.
  !n. n = LENGTH d ==>
  !f. f = splice_pc b m n ==>
  !kept. kept = ^Kept b m pc V ==>
  !ann. ann = ^Data (^CData f pc height rank need tag boolean) (^PData b H R G B) id ==>
  !image. image = ^Image kept n z ==>
  0<m /\ ^Layout p q b m n /\ ^Rows p cc V rank pc height need tag boolean edge /\
  ^PortSelection q cc b m d V pc height rank need tag boolean z H R G B ==>
  !x. x IN kept ==>
    (!y. edge x y ==> y IN kept UNION ^Heads b pc V) /\
    ^LocalRow q cc (^Pc ann) (^Ht ann) (^Rk ann) (^Nd ann) (^Tg ann) (^Bl ann)
       (^Copy x) (\u. ?y. edge x y /\ u=image y)
Proof
  ntac 20 gen_tac >> stack_intro_aliases [`n`,`f`,`kept`,`ann`,`image`] >> BETA_TAC >>
  disch_then (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 (mk_asm "layout")
    (CONJUNCTS_THEN2 (mk_asm "rows") assume_tac))) >>
  qx_gen_tac `x` >> disch_tac >>
  `x IN V` by fs[Abbr `kept`] >>
  asm "rows" (map_every assume_tac o CONJUNCTS o BETA_RULE) >>
  `^Dispatch p cc pc height tag x (edge x)` by
    (BETA_TAC >> gvs[]) >>
  `pc x < LENGTH p` by simp[] >>
  asm "layout" (stack_apply_aliases [`Abbrev (f = _)`]
    (map_every assume_tac o CONJUNCTS) o CONV_RULE stack_alias_head) >>
  `!y. edge x y ==> y IN kept UNION ^Heads b pc V` by suspend "incidence" >>
  conj_tac >- first_assum (ACCEPT_TAC o BETA_RULE) >>
  `ann (^Copy x) = ^CData f pc height rank need tag boolean x` by
    simp[Abbr `ann`, stack_port_data] >>
  qspecl_then [`p`,`q`,`cc`,`V`,`pc`,`height`,`rank`,`need`,`tag`,`boolean`,`edge`,
    `x`,`^Pc ann`,`^Ht ann`,`^Rk ann`,`^Nd ann`,`^Tg ann`,`^Bl ann`,
    `^Copy x`,`image`,`f`] (mp_tac o BETA_RULE) stack_retained_local >>
  (impl_tac >- suspend "row") >> stack_norm_tac >>
  metis_tac[]
QED

Resume stack_selected_retained[incidence]:
  qx_gen_tac `y` >> disch_tac >>
  `y IN V` by
    (qpat_assum `!u v. edge u v ==> _` (qspecl_then [`x`,`y`] (drule_then strip_assume_tac)) >> simp[]) >>
  `^Motion p pc tag x y` by
    (BETA_TAC >> irule (BETA_RULE stack_dispatch_motion) >>
     reverse conj_tac >- first_assum ACCEPT_TAC >>
     qexistsl [`edge x`,`cc`,`height`] >> BETA_TAC >>
     conj_tac >- first_assum ACCEPT_TAC >>
     gvs[]) >>
  `y IN ^Kept b m pc V UNION ^Heads b pc V` suffices_by
    simp[Abbr `kept`] >>
  BETA_TAC >> irule (BETA_RULE stack_old_retained_edge) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl [`p`,`tag`,`x`] >>
  conj_tac >- (stack_norm_tac >> first_assum (ACCEPT_TAC o stack_norm)) >>
  conj_tac >- fs[Abbr `kept`] >>
  first_assum (ACCEPT_TAC o BETA_RULE)
QED

Resume stack_selected_retained[row]:
  conj_tac >- asm "rows" (ACCEPT_TAC o BETA_RULE) >>
  `f (pc x) < LENGTH q /\ EL (f (pc x)) q = EL (pc x) p` by
    (qpat_assum `!i. i < LENGTH p /\ _ ==> _` (qspec_then `pc x` mp_tac) >>
     fs[Abbr `kept`]) >>
  qpat_assum `ann _ = _` (assume_tac o BETA_RULE) >>
  rpt (FIRST [first_assum ACCEPT_TAC, simp[] >> NO_TAC, conj_tac])
  >- (qx_gen_tac `y` >> disch_tac >>
            `y IN kept UNION ^Heads b pc V` by
        (qpat_assum `!y. edge x y ==> y IN kept UNION _` (qspec_then `y` mp_tac) >> simp[]) >>
      `!v. v IN V ==> need v ==> cc.cc_static` by
        (rpt strip_tac >> qpat_assum `!v. v IN V ==> (need v ==> cc.cc_static) /\ _`
           (qspec_then `v` mp_tac) >> simp[]) >>
      unabbrev_all_tac >> stack_norm_tac >>
      MATCH_MP_TAC (stack_norm stack_image_fields) >>
      qexists `q` >> rule_assum_tac stack_norm >>
      rpt (FIRST [first_assum ACCEPT_TAC, conj_tac]))
  >- (rpt strip_tac >> simp[] >>
      qpat_assum `!i. i < LENGTH p /\ _ ==> f (i+1) = _`
        (qspec_then `pc x` mp_tac) >> fs[Abbr `kept`]) >>
  stack_norm_tac >> first_assum ACCEPT_TAC
QED

Finalise stack_selected_retained

(* An internal phase uses the projections supplied by the selected visit.
   At its last edge the phase-n annotations are those of the copied exit. *)
Theorem stack_selected_phase[local]:
  !q cc b m d V pc height rank need tag boolean z H R G B id.
  !n. n = LENGTH d ==>
  !f. f = splice_pc b m n ==>
  !ann. ann = ^Data (^CData f pc height rank need tag boolean) (^PData b H R G B) id ==>
  ^PortSelection q cc b m d V pc height rank need tag boolean z H R G B /\
  f (b+m)=b+n ==>
  !v i. v IN ^Heads b pc V /\ i<n ==>
    ^LocalRow q cc (^Pc ann) (^Ht ann) (^Rk ann) (^Nd ann) (^Tg ann) (^Bl ann)
      (^Phase v i) (\y. y = ^Next n z v i)
Proof
  ntac 18 gen_tac >> stack_intro_aliases [`n`,`f`,`ann`] >>
  CONV_TAC (REDEPTH_CONV BETA_CONV) >> strip_tac >> rpt gen_tac >> strip_tac >>
  qspecl_then [`q`,`cc`,`^Pc ann`,`^Ht ann`,`^Rk ann`,`^Nd ann`,`^Tg ann`,
    `^Bl ann`,`^Phase v i`,`^Next n z v i`]
    (MATCH_MP_TAC o CONV_RULE (REDEPTH_CONV BETA_CONV)) stack_local_one >>
  qpat_assum `!k. k = LENGTH d ==> _`
    (stack_apply_aliases [`Abbrev (n = _)`,`Abbrev (f = _)`]
       (qspec_then `v` mp_tac) o CONV_RULE (stack_alias_rule 2 ALL_CONV)) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  `n<>0` by decide_tac >>
  qpat_assum `n<>0` (fn th =>
    CONV_TAC (LAND_CONV (PURE_REWRITE_CONV [EQF_INTRO th,COND_CLAUSES]))) >>
  disch_then (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac
    (CONJUNCTS_THEN2 assume_tac
      (stack_apply_aliases [`Abbrev (n = _)`]
        (map_every assume_tac o CONJUNCTS o CONV_RULE stack_inline_alias) o
       CONV_RULE stack_alias_head)))) >>
  `ann (^Phase v i) = ^PData b H R G B v i` by simp[NoAsms, Abbr `ann`,stack_port_data] >>
  `ann (^Next n z v i) = (b+SUC i,H v (SUC i,0),R v (SUC i,0),
      (SUC i=n /\ need (z v)),G v (SUC i,0),B v (SUC i,0))` by suspend "next" >>
  `^PortSlots q cc (H v (i,0)) F (G v (i,0)) (B v (i,0))` by suspend "slots" >>
  qpat_assum `!i. i<n ==> _` (qspec_then `i` (drule_then (map_every assume_tac o CONJUNCTS))) >>
  suspend "row"
QED

Resume stack_selected_phase[next]:
  Cases_on `SUC i=n` >>
  simp[Abbr `ann`,stack_port_data, FUN_EQ_THM]
QED

Resume stack_selected_phase[slots]:
  BETA_TAC >> irule (iffLR (CONV_RULE (REDEPTH_CONV BETA_CONV) stack_ports_slots)) >>
  qpat_assum `!i. i<=n ==> _` (qspec_then `i` mp_tac) >>
  `i<=n /\ i<>n` by decide_tac >> simp[]
QED

Resume stack_selected_phase[row]:
  `1:num <> 0` by decide_tac >>
  let
    val project = SIMP_RULE bool_ss [LET_THM,FST,SND]
  in
    rule_assum_tac project >>
    qpat_assum `ann (SUC (pair_to_num v),SUC i) = _` (fn src =>
      qpat_assum `ann (if _ then _ else _) = _` (fn dst =>
        qpat_assum `1:num <> 0` (fn nonzero =>
          SIMP_TAC bool_ss [src,dst,nonzero,LET_THM,FST,SND])))
  end >>
  rpt (FIRST [first_assum ACCEPT_TAC, conj_tac]) >>
  qpat_assum `EL (b+i) q = EL i d` (fn fetch =>
    PURE_REWRITE_TAC [fetch] >>
    first_assum (ACCEPT_TAC o PURE_REWRITE_RULE [fetch]))
QED

Finalise stack_selected_phase

(* Keep the occurrence encoding and annotation function fixed while building
   the reachable restriction of the selected port table. *)
val rooted_rows = ``\q cc V e rank pc height need tag boolean edge.
  FINITE V /\ e IN V /\ (!x. x IN V ==> ^Reach edge e x) /\
  ^Rows q cc V rank pc height need tag boolean edge /\
  (!x y. edge x y ==> ^EdgeOK q pc height tag boolean x y)``;

fun stack_project_conv eq = REDEPTH_CONV (FIRST_CONV (BETA_CONV ::
  map REWR_CONV [LET_THM,FST,SND,ratTheory.RAT_OF_NUM_LES,eq]));

fun stack_packet 0 th = [th]
  | stack_packet n th = CONJUNCT1 th :: stack_packet (n-1) (CONJUNCT2 th);

Theorem stack_build_selected_table[local]:
  !p q cc req b m d V pc height rank need tag boolean edge z H R G B
    ih ir it ib init j start.
  !n. n = LENGTH d ==>
  !f. f = splice_pc b m n ==>
  !kept. kept = ^Kept b m pc V ==>
  !id. id = (b,ih,ir,F,it,ib) ==>
  !ann. ann = ^Data (^CData f pc height rank need tag boolean) (^PData b H R G B) id ==>
  !e. e = (if init then ^First else ^Image kept n z start) ==>
  FINITE V /\ 0<m /\ ^Layout p q b m n /\ ^Rows p cc V rank pc height need tag boolean edge /\
  ^PortSelection q cc b m d V pc height rank need tag boolean z H R G B /\
  (if init then j IN kept else start IN kept UNION ^Heads b pc V) /\
  (init ==> ^LocalRow q cc (^Pc ann) (^Ht ann) (^Rk ann) (^Nd ann) (^Tg ann) (^Bl ann)
     ^First (\y. y = ^Copy j)) ==>
  ?W R. ^rooted_rows q cc W e (^Rk ann) (^Pc ann) (^Ht ann) (^Nd ann) (^Tg ann) (^Bl ann) R
Proof
  ntac 27 gen_tac >> stack_intro_aliases [`n`,`f`,`kept`,`id`,`ann`,`e`] >>
  CONV_TAC (REDEPTH_CONV BETA_CONV) >>
  disch_then (map_every assume_tac o stack_packet 6) >>
  `!v. v IN V ==> need v ==> cc.cc_static` by suspend "static" >>
  `!v. v IN kept ==> (!u. edge v u ==> u IN kept UNION ^Heads b pc V) /\
      ^LocalRow q cc (^Pc ann) (^Ht ann) (^Rk ann) (^Nd ann) (^Tg ann) (^Bl ann)
        (^Copy v) (\y. ?u. edge v u /\ y = ^Image kept n z u)` by suspend "copy" >>
  `!v i. v IN ^Heads b pc V /\ i<n ==>
      ^LocalRow q cc (^Pc ann) (^Ht ann) (^Rk ann) (^Nd ann) (^Tg ann) (^Bl ann)
        (^Phase v i) (\y. y = ^Next n z v i)` by suspend "phase" >>
  `!v. v IN ^Heads b pc V ==>
      z v IN kept /\ pc (z v)=b+m /\ rank (z v)<rank v /\
      (let x = ^Image kept n z v in
       ^Pc ann x=b /\ ^Ht ann x=height v /\
       (if n=0 then ^Rk ann x<rank v else ^Rk ann x=rank v) /\
       (!k l o'. ^Tg ann x k=SOME(l,o') ==> ^tr f tag v k=SOME(l,o')) /\
       (!k. ^Bl ann x k ==> boolean v k))` by suspend "head" >>
  suspend "table"
QED

Resume stack_build_selected_table[static]:
  rpt gen_tac >> strip_tac >>
  qpat_assum `(!x. x IN V ==> (need x ==> cc.cc_static) /\ _) /\ _`
    (qspec_then `v` (drule_then (ACCEPT_TAC o CONJUNCT1)) o CONJUNCT1)
QED

Resume stack_build_selected_table[copy]:
  CONV_TAC (REDEPTH_CONV BETA_CONV) >>
  qspecl_then [`p`,`q`,`cc`,`b`,`m`,`d`,`V`,`pc`,`height`,`rank`,`need`,`tag`,`boolean`,
      `edge`,`z`,`H`,`R`,`G`,`B`,`id`]
    (stack_apply_aliases [`Abbrev (n = _)`,`Abbrev (f = _)`,
      `Abbrev (kept = _)`,`Abbrev (ann = _)`] mp_tac)
    (CONV_RULE (stack_aliases 20 (stack_alias_rule 4 stack_inline_alias))
       stack_selected_retained) >>
  (impl_tac >- rpt (FIRST [first_assum ACCEPT_TAC, conj_tac])) >>
  disch_then (ACCEPT_TAC o BETA_RULE)
QED

Resume stack_build_selected_table[phase]:
  CONV_TAC (REDEPTH_CONV BETA_CONV) >>
  `f (b+m)=b+n` by
    ((gvs[])) >>
  qspecl_then [`q`,`cc`,`b`,`m`,`d`,`V`,`pc`,`height`,`rank`,`need`,`tag`,`boolean`,
      `z`,`H`,`R`,`G`,`B`,`id`]
    (stack_apply_aliases [`Abbrev (n = _)`,`Abbrev (f = _)`,
      `Abbrev (ann = _)`] (mp_tac o CONV_RULE (REDEPTH_CONV BETA_CONV)))
    (CONV_RULE (stack_aliases 18 (stack_alias_rule 3 ALL_CONV)) stack_selected_phase) >>
  (impl_tac >- rpt (FIRST [first_assum ACCEPT_TAC, conj_tac])) >>
  disch_then ACCEPT_TAC
QED

Resume stack_build_selected_table[head]:
  CONV_TAC (REDEPTH_CONV BETA_CONV) >> qx_gen_tac `v` >> disch_tac >>
  `v NOTIN kept` by
    (qpat_assum `v IN _` mp_tac >> qpat_assum `0<m` mp_tac >>
     simp[NoAsms, Abbr `kept`]) >>
  qpat_assum `!k. k = LENGTH d ==> _`
    (stack_apply_aliases [`Abbrev (n = _)`,`Abbrev (f = _)`]
      (qspec_then `v` mp_tac) o CONV_RULE (stack_alias_rule 2 ALL_CONV)) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  `z v IN kept` by simp[Abbr `kept`] >>
  Cases_on `n=0`
  >- (qpat_x_assum `if n=0 then _ else _` (fn th =>
        qpat_assum `n=0` (fn eq =>
          map_every assume_tac (CONJUNCTS (SIMP_RULE bool_ss [eq] th)))) >>
      `f (b+m)=b+n` by simp[Abbr `f`,asmSpliceTheory.splice_pc_def] >>
      `ann (SUC (pair_to_num (z v)),0) =
        (f (pc (z v)),height (z v),rank (z v),need (z v),^tr f tag (z v),boolean (z v))` by
        simp[NoAsms, Abbr `ann`, stack_port_data, LET_THM] >>
      simp[LET_THM] >>
      simp[NoAsms, pairTheory.EXISTS_PROD] >>
      rpt strip_tac >>
      qpat_assum `!k l i. tag (z v) k = SOME (l,i) ==> _` drule >>
      disch_tac >> goal_assum (drule_at Any) >> simp[]) >>
  qpat_x_assum `if n=0 then _ else _` (fn th =>
    qpat_assum `n<>0` (fn neq =>
      map_every assume_tac (CONJUNCTS (SIMP_RULE bool_ss
        [neq, UNWIND_FORALL_THM2] th)))) >>
  `ann (SUC (pair_to_num v),1) = ^PData b H R G B v 0` by
    simp[NoAsms, Abbr `ann`, stack_port_data, LET_THM] >>
  simp[LET_THM]
QED

(* Keep the five fields whose names are shared with the caller. *)
val stack_table_formals = List.take (fst (strip_forall (concl stack_selected_port_table)), 26);
val stack_table_schema =
  let
    val expose = stack_alias_rule 2 (stack_inline_lets 6
      (stack_alias_rule 1 (stack_inline_lets 3
        (stack_alias_rule 1 (stack_inline_lets 1
          (stack_alias_rule 1 (stack_inline_lets 16 ALL_CONV)))))))
  in
    CONV_RULE expose (SPECL stack_table_formals stack_selected_port_table)
  end;

(* Instantiate the unquantified rule by name, with an explicit array view. *)
fun stack_table_instance (asl,w) =
  let
    val vars = free_varsl (w::asl)
    fun lookup name = case List.find (fn v => fst (dest_var v) = name) vars of
        SOME v => v
      | NONE => raise Fail ("stack table argument missing: " ^ name)
    fun embed n = mk_comb (``rat$rat_of_num``, n)
    fun rank_view () =
      let val v = mk_var ("v", ``:num#num``)
      in mk_abs (v, embed (mk_comb (lookup "rank", v))) end
    fun phase_view formal name project =
      let
        val (_, [dom, rest]) = Type.dest_type (type_of formal)
        val (_, [idx, _]) = Type.dest_type rest
        val v = mk_var ("v", dom)
        val i = mk_var ("i", idx)
        val vi = pairSyntax.mk_pair (i, ``0:num``)
      in mk_abs (v, mk_abs (i, project (list_mk_comb (lookup name, [v,vi])))) end
    fun argument formal =
      let
        val (name, ty) = dest_var formal
        val arg = case name of
            "old" => lookup "edge"
          | "req" => ``(ARB:asm_state).as_requests``
          | "rank" => rank_view ()
          | "ir" => embed (lookup "ir")
          | "ph_h" => phase_view formal "H" I
          | "ph_r" => phase_view formal "R" embed
          | "ph_t" => phase_view formal "G" I
          | "ph_b" => phase_view formal "B" I
          | _ => lookup name
      in
        if type_of arg = ty then formal |-> arg
        else raise Fail ("stack table argument " ^ name ^ ": expected " ^
          Parse.type_to_string ty ^ ", got " ^ Parse.term_to_string arg ^ " : " ^
          Parse.type_to_string (type_of arg))
      end
  in
    CONV_RULE (REDEPTH_CONV BETA_CONV) (INST (map argument stack_table_formals) stack_table_schema)
  end;

(* Lift just the rank field while leaving the occurrence data abstract. *)
val StackRatData = ``\(a:num#num#num#bool#(num->(string#num)option)#(num->bool)).
  (FST a, FST (SND a), rat$rat_of_num (FST (SND (SND a))), SND (SND (SND a)))``;
val StackRatAnn = ``\(ann:(num#num)->num#num#num#bool#(num->(string#num)option)#(num->bool)) x.
  ^StackRatData (ann x)``;

(* The worker packages canonical jump targets under a nested existential. *)
val stack_table_project = stack_project_conv
  (CONJUNCT1 ratTheory.RAT_EQ_NUM_CALCULATE) THENC
  DEPTH_CONV (HO_REWR_CONV (GSYM RIGHT_EXISTS_AND_THM)) THENC
  DEPTH_CONV (REWR_CONV CONJ_ASSOC);

val stack_project_assumption = ACCEPT_TAC o CONV_RULE stack_table_project;
fun stack_accept_row th = CONV_TAC stack_table_project >> stack_project_assumption th;

Resume stack_build_selected_table[table]:
  `Abbrev (^StackRatData id = (b,ih,rat$rat_of_num ir,F,it,ib))` by
    simp[markerTheory.Abbrev_def, Abbr `id`] >>
  `Abbrev (^StackRatAnn ann = \x.
     if FST x=0 then ^StackRatData id else
       let v = num_to_pair (PRE (FST x)) in
       if SND x=0 then
         (f (pc v),height v,rat$rat_of_num (rank v),need v,^tr f tag v,boolean v)
       else (b+PRE (SND x),H v (PRE (SND x),0),rat$rat_of_num (R v (PRE (SND x),0)),F,
         G v (PRE (SND x),0),B v (PRE (SND x),0)))` by
    (qpat_assum `Abbrev (ann = _)` (fn h =>
       simp[NoAsms, FUN_EQ_THM, LET_THM, markerTheory.Abbrev_def,
            REWRITE_RULE [markerTheory.Abbrev_def] h]) >>
     gen_tac >> Cases_on `FST x=0`
     >- (pop_assum (fn h => simp[NoAsms,h,Abbr `id`])) >>
     Cases_on `SND x=0` >>
     pop_assum (fn h => pop_assum (fn j => simp[NoAsms,h,j,combinTheory.C_DEF]))) >>
  (fn goal => mp_tac (stack_table_instance goal) goal) >>
  disch_then (fn th => fn goal as (asl,_) =>
    let
      val normalize = REDEPTH_CONV (FIRST_CONV [REWR_CONV LET_THM,BETA_CONV])
      fun matches rhs h =
        let val (l,r) = dest_eq (rand (concl h))
        in aconv rhs (rhs_of r) end handle HOL_ERR _ => false
      and rhs_of t = rhs (concl (normalize t)) handle UNCHANGED => t
      val equations = map ASSUME (List.filter (can (dest_eq o rand)) asl)
      fun consume 0 th = th
        | consume n th =
          let
            val guard = fst (dest_imp (snd (dest_forall (concl th))))
            val target = rhs_of (rhs (rand guard))
            val h = case List.find (matches target) equations of
                SOME h => h
              | NONE => raise Fail ("unmatched table guard: " ^ Parse.term_to_string guard)
            val alias = lhs (rand (concl h))
          in
            consume (n-1) (MP (CONV_RULE (LAND_CONV normalize) (SPEC alias th))
                              (CONV_RULE normalize h))
          end
    in
      mp_tac (CONV_RULE (stack_project_conv (CONJUNCT1 ratTheory.RAT_EQ_NUM_CALCULATE))
              (consume 5 th)) goal
    end) >>
  (impl_tac >-
    (ntac 2 (conj_tac >- first_assum ACCEPT_TAC) >>
     conj_tac >-
       (qx_gen_tac `src` >> qx_gen_tac `dst` >> strip_tac >>
        qpat_assum `!x. x IN kept ==> (!y. edge x y ==> _) /\ _`
          (qspec_then `src` mp_tac) >>
        (impl_tac >- first_assum ACCEPT_TAC) >>
        disch_then (qspec_then `dst` mp_tac o CONJUNCT1) >>
        (impl_tac >- first_assum ACCEPT_TAC) >>
        disch_then (ACCEPT_TAC o CONV_RULE (REDEPTH_CONV BETA_CONV))) >>
     conj_tac >- first_assum (ACCEPT_TAC o CONV_RULE (stack_project_conv
       (CONJUNCT1 ratTheory.RAT_EQ_NUM_CALCULATE))) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >-
       (qx_gen_tac `src` >> disch_tac >>
        qpat_assum `!x. x IN kept ==> (!y. edge x y ==> _) /\ _`
          (qspec_then `src` mp_tac) >>
        (impl_tac >- first_assum ACCEPT_TAC) >>
        disch_then (stack_accept_row o CONJUNCT2)) >>
     conj_tac >- (CONV_TAC stack_table_project >> first_assum stack_project_assumption) >>
     CONV_TAC stack_table_project >> first_assum stack_project_assumption)) >>
  disch_then (X_CHOOSE_THEN ``live:(num#num)->bool``
    (X_CHOOSE_THEN ``live_edge:(num#num)->(num#num)->bool`` (fn th =>
      let val packets = stack_packet 7 th
      in map_every (fn i => assume_tac (List.nth (packets,i))) [0,1,2,3,6] end))) >>
  qexistsl [`live`,`live_edge`] >>
  ntac 3 (conj_tac >- first_assum ACCEPT_TAC) >>
  conj_tac >-
    (CONV_TAC stack_table_project >>
     qpat_assum `( !x. x IN live ==> _) /\ _` (fn th =>
       let fun off_first tm =
         let val (dest,tail) = dest_exists tm
             val (off,body) = dest_exists tail
             val (lookup,_) = dest_conj body
         in if free_in off lookup andalso not (free_in dest lookup)
            then SWAP_EXISTS_CONV tm else raise UNCHANGED end
       in stack_project_assumption (CONV_RULE (DEPTH_CONV off_first) th) end)) >>
  map_every qx_gen_tac [`src`,`dst`] >> disch_tac >>
  qpat_assum `!x y. live_edge x y ==> x IN live /\ y IN live /\ _ /\ _` (qspecl_then [`src`,`dst`] mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (stack_accept_row o CONJUNCT2 o CONJUNCT2 o CONJUNCT2)
QED

Finalise stack_build_selected_table

(* A replayed cut and its root demands use the same table returned by the
   selected-port builder. The initial row is inactive in the other cases. *)
Theorem stack_attach_replayed_cut[local]:
  !orig s data req_bound p q cc req b m d V pc height rank need tag boolean edge
    z H R G B ih ir it ib init dest start j u.
  !n. n = LENGTH d ==>
  !f. f = splice_pc b m n ==>
  !kept. kept = ^Kept b m pc V ==>
  !id. id = (b,ih,ir,F,it,ib) ==>
  !ann. ann = ^Data (^CData f pc height rank need tag boolean) (^PData b H R G B) id ==>
  !root. root = (if init then ^First else ^Image kept n z start) ==>
  ^Entry orig s data q /\ req <<= req_bound /\
  FINITE V /\ 0<m /\ ^Layout p q b m n /\ ^Rows p cc V rank pc height need tag boolean edge /\
  ^PortSelection q cc b m d V pc height rank need tag boolean z H R G B /\
  (if init then dest IN kept else start IN kept UNION ^Heads b pc V) /\
  (init ==> ^LocalRow q cc (^Pc ann) (^Ht ann) (^Rk ann) (^Nd ann) (^Tg ann) (^Bl ann)
     ^First (\y. y = ^Copy dest)) /\
  sym_steps q (asm_data_env orig (assemble orig ++ data)) j (sym_init s) = SymOK u /\
  u.sym_base.as_pc = ^Pc ann root /\ LENGTH u.sym_stack = ^Ht ann root /\
  u.sym_base.as_call_ctx = cc /\ u.sym_base.as_requests = req /\
  ^Just u (^Tg ann) (^Bl ann) root ==>
  ^Pending orig s data req_bound q
Proof
  ntac 33 gen_tac >>
  stack_intro_aliases [`n`,`f`,`kept`,`id`,`ann`,`root`] >> BETA_TAC >>
  disch_then (map_every assume_tac o stack_packet 14) >>
  qspecl_then [`p`,`q`,`cc`,`req`,`b`,`m`,`d`,`V`,`pc`,`height`,`rank`,`need`,`tag`,
    `boolean`,`edge`,`z`,`H`,`R`,`G`,`B`,`ih`,`ir`,`it`,`ib`,`init`,`dest`,`start`]
    (stack_apply_aliases [`Abbrev (n = _)`,`Abbrev (f = _)`,`Abbrev (kept = _)`,
      `Abbrev (id = _)`,`Abbrev (ann = _)`,`Abbrev (root = _)`]
      (mp_tac o BETA_RULE) o CONV_RULE (stack_alias_rule 6 ALL_CONV))
    stack_build_selected_table >>
  (impl_tac >- rpt (FIRST [first_assum ACCEPT_TAC, conj_tac])) >>
  disch_then (X_CHOOSE_THEN ``live:(num#num)->bool``
    (X_CHOOSE_THEN ``live_edge:(num#num)->(num#num)->bool``
      (map_every (assume_tac o BETA_RULE) o stack_packet 4))) >>
  qspecl_then [`orig`,`s`,`data`,`req_bound`,`q`,`j`,`u`,`cc`,`req`,`live`,`root`,
      `^Rk ann`,`^Pc ann`,`^Ht ann`,`^Nd ann`,`^Tg ann`,`^Bl ann`,`live_edge`]
    (mp_tac o CONV_RULE (REDEPTH_CONV BETA_CONV)) stack_selected_table_restart >>
  (impl_tac >-
    (rpt (FIRST [first_assum ACCEPT_TAC, conj_tac]) >> simp[])) >>
  disch_then ACCEPT_TAC
QED

Theorem stack_attach_replayed_image[local]:
  !orig s data req_bound p q cc req b m d V pc height rank need tag boolean edge
    z H R G B v j u.
  !f. f = splice_pc b m (LENGTH d) ==>
  ^Entry orig s data q /\ req <<= req_bound /\
  FINITE V /\ 0<m /\ ^Layout p q b m (LENGTH d) /\
  ^Rows p cc V rank pc height need tag boolean edge /\
  ^PortSelection q cc b m d V pc height rank need tag boolean z H R G B /\
  v IN ^Kept b m pc V UNION ^Heads b pc V /\
  sym_steps q (asm_data_env orig (assemble orig ++ data)) j (sym_init s) = SymOK u /\
  u.sym_base.as_pc = f (pc v) /\ LENGTH u.sym_stack = height v /\
  u.sym_base.as_call_ctx = cc /\ u.sym_base.as_requests = req /\
  ^Just u tag boolean v ==>
  ^Pending orig s data req_bound q
Proof
  ntac 27 gen_tac >> CONV_TAC stack_inline_alias >> BETA_TAC >>
  disch_then (fn th =>
    let val ps = stack_packet 13 th
        val layout = stack_packet 8 (CONV_RULE stack_inline_alias (List.nth (ps,4)))
    in map_every assume_tac
      (List.nth (layout,6) :: List.nth (layout,7) :: CONJUNCT1 (List.nth (ps,5)) :: ps) end) >>
  qspecl_then [`q`,`cc`,`b`,`m`,`d`,`V`,`pc`,`height`,`rank`,`need`,`tag`,`boolean`,
    `z`,`H`,`R`,`G`,`B`,`(b,0:num,0:num,F,(\k:num. NONE:(string#num)option),\k:num. F)`,`v`]
    (mp_tac o CONV_RULE (stack_inline_lets 5 ALL_CONV THENC REDEPTH_CONV BETA_CONV))
    stack_image_fields >>
  (impl_tac >-
    (ntac 3 (conj_tac >- first_assum ACCEPT_TAC) >>
     conj_tac >- (gen_tac >> disch_tac >>
       qpat_assum `!x. x IN V ==> (need x ==> cc.cc_static) /\ _`
         (drule_then (ACCEPT_TAC o CONJUNCT1))) >>
     first_assum ACCEPT_TAC)) >>
  disch_then (map_every assume_tac o stack_packet 5) >>
  qspecl_then [`orig`,`s`,`data`,`req_bound`,`p`,`q`,`cc`,`req`,`b`,`m`,`d`,`V`,`pc`,
    `height`,`rank`,`need`,`tag`,`boolean`,`edge`,`z`,`H`,`R`,`G`,`B`,
    `0`,`0`,`\k:num. NONE:(string#num)option`,`\k:num. F`,`F`,`v`,`v`,`j`,`u`]
    (mp_tac o PURE_REWRITE_RULE [COND_CLAUSES, F_IMP] o
      CONV_RULE (stack_inline_lets 6 ALL_CONV THENC REDEPTH_CONV BETA_CONV))
    stack_attach_replayed_cut >>
  (impl_tac >-
    (ntac 8 (conj_tac >- first_assum ACCEPT_TAC) >>
     conj_tac >- rewrite_tac[] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     ntac 2 (conj_tac >- simp[]) >>
     ntac 2 (conj_tac >- first_assum ACCEPT_TAC) >>
     qpat_assum `(!k l o'. tag v k = SOME(l,o') ==> _) /\ _`
       (map_every assume_tac o CONJUNCTS) >>
     conj_tac >-
       (rpt gen_tac >> disch_tac >>
        qpat_assum `!k l o'. _ ==> ?i. tag v k = SOME(l,i) /\ _`
          (drule_then strip_assume_tac) >>
        qpat_assum `!k l i. tag v k = SOME(l,i) ==> _` (drule_then ACCEPT_TAC)) >>
     gen_tac >> disch_tac >>
     qpat_assum `!k. _ ==> boolean v k` (drule_then assume_tac) >>
     qpat_assum `!k. boolean v k ==> _` (drule_then ACCEPT_TAC))) >>
  disch_then ACCEPT_TAC
QED

Theorem stack_replayed_nonstrict[local]:
  !pre w d tail orig s data req_bound p q cc req V pc height rank need tag boolean edge
   z H R G B e k u.
   !b. b = LENGTH pre ==>
  !m. m = LENGTH w ==>
   !f. f = splice_pc b m (LENGTH d) ==>
   ^window w d /\ p=pre++w++tail /\ q=pre++d++tail /\
   ^Entry orig s data p /\ ^Entry orig s data q /\ req <<= req_bound /\
   FINITE V /\ ^Layout p q b m (LENGTH d) /\
   ^Rows p cc V rank pc height need tag boolean edge /\
   ^PortSelection q cc b m d V pc height rank need tag boolean z H R G B /\
   e IN V /\ ~(b<pc e /\ pc e<b+m) /\
   sym_steps p (asm_data_env orig (assemble orig ++ data)) k (sym_init s) = SymOK u /\
   u.sym_base.as_pc=pc e /\ LENGTH u.sym_stack=height e /\
   u.sym_base.as_call_ctx=cc /\ u.sym_base.as_requests=req /\ ^Just u tag boolean e ==>
   ^Pending orig s data req_bound q
Proof
  ntac 28 gen_tac >> stack_intro_aliases [`b`,`m`,`f`] >> BETA_TAC >>
  disch_then (fn th =>
    let val ps = stack_packet 17 th in
      map_every assume_tac (CONJUNCTS (List.nth (ps,3)) @ ps)
    end) >>
  `?j. sym_steps q (asm_data_env orig (assemble orig ++ data)) j (sym_init s) =
       SymOK (sym_with_pc (f (pc e)) u)` by
    (qabbrev_tac `env = asm_data_env orig (assemble orig ++ data)` >>
     qspecl_then [`pre`,`w`,`d`,`tail`,`env`,`s`,`k`,`u`]
       (mp_tac o SIMP_RULE bool_ss [LET_THM]) stack_peephole_one_stopped_prefix >>
     (impl_tac >-
       (conj_tac >- (pure_rewrite_tac [GSYM (BETA_RULE (cj 1 stack_window_rule_form))] >> first_assum ACCEPT_TAC) >>
        qpat_assum `p = pre ++ w ++ tail` (SUBST1_TAC o SYM) >>
        rpt conj_tac >> first_assum ACCEPT_TAC)) >>
     `~(LENGTH pre < u.sym_base.as_pc /\
        u.sym_base.as_pc < LENGTH pre + LENGTH w)` by
       (qpat_assum `Abbrev (b = _)` (fn hb =>
          qpat_assum `Abbrev (m = _)` (fn hm =>
            qpat_assum `u.sym_base.as_pc = pc e` (fn hpc =>
              qpat_assum `~(b < pc e /\ pc e < b+m)`
                (ACCEPT_TAC o PURE_REWRITE_RULE
                   (GSYM hpc :: map (REWRITE_RULE [markerTheory.Abbrev_def]) [hb,hm])))))) >>
     disch_then (fn th =>
       qpat_assum `~(LENGTH pre < u.sym_base.as_pc /\ _)` (fn hg =>
         let val replay = MP (CONJUNCT2 (CONV_RULE (REWR_CONV COND_EXPAND_IMP) th)) hg
         in
           qpat_assum `Abbrev (b = _)` (fn hb =>
             qpat_assum `Abbrev (m = _)` (fn hm =>
               qpat_assum `Abbrev (f = _)` (fn hf =>
                 qpat_assum `u.sym_base.as_pc = pc e` (fn hpc =>
                   qpat_assum `q = pre ++ d ++ tail` (fn hq =>
                     let val [b_eq,m_eq,f_eq] =
                           map (REWRITE_RULE [markerTheory.Abbrev_def]) [hb,hm,hf]
                         val unfold_f = PURE_REWRITE_RULE [b_eq,m_eq] f_eq
                     in ACCEPT_TAC
                       (PURE_REWRITE_RULE [GSYM unfold_f,GSYM hq,hpc] replay)
                     end)))))
         end))) >>
  `e IN ^Kept b m pc V UNION ^Heads b pc V` by
    (simp[] >> decide_tac) >>
  `0<m` by
    (simp[Abbr `m`] >> irule (BETA_RULE (cj 2 stack_window_rule_form)) >>
     qexists `d` >> first_assum ACCEPT_TAC) >>
  qspecl_then [`orig`,`s`,`data`,`req_bound`,`p`,`q`,`cc`,`req`,`b`,`m`,`d`,`V`,`pc`,
    `height`,`rank`,`need`,`tag`,`boolean`,`edge`,`z`,`H`,`R`,`G`,`B`,`e`,`j`,
    `sym_with_pc (f (pc e)) u`]
    (stack_apply_aliases [`Abbrev (f = _)`] (mp_tac o BETA_RULE))
    (CONV_RULE (stack_aliases 27 stack_alias_head) stack_attach_replayed_image) >>
  (impl_tac >-
    (ntac 4 (conj_tac >- first_assum ACCEPT_TAC) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     ntac 2 (conj_tac >- first_assum ACCEPT_TAC) >>
     conj_tac >- qpat_assum `e IN _ UNION _` (ACCEPT_TAC o BETA_RULE) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     simp[asmSymPcTheory.sym_with_pc_def] >> first_assum ACCEPT_TAC)) >>
  disch_then ACCEPT_TAC
QED

(* A strict permutation/POP cut restarts at its retained exit. *)
Theorem stack_replayed_shuffle[local]:
  !pre w d tail orig s data req_bound p q cc req V pc height rank need tag boolean edge
    z H R G B e k t u.
  !b. b = LENGTH pre ==>
  !m. m = LENGTH w ==>
  !f. f = splice_pc b m (LENGTH d) ==>
  ^window w d /\ ~^comm w d /\ p=pre++w++tail /\ q=pre++d++tail /\
  ^Entry orig s data p /\ ^Entry orig s data q /\ req <<= req_bound /\
  FINITE V /\ ^Layout p q b m (LENGTH d) /\
  ^Rows p cc V rank pc height need tag boolean edge /\
  ^PortSelection q cc b m d V pc height rank need tag boolean z H R G B /\
  e IN V /\ b<pc e /\ pc e<b+m /\
  sym_steps p (asm_data_env orig (assemble orig ++ data)) k (sym_init s) = SymOK u /\
  asm_sym_rel p (asm_data_env p (assemble p ++ data)) t u /\
  u.sym_base.as_pc=pc e /\ LENGTH u.sym_stack=height e /\
  ^Shape p cc req pc height need tag boolean e t /\ ^Just u tag boolean e ==>
  ^Pending orig s data req_bound q
Proof
  ntac 29 gen_tac >> stack_intro_aliases [`b`,`m`,`f`] >> BETA_TAC >>
  disch_then (fn th =>
    let val ps = stack_packet 20 th
        val [slots,flows,dispatch] = CONJUNCTS (List.nth (ps,9))
    in
      map_every assume_tac
        (List.concat (map (CONJUNCTS o (fn i => List.nth (ps,i))) [4,5,18,19]) @
         [slots,flows,dispatch] @ ps) >>
      mk_asm "shuffle-window" (hd ps) >>
      mk_asm "shuffle-dispatch" (SIMP_RULE bool_ss [LET_THM,CONJ_ASSOC] dispatch) >>
      mk_asm "shuffle-flows" (SIMP_RULE bool_ss [LET_THM,CONJ_ASSOC] flows)
    end) >>
  qspecl_then [`pre`,`w`,`d`,`tail`,`orig`,`data`,`s`,`k`,`u`,`t`,`e`,`V`,`pc`,
    `cc`,`req`,`height`,`need`,`tag`,`boolean`,`rank`,`edge`]
    (fn th =>
      qpat_assum `p = pre ++ w ++ tail` (fn hp =>
      qpat_assum `q = pre ++ d ++ tail` (fn hq =>
      qpat_assum `Abbrev (b = _)` (fn hb =>
      qpat_assum `Abbrev (m = _)` (fn hm =>
      qpat_assum `Abbrev (f = _)` (fn hf =>
        mp_tac (PURE_REWRITE_RULE
          (map (GSYM o REWRITE_RULE [markerTheory.Abbrev_def]) [hp,hq,hb,hm,hf]) th)))))))
    (Q.GENL [`pre`,`pat`,`repl`,`tail`,`orig`,`data`,`s`,`n`,`ss`,`t`,`e`,`V`,`pc`,
      `cc`,`req`,`height`,`need`,`tag`,`boolean`,`rank`,`edge`]
      (CONV_RULE (stack_inline_lets 5 ALL_CONV) stack_shuffle_strict_endpoint)) >>
  (impl_tac >-
    (conj_tac >-
      (qpat_assum `~(?a. asm_commutative_op a /\ w = [AsmOp "SWAP1";a] /\ d = [a])` mp_tac >>
       asm "shuffle-window" mp_tac >>
       POP_ASSUM_LIST (K ALL_TAC) >> simp[LET_THM] >> metis_tac[]) >>
     SIMP_TAC bool_ss [LET_THM, CONJ_ASSOC] >>
     RULE_ASSUM_TAC (SIMP_RULE bool_ss [LET_THM, CONJ_ASSOC]) >>
     rpt (FIRST [first_assum ACCEPT_TAC, conj_tac]) >>
     TRY (sym_tac >> first_assum ACCEPT_TAC) >>
     TRY (qpat_assum `LENGTH u.sym_stack = height e` (SUBST1_TAC o SYM) >>
          first_assum ACCEPT_TAC) >>
     TRY (qx_gen_tac `x` >> disch_tac >>
          asm "shuffle-dispatch" (qspec_then `x` mp_tac) >>
          Cases_on `EL (pc x) p` >> simp[CONJ_ASSOC] >>
          rename1 `EL (pc x) p = AsmOp name` >>
          Cases_on `name = "INVALID"` >> Cases_on `name = "REVERT"` >>
          simp[CONJ_ASSOC] >> NO_TAC) >>
     qx_gen_tac `x` >> qx_gen_tac `y` >> disch_tac >>
     asm "shuffle-flows" (qspecl_then [`x`,`y`] mp_tac) >>
     Cases_on `EL (pc x) p` >> simp[] >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     rpt (CASE_TAC >> simp[]) >> metis_tac[])) >>
  disch_then (qx_choose_then `exit` (qx_choose_then `j` (qx_choose_then `out`
    (qx_choose_then `tq` (qx_choose_then `ops` (qx_choose_then `path` (fn th =>
      let val ps = stack_packet 11 th
      in map_every (fn i => assume_tac (BETA_RULE (List.nth (ps,i))))
           [2,3,5,6,7,8,9] >> mk_asm "exit-just" (BETA_RULE (List.nth (ps,10))) end))))))) >>
  qspecl_then [`orig`,`s`,`data`,`req_bound`,`p`,`q`,`cc`,`req`,`b`,`m`,`d`,`V`,
    `pc`,`height`,`rank`,`need`,`tag`,`boolean`,`edge`,`z`,`H`,`R`,`G`,`B`,`exit`,`j`,`out`]
    (stack_apply_aliases [`Abbrev (f = _)`] (mp_tac o BETA_RULE))
    (CONV_RULE (stack_aliases 27 stack_alias_head) stack_attach_replayed_image) >>
  (impl_tac >-
    (rpt (FIRST [first_assum ACCEPT_TAC, conj_tac]) >>
     TRY (qpat_assum `b < pc e` mp_tac >> qpat_assum `pc e < b+m` mp_tac >> decide_tac) >>
     TRY (simp[IN_UNION] >> NO_TAC) >>
     asm "exit-just" (fn th =>
       map_every (assume_tac o CONV_RULE (REDEPTH_CONV BETA_CONV))
         (tl (CONJUNCTS th))) >>
     rpt gen_tac >> disch_tac
     >- (rename1 `tag exit slot = SOME (lab,old)` >>
         qpat_assum `!k l o'. OPTION_MAP _ (tag exit k) = SOME(l,o') ==> _`
          (qspecl_then [`slot`,`lab`,`f old`] mp_tac) >> simp[]) >>
     qpat_assum `!k. boolean exit k ==> _` drule >> simp[])) >>
  disch_then ACCEPT_TAC
QED

(* At a strict commutative cut the binary instruction remains pending. *)
Theorem stack_replayed_comm[local]:
  !pre a tail orig s data req_bound p q cc req V pc height rank need tag boolean edge
    z H R G B e k u.
  !b. b = LENGTH pre ==>
  ^Entry orig s data p /\ ^Entry orig s data q /\ req <<= req_bound /\
  asm_commutative_op a /\ p=pre++[AsmOp "SWAP1";a]++tail /\ q=pre++[a]++tail /\
  FINITE V /\ ^Layout p q b 2 1 /\
  ^Rows p cc V rank pc height need tag boolean edge /\
  ^Open p cc req V {} rank pc height need tag boolean edge /\
  ^PortSelection q cc b 2 [a] V pc height rank need tag boolean z H R G B /\
  e IN V /\ pc e=b+1 /\
  sym_steps p (asm_data_env orig (assemble orig ++ data)) k (sym_init s) = SymOK u /\
  u.sym_base.as_pc=pc e /\ LENGTH u.sym_stack=height e /\
  u.sym_base.as_call_ctx=cc /\ u.sym_base.as_requests=req /\ ^Just u tag boolean e ==>
  ^Pending orig s data req_bound q
Proof
  ntac 27 gen_tac >> stack_intro_aliases [`b`] >> BETA_TAC >>
  disch_then (fn th =>
    let val ps = stack_packet 18 th
    in map_every assume_tac (List.concat (map (CONJUNCTS o (fn i => List.nth (ps,i)))
         [0,1,8]) @ ps) >> mk_asm "comm-open" (List.nth (ps,9)) end) >>
  qpat_assum `p = _` (fn hp =>
  qpat_assum `q = _` (fn hq =>
  qpat_assum `Abbrev (b = _)` (fn hb =>
    qspecl_then [`pre`,`a`,`tail`,`asm_data_env orig (assemble orig ++ data)`,`s`,`k`,`u`,
      `cc`,`req`,`V`,`rank`,`pc`,`height`,`need`,`tag`,`boolean`,`edge`,`e`]
      (mp_tac o PURE_REWRITE_RULE
        (map (GSYM o REWRITE_RULE [markerTheory.Abbrev_def]) [hp,hq,hb]) o
        CONV_RULE (stack_inline_lets 10 ALL_CONV))
      stack_comm_strict_endpoint_row))) >>
  (impl_tac >- suspend "endpoint_input") >>
  suspend "attach"
QED

Resume stack_replayed_comm[endpoint_input]:
  CONV_TAC (REDEPTH_CONV BETA_CONV) >>
  ntac 10 (conj_tac >- (first_assum ACCEPT_TAC ORELSE (sym_tac >> first_assum ACCEPT_TAC))) >>
  conj_tac >-
    (SIMP_TAC (srw_ss()) [LET_THM, CONJ_ASSOC] >>
     asm "comm-open" (ACCEPT_TAC o SIMP_RULE (srw_ss()) [LET_THM, CONJ_ASSOC])) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qpat_assum `!x. x IN V ==> (need x ==> _) /\ _`
    (qspec_then `e` (fn th =>
      qpat_assum `e IN V` (ACCEPT_TAC o CONJUNCT2 o MP th)))
QED

Resume stack_replayed_comm[attach]:
  disch_then (qx_choose_then `j` (qx_choose_then `out` (qx_choose_then `exit`
    (qx_choose_then `name` (fn th =>
      let val ps = map (SIMP_RULE bool_ss [LET_THM,FST,arithmeticTheory.ADD_CLAUSES])
                     (stack_packet 23 (CONV_RULE (stack_inline_lets 4 ALL_CONV) th))
      in map_every (fn i => assume_tac (List.nth (ps,i)))
           ([0,1,2,3,4,5,8,10,11,12,13,14,15,17,18,19,20,21]) >>
         mk_asm "comm-root-just" (List.nth (ps,6)) >>
         mk_asm "comm-root-slots" (List.nth (ps,7)) >>
         mk_asm "comm-row-flow" (List.nth (ps,22)) end))))) >>
  qabbrev_tac `it = \k. if k<2 then NONE else ^tr (splice_pc b 2 1) tag e k` >>
  qabbrev_tac `ib = \k. 2<=k /\ boolean e k` >>
  qabbrev_tac `ann = ^Data (^CData (splice_pc b 2 1) pc height rank need tag boolean)
      (^PData b H R G B) (b,height e,rank e,F,it,ib)` >>
  `ann ^First = (b,height e,rank e,F,it,ib)` by simp[NoAsms, Abbr `ann`,stack_port_data] >>
  `ann (^Copy exit) = ^CData (splice_pc b 2 1) pc height rank need tag boolean exit`
    by simp[NoAsms, Abbr `ann`,stack_port_data] >>
  Q.SUBGOAL_THEN
    `^LocalRow q cc (^Pc ann) (^Ht ann) (^Rk ann) (^Nd ann) (^Tg ann) (^Bl ann)
      ^First (\y. y = ^Copy exit)` (mk_asm "stack-initial-row") >-
    suspend "initial_row" >>
  suspend "restart"
QED

Resume stack_replayed_comm[initial_row]:
  qspecl_then [`q`,`cc`,`^Pc ann`,`^Ht ann`,`^Rk ann`,`^Nd ann`,`^Tg ann`,`^Bl ann`,
    `^First`,`^Copy exit`] (mp_tac o BETA_RULE) stack_local_one >>
  (impl_tac >-
    (qpat_assum `ann ^First = _` (fn h0 =>
       qpat_assum `ann (^Copy exit) = _` (fn h1 =>
         SIMP_TAC bool_ss [BETA_RULE h0,BETA_RULE h1,FST,SND])) >>
     conj_tac >-
       (SIMP_TAC bool_ss [Abbr `it`, Abbr `ib`, LET_THM] >>
        asm "comm-root-slots" (fn h => POP_ASSUM_LIST (K (mp_tac h))) >>
        metis_tac[]) >>
     ntac 3 (conj_tac >- (first_assum ACCEPT_TAC ORELSE (sym_tac >> first_assum ACCEPT_TAC))) >>
     conj_tac >-
       (qexists `name` >>
        qpat_assum `EL b q = AsmOp name` (fn hins =>
        qpat_assum `ALOOKUP dup_table name = NONE` (fn hdup =>
        qpat_assum `ALOOKUP swap_table name = NONE` (fn hswap =>
          simp[NoAsms,hins,hdup,hswap]))) >>
        qexists `1` >>
        qpat_assum `asm_op_arity name = 2` (fn ha =>
        qpat_assum `height exit = height e - 1` (fn hh =>
        qpat_assum `static_abort_straight name 1` (fn hn =>
        qpat_assum `2 <= height e` (fn h2 =>
          simp[NoAsms, Abbr `it`,ha,hh,hn,h2] >> decide_tac))))) >>
     SIMP_TAC bool_ss [LET_THM,FST,Abbr `it`,Abbr `ib`,arithmeticTheory.ONE,numTheory.NOT_SUC] >>
     asm "comm-row-flow" (ACCEPT_TAC o SIMP_RULE bool_ss
       [LET_THM,arithmeticTheory.ONE,numTheory.NOT_SUC]))) >>
  disch_then (fn h => CONV_TAC (REDEPTH_CONV BETA_CONV) >>
    ACCEPT_TAC (CONV_RULE (REDEPTH_CONV BETA_CONV) h))
QED

Resume stack_replayed_comm[restart]:
  qspecl_then [`orig`,`s`,`data`,`req_bound`,`p`,`q`,`cc`,`req`,`b`,`2`,`[a]`,`V`,`pc`,
    `height`,`rank`,`need`,`tag`,`boolean`,`edge`,`z`,`H`,`R`,`G`,`B`,
    `height e`,`rank e`,`it`,`ib`,`T`,`exit`,`e`,`j`,`out`]
    (mp_tac o CONV_RULE (REDEPTH_CONV BETA_CONV) o
      PURE_REWRITE_RULE [LENGTH,GSYM arithmeticTheory.ONE,COND_CLAUSES,IMP_CLAUSES])
    stack_attach_replayed_cut >>
  map_every (fn (term,solve) =>
    disch_then (qspec_then term mp_tac) >> (impl_tac >- solve))
    [(`1`, REFL_TAC), (`splice_pc b 2 1`, REFL_TAC),
     (`^Kept b 2 pc V`, BETA_TAC >> REFL_TAC),
     (`(b,height e,rank e,F,it,ib)`, REFL_TAC),
     (`ann`, SIMP_TAC bool_ss [Abbr `ann`]), (`^First`, REFL_TAC)] >>
  (impl_tac >-
    (ntac 3 (conj_tac >- first_assum ACCEPT_TAC) >>
     conj_tac >- simp[NoAsms] >>
     ntac 3 (conj_tac >- (first_assum ACCEPT_TAC ORELSE first_assum
       (ACCEPT_TAC o PURE_REWRITE_RULE [LENGTH,GSYM arithmeticTheory.ONE,COND_CLAUSES,IMP_CLAUSES]))) >>
     conj_tac >-
       (qpat_assum `exit IN V` (fn hV =>
        qpat_assum `pc exit = b+2` (fn hpc => simp[NoAsms,hV,hpc]))) >>
     conj_tac >-
       asm "stack-initial-row" (ACCEPT_TAC o CONV_RULE (REDEPTH_CONV BETA_CONV)) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     qpat_assum `ann ^First = _` (fn h => SIMP_TAC bool_ss [BETA_RULE h,FST,SND]) >>
     ntac 4 (conj_tac >- first_assum ACCEPT_TAC) >>
     SIMP_TAC bool_ss [Abbr `it`,Abbr `ib`] >>
     asm "comm-root-just" (ACCEPT_TAC o BETA_RULE))) >>
  disch_then (fn h => CONV_TAC (REDEPTH_CONV BETA_CONV) >> ACCEPT_TAC h)
QED

Finalise stack_replayed_comm[local]

(* Each contextual rewrite preserves a pending certificate with a new actual
   replay endpoint. Terminal inputs use the whole-pass refinement separately. *)
Theorem stack_pending_contextual[local]:
  !orig s data req_bound pre w d tail.
  !p. p = pre++w++tail ==>
  !q. q = pre++d++tail ==>
  !b. b = LENGTH pre ==>
  !m. m = LENGTH w ==>
  ^window w d /\ ^Entry orig s data p /\ ^Pending orig s data req_bound p ==>
  ^Entry orig s data q /\ ^Pending orig s data req_bound q
Proof
  ntac 8 gen_tac >> stack_intro_aliases [`p`,`q`,`b`,`m`] >>
  CONV_TAC (REDEPTH_CONV BETA_CONV) >>
  disch_then (fn th =>
    let val [win,entry,pending] = stack_packet 2 th
    in assume_tac win >> assume_tac entry >>
       map_every assume_tac (CONJUNCTS entry) >>
       foldr (fn (name,k) => qx_choose_then name k)
         (fn h => let val ps = stack_packet 15 h
                  in map_every assume_tac ps >>
                     map_every assume_tac (CONJUNCTS (List.nth (ps,14))) >>
                     mk_asm "stack-source-open" (List.nth (ps,11)) end)
         [`k`,`t`,`u`,`cc`,`req`,`V`,`e`,`rank`,`pc`,`height`,`need`,`tag`,`boolean`,`edge`]
         pending
    end) >>
  Q.SUBGOAL_THEN `^Layout p q b m (LENGTH d)`
    (fn th => let val h = CONV_RULE (REDEPTH_CONV BETA_CONV) th
                  val parts = stack_packet 4
                    (CONV_RULE stack_inline_alias h)
              in map_every assume_tac (h :: List.take (parts,4)) end) >- suspend "layout" >>
  Q.SUBGOAL_THEN `^Entry orig s data q` (assume_tac o BETA_RULE) >- suspend "entry" >>
  conj_tac >- first_assum ACCEPT_TAC >>
  Q.SUBGOAL_THEN `?z H R G B. ^PortSelection q cc b m d V pc height rank need tag boolean z H R G B`
    (foldr (fn (name,k) => qx_choose_then name k) (assume_tac o BETA_RULE) [`z`,`H`,`R`,`G`,`B`]) >-
    suspend "ports" >>
  suspend "restart"
QED

Resume stack_pending_contextual[layout]:
  qspecl_then [`pre`,`w`,`d`,`tail`] (mp_tac o BETA_RULE) stack_window_layout >>
  (impl_tac >-
    (qpat_assum `Abbrev (p = _)` (fn h => PURE_REWRITE_TAC
       [GSYM (REWRITE_RULE [markerTheory.Abbrev_def] h)]) >>
     conj_tac >> first_assum ACCEPT_TAC)) >>
  BETA_TAC >> CONV_TAC (RAND_CONV stack_inline_alias) >>
  SIMP_TAC bool_ss [Abbr `p`,Abbr `q`,Abbr `b`,Abbr `m`] >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  rpt conj_tac >> first_assum ACCEPT_TAC
QED

Resume stack_pending_contextual[entry]:
  CONV_TAC (REDEPTH_CONV BETA_CONV) >>
  rpt (FIRST [first_assum ACCEPT_TAC, conj_tac]) >>
  qpat_assum `FILTER is_data_inst q = FILTER is_data_inst p` SUBST1_TAC >>
  first_assum ACCEPT_TAC
QED

Resume stack_pending_contextual[ports]:
  qspecl_then [`pre`,`w`,`d`,`tail`,`p`,`q`,`cc`,`req`,`V`,`rank`,`pc`,`height`,`need`,`tag`,`boolean`,`edge`]
    (mp_tac o CONV_RULE (stack_inline_lets 4 ALL_CONV)) stack_select_ports >>
  map_every (fn pat => qpat_assum pat
      (PURE_REWRITE_TAC o single o GSYM o REWRITE_RULE [markerTheory.Abbrev_def]))
    [`Abbrev (b = _)`,`Abbrev (m = _)`] >>
  (impl_tac >-
    (ntac 6 (conj_tac >- (first_assum ACCEPT_TAC ORELSE first_assum
       (ACCEPT_TAC o SIMP_RULE bool_ss [LET_THM,markerTheory.Abbrev_def]))) >>
     asm "stack-source-open" ACCEPT_TAC)) >>
  disch_then (foldr (fn (name,k) => qx_choose_then name k) assume_tac [`z`,`H`,`R`,`G`,`B`]) >>
  qexistsl [`z`,`H`,`R`,`G`,`B`] >>
  SIMP_TAC bool_ss [LET_THM,IN_GSPEC_IFF] >>
  qx_gen_tac `v` >> disch_tac >>
  qpat_assum `!v. v IN V /\ pc v = b ==> _` (qspec_then `v` mp_tac) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  qpat_assum `Abbrev (q = _)` (PURE_REWRITE_TAC o single o GSYM o
    REWRITE_RULE [markerTheory.Abbrev_def]) >>
  disch_then (map_every assume_tac o stack_packet 3) >>
  conj_tac >- simp[] >>
  ntac 2 (conj_tac >- first_assum ACCEPT_TAC) >>
  first_assum (ACCEPT_TAC o SIMP_RULE bool_ss [LET_THM,IN_GSPEC_IFF])
QED

Resume stack_pending_contextual[restart]:
  asm "stack-source-open" (assume_tac o CONJUNCT1 o
    CONV_RULE stack_inline_alias) >>
  `u.sym_base.as_pc = pc e /\ LENGTH u.sym_stack = height e /\
   u.sym_base.as_call_ctx = cc /\ u.sym_base.as_requests = req` by
    (map_every (fn pat => qpat_assum pat (PURE_REWRITE_TAC o single o GSYM))
       [`t.as_pc = u.sym_base.as_pc`,`LENGTH t.as_stack = LENGTH u.sym_stack`,
        `t.as_call_ctx = u.sym_base.as_call_ctx`,`t.as_requests = u.sym_base.as_requests`] >>
     rpt conj_tac >> first_assum ACCEPT_TAC) >>
  pop_assum (map_every assume_tac o CONJUNCTS) >>
  Cases_on `b<pc e /\ pc e<b+m`
  >- (pop_assum (fn h => assume_tac h >> map_every assume_tac (CONJUNCTS h)) >>
      Cases_on `^comm w d`
      >- (pop_assum (assume_tac o BETA_RULE) >> suspend "comm")
      >- (pop_assum (assume_tac o BETA_RULE) >> suspend "shuffle")) >>
  suspend "outside"
QED

Resume stack_pending_contextual[outside]:
  qspecl_then [`pre`,`w`,`d`,`tail`,`orig`,`s`,`data`,`req_bound`,`p`,`q`,
    `cc`,`req`,`V`,`pc`,`height`,`rank`,`need`,`tag`,`boolean`,`edge`,`z`,
    `H`,`R`,`G`,`B`,`e`,`k`,`u`]
    (mp_tac o BETA_RULE o CONV_RULE (stack_inline_lets 3 ALL_CONV)) stack_replayed_nonstrict >>
  map_every (fn pat => qpat_assum pat
      (PURE_REWRITE_TAC o single o GSYM o REWRITE_RULE [markerTheory.Abbrev_def]))
    [`Abbrev (b = _)`,`Abbrev (m = _)`] >>
  (impl_tac >- rpt (FIRST [first_assum
    (ACCEPT_TAC o REWRITE_RULE [markerTheory.Abbrev_def]),conj_tac])) >>
  disch_then ACCEPT_TAC
QED

Resume stack_pending_contextual[shuffle]:
  qspecl_then [`pre`,`w`,`d`,`tail`,`orig`,`s`,`data`,`req_bound`,`p`,`q`,
    `cc`,`req`,`V`,`pc`,`height`,`rank`,`need`,`tag`,`boolean`,`edge`,`z`,
    `H`,`R`,`G`,`B`,`e`,`k`,`t`,`u`]
    (mp_tac o BETA_RULE o CONV_RULE (stack_inline_lets 3 ALL_CONV)) stack_replayed_shuffle >>
  map_every (fn pat => qpat_assum pat
      (PURE_REWRITE_TAC o single o GSYM o REWRITE_RULE [markerTheory.Abbrev_def]))
    [`Abbrev (b = _)`,`Abbrev (m = _)`] >>
  (impl_tac >- rpt (FIRST [first_assum
    (ACCEPT_TAC o CONV_RULE (REDEPTH_CONV BETA_CONV) o REWRITE_RULE [markerTheory.Abbrev_def]),
    conj_tac])) >>
  disch_then ACCEPT_TAC
QED

Resume stack_pending_contextual[comm]:
  qpat_assum `?a. asm_commutative_op a /\ w=[AsmOp "SWAP1";a] /\ d=[a]` (qx_choose_then `a` (map_every assume_tac o CONJUNCTS) o BETA_RULE) >>
  `m = 2` by
    (qpat_assum `w = [AsmOp "SWAP1"; a]` (fn hw => simp[NoAsms, Abbr `m`, hw])) >>
  `pc e = b+1` by
    (qpat_assum `m = 2` (fn hm =>
       qpat_assum `b<pc e /\ pc e<b+m` (mp_tac o REWRITE_RULE [hm])) >> decide_tac) >>
  qspecl_then [`pre`,`a`,`tail`,`orig`,`s`,`data`,`req_bound`,`p`,`q`,
    `cc`,`req`,`V`,`pc`,`height`,`rank`,`need`,`tag`,`boolean`,`edge`,`z`,
    `H`,`R`,`G`,`B`,`e`,`k`,`u`]
    (mp_tac o BETA_RULE o CONV_RULE (stack_inline_lets 1 ALL_CONV)) stack_replayed_comm >>
  qpat_assum `Abbrev (b = _)` (PURE_REWRITE_TAC o single o GSYM o
    REWRITE_RULE [markerTheory.Abbrev_def]) >>
  (impl_tac >-
    (ntac 4 (conj_tac >- first_assum ACCEPT_TAC) >>
     ntac 2 (conj_tac >-
       (qpat_assum `w = [AsmOp "SWAP1"; a]` (fn hw =>
          qpat_assum `d = [a]` (fn hd => simp[NoAsms,Abbr `p`,Abbr `q`,hw,hd])))) >>
     conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- (qpat_assum `m = 2` (fn hm =>
       qpat_assum `d = [a]` (fn hd => first_assum
         (ACCEPT_TAC o PURE_REWRITE_RULE [hm,hd,LENGTH,GSYM arithmeticTheory.ONE])))) >>
     ntac 2 (conj_tac >- first_assum ACCEPT_TAC) >>
     conj_tac >- (qpat_assum `m = 2` (fn hm =>
       qpat_assum `d = [a]` (fn hd => first_assum
         (ACCEPT_TAC o PURE_REWRITE_RULE [hm,hd])))) >>
     rpt (FIRST [first_assum ACCEPT_TAC,conj_tac]))) >>
  disch_then ACCEPT_TAC
QED

Finalise stack_pending_contextual[local]


(* Replay each pending endpoint through the same six closures as the optimizer. *)
Theorem stack_pending_walk[local]:
  !orig s data req_bound p q ch.
  ^Entry orig s data p /\ ^Pending orig s data req_bound p /\
  stack_peephole_opts p = SOME(q,ch) ==>
  ^Entry orig s data q /\ ^Pending orig s data req_bound q
Proof
  map_every qx_gen_tac [`orig`,`s`,`data`,`req_bound`] >>
  mp_tac (CONV_RULE (REDEPTH_CONV BETA_CONV) (Q.INST [`P` |->
    `\p. ^Entry orig s data p /\ ^Pending orig s data req_bound p`]
    stack_peephole_walk_preserves_contextual)) >>
  (impl_tac >-
    (let
       fun close_window w d prove_window =
         qspecl_then [`orig`,`s`,`data`,`req_bound`,`pre`,w,d,`tail`]
           (mp_tac o PURE_REWRITE_RULE [GSYM APPEND_ASSOC,APPEND,APPEND_NIL] o
              CONV_RULE (REDEPTH_CONV BETA_CONV) o
              CONV_RULE (stack_inline_lets 4 ALL_CONV)) stack_pending_contextual >>
         (impl_tac >-
           (conj_tac >- prove_window >>
            first_assum ACCEPT_TAC)) >>
         disch_then (fn th => CONV_TAC (REDEPTH_CONV BETA_CONV) >> ACCEPT_TAC th)
     in
       (conj_tac >- (rpt gen_tac >> disch_tac >>
          close_window `[AsmOp "DUP1";AsmOp "SWAP2";AsmOp "SWAP1"]`
                       `[AsmOp "SWAP1";AsmOp "DUP2"]` (simp[NoAsms])) >>
        conj_tac >- (rpt gen_tac >> disch_tac >>
          close_window `[AsmOp "DUP1";AsmOp "SWAP1";AsmOp "POP"]` `[]` (simp[NoAsms])) >>
        conj_tac >- (rpt gen_tac >> disch_tac >>
          close_window `[AsmOp "SWAP1";AsmOp "POP";AsmOp "POP"]`
                       `[AsmOp "POP";AsmOp "POP"]` (simp[NoAsms])) >>
        conj_tac >- (rpt gen_tac >> disch_then (CONJUNCTS_THEN2 assume_tac assume_tac) >>
          close_window `[a;a]` `[]`
            (disj1_tac >> conj_tac >- REFL_TAC >>
             disj2_tac >> qexists_tac `a` >> simp[])) >>
        conj_tac >- (rpt gen_tac >> disch_then (CONJUNCTS_THEN2 assume_tac assume_tac) >>
          close_window `[AsmOp "SWAP1";a]` `[a]`
            (disj2_tac >> disj2_tac >> qexists_tac `a` >> simp[])) >>
        rpt gen_tac >> disch_tac >>
        close_window `[AsmOp "DUP1";AsmOp "SWAP1"]` `[AsmOp "DUP1"]` (simp[NoAsms]))
     end)) >>
  disch_tac >>
  map_every qx_gen_tac [`p`,`q`,`ch`] >>
  CONV_TAC (REDEPTH_CONV BETA_CONV) >>
  pop_assum (qspecl_then [`p`,`q`,`ch`] assume_tac) >>
  disch_then (fn h =>
    let val [entry,pending,opts] = stack_packet 2 h
    in first_assum (ACCEPT_TAC o (fn rule => MP rule (CONJ (CONJ entry pending) opts))) end)
QED

Theorem stack_peephole_abort_certificate:
  !orig s data req_bound.
  !M_R. M_R = (\p. ^Entry orig s data p /\
                    (^Terminal orig s data req_bound p \/
                     ^Pending orig s data req_bound p)) ==>
  !p q ch. M_R p /\ stack_peephole_opts p = SOME(q,ch) ==> M_R q
Proof
  map_every qx_gen_tac [`orig`,`s`,`data`,`req_bound`] >>
  CONV_TAC stack_inline_alias >>
  rpt gen_tac >> BETA_TAC >>
  disch_then (fn th =>
    let val (entry,cases) = CONJ_PAIR (CONJUNCT1 th)
    in map_every assume_tac (CONJUNCT2 th :: CONJUNCTS entry) >>
       DISJ_CASES_TAC cases end)
  >- (pop_assum (qx_choose_then `n` (qx_choose_then `out`
        (map_every assume_tac o CONJUNCTS))) >>
      qspecl_then [`orig`,`s`,`data`,`req_bound`,`p`,`q`,`ch`,`n`,`out`]
        (mp_tac o CONV_RULE (stack_inline_lets 3 ALL_CONV))
        stack_terminal_certificate_transfer >>
      (impl_tac >- rpt (FIRST [first_assum ACCEPT_TAC,conj_tac])) >>
      disch_then (map_every assume_tac o stack_packet 2) >>
      conj_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
      disj1_tac >> first_assum ACCEPT_TAC) >>
  qspecl_then [`orig`,`s`,`data`,`req_bound`,`p`,`q`,`ch`]
    (mp_tac o BETA_RULE) stack_pending_walk >>
  (impl_tac >- rpt (FIRST [first_assum ACCEPT_TAC,conj_tac])) >>
  disch_then (CONJUNCTS_THEN2 assume_tac assume_tac) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  disj2_tac >> first_assum ACCEPT_TAC
QED
