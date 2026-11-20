Theory staticAbortOptMergeIszero
Ancestors
  staticAbortOptMergeIszeroPrefix staticAbortOptMergeIszeroLayout
  staticAbortProtectedActualPrefix staticAbortOptMergeIszeroLive
  staticAbortOptMergeIszeroWalk
  staticAbortOptMergeIszeroInterior staticAbortOptMergeIszeroPairRows
  staticAbortOptMergeIszeroBranchRows
  asmOptOwnMergeIszero asmSymOwnCode asmOptMergeIszero asmSplice asmSymPc asmSymBridge asmSymSem asmDataEnv
  words list finite_map pred_set staticAbortStraight staticAbortOptTerminalTransfer

val iszero_protected_terminal = staticAbortOptTerminalTransferTheory.protected_terminal_mode

val iszero_norm = TOP_DEPTH_CONV (FIRST_CONV
  [HO_REWR_CONV UNWIND_FORALL_THM2, REWR_CONV LET_THM, BETA_CONV])
val iszero_beta = TOP_DEPTH_CONV BETA_CONV

fun exact_components g =
  (FIRST [first_assum ACCEPT_TAC, ACCEPT_TAC TRUTH, conj_tac >> exact_components]) g

Theorem merge_iszero_actual_synchronized_cut_mode[local]:
  !r. r = splice_pc (LENGTH pre) (LENGTH pat) (LENGTH repl) ==>
  p = pre ++ pat ++ tail /\ q = pre ++ repl ++ tail /\
  ((?x. asm_returns_zero_or_one x /\
        pat = [x; AsmOp "ISZERO"; AsmOp "ISZERO"] /\ repl = [x]) \/
   (?l. pat = [AsmOp "ISZERO"; AsmOp "ISZERO"; AsmPushLabel l; AsmOp "JUMPI"] /\
        repl = [AsmPushLabel l; AsmOp "JUMPI"])) /\
  s.as_pc = 0 /\ s.as_code = assemble orig ++ data /\ asm_static_wf orig /\ asm_static_wf p /\
  FILTER is_data_inst p = FILTER is_data_inst orig /\
  sym_steps_mode allow_own p (asm_data_env orig (assemble orig ++ data)) s.as_code n (sym_init s) = SymOK ss /\
  ~(LENGTH pre < ss.sym_base.as_pc /\ ss.sym_base.as_pc < LENGTH pre + LENGTH pat)
  ==>
  asm_static_wf q /\
  ?j t.
    sym_steps_mode allow_own q (asm_data_env orig (assemble orig ++ data)) s.as_code j
      (sym_init s) =
        SymOK (sym_with_pc (r ss.sym_base.as_pc) ss) /\
    asm_steps (if allow_own then lo_reloc q orig else SND (compute_label_offsets q)) (build_offset_to_pc q) q j
      (if allow_own then s else (s with as_code := assemble q ++ data)) = AsmOK t /\
    (if allow_own then asm_sym_rel_own (lo_reloc q orig) q (asm_data_env orig s.as_code) s.as_code
     else asm_sym_rel q (asm_data_env q (assemble q ++ data))) t
      (sym_with_pc (r ss.sym_base.as_pc) ss) /\
    t.as_pc = r ss.sym_base.as_pc /\ LENGTH t.as_stack = LENGTH ss.sym_stack /\
    t.as_call_ctx = ss.sym_base.as_call_ctx /\ t.as_requests = ss.sym_base.as_requests
Proof
  CONV_TAC iszero_norm >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  mp_tac (CONV_RULE iszero_norm merge_iszero_one_canonical_layout) >>
  (impl_tac >- exact_components) >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  mp_tac (Q.INST [`env` |-> `asm_data_env orig (assemble orig ++ data)`, `own` |-> `s.as_code`]
    (CONV_RULE iszero_norm merge_iszero_one_stopped_prefix_mode)) >>
  (impl_tac >- exact_components) >>
  qpat_assum `~(LENGTH pre < _ /\ _)`
    (fn th => simp[NoAsms, th]) >> strip_tac >>
  `FILTER is_data_inst q = FILTER is_data_inst orig` by metis_tac[] >>
  mp_tac (Q.INST [`p` |-> `orig`, `q` |-> `q`, `n` |-> `j`,
     `ss` |-> `sym_with_pc
       (splice_pc (LENGTH (pre:asm_inst list)) (LENGTH (pat:asm_inst list)) (LENGTH (repl:asm_inst list))
         ss.sym_base.as_pc) ss`] stopped_symbolic_prefix_mode) >>
  (impl_tac >- exact_components) >>
  disch_then (qx_choose_then `t` (map_every assume_tac o CONJUNCTS)) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl_tac [`j`, `t`] >> gvs[sym_with_pc_def]
QED

Theorem merge_iszero_site_endpoint_mode[local]:
  !c. c = ss.sym_base.as_pc ==>
  !b. b = LENGTH pre ==>
  !m. m = LENGTH pat ==>
  !d. d = c-b ==>
  !B. B = (\w:bytes32. (b2w (w=0w):bytes32)) ==>
  p = pre ++ pat ++ tail /\ q = pre ++ repl ++ tail /\
  ((?x. asm_returns_zero_or_one x /\
        pat = [x; AsmOp "ISZERO"; AsmOp "ISZERO"] /\ repl = [x]) \/
   (?l. pat = [AsmOp "ISZERO"; AsmOp "ISZERO"; AsmPushLabel l; AsmOp "JUMPI"] /\
        repl = [AsmPushLabel l; AsmOp "JUMPI"])) /\
  s.as_pc = 0 /\ s.as_code = assemble orig ++ data /\ asm_static_wf orig /\ asm_static_wf p /\
  FILTER is_data_inst p = FILTER is_data_inst orig /\
  sym_steps_mode allow_own p (asm_data_env orig (assemble orig ++ data)) s.as_code n (sym_init s) = SymOK ss ==>
  asm_static_wf q /\ FILTER is_data_inst q = FILTER is_data_inst p /\
  ?j t u.
    asm_steps (if allow_own then lo_reloc q orig else SND (compute_label_offsets q)) (build_offset_to_pc q) q j
      (if allow_own then s else (s with as_code := assemble q ++ data)) = AsmOK t /\
    sym_steps_mode allow_own q (asm_data_env orig (assemble orig ++ data)) s.as_code j (sym_init s) = SymOK u /\
    (if allow_own then asm_sym_rel_own (lo_reloc q orig) q (asm_data_env orig s.as_code) s.as_code
     else asm_sym_rel q (asm_data_env q (assemble q ++ data))) t u /\
    t.as_pc = u.sym_base.as_pc /\ LENGTH t.as_stack = LENGTH u.sym_stack /\
    t.as_call_ctx = u.sym_base.as_call_ctx /\ t.as_requests = u.sym_base.as_requests /\
    t.as_call_ctx = ss.sym_base.as_call_ctx /\ t.as_requests = ss.sym_base.as_requests /\
    (if b<c /\ c<b+m then
       if m=3 then u.sym_base.as_pc=b+1 /\ ?w stk.
          (w=0w \/ w=1w) /\ u.sym_stack=Val w::stk /\
          ss.sym_stack=Val (FUNPOW B (d-1) w)::stk
       else u.sym_base.as_pc=b /\ ?l w stk.
          repl=[AsmPushLabel l; AsmOp "JUMPI"] /\ u.sym_stack=Val w::stk /\
          ss.sym_stack=(if d=3 then [Lab l 0] else []) ++ (Val (FUNPOW B (MIN d 2) w)::stk)
     else u=sym_with_pc (splice_pc b m (LENGTH repl) c) ss)
Proof
  CONV_TAC iszero_norm >>
  disch_then (map_every assume_tac o CONJUNCTS) >>
  mp_tac (cj 2 (CONV_RULE iszero_norm merge_iszero_one_canonical_layout)) >>
  (impl_tac >- exact_components) >>
  disch_then assume_tac >>
  Cases_on `LENGTH pre < ss.sym_base.as_pc /\ ss.sym_base.as_pc < LENGTH pre + LENGTH pat`
  >- suspend "interior" >> suspend "synchronized"
QED

Resume merge_iszero_site_endpoint_mode[interior]:
  pop_assum (map_every assume_tac o CONJUNCTS) >>
  mp_tac (CONV_RULE iszero_norm merge_iszero_actual_interior_cut_mode) >>
  (impl_tac >- exact_components) >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (qx_choose_then `j` (qx_choose_then `u` (qx_choose_then `t`
      (map_every assume_tac o CONJUNCTS))))) >>
  `asm_data_env orig (assemble orig ++ data) = asm_data_env q (assemble q ++ data)` by
    (irule asm_data_env_agree >> rpt conj_tac >> metis_tac[]) >>
  conj_tac >- first_assum ACCEPT_TAC >> conj_tac >- first_assum ACCEPT_TAC >>
  `sym_init (if allow_own then s else s with as_code := assemble q ++ data) = sym_init s`
    by (Cases_on `allow_own` >> simp[sym_init_def]) >>
  `t.as_call_ctx = ss.sym_base.as_call_ctx /\ t.as_requests = ss.sym_base.as_requests`
    by (conj_tac >> asm_rewrite_tac []) >>
  pop_assum (map_every assume_tac o CONJUNCTS) >>
  qexistsl_tac [`j`,`t`,`u`] >>
  conj_tac >- first_assum ACCEPT_TAC >>
  conj_tac >- (
    `(if allow_own then asm_data_env orig s.as_code
         else asm_data_env q (assemble q ++ data)) = asm_data_env orig (assemble orig ++ data)`
      by (Cases_on `allow_own` >> simp[COND_CLAUSES]) >>
    qpat_assum `sym_init _ = sym_init s` (fn init =>
    qpat_assum `(if allow_own then _ else _) = asm_data_env orig _` (fn env =>
      first_assum (ACCEPT_TAC o PURE_REWRITE_RULE [init,env])))) >>
  conj_tac >- (
    qpat_assum `s.as_code = assemble orig ++ data` (fn code =>
    qpat_assum `asm_data_env orig (assemble orig ++ data) = asm_data_env q (assemble q ++ data)` (fn env =>
      Cases_on `allow_own` >> PURE_REWRITE_TAC [COND_CLAUSES,code] >>
      first_assum (ACCEPT_TAC o PURE_REWRITE_RULE [COND_CLAUSES,code]) ORELSE
      first_assum (ACCEPT_TAC o PURE_REWRITE_RULE [COND_CLAUSES,code,env])))) >>
  ntac 6 (conj_tac >- first_assum ACCEPT_TAC) >>
  `LENGTH pre < ss.sym_base.as_pc /\ ss.sym_base.as_pc < LENGTH pre + LENGTH pat`
    by (conj_tac >> first_assum ACCEPT_TAC) >>
  asm_rewrite_tac [COND_CLAUSES]
QED

Resume merge_iszero_site_endpoint_mode[synchronized]:
  mp_tac (CONV_RULE iszero_norm merge_iszero_actual_synchronized_cut_mode) >>
  (impl_tac >- exact_components) >>
  disch_then (CONJUNCTS_THEN2 assume_tac
    (qx_choose_then `j` (qx_choose_then `t` (map_every assume_tac o CONJUNCTS)))) >>
  conj_tac >- first_assum ACCEPT_TAC >> conj_tac >- first_assum ACCEPT_TAC >>
  qexistsl [`j`,`t`,`sym_with_pc (splice_pc (LENGTH pre) (LENGTH pat) (LENGTH repl) ss.sym_base.as_pc) ss`] >>
  simp[sym_with_pc_def]
QED

Finalise merge_iszero_site_endpoint_mode

fun iszero_bind bindings =
  map_every (fn (v,k) => qx_gen_tac v >> disch_then (mk_asm k)) bindings
fun iszero_abbrev name q =
  qabbrev_tac q >> pop_assum (mk_asm name o REWRITE_RULE [markerTheory.Abbrev_def])
fun iszero_equations [] k = k []
  | iszero_equations (name::names) k =
      asm name (fn th => iszero_equations names (fn eqs => k (th::eqs)))
fun iszero_open names =
  iszero_equations names (pure_rewrite_tac) >> CONV_TAC iszero_norm
fun iszero_fact names pat ttac = iszero_equations names
  (fn eqs => qpat_assum pat (ttac o CONV_RULE iszero_norm o PURE_REWRITE_RULE eqs))

(* Match the worker's naming premises to the local equations, leaving
   Cert folded. Inline Control, Slots and the trailing geometry aliases. *)
fun iszero_rows_rule [] th k =
      k (CONV_RULE (REPEATC (HO_REWR_CONV UNWIND_FORALL_THM2) THENC iszero_beta) th)
  | iszero_rows_rule (NONE::names) th k = iszero_rows_rule names
      (CONV_RULE (HO_REWR_CONV UNWIND_FORALL_THM2) th) k
  | iszero_rows_rule (SOME name::names) th k =
      asm name (fn eq => iszero_rows_rule names
        (MP (CONV_RULE (LAND_CONV iszero_norm) (SPEC (lhs (concl eq)) th))
            (CONV_RULE iszero_norm eq)) k)

fun iszero_site_facts k =
  qpat_assum `pat = _` (fn hp => qpat_assum `repl = _` (fn hq => k [hp,hq]))

fun iszero_apply_rows worker =
  iszero_rows_rule [SOME "shape",SOME "flow",SOME "target",NONE,SOME "open",
                    SOME "reach",NONE,SOME "rows",SOME "root",SOME "cert"]
    (Q.INST [`env` |-> `asm_data_env orig s.as_code`, `own` |-> `s.as_code`] worker)
    (fn rule => iszero_site_facts (fn site =>
      qpat_assum `p = pre ++ pat ++ tail` (fn hp =>
      qpat_assum `q = pre ++ repl ++ tail` (fn hq =>
      iszero_fact ["bytes"]
        `(if allow_own then asm_sym_rel_own (lo_reloc p orig) p (asm_data_env orig s.as_code) s.as_code
          else asm_sym_rel p (asm_data_env p (cert_bytes p))) a ss` (fn src =>
        let fun premises c = strip_conj (fst (dest_imp c))
            val hp = PURE_REWRITE_RULE site hp
            val hq = PURE_REWRITE_RULE site hq
            val rule = PART_MATCH (hd o premises) rule (concl hp)
            val rule = PART_MATCH (hd o tl o premises) rule (concl hq)
        in
          assume_tac src >> assume_tac hp >> assume_tac hq >> mp_tac rule
        end)))))

Theorem merge_iszero_abort_certificate_mode:
  !orig (s:asm_state) data req_bound.
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
      off < dimword(:256) /\ FLOOKUP (build_offset_to_pc p) off = SOME(pc y)) ==>
  !Open. Open = (\p cc req (V:(num#num)->bool) X rank pc height need
        (tag:(num#num)->num->(string#num)option)
        (boolean:(num#num)->num->bool) edge.
    !S. S = Shape p cc req pc height need tag boolean ==>
    FINITE V /\ X SUBSET V /\
    (!x. x IN V ==> ?t. S x t) /\
    (!x. x IN V DIFF X ==> pc x < LENGTH p) /\
    (!x y. edge x y ==>
       x IN V DIFF X /\ y IN V /\ rank y < rank x /\
       Flow p pc height tag boolean x y /\
       (if EL (pc x) p = AsmOp "JUMP" then Target p pc tag x y
        else if EL (pc x) p = AsmOp "JUMPI" then pc y = pc x+1 \/ Target p pc tag x y
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
  !Rows. Rows = (\p cc (V:(num#num)->bool) X (rank:num#num->num) pc height need tag boolean edge.
    !lo. lo = SND(compute_label_offsets p) ==>
    (!x. x IN V ==>
      (need x ==> cc.cc_static) /\
      (!k. boolean x k ==> k < height x /\ tag x k=NONE) /\
      (!k l origin. tag x k = SOME(l,origin) ==>
         k < height x /\ origin < LENGTH p /\
         (EL origin p = AsmPushLabel l \/ EL origin p = AsmPushOfst l 0) /\
         ?off dest. FLOOKUP (SND(compute_label_offsets p)) l = SOME off /\
           off < dimword(:256) /\ FLOOKUP (build_offset_to_pc p) off = SOME dest)) /\
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
  !cert_bytes. cert_bytes = (\p. assemble p ++ data) ==>
  !env0. env0 = asm_data_env orig (cert_bytes orig) ==>
  !cert_run. cert_run = (\p n. asm_steps
    (if allow_own then lo_reloc p orig else SND (compute_label_offsets p))
    (build_offset_to_pc p) p n (if allow_own then s else (s with as_code := cert_bytes p))) ==>
  !Base. Base = (\p. s.as_pc = 0 /\ s.as_code = cert_bytes orig /\
                     asm_static_wf orig /\ asm_static_wf p /\
                     FILTER is_data_inst p = FILTER is_data_inst orig) ==>
  !Terminal. Terminal = (\p. ?n out.
    (cert_run p n = AsmRevert out \/ cert_run p n = AsmFault out) /\
    sym_terminal (sym_steps_mode allow_own p env0 s.as_code n (sym_init s)) /\
    out.as_requests <<= req_bound) ==>
  !Cut. Cut = (\p.
    ?j t u cc req (V:(num#num)->bool) e (rank:(num#num)->num)
      pc height need tag boolean edge.
      cert_run p j = AsmOK t /\
      sym_steps_mode allow_own p env0 s.as_code j (sym_init s) = SymOK u /\
      (if allow_own then asm_sym_rel_own (lo_reloc p orig) p (asm_data_env orig s.as_code) s.as_code
       else asm_sym_rel p (asm_data_env p (cert_bytes p))) t u /\
      t.as_pc = u.sym_base.as_pc /\ LENGTH t.as_stack = LENGTH u.sym_stack /\
      t.as_call_ctx = u.sym_base.as_call_ctx /\ t.as_requests = u.sym_base.as_requests /\
      t.as_call_ctx = cc /\ t.as_requests = req /\ req <<= req_bound /\
      Rows p cc V {} rank pc height need tag boolean edge /\
      Open p cc req V {} rank pc height need tag boolean edge /\
      e IN V /\ (!x. x IN V ==> Reach edge e x) /\
      Shape p cc req pc height need tag boolean e t /\
      (!k l origin. tag e k = SOME(l,origin) ==>
         k < LENGTH u.sym_stack /\ EL k u.sym_stack = Lab l 0) /\
      (!k. boolean e k ==>
         k < LENGTH u.sym_stack /\ (EL k u.sym_stack = Val 0w \/ EL k u.sym_stack = Val 1w))) ==>
  !p. Base p /\ (Terminal p \/ Cut p) ==>
    Base (FST (merge_iszero p)) /\
    (Terminal (FST (merge_iszero p)) \/ Cut (FST (merge_iszero p)))
Proof
  ntac 4 gen_tac >>
  iszero_bind [(`Shape`,"shape"),(`Flow`,"flow"),(`Target`,"target"),
               (`Open`,"open"),(`Reach`,"reach"),(`Rows`,"rows"),
               (`cert_bytes`,"bytes"),(`env0`,"env"),(`cert_run`,"run"),
               (`Base`,"base"),(`Terminal`,"terminal"),(`Cut`,"cut")] >>
  iszero_abbrev "root" `Root = \p ss a pc height need tag boolean e.
    Shape p a.as_call_ctx a.as_requests pc height need tag boolean e a /\
    (!k l origin. tag e k=SOME(l,origin) ==>
       k<LENGTH ss.sym_stack /\ EL k ss.sym_stack=Lab l 0) /\
    (!k. boolean e k ==> k<LENGTH ss.sym_stack /\
       (EL k ss.sym_stack=Val 0w \/ EL k ss.sym_stack=Val 1w))` >>
  iszero_abbrev "cert" `Cert = \p ss a. ?V e rank pc height need tag boolean edge.
    Rows p a.as_call_ctx V {} rank pc height need tag boolean edge /\
    Open p a.as_call_ctx a.as_requests V {} rank pc height need tag boolean edge /\
    e IN V /\ (!x. x IN V ==> Reach edge e x) /\
    Root p ss a pc height need tag boolean e` >>
  `!p. Cut p <=> ?j t u. cert_run p j = AsmOK t /\
    sym_steps_mode allow_own p env0 s.as_code j (sym_init s) = SymOK u /\
    (if allow_own then asm_sym_rel_own (lo_reloc p orig) p (asm_data_env orig s.as_code) s.as_code
       else asm_sym_rel p (asm_data_env p (cert_bytes p))) t u /\
    t.as_pc = u.sym_base.as_pc /\ LENGTH t.as_stack = LENGTH u.sym_stack /\
    t.as_call_ctx = u.sym_base.as_call_ctx /\ t.as_requests = u.sym_base.as_requests /\
    t.as_requests <<= req_bound /\ Cert p u t` by suspend "cut_interface" >>
  `!p q pre pat repl tail.
    p = pre ++ pat ++ tail /\ q = pre ++ repl ++ tail /\
    ((?x. asm_returns_zero_or_one x /\
          pat = [x; AsmOp "ISZERO"; AsmOp "ISZERO"] /\ repl = [x]) \/
     (?l. pat = [AsmOp "ISZERO"; AsmOp "ISZERO"; AsmPushLabel l; AsmOp "JUMPI"] /\
          repl = [AsmPushLabel l; AsmOp "JUMPI"])) /\
    Base p /\ Cut p ==> Base q /\ Cut q` by suspend "pending_site" >>
  gen_tac >>
  disch_then (CONJUNCTS_THEN2 assume_tac DISJ_CASES_TAC)
  >- suspend "terminal_arm" >>
  `Base (FST (merge_iszero p)) /\ Cut (FST (merge_iszero p))` suffices_by
    (strip_tac >> conj_tac >- first_assum ACCEPT_TAC >> disj2_tac >> first_assum ACCEPT_TAC) >>
  mp_tac (BETA_RULE (Q.INST [`P` |-> `\r. Base r /\ Cut r`]
                            merge_iszero_walks_preserve_contextual)) >>
  (impl_tac >- suspend "walk") >>
  disch_then (qspec_then `p` mp_tac) >>
  (impl_tac >- exact_components) >> disch_then ACCEPT_TAC
QED

Resume merge_iszero_abort_certificate_mode[cut_interface]:
  iszero_open ["cut","cert","root"] >>
  simp[NoAsms, RIGHT_EXISTS_AND_THM, GSYM CONJ_ASSOC]
QED

Resume merge_iszero_abort_certificate_mode[pending_site]:
  rpt gen_tac >> disch_then (map_every assume_tac o CONJUNCTS) >>
  iszero_fact ["base","bytes"] `Base p` (map_every assume_tac o CONJUNCTS) >>
  qpat_assum `!p. Cut p <=> _` (fn th =>
    qpat_assum `Cut p` (strip_assume_tac o REWRITE_RULE [th])) >>
  rename1 `Cert p ss a` >>
  rename1 `sym_steps_mode allow_own p env0 s.as_code n (sym_init s) = SymOK ss` >>
  `env0 = asm_data_env orig (assemble orig ++ data)` by (iszero_open ["env","bytes"] >> REFL_TAC) >>
  `sym_steps_mode allow_own p (asm_data_env orig (assemble orig ++ data)) s.as_code n (sym_init s) = SymOK ss` by
    (qpat_assum `env0 = _` (pure_rewrite_tac o single o SYM) >> first_assum ACCEPT_TAC) >>
  mp_tac (CONV_RULE iszero_norm merge_iszero_site_endpoint_mode) >>
  (impl_tac >- exact_components) >>
  disch_then (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac
    (qx_choose_then `j` (qx_choose_then `t` (qx_choose_then `u`
      (map_every assume_tac o CONJUNCTS)))))) >>
  `Cert q u t` by suspend "rows" >>
  `FILTER is_data_inst q = FILTER is_data_inst orig` by
    (qpat_assum `FILTER is_data_inst q = FILTER is_data_inst p`
       (pure_rewrite_tac o single) >> first_assum ACCEPT_TAC) >>
  conj_tac >- (iszero_open ["base","bytes"] >> exact_components) >>
  qpat_assum `!p. Cut p <=> _` (pure_rewrite_tac o single) >>
  qexistsl [`j`,`t`,`u`] >> iszero_open ["run","bytes"] >>
  `t.as_requests <<= req_bound` by
    (qpat_assum `t.as_requests = ss.sym_base.as_requests` (pure_rewrite_tac o single) >>
     qpat_assum `a.as_requests = ss.sym_base.as_requests` (pure_rewrite_tac o single o SYM) >>
     first_assum ACCEPT_TAC) >>
  `sym_steps_mode allow_own q env0 s.as_code j (sym_init s) = SymOK u` by
    (qpat_assum `env0 = _` (pure_rewrite_tac o single) >> first_assum ACCEPT_TAC) >>
  exact_components
QED

Resume merge_iszero_abort_certificate_mode[rows]:
  `t.as_call_ctx = a.as_call_ctx` by
    (qpat_assum `t.as_call_ctx = ss.sym_base.as_call_ctx` (pure_rewrite_tac o single) >>
     sym_tac >> first_assum ACCEPT_TAC) >>
  `t.as_requests = a.as_requests` by
    (qpat_assum `t.as_requests = ss.sym_base.as_requests` (pure_rewrite_tac o single) >>
     sym_tac >> first_assum ACCEPT_TAC) >>
  qpat_x_assum `(?x. asm_returns_zero_or_one x /\ _) \/ _` strip_assume_tac
  >- suspend "pair" >> suspend "branch"
QED

Resume merge_iszero_abort_certificate_mode[pair]:
  `allow_own ==> asm_static_wf q` by (strip_tac >> first_assum ACCEPT_TAC) >>
  iszero_apply_rows merge_iszero_pair_cut_rows_mode >>
  (impl_tac >- (
    rpt (FIRST [first_assum ACCEPT_TAC, conj_tac]) >>
    qmatch_goalsub_rename_tac `if LENGTH pre < _ /\ _ then _ else _` >>
    qpat_assum `if LENGTH pre < _ /\ _ then _ else _` mp_tac >>
    iszero_site_facts (fn eqs => simp (NoAsms::eqs)))) >>
  simp[]
QED

Resume merge_iszero_abort_certificate_mode[branch]:
  `allow_own ==> asm_static_wf q` by (strip_tac >> first_assum ACCEPT_TAC) >>
  iszero_apply_rows merge_iszero_jumpi_cut_rows_mode >>
  (impl_tac >- (
    rpt (FIRST [first_assum ACCEPT_TAC, conj_tac]) >>
    qmatch_goalsub_rename_tac `if LENGTH pre < _ /\ _ then _ else _` >>
    qpat_assum `if LENGTH pre < _ /\ _ then _ else _` mp_tac >>
    iszero_site_facts (fn eqs => simp (NoAsms::eqs)))) >>
  simp[]
QED

Resume merge_iszero_abort_certificate_mode[terminal_arm]:
  iszero_fact ["base","bytes"] `Base p` (map_every assume_tac o CONJUNCTS) >>
  iszero_fact ["terminal","run","env","bytes"] `Terminal p`
    (qx_choose_then `n` (qx_choose_then `out` (map_every assume_tac o CONJUNCTS))) >>
  `if allow_own then asm_refines_own p (FST (merge_iszero p))
    else asm_refines p (FST (merge_iszero p))` by
    (Cases_on `allow_own` >> simp[merge_iszero_refines, merge_iszero_refines_own]) >>
  mp_tac (Q.INST [`q` |-> `FST (merge_iszero p)`]
          (CONV_RULE iszero_norm iszero_protected_terminal)) >>
  (impl_tac >- exact_components) >>
  disch_then (CONJUNCTS_THEN2 assume_tac (CONJUNCTS_THEN2 assume_tac
    (qx_choose_then `m` (qx_choose_then `t` (map_every assume_tac o CONJUNCTS))))) >>
  iszero_open ["base","terminal","run","env","bytes"] >>
  conj_tac >- exact_components >>
  disj1_tac >> qexistsl [`m`,`t`] >>
  `t.as_requests <<= req_bound` by
    (qpat_assum `t.as_requests = out.as_requests` (pure_rewrite_tac o single) >>
     first_assum ACCEPT_TAC) >>
  exact_components
QED

Resume merge_iszero_abort_certificate_mode[walk]:
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_assum `!p q pre pat repl tail. _ ==> _`
        (qspecl_then [`pre ++ [x; AsmOp "ISZERO"; AsmOp "ISZERO"] ++ tail`,
                     `pre ++ [x] ++ tail`, `pre`,
                     `[x; AsmOp "ISZERO"; AsmOp "ISZERO"]`, `[x]`, `tail`] mp_tac) >>
      (impl_tac >- (rpt (FIRST [REFL_TAC, first_assum ACCEPT_TAC, conj_tac]) >>
                   disj1_tac >> qexists `x` >>
                   rpt (FIRST [REFL_TAC, first_assum ACCEPT_TAC, conj_tac]))) >>
      disch_then ACCEPT_TAC) >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `!p q pre pat repl tail. _ ==> _`
    (qspecl_then [`pre ++ [AsmOp "ISZERO"; AsmOp "ISZERO"; AsmPushLabel l; AsmOp "JUMPI"] ++ tail`,
                 `pre ++ [AsmPushLabel l; AsmOp "JUMPI"] ++ tail`, `pre`,
                 `[AsmOp "ISZERO"; AsmOp "ISZERO"; AsmPushLabel l; AsmOp "JUMPI"]`,
                 `[AsmPushLabel l; AsmOp "JUMPI"]`, `tail`] mp_tac) >>
  (impl_tac >- (rpt (FIRST [REFL_TAC, first_assum ACCEPT_TAC, conj_tac]) >>
               disj2_tac >> qexists `l` >> rpt (FIRST [REFL_TAC, conj_tac]))) >>
  disch_then ACCEPT_TAC
QED

Finalise merge_iszero_abort_certificate_mode

Theorem merge_iszero_abort_certificate:
  !orig (s:asm_state) data req_bound.
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
      off < dimword(:256) /\ FLOOKUP (build_offset_to_pc p) off = SOME(pc y)) ==>
  !Open. Open = (\p cc req (V:(num#num)->bool) X rank pc height need
        (tag:(num#num)->num->(string#num)option)
        (boolean:(num#num)->num->bool) edge.
    !S. S = Shape p cc req pc height need tag boolean ==>
    FINITE V /\ X SUBSET V /\
    (!x. x IN V ==> ?t. S x t) /\
    (!x. x IN V DIFF X ==> pc x < LENGTH p) /\
    (!x y. edge x y ==>
       x IN V DIFF X /\ y IN V /\ rank y < rank x /\
       Flow p pc height tag boolean x y /\
       (if EL (pc x) p = AsmOp "JUMP" then Target p pc tag x y
        else if EL (pc x) p = AsmOp "JUMPI" then pc y = pc x+1 \/ Target p pc tag x y
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
  !Rows. Rows = (\p cc (V:(num#num)->bool) X (rank:num#num->num) pc height need tag boolean edge.
    !lo. lo = SND(compute_label_offsets p) ==>
    (!x. x IN V ==>
      (need x ==> cc.cc_static) /\
      (!k. boolean x k ==> k < height x /\ tag x k=NONE) /\
      (!k l origin. tag x k = SOME(l,origin) ==>
         k < height x /\ origin < LENGTH p /\
         (EL origin p = AsmPushLabel l \/ EL origin p = AsmPushOfst l 0) /\
         ?off dest. FLOOKUP (SND(compute_label_offsets p)) l = SOME off /\
           off < dimword(:256) /\ FLOOKUP (build_offset_to_pc p) off = SOME dest)) /\
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
  !cert_bytes. cert_bytes = (\p. assemble p ++ data) ==>
  !env0. env0 = asm_data_env orig (cert_bytes orig) ==>
  !cert_run. cert_run = (\p n. asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p)
                    p n (s with as_code := cert_bytes p)) ==>
  !Base. Base = (\p. s.as_pc = 0 /\ s.as_code = cert_bytes orig /\
                     asm_static_wf orig /\ asm_static_wf p /\
                     FILTER is_data_inst p = FILTER is_data_inst orig) ==>
  !Terminal. Terminal = (\p. ?n out.
    (cert_run p n = AsmRevert out \/ cert_run p n = AsmFault out) /\
    sym_terminal (sym_steps p env0 n (sym_init s)) /\
    out.as_requests <<= req_bound) ==>
  !Cut. Cut = (\p.
    ?j t u cc req (V:(num#num)->bool) e (rank:(num#num)->num)
      pc height need tag boolean edge.
      cert_run p j = AsmOK t /\
      sym_steps p env0 j (sym_init s) = SymOK u /\
      asm_sym_rel p (asm_data_env p (cert_bytes p)) t u /\
      t.as_pc = u.sym_base.as_pc /\ LENGTH t.as_stack = LENGTH u.sym_stack /\
      t.as_call_ctx = u.sym_base.as_call_ctx /\ t.as_requests = u.sym_base.as_requests /\
      t.as_call_ctx = cc /\ t.as_requests = req /\ req <<= req_bound /\
      Rows p cc V {} rank pc height need tag boolean edge /\
      Open p cc req V {} rank pc height need tag boolean edge /\
      e IN V /\ (!x. x IN V ==> Reach edge e x) /\
      Shape p cc req pc height need tag boolean e t /\
      (!k l origin. tag e k = SOME(l,origin) ==>
         k < LENGTH u.sym_stack /\ EL k u.sym_stack = Lab l 0) /\
      (!k. boolean e k ==>
         k < LENGTH u.sym_stack /\ (EL k u.sym_stack = Val 0w \/ EL k u.sym_stack = Val 1w))) ==>
  !p. Base p /\ (Terminal p \/ Cut p) ==>
    Base (FST (merge_iszero p)) /\
    (Terminal (FST (merge_iszero p)) \/ Cut (FST (merge_iszero p)))
Proof
  MATCH_ACCEPT_TAC (Q.INST [`allow_own` |-> `F`] merge_iszero_abort_certificate_mode
    |> PURE_REWRITE_RULE [codegenSymRelTheory.sym_steps_mode_def, COND_CLAUSES])
QED
