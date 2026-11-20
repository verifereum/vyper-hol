(* Positive empty-demand rows for the generated revert-forward occurrences. *)
Theory staticAbortGeneratedRevertRows
Ancestors
  staticAbortAdminRows staticAbortGeneratedAdminMicro staticAbortOpenAdminFlow
  staticAbortGeneratedRevertSpine staticAbortGeneratedRevertStep fnStaticAbortBoundary
  staticAbortRevertOccurrences staticAbortRevertRowsLink staticAbortStraight codegenSymRel
  asmOpSim stackOpAsmSim stackOpSim asmIR asmSem asmOptimizer planExec
  option rich_list list arithmetic pred_set finite_map words pair

(* The ordinary administrative operations do not take the fault alternative
   of the generic straight dispatcher. Keep their exact output count. *)
Theorem revert_admin_straight_ok[local]:
  (name = "POP" \/ name = "MSTORE" \/ name = "MLOAD") /\
  asm_op_arity name <= LENGTH t.as_stack ==>
  ?u m. static_abort_straight name m /\
    asm_step lo otp (AsmOp name) t = AsmOK u /\
    LENGTH u.as_stack = LENGTH t.as_stack - asm_op_arity name + m
Proof
  strip_tac >> gvs[EVAL ``asm_op_arity "POP"``,
                   EVAL ``asm_op_arity "MSTORE"``, EVAL ``asm_op_arity "MLOAD"``]
  >- (`t.as_stack <> []` by (strip_tac >> fs[]) >>
      drule asm_step_pop_ok >> disch_then (qspecl_then [`lo`,`otp`] strip_assume_tac) >>
      qexistsl [`asm_next (t with as_stack := stk)`,`0`] >>
      simp[asm_next_def, static_abort_straight_def] >> decide_tac)
  >- (qspecl_then [`lo`,`otp`,`t`] mp_tac asm_step_mstore_ok >>
      simp[GREATER_EQ] >> strip_tac >>
      qexistsl [`s2`,`0`] >> simp[static_abort_straight_def] >> decide_tac) >>
  `t.as_stack <> []` by (strip_tac >> fs[]) >>
  drule asm_step_mload_ok >> disch_then (qspecl_then [`lo`,`otp`] strip_assume_tac) >>
  qexistsl [`s2`,`1`] >> simp[static_abort_straight_def] >> decide_tac
QED

(* Instantiate the naming equalities before applying the existing row proof. *)
val revert_row_names_conv = TOP_DEPTH_CONV
  (FIRST_CONV [HO_REWR_CONV UNWIND_FORALL_THM2, BETA_CONV]);

(* Keep both the positive opcode inventory and the exact row heights from the
   same administrative fragment. Its demands and static requirement are empty. *)
Theorem revert_admin_row_heights[local]:
  !p b fmp ops h extra cc req.
    prefix_wf (SND(compute_label_offsets p)) h ops /\
    asm_block_at p b (execute_plan fmp ops) ==>
    ?H. H 0 = h+extra /\
      H (LENGTH(execute_plan fmp ops)) =
        prefix_end_len (SND(compute_label_offsets p)) h ops+extra /\
      (!s. s < LENGTH(execute_plan fmp ops) ==>
        b+s < LENGTH p /\
        case EL (b+s) p of
          AsmLabel l => H (SUC s) = H s
        | AsmPush bs => H (SUC s) = H s+1
        | AsmPushLabel l => IS_SOME (FLOOKUP (SND(compute_label_offsets p)) l) /\
                            H (SUC s) = H s+1
        | AsmPushOfst l d => IS_SOME (FLOOKUP (SND(compute_label_offsets p)) l) /\
                             H (SUC s) = H s+1
        | AsmOp name =>
            ~MEM name ["INVALID";"REVERT";"SSTORE";"TSTORE";"LOG0";
                       "LOG1";"LOG2";"LOG3";"LOG4";"JUMP";"JUMPI"] /\
            (case ALOOKUP dup_table name of
               SOME n => n < H s /\ H (SUC s) = H s+1
             | NONE => case ALOOKUP swap_table name of
                 SOME n => 0 < n /\ n < H s /\ H (SUC s) = H s
               | NONE => ?m. static_abort_straight name m /\
                    asm_op_arity name <= H s /\ H (SUC s) = H s-asm_op_arity name+m)
        | _ => F) /\
      (!s t. s < LENGTH(execute_plan fmp ops) /\ t.as_pc = b+s /\
              LENGTH t.as_stack = H s /\ t.as_call_ctx = cc /\ t.as_requests = req ==>
        (?u. (asm_steps (SND(compute_label_offsets p)) (build_offset_to_pc p) p 1 t = AsmRevert u \/
              asm_steps (SND(compute_label_offsets p)) (build_offset_to_pc p) p 1 t = AsmFault u) /\
             u.as_requests = req) \/
        (?u. asm_steps (SND(compute_label_offsets p)) (build_offset_to_pc p) p 1 t = AsmOK u /\
             u.as_pc = b+s+1 /\ LENGTH u.as_stack = H(SUC s) /\
             u.as_call_ctx = cc /\ u.as_requests = req))
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (MATCH_MP admin_prefix_open_fragment
    (SIMP_RULE std_ss []
      (CONV_RULE revert_row_names_conv generated_admin_micro_coverage))) >>
  disch_then (qspecl_then [`p`,`b`,`fmp`,`ops`,`h`,`extra`,`0`,
                          `cc`,`req`] mp_tac) >>
  asm_simp_tac std_ss [] >>
  disch_then (qx_choose_then `A` strip_assume_tac) >>
  qexists `\s. A s+extra` >> asm_simp_tac std_ss [] >>
  reverse conj_tac
  >- (rpt gen_tac >> strip_tac >>
      qpat_assum `!x t. _ ==> _ \/ _` (qspecl_then [`(0,s)`,`t`] mp_tac) >>
      (impl_tac >- (simp[IN_DIFF] >> decide_tac)) >>
      SIMP_TAC bool_ss [FST,SND,ADD1,ADD_ASSOC] >>
      disch_then (DISJ_CASES_THEN2 (fn th => disj1_tac >> ACCEPT_TAC th)
        (qx_choose_then `u` strip_assume_tac)) >>
      disj2_tac >> qexists `u` >> simp[]) >>
  qx_gen_tac `s` >> strip_tac >>
  `b+s < LENGTH p /\ EL (b+s) p = EL s (execute_plan fmp ops)` by
    (qpat_assum `asm_block_at _ _ _` (strip_assume_tac o REWRITE_RULE [asm_block_at_def]) >>
     conj_tac >- decide_tac >> first_x_assum irule >> simp[]) >>
  `MEM (EL (b+s) p) (execute_plan fmp ops)` by metis_tac[EL_MEM] >>
  drule_all pending_admin_instruction_rows >>
  disch_then (assume_tac o SIMP_RULE std_ss []) >>
  qpat_x_assum `EL (b+s) p = EL s (execute_plan fmp ops)` kall_tac >>
  qpat_x_assum `!x. FST x = 0 /\ SND x < _ ==> _`
    (qspec_then `(0,s)` (mp_tac o SIMP_RULE bool_ss [FST,SND])) >>
  (impl_tac >- first_assum ACCEPT_TAC) >> strip_tac >>
  Cases_on `EL (b+s) p` >> gnvs[asm_inst_case_def] >>
  rename1 `EL (b+s) p = AsmOp name` >>
  suspend "opcode"
QED

Resume revert_admin_row_heights[opcode]:
  conj_tac
  >- (simp[] >> rpt strip_tac >> gvs[] >> fs[dup_table_def,swap_table_def]) >>
  Cases_on `ALOOKUP dup_table name` >>
  NO_STRIP_FULL_SIMP_TAC bool_ss [option_case_def, optionTheory.NOT_NONE_SOME] >>
  Cases_on `ALOOKUP swap_table name` >>
  NO_STRIP_FULL_SIMP_TAC bool_ss [option_case_def, optionTheory.NOT_NONE_SOME] >>
  suspend "ordinary"
QED

Resume revert_admin_row_heights[ordinary]:
  qabbrev_tac `t = (ARB:asm_state) with <| as_pc := b+s;
      as_stack := REPLICATE (A s+extra) 0w;
      as_call_ctx := cc; as_requests := req |>` >>
  `asm_op_arity name <= LENGTH t.as_stack /\ t.as_pc = b+s` by
    (simp[Abbr `t`] >> decide_tac) >>
  drule_all revert_admin_straight_ok >>
  disch_then (qspecl_then [`build_offset_to_pc p`,`SND(compute_label_offsets p)`]
    (qx_choose_then `u` (qx_choose_then `m` strip_assume_tac))) >>
  `t.as_pc < LENGTH p` by simp[] >>
  `asm_steps (SND(compute_label_offsets p)) (build_offset_to_pc p) p 1 t = AsmOK u` by
    simp[asm_step_one] >>
  qpat_x_assum `!x t. _ ==> _ \/ _`
    (qspecl_then [`(0,s)`,`t`] mp_tac) >>
  (impl_tac >- simp[Abbr `t`,IN_DIFF]) >>
  asm_simp_tac bool_ss [asm_result_distinct, asm_result_11] >>
  disch_then strip_assume_tac >>
  qexists `m` >> conj_tac >- first_assum ACCEPT_TAC >>
  `LENGTH t.as_stack = extra + A s` by simp[Abbr `t`,ADD_COMM] >>
  qpat_assum `LENGTH t.as_stack = extra + A s` mp_tac >>
  qpat_assum `LENGTH t.as_stack - _ + m = extra + A _`
    (mp_tac o REWRITE_RULE [SND]) >>
  qpat_assum `_ /\ extra + A (SUC s) = _ /\ _`
    (mp_tac o CONJUNCT1 o CONJUNCT2) >>
  POP_ASSUM_LIST (K ALL_TAC) >> decide_tac
QED

Finalise revert_admin_row_heights

Theorem generated_revert_cut_rows_reloc:
  !lo'. lo' = SND(compute_label_offsets prog) ==>
  !otp. otp = build_offset_to_pc prog ==>
  !Shape. Shape = (\pc height need tag boolean (x:num#num) (t:asm_state).
    t.as_pc = pc x /\ LENGTH t.as_stack = height x /\
    t.as_call_ctx = cut.as_call_ctx /\ t.as_requests = cut.as_requests /\
    (need x ==> t.as_call_ctx.cc_static) /\
    (!k l origin. tag x k = SOME(l,origin) ==>
       k < height x /\ origin < LENGTH prog /\
       (EL origin prog = AsmPushLabel l \/
        (?d. EL origin prog = AsmPushOfst l d) \/ EL origin prog = AsmDataLabel l) /\
       ?off dest. FLOOKUP lo' l = SOME off /\ off < dimword(:256) /\
         FLOOKUP otp off = SOME dest /\ EL k t.as_stack = (n2w off:bytes32)) /\
    (!k. boolean x k ==> k < height x /\
       (EL k t.as_stack = 0w \/ EL k t.as_stack = 1w))) ==>
  !target. target = (\pc tag (x:num#num) (y:num#num).
    ?l origin off. tag x 0 = SOME(l,origin) /\ FLOOKUP lo' l = SOME off /\
      off < dimword(:256) /\ FLOOKUP otp off = SOME(pc y)) ==>
  !Flow. Flow = (\pc height tag boolean (x:num#num) (y:num#num).
    !hi. hi = height x ==>
    !hj. hj = height y ==>
    !ins. ins = EL (pc x) prog ==>
    !inherit. inherit =
      (\(src:num -> num option) (fresh:num -> (string#num)option) (bnew:num -> bool).
        (!k l origin. tag y k = SOME(l,origin) ==>
           k < hj /\ (fresh k = SOME(l,origin) \/
             ?a. src k = SOME a /\ a < hi /\ tag x a = SOME(l,origin))) /\
        (!k. boolean y k ==> k < hj /\
           (bnew k \/ ?a. src k = SOME a /\ a < hi /\ boolean x a))) ==>
    case ins of
      AsmLabel l => hj = hi /\ inherit (\k. SOME k) (\k. NONE) (\k. F)
    | AsmPush bs => hj = hi+1 /\
        inherit (\k. if k=0 then NONE else SOME(k-1)) (\k. NONE)
          (\k. k=0 /\ !s v. asm_step lo' otp (AsmPush bs) s = AsmOK v ==>
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
               !m. m = hj + asm_op_arity name - hi ==>
               a <= hi /\ hj = m+(hi-a) /\
               ((name="JUMP" \/ name="JUMPI") ==> m=0) /\
               inherit (\k. if k<m then NONE else SOME(k-m+a)) (\k. NONE)
                 (\k. k=0 /\ m=1 /\ asm_returns_zero_or_one ins /\
                   !s v. LENGTH s.as_stack=hi /\ asm_step lo' otp ins s=AsmOK v ==>
                     (EL 0 v.as_stack=0w \/ EL 0 v.as_stack=1w)))
    | _ => F) ==>
  body_inv_abort_reloc rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
    block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 cvs cut Inv
    ra pc_ret rest mem0 /\
  (!l. IS_SOME (FLOOKUP lo l) ==>
    IS_SOME (FLOOKUP (SND (compute_label_offsets prog)) l)) /\
  in_revert_forward fn cvs ==>
  ?(V:(num#num)->bool) e rank pc height need tag boolean edge.
    (!S. S = Shape pc height need tag boolean ==>
      FINITE V /\ {} SUBSET V /\
      (!x. x IN V ==> ?s. S x s) /\
      (!x. x IN V DIFF {} ==> pc x < LENGTH prog) /\
      (!x y. edge x y ==> x IN V DIFF {} /\ y IN V /\ rank y < (rank x:num) /\
         Flow pc height tag boolean x y /\
         (if EL (pc x) prog = AsmOp "JUMP" then target pc tag x y
          else if EL (pc x) prog = AsmOp "JUMPI" then pc y = pc x+1 \/ target pc tag x y
          else pc y = pc x+1)) /\
      (!x s. x IN V DIFF {} /\ S x s ==>
         (?v. (asm_steps lo' otp prog 1 s = AsmRevert v \/
               asm_steps lo' otp prog 1 s = AsmFault v) /\ v.as_requests=cut.as_requests) \/
         (?y v. edge x y /\ asm_steps lo' otp prog 1 s = AsmOK v /\ S y v))) /\
    e IN V /\ (!x. x IN V ==>
      ?n (path:num->num#num).
        path 0=e /\ path n=x /\ !k. k<n ==> edge (path k) (path(SUC k))) /\
    Shape pc height need tag boolean e cut /\
    (!j. tag e j=NONE /\ ~boolean e j) /\
    ((!x. x IN V ==>
       (need x ==> cut.as_call_ctx.cc_static) /\
       (!k. boolean x k ==> k < height x /\ tag x k=NONE) /\
       (!k l origin. tag x k = SOME(l,origin) ==>
          k < height x /\ origin < LENGTH prog /\
          (EL origin prog = AsmPushLabel l \/ EL origin prog = AsmPushOfst l 0) /\
          ?off dest. FLOOKUP lo' l = SOME off /\ off < dimword(:256) /\
                     FLOOKUP otp off = SOME dest)) /\
     (!x y. edge x y ==> x IN V /\ y IN V /\ rank y < rank x /\ Flow pc height tag boolean x y) /\
     (!x. x IN V ==>
       pc x < LENGTH prog /\
       (!h. h = height x ==>
        !fall. fall = (\y. pc y = pc x+1) ==>
        !arm. arm = (\P n. ?y. edge x y /\ P y /\ height y = n) ==>
        !legal. legal = (\P n. !y. edge x y ==> P y /\ height y = n) ==>
        !next. next = (\n. arm fall n /\ legal fall n) ==>
        !untagged. untagged = (\a. !k. k<a ==> tag x k=NONE) ==>
        !stop. stop = (\a. a<=h /\ untagged a /\ !y. ~edge x y) ==>
        case EL (pc x) prog of
          AsmLabel l => next h
        | AsmPush bs => next (h+1)
        | AsmPushLabel l => IS_SOME (FLOOKUP lo' l) /\ next (h+1)
        | AsmPushOfst l d => IS_SOME (FLOOKUP lo' l) /\ next (h+1)
        | AsmOp name =>
            if name="INVALID" then stop 0
            else if name="REVERT" then stop 2
            else if MEM name ["SSTORE";"TSTORE";"LOG0";"LOG1";"LOG2";"LOG3";"LOG4"]
                 then cut.as_call_ctx.cc_static /\ stop (asm_op_arity name)
            else
              (case ALOOKUP dup_table name of
                 SOME n => n<h /\ next (h+1)
               | NONE => case ALOOKUP swap_table name of
                   SOME n => 0<n /\ n<h /\ next h
                 | NONE =>
                     if name="JUMP" then
                        1<=h /\ arm (target pc tag x) (h-1) /\ legal (target pc tag x) (h-1)
                     else if name="JUMPI" then
                        2<=h /\ tag x 1=NONE /\ arm fall (h-2) /\ arm (target pc tag x) (h-2) /\
                        legal (\y. fall y \/ target pc tag x y) (h-2)
                     else
                        ?m. static_abort_straight name m /\ asm_op_arity name <= h /\
                            untagged (asm_op_arity name) /\ next (h-asm_op_arity name+m))
        | _ => F)))
Proof
  CONV_TAC revert_row_names_conv >> SIMP_TAC bool_ss [] >> strip_tac >>
  `LENGTH cut.as_stack = LENGTH ps.ps_stack + LENGTH rest` by
    (qhdtm_assum `body_inv_abort_reloc`
       (strip_assume_tac o REWRITE_RULE [body_inv_abort_reloc_def]) >>
     drule static_abort_frame_cut >> simp[] >> strip_tac >> simp[]) >>
  drule_all (Q.INST [`row_lo` |-> `SND (compute_label_offsets prog)`]
    generated_revert_cut_spine_reloc) >>
  disch_then (qspec_then `LENGTH rest` strip_assume_tac) >>
  qabbrev_tac `extra = LENGTH rest` >> qabbrev_tac `fmp = cpl.cp_initial_fmp` >>
  qabbrev_tac `cc = cut.as_call_ctx` >> qabbrev_tac `req = cut.as_requests` >>
  qabbrev_tac `a = \q. LENGTH (execute_plan fmp (pre q))` >>
  qabbrev_tac `b = \q. LENGTH (execute_plan fmp (emit q))` >>
  qabbrev_tac `c = \q. LENGTH (execute_plan fmp (post q))` >>
  qabbrev_tac `terminal = \at (hi:num). EL at prog = AsmOp "REVERT" /\ 2<=hi` >>
  qabbrev_tac `normal = \at hi hj.
    case EL at prog of
      AsmLabel l => hj=hi
    | AsmPush bs => hj=hi+1
    | AsmPushLabel l => IS_SOME (FLOOKUP (SND(compute_label_offsets prog)) l) /\ hj=hi+1
    | AsmPushOfst l delta => IS_SOME (FLOOKUP (SND(compute_label_offsets prog)) l) /\ hj=hi+1
    | AsmOp name =>
        ~MEM name ["INVALID";"REVERT";"SSTORE";"TSTORE";"LOG0";
                   "LOG1";"LOG2";"LOG3";"LOG4";"JUMP";"JUMPI"] /\
        (case ALOOKUP dup_table name of
           SOME n => n<hi /\ hj=hi+1
         | NONE => case ALOOKUP swap_table name of
             SOME n => 0<n /\ n<hi /\ hj=hi
           | NONE => ?m. static_abort_straight name m /\
                         asm_op_arity name<=hi /\ hj=hi-asm_op_arity name+m)
    | _ => F` >>
  qabbrev_tac `piece = \base len (H:num->num) last.
    base+len<=LENGTH prog /\
    (!s. s<len ==> if last then terminal (base+s) (H s)
                   else normal (base+s) (H s) (H(SUC s))) /\
    (!s t. s<len /\ t.as_pc=base+s /\ LENGTH t.as_stack=H s /\
      t.as_call_ctx=cc /\ t.as_requests=req ==>
      (?u. (asm_steps (SND(compute_label_offsets prog)) (build_offset_to_pc prog)
                 prog 1 t=AsmRevert u \/
             asm_steps (SND(compute_label_offsets prog)) (build_offset_to_pc prog)
                 prog 1 t=AsmFault u) /\ u.as_requests=req) \/
      (~last /\ ?u. asm_steps (SND(compute_label_offsets prog)) (build_offset_to_pc prog)
         prog 1 t=AsmOK u /\ u.as_pc=base+SUC s /\ LENGTH u.as_stack=H(SUC s) /\
         u.as_call_ctx=cc /\ u.as_requests=req))` >>
  `!base ops hin.
     prefix_wf (SND(compute_label_offsets prog)) hin ops /\
     asm_block_at prog base (execute_plan fmp ops) ==>
     ?H. H 0=hin+extra /\ H (LENGTH(execute_plan fmp ops))=
       prefix_end_len (SND(compute_label_offsets prog)) hin ops+extra /\
       piece base (LENGTH(execute_plan fmp ops)) H F` by suspend "admin" >>
  `!q. k<=q /\ q<=j ==> ?A.
     A 0=LENGTH (P q).ps_stack+extra /\ A (a q)=m q+extra /\
     piece (pc q) (a q) A F` by suspend "pre" >>
  pop_assum (mp_tac o SIMP_RULE bool_ss [GSYM RIGHT_EXISTS_IMP_THM, SKOLEM_THM]) >>
  disch_then (qx_choose_then `A` assume_tac) >>
  `!q. k<=q /\ q<j ==> ?C.
     C 0=d q+extra /\ C (c q)=LENGTH (P(SUC q)).ps_stack+extra /\
     piece (pc q+a q+b q) (c q) C F` by suspend "post" >>
  pop_assum (mp_tac o SIMP_RULE bool_ss [GSYM RIGHT_EXISTS_IMP_THM, SKOLEM_THM]) >>
  disch_then (qx_choose_then `C` assume_tac) >>
  qabbrev_tac `M = \q s:num. if s=0 then m q+extra else d q+extra` >>
  `b j = 1 /\
   (!q. k<=q /\ q<=j ==> piece (pc q+a q) (b q) (M q) (q=j)) /\
   (!q. k<=q /\ q<j ==> M q (b q)=d q+extra)` by suspend "emits" >>
  `?(base:num->num) (len:num->num) H.
    base (3*k) = cut.as_pc /\ H (3*k) 0 = LENGTH cut.as_stack /\ len (3*j+1) = 1 /\
    (!i. 3*k <= i /\ i <= 3*j+1 ==> piece (base i) (len i) (H i) (i = 3*j+1)) /\
    (!i. 3*k <= i /\ i < 3*j+1 ==>
       base (SUC i) = base i + len i /\ H (SUC i) 0 = H i (len i))` by suspend "flatten" >>
  suspend "close"
QED

Resume generated_revert_cut_rows_reloc[admin]:
  rpt gen_tac >> strip_tac >>
  drule_all revert_admin_row_heights >>
  disch_then (qspecl_then [`extra`,`cc`,`req`] (qx_choose_then `H` strip_assume_tac)) >>
  qexists `H` >> simp[Abbr `piece`] >> rpt conj_tac
  >- fs[asm_block_at_def]
  >- ((qx_gen_tac `s` >> strip_tac >>
      qpat_assum `!s. s < _ ==> _ /\ _` (qspec_then `s` mp_tac) >>
      (impl_tac >- first_assum ACCEPT_TAC) >>
      disch_then (mp_tac o CONJUNCT2) >> simp[Abbr `normal`] >> gvs[])) >>
  rpt gen_tac >> strip_tac >>
  qpat_assum `!s t. _ ==> _ \/ _` (qspecl_then [`s`,`t`] mp_tac) >>
  (impl_tac >- simp[]) >>
  pure_rewrite_tac [ADD1, ADD_ASSOC] >> simp[NoAsms]
QED

Resume generated_revert_cut_rows_reloc[pre]:
  qx_gen_tac `q` >> strip_tac >>
  qpat_assum `!q. k<=q /\ q<=j ==> get_instruction _ _ = _ /\ _`
    (qspec_then `q` mp_tac) >> (impl_tac >- simp[]) >> strip_tac >>
  qpat_assum `!base ops hin. _ ==> ?H. _`
    (qspecl_then [`pc q`,`pre q`,`LENGTH (P q).ps_stack`] mp_tac) >>
  (impl_tac >- simp[]) >>
  disch_then (qx_choose_then `H` strip_assume_tac) >>
  qexists `H` >> simp[Abbr `a`]
QED

Resume generated_revert_cut_rows_reloc[post]:
  qx_gen_tac `q` >> strip_tac >>
  `q<=j` by decide_tac >>
  qpat_assum `!q. k<=q /\ q<=j ==> get_instruction _ _ = _ /\ _`
    (qspec_then `q` mp_tac) >> (impl_tac >- simp[]) >> strip_tac >>
  qpat_assum `!base ops hin. _ ==> ?H. _`
    (qspecl_then [`pc q + LENGTH (execute_plan fmp (pre q)) +
                       LENGTH (execute_plan fmp (emit q))`,`post q`,`d q`] mp_tac) >>
  (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choose_then `H` strip_assume_tac) >>
  qexists `H` >> simp[Abbr `a`, Abbr `b`, Abbr `c`] >>
  qpat_assum `piece _ _ H F` mp_tac >>
  simp[NoAsms, AC ADD_ASSOC ADD_COMM]
QED

Resume generated_revert_cut_rows_reloc[emits]:
  conj_tac
  >- (qpat_assum `!q. k<=q /\ q<=j ==> get_instruction _ _ = _ /\ _`
        (qspec_then `j` mp_tac) >> (impl_tac >- decide_tac) >> strip_tac >>
      simp[Abbr `b`, execute_plan_def, exec_stack_op_def]) >>
  reverse conj_tac
  >- (qx_gen_tac `q` >> strip_tac >>
      qpat_assum `!q. k<=q /\ q<=j ==> get_instruction _ _ = _ /\ _`
        (qspec_then `q` mp_tac) >> (impl_tac >- decide_tac) >> strip_tac >>
      Cases_on `q=k` >> simp[Abbr `M`, Abbr `b`, execute_plan_def, exec_stack_op_def] >>
      `k<q /\ q<j` by decide_tac >> simp[execute_plan_def]) >>
  qx_gen_tac `q` >> strip_tac >>
  qpat_assum `!q. k<=q /\ q<=j ==> get_instruction _ _ = _ /\ _`
    (qspec_then `q` mp_tac) >> (impl_tac >- simp[]) >> strip_tac >>
  qabbrev_tac `at = pc q+a q` >>
  `asm_block_at prog at (execute_plan fmp (emit q))` by
    (qunabbrevl_tac [`at`,`a`] >> BETA_TAC >> first_assum ACCEPT_TAC) >>
  Cases_on `q=j`
  >- (`emit q=[SOEmit "REVERT"] /\ 2<=m q+extra` by simp[] >>
      `asm_block_at prog at [AsmOp "REVERT"]` by
        (qpat_assum `asm_block_at prog at (execute_plan _ _)` mp_tac >>
         gvs[execute_plan_def,exec_stack_op_def]) >>
      qpat_assum `asm_block_at prog at [AsmOp "REVERT"]`
        (strip_assume_tac o REWRITE_RULE [asm_block_at_cons,asm_block_at_nil]) >>
      simp[Abbr `piece`, Abbr `b`, Abbr `M`, Abbr `terminal`,
           execute_plan_def, exec_stack_op_def] >>
      conj_tac >- (qpat_x_assum `q=j` SUBST_ALL_TAC >>
                   qpat_assum `2<=m j+extra` mp_tac >>
                   simp[NoAsms, AC ADD_ASSOC ADD_COMM]) >>
      rpt strip_tac >>
      `?u. asm_steps (SND(compute_label_offsets prog)) (build_offset_to_pc prog)
              prog 1 t=AsmRevert u /\ u.as_requests=t.as_requests` by
        (irule generated_revert_step_requests >> conj_tac
         >- (qpat_x_assum `q=j` SUBST_ALL_TAC >>
             qpat_assum `2<=m j+extra` mp_tac >>
             simp[AC ADD_ASSOC ADD_COMM]) >> simp[]) >>
      qexists `u` >> simp[]) >>
  Cases_on `q=k`
  >- (`emit q=[SOEmit "RETURNDATACOPY"] /\ 3<=m q+extra /\
        d q+extra+3=m q+extra` by simp[] >>
      `asm_block_at prog at [AsmOp "RETURNDATACOPY"]` by
        (qpat_assum `asm_block_at prog at (execute_plan _ _)` mp_tac >>
         gvs[execute_plan_def,exec_stack_op_def]) >>
      qpat_assum `asm_block_at prog at [AsmOp "RETURNDATACOPY"]`
        (strip_assume_tac o REWRITE_RULE [asm_block_at_cons,asm_block_at_nil]) >>
      `ALOOKUP dup_table "RETURNDATACOPY"=NONE /\
       ALOOKUP swap_table "RETURNDATACOPY"=NONE /\
       asm_op_arity "RETURNDATACOPY"=3 /\
       static_abort_straight "RETURNDATACOPY" 0` by
        (conj_tac >- EVAL_TAC >> conj_tac >- EVAL_TAC >>
         conj_tac >- EVAL_TAC >> simp[static_abort_straight_def]) >>
      simp[Abbr `piece`, Abbr `b`, Abbr `M`, Abbr `normal`,
           execute_plan_def,exec_stack_op_def] >>
      qpat_x_assum `q=k` SUBST_ALL_TAC >>
      `3 <= extra + m k /\ extra + d k = extra + m k - 3` by
        (qpat_assum `3<=m k+extra` mp_tac >>
         qpat_assum `d k+extra+3=m k+extra` mp_tac >> decide_tac) >>
      conj_tac >- (qexists `0` >> simp[]) >>
      rpt strip_tac >>
      `asm_steps (SND(compute_label_offsets prog)) (build_offset_to_pc prog) prog 1 t =
       asm_step (SND(compute_label_offsets prog)) (build_offset_to_pc prog)
         (AsmOp "RETURNDATACOPY") t` by simp[asm_step_one] >>
      mp_tac (Q.INST [`name` |-> `"RETURNDATACOPY"`, `outputs` |-> `0`,
                      `s` |-> `t`, `lo` |-> `SND(compute_label_offsets prog)`,
                      `o2pc` |-> `build_offset_to_pc prog`] static_abort_straight_dispatch) >>
      simp[] >> strip_tac
      >- (disj2_tac >> qexists `t'` >> simp[]) >>
      disj1_tac >> qexists `t with as_returndata := []` >> simp[]) >>
  `k<q /\ q<j` by decide_tac >>
  `emit q=[]` by simp[] >>
  `asm_block_at prog at []` by
    (qpat_assum `asm_block_at prog at (execute_plan _ _)` mp_tac >> gvs[execute_plan_def]) >>
  qpat_assum `asm_block_at prog at []` (assume_tac o REWRITE_RULE [asm_block_at_nil]) >>
  simp[Abbr `piece`, Abbr `b`, execute_plan_def]
QED

Resume generated_revert_cut_rows_reloc[flatten]:
  `A k 0 = LENGTH cut.as_stack` by
    (qpat_assum `!q. k<=q /\ q<=j ==> A q 0 = _ /\ _`
       (qspec_then `k` mp_tac) >> simp[]) >>
  mp_tac (Q.INST [`B` |-> `M:num->num->num`]
    (Q.ISPEC `piece:num->num->(num->num)->bool->bool`
      (Q.GEN `P` revert_flatten_occurrences))) >>
  (impl_tac >- (
    conj_tac >- decide_tac >> conj_tac
    >- (qx_gen_tac `q` >> strip_tac >>
        qpat_assum `!q. k<=q /\ q<=j ==> A q 0 = _ /\ _`
          (qspec_then `q` mp_tac) >> simp[Abbr `M`]) >>
    qx_gen_tac `q` >> strip_tac >>
    `k<=SUC q /\ SUC q<=j` by decide_tac >>
    qpat_assum `!q. k<=q /\ q<=j ==> A q 0 = _ /\ _`
      (qspec_then `SUC q` mp_tac) >> (impl_tac >- simp[]) >> strip_tac >>
    qpat_assum `!q. k<=q /\ q<j ==> C q 0 = _ /\ _`
      (qspec_then `q` mp_tac) >> (impl_tac >- simp[]) >> strip_tac >>
    qpat_assum `!q. k<=q /\ q<=j ==> get_instruction _ _ = _ /\ _`
      (qspec_then `q` mp_tac) >> (impl_tac >- decide_tac) >> strip_tac >>
    pure_asm_rewrite_tac [] >> simp[Abbr `a`, Abbr `b`, Abbr `c`])) >>
  pure_asm_rewrite_tac [] >> disch_then ACCEPT_TAC
QED

Resume generated_revert_cut_rows_reloc[close]:
  `!i. 3*k <= i /\ i <= 3*j+1 ==> base' i+len i<=LENGTH prog` by
    ((gen_tac >> strip_tac >> qpat_assum `!i. _ ==> piece (base' i) _ _ _` drule_all >>
     disch_then (mp_tac o SIMP_RULE bool_ss []) >> simp[Abbr `piece`] >> (metis_tac[Abbr `piece`]))) >>
  qspecl_then [`base'`,`3*k`,`3*j+1`,`len`,`H`,`prog`,`terminal`,`normal`,
               `cc`,`req`,`LENGTH prog`] mp_tac revert_spine_link_rows >>
  (impl_tac >- (conj_tac >- decide_tac >> conj_tac >- simp[] >>
    conj_tac >- simp[] >> conj_tac
    >- (map_every qx_gen_tac [`ix`,`slot`] >> strip_tac >>
        qpat_assum `!i. _ ==> piece (base' i) _ _ _` (qspec_then `ix` mp_tac) >>
        (impl_tac >- simp[]) >>
        qpat_assum `Abbrev (piece = _)` (fn def =>
          disch_then (strip_assume_tac o SIMP_RULE bool_ss
            [REWRITE_RULE [markerTheory.Abbrev_def] def])) >>
        conj_tac >- decide_tac >>
        qpat_assum `!s. s < len ix ==> _` (qspec_then `slot` mp_tac) >>
        asm_simp_tac bool_ss []) >>
    conj_tac
    >- (map_every qx_gen_tac [`ix`,`slot`,`st`] >> strip_tac >>
        qpat_assum `!i. _ ==> piece (base' i) _ _ _` (qspec_then `ix` mp_tac) >>
        (impl_tac >- simp[]) >>
        qpat_assum `Abbrev (piece = _)` (fn def =>
          disch_then (strip_assume_tac o SIMP_RULE bool_ss
            [REWRITE_RULE [markerTheory.Abbrev_def] def])) >>
        qpat_assum `!s t. _ ==> _ \/ _` (qspecl_then [`slot`,`st`] mp_tac) >>
        `ix < 3*j+1 <=> ix <> 3*j+1` by decide_tac >>
        asm_simp_tac bool_ss []) >>
    gen_tac >> strip_tac >>
    qpat_assum `!i. _ ==> base' i+len i<=LENGTH prog` drule_all >> decide_tac)) >>
  disch_then (qx_choose_then `V` (qx_choose_then `e` (qx_choose_then `rank`
    (qx_choose_then `vpc` (qx_choose_then `height` (qx_choose_then `edge` strip_assume_tac)))))) >>
  qexistsl [`V`,`e`,`rank`,`vpc`,`height`,`\x. F`,`\x k. NONE`,`\x k. F`,`edge`] >>
  simp[] >> conj_asm1_tac
  >- (conj_tac
      >- (gen_tac >> disch_tac >>
          qexists `cut with <| as_pc := vpc x; as_stack := REPLICATE (height x) 0w |>` >>
          simp[Abbr `cc`, Abbr `req`]) >>
      suspend "flow") >>
  conj_tac
  >- (rpt gen_tac >> disch_tac >>
      qpat_assum `!x y. edge x y ==> _ /\ _ /\ _ /\ _` drule >> simp[]) >>
  suspend "rows"
QED

Resume generated_revert_cut_rows_reloc[flow]:
  rpt gen_tac >> disch_tac >>
  qpat_assum `!x y. edge x y ==> _ /\ _ /\ _ /\ _` drule >> strip_tac >>
  conj_tac >- simp[] >> conj_tac >- simp[] >>
  qpat_x_assum `normal (vpc x) (height x) (height y)` mp_tac >>
  qpat_assum `Abbrev (normal = _)` (fn def =>
    rewrite_tac [REWRITE_RULE [markerTheory.Abbrev_def] def]) >>
  Cases_on `EL (vpc x) prog` >> pop_assum (fn th => SIMP_TAC (srw_ss()) [th]) >>
  qmatch_goalsub_rename_tac `ALOOKUP dup_table name` >>
  Cases_on `ALOOKUP dup_table name` >> pop_assum (fn th => SIMP_TAC (srw_ss()) [th]) >>
  Cases_on `ALOOKUP swap_table name` >> pop_assum (fn th => SIMP_TAC (srw_ss()) [th]) >>
  strip_tac >> decide_tac
QED

Resume generated_revert_cut_rows_reloc[rows]:
  gen_tac >> disch_tac >>
  qpat_assum `!x. x IN V ==> vpc x < LENGTH prog /\ _` (qspec_then `x` mp_tac) >>
  (impl_tac >- simp[]) >>
  Cases_on `FST x = 3*j+1`
  >- (pop_assum (fn guard => SIMP_TAC bool_ss [guard]) >>
      qpat_assum `Abbrev (terminal = _)` (fn def =>
        rewrite_tac [REWRITE_RULE [markerTheory.Abbrev_def] def]) >>
      BETA_TAC >> disch_then strip_assume_tac >> simp[]) >>
  pop_assum (fn guard => SIMP_TAC bool_ss [guard]) >> disch_then strip_assume_tac >>
  qpat_x_assum `normal (vpc x) (height x) out` mp_tac >>
  qpat_assum `Abbrev (normal = _)` (fn def =>
    rewrite_tac [REWRITE_RULE [markerTheory.Abbrev_def] def]) >>
  qpat_assum `!y. edge x y ==> _ /\ height y = out` mp_tac >>
  reverse (qsuff_tac `?y. edge x y /\ vpc y = vpc x+1 /\ height y = out`)
  >- metis_tac[] >>
  POP_ASSUM_LIST kall_tac >> ntac 2 disch_tac >>
  Cases_on `EL (vpc x) prog` >> pop_assum (fn th => SIMP_TAC (srw_ss()) [th]) >>
  disch_then strip_assume_tac >> gvs[]
  >- (qmatch_goalsub_rename_tac `ALOOKUP dup_table name` >>
      Cases_on `ALOOKUP dup_table name` >> gvs[]
      >- (Cases_on `ALOOKUP swap_table name` >> gvs[]
          >- (rename1 `static_abort_straight name m` >> qexists `m` >> metis_tac[]) >>
          metis_tac[]) >>
      metis_tac[]) >>
  metis_tac[]
QED

Finalise generated_revert_cut_rows_reloc

Theorem generated_revert_cut_rows:
  !lo'. lo' = SND(compute_label_offsets prog) ==>
  !otp. otp = build_offset_to_pc prog ==>
  !Shape. Shape = (\pc height need tag boolean (x:num#num) (t:asm_state).
    t.as_pc = pc x /\ LENGTH t.as_stack = height x /\
    t.as_call_ctx = cut.as_call_ctx /\ t.as_requests = cut.as_requests /\
    (need x ==> t.as_call_ctx.cc_static) /\
    (!k l origin. tag x k = SOME(l,origin) ==>
       k < height x /\ origin < LENGTH prog /\
       (EL origin prog = AsmPushLabel l \/
        (?d. EL origin prog = AsmPushOfst l d) \/ EL origin prog = AsmDataLabel l) /\
       ?off dest. FLOOKUP lo' l = SOME off /\ off < dimword(:256) /\
         FLOOKUP otp off = SOME dest /\ EL k t.as_stack = (n2w off:bytes32)) /\
    (!k. boolean x k ==> k < height x /\
       (EL k t.as_stack = 0w \/ EL k t.as_stack = 1w))) ==>
  !target. target = (\pc tag (x:num#num) (y:num#num).
    ?l origin off. tag x 0 = SOME(l,origin) /\ FLOOKUP lo' l = SOME off /\
      off < dimword(:256) /\ FLOOKUP otp off = SOME(pc y)) ==>
  !Flow. Flow = (\pc height tag boolean (x:num#num) (y:num#num).
    !hi. hi = height x ==>
    !hj. hj = height y ==>
    !ins. ins = EL (pc x) prog ==>
    !inherit. inherit =
      (\(src:num -> num option) (fresh:num -> (string#num)option) (bnew:num -> bool).
        (!k l origin. tag y k = SOME(l,origin) ==>
           k < hj /\ (fresh k = SOME(l,origin) \/
             ?a. src k = SOME a /\ a < hi /\ tag x a = SOME(l,origin))) /\
        (!k. boolean y k ==> k < hj /\
           (bnew k \/ ?a. src k = SOME a /\ a < hi /\ boolean x a))) ==>
    case ins of
      AsmLabel l => hj = hi /\ inherit (\k. SOME k) (\k. NONE) (\k. F)
    | AsmPush bs => hj = hi+1 /\
        inherit (\k. if k=0 then NONE else SOME(k-1)) (\k. NONE)
          (\k. k=0 /\ !s v. asm_step lo' otp (AsmPush bs) s = AsmOK v ==>
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
               !m. m = hj + asm_op_arity name - hi ==>
               a <= hi /\ hj = m+(hi-a) /\
               ((name="JUMP" \/ name="JUMPI") ==> m=0) /\
               inherit (\k. if k<m then NONE else SOME(k-m+a)) (\k. NONE)
                 (\k. k=0 /\ m=1 /\ asm_returns_zero_or_one ins /\
                   !s v. LENGTH s.as_stack=hi /\ asm_step lo' otp ins s=AsmOK v ==>
                     (EL 0 v.as_stack=0w \/ EL 0 v.as_stack=1w)))
    | _ => F) ==>
  body_inv_abort rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
    block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 cvs cut Inv
    ra pc_ret rest mem0 /\
  sym_frame_inv prog env ctx cpl fn ret srest labs0 ps cut sc /\
  label_flow_ok ctx /\
  code_end_offset_ok (\ctx fn inst s. Inv ctx fn inst s /\ ~in_static_abort_prefix fn s) ctx /\
  sym_unit_static_ok unit /\
  asm_static_wf prog /\ (!l. MEM (AsmDataHeader l) prog ==> l IN FDOM env) /\
  in_revert_forward fn cvs ==>
  ?(V:(num#num)->bool) e rank pc height need tag boolean edge.
    (!S. S = Shape pc height need tag boolean ==>
      FINITE V /\ {} SUBSET V /\
      (!x. x IN V ==> ?s. S x s) /\
      (!x. x IN V DIFF {} ==> pc x < LENGTH prog) /\
      (!x y. edge x y ==> x IN V DIFF {} /\ y IN V /\ rank y < (rank x:num) /\
         Flow pc height tag boolean x y /\
         (if EL (pc x) prog = AsmOp "JUMP" then target pc tag x y
          else if EL (pc x) prog = AsmOp "JUMPI" then pc y = pc x+1 \/ target pc tag x y
          else pc y = pc x+1)) /\
      (!x s. x IN V DIFF {} /\ S x s ==>
         (?v. (asm_steps lo' otp prog 1 s = AsmRevert v \/
               asm_steps lo' otp prog 1 s = AsmFault v) /\ v.as_requests=cut.as_requests) \/
         (?y v. edge x y /\ asm_steps lo' otp prog 1 s = AsmOK v /\ S y v))) /\
    e IN V /\ (!x. x IN V ==>
      ?n (path:num->num#num).
        path 0=e /\ path n=x /\ !k. k<n ==> edge (path k) (path(SUC k))) /\
    Shape pc height need tag boolean e cut /\
    (!j. tag e j=NONE /\ ~boolean e j) /\
    ((!x. x IN V ==>
       (need x ==> cut.as_call_ctx.cc_static) /\
       (!k. boolean x k ==> k < height x /\ tag x k=NONE) /\
       (!k l origin. tag x k = SOME(l,origin) ==>
          k < height x /\ origin < LENGTH prog /\
          (EL origin prog = AsmPushLabel l \/ EL origin prog = AsmPushOfst l 0) /\
          ?off dest. FLOOKUP lo' l = SOME off /\ off < dimword(:256) /\
                     FLOOKUP otp off = SOME dest)) /\
     (!x y. edge x y ==> x IN V /\ y IN V /\ rank y < rank x /\ Flow pc height tag boolean x y) /\
     (!x. x IN V ==>
       pc x < LENGTH prog /\
       (!h. h = height x ==>
        !fall. fall = (\y. pc y = pc x+1) ==>
        !arm. arm = (\P n. ?y. edge x y /\ P y /\ height y = n) ==>
        !legal. legal = (\P n. !y. edge x y ==> P y /\ height y = n) ==>
        !next. next = (\n. arm fall n /\ legal fall n) ==>
        !untagged. untagged = (\a. !k. k<a ==> tag x k=NONE) ==>
        !stop. stop = (\a. a<=h /\ untagged a /\ !y. ~edge x y) ==>
        case EL (pc x) prog of
          AsmLabel l => next h
        | AsmPush bs => next (h+1)
        | AsmPushLabel l => IS_SOME (FLOOKUP lo' l) /\ next (h+1)
        | AsmPushOfst l d => IS_SOME (FLOOKUP lo' l) /\ next (h+1)
        | AsmOp name =>
            if name="INVALID" then stop 0
            else if name="REVERT" then stop 2
            else if MEM name ["SSTORE";"TSTORE";"LOG0";"LOG1";"LOG2";"LOG3";"LOG4"]
                 then cut.as_call_ctx.cc_static /\ stop (asm_op_arity name)
            else
              (case ALOOKUP dup_table name of
                 SOME n => n<h /\ next (h+1)
               | NONE => case ALOOKUP swap_table name of
                   SOME n => 0<n /\ n<h /\ next h
                 | NONE =>
                     if name="JUMP" then
                        1<=h /\ arm (target pc tag x) (h-1) /\ legal (target pc tag x) (h-1)
                     else if name="JUMPI" then
                        2<=h /\ tag x 1=NONE /\ arm fall (h-2) /\ arm (target pc tag x) (h-2) /\
                        legal (\y. fall y \/ target pc tag x y) (h-2)
                     else
                        ?m. static_abort_straight name m /\ asm_op_arity name <= h /\
                            untagged (asm_op_arity name) /\ next (h-asm_op_arity name+m))
        | _ => F)))
Proof
  CONV_TAC revert_row_names_conv >> SIMP_TAC bool_ss [] >> strip_tac >>
  fs[body_inv_abort_reloc_canonical] >>
  `!l. IS_SOME (FLOOKUP lo l) ==>
        IS_SOME (FLOOKUP (SND (compute_label_offsets prog)) l)` by simp[] >>
  drule_all (CONV_RULE revert_row_names_conv generated_revert_cut_rows_reloc) >>
  simp[]
QED
