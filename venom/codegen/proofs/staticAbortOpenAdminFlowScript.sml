(* Empty-demand administrative open fragments from universal microcoverage. *)
Theory staticAbortOpenAdminFlow
Ancestors
  staticAbortStack staticAbortTrace planWf planExec stackOpSim stackOpAsmSim
  asmSem asmIR asmSymSem asmOptimizer words list rich_list pred_set
  arithmetic finite_map

Theorem admin_success_numerical_flow[local]:
  !inst lo otp t u.
  static_abort_admin inst /\ asm_step lo otp inst t = AsmOK u ==>
  case inst of
    AsmLabel l => LENGTH u.as_stack = LENGTH t.as_stack
  | AsmPush bs => LENGTH u.as_stack = LENGTH t.as_stack + 1
  | AsmPushLabel l => LENGTH u.as_stack = LENGTH t.as_stack + 1
  | AsmPushOfst l d => LENGTH u.as_stack = LENGTH t.as_stack + 1
  | AsmOp name =>
      (case ALOOKUP dup_table name of
         SOME n => n < LENGTH t.as_stack /\
                   LENGTH u.as_stack = LENGTH t.as_stack + 1
       | NONE => case ALOOKUP swap_table name of
           SOME n => 0 < n /\ n < LENGTH t.as_stack /\
                     LENGTH u.as_stack = LENGTH t.as_stack
         | NONE =>
             asm_op_arity name <= LENGTH t.as_stack /\
             LENGTH u.as_stack =
               (LENGTH u.as_stack + asm_op_arity name - LENGTH t.as_stack) +
               (LENGTH t.as_stack - asm_op_arity name) /\
             ((name = "JUMP" \/ name = "JUMPI") ==>
               LENGTH u.as_stack + asm_op_arity name - LENGTH t.as_stack = 0))
  | _ => F
(* E0111 resisting route, prior to the checked zero-based DUP correction:
   Cases_on `inst` >>
   simp[static_abort_admin_def, GENLIST_CONS, dup_name_def, swap_name_def] >>
   rpt gen_tac >> strip_tac >> gvs[] >>
   qpat_x_assum `asm_step _ _ _ _ = _` mp_tac >>
   CONV_TAC (LAND_CONV (LAND_CONV (computeLib.RESTR_EVAL_CONV
     [``asm_pop``, ``asm_mstore``, ``asm_mload``, ``asm_dup``, ``asm_swap``,
      ``asm_next``, ``FLOOKUP``]))) >>
   CONV_TAC (computeLib.RESTR_EVAL_CONV
     [``asm_pop``, ``asm_mstore``, ``asm_mload``, ``asm_dup``, ``asm_swap``,
      ``asm_next``, ``FLOOKUP``, ``LENGTH``, ``as_stack``]) >>
   FAIL_TAC "numerical inversion state"
*)
Proof
  Cases_on `inst` >>
  simp[static_abort_admin_def, GENLIST_CONS, dup_name_def, swap_name_def] >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  qpat_x_assum `asm_step _ _ _ _ = _` mp_tac >>
  CONV_TAC (LAND_CONV (LAND_CONV (computeLib.RESTR_EVAL_CONV
    [``asm_pop``, ``asm_mstore``, ``asm_mload``, ``asm_dup``, ``asm_swap``,
     ``asm_next``, ``FLOOKUP``]))) >>
  CONV_TAC (computeLib.RESTR_EVAL_CONV
    [``asm_pop``, ``asm_mstore``, ``asm_mload``, ``asm_dup``, ``asm_swap``,
     ``asm_next``, ``FLOOKUP``, ``LENGTH``, ``as_stack``]) >>
  all_tac
  >~ [`asm_pop t = AsmOK u ==> _`]
  >- (Cases_on `t.as_stack` >> simp[asm_pop_def, asm_next_def] >>
      strip_tac >> gvs[])
  >~ [`asm_mload t = AsmOK u ==> _`]
  >- (Cases_on `t.as_stack` >> simp[asm_mload_def, asm_next_def] >>
      strip_tac >> gvs[])
  >~ [`asm_mstore t = AsmOK u ==> _`]
  >- (namedCases_on `t.as_stack` ["", "a stk"] >> simp[asm_mstore_def] >>
      Cases_on `stk` >> simp[asm_mstore_def, asm_next_def] >>
      strip_tac >> gvs[])
  >>~- ([`asm_dup _ t = AsmOK u ==> _`],
     simp[asm_dup_def] >> IF_CASES_TAC >> simp[asm_next_def] >>
     strip_tac >> gvs[])
  >>~- ([`asm_swap _ t = AsmOK u ==> _`],
     simp[asm_swap_def] >> IF_CASES_TAC >> simp[asm_next_def] >>
     strip_tac >> gvs[LENGTH_LUPDATE])
  >> simp[asm_next_def, AllCaseEqs()] >> rpt strip_tac >> gvs[]
QED

Theorem admin_prefix_open_fragment:
  (!p b fmp ops h.
    prefix_wf (SND(compute_label_offsets p)) h ops /\
    asm_block_at p b (execute_plan fmp ops) ==>
    ?H. H 0 = h /\
      H (LENGTH(execute_plan fmp ops)) =
        prefix_end_len (SND(compute_label_offsets p)) h ops /\
      (!inst. MEM inst (execute_plan fmp ops) ==>
        inst <> AsmOp "JUMP" /\ inst <> AsmOp "JUMPI") /\
      !k extra t.
        k < LENGTH(execute_plan fmp ops) /\ t.as_pc = b+k /\
        LENGTH t.as_stack = H k + extra ==>
        ?u. static_abort_normal (SND(compute_label_offsets p))
              (build_offset_to_pc p) p 1 t u /\
            u.as_pc = b+k+1 /\ LENGTH u.as_stack = H(SUC k)+extra /\
            u.as_call_ctx = t.as_call_ctx /\ u.as_requests = t.as_requests) ==>
  !p b fmp ops h extra (f:num) cc req.
    prefix_wf (SND(compute_label_offsets p)) h ops /\
    asm_block_at p b (execute_plan fmp ops) ==>
    ?H. H 0 = h /\
      H (LENGTH(execute_plan fmp ops)) =
        prefix_end_len (SND(compute_label_offsets p)) h ops /\
      (FINITE {(f,k) | k <= LENGTH(execute_plan fmp ops)} /\
       {(f,LENGTH(execute_plan fmp ops))} SUBSET
         {(f,k) | k <= LENGTH(execute_plan fmp ops)} /\
       (!x. x IN {(f,k) | k <= LENGTH(execute_plan fmp ops)} ==>
         ?t:asm_state.
           t.as_pc = b+SND x /\ LENGTH t.as_stack = H(SND x)+extra /\
           t.as_call_ctx = cc /\ t.as_requests = req /\
           (F ==> t.as_call_ctx.cc_static) /\
           (!k l origin. (NONE:(string#num)option) = SOME(l,origin) ==>
             k < H(SND x)+extra /\ origin < LENGTH p /\
             (EL origin p = AsmPushLabel l \/
              (?d. EL origin p = AsmPushOfst l d) \/ EL origin p = AsmDataLabel l) /\
             ?off dest. FLOOKUP (SND(compute_label_offsets p)) l = SOME off /\
               off < dimword(:256) /\
               FLOOKUP (build_offset_to_pc p) off = SOME dest /\
               EL k t.as_stack = (n2w off:bytes32)) /\
           (!k. F ==> k < H(SND x)+extra /\
             (EL k t.as_stack = 0w \/ EL k t.as_stack = 1w))) /\
       (!x. x IN {(f,k) | k <= LENGTH(execute_plan fmp ops)} DIFF
           {(f,LENGTH(execute_plan fmp ops))} ==> b+SND x < LENGTH p) /\
       (!x y. FST x = f /\ SND x < LENGTH(execute_plan fmp ops) /\
           y = (f,SUC(SND x)) ==>
         x IN {(f,k) | k <= LENGTH(execute_plan fmp ops)} DIFF
           {(f,LENGTH(execute_plan fmp ops))} /\
         y IN {(f,k) | k <= LENGTH(execute_plan fmp ops)} /\
         LENGTH(execute_plan fmp ops)-SND y <
           LENGTH(execute_plan fmp ops)-SND x /\
         (case EL (b+SND x) p of
            AsmLabel l =>
              H(SND y)+extra = H(SND x)+extra /\
              (!k l origin. (NONE:(string#num)option) = SOME(l,origin) ==>
                k < H(SND y)+extra /\
                ((NONE:(string#num)option) = SOME(l,origin) \/
                 ?a. SOME k = SOME a /\ a < H(SND x)+extra /\
                   (NONE:(string#num)option) = SOME(l,origin))) /\
              (!k. F ==> k < H(SND y)+extra /\
                (F \/ ?a. SOME k = SOME a /\ a < H(SND x)+extra /\ F))
          | AsmPush bs =>
              H(SND y)+extra = H(SND x)+extra+1 /\
              (!k l origin. (NONE:(string#num)option) = SOME(l,origin) ==>
                k < H(SND y)+extra /\
                ((NONE:(string#num)option) = SOME(l,origin) \/
                 ?a. (if k=0 then NONE else SOME(k-1)) = SOME a /\
                   a < H(SND x)+extra /\ (NONE:(string#num)option) = SOME(l,origin))) /\
              (!k. F ==> k < H(SND y)+extra /\
                ((k=0 /\ !t u. asm_step (SND(compute_label_offsets p))
                    (build_offset_to_pc p) (AsmPush bs) t = AsmOK u ==>
                    (EL 0 u.as_stack = 0w \/ EL 0 u.as_stack = 1w)) \/
                 ?a. (if k=0 then NONE else SOME(k-1)) = SOME a /\
                   a < H(SND x)+extra /\ F))
          | AsmPushLabel l =>
              H(SND y)+extra = H(SND x)+extra+1 /\
              (!k l' origin. (NONE:(string#num)option) = SOME(l',origin) ==>
                k < H(SND y)+extra /\
                ((if k=0 then SOME(l,b+SND x) else NONE) = SOME(l',origin) \/
                 ?a. (if k=0 then NONE else SOME(k-1)) = SOME a /\
                   a < H(SND x)+extra /\ (NONE:(string#num)option) = SOME(l',origin))) /\
              (!k. F ==> k < H(SND y)+extra /\
                (F \/ ?a. (if k=0 then NONE else SOME(k-1)) = SOME a /\
                  a < H(SND x)+extra /\ F))
          | AsmPushOfst l d =>
              H(SND y)+extra = H(SND x)+extra+1 /\
              (!k l' origin. (NONE:(string#num)option) = SOME(l',origin) ==>
                k < H(SND y)+extra /\
                ((if k=0 /\ d=0 then SOME(l,b+SND x) else NONE) = SOME(l',origin) \/
                 ?a. (if k=0 then NONE else SOME(k-1)) = SOME a /\
                   a < H(SND x)+extra /\ (NONE:(string#num)option) = SOME(l',origin))) /\
              (!k. F ==> k < H(SND y)+extra /\
                (F \/ ?a. (if k=0 then NONE else SOME(k-1)) = SOME a /\
                  a < H(SND x)+extra /\ F))
          | AsmOp name =>
              (case ALOOKUP dup_table name of
                 SOME n => n < H(SND x)+extra /\
                   H(SND y)+extra = H(SND x)+extra+1 /\
                   (!k l origin. (NONE:(string#num)option) = SOME(l,origin) ==>
                     k < H(SND y)+extra /\
                     ((NONE:(string#num)option) = SOME(l,origin) \/
                      ?a. SOME(if k=0 then n else k-1) = SOME a /\
                        a < H(SND x)+extra /\ (NONE:(string#num)option) = SOME(l,origin))) /\
                   (!k. F ==> k < H(SND y)+extra /\
                     (F \/ ?a. SOME(if k=0 then n else k-1) = SOME a /\
                       a < H(SND x)+extra /\ F))
               | NONE => case ALOOKUP swap_table name of
                   SOME n => 0 < n /\ n < H(SND x)+extra /\
                     H(SND y)+extra = H(SND x)+extra /\
                     (!k l origin. (NONE:(string#num)option) = SOME(l,origin) ==>
                       k < H(SND y)+extra /\
                       ((NONE:(string#num)option) = SOME(l,origin) \/
                        ?a. SOME(if k=0 then n else if k=n then 0 else k) = SOME a /\
                          a < H(SND x)+extra /\ (NONE:(string#num)option) = SOME(l,origin))) /\
                     (!k. F ==> k < H(SND y)+extra /\
                       (F \/ ?a. SOME(if k=0 then n else if k=n then 0 else k) = SOME a /\
                         a < H(SND x)+extra /\ F))
                 | NONE => asm_op_arity name <= H(SND x)+extra /\
                     H(SND y)+extra =
                       (H(SND y)+extra+asm_op_arity name-(H(SND x)+extra)) +
                       (H(SND x)+extra-asm_op_arity name) /\
                     ((name="JUMP" \/ name="JUMPI") ==>
                       H(SND y)+extra+asm_op_arity name-(H(SND x)+extra) = 0) /\
                     (!k l origin. (NONE:(string#num)option) = SOME(l,origin) ==>
                       k < H(SND y)+extra /\
                       ((NONE:(string#num)option) = SOME(l,origin) \/
                        ?a. (if k < H(SND y)+extra+asm_op_arity name-(H(SND x)+extra)
                             then NONE else SOME(k-(H(SND y)+extra+asm_op_arity name-
                               (H(SND x)+extra))+asm_op_arity name)) = SOME a /\
                          a < H(SND x)+extra /\ (NONE:(string#num)option) = SOME(l,origin))) /\
                     (!k. F ==> k < H(SND y)+extra /\
                       ((k=0 /\ H(SND y)+extra+asm_op_arity name-(H(SND x)+extra)=1 /\
                         asm_returns_zero_or_one (EL (b+SND x) p) /\
                         !t u. LENGTH t.as_stack=H(SND x)+extra /\
                           asm_step (SND(compute_label_offsets p))
                             (build_offset_to_pc p) (EL (b+SND x) p) t = AsmOK u ==>
                           (EL 0 u.as_stack=0w \/ EL 0 u.as_stack=1w)) \/
                        ?a. (if k < H(SND y)+extra+asm_op_arity name-(H(SND x)+extra)
                             then NONE else SOME(k-(H(SND y)+extra+asm_op_arity name-
                               (H(SND x)+extra))+asm_op_arity name)) = SOME a /\
                          a < H(SND x)+extra /\ F)))
          | _ => F) /\
         (if EL (b+SND x) p = AsmOp "JUMP" then
            ?l origin off. (NONE:(string#num)option) = SOME(l,origin) /\
              FLOOKUP (SND(compute_label_offsets p)) l = SOME off /\
              off < dimword(:256) /\
              FLOOKUP (build_offset_to_pc p) off = SOME(b+SND y)
          else if EL (b+SND x) p = AsmOp "JUMPI" then
            b+SND y = b+SND x+1 \/
            (?l origin off. (NONE:(string#num)option) = SOME(l,origin) /\
              FLOOKUP (SND(compute_label_offsets p)) l = SOME off /\
              off < dimword(:256) /\
              FLOOKUP (build_offset_to_pc p) off = SOME(b+SND y))
          else b+SND y = b+SND x+1)) /\
       (!x (t:asm_state).
         x IN {(f,k) | k <= LENGTH(execute_plan fmp ops)} DIFF
           {(f,LENGTH(execute_plan fmp ops))} /\
         (t.as_pc=b+SND x /\ LENGTH t.as_stack=H(SND x)+extra /\
          t.as_call_ctx=cc /\ t.as_requests=req /\
          (F ==> t.as_call_ctx.cc_static) /\
          (!k l origin. (NONE:(string#num)option) = SOME(l,origin) ==>
            k < H(SND x)+extra /\ origin < LENGTH p /\
            (EL origin p=AsmPushLabel l \/ (?d. EL origin p=AsmPushOfst l d) \/
              EL origin p=AsmDataLabel l) /\
            ?off dest. FLOOKUP (SND(compute_label_offsets p)) l=SOME off /\
              off < dimword(:256) /\ FLOOKUP (build_offset_to_pc p) off=SOME dest /\
              EL k t.as_stack=(n2w off:bytes32)) /\
          (!k. F ==> k < H(SND x)+extra /\
            (EL k t.as_stack=0w \/ EL k t.as_stack=1w))) ==>
         (?u. (asm_steps (SND(compute_label_offsets p)) (build_offset_to_pc p) p 1 t =
                 AsmRevert u \/
               asm_steps (SND(compute_label_offsets p)) (build_offset_to_pc p) p 1 t =
                 AsmFault u) /\ u.as_requests=req) \/
         (?y u. (FST x=f /\ SND x < LENGTH(execute_plan fmp ops) /\
             y=(f,SUC(SND x))) /\
           asm_steps (SND(compute_label_offsets p)) (build_offset_to_pc p) p 1 t = AsmOK u /\
           (u.as_pc=b+SND y /\ LENGTH u.as_stack=H(SND y)+extra /\
            u.as_call_ctx=cc /\ u.as_requests=req /\
            (F ==> u.as_call_ctx.cc_static) /\
            (!k l origin. (NONE:(string#num)option) = SOME(l,origin) ==>
              k < H(SND y)+extra /\ origin < LENGTH p /\
              (EL origin p=AsmPushLabel l \/ (?d. EL origin p=AsmPushOfst l d) \/
                EL origin p=AsmDataLabel l) /\
              ?off dest. FLOOKUP (SND(compute_label_offsets p)) l=SOME off /\
                off < dimword(:256) /\ FLOOKUP (build_offset_to_pc p) off=SOME dest /\
                EL k u.as_stack=(n2w off:bytes32)) /\
            (!k. F ==> k < H(SND y)+extra /\
              (EL k u.as_stack=0w \/ EL k u.as_stack=1w)))))) /\
      (!x. x IN {(f,k) | k <= LENGTH(execute_plan fmp ops)} ==>
        ?n (path:num->num#num). path 0=(f,0) /\ path n=x /\
          !k. k<n ==> FST(path k)=f /\
            SND(path k) < LENGTH(execute_plan fmp ops) /\
            path(SUC k)=(f,SUC(SND(path k)))) /\
      (!t:asm_state. t.as_pc=b /\ LENGTH t.as_stack=h+extra /\
          t.as_call_ctx=cc /\ t.as_requests=req ==>
        t.as_pc=b+SND(f,0) /\ LENGTH t.as_stack=H(SND(f,0))+extra /\
        t.as_call_ctx=cc /\ t.as_requests=req /\
        (F ==> t.as_call_ctx.cc_static) /\
        (!k l origin. (NONE:(string#num)option) = SOME(l,origin) ==>
          k < H(SND(f,0))+extra /\ origin < LENGTH p /\
          (EL origin p=AsmPushLabel l \/ (?d. EL origin p=AsmPushOfst l d) \/
            EL origin p=AsmDataLabel l) /\
          ?off dest. FLOOKUP (SND(compute_label_offsets p)) l=SOME off /\
            off < dimword(:256) /\ FLOOKUP (build_offset_to_pc p) off=SOME dest /\
            EL k t.as_stack=(n2w off:bytes32)) /\
        (!k. F ==> k < H(SND(f,0))+extra /\
          (EL k t.as_stack=0w \/ EL k t.as_stack=1w)))
Proof
  disch_tac >> rpt gen_tac >> strip_tac >>
  first_x_assum (qspecl_then [`p`, `b`, `fmp`, `ops`, `h`] mp_tac) >>
  simp[] >> strip_tac >>
  `!k. k < LENGTH(execute_plan fmp ops) ==>
     b+k < LENGTH p /\ EL (b+k) p = EL k (execute_plan fmp ops) /\
     static_abort_admin (EL (b+k) p)` by
    (gen_tac >> strip_tac >>
     `EVERY static_abort_admin (execute_plan fmp ops)` by
       metis_tac[prefix_static_abort_admin] >>
     gvs[asm_block_at_def] >> metis_tac[EVERY_EL]) >>
  qexists `H` >> simp[] >> reverse conj_tac
  >- (rpt strip_tac >> gvs[] >>
      qexistsl [`k`, `\j. (f,j)`] >> simp[]) >>
  conj_tac
  >- (irule SUBSET_FINITE_I >>
      qexists `{f} CROSS count (SUC(LENGTH(execute_plan fmp ops)))` >>
      simp[SUBSET_DEF] >> rpt strip_tac >> gvs[]) >>
  conj_tac
  >- (rpt strip_tac >>
      qexists `ARB with <| as_pc := b+SND x;
        as_stack := REPLICATE (extra+H(SND x)) 0w;
        as_call_ctx := cc; as_requests := req |>` >> simp[]) >>
  conj_tac
  >- (rpt strip_tac >> gvs[] >>
      `k < LENGTH(execute_plan fmp ops)` by decide_tac >> metis_tac[]) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >>
      `x = (f,SND x)` by (Cases_on `x` >> gvs[]) >>
      `b+SND x < LENGTH p /\
       EL (b+SND x) p = EL (SND x) (execute_plan fmp ops) /\
       static_abort_admin (EL (b+SND x) p)` by metis_tac[] >>
      drule static_abort_admin_safe >> strip_tac >> simp[] >>
      qabbrev_tac `t0 = (ARB:asm_state) with
        <| as_pc := b+SND x;
           as_stack := REPLICATE (H(SND x)+extra) 0w |>` >>
      qpat_x_assum `!k extra t. _` (qspec_then `SND x` mp_tac) >>
      disch_then (qspecl_then [`extra`, `t0`] mp_tac) >>
      simp[Abbr `t0`] >> strip_tac >>
      conj_tac
      >- (Cases_on `x` >> gvs[]) >>
      `EL (SND x) (execute_plan fmp ops) <> AsmOp "JUMP"` by metis_tac[] >>
      simp[] >>
      qpat_x_assum `static_abort_normal _ _ _ _ _ _` mp_tac >>
      pure_rewrite_tac[static_abort_normal_def] >>
      disch_then (mp_tac o CONJUNCT1) >>
      CONV_TAC (LAND_CONV (ONCE_REWRITE_CONV [arithmeticTheory.ONE])) >>
      simp[asm_steps_def] >>
      strip_tac >>
      gvs[AllCaseEqs()] >>
      `static_abort_admin (EL (SND x) (execute_plan fmp ops))` by metis_tac[] >>
      drule_all admin_success_numerical_flow >>
      simp[]) >>
  rpt gen_tac >> strip_tac >> gvs[] >>
  `k < LENGTH(execute_plan fmp ops)` by decide_tac >>
  qpat_x_assum `!k extra t. _` drule >>
  disch_then (qspecl_then [`extra`, `t`] mp_tac) >> simp[] >>
  strip_tac >> disj2_tac >> qexists `u` >>
  gvs[static_abort_normal_def]
QED
