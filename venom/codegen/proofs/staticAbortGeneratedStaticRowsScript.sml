(* Structural tables for the generated static interval, interpreted at its cut. *)
Theory staticAbortGeneratedStaticRows
Ancestors staticAbortEmitRows[qualified,ignore_grammar] staticAbortChunk[qualified,ignore_grammar] marker[qualified,ignore_grammar] asmOptimizer[qualified,ignore_grammar]
  staticAbortRowsSplice staticAbortPlacedEmitRows staticAbortAdminRows
  staticAbortGeneratedStaticCut staticAbortGeneratedStaticFactors
  staticAbortGeneratedAdminMicro staticAbortOpenAdminFlow staticAbortRoleStep stackOpSim[qualified]
  codegenEncodingWf[qualified] fnPlanPlaceDfsBlock[qualified] codegen[qualified]
  staticAbortOptMergeIszeroBranchPackage[qualified] fnStaticAbortBoundary codegenSymRel
  contextStaticAbortRel unitShapeDefs
  staticAbortEmit staticAbortStraight symbolResolve staticAbortInst staticAbortDefs
  stackPlanGen planExec venomInst asmIR asmSem asmSymSem list rich_list
  arithmetic pred_set finite_map words pair option alist rat[qualified,ignore_grammar]

(* Quoted interfaces, not logical constants. *)
val flow_tm = ``
  \p pc height tag boolean (x:num#num) (y:num#num).
  !hi. hi = height x ==>
  !hj. hj = height y ==>
  !ins. ins = EL (pc x) p ==>
  !inherit. inherit = (
    \(src:num -> num option) (fresh:num -> (string#num)option) (bnew:num -> bool).
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
          (EL 0 u.as_stack=0w \/ EL 0 u.as_stack=1w))
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
             inherit (\k. SOME(if k=0 then n else if k=n then 0 else k)) (\k. NONE) (\k. F)
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

val reach_tm = ``\(edge:(num#num)->(num#num)->bool) e x.
  ?n (path:num->num#num).
    path 0=e /\ path n=x /\ !k. k<n ==> edge (path k) (path(SUC k))``;

val rows_tm = ``\Flow p cc V X (rank:num#num->num) pc height need tag boolean edge.
  !lo. lo = SND(compute_label_offsets p) ==>
  !otp. otp = build_offset_to_pc p ==>
  !target. target = (\x y.
    ?l origin off. tag x 0 = SOME(l,origin) /\ FLOOKUP lo l = SOME off /\
      off < dimword(:256) /\ FLOOKUP otp off = SOME(pc y)) ==>
  (!x. x IN V ==>
    (need x ==> cc.cc_static) /\
    (!k. boolean x k ==> k < height x /\ tag x k=NONE) /\
    (!k l origin. tag x k = SOME(l,origin) ==>
       k < height x /\ origin < LENGTH p /\
       (EL origin p = AsmPushLabel l \/ EL origin p = AsmPushOfst l 0) /\
       ?off dest. FLOOKUP lo l = SOME off /\ off < dimword(:256) /\
                  FLOOKUP otp off = SOME dest)) /\
  (!x y. edge x y ==> x IN V DIFF X /\ y IN V /\ rank y < rank x /\
    Flow p pc height tag boolean x y) /\
  (!x. x IN V DIFF X ==>
    pc x < LENGTH p /\
    (!h. h = height x ==>
    !fall. fall = (\y. pc y = pc x+1) ==>
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
        else
          (case ALOOKUP dup_table name of
             SOME n => n<h /\ next (h+1)
           | NONE => case ALOOKUP swap_table name of
               SOME n => 0<n /\ n<h /\ next h
             | NONE =>
                 if name="JUMP" then
                    1<=h /\ arm (target x) (h-1) /\ legal (target x) (h-1)
                 else if name="JUMPI" then
                    2<=h /\ tag x 1=NONE /\ arm fall (h-2) /\ arm (target x) (h-2) /\
                    legal (\y. fall y \/ target x y) (h-2)
                 else
                    ?m. static_abort_straight name m /\ asm_op_arity name <= h /\
                        untagged (asm_op_arity name) /\ next (h-asm_op_arity name+m))
    | _ => F))``;

val table_tm = ``\p cc f V X e (rank:num#num->num) I R.
  FINITE V /\ X SUBSET V /\ e IN V /\
  (!x. x IN V ==> FST x=f /\ ^reach_tm R e x) /\
  ^rows_tm ^flow_tm p cc V X rank (\x. FST (I x)) (\x. FST (SND (I x)))
    (\x. FST (SND (SND (I x)))) (\x. FST (SND (SND (SND (I x)))))
    (\x. SND (SND (SND (SND (I x))))) R``;

(* Recover the concrete predicates before replaying the existing row proofs. *)
val lets_conv = TOP_DEPTH_CONV
  (FIRST_CONV [HO_REWR_CONV UNWIND_FORALL_THM2, REWR_CONV LET_THM, BETA_CONV]);
val lets = CONV_TAC lets_conv;
val norm_lets = CONV_RULE lets_conv;
val admin_micro = norm_lets generated_admin_micro_coverage;

Theorem static_admin_rows[local]:
  !p cc f b fmp ops h extra.
  prefix_wf (SND(compute_label_offsets p)) h ops /\
  asm_block_at p b (execute_plan fmp ops) ==>
  ?V e z rank I edge.
    ^table_tm p cc f V {z} e rank I edge /\
    I e=(b,h+extra,F,(\_:num. NONE:(string#num)option),(\_:num. F)) /\
    I z=(b+LENGTH(execute_plan fmp ops),
         prefix_end_len (SND(compute_label_offsets p)) h ops+extra,
         F,(\_:num. NONE:(string#num)option),(\_:num. F))
Proof
  rpt gen_tac >> strip_tac >>
  mp_tac (MATCH_MP admin_prefix_open_fragment admin_micro) >>
  disch_then (qspecl_then [`p`,`b`,`fmp`,`ops`,`h`,`extra`,`f`,`cc`,
                           `[]:call_request list`] mp_tac) >>
  asm_simp_tac std_ss [] >> strip_tac >>
  lets >>
  qexistsl [`{(f,k) | k <= LENGTH(execute_plan fmp ops)}`,
    `(f,0)`,`(f,LENGTH(execute_plan fmp ops))`,
    `\x. LENGTH(execute_plan fmp ops)-SND x`,
    `\x. (b+SND x,H(SND x)+extra,F,(\_:num. NONE:(string#num)option),(\_:num. F))`,
    `\x y. FST x=f /\ SND x<LENGTH(execute_plan fmp ops) /\ y=(f,SUC(SND x))`] >>
  lets >> asm_simp_tac std_ss [] >>
  conj_tac >- simp[] >>
  conj_tac
  >- (rpt gen_tac >> disch_tac >> gvs[]) >>
  qx_gen_tac `x` >> disch_tac >>
  `FST x=f /\ SND x<LENGTH(execute_plan fmp ops)` by
    (Cases_on `x` >> fs[IN_DIFF] >> decide_tac) >>
  `EL (b+SND x) p = EL (SND x) (execute_plan fmp ops)` by
    (qpat_assum `asm_block_at _ _ _` (strip_assume_tac o REWRITE_RULE [asm_block_at_def]) >>
     first_x_assum irule >> simp[]) >>
  `MEM (EL (b+SND x) p) (execute_plan fmp ops)` by metis_tac[EL_MEM] >>
  drule_all pending_admin_instruction_rows >> disch_then assume_tac >>
  qpat_x_assum `EL (b+SND x) p = EL _ _` kall_tac >>
  qpat_x_assum `!x. FST x=f /\ SND x < _ ==> _`
    (qspec_then `x` mp_tac) >>
  (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
  strip_tac >>
  `b + SUC (SND x) = b + SND x + 1` by decide_tac >>
  Cases_on `EL (b+SND x) p` >>
  gnvs[asm_inst_case_def] >>
  rename1 `EL (b+SND x) p = AsmOp name` >>
  suspend "opcode"
QED

Resume static_admin_rows[opcode]:
  `name <> "INVALID" /\ name <> "REVERT" /\
   ~MEM name ["SSTORE";"TSTORE";"LOG0";"LOG1";"LOG2";"LOG3";"LOG4"] /\
   name <> "JUMP" /\ name <> "JUMPI"` by
    (qpat_assum `(?n. ALOOKUP dup_table name = SOME n /\ _) \/ _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> simp[] >> strip_tac >>
     rpt conj_tac >> strip_tac >> gvs[] >> fs[dup_table_def,swap_table_def]) >>
  `name <> "SSTORE" /\ name <> "TSTORE" /\ name <> "LOG0" /\
   name <> "LOG1" /\ name <> "LOG2" /\ name <> "LOG3" /\ name <> "LOG4"` by fs[] >>
  Cases_on `ALOOKUP dup_table name` >>
  NO_STRIP_FULL_SIMP_TAC bool_ss [option_case_def,optionTheory.NOT_NONE_SOME] >>
  Cases_on `ALOOKUP swap_table name` >>
  NO_STRIP_FULL_SIMP_TAC bool_ss [option_case_def,optionTheory.NOT_NONE_SOME] >>
  suspend "ordinary"
QED

Resume static_admin_rows[ordinary]:
  qpat_assum `!a t. _ ==> _ \/ _` (qspec_then `x` assume_tac) >>
  qpat_assum `!a. _ ==> ?t. t.as_pc = _ /\ _`
    (qspec_then `x` mp_tac) >>
  (impl_tac >- (qpat_assum `_ /\ x <> _` (ACCEPT_TAC o CONJUNCT1))) >>
  disch_then (qx_choose_then `t` strip_assume_tac) >>
  `t.as_pc < LENGTH p /\ asm_op_arity name <= LENGTH t.as_stack` by
    metis_tac[] >>
  `?u m. asm_step (SND(compute_label_offsets p)) (build_offset_to_pc p)
                (AsmOp name) t = AsmOK u /\
         static_abort_straight name m /\
         LENGTH u.as_stack = LENGTH t.as_stack - asm_op_arity name + m` by
    (qpat_x_assum `name = "POP" \/ _` strip_assume_tac >>
     gvs[EVAL ``asm_op_arity "POP"``, EVAL ``asm_op_arity "MSTORE"``,
         EVAL ``asm_op_arity "MLOAD"``] >>
     TRY (`t.as_stack <> []` by (strip_tac >> fs[]))
     >- (drule stackOpAsmSimTheory.asm_step_pop_ok >>
         disch_then (qspecl_then [`SND(compute_label_offsets p)`,`build_offset_to_pc p`] strip_assume_tac) >>
         qexists `asm_next (t with as_stack := stk)` >> qexists `0` >>
         simp[asm_next_def,static_abort_straight_def] >> decide_tac)
     >- (qspecl_then [`SND(compute_label_offsets p)`,`build_offset_to_pc p`,`t`]
          mp_tac stackOpAsmSimTheory.asm_step_mstore_ok >>
         simp[GREATER_EQ] >> strip_tac >> qexistsl [`s2`,`0`] >>
         simp[static_abort_straight_def] >> decide_tac) >>
     drule stackOpAsmSimTheory.asm_step_mload_ok >>
     disch_then (qspecl_then [`SND(compute_label_offsets p)`,`build_offset_to_pc p`] strip_assume_tac) >>
     qexistsl [`s2`,`1`] >> simp[static_abort_straight_def] >> decide_tac) >>
  `asm_steps (SND(compute_label_offsets p)) (build_offset_to_pc p) p 1 t = AsmOK u` by
    (qpat_assum `t.as_pc < LENGTH p` (mp_then Any assume_tac asmOpSimTheory.asm_step_one) >>
     metis_tac[]) >>
  `LENGTH u.as_stack = extra + H (SUC (SND x))` by
    (qpat_assum `!s. _ ==> _ \/ _` (qspec_then `t` mp_tac) >>
     (impl_tac >- metis_tac[]) >>
     disch_then (fn row =>
       qpat_assum `asm_steps _ _ p 1 t = AsmOK u` (fn step =>
         strip_assume_tac (REWRITE_RULE [step,asm_result_distinct,asm_result_11] row))) >>
     metis_tac[]) >>
  qexists `m` >> conj_tac >- first_assum ACCEPT_TAC >>
  qpat_assum `LENGTH u.as_stack = LENGTH t.as_stack - _ + m` mp_tac >>
  qpat_assum `LENGTH u.as_stack = extra + H (SUC (SND x))` mp_tac >>
  qpat_assum `LENGTH t.as_stack = _` mp_tac >>
  qpat_assum `_ /\ extra + H (SUC (SND x)) = _` (mp_tac o CONJUNCT2) >>
  POP_ASSUM_LIST (K ALL_TAC) >> decide_tac
QED

Finalise static_admin_rows

Theorem static_placed_rows[local]:
  !p b f cc fmp inst topics ps6 emit ps7 H.
  !code. code = execute_plan fmp emit ==>
  !lo. lo = SND (compute_label_offsets p) ==>
  !invmap. invmap = build_offset_to_pc p ==>
  !iface. iface = (\a n. (a,n,F,(\_:num. NONE:(string#num)option),(\_:num. F))) ==>
  generate_emit_ops inst topics ps6=(emit,ps7) /\ asm_block_at p b code ==>
  (!nin nout.
    ~is_terminator inst.inst_opcode /\
    ~MEM inst.inst_opcode [INVOKE;CALL;STATICCALL;DELEGATECALL;CREATE;CREATE2;
                           SSTORE;TSTORE;LOG] /\
    static_abort_emit_io inst nin nout /\ nin<=H /\
    static_abort_emit_labels lo invmap p fmp b inst emit /\
    (inst.inst_opcode=ASSERT ==>
       ?off dest. FLOOKUP lo "revert"=SOME off /\ off<dimword(:256) /\
         FLOOKUP invmap off=SOME dest) /\
    (inst.inst_opcode=ASSERT_UNREACHABLE ==>
       !lbl. emit=[SOPushLabel lbl;SOEmit "JUMPI";SOEmit "INVALID";SOLabel lbl] ==>
         ?off dest. FLOOKUP lo lbl=SOME off /\ off<dimword(:256) /\
           FLOOKUP invmap off=SOME dest) ==>
     ?V e z rank I edge.
       ^table_tm p cc f V {z} e rank I edge /\ I e=iface b H /\
       I z=iface (b+LENGTH code) (H-nin+nout)) /\
  (MEM inst.inst_opcode [SSTORE;TSTORE;LOG] /\
   (inst.inst_opcode=LOG ==> topics<=4) /\
   (if inst.inst_opcode=LOG then 2+topics else 2)<=H /\ cc.cc_static ==>
     ?e rank I edge.
       ^table_tm p cc f {e} {} e rank I edge /\ I e=iface b H)
Proof
  lets >> rpt gen_tac >> strip_tac >>
  drule_all (norm_lets placed_static_emit_rows) >>
  disch_then (qspecl_then [`f`,`cc`,`H`] mp_tac) >>
  disch_then (CONJUNCTS_THEN2 (mk_asm "continuing") (mk_asm "terminal")) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> asm "continuing" drule_all >> strip_tac >>
      qexistsl [`V`,`e`,`z`,`rank`,
        `\x. (pc x,height x,need x,tag x,boolean x)`,`edge`] >>
      lets >> pure_rewrite_tac [FST,SND,GSYM CONJ_ASSOC] >>
      RULE_ASSUM_TAC (PURE_REWRITE_RULE [GSYM CONJ_ASSOC]) >>
      rpt (conj_tac >- first_assum ACCEPT_TAC) >>
      simp[PAIR_EQ,FUN_EQ_THM]) >>
  strip_tac >> asm "terminal" drule_all >> strip_tac >>
  qexistsl [`e`,`rank`,`\x. (pc x,height x,need x,tag x,boolean x)`,`edge`] >>
  lets >> pure_rewrite_tac [FST,SND,GSYM CONJ_ASSOC] >>
      RULE_ASSUM_TAC (PURE_REWRITE_RULE [GSYM CONJ_ASSOC]) >>
      rpt (conj_tac >- first_assum ACCEPT_TAC) >>
      simp[PAIR_EQ,FUN_EQ_THM]
QED

Theorem static_rows_prepend[local]:
  !p cc f V1 V2 e1 e2 z r1 r2 I1 I2 R1 R2.
    ^table_tm p cc f V1 {z} e1 r1 I1 R1 /\
    ^table_tm p cc f V2 {} e2 r2 I2 R2 /\ I1 z=I2 e2 ==>
    ?V e rank I edge. ^table_tm p cc f V {} e rank I edge /\ I e=I1 e1
Proof
  rpt gen_tac >> disch_tac >>
  qspecl_then [`p`,`cc`,`f`,`V1`,`{}` ,`e1`,`e2`,`z`,`r1`,`r2`,
               `I1`,`I2`,`R1`,`R2`]
    (mp_tac o PURE_REWRITE_RULE [GSYM CONJ_ASSOC] o norm_lets)
    bounded_static_rows_splice >>
  lets >> pure_rewrite_tac [IMAGE_EMPTY, GSYM CONJ_ASSOC] >>
  RULE_ASSUM_TAC (PURE_REWRITE_RULE [GSYM CONJ_ASSOC] o norm_lets) >>
  (impl_tac >- first_assum ACCEPT_TAC) >>
  disch_then (qx_choose_then `rr` (qx_choose_then `iface`
    (EVERY o map assume_tac o CONJUNCTS))) >>
  qexistsl [`IMAGE (\x. (f,2*SND x)) (V1 DELETE z) UNION IMAGE (\x. (f,2*SND x+1)) V2`,
            `if e1=z then (f,2*SND e2+1) else (f,2*SND e1)`,`rr`,`iface`,
            `\a b. (?x y. R1 x y /\ a=(f,2*SND x) /\
                           b=(if y=z then (f,2*SND e2+1) else (f,2*SND y))) \/
                    (?x y. R2 x y /\ a=(f,2*SND x+1) /\ b=(f,2*SND y+1))`] >>
  lets >> pure_rewrite_tac [GSYM CONJ_ASSOC] >>
  rpt (conj_tac >- first_assum ACCEPT_TAC) >> first_assum ACCEPT_TAC
QED

val empty_iface_tm = ``\(a:num) (n:num). (a,n,F,(\_:num. NONE:(string#num)option),(\_:num. F))``;
val closed_tm = ``\p cc f root.
  ?V e rank I edge. ^table_tm p cc f V {} e rank I edge /\ I e=root``;
val continuing_tm = ``\p cc f root exit.
  ?V e z rank I edge. ^table_tm p cc f V {z} e rank I edge /\ I e=root /\ I z=exit``;

Theorem static_rows_link[local]:
  !p cc f root mid.
    ^continuing_tm p cc f root mid /\ ^closed_tm p cc f mid ==>
    ^closed_tm p cc f root
Proof
  rpt gen_tac >> lets >>
  disch_then (CONJUNCTS_THEN2
    (qx_choose_then `V1` (qx_choose_then `e1` (qx_choose_then `z1`
     (qx_choose_then `r1` (qx_choose_then `I1` (qx_choose_then `E1`
       (CONJUNCTS_THEN2 (mk_asm "head") strip_assume_tac)))))))
    (qx_choose_then `V2` (qx_choose_then `e2`
     (qx_choose_then `r2` (qx_choose_then `I2` (qx_choose_then `E2`
       (CONJUNCTS_THEN2 (mk_asm "tail") assume_tac))))))) >>
  qspecl_then [`p`,`cc`,`f`,`V1`,`V2`,`e1`,`e2`,`z1`,`r1`,`r2`,`I1`,`I2`,`E1`,`E2`]
    mp_tac (norm_lets static_rows_prepend) >>
  (impl_tac >- (conj_tac >- asm "head" ACCEPT_TAC >>
                conj_tac >- asm "tail" ACCEPT_TAC >> simp[])) >>
  qpat_assum `I1 e1 = root` (fn th => disch_then (ACCEPT_TAC o PURE_REWRITE_RULE [th]))
QED

Theorem static_interval_rows[local]:
  !unit cplan rpolicy prog lv dfg cfg ch growth base ctr fn fn_ops ps_end
   lbl bb ps_l ps_dfs ps_dfs_after height promised block_ops ps_after
   j cc f extra.
  generate_context_plan unit.cu_context = SOME cplan /\
  codegen_assembly rpolicy unit = SOME prog /\
  lv = liveness_analyze fn /\ dfg = dfg_build_function fn /\ cfg = cfg_analyze fn /\
  codegen_ready_fn fn /\
  generate_fn_plan_with_cleanup_analyzed lv dfg cfg ch growth fn base ctr =
    SOME (fn_ops,ps_end) /\
  lookup_block lbl fn.fn_blocks = SOME bb /\ bb.bb_label = lbl /\
  lineage_state lv dfg cfg fn (init_cleanup_plan_state ch growth base ctr) lbl ps_l /\
  dfs_block_state lv dfg cfg fn (init_cleanup_plan_state ch growth base ctr) lbl ps_dfs /\
  generate_block_plan lv dfg cfg fn bb ps_dfs = SOME (block_ops,ps_dfs_after) /\
  generate_block_plan lv dfg cfg fn bb
    (ps_l with <|ps_cleanup_height := height; ps_cleanup_promised := promised|>) =
    SOME (block_ops,ps_after) /\
  non_param_insts bb = DROP (LENGTH (get_params bb.bb_instructions)) bb.bb_instructions /\
  EVERY inst_shape_ok bb.bb_instructions /\ EVERY codegen_ready_inst bb.bb_instructions /\
  cc.cc_static ==>
  !i ps ops qs pc.
  block_plan_state lv dfg cfg fn bb
    (ps_l with <|ps_cleanup_height := height; ps_cleanup_promised := promised|>) i ps /\
  phi_prefix_length bb.bb_instructions <= i /\
  LENGTH (get_params bb.bb_instructions) <= i /\
  static_abort_pair bb i j /\
  generate_block_insts_prefix lv dfg cfg fn lbl (bb_is_halting bb)
    (LENGTH (get_params bb.bb_instructions)) (LENGTH bb.bb_instructions)
    (i - LENGTH (get_params bb.bb_instructions)) (SUC j - i)
    (DROP i bb.bb_instructions) ps = SOME (ops,qs) /\
  (!k inst l. i <= k /\ k <= j /\ get_instruction bb k = SOME inst /\
     MEM (Label l) (compute_operands inst) ==>
     IS_SOME (FLOOKUP (SND (compute_label_offsets prog)) l)) /\
  asm_block_at prog pc (execute_plan cplan.cp_initial_fmp ops) ==>
  ^closed_tm prog cc f (^empty_iface_tm pc (LENGTH ps.ps_stack+extra))
Proof
  rpt gen_tac >> strip_tac >>
  measureInduct_on `SUC j - i` >> rpt gen_tac >> strip_tac >>
  drule_all generated_static_head_factors >>
  disch_then (qx_choose_then `a` (qx_choose_then `mid` (qx_choose_then `b`
    (EVERY o map assume_tac o CONJUNCTS))) o SPEC_ALL) >>
  `i <= j /\ j < LENGTH bb.bb_instructions` by fs[static_abort_pair_def] >>
  qabbrev_tac `fmp = cplan.cp_initial_fmp` >>
  Cases_on `i=j`
  >- suspend "terminal_head" >>
  `i < j` by decide_tac >>
  `^closed_tm prog cc f
     (^empty_iface_tm (pc+LENGTH(execute_plan fmp a)) (LENGTH mid.ps_stack+extra))` by
    suspend "tail" >>
  pop_assum (mk_asm "tail_table") >>
  qpat_x_assum `!inst. inst = _ ==> _` (mp_tac o norm_lets) >>
  disch_then (DISJ_CASES_THEN2 strip_assume_tac strip_assume_tac)
  >- suspend "nop" >>
  suspend "regular_head"
QED

Resume static_interval_rows[tail]:
  qpat_x_assum `!y. SUC j - y < _ ==> _` (qspec_then `SUC i` mp_tac) >>
  (impl_tac >- decide_tac) >>
  disch_then (qspecl_then [`mid`,`b`,`qs`,`pc+LENGTH(execute_plan fmp a)`] mp_tac) >>
  (impl_tac >-
    (conj_tac >- first_assum ACCEPT_TAC >>
     conj_tac >- decide_tac >> conj_tac >- decide_tac >>
     conj_tac >- metis_tac[] >>
     conj_tac >- first_assum ACCEPT_TAC >>
     reverse conj_tac >- first_assum ACCEPT_TAC >>
     rpt strip_tac >> qpat_assum `!k inst l. i <= k /\ _ ==> _` irule >>
     qexistsl [`inst`,`k`] >> simp[] >> decide_tac)) >>
  disch_then ACCEPT_TAC
QED

Resume static_interval_rows[nop]:
  qpat_x_assum `a=[]` SUBST_ALL_TAC >>
  qpat_x_assum `mid=ps` SUBST_ALL_TAC >>
  `pc+LENGTH(execute_plan fmp [])=pc` by simp[execute_plan_def] >>
  pop_assum SUBST_ALL_TAC >> asm "tail_table" ACCEPT_TAC
QED

Resume static_interval_rows[terminal_head]:
  qpat_x_assum `!inst. inst = _ ==> _` (mp_tac o norm_lets) >>
  disch_then (DISJ_CASES_THEN2 strip_assume_tac strip_assume_tac)
  >- (`F` suffices_by simp[] >>
      qpat_assum `static_abort_pair bb i j` mp_tac >>
      qpat_assum `i=j` mp_tac >>
      qpat_assum `(EL i bb.bb_instructions).inst_opcode = NOP` mp_tac >>
      POP_ASSUM_LIST (K ALL_TAC) >> rpt strip_tac >> gvs[static_abort_pair_def]) >>
  qmatch_asmsub_abbrev_tac `generate_emit_ops inst topics ps6` >>
  qspecl_then [`prog`,`cc`,`f`,
    `^empty_iface_tm pc (LENGTH ps.ps_stack+extra)`,
    `^empty_iface_tm (pc+LENGTH(execute_plan fmp pre)) (m+extra)`]
    MATCH_MP_TAC static_rows_link >>
  conj_tac
  >- (qspecl_then [`prog`,`cc`,`f`,`pc`,`fmp`,`pre`,`LENGTH ps.ps_stack`,`extra`]
        mp_tac (norm_lets static_admin_rows) >>
      (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
      lets >> qpat_assum `prefix_end_len _ _ pre=m` (fn len =>
        disch_then (ACCEPT_TAC o PURE_REWRITE_RULE [len] o norm_lets))) >>
  qpat_x_assum `i=j ==> _` drule >> strip_tac >>
  `(if inst.inst_opcode=LOG then 2+topics else 2) <= m+extra` by (gvs[staticAbortGeneratedStaticFactorsTheory.generated_static_head_factors, staticAbortInstTheory.static_abort_inst_terminal, staticAbortInstTheory.static_abort_inst_progress, staticAbortPlacedEmitRowsTheory.placed_static_emit_rows, staticAbortInstTheory.static_abort_regular_inst_terminal, staticAbortInstTheory.static_abort_regular_inst_progress, staticAbortEmitRowsTheory.pending_static_emit_rows, staticAbortChunkTheory.static_abort_chunk_terminal, markerTheory.Abbrev_def, staticAbortDefsTheory.static_abort_pair_def, staticAbortEmitTheory.static_abort_emit_io_def, asmOptimizerTheory.asm_returns_zero_or_one_def, staticAbortStraightTheory.static_abort_straight_def, asmSemTheory.dup_table_def, asmSemTheory.swap_table_def, asmSymSemTheory.asm_op_arity_def]) >>
  drule_all (norm_lets static_placed_rows) >>
  disch_then (qspecl_then [`f`,`cc`,`m+extra`] (mp_tac o CONJUNCT2)) >>
  (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
  disch_then (qx_choose_then `et` (qx_choose_then `rt` (qx_choose_then `It`
    (qx_choose_then `Et` (CONJUNCTS_THEN2 (mk_asm "emitter") assume_tac))))) >>
  lets >> qexistsl [`{et}`,`et`,`rt`,`It`,`Et`] >>
  conj_tac >- asm "emitter" ACCEPT_TAC >> first_assum ACCEPT_TAC
QED

Resume static_interval_rows[regular_head]:
  qmatch_asmsub_abbrev_tac `generate_emit_ops inst topics ps6` >>
  qpat_x_assum `i < j ==> ?nin nout. _` drule >> strip_tac >>
  `~is_terminator inst.inst_opcode /\
    ~MEM inst.inst_opcode [INVOKE;CALL;STATICCALL;DELEGATECALL;CREATE;CREATE2;
                           SSTORE;TSTORE;LOG]` by
    (qpat_assum `static_abort_pair bb i j`
      (mp_tac o CONJUNCT2 o CONJUNCT2 o CONJUNCT2 o
        REWRITE_RULE [static_abort_pair_def]) >>
     disch_then (qspecl_then [`i`, `inst`] mp_tac) >>
     qpat_assum `Abbrev (inst = _)` mp_tac >>
     qpat_assum `static_abort_pair bb i j` mp_tac >>
     qpat_assum `i < j` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     simp[markerTheory.Abbrev_def, get_instruction_def, static_abort_pair_def] >>
     rpt strip_tac >> first_x_assum irule >> decide_tac) >>
  suspend "regular_labels"
QED

Resume static_interval_rows[regular_labels]:
  `static_abort_emit_labels (SND (compute_label_offsets prog))
     (build_offset_to_pc prog) prog fmp
     (pc + LENGTH (execute_plan fmp pre)) inst emit` by
    (qpat_assum `asm_block_at prog (pc + LENGTH (execute_plan fmp pre))
       (execute_plan fmp emit)` mp_tac >>
     qpat_assum `generate_context_plan unit.cu_context = SOME cplan` mp_tac >>
     qpat_assum `codegen_assembly rpolicy unit = SOME prog` mp_tac >>
     simp_tac std_ss [Abbr `fmp`] >> rpt disch_tac >>
     drule_all static_abort_generated_emit_labels >>
     disch_then (qspec_then `inst` ACCEPT_TAC)) >>
  `!l off. FLOOKUP (SND (compute_label_offsets prog)) l = SOME off ==>
     off < dimword(:256)` by
    (qpat_assum `codegen_assembly rpolicy unit = SOME prog`
       (mp_tac o REWRITE_RULE [codegenTheory.asm_symbols_ok_def] o
         MATCH_MP fnPlanPlaceDfsBlockTheory.codegen_assembly_symbols_ok) >>
     qspec_then `prog` (mp_tac o CONJUNCT2) codegenEncodingWfTheory.compute_label_offsets_bound >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     rpt strip_tac >> first_x_assum drule >>
     simp_tac std_ss [dimword_def] >> simp[]) >>
  `(inst.inst_opcode = ASSERT ==>
      ?off dest. FLOOKUP (SND(compute_label_offsets prog)) "revert"=SOME off /\
        off<dimword(:256) /\ FLOOKUP (build_offset_to_pc prog) off=SOME dest) /\
   (inst.inst_opcode = ASSERT_UNREACHABLE ==>
      !lbl. emit=[SOPushLabel lbl;SOEmit "JUMPI";SOEmit "INVALID";SOLabel lbl] ==>
        ?off dest. FLOOKUP (SND(compute_label_offsets prog)) lbl=SOME off /\
          off<dimword(:256) /\ FLOOKUP (build_offset_to_pc prog) off=SOME dest)` by
    (qpat_assum `static_abort_emit_labels _ _ _ _ _ _ _`
       (mp_tac o REWRITE_RULE [static_abort_emit_labels_def]) >>
     qpat_assum `!l off. FLOOKUP _ l = SOME off ==> _` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >>
     strip_tac >> strip_tac >> conj_tac >> rpt strip_tac >>
     first_x_assum drule_all >> strip_tac >>
     `off < dimword(:256)` by metis_tac[] >>
     qexists_tac `off` >> simp[w2n_n2w_compute] >>
     metis_tac[w2n_n2w_compute]) >>
  suspend "regular_splice"
QED

Resume static_interval_rows[regular_splice]:
  `(m+extra)-nin+nout=h+extra /\ nin<=m+extra` by
    (qpat_assum `nin <= m` mp_tac >> qpat_assum `h+nin=m+nout` mp_tac >>
     POP_ASSUM_LIST (K ALL_TAC) >> decide_tac) >>
  `pc+LENGTH (execute_plan fmp a) =
   pc+LENGTH (execute_plan fmp pre)+LENGTH (execute_plan fmp emit)+
      LENGTH (execute_plan fmp post)` by
    (qpat_assum `a=pre++emit++post` mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >>
     simp[stackOpSimTheory.execute_plan_append] >> decide_tac) >>
  qspecl_then [`prog`,`cc`,`f`,
    `^empty_iface_tm pc (LENGTH ps.ps_stack+extra)`,
    `^empty_iface_tm (pc+LENGTH(execute_plan fmp pre)) (m+extra)`]
    MATCH_MP_TAC static_rows_link >>
  conj_tac
  >- (qspecl_then [`prog`,`cc`,`f`,`pc`,`fmp`,`pre`,`LENGTH ps.ps_stack`,`extra`]
        mp_tac (norm_lets static_admin_rows) >>
      (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
      lets >> qpat_assum `prefix_end_len _ _ pre=m` (fn len =>
        disch_then (ACCEPT_TAC o PURE_REWRITE_RULE [len] o norm_lets))) >>
  qspecl_then [`prog`,`cc`,`f`,
    `^empty_iface_tm (pc+LENGTH(execute_plan fmp pre)) (m+extra)`,
    `^empty_iface_tm (pc+LENGTH(execute_plan fmp pre)+LENGTH(execute_plan fmp emit)) (h+extra)`]
    MATCH_MP_TAC static_rows_link >>
  conj_tac
  >- (drule_all (norm_lets static_placed_rows) >>
      disch_then (qspecl_then [`f`,`cc`,`m+extra`] (mp_tac o CONJUNCT1)) >>
      disch_then (qspecl_then [`nin`,`nout`] mp_tac) >>
      (impl_tac >- (rpt conj_tac >> first_assum ACCEPT_TAC)) >>
      lets >> qpat_assum `(m+extra)-nin+nout=h+extra` (fn len =>
        disch_then (ACCEPT_TAC o PURE_REWRITE_RULE [len]))) >>
  suspend "regular_post"
QED

Resume static_interval_rows[regular_post]:
  qspecl_then [`prog`,`cc`,`f`,
    `^empty_iface_tm (pc+LENGTH(execute_plan fmp pre)+LENGTH(execute_plan fmp emit)) (h+extra)`,
    `^empty_iface_tm (pc+LENGTH(execute_plan fmp a)) (LENGTH mid.ps_stack+extra)`]
    MATCH_MP_TAC static_rows_link >>
  reverse conj_tac >- asm "tail_table" ACCEPT_TAC >>
  qspecl_then [`prog`,`cc`,`f`,`pc+LENGTH(execute_plan fmp pre)+LENGTH(execute_plan fmp emit)`,
    `fmp`,`post`,`h`,`extra`] mp_tac (norm_lets static_admin_rows) >>
  (impl_tac >- (conj_tac >> first_assum ACCEPT_TAC)) >>
  lets >> qpat_assum `prefix_end_len _ _ post = LENGTH mid.ps_stack` (fn len =>
    qpat_assum `pc+LENGTH(execute_plan fmp a) = _` (fn loc =>
      disch_then (ACCEPT_TAC o PURE_REWRITE_RULE [len,GSYM loc] o norm_lets)))
QED

Finalise static_interval_rows

val target_tm = ``\p pc (tag:(num#num)->num->(string#num)option) (x:num#num) (y:num#num).
  ?l origin off. tag x 0 = SOME(l,origin) /\
    FLOOKUP (SND(compute_label_offsets p)) l = SOME off /\
    off < dimword(:256) /\ FLOOKUP (build_offset_to_pc p) off = SOME (pc y)``;

Theorem static_row_edge_control[local]:
  !p cc V rank pc height need tag boolean edge x y.
    ^rows_tm ^flow_tm p cc V {} rank pc height need tag boolean edge /\ edge x y ==>
    ^flow_tm p pc height tag boolean x y /\
    (if EL (pc x) p = AsmOp "JUMP" then ^target_tm p pc tag x y
     else if EL (pc x) p = AsmOp "JUMPI" then pc y=pc x+1 \/ ^target_tm p pc tag x y
     else pc y=pc x+1)
Proof
  rpt gen_tac >> lets >>
  disch_then (CONJUNCTS_THEN2
    (CONJUNCTS_THEN2 kall_tac (CONJUNCTS_THEN2 (mk_asm "edges") (mk_asm "rows")))
    assume_tac) >>
  asm "edges" (qspecl_then [`x`,`y`] (drule_then strip_assume_tac)) >>
  conj_tac >- first_assum ACCEPT_TAC >>
  asm "rows" (qspec_then `x` (drule_then (mp_tac o CONJUNCT2))) >>
  qpat_assum `edge x y` mp_tac >> POP_ASSUM_LIST (K ALL_TAC) >>
  Cases_on `EL (pc x) p` >> simp[asm_inst_case_def,Excl "MEM"] >>
  TRY (rename1 `EL (pc x) p = AsmOp name` >> suspend "opcode") >> metis_tac[]
QED

Resume static_row_edge_control[opcode]:
  Cases_on `name="JUMP"` >- simp[dup_table_def,swap_table_def] >>
  Cases_on `name="JUMPI"` >- simp[dup_table_def,swap_table_def] >>
  simp[Excl "MEM"] >>
  Cases_on `name="INVALID"` >- (simp[Excl "MEM"] >> metis_tac[]) >>
  Cases_on `name="REVERT"` >- (simp[Excl "MEM"] >> metis_tac[]) >>
  simp[Excl "MEM"] >> COND_CASES_TAC >- metis_tac[] >>
  Cases_on `ALOOKUP dup_table name` >> simp[] >>
  TRY (Cases_on `ALOOKUP swap_table name` >> simp[]) >> metis_tac[]
QED

Finalise static_row_edge_control

val shape_tm = ``\p cc req pc height need tag boolean (i:num#num) (t:asm_state).
    t.as_pc = pc i /\ LENGTH t.as_stack = height i /\
    t.as_call_ctx = cc /\ t.as_requests = req /\
    (need i ==> t.as_call_ctx.cc_static) /\
    (!k l origin. tag i k = SOME(l,origin) ==>
       k < height i /\ origin < LENGTH p /\
       (EL origin p = AsmPushLabel l \/
        (?d. EL origin p = AsmPushOfst l d) \/ EL origin p = AsmDataLabel l) /\
       ?off dest. FLOOKUP (SND(compute_label_offsets p)) l = SOME off /\
         off < dimword(:256) /\
         FLOOKUP (build_offset_to_pc p) off = SOME dest /\
         EL k t.as_stack = (n2w off:bytes32)) /\
    (!k. boolean i k ==> k < height i /\
       (EL k t.as_stack = 0w \/ EL k t.as_stack = 1w))``;

val open_tm = ``\S Flow p (cc:call_context) req (V:(num#num)->bool) X
  (rank:(num#num)->num) pc (height:(num#num)->num) (need:(num#num)->bool)
  tag (boolean:(num#num)->num->bool) edge.
  !S_here. S_here = S p cc req pc height need tag boolean ==>
  !target. target = ^target_tm p pc tag ==>
  FINITE V /\ X SUBSET V /\
  (!x. x IN V ==> ?t. S_here x t) /\
  (!x. x IN V DIFF X ==> pc x < LENGTH p) /\
  (!x y. edge x y ==>
     x IN V DIFF X /\ y IN V /\ rank y < rank x /\
     Flow p pc height tag boolean x y /\
     (if EL (pc x) p = AsmOp "JUMP" then target x y
      else if EL (pc x) p = AsmOp "JUMPI" then pc y = pc x+1 \/ target x y
      else pc y = pc x+1)) /\
  (!x t. x IN V DIFF X /\ S_here x t ==>
     (?u. (asm_steps (SND(compute_label_offsets p)) (build_offset_to_pc p)
                  p 1 t = AsmRevert u \/
            asm_steps (SND(compute_label_offsets p)) (build_offset_to_pc p)
                  p 1 t = AsmFault u) /\ u.as_requests=req) \/
     (?y u. edge x y /\
        asm_steps (SND(compute_label_offsets p)) (build_offset_to_pc p)
          p 1 t = AsmOK u /\ S_here y u))``;

Theorem generated_static_cut_rows_reloc:
  !Shape. Shape = ^shape_tm ==>
  !Flow. Flow = ^flow_tm ==>
  body_inv_abort_reloc rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
    block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 cvs cut Inv
    ra pc_ret rest mem0 /\
  (!f inst l.
    MEM f ctx.ctx_functions /\ MEM inst (fn_insts f) /\
    inst.inst_opcode <> PHI /\ MEM (Label l) (compute_operands inst) ==>
    IS_SOME (FLOOKUP (SND (compute_label_offsets prog)) l)) /\
  in_static_abort_prefix fn cvs ==>
  ?V e rank pc height need tag boolean edge.
    ^open_tm Shape Flow prog cut.as_call_ctx cut.as_requests V {} rank pc height need tag boolean edge /\
    ^rows_tm Flow prog cut.as_call_ctx V {} rank pc height need tag boolean edge /\
    e IN V /\ (!x. x IN V ==> ^reach_tm edge e x) /\
    Shape prog cut.as_call_ctx cut.as_requests pc height need tag boolean e cut /\
    (!j. tag e j=NONE /\ ~boolean e j)
Proof
  lets >> strip_tac >>
  drule_all (Q.INST [`row_lo` |-> `SND (compute_label_offsets prog)`]
    generated_static_cut_interval_reloc) >> strip_tac >>
  `bb.bb_label = bb.bb_label` by REFL_TAC >>
  drule_all (norm_lets static_interval_rows) >>
  disch_then (qspecl_then [`0:num`, `LENGTH cut.as_stack - LENGTH ps.ps_stack`] assume_tac) >>
  suspend "certify"
QED

Resume generated_static_cut_rows_reloc[certify]:
  qpat_x_assum `?V e rank I edge. _` (REPEAT_TCL CHOOSE_THEN
    (CONJUNCTS_THEN2 (mk_asm "table") (mk_asm "entry"))) >>
  qmatch_asmsub_rename_tac `iface e = (cut.as_pc,_,F,_,_)` >>
  asm_x "table" (CONJUNCTS_THEN2 (mk_asm "finite")
    (CONJUNCTS_THEN2 kall_tac (CONJUNCTS_THEN2 (mk_asm "root_in")
      (CONJUNCTS_THEN2 (mk_asm "reach") (mk_asm "rows"))))) >>
  `LENGTH ps.ps_stack + (LENGTH cut.as_stack - LENGTH ps.ps_stack) =
    LENGTH cut.as_stack` by decide_tac >>
  `{x | x IN V /\ ?n (path:num->num#num).
      path 0=e /\ path n=x /\ !k. k<n ==> edge (path k) (path(SUC k))} = V` by
    (asm "reach" (fn th =>
      POP_ASSUM_LIST (K ALL_TAC) >> simp[EXTENSION] >> metis_tac[th])) >>
  pop_assum (mk_asm "live_set") >>
  `!x y. (x IN V /\ edge x y) = edge x y` by
    (rpt gen_tac >> eq_tac >> simp[] >> strip_tac >>
     asm "rows" (qspecl_then [`x`,`y`] (drule_then (mp_tac o CONJUNCT1)) o
       CONJUNCT1 o CONJUNCT2) >> simp[]) >>
  pop_assum (mk_asm "live_edge") >>
  qabbrev_tac `pch = \x:num#num. FST (iface x)` >>
  qabbrev_tac `ht = \x:num#num. FST (SND (iface x))` >>
  qabbrev_tac `nd = \x:num#num. FST (SND (SND (iface x)))` >>
  qabbrev_tac `tg = \x:num#num. FST (SND (SND (SND (iface x))))` >>
  qabbrev_tac `bl = \x:num#num. SND (SND (SND (SND (iface x))))` >>
  qexistsl [`V`,`e`,`rank`,`pch`,`ht`,`nd`,`tg`,`bl`,`edge`] >>
  (* The interpreter's rank comparison is rational; it preserves the
     natural comparison after embedding. *)
  mp_tac (norm_lets (Q.SPECL [`prog`,`sym_init cut`,`cut`,`V`,`e`,`\x. rat$rat_of_num (rank x)`,
                  `pch`,`ht`,`nd`,`tg`,`bl`,`edge`]
    staticAbortOptMergeIszeroBranchPackageTheory.pending_rows_rooted_package)) >>
  lets >> PURE_REWRITE_TAC [DIFF_EMPTY,ratTheory.RAT_OF_NUM_LES] >>
  impl_tac >- (
    conj_tac >- asm "finite" ACCEPT_TAC >>
    conj_tac >- asm "root_in" ACCEPT_TAC >>
    conj_tac >- (unabbrev_all_tac >> BETA_TAC >>
      asm "rows" (ACCEPT_TAC o PURE_REWRITE_RULE [DIFF_EMPTY])) >>
    conj_tac >- (
      rpt gen_tac >> disch_tac >>
      qspecl_then [`x`,`y`] mp_tac
        (Q.SPECL [`prog`,`cut.as_call_ctx`,`V`,`rank`,`pch`,`ht`,`nd`,`tg`,`bl`,`edge`]
          static_row_edge_control) >>
      lets >> unabbrev_all_tac >> BETA_TAC >>
      (impl_tac >- (conj_tac >- asm "rows" ACCEPT_TAC >> first_assum ACCEPT_TAC)) >>
      disch_then ACCEPT_TAC) >>
    unabbrev_all_tac >> BETA_TAC >> asm "entry" (fn th => simp[th])) >>
  unabbrev_all_tac >> BETA_TAC >>
  asm "live_set" (fn set_eq => asm "live_edge" (fn edge_eq =>
    PURE_REWRITE_TAC [set_eq,edge_eq])) >>
  disch_then (CONJUNCTS_THEN2 (mk_asm "live_root")
    (CONJUNCTS_THEN2 (mk_asm "live_reach")
      (CONJUNCTS_THEN2 (mk_asm "live_rows")
        (CONJUNCTS_THEN2 (mk_asm "open")
          (CONJUNCTS_THEN2 (mk_asm "shape") kall_tac))))) >>
  conj_tac >- asm "open" ACCEPT_TAC >>
  conj_tac >- asm "live_rows" ACCEPT_TAC >>
  conj_tac >- asm "live_root" ACCEPT_TAC >>
  conj_tac >- asm "live_reach" ACCEPT_TAC >>
  conj_tac >- asm "shape" ACCEPT_TAC >>
  asm "entry" (fn th => simp[th])
QED

Finalise generated_static_cut_rows_reloc

Theorem generated_static_cut_rows:
  !Shape. Shape = ^shape_tm ==>
  !Flow. Flow = ^flow_tm ==>
  body_inv_abort rpolicy unit cpl prog ctx lo o2pc i fn r liveness dfg cfg ch
    growth spill_base lbl_ctr fn_ops ps_end bb ps_l h promised ps_dfs
    block_ops ps_dfs_after ps_after prefix_ops rest_ops k ps pc0 cvs cut Inv
    ra pc_ret rest mem0 /\
  sym_frame_inv prog env ctx cpl fn ret srest labs0 ps cut sc /\
  label_flow_ok ctx /\
  code_end_offset_ok (\ctx fn inst s. Inv ctx fn inst s /\ ~in_static_abort_prefix fn s)
    ctx /\ sym_unit_static_ok unit /\
  asm_static_wf prog /\ (!l. MEM (AsmDataHeader l) prog ==> l IN FDOM env) /\
  in_static_abort_prefix fn cvs ==>
  ?V e rank pc height need tag boolean edge.
    ^open_tm Shape Flow prog cut.as_call_ctx cut.as_requests V {} rank pc height need tag boolean edge /\
    ^rows_tm Flow prog cut.as_call_ctx V {} rank pc height need tag boolean edge /\
    e IN V /\ (!x. x IN V ==> ^reach_tm edge e x) /\
    Shape prog cut.as_call_ctx cut.as_requests pc height need tag boolean e cut /\
    (!j. tag e j=NONE /\ ~boolean e j)
Proof
  lets >> strip_tac >> fs[body_inv_abort_reloc_canonical] >>
  `!f inst l.
    MEM f ctx.ctx_functions /\ MEM inst (fn_insts f) /\
    inst.inst_opcode <> PHI /\ MEM (Label l) (compute_operands inst) ==>
    IS_SOME (FLOOKUP (SND (compute_label_offsets prog)) l)` by
    (qpat_assum `lo = SND (compute_label_offsets prog)` (SUBST1_TAC o SYM) >>
     qhdtm_assum `body_inv_abort_reloc`
       (ACCEPT_TAC o cj 14 o REWRITE_RULE [body_inv_abort_reloc_def])) >>
  drule_all (norm_lets generated_static_cut_rows_reloc) >> simp[]
QED
