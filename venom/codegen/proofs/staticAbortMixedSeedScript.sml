(* Seed the mixed certificate using the stopped execution at the real entry. *)
Theory staticAbortMixedSeed
Ancestors
  codegenStaticAbortCutSim staticAbortGeneratedStaticRows staticAbortGeneratedRevertRows
  codegenAsmOpt[qualified] codegenAsmStaticWf codegenEntrySim codegenSymRel
  contextStaticAbortRel asmDataEnv asmSymBridge asmSymSem asmOptimizer
  asmIR asmSem asmToBytecodeProofs staticAbortStraight
  pred_set finite_map alist words list arithmetic

val _ = Parse.hide "cp";

(* Compare the row producers at their defining values. *)
val seed_names_conv = REDEPTH_CONV
  (HO_REWR_CONV UNWIND_FORALL_THM2 ORELSEC BETA_CONV);
fun closed_rows th = PURE_REWRITE_RULE [DIFF_EMPTY] (CONV_RULE seed_names_conv th);

Theorem codegen_entry_abort_mixed_seed:
  !fuel rpolicy unit cp prog Inv vs s a vs'.
    generate_context_plan unit.cu_context = SOME cp /\
    codegen_assembly rpolicy unit = SOME prog /\
    unit_shape_ok unit /\
    codegen_context_obligations_abort Inv unit.cu_context cp /\
    codegen_reachability_package Inv unit.cu_context vs /\
    (!fn inst l.
      MEM fn unit.cu_context.ctx_functions /\ MEM inst (fn_insts fn) /\
      inst.inst_opcode <> PHI /\ MEM (Label l) (compute_operands inst) ==>
      IS_SOME (FLOOKUP (SND (compute_label_offsets prog)) l)) /\
    label_flow_ok unit.cu_context /\
    code_end_offset_ok
      (\ctx fn inst s. Inv ctx fn inst s /\ ~in_static_abort_prefix fn s)
      unit.cu_context /\ sym_unit_static_ok unit /\
    vs.vs_code = assemble prog ++ vs.vs_data_section /\
    s.as_code = assemble prog ++ vs.vs_data_section /\
    codegen_asm_entry_rel cp prog vs s /\
    run_context fuel unit.cu_context vs = Abort a vs' ==>
  !req_bound. req_bound = vs'.vs_requests ==>
  !bytes. bytes = assemble prog ++ vs.vs_data_section ==>
  !env0. env0 = asm_data_env prog bytes ==>
  !start. start = (s with as_code := bytes) ==>
  !lo'. lo' = SND (compute_label_offsets prog) ==>
  !otp. otp = build_offset_to_pc prog ==>
  !run. run = asm_steps lo' otp prog ==>
  !Shape. Shape = (\cc req pc height need tag boolean i (t:asm_state).
    t.as_pc = pc i /\ LENGTH t.as_stack = height i /\
    t.as_call_ctx = cc /\ t.as_requests = req /\
    (need i ==> t.as_call_ctx.cc_static) /\
    (!k l origin. tag i k = SOME(l,origin) ==>
       k < height i /\ origin < LENGTH prog /\
       (EL origin prog = AsmPushLabel l \/
        (?d. EL origin prog = AsmPushOfst l d) \/ EL origin prog = AsmDataLabel l) /\
       ?off dest.
         FLOOKUP lo' l = SOME off /\ off < dimword(:256) /\
         FLOOKUP otp off = SOME dest /\ EL k t.as_stack = (n2w off:bytes32)) /\
    (!k. boolean i k ==> k < height i /\
       (EL k t.as_stack = 0w \/ EL k t.as_stack = 1w))) ==>
  !target. target = (\pc tag (x:num#num) (y:num#num).
    ?l origin off. tag x 0 = SOME(l,origin) /\
      FLOOKUP lo' l = SOME off /\ off < dimword(:256) /\
      FLOOKUP otp off = SOME(pc y)) ==>
  !Flow. Flow = (\pc height tag boolean (x:num#num) (y:num#num).
    !hi. hi = height x ==>
    !hj. hj = height y ==>
    !ins. ins = EL (pc x) prog ==>
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
    | AsmPush bs => hj = hi+1 /\
        inherit (\k. if k=0 then NONE else SOME(k-1)) (\k. NONE)
          (\k. k=0 /\ !t u.
            asm_step lo' otp (AsmPush bs) t = AsmOK u ==>
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
                     asm_step lo' otp ins t = AsmOK u ==>
                     (EL 0 u.as_stack=0w \/ EL 0 u.as_stack=1w)))
    | _ => F) ==>
  s.as_pc = 0 /\ s.as_code = bytes /\
  asm_static_wf prog /\ asm_static_wf prog /\
  FILTER is_data_inst prog = FILTER is_data_inst prog /\
  ((?n out.
      (run n start = AsmRevert out \/ run n start = AsmFault out) /\
      sym_terminal (sym_steps prog env0 n (sym_init s)) /\
      out.as_requests <<= req_bound) \/
   (?j t u cc req (V:(num#num)->bool) e (rank:(num#num)->num)
       pc height need tag boolean edge.
      run j start = AsmOK t /\
      sym_steps prog env0 j (sym_init s) = SymOK u /\
      asm_sym_rel prog env0 t u /\
      t.as_pc = u.sym_base.as_pc /\ LENGTH t.as_stack = LENGTH u.sym_stack /\
      t.as_call_ctx = u.sym_base.as_call_ctx /\ t.as_requests = u.sym_base.as_requests /\
      t.as_call_ctx = cc /\ t.as_requests = req /\ req <<= req_bound /\
      ((!x. x IN V ==>
          (need x ==> cc.cc_static) /\
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
                    then cc.cc_static /\ stop (asm_op_arity name)
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
           | _ => F))) /\
      (!S. S = Shape cc req pc height need tag boolean ==>
        FINITE V /\ {} SUBSET V /\
        (!x. x IN V ==> ?t. S x t) /\
        (!x. x IN V ==> pc x < LENGTH prog) /\
        (!x y. edge x y ==>
           x IN V /\ y IN V /\ rank y < rank x /\ Flow pc height tag boolean x y /\
           (if EL (pc x) prog = AsmOp "JUMP" then target pc tag x y
            else if EL (pc x) prog = AsmOp "JUMPI" then pc y = pc x+1 \/ target pc tag x y
            else pc y = pc x+1)) /\
        (!x t. x IN V /\ S x t ==>
           (?u. (run 1 t = AsmRevert u \/ run 1 t = AsmFault u) /\ u.as_requests=req) \/
           (?y u. edge x y /\ run 1 t = AsmOK u /\ S y u))) /\
      e IN V /\
      (!x. x IN V ==> ?n (path:num->num#num).
         path 0=e /\ path n=x /\ !k. k<n ==> edge (path k) (path(SUC k))) /\
      Shape cc req pc height need tag boolean e t /\
      (!k l origin. tag e k = SOME(l,origin) ==>
         k < LENGTH u.sym_stack /\ EL k u.sym_stack = Lab l 0) /\
      (!k. boolean e k ==>
         k < LENGTH u.sym_stack /\ (EL k u.sym_stack = Val 0w \/ EL k u.sym_stack = Val 1w))))
Proof
  rpt gen_tac >> strip_tac >>
  `s.as_pc = 0` by fs[codegen_asm_entry_rel_def] >>
  `codegen_ready unit.cu_context` by fs[codegen_context_obligations_abort_def] >>
  `asm_static_wf prog` by (irule codegen_asm_static_wf >> metis_tac[]) >>
  `s with as_code := assemble prog ++ vs.vs_data_section = s` by
    simp[asm_state_component_equality] >>
  qabbrev_tac `env0 = asm_data_env prog (assemble prog ++ vs.vs_data_section)` >>
  `!l. MEM (AsmDataHeader l) prog ==> l IN FDOM env0` by
    simp[Abbr `env0`, codegenAsmOptTheory.asm_data_env_header_fdom] >>
  `asm_data_env_ok prog env0 vs.vs_code` by
    simp[Abbr `env0`, asm_data_env_ok_asm_data_env] >>
  CONV_TAC seed_names_conv >>
  qpat_assum `Abbrev (env0 = _)` (fn th =>
    PURE_REWRITE_TAC [DIFF_EMPTY, GSYM (REWRITE_RULE [markerTheory.Abbrev_def] th)]) >>
  qpat_assum `s with as_code := _ = s` (fn th => PURE_REWRITE_TAC [th]) >>
  rpt (conj_tac >- (first_assum ACCEPT_TAC ORELSE REFL_TAC)) >>
  drule_all codegen_entry_abort_stopped >>
  disch_then (DISJ_CASES_THEN (REPEAT_TCL CHOOSE_THEN
    (REPEAT_TCL CONJUNCTS_THEN assume_tac)))
  >- (disj1_tac >> qexistsl [`n`,`out`] >> rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disj2_tac >>
  `asm_sym_rel prog env0 cut sc` by fs[sym_frame_inv_def] >>
  `cut.as_pc = sc.sym_base.as_pc /\ LENGTH cut.as_stack = LENGTH sc.sym_stack /\
   cut.as_call_ctx = sc.sym_base.as_call_ctx /\ cut.as_requests = sc.sym_base.as_requests` by
    (qpat_assum `asm_sym_rel _ _ _ _` (strip_assume_tac o REWRITE_RULE [asm_sym_rel_def]) >>
     drule LIST_REL_LENGTH >> simp[]) >>
  `cut.as_requests <<= vs'.vs_requests` by
    (qpat_assum `cut.as_requests = vs'.vs_requests` (fn th => simp[NoAsms, th])) >>
  qexistsl [`nc`,`cut`,`sc`,`cut.as_call_ctx`,`cut.as_requests`] >>
  qpat_x_assum `in_static_abort_prefix _ _ \/ in_revert_forward _ _` DISJ_CASES_TAC >>
  (drule_all (closed_rows generated_static_cut_rows) ORELSE
   drule_all (closed_rows generated_revert_cut_rows)) >>
  disch_then (REPEAT_TCL CHOOSE_THEN (REPEAT_TCL CONJUNCTS_THEN assume_tac)) >>
  qexistsl [`V`,`e`,`rank`,`pc`,`height`,`need`,`tag`,`boolean`,`edge`] >>
  rpt conj_tac >>
  (first_assum ACCEPT_TAC ORELSE
   qpat_assum `!k. tag e k = NONE /\ ~boolean e k` (fn th => simp[NoAsms, th]))
QED
