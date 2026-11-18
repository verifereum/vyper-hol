(* Seed the mixed certificate using the stopped execution at the real entry. *)
Theory staticAbortMixedSeed
Ancestors
  codegenStaticAbortCutSim staticAbortGeneratedStaticRows staticAbortGeneratedRevertRows
  codegenAsmOpt[qualified] codegenAsmStaticWf codegenEntrySim codegenSymRel
  contextStaticAbortRel asmDataEnv asmSymBridge asmSymSem asmOptimizer
  asmIR asmSem asmToBytecodeProofs staticAbortStraight
  pred_set finite_map alist words list arithmetic

val _ = Parse.hide "cp";

val lets_conv = REDEPTH_CONV (FIRST_CONV [REWR_CONV LET_THM, BETA_CONV]);
fun closed_rows th = PURE_REWRITE_RULE [DIFF_EMPTY] (CONV_RULE lets_conv th);

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
  let data = vs.vs_data_section; req_bound = vs'.vs_requests in
  let Shape = \p cc req pc height need tag boolean i (t:asm_state).
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
       (EL k t.as_stack = 0w \/ EL k t.as_stack = 1w))
  in
  let target = \p pc tag (x:num#num) (y:num#num).
    ?l origin off. tag x 0 = SOME(l,origin) /\
      FLOOKUP (SND(compute_label_offsets p)) l = SOME off /\
      off < dimword(:256) /\ FLOOKUP (build_offset_to_pc p) off = SOME(pc y)
  in
  let Flow = \p pc height tag boolean (x:num#num) (y:num#num).
    let hi = height x; hj = height y; ins = EL (pc x) p in
    let inherit =
      \(src:num -> num option)
        (fresh:num -> (string#num)option) (bnew:num -> bool).
        (!k l origin. tag y k = SOME(l,origin) ==>
           k < hj /\ (fresh k = SOME(l,origin) \/
             ?a. src k = SOME a /\ a < hi /\ tag x a = SOME(l,origin))) /\
        (!k. boolean y k ==> k < hj /\
           (bnew k \/ ?a. src k = SOME a /\ a < hi /\ boolean x a))
    in
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
               let a = asm_op_arity name; m = hj + asm_op_arity name - hi in
               a <= hi /\ hj = m+(hi-a) /\
               ((name="JUMP" \/ name="JUMPI") ==> m=0) /\
               inherit (\k. if k<m then NONE else SOME(k-m+a)) (\k. NONE)
                 (\k. k=0 /\ m=1 /\ asm_returns_zero_or_one ins /\
                   !t u. LENGTH t.as_stack=hi /\
                     asm_step (SND(compute_label_offsets p)) (build_offset_to_pc p)
                       ins t=AsmOK u ==>
                     (EL 0 u.as_stack=0w \/ EL 0 u.as_stack=1w)))
    | _ => F
  in
  let Rows = \p cc V rank pc height need tag boolean edge.
    let lo = SND (compute_label_offsets p) in
    let otp = build_offset_to_pc p in
    (!x. x IN V ==>
      (need x ==> cc.cc_static) /\
      (!k. boolean x k ==> k < height x /\ tag x k=NONE) /\
      (!k l origin. tag x k = SOME(l,origin) ==>
         k < height x /\ origin < LENGTH p /\
         (EL origin p = AsmPushLabel l \/ EL origin p = AsmPushOfst l 0) /\
         ?off dest. FLOOKUP lo l = SOME off /\ off < dimword(:256) /\
                    FLOOKUP otp off = SOME dest)) /\
    (!x y. edge x y ==> x IN V /\ y IN V /\ rank y < rank x /\ Flow p pc height tag boolean x y) /\
    (!x. x IN V ==>
      pc x < LENGTH p /\
      let h = height x in
      let fall = \y. pc y = pc x+1 in
      let arm = \P n. ?y. edge x y /\ P y /\ height y = n in
      let legal = \P n. !y. edge x y ==> P y /\ height y = n in
      let next = \n. arm fall n /\ legal fall n in
      let untagged = \a. !k. k<a ==> tag x k=NONE in
      let stop = \a. a<=h /\ untagged a /\ !y. ~edge x y in
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
                      1<=h /\ arm (target p pc tag x) (h-1) /\ legal (target p pc tag x) (h-1)
                   else if name="JUMPI" then
                      2<=h /\ tag x 1=NONE /\ arm fall (h-2) /\ arm (target p pc tag x) (h-2) /\
                      legal (\y. fall y \/ target p pc tag x y) (h-2)
                   else
                      ?m. static_abort_straight name m /\ asm_op_arity name <= h /\
                          untagged (asm_op_arity name) /\ next (h-asm_op_arity name+m))
      | _ => F)
  in
  let Open = \p cc req (V:(num#num)->bool) X rank pc height need
    (tag:(num#num)->num->(string#num)option)
    (boolean:(num#num)->num->bool) edge.
    let S = Shape p cc req pc height need tag boolean in
    FINITE V /\ X SUBSET V /\
    (!x. x IN V ==> ?t. S x t) /\
    (!x. x IN V DIFF X ==> pc x < LENGTH p) /\
    (!x y. edge x y ==>
       x IN V DIFF X /\ y IN V /\ rank y < rank x /\
       Flow p pc height tag boolean x y /\
       (if EL (pc x) p = AsmOp "JUMP" then target p pc tag x y
        else if EL (pc x) p = AsmOp "JUMPI" then pc y = pc x+1 \/ target p pc tag x y
        else pc y = pc x+1)) /\
    (!x t. x IN V DIFF X /\ S x t ==>
       (?u. (asm_steps (SND(compute_label_offsets p)) (build_offset_to_pc p)
                    p 1 t = AsmRevert u \/
              asm_steps (SND(compute_label_offsets p)) (build_offset_to_pc p)
                    p 1 t = AsmFault u) /\ u.as_requests=req) \/
       (?y u. edge x y /\
          asm_steps (SND(compute_label_offsets p)) (build_offset_to_pc p)
            p 1 t = AsmOK u /\ S y u))
  in
  let Reach = \(edge:(num#num)->(num#num)->bool) e x.
    ?n (path:num->num#num).
      path 0=e /\ path n=x /\ !k. k<n ==> edge (path k) (path(SUC k))
  in
  let bytes = \p. assemble p ++ data in
  let env0 = asm_data_env prog (bytes prog) in
  let M_R = \p.
    let envp = asm_data_env p (bytes p) in
    let start = s with as_code := bytes p in
    let run = asm_steps (SND (compute_label_offsets p)) (build_offset_to_pc p) p in
    s.as_pc = 0 /\ s.as_code = bytes prog /\
    asm_static_wf prog /\ asm_static_wf p /\
    FILTER is_data_inst p = FILTER is_data_inst prog /\
    ((?n out.
        (run n start = AsmRevert out \/ run n start = AsmFault out) /\
        sym_terminal (sym_steps p env0 n (sym_init s)) /\
        out.as_requests <<= req_bound) \/
     (?j t u cc req (V:(num#num)->bool) e (rank:(num#num)->num)
         pc height need tag boolean edge.
        run j start = AsmOK t /\
        sym_steps p env0 j (sym_init s) = SymOK u /\
        asm_sym_rel p envp t u /\
        t.as_pc = u.sym_base.as_pc /\ LENGTH t.as_stack = LENGTH u.sym_stack /\
        t.as_call_ctx = u.sym_base.as_call_ctx /\ t.as_requests = u.sym_base.as_requests /\
        t.as_call_ctx = cc /\ t.as_requests = req /\ req <<= req_bound /\
        Rows p cc V rank pc height need tag boolean edge /\
        Open p cc req V {} rank pc height need tag boolean edge /\
        e IN V /\ (!x. x IN V ==> Reach edge e x) /\
        Shape p cc req pc height need tag boolean e t /\
        (!k l origin. tag e k = SOME(l,origin) ==>
           k < LENGTH u.sym_stack /\ EL k u.sym_stack = Lab l 0) /\
        (!k. boolean e k ==>
           k < LENGTH u.sym_stack /\ (EL k u.sym_stack = Val 0w \/ EL k u.sym_stack = Val 1w))))
  in M_R prog
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
  CONV_TAC lets_conv >>
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
