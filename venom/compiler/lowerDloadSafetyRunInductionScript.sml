(* Relation-parametric successful semantic recursion interface. *)
Theory lowerDloadSafetyRunInduction
Ancestors
  venomExecSemantics venomExecProofs venomState venomInst list

Theorem ld_invoke_success:
  inst.inst_opcode = INVOKE /\ step_inst fuel ctx inst s = OK t ==>
  ?nm ops callee args cs ret cs'.
    decode_invoke inst = SOME (nm,ops) /\
    lookup_function nm ctx.ctx_functions = SOME callee /\
    eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
    run_blocks fuel ctx callee cs = IntRet ret cs' /\
    bind_outputs inst.inst_outputs ret.iret_values
      (adopt_return_fmp ret (merge_callee_state s cs')) = SOME t
Proof
  strip_tac >> qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
  once_rewrite_tac[step_inst_def] >> simp[AllCaseEqs()] >> metis_tac[]
QED

Theorem ld_successful_run_induction:
  !S E R.
  (!fuel ctx inst s z.
    inst.inst_opcode <> INVOKE /\ step_inst_base inst s = z /\
    ((?t. z = OK t) \/ (?ret t. z = IntRet ret t)) ==>
    S fuel ctx inst s z) /\
  (!fuel ctx inst s nm ops callee args cs ret cs' t.
    inst.inst_opcode = INVOKE /\ decode_invoke inst = SOME (nm,ops) /\
    lookup_function nm ctx.ctx_functions = SOME callee /\
    eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
    run_blocks fuel ctx callee cs = IntRet ret cs' /\
    R fuel ctx callee cs (IntRet ret cs') /\
    bind_outputs inst.inst_outputs ret.iret_values
      (adopt_return_fmp ret (merge_callee_state s cs')) = SOME t ==>
    S fuel ctx inst s (OK t)) /\
  (!fuel ctx bb s inst u z.
    get_instruction bb s.vs_inst_idx = SOME inst /\
    step_inst fuel ctx inst s = OK u /\ S fuel ctx inst s (OK u) /\
    ~is_terminator inst.inst_opcode /\
    run_block_non_phis fuel ctx bb (u with vs_inst_idx := SUC s.vs_inst_idx) = z /\
    E fuel ctx bb (u with vs_inst_idx := SUC s.vs_inst_idx) z /\
    ((?t. z = OK t) \/ (?ret t. z = IntRet ret t)) ==>
    E fuel ctx bb s z) /\
  (!fuel ctx bb s inst u.
    get_instruction bb s.vs_inst_idx = SOME inst /\
    step_inst fuel ctx inst s = OK u /\ S fuel ctx inst s (OK u) /\
    is_terminator inst.inst_opcode /\ ~u.vs_halted ==>
    E fuel ctx bb s (OK u)) /\
  (!fuel ctx bb s inst ret u.
    get_instruction bb s.vs_inst_idx = SOME inst /\
    step_inst fuel ctx inst s = IntRet ret u /\
    S fuel ctx inst s (IntRet ret u) ==> E fuel ctx bb s (IntRet ret u)) /\
  (!fuel ctx fn s bb sp u z.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    eval_phis s bb.bb_instructions = OK sp /\
    run_block_non_phis fuel ctx bb (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions) = OK u /\
    E fuel ctx bb (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions) (OK u) /\
    ~u.vs_halted /\ run_blocks fuel ctx fn u = z /\ R fuel ctx fn u z /\
    ((?t. z = OK t) \/ (?ret t. z = IntRet ret t)) ==>
    R (SUC fuel) ctx fn s z) /\
  (!fuel ctx fn s bb sp ret u.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    eval_phis s bb.bb_instructions = OK sp /\
    run_block_non_phis fuel ctx bb (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions) = IntRet ret u /\
    E fuel ctx bb (sp with vs_inst_idx := phi_prefix_length bb.bb_instructions) (IntRet ret u) ==>
    R (SUC fuel) ctx fn s (IntRet ret u)) ==>
  (!fuel ctx inst s z. step_inst fuel ctx inst s = z /\
    ((?t. z = OK t) \/ (?ret t. z = IntRet ret t)) ==> S fuel ctx inst s z) /\
  (!fuel ctx bb s z. run_block_non_phis fuel ctx bb s = z /\
    ((?t. z = OK t) \/ (?ret t. z = IntRet ret t)) ==> E fuel ctx bb s z) /\
  (!fuel ctx fn s z. run_blocks fuel ctx fn s = z /\
    ((?t. z = OK t) \/ (?ret t. z = IntRet ret t)) ==> R fuel ctx fn s z)
Proof
  rpt gen_tac >>
  disch_then (CONJUNCTS_THEN2 (mk_asm "base")
    (CONJUNCTS_THEN2 (mk_asm "call")
      (CONJUNCTS_THEN2 (mk_asm "next")
        (CONJUNCTS_THEN2 (mk_asm "term")
          (CONJUNCTS_THEN2 (mk_asm "ret")
            (CONJUNCTS_THEN2 (mk_asm "jump") (mk_asm "return"))))))) >>
  ho_match_mp_tac run_defs_ind >> rpt conj_tac
  >- suspend "step"
  >- suspend "block"
  >> suspend "run"
QED

Resume ld_successful_run_induction[step]:
  rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
  (Cases_on `inst.inst_opcode = INVOKE`
   >- (qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
       once_rewrite_tac[step_inst_def] >> simp[AllCaseEqs()] >>
       strip_tac >> asm_x "call" irule >> metis_tac[]) >>
   asm_x "base" irule >> simp[] >>
   qpat_x_assum `step_inst _ _ _ _ = _` mp_tac >>
   simp[step_inst_non_invoke])
QED

Resume ld_successful_run_induction[block]:
  asm_x "base" kall_tac >> asm_x "call" kall_tac >>
  asm_x "jump" kall_tac >> asm_x "return" kall_tac >>
  rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
  qpat_x_assum `run_block_non_phis _ _ _ _ = _` mp_tac >>
  once_rewrite_tac[run_block_non_phis_def] >>
  simp[AllCaseEqs()] >> strip_tac >> gvs[]
  >- (asm_x "term" irule >> metis_tac[])
  >- (asm_x "next" irule >> metis_tac[])
  >- (asm_x "next" irule >> metis_tac[]) >>
  asm_x "ret" irule >> metis_tac[]
QED

Resume ld_successful_run_induction[run]:
  asm_x "base" kall_tac >> asm_x "call" kall_tac >>
  asm_x "next" kall_tac >> asm_x "term" kall_tac >> asm_x "ret" kall_tac >>
  rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
  (Cases_on `fuel`
   >- (qpat_x_assum `run_blocks _ _ _ _ = _` mp_tac >>
       simp[Once run_blocks_def]) >>
   qpat_x_assum `run_blocks _ _ _ _ = _` mp_tac >>
   once_rewrite_tac[run_blocks_def] >>
   simp[AllCaseEqs()] >> strip_tac >>
   qspecl_then [`s`, `bb.bb_instructions`] strip_assume_tac
     eval_phis_ok_or_error_defs >> gvs[])
  >- (asm_x "jump" irule >> metis_tac[])
  >- (asm_x "jump" irule >> metis_tac[]) >>
  asm_x "return" irule >> metis_tac[]
QED

Finalise ld_successful_run_induction

val _ = if null (hyp ld_successful_run_induction) then ()
        else raise Fail "successful run induction has hypotheses";
