(* The actual typed-array CFG scaffold; element execution is separate. *)
Theory typedCopyArrayPtr
Ancestors typedCopyTuplePtr context compileEnv emitHelper

Theorem compile_copy_sarray_typed_slow:
  !cenv dst dty src sty count sa sz.
    ~(type_memory_bytes cenv dty = type_memory_bytes cenv sty /\
      ~is_abi_dynamic cenv.ce_struct_fields dty) ==>
    (compile_copy_sarray_typed cenv dst dty src sty count sa = ((),sz) <=>
     (do cond_lbl <- fresh_label "typed_sa_cond";
         body_lbl <- fresh_label "typed_sa_body";
         exit_lbl <- fresh_label "typed_sa_exit";
         counter <- fresh_var;
         emit_inst ASSIGN [Lit 0w] [counter];
         emit_inst JMP [Label cond_lbl] [];
         new_block cond_lbl;
         lt_op <- emit_op LT [Var counter; Lit (n2w count)];
         done_op <- emit_op ISZERO [lt_op];
         emit_inst JNZ [done_op; Label exit_lbl; Label body_lbl] [];
         new_block body_lbl;
         src_off <- emit_op MUL [Var counter; Lit (n2w (type_memory_bytes cenv sty))];
         dst_off <- emit_op MUL [Var counter; Lit (n2w (type_memory_bytes cenv dty))];
         src_elem <- emit_op ADD [src; src_off];
         dst_elem <- emit_op ADD [dst; dst_off];
         compile_store_memory_typed cenv dst_elem dty src_elem sty;
         new_ctr <- emit_op ADD [Var counter; Lit 1w];
         emit_inst ASSIGN [new_ctr] [counter];
         emit_inst JMP [Label cond_lbl] [];
         _ <- new_block exit_lbl;
         return ()
      od) sa = ((),sz))
Proof
  rpt gen_tac >> strip_tac >>
  simp[Once contextTheory.compile_store_memory_typed_def]
QED

Theorem entry_ghost_no_phi:
  !fn s bb G tn.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    phi_prefix_length bb.bb_instructions = 0 ==>
    entry_prov fn s G = G /\ entry_taint_vars fn s tn = tn
Proof
  rpt strip_tac >> Cases_on `bb.bb_instructions` >>
  gvs[venomExecSemanticsTheory.phi_prefix_length_def,
      ptrDisciplineTheory.entry_prov_def,
      ptrDisciplineTheory.entry_taint_vars_def,
      ptrDisciplineTheory.phis_prov_def, ptrDisciplineTheory.phis_taint_def] >>
  Cases_on `h.inst_opcode = PHI` >>
  gvs[venomExecSemanticsTheory.phi_prefix_length_def,
      ptrDisciplineTheory.phis_prov_def, ptrDisciplineTheory.phis_taint_def]
QED

Theorem ghost_run_jump_no_phi:
  !fuel ctx fn PG G tn s bb inst lbl target.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME inst /\
    is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
    step_inst_base inst s = OK (jump_to lbl s) /\ ~s.vs_halted /\
    lookup_block lbl fn.fn_blocks = SOME target /\
    phi_prefix_length target.bb_instructions = 0 ==>
    ghost_run (SUC fuel) ctx fn PG G tn s =
    ghost_run fuel ctx fn PG G tn (jump_to lbl s)
Proof
  rpt strip_tac >>
  `step_inst (SUC fuel) ctx inst s = OK (jump_to lbl s)` by
    simp[venomExecSemanticsTheory.step_inst_non_invoke] >>
  `~(jump_to lbl s).vs_halted` by simp[venomStateTheory.jump_to_def] >>
  `entry_prov fn (jump_to lbl s) G = G /\
   entry_taint_vars fn (jump_to lbl s) tn = tn` by
    (irule entry_ghost_no_phi >>
     simp[venomStateTheory.jump_to_def] >> metis_tac[]) >>
  simp[ptrSafeRunTheory.ghost_run_def] >>
  drule_all ptrSafeRunTheory.ghost_block_terminator >>
  disch_then (qspecl_then [`fn`, `PG`, `G`, `tn`] SUBST1_TAC) >>
  `eval_phis (jump_to lbl s) target.bb_instructions = OK (jump_to lbl s)` by
    (Cases_on `target.bb_instructions`
     >- simp[venomExecSemanticsTheory.eval_phis_def] >>
     Cases_on `h.inst_opcode = PHI` >>
     gvs[venomExecSemanticsTheory.eval_phis_def,
         venomExecSemanticsTheory.phi_prefix_length_def]) >>
  gvs[venomStateTheory.jump_to_def] >>
  simp[Once ptrSafeRunTheory.ghost_blocks_def]
QED

Theorem ptr_safe_run_jump_no_phi:
  !fuel D lo ctx fn PG G tn s bb inst lbl target.
    lookup_block s.vs_current_bb fn.fn_blocks = SOME bb /\
    get_instruction bb s.vs_inst_idx = SOME inst /\
    is_terminator inst.inst_opcode /\ inst.inst_opcode <> INVOKE /\
    step_inst_base inst s = OK (jump_to lbl s) /\ ~s.vs_halted /\
    lookup_block lbl fn.fn_blocks = SOME target /\
    phi_prefix_length target.bb_instructions = 0 ==>
    (ptr_safe_run D lo (SUC fuel) ctx fn PG G tn s <=>
     ptr_safe_step D lo (SUC fuel) ctx fn PG G tn inst s /\
     ptr_safe_run D lo fuel ctx fn PG G tn (jump_to lbl s))
Proof
  rpt strip_tac >>
  `step_inst (SUC fuel) ctx inst s = OK (jump_to lbl s)` by
    simp[venomExecSemanticsTheory.step_inst_non_invoke] >>
  `entry_prov fn (jump_to lbl s) G = G /\
   entry_taint_vars fn (jump_to lbl s) tn = tn` by
    (irule entry_ghost_no_phi >>
     simp[venomStateTheory.jump_to_def] >> metis_tac[]) >>
  `eval_phis (jump_to lbl s) target.bb_instructions = OK (jump_to lbl s)` by
    (Cases_on `target.bb_instructions`
     >- simp[venomExecSemanticsTheory.eval_phis_def] >>
     Cases_on `h.inst_opcode = PHI` >>
     gvs[venomExecSemanticsTheory.eval_phis_def,
         venomExecSemanticsTheory.phi_prefix_length_def]) >>
  simp[ptrSafeRunTheory.ptr_safe_run_def,
       Once ptrSafeRunTheory.ptr_safe_block_def] >>
  gvs[venomStateTheory.jump_to_def] >>
  simp[Once ptrSafeRunTheory.ptr_safe_blocks_def]
QED

Theorem finite_ptr_continuation_chain:
  !count H R D lo ctx fn PG.
    (!i G tn s. i < count /\ H i G tn s ==>
      ((?G' tn' s'. H (SUC i) G' tn' s' /\
        (!fuel r. run_from fuel ctx fn s' = r /\ (!e. r <> Error e) ==>
          ?fuel'. run_from fuel' ctx fn s = r /\
            ghost_run fuel' ctx fn PG G tn s =
              ghost_run fuel ctx fn PG G' tn' s' /\
            (ptr_safe_run D lo fuel ctx fn PG G' tn' s' ==>
             ptr_safe_run D lo fuel' ctx fn PG G tn s))) \/
       (?fuel r. run_from fuel ctx fn s = r /\ exit_result r /\
         (!e. r <> Error e) /\ R (ghost_run fuel ctx fn PG G tn s) r /\
         ptr_safe_run D lo fuel ctx fn PG G tn s))) ==>
    !i G tn s. i <= count /\ H i G tn s ==>
      ((?G' tn' s'. H count G' tn' s' /\
        (!fuel r. run_from fuel ctx fn s' = r /\ (!e. r <> Error e) ==>
          ?fuel'. run_from fuel' ctx fn s = r /\
            ghost_run fuel' ctx fn PG G tn s =
              ghost_run fuel ctx fn PG G' tn' s' /\
            (ptr_safe_run D lo fuel ctx fn PG G' tn' s' ==>
             ptr_safe_run D lo fuel' ctx fn PG G tn s))) \/
       (?fuel r. run_from fuel ctx fn s = r /\ exit_result r /\
         (!e. r <> Error e) /\ R (ghost_run fuel ctx fn PG G tn s) r /\
         ptr_safe_run D lo fuel ctx fn PG G tn s))
Proof
  rpt gen_tac >> disch_tac >> gen_tac >>
  rename1 `i <= n` >>
  completeInduct_on `n-i` >> rpt strip_tac >>
  Cases_on `i = n`
  >- (gvs[] >> disj1_tac >> qexistsl_tac [`G`, `tn`, `s`] >>
      asm_rewrite_tac[] >> rpt strip_tac >> qexists_tac `fuel` >>
      asm_rewrite_tac[]) >>
  `i < n` by decide_tac >>
  qpat_x_assum `!m. m < v ==> _` (qspec_then `n - SUC i` mp_tac) >>
  (impl_tac >- decide_tac) >>
  disch_then (qspecl_then [`n`, `SUC i`] mp_tac) >>
  rewrite_tac[] >> (impl_tac >- first_assum ACCEPT_TAC) >> disch_tac >>
  `SUC i <= n` by decide_tac >>
  qpat_x_assum `!i G tn s. i < n /\ H i G tn s ==> _` drule_all >>
  strip_tac
  >- (rename1 `H (SUC i) g1 t1 s1` >>
      qpat_x_assum `!G tn s. _ ==> _` drule_all >>
      strip_tac
      >- (disj1_tac >> qexistsl_tac [`G'`, `tn'`, `s'`] >>
          asm_rewrite_tac[] >> rpt strip_tac >>
          qpat_x_assum `!fuel r. run_from fuel ctx fn s' = r /\ _ ==> _`
            drule_all >> strip_tac >>
          qpat_x_assum `!fuel r. run_from fuel ctx fn s1 = r /\ _ ==> _`
            drule_all >> strip_tac >>
          goal_assum (drule_at Any) >> metis_tac[]) >>
      disj2_tac >>
      qpat_x_assum `!fuel r. run_from fuel ctx fn s1 = r /\ _ ==> _`
        drule_all >> strip_tac >>
      goal_assum (drule_at Any) >> metis_tac[]) >>
  disj2_tac >> metis_tac[]
QED
