Theory asmFinalizerPrefixInefficient
Ancestors
  arithmetic asmOptInefficientJumps asmSplice asmSymPc finalizerContract
  asmSymSem asmOptimizer asmWf

(* ML quotations below abbreviate propositions, not logical definitions. *)
val transport = ``\p q.
  ?K. 0 < K /\ !env s n a.
    s.as_pc = 0 /\ sym_steps p env n (sym_init s) = SymOK a ==>
    (?m b. sym_steps q env m (sym_init s) = SymOK b /\ n <= K * (m+1)) /\
    (a.sym_base.as_pc < LENGTH p /\ EL a.sym_base.as_pc p = AsmOp "GAS" ==>
     ?m b. sym_steps q env m (sym_init s) = SymOK b /\
       b.sym_base.as_pc < LENGTH q /\ EL b.sym_base.as_pc q = AsmOp "GAS" /\
       b.sym_base.as_gas_readings = a.sym_base.as_gas_readings)``;

val site = ``!pre pat repl post D.
  asm_splice_ok pat repl /\ asm_static_wf (pre ++ pat ++ post) /\
  (!l. MEM (AsmLabel l) pat ==> ~MEM l (asm_label_refs (pre ++ pat ++ post))) /\
  (!env u. u.sym_base.as_pc = (LENGTH pre) /\ u.sym_base.as_stack = [] /\
      sym_state_labels_in (asm_label_refs (pre ++ pat ++ post)) u ==>
    ?d. 0 < d /\ d <= D /\
      (!i a. i < d /\ sym_steps (pre ++ pat ++ post) env i u = SymOK a ==>
        ~(a.sym_base.as_pc < LENGTH (pre ++ pat ++ post) /\ EL a.sym_base.as_pc (pre ++ pat ++ post) = AsmOp "GAS")) /\
      (!a. sym_steps (pre ++ pat ++ post) env d u = SymOK a ==>
        ?e. sym_steps (pre ++ repl ++ post) env e u = SymOK (sym_with_pc ((splice_pc (LENGTH pre) (LENGTH pat) (LENGTH repl)) a.sym_base.as_pc) a) /\
          (a.sym_base.as_pc <= (LENGTH pre) \/ (LENGTH pre)+(LENGTH pat) <= a.sym_base.as_pc) /\
          (e = 0 ==> (LENGTH pre)+(LENGTH pat) <= a.sym_base.as_pc))) ==>
  ^transport (pre ++ pat ++ post) (pre ++ repl ++ post)``;

val transitive = ``!p q r. ^transport p q /\ ^transport q r ==> ^transport p r``;

Theorem inefficient_jump_window[local]:
  !pre x y rest env u.
  asm_static_wf (pre ++ [AsmPushLabel x; AsmOp "JUMPI"; AsmPushLabel y; AsmOp "JUMP"] ++ AsmLabel x
    :: rest) /\ u.sym_base.as_pc = LENGTH pre /\ u.sym_base.as_stack = [] ==>
  ?d. 0 < d /\ d <= 4 /\
    (!i a. i < d /\ sym_steps (pre ++ [AsmPushLabel x; AsmOp "JUMPI"; AsmPushLabel y; AsmOp "JUMP"]
      ++ AsmLabel x :: rest) env i u = SymOK a ==>
      ~(a.sym_base.as_pc < LENGTH (pre ++ [AsmPushLabel x; AsmOp "JUMPI"; AsmPushLabel y; AsmOp
        "JUMP"] ++ AsmLabel x :: rest) /\ EL a.sym_base.as_pc (pre ++ [AsmPushLabel x; AsmOp
        "JUMPI"; AsmPushLabel y; AsmOp "JUMP"] ++ AsmLabel x :: rest) = AsmOp "GAS")) /\
    (!a. sym_steps (pre ++ [AsmPushLabel x; AsmOp "JUMPI"; AsmPushLabel y; AsmOp "JUMP"] ++ AsmLabel
      x :: rest) env d u = SymOK a ==>
      ?e. sym_steps (pre ++ [AsmOp "ISZERO"; AsmPushLabel y; AsmOp "JUMPI"] ++ AsmLabel x :: rest)
        env e u = SymOK (sym_with_pc
        (splice_pc (LENGTH pre) 4 3 a.sym_base.as_pc) a) /\
        (a.sym_base.as_pc <= LENGTH pre \/ LENGTH pre+4 <= a.sym_base.as_pc) /\
        (e = 0 ==> LENGTH pre+4 <= a.sym_base.as_pc))
Proof
  simp_tac bool_ss [LET_THM] >> rpt gen_tac >> strip_tac >>
  `~MEM (AsmLabel x) pre`
    by (fs[asm_static_wf_def] >>
        qpat_x_assum `asm_labels_unique _`
          (mp_tac o MATCH_MP (REWRITE_RULE [GSYM AND_IMP_INTRO]
                                asm_labels_unique_append_not_mem)) >>
        disch_then (qspec_then `x` mp_tac) >> simp[]) >>
  qabbrev_tac `p = pre ++ [AsmPushLabel x; AsmOp "JUMPI"; AsmPushLabel y; AsmOp "JUMP"] ++ AsmLabel x :: rest` >>
  qabbrev_tac `q = pre ++ [AsmOp "ISZERO"; AsmPushLabel y; AsmOp "JUMPI"] ++ AsmLabel x :: rest` >>
  `LENGTH pre < LENGTH p /\ EL (LENGTH pre) p = AsmPushLabel x /\
   LENGTH pre+1 < LENGTH p /\ EL (LENGTH pre+1) p = AsmOp "JUMPI" /\
   LENGTH pre+2 < LENGTH p /\ EL (LENGTH pre+2) p = AsmPushLabel y /\
   LENGTH pre+3 < LENGTH p /\ EL (LENGTH pre+3) p = AsmOp "JUMP" /\
   INDEX_OF (AsmLabel x) p = SOME (LENGTH pre+4) /\
   LENGTH pre < LENGTH q /\ EL (LENGTH pre) q = AsmOp "ISZERO" /\
   LENGTH pre+1 < LENGTH q /\ EL (LENGTH pre+1) q = AsmPushLabel y /\
   LENGTH pre+2 < LENGTH q /\ EL (LENGTH pre+2) q = AsmOp "JUMPI"`
    by simp[Abbr `p`, Abbr `q`, listTheory.EL_APPEND_EQN,
            INDEX_OF_APPEND, INDEX_OF_CONS] >>
  Cases_on `u.sym_stack` >- (
    qexists_tac `2` >> simp[] >> conj_tac
    >- (rpt strip_tac >> `i = 0 \/ i = 1` by decide_tac >>
        gvs[sym_steps_pos, sym_steps_def, sym_step_push_label, asmSemTheory.asm_next_def]) >>
    simp[sym_steps_pos, sym_steps_def, sym_step_push_label, sym_step_def, sym_step_op_def,
         sym_jumpi_def, sym_set_stack_def, asmSemTheory.asm_next_def]) >>
  rename1 `u.sym_stack = v :: stk` >> reverse (Cases_on `v`)
  >- (qexists_tac `2` >> simp[] >> conj_tac
      >- (rpt strip_tac >> `i = 0 \/ i = 1` by decide_tac >>
          gvs[sym_steps_pos, sym_steps_def, sym_step_push_label, asmSemTheory.asm_next_def]) >>
      simp[sym_steps_pos, sym_steps_def, sym_step_def, sym_step_op_def,
           sym_jumpi_def, sym_set_stack_def, asmSemTheory.asm_next_def]) >>
  rename1 `u.sym_stack = Val c :: stk` >>
  drule_then (qspecl_then [`q`, `env`] assume_tac) sym_step_iszero_val >>
  reverse (Cases_on `c = 0w`)
  >- (qexists_tac `2` >> simp[] >> conj_tac
      >- (rpt strip_tac >> `i = 0 \/ i = 1` by decide_tac >>
          gvs[sym_steps_pos, sym_steps_def, sym_step_push_label, asmSemTheory.asm_next_def]) >>
      simp[sym_steps_pos, sym_steps_def, sym_step_push_label,
           sym_step_jumpi_label, asmSemTheory.asm_next_def] >>
      simp[sym_step_def, sym_step_op_def, sym_jumpi_def, sym_jump_dest_def] >>
      rpt strip_tac >> gvs[] >> qexists_tac `3` >>
      simp[sym_steps_pos, sym_steps_def, sym_step_push_label,
           sym_step_jumpi_label, asmSemTheory.asm_next_def, sym_with_pc_def,
           splice_pc_def, sym_state_component_equality,
           asmSemTheory.asm_state_component_equality] >>
      simp[sym_step_def, sym_step_op_def, sym_jumpi_def, sym_jump_dest_def,
           sym_set_stack_def, asmSemTheory.asm_next_def] >>
      simp[sym_state_component_equality, asmSemTheory.asm_state_component_equality]) >>
  gvs[] >>
  `INDEX_OF (AsmLabel y) q =
     OPTION_MAP (splice_pc (LENGTH pre) 4 3) (INDEX_OF (AsmLabel y) p) /\
   !i. INDEX_OF (AsmLabel y) p = SOME i ==> i <= LENGTH pre \/ LENGTH pre+4 <= i`
    by (mp_tac (Q.INST [`pat` |-> `[AsmPushLabel x; AsmOp "JUMPI"; AsmPushLabel y; AsmOp "JUMP"]`,
                        `repl` |-> `[AsmOp "ISZERO"; AsmPushLabel y; AsmOp "JUMPI"]`,
                        `pfx` |-> `pre`, `sfx` |-> `AsmLabel x :: rest`, `l` |-> `y`]
                       splice_index_of_label) >>
        simp[Abbr `p`, Abbr `q`] >> strip_tac >> simp[] >>
        rpt strip_tac >> first_x_assum drule >> strip_tac >> simp[]) >>
  qexists_tac `4` >> simp[] >> conj_tac
  >- (rpt strip_tac >> `i = 0 \/ i = 1 \/ i = 2 \/ i = 3` by decide_tac >>
      gvs[sym_steps_pos, sym_steps_def, sym_step_push_label, asmSemTheory.asm_next_def] >>
      gvs[sym_step_def, sym_step_op_def, sym_jumpi_def, sym_set_stack_def,
          sym_steps_pos, sym_steps_def, asmSemTheory.asm_next_def]) >>
  simp[sym_steps_pos, sym_steps_def, sym_step_push_label, asmSemTheory.asm_next_def] >>
  simp[sym_step_def, sym_step_op_def, sym_jumpi_def, sym_set_stack_def,
       sym_steps_pos, sym_steps_def, asmSemTheory.asm_next_def] >>
  simp[sym_jump_def, sym_jump_dest_def] >>
  Cases_on `INDEX_OF (AsmLabel y) p` >> simp[] >>
  rpt strip_tac >> gvs[] >> qexists_tac `3` >>
  simp[sym_steps_pos, sym_steps_def, sym_step_push_label, asmSemTheory.asm_next_def] >>
  simp[sym_step_def, sym_step_op_def, sym_jumpi_def, sym_jump_dest_def,
       sym_set_stack_def, sym_with_pc_def, asmSemTheory.asm_next_def] >>
  simp[sym_state_component_equality, asmSemTheory.asm_state_component_equality] >>
  metis_tac[]
QED

Theorem inefficient_jump_site[local]:
  ^site ==>
  !pre x y rest.
    asm_static_wf (pre ++ [AsmPushLabel x; AsmOp "JUMPI"; AsmPushLabel y; AsmOp "JUMP"] ++ AsmLabel
      x :: rest) ==>
    ^transport
      (pre ++ [AsmPushLabel x; AsmOp "JUMPI"; AsmPushLabel y; AsmOp "JUMP"] ++ AsmLabel x :: rest)
      (pre ++ [AsmOp "ISZERO"; AsmPushLabel y; AsmOp "JUMPI"] ++ AsmLabel x :: rest)
Proof
  disch_tac >> rpt gen_tac >> disch_tac >>
  first_x_assum (qspecl_then [`pre`,
    `[AsmPushLabel x; AsmOp "JUMPI"; AsmPushLabel y; AsmOp "JUMP"]`,
    `[AsmOp "ISZERO"; AsmPushLabel y; AsmOp "JUMPI"]`, `AsmLabel x :: rest`, `4`] mp_tac) >>
  simp_tac bool_ss [LET_THM] >> impl_tac
  >- (conj_tac
      >- (simp[asm_splice_ok_def, is_data_inst_def, asm_label_refs_def,
               symbolResolveTheory.asm_inst_size_def] >> rw[] >> EVAL_TAC) >>
      simp[] >> rpt strip_tac >>
      mp_tac inefficient_jump_window >> simp_tac bool_ss [LET_THM] >>
      simp[]) >> simp[]
QED

Theorem inefficient_jumps_prefix_transport_conditional:
  ^site /\ ^transitive ==>
  !p. asm_static_wf p ==> ^transport p (FST (optimize_inefficient_jumps p))
Proof
  qabbrev_tac `tr = ^transport` >> strip_tac >>
  `!p. tr p p`
    by (simp[Abbr `tr`] >> gen_tac >> qexists_tac `1` >> simp[] >>
        rpt strip_tac >> metis_tac[LE_ADD]) >>
  `!pre x y rest.
    asm_static_wf (pre ++ [AsmPushLabel x; AsmOp "JUMPI"; AsmPushLabel y; AsmOp "JUMP"] ++ AsmLabel x :: rest) ==>
    tr (pre ++ [AsmPushLabel x; AsmOp "JUMPI"; AsmPushLabel y; AsmOp "JUMP"] ++ AsmLabel x :: rest)
       (pre ++ [AsmOp "ISZERO"; AsmPushLabel y; AsmOp "JUMPI"] ++ AsmLabel x :: rest)`
    by (unabbrev_all_tac >> MATCH_MP_TAC inefficient_jump_site >>
        first_assum MATCH_ACCEPT_TAC) >>
  qpat_x_assum `!pre pat repl post D. _` kall_tac >>
  `!sfx pre. asm_static_wf (pre ++ sfx) ==>
      tr (pre ++ sfx) (pre ++ FST (optimize_inefficient_jumps sfx))`
    suffices_by (strip_tac >> gen_tac >>
      first_x_assum (qspecl_then [`p`, `[]`] mp_tac) >> simp[]) >>
  ho_match_mp_tac optimize_inefficient_jumps_ind >>
  reverse (rpt conj_tac)
  >- simp[optimize_inefficient_jumps_def]
  >- simp[optimize_inefficient_jumps_def]
  >- simp[optimize_inefficient_jumps_def]
  >- simp[optimize_inefficient_jumps_def]
  >- simp[optimize_inefficient_jumps_def] >>
  rpt gen_tac >> strip_tac >> gen_tac >> strip_tac >>
  simp[optimize_inefficient_jumps_fst] >>
  reverse IF_CASES_TAC
  >- (gvs[] >> first_x_assum (qspec_then `pre ++ [a]` mp_tac) >>
      pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC,listTheory.APPEND] >> simp[]) >>
  Cases_on `a` >> Cases_on `e` >> gvs[asm_jumpi_over_jump_def] >>
  Cases_on `c` >> gvs[asm_is_push_label_def] >>
  rename1 `AsmPushLabel lx :: AsmOp "JUMPI" :: AsmPushLabel ly :: _` >>
  `asm_static_wf (pre ++ AsmOp "ISZERO" :: AsmPushLabel ly :: AsmOp "JUMPI" :: AsmLabel lx :: rest)`
    by (mp_tac (Q.INST
          [`pat` |-> `[AsmPushLabel lx; AsmOp "JUMPI"; AsmPushLabel ly; AsmOp "JUMP"]`,
           `repl` |-> `[AsmOp "ISZERO"; AsmPushLabel ly; AsmOp "JUMPI"]`,
           `pfx` |-> `pre`, `sfx` |-> `AsmLabel lx :: rest`] asm_splice_static_wf) >>
        impl_tac
        >- (simp[asm_splice_ok_def, is_data_inst_def, asm_label_refs_def,
                 symbolResolveTheory.asm_inst_size_def] >>
            pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC,listTheory.APPEND] >> simp[] >>
            rpt strip_tac >> gvs[] >> CONV_TAC EVAL) >>
        pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC,listTheory.APPEND] >> simp[]) >>
  first_x_assum (qspec_then `pre` drule) >> disch_tac >>
  qpat_x_assum `!p q r. _` irule >>
  qexists_tac `pre ++ AsmOp "ISZERO" :: AsmPushLabel ly :: AsmOp "JUMPI" :: AsmLabel lx :: rest` >>
  simp[] >>
  qpat_x_assum `!pre x y rest. _` (qspecl_then [`pre`, `lx`, `ly`, `rest`] mp_tac) >>
  pure_rewrite_tac[GSYM listTheory.APPEND_ASSOC,listTheory.APPEND] >> simp[]
QED
