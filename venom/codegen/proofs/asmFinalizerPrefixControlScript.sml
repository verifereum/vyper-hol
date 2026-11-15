(* Quantitative source chunks for control-flow label renaming. *)
Theory asmFinalizerPrefixControl
Ancestors
  asmSplice asmSymPc asmSymSem asmSem
  asmFinalizerPrefixRename asmFinalizerPrefixUnreachable
  asmFinalizerPrefixUnused asmFinalizerPrefixCompose
  asmOptMergeJumpdests

Theorem rename_label_prefix_chunk:
  !p k x y env ss.
    k+1<LENGTH p /\ EL k p=AsmLabel x /\
    EL (k+1) p=AsmLabel y /\ ss.sym_base.as_pc=k /\
    ss.sym_base.as_stack=[] ==>
    sym_steps p env 1 ss=SymOK(sym_with_pc (k+1) ss) /\
    (!i a. i<1 /\ sym_steps p env i ss=SymOK a ==>
      a.sym_base.as_pc<LENGTH p /\ EL a.sym_base.as_pc p<>AsmOp "GAS" /\
      a.sym_base.as_gas_readings=ss.sym_base.as_gas_readings)
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- (simp[sym_steps_pos, sym_step_def, asm_step_def, sym_lift_def,
           asm_next_def, sym_steps_def, sym_with_pc_def] >>
      simp[sym_state_component_equality, asm_state_component_equality]) >>
  rpt strip_tac >> `i=0` by decide_tac >>
  gvs[sym_steps_def]
QED

Theorem rename_jump_prefix_chunk:
  !p k x y j env ss.
    k+2<LENGTH p /\ EL k p=AsmLabel x /\
    EL (k+1) p=AsmPushLabel y /\ EL (k+2) p=AsmOp "JUMP" /\
    INDEX_OF (AsmLabel y) p=SOME j /\ ss.sym_base.as_pc=k /\
    ss.sym_base.as_stack=[] ==>
    sym_steps p env 3 ss=SymOK(sym_with_pc j ss) /\
    (!i a. i<3 /\ sym_steps p env i ss=SymOK a ==>
      a.sym_base.as_pc<LENGTH p /\ EL a.sym_base.as_pc p<>AsmOp "GAS" /\
      a.sym_base.as_gas_readings=ss.sym_base.as_gas_readings)
Proof
  rpt gen_tac >> strip_tac >> conj_tac
  >- (simp[sym_steps_pos, sym_step_def, asm_step_def, sym_lift_def,
           asm_next_def, sym_steps_def, sym_with_pc_def,
           sym_set_stack_def, sym_step_op_def, sym_jump_def, sym_jump_dest_def] >>
      simp[sym_state_component_equality, asm_state_component_equality]) >>
  rpt strip_tac >> `i=0 \/ i=1 \/ i=2` by decide_tac >>
  gvs[sym_steps_pos, sym_steps_def, sym_step_def, asm_step_def,
      sym_lift_def, asm_next_def, sym_set_stack_def] >>
  gvs[sym_state_component_equality, asm_state_component_equality]
QED

(* Quotation abbreviation only; the exported conclusions contain no new constant. *)
val transport = ``\p q.
  ?K. 0 < K /\ !env s n a.
    s.as_pc = 0 /\ sym_steps p env n (sym_init s) = SymOK a ==>
    (?m b. sym_steps q env m (sym_init s) = SymOK b /\ n <= K * (m+1)) /\
    (a.sym_base.as_pc < LENGTH p /\ EL a.sym_base.as_pc p = AsmOp "GAS" ==>
     ?m b. sym_steps q env m (sym_init s) = SymOK b /\
       b.sym_base.as_pc < LENGTH q /\ EL b.sym_base.as_pc q = AsmOp "GAS" /\
       b.sym_base.as_gas_readings = a.sym_base.as_gas_readings)``;

Theorem merge_jumpdests_prefix_transport:
  !p. asm_static_wf p ==> ^transport p (FST (merge_jumpdests p))
Proof
  BETA_TAC >> match_mp_tac (BETA_RULE merge_jumpdests_prefix_transport_conditional) >> conj_tac
  >- (BETA_TAC >> MATCH_ACCEPT_TAC rename_site_prefix_transport) >>
  MATCH_ACCEPT_TAC (BETA_RULE prefix_transport_trans)
QED

Theorem prune_unreachable_prefix_transport:
  !p. asm_static_wf p ==> ^transport p (FST (prune_unreachable_code p))
Proof
  BETA_TAC >> match_mp_tac (BETA_RULE prune_unreachable_prefix_transport_conditional) >> conj_tac
  >- (BETA_TAC >> MATCH_ACCEPT_TAC bounded_splice_prefix_transport) >>
  MATCH_ACCEPT_TAC (BETA_RULE prefix_transport_trans)
QED

Theorem prune_unused_prefix_transport:
  !p. asm_static_wf p ==> ^transport p (FST (prune_unused_jumpdests p))
Proof
  BETA_TAC >> match_mp_tac (BETA_RULE prune_unused_prefix_transport_conditional) >> conj_tac
  >- (BETA_TAC >> MATCH_ACCEPT_TAC bounded_splice_prefix_transport) >>
  MATCH_ACCEPT_TAC (BETA_RULE prefix_transport_trans)
QED
