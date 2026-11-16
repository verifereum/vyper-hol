Theory asmFinalizerPrefixPeephole
Ancestors
  asmSplice asmSymPc asmSymSem asmOptimizer asmWf asmOptPeephole list
  asmFinalizerPrefixPeepFixed asmFinalizerPrefixPeepSwap
  asmFinalizerPrefixPeepComm

(* The ordered walk is parametric in its contextual semantic relation. *)
Theorem peephole_walk_relation[local]:
  !R.
    (!p. R p p) /\
    (!p q r. R p q /\ R q r ==> R p r) /\
    (!pre rest. R
      (pre ++ AsmOp "DUP1" :: AsmOp "SWAP2" :: AsmOp "SWAP1" :: rest)
      (pre ++ AsmOp "SWAP1" :: AsmOp "DUP2" :: rest)) /\
    (!pre rest. R
      (pre ++ AsmOp "DUP1" :: AsmOp "SWAP1" :: AsmOp "POP" :: rest)
      (pre ++ rest)) /\
    (!pre rest. R
      (pre ++ AsmOp "SWAP1" :: AsmOp "POP" :: AsmOp "POP" :: rest)
      (pre ++ AsmOp "POP" :: AsmOp "POP" :: rest)) /\
    (!pre rest name. isPREFIX "SWAP" name ==>
      R (pre ++ AsmOp name :: AsmOp name :: rest) (pre ++ rest)) /\
    (!pre rest y. asm_commutative_op y ==>
      R (pre ++ AsmOp "SWAP1" :: y :: rest) (pre ++ y :: rest)) /\
    (!pre rest. R (pre ++ AsmOp "DUP1" :: AsmOp "SWAP1" :: rest)
      (pre ++ AsmOp "DUP1" :: rest)) ==>
    !asm pre out ch. stack_peephole_opts asm = SOME(out,ch) ==>
      R (pre ++ asm) (pre ++ out)
Proof
  gen_tac >> strip_tac >>
  `!a b c rest l ch pre. peep_swap_pair a b c rest = (l,ch) ==>
    R (pre ++ a::b::c::rest) (pre ++ l)` by
    (rw[peep_swap_pair_def] >> simp[] >>
     Cases_on `a` >> gvs[asm_swap_op_def]) >>
  `!l l' ch pre. peep_swap_comm l = SOME(l',ch) ==>
    R (pre ++ l) (pre ++ l')` by
    (rw[peep_swap_comm_def, AllCaseEqs()] >> simp[]) >>
  `!l l' ch pre. peep_dup_swap l = SOME(l',ch) ==>
    R (pre ++ l) (pre ++ l')` by
    (rw[peep_dup_swap_def, AllCaseEqs()] >> simp[]) >>
  measureInduct_on `LENGTH asm` >>
  Cases_on `asm` >- simp[Once stack_peephole_opts_def] >>
  rename1 `a::t1` >> Cases_on `t1`
  >- simp[Once stack_peephole_opts_def] >>
  rename1 `a::b::t2` >> Cases_on `t2`
  >- simp[Once stack_peephole_opts_def] >>
  rename1 `a::b::c::rest` >> rpt gen_tac >> strip_tac >>
  drule stack_peephole_opts_cons3 >> strip_tac >> gvs[]
  >~ [`stack_peephole_opts (AsmOp "SWAP1" :: AsmOp "DUP2" :: _)`]
  >- (first_x_assum (qspecl_then
        [`AsmOp "SWAP1" :: AsmOp "DUP2" :: rest`] mp_tac) >>
      simp[] >> metis_tac[])
  >~ [`stack_peephole_opts rest = SOME _`]
  >- (first_x_assum (qspecl_then [`rest`] mp_tac) >>
      simp[] >> metis_tac[])
  >~ [`stack_peephole_opts (AsmOp "POP" :: AsmOp "POP" :: _)`]
  >- (first_x_assum (qspecl_then
        [`AsmOp "POP" :: AsmOp "POP" :: rest`] mp_tac) >>
      simp[] >> metis_tac[]) >>
  imp_res_tac peep_swap_pair_length >>
  imp_res_tac peep_swap_comm_length >>
  imp_res_tac peep_dup_swap_length >>
  `LENGTH t < LENGTH (a::b::c::rest)` by gvs[] >>
  first_x_assum (drule_at Any) >>
  disch_then (qspec_then `pre ++ [h]` mp_tac) >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  (impl_tac >- fs[]) >> strip_tac >>
  `R (pre ++ a::b::c::rest) (pre ++ l1)` by metis_tac[] >>
  `R (pre ++ l1) (pre ++ l2)` by metis_tac[] >>
  `R (pre ++ l2) (pre ++ h::t)` by metis_tac[] >>
  metis_tac[]
QED

(* These ML quotations expand in the exported theorem; no logical wrappers. *)
val transport = ``\p q.
  ?K. 0 < K /\ !env s n a.
    s.as_pc = 0 /\ sym_steps p env n (sym_init s) = SymOK a ==>
    (?m b. sym_steps q env m (sym_init s) = SymOK b /\ n <= K * (m + 1)) /\
    (a.sym_base.as_pc < LENGTH p /\ EL a.sym_base.as_pc p = AsmOp "GAS" ==>
      ?m b. sym_steps q env m (sym_init s) = SymOK b /\
        b.sym_base.as_pc < LENGTH q /\ EL b.sym_base.as_pc q = AsmOp "GAS" /\
        b.sym_base.as_gas_readings = a.sym_base.as_gas_readings)``;
val window = ``\pre pat repl post D.
  !env u. u.sym_base.as_pc = LENGTH pre /\ u.sym_base.as_stack = [] /\
    sym_state_labels_in (asm_label_refs (pre ++ pat ++ post)) u ==>
    ?d. 0 < d /\ d <= D /\
      (!i a. i < d /\ sym_steps (pre ++ pat ++ post) env i u = SymOK a ==>
        ~(a.sym_base.as_pc < LENGTH (pre ++ pat ++ post) /\
          EL a.sym_base.as_pc (pre ++ pat ++ post) = AsmOp "GAS")) /\
      (!a. sym_steps (pre ++ pat ++ post) env d u = SymOK a ==>
        ?e. sym_steps (pre ++ repl ++ post) env e u =
          SymOK (sym_with_pc
            (splice_pc (LENGTH pre) (LENGTH pat) (LENGTH repl) a.sym_base.as_pc) a) /\
          (a.sym_base.as_pc <= LENGTH pre \/ LENGTH pre + LENGTH pat <= a.sym_base.as_pc) /\
          (e = 0 ==> LENGTH pre + LENGTH pat <= a.sym_base.as_pc))``;
val single_site = ``!pre pat repl post D.
  asm_splice_ok pat repl /\ asm_static_wf (pre ++ pat ++ post) /\
  (!l. MEM (AsmLabel l) pat ==> ~MEM l (asm_label_refs (pre ++ pat ++ post))) /\
  ^window pre pat repl post D ==>
  ^transport (pre ++ pat ++ post) (pre ++ repl ++ post)``;
val transport_laws = ``(!p. ^transport p p) /\
  (!p q r. ^transport p q /\ ^transport q r ==> ^transport p r)``;
val comm_window = ``!pre post y. asm_commutative_op y ==>
  ^window pre [AsmOp "SWAP1"; y] [y] post 2``;

Theorem peephole_prefix_transport_from_comm_window:
  ^comm_window ==> (^single_site /\ ^transport_laws ==>
    !p q c. asm_static_wf p /\ stack_peephole_opts p = SOME(q,c) ==>
      ^transport p q)
Proof
  qabbrev_tac `tr = ^transport` >> qabbrev_tac `win = ^window` >>
  strip_tac >> strip_tac >>
  `!pre pat repl post D.
    asm_splice_ok pat repl /\ (!l. ~MEM (AsmLabel l) pat) /\
    win pre pat repl post D ==>
    asm_static_wf (pre ++ pat ++ post) ==>
    asm_static_wf (pre ++ repl ++ post) /\
    tr (pre ++ pat ++ post) (pre ++ repl ++ post)` by
    (rpt gen_tac >> strip_tac >> strip_tac >> conj_tac
     >- (irule (cj 1 asm_splice_static_wf) >> qexists_tac `pat` >> simp[]) >>
     qpat_x_assum `!pre pat repl post D. _` irule >>
     simp[] >> qexists_tac `D` >> simp[]) >>
  `IS_SOME (symbolResolve$evm_opcode_byte "DUP2")` by EVAL_TAC >>
  qspec_then `\p q. asm_static_wf p ==> asm_static_wf q /\ tr p q`
    mp_tac peephole_walk_relation >>
  (impl_tac >- (BETA_TAC >> conj_tac >- metis_tac[] >>
    conj_tac >- metis_tac[] >>
    conj_tac >- suspend "dup_swap2_swap1" >>
    conj_tac >- suspend "dup_swap_pop" >>
    conj_tac >- suspend "swap_pop_pop" >>
    conj_tac >- suspend "swap_pair" >>
    conj_tac >- suspend "swap_comm" >>
    suspend "dup_swap")) >>
  strip_tac >> rpt gen_tac >> strip_tac >>
  first_x_assum (qspecl_then [`p`, `[]`, `q`, `c`] mp_tac) >> simp[]
QED

Resume peephole_prefix_transport_from_comm_window[dup_swap2_swap1]:
  rpt gen_tac >>
  `win pre [AsmOp "DUP1"; AsmOp "SWAP2"; AsmOp "SWAP1"]
    [AsmOp "SWAP1"; AsmOp "DUP2"] rest 3` by
    (unabbrev_all_tac >> BETA_TAC >>
     MATCH_ACCEPT_TAC (BETA_RULE dup1_swap2_swap1_bounded_window)) >>
  first_x_assum (drule_at (Pat `win _ _ _ _ _`)) >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  simp[asm_splice_ok_def, is_data_inst_def, asm_label_refs_def,
    symbolResolveTheory.asm_inst_size_def, DISJ_IMP_THM, FORALL_AND_THM]
QED

Resume peephole_prefix_transport_from_comm_window[dup_swap_pop]:
  rpt gen_tac >>
  `win pre [AsmOp "DUP1"; AsmOp "SWAP1"; AsmOp "POP"] [] rest 3` by
    (unabbrev_all_tac >> BETA_TAC >>
     MATCH_ACCEPT_TAC (BETA_RULE dup1_swap1_pop_bounded_window)) >>
  first_x_assum (drule_at (Pat `win _ _ _ _ _`)) >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  simp[asm_splice_ok_def, is_data_inst_def, asm_label_refs_def,
    symbolResolveTheory.asm_inst_size_def, DISJ_IMP_THM, FORALL_AND_THM]
QED

Resume peephole_prefix_transport_from_comm_window[swap_pop_pop]:
  rpt gen_tac >>
  `win pre [AsmOp "SWAP1"; AsmOp "POP"; AsmOp "POP"]
    [AsmOp "POP"; AsmOp "POP"] rest 3` by
    (unabbrev_all_tac >> BETA_TAC >>
     MATCH_ACCEPT_TAC (BETA_RULE swap1_pop_pop_bounded_window)) >>
  first_x_assum (drule_at (Pat `win _ _ _ _ _`)) >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  simp[asm_splice_ok_def, is_data_inst_def, asm_label_refs_def,
    symbolResolveTheory.asm_inst_size_def, DISJ_IMP_THM, FORALL_AND_THM]
QED

Resume peephole_prefix_transport_from_comm_window[swap_pair]:
  rpt gen_tac >> strip_tac >>
  `win pre [AsmOp name; AsmOp name] [] rest 2` by
    (unabbrev_all_tac >> BETA_TAC >>
     drule (BETA_RULE swap_pair_bounded_window) >> disch_then MATCH_ACCEPT_TAC) >>
  first_x_assum (drule_at (Pat `win _ _ _ _ _`)) >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  simp[asm_splice_ok_def, is_data_inst_def, asm_label_refs_def,
    symbolResolveTheory.asm_inst_size_def, DISJ_IMP_THM, FORALL_AND_THM]
QED

Resume peephole_prefix_transport_from_comm_window[swap_comm]:
  rpt gen_tac >> strip_tac >>
  `?name. y = AsmOp name` by (Cases_on `y` >> gvs[asm_commutative_op_def]) >>
  gvs[] >>
  `win pre [AsmOp "SWAP1"; AsmOp name] [AsmOp name] rest 2` by metis_tac[] >>
  first_x_assum (drule_at (Pat `win _ _ _ _ _`)) >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  simp[asm_splice_ok_def, is_data_inst_def, asm_label_refs_def,
    symbolResolveTheory.asm_inst_size_def, DISJ_IMP_THM, FORALL_AND_THM]
QED

Resume peephole_prefix_transport_from_comm_window[dup_swap]:
  rpt gen_tac >>
  `win pre [AsmOp "DUP1"; AsmOp "SWAP1"] [AsmOp "DUP1"] rest 2` by
    (unabbrev_all_tac >> BETA_TAC >>
     MATCH_ACCEPT_TAC (BETA_RULE dup1_swap1_bounded_window)) >>
  first_x_assum (drule_at (Pat `win _ _ _ _ _`)) >>
  pure_rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  simp[asm_splice_ok_def, is_data_inst_def, asm_label_refs_def,
    symbolResolveTheory.asm_inst_size_def, DISJ_IMP_THM, FORALL_AND_THM]
QED

Finalise peephole_prefix_transport_from_comm_window


Theorem peephole_prefix_transport_conditional:
  ^single_site /\ ^transport_laws ==>
    !p q c. asm_static_wf p /\ stack_peephole_opts p = SOME(q,c) ==>
      ^transport p q
Proof
  match_mp_tac peephole_prefix_transport_from_comm_window >>
  MATCH_ACCEPT_TAC swap1_commutative_bounded_window
QED
