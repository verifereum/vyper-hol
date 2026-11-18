Theory staticAbortOptStackWalk
Ancestors
  list asmOptimizer asmOptPeephole

(* Only syntactic contextual closure is used here.  No execution
   invariant is assumed, and successful options are kept explicit. *)
Theorem peep_swap_pair_contextual[local]:
  (!pre a tail. asm_swap_op a /\ P (pre ++ a::a::tail) ==>
      P (pre ++ tail)) ==>
  !pre a b c rest l ch.
    peep_swap_pair a b c rest = (l,ch) /\
    P (pre ++ a::b::c::rest) ==> P (pre ++ l)
Proof
  strip_tac >> rw[peep_swap_pair_def] >> metis_tac[]
QED

Theorem peep_swap_comm_contextual[local]:
  (!pre a tail. asm_commutative_op a /\
      P (pre ++ AsmOp "SWAP1"::a::tail) ==> P (pre ++ a::tail)) ==>
  !pre l l' ch.
    peep_swap_comm l = SOME(l',ch) /\ P (pre ++ l) ==> P (pre ++ l')
Proof
  strip_tac >> rw[peep_swap_comm_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem peep_dup_swap_contextual[local]:
  (!pre tail. P (pre ++ AsmOp "DUP1"::AsmOp "SWAP1"::tail) ==>
      P (pre ++ AsmOp "DUP1"::tail)) ==>
  !pre l l' ch.
    peep_dup_swap l = SOME(l',ch) /\ P (pre ++ l) ==> P (pre ++ l')
Proof
  strip_tac >> rw[peep_dup_swap_def, AllCaseEqs()] >> metis_tac[]
QED

Theorem stack_peephole_walk_preserves_contextual_under:
  (!pre tail.
    P (pre ++ AsmOp "DUP1"::AsmOp "SWAP2"::AsmOp "SWAP1"::tail) ==>
    P (pre ++ AsmOp "SWAP1"::AsmOp "DUP2"::tail)) /\
  (!pre tail.
    P (pre ++ AsmOp "DUP1"::AsmOp "SWAP1"::AsmOp "POP"::tail) ==>
    P (pre ++ tail)) /\
  (!pre tail.
    P (pre ++ AsmOp "SWAP1"::AsmOp "POP"::AsmOp "POP"::tail) ==>
    P (pre ++ AsmOp "POP"::AsmOp "POP"::tail)) /\
  (!pre a tail. asm_swap_op a /\ P (pre ++ a::a::tail) ==>
    P (pre ++ tail)) /\
  (!pre a tail. asm_commutative_op a /\
    P (pre ++ AsmOp "SWAP1"::a::tail) ==> P (pre ++ a::tail)) /\
  (!pre tail. P (pre ++ AsmOp "DUP1"::AsmOp "SWAP1"::tail) ==>
    P (pre ++ AsmOp "DUP1"::tail)) ==>
  !asm pre out ch.
    P (pre ++ asm) /\ stack_peephole_opts asm = SOME(out,ch) ==>
    P (pre ++ out)
Proof
  strip_tac >>
  drule peep_swap_pair_contextual >> strip_tac >>
  drule peep_swap_comm_contextual >> strip_tac >>
  drule peep_dup_swap_contextual >> strip_tac >>
  measureInduct_on `LENGTH asm` >>
  Cases_on `asm` >- simp_tac (srw_ss()) [Once stack_peephole_opts_def] >>
  rename1 `a::t1` >> Cases_on `t1`
  >- simp_tac (srw_ss()) [Once stack_peephole_opts_def] >>
  rename1 `a::b::t2` >> Cases_on `t2`
  >- simp_tac (srw_ss()) [Once stack_peephole_opts_def] >>
  rename1 `a::b::c::rest` >> rpt gen_tac >> strip_tac >>
  drule stack_peephole_opts_cons3 >> strip_tac >>
  rpt (qpat_x_assum `_ = AsmOp _` SUBST_ALL_TAC)
  >~ [`stack_peephole_opts (AsmOp "SWAP1"::AsmOp "DUP2"::_)`]
  >- (qpat_x_assum `!y. LENGTH y < _ ==> _`
        (qspec_then `AsmOp "SWAP1"::AsmOp "DUP2"::rest` mp_tac) >>
      simp_tac (srw_ss() ++ ARITH_ss) [] >>
      disch_then (qspec_then `pre` mp_tac) >> disch_then irule >>
      conj_tac
      >- (qpat_x_assum `!pre tail. P (_ ++ AsmOp "DUP1"::AsmOp "SWAP2"::_) ==> _`
            irule >> first_assum ACCEPT_TAC) >>
      first_assum (irule_at Any))
  >~ [`stack_peephole_opts rest = SOME _`]
  >- (qpat_x_assum `!y. LENGTH y < _ ==> _` (qspec_then `rest` mp_tac) >>
      simp_tac (srw_ss() ++ ARITH_ss) [] >>
      disch_then (qspec_then `pre` mp_tac) >> disch_then irule >>
      conj_tac
      >- (qpat_x_assum `!pre tail. P (_ ++ AsmOp "DUP1"::AsmOp "SWAP1"::_) ==> P (_ ++ tail)`
            irule >> first_assum ACCEPT_TAC) >>
      first_assum (irule_at Any))
  >~ [`stack_peephole_opts (AsmOp "POP"::AsmOp "POP"::_)`]
  >- (qpat_x_assum `!y. LENGTH y < _ ==> _`
        (qspec_then `AsmOp "POP"::AsmOp "POP"::rest` mp_tac) >>
      simp_tac (srw_ss() ++ ARITH_ss) [] >>
      disch_then (qspec_then `pre` mp_tac) >> disch_then irule >>
      conj_tac
      >- (qpat_x_assum `!pre tail. P (_ ++ AsmOp "SWAP1"::_) ==> _`
            irule >> first_assum ACCEPT_TAC) >>
      first_assum (irule_at Any)) >>
  qpat_x_assum `_ = _::_` SUBST_ALL_TAC >>
  imp_res_tac peep_swap_pair_length >>
  imp_res_tac peep_swap_comm_length >>
  imp_res_tac peep_dup_swap_length >>
  qpat_assum `!pre a b c rest l ch. _` (drule_all_then assume_tac) >>
  qpat_assum `!pre l l' ch. peep_swap_comm _ = _ /\ _ ==> _`
    (drule_all_then assume_tac) >>
  qpat_assum `!pre l l' ch. peep_dup_swap _ = _ /\ _ ==> _`
    (drule_all_then assume_tac) >>
  qpat_x_assum `!y. LENGTH y < _ ==> _` (qspec_then `t` mp_tac) >> impl_tac
  >- (qpat_x_assum `LENGTH (h::t) <= _` mp_tac >>
      simp_tac (srw_ss() ++ ARITH_ss) [] >> decide_tac) >>
  disch_then (qspec_then `pre ++ [h]` mp_tac) >>
  rewrite_tac[GSYM APPEND_ASSOC, APPEND] >>
  disch_then irule >> conj_tac
  >- first_assum ACCEPT_TAC >> first_assum (irule_at Any)
QED

Theorem stack_peephole_walk_preserves_contextual:
  (!pre tail.
    P (pre ++ AsmOp "DUP1"::AsmOp "SWAP2"::AsmOp "SWAP1"::tail) ==>
    P (pre ++ AsmOp "SWAP1"::AsmOp "DUP2"::tail)) /\
  (!pre tail.
    P (pre ++ AsmOp "DUP1"::AsmOp "SWAP1"::AsmOp "POP"::tail) ==>
    P (pre ++ tail)) /\
  (!pre tail.
    P (pre ++ AsmOp "SWAP1"::AsmOp "POP"::AsmOp "POP"::tail) ==>
    P (pre ++ AsmOp "POP"::AsmOp "POP"::tail)) /\
  (!pre a tail. asm_swap_op a /\ P (pre ++ a::a::tail) ==>
    P (pre ++ tail)) /\
  (!pre a tail. asm_commutative_op a /\
    P (pre ++ AsmOp "SWAP1"::a::tail) ==> P (pre ++ a::tail)) /\
  (!pre tail. P (pre ++ AsmOp "DUP1"::AsmOp "SWAP1"::tail) ==>
    P (pre ++ AsmOp "DUP1"::tail)) ==>
  !p q ch. P p /\ stack_peephole_opts p = SOME(q,ch) ==> P q
Proof
  strip_tac >> rpt gen_tac >>
  mp_tac stack_peephole_walk_preserves_contextual_under >> impl_tac
  >- (rpt conj_tac >> first_assum ACCEPT_TAC) >>
  disch_then (qspecl_then [`p`, `[]`, `q`, `ch`] mp_tac) >>
  simp_tac (srw_ss()) [APPEND]
QED
