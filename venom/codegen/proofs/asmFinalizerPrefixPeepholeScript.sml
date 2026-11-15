Theory asmFinalizerPrefixPeephole
Ancestors
  asmSplice asmSymPc asmSymSem asmOptimizer asmWf asmOptPeephole list

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
