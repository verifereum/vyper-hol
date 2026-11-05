(* Endpoint-only allocation separation; no initial allocation history assumed. *)
Theory bodyPtrBopInEndpoint
Ancestors abiCallerAllocation venomExecSemantics exprLoweringProps words

Theorem endpoint_allocation_words_distinct:
  alloca_inv t /\ t.vs_alloca_next < dimword (:256) /\
  FLOOKUP t.vs_allocas a = SOME (p,n) /\
  FLOOKUP t.vs_allocas b = SOME (q,m) /\
  a <> b /\ 0 < n /\ 0 < m ==>
  (n2w p : bytes32) <> n2w q
Proof
  strip_tac >>
  `p + n <= t.vs_alloca_next` by
    (gvs[venomMemDefsTheory.alloca_inv_def,
         venomMemDefsTheory.alloca_next_valid_def] >>
     qpat_x_assum `!aid base sz. _` (qspecl_then [`a`,`p`,`n`] mp_tac) >> simp[]) >>
  `q + m <= t.vs_alloca_next` by
    (gvs[venomMemDefsTheory.alloca_inv_def,
         venomMemDefsTheory.alloca_next_valid_def] >>
     qpat_x_assum `!aid base sz. _` drule >> simp[]) >>
  drule_all abi_caller_allocation_separate >> strip_tac >>
  `p < dimword (:256) /\ q < dimword (:256) /\ p <> q` by decide_tac >>
  simp[wordsTheory.n2w_11, arithmeticTheory.LESS_MOD]
QED

Theorem exec_alloca_recorded_output:
  inst.inst_outputs = [x] /\ exec_alloca inst s szw = OK t ==>
  ?p n. FLOOKUP t.vs_allocas inst.inst_id = SOME (p,n) /\
        lookup_var x t = SOME (n2w p)
Proof
  strip_tac >>
  Cases_on `FLOOKUP s.vs_allocas inst.inst_id`
  >- gvs[exec_alloca_def, venomStateTheory.update_var_def,
         venomStateTheory.lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  rename1 `FLOOKUP s.vs_allocas inst.inst_id = SOME entry` >>
  PairCases_on `entry` >>
  gvs[exec_alloca_def, venomStateTheory.update_var_def,
      venomStateTheory.lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE]
QED


Theorem step_dispatch_mstore:
  inst.inst_opcode = MSTORE ==>
  step_inst_base inst s = exec_write2 (\addr value s. mstore (w2n addr) value s) inst s
Proof
  simp[step_inst_base_def]
QED

Theorem step_dispatch_add:
  inst.inst_opcode = ADD ==>
  step_inst_base inst s = exec_pure2 word_add inst s
Proof
  simp[step_inst_base_def]
QED

Theorem step_dispatch_eq:
  inst.inst_opcode = EQ ==>
  step_inst_base inst s = exec_pure2 (\x y. bool_to_word (x = y)) inst s
Proof
  simp[step_inst_base_def]
QED

Theorem literal_payload_stores_frame:
  run_inst_seq
    [mk_inst i MSTORE [Var x; Lit 1w] [];
     mk_inst j ADD [Var x; Lit 32w] [px];
     mk_inst k MSTORE [Var px; Lit payload] []] s = OK t ==>
  t.vs_allocas = s.vs_allocas /\ t.vs_alloca_next = s.vs_alloca_next /\
  (!v. v <> px ==> lookup_var v t = lookup_var v s)
Proof
  simp[run_inst_seq_def, step_dispatch_mstore, step_dispatch_add,
       venomInstTheory.mk_inst_def, exec_write2_def, exec_pure2_def,
       venomStateTheory.eval_operand_def,
       venomStateTheory.mstore_def, venomStateTheory.update_var_def,
       venomStateTheory.lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE,
       AllCaseEqs()] >>
  rpt strip_tac >> gvs[finite_mapTheory.FLOOKUP_UPDATE]
QED

Theorem step_dispatch_alloca:
  inst.inst_opcode = ALLOCA /\ inst.inst_operands = [Lit szw] ==>
  step_inst_base inst s = exec_alloca inst s szw
Proof
  simp[step_inst_base_def]
QED

Theorem exec_alloca_other_fields:
  inst.inst_outputs = [x] /\ exec_alloca inst s szw = OK t ==>
  (!v. v <> x ==> lookup_var v t = lookup_var v s) /\
  (!aid entry. aid <> inst.inst_id /\
    FLOOKUP s.vs_allocas aid = SOME entry ==>
    FLOOKUP t.vs_allocas aid = SOME entry)
Proof
  strip_tac >>
  Cases_on `FLOOKUP s.vs_allocas inst.inst_id`
  >- (gvs[exec_alloca_def, venomStateTheory.update_var_def,
          venomStateTheory.lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
      rpt strip_tac >> gvs[]) >>
  rename1 `FLOOKUP s.vs_allocas inst.inst_id = SOME entry` >>
  PairCases_on `entry` >>
  gvs[exec_alloca_def, venomStateTheory.update_var_def,
      venomStateTheory.lookup_var_def, finite_mapTheory.FLOOKUP_UPDATE] >>
  rpt strip_tac >> gvs[]
QED

Theorem endpoint_two_allocations_eq:
  exec_alloca (mk_inst a ALLOCA [Lit 64w] [x]) s 64w = OK u ==>
  exec_alloca (mk_inst b ALLOCA [Lit 64w] [y]) v 64w = OK w ==>
  step_inst_base (mk_inst e EQ [Var x; Var y] [z]) r = OK t ==>
  a <> b /\ x <> y /\ x <> z /\ y <> z /\
  v.vs_allocas = u.vs_allocas /\ lookup_var x v = lookup_var x u /\
  r.vs_allocas = w.vs_allocas /\
  lookup_var x r = lookup_var x w /\ lookup_var y r = lookup_var y w /\
  alloca_inv t /\ t.vs_alloca_next < dimword (:256) /\
  (!p n. FLOOKUP t.vs_allocas a = SOME (p,n) ==> 0 < n) /\
  (!p n. FLOOKUP t.vs_allocas b = SOME (p,n) ==> 0 < n) ==>
  lookup_var z t = SOME 0w
Proof
  rpt strip_tac >>
  `?p n. FLOOKUP u.vs_allocas a = SOME (p,n) /\
         lookup_var x u = SOME (n2w p)` by
    (rev_drule_at (Pos (el 2)) exec_alloca_recorded_output >>
     simp[venomInstTheory.mk_inst_def]) >>
  `?q m. FLOOKUP w.vs_allocas b = SOME (q,m) /\
         lookup_var y w = SOME (n2w q)` by
    (qpat_x_assum `exec_alloca _ v _ = _` mp_tac >>
     simp[Once exec_alloca_def, venomInstTheory.mk_inst_def,
          AllCaseEqs()] >> rpt strip_tac >>
     gvs[venomStateTheory.update_var_def, venomStateTheory.lookup_var_def,
         finite_mapTheory.FLOOKUP_UPDATE]) >>
  `lookup_var x w = lookup_var x v /\
   FLOOKUP w.vs_allocas a = SOME (p,n)` by
    (drule_at (Pos (el 2)) exec_alloca_other_fields >>
     simp[venomInstTheory.mk_inst_def] >> metis_tac[]) >>
  qpat_x_assum `step_inst_base _ _ = _` mp_tac >>
  simp[step_dispatch_eq, venomInstTheory.mk_inst_def, exec_pure2_def,
       venomStateTheory.eval_operand_def] >> strip_tac >>
  gvs[venomStateTheory.update_var_def, venomStateTheory.lookup_var_def,
      finite_mapTheory.FLOOKUP_UPDATE] >>
  `alloca_inv r` by
    (irule localPtrsPropsTheory.alloca_inv_fields >>
     goal_assum (drule_at Any) >> simp[]) >>
  `((n2w p):bytes32) <> n2w q` by
    (irule endpoint_allocation_words_distinct >> metis_tac[]) >>
  gvs[wordsTheory.n2w_11, bool_to_word_def]
QED


Theorem step_alloca_literal:
  step_inst_base (mk_inst a ALLOCA [Lit szw] [x]) s =
  exec_alloca (mk_inst a ALLOCA [Lit szw] [x]) s szw
Proof
  simp[step_inst_base_def, venomInstTheory.mk_inst_def]
QED

Theorem endpoint_literal_pair_eq:
  a <> b /\ ALL_DISTINCT [x;px;y;py;z] /\
  step_inst_base (mk_inst a ALLOCA [Lit 64w] [x]) s = OK u /\
  run_inst_seq [mk_inst i MSTORE [Var x;Lit 1w] [];
                mk_inst j ADD [Var x;Lit 32w] [px];
                mk_inst k MSTORE [Var px;Lit payload] []] u = OK v /\
  step_inst_base (mk_inst b ALLOCA [Lit 64w] [y]) v = OK w /\
  run_inst_seq [mk_inst l MSTORE [Var y;Lit 1w] [];
                mk_inst m ADD [Var y;Lit 32w] [py];
                mk_inst n MSTORE [Var py;Lit payload] []] w = OK r /\
  step_inst_base (mk_inst e EQ [Var x;Var y] [z]) r = OK t /\
  alloca_inv t /\ t.vs_alloca_next < dimword (:256) /\
  (!p sz. FLOOKUP t.vs_allocas a = SOME (p,sz) ==> sz = 64) /\
  (!p sz. FLOOKUP t.vs_allocas b = SOME (p,sz) ==> sz = 64) ==>
  lookup_var z t = SOME 0w
Proof
  simp_tac (srw_ss()) [listTheory.ALL_DISTINCT] >> strip_tac >>
  drule literal_payload_stores_frame >> strip_tac >>
  rev_drule literal_payload_stores_frame >> strip_tac >>
  qpat_x_assum `step_inst_base (mk_inst a ALLOCA _ _) _ = _` mp_tac >>
  rewrite_tac[step_alloca_literal] >> strip_tac >>
  qpat_x_assum `step_inst_base (mk_inst b ALLOCA _ _) _ = _` mp_tac >>
  rewrite_tac[step_alloca_literal] >> strip_tac >>
  `lookup_var x r = lookup_var x w /\
   lookup_var y r = lookup_var y w /\ lookup_var x v = lookup_var x u` by
    metis_tac[] >>
  `(!p sz. FLOOKUP t.vs_allocas a = SOME (p,sz) ==> 0 < sz) /\
   (!p sz. FLOOKUP t.vs_allocas b = SOME (p,sz) ==> 0 < sz)` by
    (conj_tac
     >- (rpt gen_tac >> disch_tac >>
         qpat_x_assum `!p sz. FLOOKUP t.vs_allocas a = _ ==> _` drule >>
         simp_tac arith_ss []) >>
     rpt gen_tac >> disch_tac >>
     qpat_x_assum `!p sz. FLOOKUP t.vs_allocas b = _ ==> _` drule >>
     simp_tac arith_ss []) >>
  drule_all endpoint_two_allocations_eq >> simp_tac bool_ss []
QED
