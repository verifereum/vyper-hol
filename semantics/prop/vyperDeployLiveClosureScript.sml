(* The bounded checker worklist contains its roots and is closed under calls. *)
Theory vyperDeployLiveClosure
Ancestors
  arithmetic list rich_list pair vyperTypeContract vyperTypeCallGraph
  vyperTypeCallGraphSoundness

(* Processing a fresh key transfers its outgoing edges into the queue,
   counting occurrences even when an edge or its target is repeated. *)
Theorem fresh_callees_budget[local]:
  !edges k seen.
    ~MEM k seen ==>
    LENGTH (direct_callees edges k) +
    LENGTH (FILTER (\e. ~MEM (FST e) (k::seen)) edges) =
    LENGTH (FILTER (\e. ~MEM (FST e) seen) edges)
Proof
  Induct >> simp[direct_callees_def] >> rpt strip_tac >>
  first_x_assum (qspecl_then [`k`,`seen`] mp_tac) >>
  Cases_on `FST h = k` >> Cases_on `MEM (FST h) seen` >>
  gvs[direct_callees_def] >> decide_tac
QED

(* All outgoing edges from seen keys must already point into seen or todo.
   With the remaining budget, this invariant yields closure on exhaustion. *)
Theorem call_closure_saturated[local]:
  !edges fuel seen todo.
    LENGTH todo + LENGTH (FILTER (\e. ~MEM (FST e) seen) edges) <= fuel /\
    (!k c. MEM k seen /\ MEM (k,c) edges ==> MEM c seen \/ MEM c todo) ==>
    (!k. MEM k seen \/ MEM k todo ==>
         MEM k (call_closure edges fuel seen todo)) /\
    (!k c. MEM k (call_closure edges fuel seen todo) /\ MEM (k,c) edges ==>
           MEM c (call_closure edges fuel seen todo))
Proof
  gen_tac >> Induct
  >- (rpt gen_tac >> Cases_on `todo` >> simp[call_closure_def] >> metis_tac[]) >>
  pop_assum $ mk_asm "ih" >>
  qx_gen_tac `seen` >> Cases_on `todo`
  >- (simp[call_closure_def] >> metis_tac[]) >>
  strip_tac >> Cases_on `MEM h seen` >> simp[call_closure_def]
  >- (asm_x "ih" $ qspecl_then [`seen`,`t`] mp_tac >>
      (impl_tac >- (conj_tac >- (fs[LENGTH] >> decide_tac) >> fs[] >> metis_tac[])) >>
      simp[] >> metis_tac[]) >>
  asm_x "ih" $ qspecl_then [`h::seen`,`direct_callees edges h ++ t`] mp_tac >>
  (impl_tac
   >- (conj_tac
       >- (qspecl_then [`edges`,`h`,`seen`] mp_tac fresh_callees_budget >>
           simp[LENGTH_APPEND] >>
           fs[LENGTH] >> decide_tac) >>
       simp[MEM_direct_callees, call_edge_rel_def] >> fs[] >> metis_tac[])) >>
  simp[] >> metis_tac[]
QED

Theorem deploy_live_functions_closed:
  (!src ts fn vis mut nr raw args ds ret body.
     MEM (src,ts) mods /\ module_allocated layouts addr src ts /\
     MEM (FunctionDecl vis mut nr raw fn args ds ret body) ts ==>
     MEM (src,fn) (live_functions layouts addr mods)) /\
  (!k c. MEM k (live_functions layouts addr mods) /\
         MEM (k,c) (contract_call_edges mods) ==>
         MEM c (live_functions layouts addr mods))
Proof
  simp[live_functions_def] >>
  qabbrev_tac `edges = contract_call_edges mods` >>
  qabbrev_tac `roots = live_roots layouts addr mods` >>
  qspecl_then [`edges`,`LENGTH roots + LENGTH edges`,`[]`,`roots`]
    mp_tac call_closure_saturated >>
  simp[] >> disch_then (CONJUNCTS_THEN2 (mk_asm "reach") (mk_asm "closed")) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> asm "reach" irule >>
      simp[Abbr `roots`, live_roots_def, MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
      qexists_tac `(src,ts)` >> simp[MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
      qexists_tac `FunctionDecl vis mut nr raw fn args ds ret body` >>
      simp[toplevel_function_keys_def]) >>
  asm "closed" ACCEPT_TAC
QED
