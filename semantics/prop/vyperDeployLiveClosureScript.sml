(* The bounded checker worklist contains its roots and is closed under calls. *)
Theory vyperDeployLiveClosure
Ancestors
  arithmetic list rich_list pair vyperTypeContract vyperTypeCallGraph
  vyperTypeCallGraphSoundness

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
  qspecl_then [`roots`,`edges`] mp_tac
    (Q.GENL [`roots`,`edges`] call_closure_from_roots) >>
  simp[call_edge_rel_def] >>
  disch_then (CONJUNCTS_THEN2 (mk_asm "reach") (mk_asm "closed")) >>
  conj_tac
  >- (rpt gen_tac >> strip_tac >> asm "reach" irule >>
      simp[Abbr `roots`, live_roots_def, MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
      qexists_tac `(src,ts)` >> simp[MEM_FLAT, MEM_MAP, PULL_EXISTS] >>
      qexists_tac `FunctionDecl vis mut nr raw fn args ds ret body` >>
      simp[toplevel_function_keys_def]) >>
  asm "closed" ACCEPT_TAC
QED
