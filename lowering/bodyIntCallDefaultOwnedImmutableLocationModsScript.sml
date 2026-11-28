(* Static location of an immutable read in the selected raw defaults. *)
Theory bodyIntCallDefaultOwnedImmutableLocationMods
Ancestors
  linkedStateOwnership linkedOwnedImmutableLocation vyperTypeContractStaticMaps
  bodyInvSplit compileEnv vyperTypeContract vyperSubscriptOverlap vyperAST
  finite_map alist list pair

Theorem intcall_default_owned_immutable_location_mods:
  check_contract mode layouts addr mods = SOME art /\
  check_linked_state_ownership layouts addr mods (linked_live_functions mods exps) /\
  ALOOKUP mods src = SOME tops /\
  MEM (FunctionDecl vis mut nr rawfn name args dflts ret ss) tops /\
  (mods = [(NONE,tops)] \/ MEM (src,name) (linked_live_functions mods exps)) /\
  MEM (ReadAcc (StateRef (owner,id))) (accesses_exprs dflts) /\
  declared_immutable mods owner id /\
  immutable_section_layout_mods mods cd ==>
  ?off. FLOOKUP cd.ce_module_vars (owner,id) = SOME (ImmutableLoc off)
Proof
  disch_then (map_every assume_tac o CONJUNCTS) >>
  drule_then assume_tac check_contract_runtime_namespaces >>
  qpat_x_assum `declared_immutable _ _ _`
    (strip_assume_tac o REWRITE_RULE [declared_immutable_def]) >>
  `ALOOKUP mods owner = SOME tls` by
    (irule ALOOKUP_ALL_DISTINCT_MEM >> fs[contract_namespaces_ok_def]) >>
  Q.SUBGOAL_THEN
    `mods = [(NONE,tls)] \/ linked_state_ref_allocated layouts addr mods (owner,id)`
    assume_tac
  >- (Cases_on `mods = [(NONE,tops)]` >- gvs[] >>
     `MEM (src,name) (linked_live_functions mods exps)` by fs[] >>
     `((case mods of [(NONE,_)] => T | _ => F) <=> ?ts. mods = [(NONE,ts)])` by
       (Cases_on `mods` >> simp[] >> PairCases_on `h` >>
        Cases_on `h0` >> Cases_on `t` >> simp[]) >>
     `MEM (src,tops) mods` by (irule ALOOKUP_MEM >> simp[]) >>
     qpat_x_assum `check_linked_state_ownership _ _ _ _` mp_tac >>
     simp[check_linked_state_ownership_def] >>
     disch_then (DISJ_CASES_THEN2 strip_assume_tac mp_tac)
     >- gvs[] >>
     simp[Once EVERY_MEM] >>
     qpat_assum `MEM (src,tops) mods`
       (fn member => disch_then (mp_tac o C MATCH_MP member)) >>
     simp[Once EVERY_MEM] >>
     qpat_assum `MEM (FunctionDecl _ _ _ _ _ _ _ _ _) tops`
       (fn decl => disch_then (mp_tac o C MATCH_MP decl)) >>
     simp[EVERY_MEM, MEM_APPEND] >> strip_tac >> disj2_tac >>
     qpat_assum `!a. MEM a (accesses_exprs dflts) ==> _`
       (drule_then mp_tac) >> simp[]) >>
  drule_all_then ACCEPT_TAC linked_owned_immutable_location
QED
