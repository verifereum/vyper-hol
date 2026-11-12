(* Active local provenance when scopes and compiler bindings change. *)
Theory bodyIntCallDeclarationRegions
Ancestors
  compileEnv loweringStateRelDefs exprLoweringProps vyperState finite_map pred_set list
  intCallFrame stmtSimDeclPath venomState venomExecSemantics venomInst

(* Lookup support, rather than equality of scopes, is sufficient for projection. *)
Theorem local_region_support_projection:
  (!name. lookup_scopes name scopes' <> NONE ==>
          lookup_scopes name scopes <> NONE) ==>
  !name b sz. local_region ce scopes' s name b sz ==>
             local_region ce scopes s name b sz
Proof
  simp[local_region_def] >> rpt strip_tac >>
  `lookup_scopes name scopes <> NONE` by (first_x_assum irule >> simp[]) >>
  Cases_on `lookup_scopes name scopes` >> gvs[] >> metis_tac[]
QED

(* A declaration can expose only its own new pointer or an old active region.
   Target register equality is deliberately required only for old active pointers. *)
Theorem local_region_declaration_cases:
  FLOOKUP ce'.ce_vars id = SOME (PtrVar (Var p) new_sz) /\
  (!name. name <> id ==> FLOOKUP ce'.ce_vars name = FLOOKUP ce.ce_vars name) /\
  (!name. name <> id /\ lookup_scopes name scopes' <> NONE ==>
          lookup_scopes name scopes <> NONE) /\
  (!name q sz. name <> id /\ lookup_scopes name scopes <> NONE /\
     FLOOKUP ce.ce_vars name = SOME (PtrVar (Var q) sz) ==>
     lookup_var q t = lookup_var q s) ==>
  !name b sz. local_region ce' scopes' t name b sz ==>
    (name = id /\ sz = new_sz /\ ?w. lookup_var p t = SOME w /\ b = w2n w) \/
    (name <> id /\ local_region ce scopes s name b sz)
Proof
  strip_tac >> rpt gen_tac >> Cases_on `name = id`
  >- (simp[local_region_def] >> metis_tac[]) >>
  simp[local_region_def] >> rpt strip_tac >>
  rename1 `lookup_var old_p t = SOME old_w` >>
  `lookup_scopes name scopes <> NONE` by (first_x_assum irule >> simp[]) >>
  `lookup_var old_p t = lookup_var old_p s` by
    (first_x_assum irule >> qexistsl_tac [`name`, `sz`] >> simp[]) >>
  Cases_on `lookup_scopes name scopes` >> gvs[]
QED

Theorem local_region_scope_declare_cases:
  !ce sc rest s id entry name b sz.
    local_region ce ((sc |+ (id,entry)) :: rest) s name b sz ==>
    name = id \/ local_region ce (sc :: rest) s name b sz
Proof
  rpt gen_tac >> Cases_on `name = id` >>
  simp[local_region_def, lookup_scopes_def, FLOOKUP_UPDATE]
QED

(* The compiler has already bound the pointer before evaluating the RHS.
   Its allocation remains registered even if the RHS performs more allocations. *)
Theorem local_region_declared_allocation:
  FLOOKUP ce.ce_vars id = SOME (PtrVar (Var p) size_bytes) /\
  lookup_var p s = SOME w /\
  FLOOKUP s.vs_allocas aid = SOME (w2n w,size_bytes) /\ allocas_above lo s /\
  (!name b sz. local_region ce (sc :: rest) s name b sz ==>
               authorized name b sz) /\
  (!b. lo <= b ==> authorized id b size_bytes) ==>
  !name b sz. local_region ce ((sc |+ (id,entry)) :: rest) s name b sz ==>
             authorized name b sz
Proof
  strip_tac >> rpt gen_tac >> strip_tac >>
  drule local_region_scope_declare_cases >> strip_tac
  >- (gvs[local_region_def] >> first_x_assum irule >>
      fs[allocas_above_def] >> metis_tac[]) >>
  first_x_assum irule >> goal_assum (drule_at Any)
QED

Theorem local_region_pop_authorized:
  (!name b sz. local_region ce (sc :: rest) s name b sz ==>
               authorized name b sz) /\
  (!name. name IN FDOM sc ==> lookup_scopes name rest = NONE) ==>
  !name b sz. local_region ce rest s name b sz ==> authorized name b sz
Proof
  rpt strip_tac >> first_x_assum irule >>
  irule local_region_pop_scope >> simp[] >> goal_assum (drule_at Any)
QED
