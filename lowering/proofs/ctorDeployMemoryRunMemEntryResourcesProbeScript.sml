Theory ctorDeployMemoryRunMemEntryResourcesProbe
Ancestors
 ctorDeployMemoryRunMemEntryTaskBound exprLoweringProps finite_map

(* The source-value bound does not bound uninitialized declarations. *)
Theorem ctor_landing_immutable_separation_counterexample:
 !ce cx es actual func.
 let c = ce with <| ce_is_ctor := T; ce_module := NONE;
       ce_vars := FEMPTY;
       ce_module_vars := FEMPTY |+ ((NONE,"imm"), ImmutableLoc 1);
       ce_module_var_type := K (SOME (BaseT BoolT)) |>;
     e = es with immutables := [];
     s = actual with <| vs_allocas := FEMPTY; vs_alloca_next := 0 |> in
 (!name tv v off.
   FLOOKUP c.ce_module_vars (c.ce_module,name) = SOME (ImmutableLoc off) /\
   FLOOKUP (case ALOOKUP e.immutables cx.txn.target of NONE => FEMPTY
     | SOME imms => get_source_immutables c.ce_module imms) name = SOME (tv,v) ==>
   off + type_memory_size tv <= 0) /\
 0 <= s.vs_alloca_next /\
 (!id b sz. FLOOKUP s.vs_allocas id = SOME (b,sz) ==> 0 <= b) /\
 (!id b sz. local_region c e.scopes s id b sz ==> 0 <= b) /\
 ~immutable_alloca_sep func c cx e s
Proof
 rpt gen_tac >> simp[LET_THM, immutable_alloca_sep_def, immutable_decl_sep_def] >>
 qexistsl [`"imm"`, `BaseTV BoolT`, `1`] >>
 simp[FLOOKUP_UPDATE, vyperValueTheory.evaluate_type_def]
QED
