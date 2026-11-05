(* Scope insertion uses the already-established memory layout at the same
   endpoint; no independently chosen S1 execution is identified with it. *)
Theory annAssignPtrMemoryAssign
Ancestors
 annAssignPtrMemoryStageFrame annAssignPtrDeclarationPost stmtSimDeclStore
 exprLoweringProps compileEnv valueEncoding finite_map

Theorem annassign_memory_scope_state_ptr:
 !ctx func cenv cx es s id p sz w inst v tv sc rest assignable.
 stmt_state_rel ctx func cenv cx es s /\ fn_inst_ids_distinct func /\
 es.scopes = sc :: rest /\ lookup_scopes id es.scopes = NONE /\
 FLOOKUP cenv.ce_vars id = SOME (PtrVar (Var p) sz) /\
 not_local_ptr cenv es.scopes p /\ lookup_var p s = SOME w /\
 MEM inst (fn_insts func) /\ inst.inst_opcode = ALLOCA /\ inst.inst_outputs = [p] /\
 FLOOKUP s.vs_allocas inst.inst_id = SOME (w2n w,sz) /\
 type_memory_size tv <= sz /\ val_wf tv v /\
 val_in_memory tv v (w2n w) s.vs_memory ==>
 stmt_state_rel ctx func cenv cx
   (es with scopes := (sc |+ (id, <|assignable := assignable; type := tv;
                                  value := v; popped := []|>)) :: rest) s
Proof
 rpt gen_tac >> strip_tac >>
 irule stmt_state_rel_declare_memory >>
 `immutables_rel cenv cx.txn.target cenv.ce_module cenv.ce_is_ctor es s` by
   fs[stmt_state_rel_def, state_rel_def] >>
 simp[] >> qexistsl [`inst`,`s`,`w`] >> simp[] >>
 qpat_x_assum `not_local_ptr _ _ _` mp_tac >> simp[]
QED
