(*
 * Raw-reachable Venom states for the codegen reachability interface.
 *
 * raw_reachable vs0 ctx is the least visited-instruction invariant generated
 * by the context entry of vs0 and closed under the three clauses of
 * reachability_closed: post-increment instruction steps, terminator-driven
 * block entries, and INVOKE callee entries.  It is Venom-only and generic in
 * the context.
 *
 * TOP-LEVEL:
 *   raw_reachable              - inductive raw-reachable states
 *   raw_reachable_closed       - raw_reachable satisfies reachability_closed
 *   raw_reachable_package      - codegen_reachability_package for it
 *   raw_reachable_package_iff  - it is packaged iff the entry resolves
 *   raw_reachable_least        - every packaged invariant contains it
 *)

Theory contextRawReachable
Ancestors
  contextCodegenRelProps contextCodegenRel venomExecSemantics

(* ===== Definition ===== *)

(* Rules mirror the context entry of codegen_reachability_package and the
   three clauses of reachability_closed, in that order. *)
Inductive raw_reachable:
[~entry:]
  (!vs0 ctx name fn lbl inst s1.
     ctx.ctx_entry = SOME name /\
     lookup_function name ctx.ctx_functions = SOME fn /\
     fn_entry_label fn = SOME lbl /\
     enters_block fn
       (vs0 with <| vs_prev_bb := NONE; vs_current_bb := lbl;
                    vs_inst_idx := 0 |>) s1 /\
     active_inst fn inst s1 ==>
     raw_reachable vs0 ctx fn inst s1)
[~next:]
  (!vs0 ctx fn inst inst' s s' fuel.
     raw_reachable vs0 ctx fn inst s /\ active_inst fn inst s /\
     ~is_terminator inst.inst_opcode /\ step_inst fuel ctx inst s = OK s' /\
     active_inst fn inst' (s' with vs_inst_idx := SUC s.vs_inst_idx) ==>
     raw_reachable vs0 ctx fn inst' (s' with vs_inst_idx := SUC s.vs_inst_idx))
[~block:]
  (!vs0 ctx fn inst inst' s s' s1 fuel.
     raw_reachable vs0 ctx fn inst s /\ active_inst fn inst s /\
     is_terminator inst.inst_opcode /\ step_inst fuel ctx inst s = OK s' /\
     ~s'.vs_halted /\ enters_block fn s' s1 /\ active_inst fn inst' s1 ==>
     raw_reachable vs0 ctx fn inst' s1)
[~callee:]
  (!vs0 ctx caller inv s nm ops callee args cs s1 inst.
     raw_reachable vs0 ctx caller inv s /\ active_inst caller inv s /\
     inv.inst_opcode = INVOKE /\ decode_invoke inv = SOME (nm, ops) /\
     lookup_function nm ctx.ctx_functions = SOME callee /\
     eval_operands ops s = SOME args /\ setup_callee callee args s = SOME cs /\
     enters_block callee cs s1 /\ active_inst callee inst s1 ==>
     raw_reachable vs0 ctx callee inst s1)
End

(* ===== Closure and package ===== *)

(* TOP-LEVEL: closure holds for every initial state and context. *)
Theorem raw_reachable_closed:
  reachability_closed (raw_reachable vs0) ctx
Proof
  rw[reachability_closed_def, fn_entry_inv_def] >>
  metis_tac[raw_reachable_rules]
QED

(* TOP-LEVEL: the package holds whenever the context has a resolvable entry
   function with an entry block. *)
Theorem raw_reachable_package:
  ctx.ctx_entry = SOME name /\
  lookup_function name ctx.ctx_functions = SOME fn /\
  fn_entry_label fn = SOME lbl ==>
  codegen_reachability_package (raw_reachable vs0) ctx vs0
Proof
  rw[codegen_reachability_package_def, raw_reachable_closed,
     fn_entry_inv_def] >>
  metis_tac[raw_reachable_rules]
QED

(* The package's entry existential is the only side condition. *)
Theorem raw_reachable_package_iff:
  codegen_reachability_package (raw_reachable vs0) ctx vs0 <=>
  ?name fn lbl.
    ctx.ctx_entry = SOME name /\
    lookup_function name ctx.ctx_functions = SOME fn /\
    fn_entry_label fn = SOME lbl
Proof
  eq_tac
  >- (simp[codegen_reachability_package_def] >> metis_tac[])
  >- metis_tac[raw_reachable_package]
QED

(* ===== Minimality ===== *)

(* Helper: raw_reachable states lie in every invariant packaged for vs0. *)
Theorem raw_reachable_least_lemma:
  !vs0 ctx fn inst s.
    raw_reachable vs0 ctx fn inst s ==>
    !Inv. codegen_reachability_package Inv ctx vs0 ==> Inv ctx fn inst s
Proof
  ho_match_mp_tac raw_reachable_ind >> rpt conj_tac >> rpt gen_tac
  >- (strip_tac >> gen_tac >>
      simp[codegen_reachability_package_def] >> strip_tac >> gvs[] >>
      drule_all fn_entry_inv_active >> simp[])
  >- (strip_tac >> gen_tac >> strip_tac >> first_x_assum drule >>
      strip_tac >> drule codegen_reachability_package_entry >> strip_tac >>
      drule_all reachability_closed_next >> simp[])
  >- (strip_tac >> gen_tac >> strip_tac >> first_x_assum drule >>
      strip_tac >> drule codegen_reachability_package_entry >> strip_tac >>
      drule_all reachability_closed_block >> simp[])
  >- (strip_tac >> gen_tac >> strip_tac >> first_x_assum drule >>
      strip_tac >> drule codegen_reachability_package_entry >> strip_tac >>
      drule_all reachability_closed_callee >> strip_tac >>
      drule_all fn_entry_inv_active >> simp[])
QED

(* TOP-LEVEL: raw_reachable is the least packaged invariant, so per-state
   obligations on any packaged Inv may be discharged on raw_reachable. *)
Theorem raw_reachable_least:
  codegen_reachability_package Inv ctx vs0 /\
  raw_reachable vs0 ctx fn inst s ==>
  Inv ctx fn inst s
Proof
  metis_tac[raw_reachable_least_lemma]
QED
