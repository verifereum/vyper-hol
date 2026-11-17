(* Stack localization keeps the bridge and operand label maps independent. *)
Theory symInstLocalizeCore
Ancestors asmSymBridge[qualified,ignore_grammar] symEmitSim codegenSymRel codegenRel

(* Parser abbreviation for the existing closed structural bridge relation. *)
val localize_bridge_core_tm = let
  val (params, body) = strip_forall (concl asmSymBridgeTheory.asm_sym_rel_core_pc)
  val core = fst (dest_imp body)
  fun named n = case List.filter (fn v => fst (dest_var v) = n) (free_vars core) of
      [v] => v | _ => raise Fail ("missing bridge parameter " ^ n)
in list_mk_abs (params @ [named "cs", named "ss"], core) end;
val _ = Parse.temp_overload_on ("bridge_core", localize_bridge_core_tm);

Theorem sym_prepared_emit_localize_maps_core:
  bridge_core lo code_ok (cs with as_stack := cs.as_stack ++ rest) ss /\
  venom_asm_rel operand_lo ps vs cs /\ sym_kinds_ok cplan fn ret srest ps ss ==>
  ?top. ss.sym_stack = top ++ srest /\
    bridge_core lo code_ok cs (ss with sym_stack := top) /\
    sym_kinds_ok cplan fn ret [] ps (ss with sym_stack := top) /\
    LIST_REL (\sv w. sval_conc lo sv = SOME w) srest rest /\
    LENGTH top = LENGTH cs.as_stack
Proof
  disch_then assume_tac >>
  rpt (qpat_x_assum `_ /\ _` (CONJUNCTS_THEN assume_tac)) >>
  `?top. ss.sym_stack = top ++ srest /\ LENGTH top = LENGTH cs.as_stack` by
    (gvs[sym_kinds_ok_def, codegenRelTheory.venom_asm_rel_def,
         codegenRelTheory.plan_stack_rel_def] >>
     metis_tac[listTheory.LIST_REL_LENGTH, listTheory.LENGTH_REVERSE]) >>
  drule asm_sym_rel_localize_stack_core >>
  disch_then (qspecl_then [`rest`, `cs.as_stack`, `top`, `srest`] mp_tac) >>
  simp[] >> disch_then (qspec_then `code_ok` mp_tac) >>
  (impl_tac >- (gvs[] >> metis_tac[])) >> strip_tac >>
  `sym_kinds_ok cplan fn ret [] ps (ss with sym_stack := top)` by
    (irule sym_kinds_ok_localize_stack >> simp[]) >>
  gvs[] >> metis_tac[]
QED
