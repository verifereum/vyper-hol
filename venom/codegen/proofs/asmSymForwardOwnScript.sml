(* Forward execution at supplied label offsets and fixed own-code bytes.
   Primitive own observations are explicit supplier contracts here. *)
Theory asmSymForwardOwn
Ancestors asmSymBridge asmSymOwnCode asmSymSem asmSem list finite_map

(* Recover the shared syntax from the exported base interface; no logical
   constant or definition is introduced by this parser abbreviation. *)
val forward_bridge_core_tm = let
  val (params, body) = strip_forall (concl asmSymBridgeTheory.asm_sym_rel_core_pc)
  val core = fst (dest_imp body)
  fun named n = case List.filter (fn v => fst (dest_var v) = n) (free_vars core) of
      [v] => v | _ => raise Fail ("missing bridge parameter " ^ n)
  val args = params @ [named "cs", named "ss"]
in list_mk_abs (args, core) end;
val forward_bridge_result_tm = let
  val body = lhs (concl asmSymBridgeTheory.asm_sym_step_rel_core_canonical)
  val rel = ``asm_sym_rel p env``
  val r = mk_var ("R", type_of rel)
  val body = subst [rel |-> r] body
  fun named n = case List.filter (fn v => fst (dest_var v) = n) (free_vars body) of
      [v] => v | _ => raise Fail ("missing result parameter " ^ n)
in list_mk_abs ([r, named "sr", named "cr"], body) end;
val _ = Parse.temp_overload_on ("bridge_core", forward_bridge_core_tm);
val _ = Parse.temp_overload_on ("bridge_result", forward_bridge_result_tm);

Theorem asm_sym_rel_own_pc:
  asm_sym_rel_own lo p env own cs ss ==>
  ss.sym_base.as_pc = cs.as_pc
Proof
  rewrite_tac[GSYM asm_sym_rel_core_own] >>
  metis_tac[asm_sym_rel_core_pc]
QED

Theorem asm_sym_inst_step_own_conditional:
  (!l. MEM (AsmPushLabel l) p \/ (?d. MEM (AsmPushOfst l d) p) ==>
    ?off. FLOOKUP lo l = SOME off) /\
  (!dest i w. sym_jump_dest p dest = SOME i /\
    sval_conc lo dest = SOME w ==>
    FLOOKUP (build_offset_to_pc p) (w2n w) = SOME i) /\
  (!cs ss name. asm_sym_rel_own lo p env own cs ss /\
    (name = "CODESIZE" \/ name = "CODECOPY") ==>
    bridge_result (asm_sym_rel_own lo p env own)
      (sym_step_op_own p env own name ss)
      (asm_step_op (build_offset_to_pc p) name cs)) /\
  asm_sym_rel_own lo p env own cs ss /\ MEM inst p ==>
  bridge_result (asm_sym_rel_own lo p env own)
    (sym_step_own p env own inst ss)
    (asm_step lo (build_offset_to_pc p) inst cs)
Proof
  strip_tac >>
  `!l d w. sym_data_label p env l /\ sym_delta_ok d /\
    sval_conc lo (Lab l d) = SOME w ==>
    ?off. FLOOKUP lo l = SOME off /\ env ' l = DROP off cs.as_code /\
      w2n w = off + d` by
    (rpt strip_tac >>
     `asm_data_env_lo_ok lo p env own /\ cs.as_code = own` by
       fs[asm_sym_rel_own_def] >>
     drule_all sym_codecopy_address_own >> simp[]) >>
  `bridge_result (asm_sym_rel_own lo p env own) (sym_step p env inst ss)
     (asm_step lo (build_offset_to_pc p) inst cs)` by
    (qspecl_then [`lo`, `\code. asm_data_env_lo_ok lo p env own /\ code = own`]
       mp_tac asm_sym_inst_step_core >>
     simp[asm_sym_rel_core_own] >> disch_then irule >> simp[]) >>
  Cases_on `inst` >> fs[sym_step_own_def] >>
  rename1 `MEM (AsmOp name) p` >>
  Cases_on `name = "CODESIZE" \/ name = "CODECOPY"`
  >- (simp[asm_step_def] >> first_x_assum irule >> simp[]) >>
  gvs[sym_step_op_own_def, sym_step_def, asm_step_def]
QED

Theorem asm_sym_forward_own_conditional:
  (!l. MEM (AsmPushLabel l) p \/ (?d. MEM (AsmPushOfst l d) p) ==>
    ?off. FLOOKUP lo l = SOME off) /\
  (!dest i w. sym_jump_dest p dest = SOME i /\
    sval_conc lo dest = SOME w ==>
    FLOOKUP (build_offset_to_pc p) (w2n w) = SOME i) /\
  (!cs ss name. asm_sym_rel_own lo p env own cs ss /\
    (name = "CODESIZE" \/ name = "CODECOPY") ==>
    bridge_result (asm_sym_rel_own lo p env own)
      (sym_step_op_own p env own name ss)
      (asm_step_op (build_offset_to_pc p) name cs)) /\
  label_disciplined_own env own p s /\ s.as_pc = 0 /\
  asm_data_env_lo_ok lo p env own /\ s.as_code = own /\
  sym_terminal (asm_result_sym (asm_steps lo (build_offset_to_pc p) p n s)) ==>
  ?fuel. sym_result_rel
    (asm_result_sym (asm_steps lo (build_offset_to_pc p) p n s))
    (sym_run_own p env own fuel (sym_init s))
Proof
  strip_tac >>
  qspecl_then [`asm_sym_rel_own lo p env own`, `sym_step_own p env own`,
    `sym_run_own p env own`, `lo`, `build_offset_to_pc p`, `p`]
    mp_tac asm_sym_run_forward_core >>
  impl_tac
  >- (conj_tac >- metis_tac[asm_sym_rel_own_pc] >>
      conj_tac >- simp[Once sym_run_own_def] >>
      rpt strip_tac >> irule asm_sym_inst_step_own_conditional >>
      simp[EL_MEM]) >>
  disch_then irule >> simp[asm_sym_rel_own_init] >>
  fs[label_disciplined_own_def]
QED
