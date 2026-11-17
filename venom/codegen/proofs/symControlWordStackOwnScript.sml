(* Word-valued stack prefixes, with independent source and bridge label maps. *)
Theory symControlWordStackOwn
Ancestors
  asmSymBridge[qualified,ignore_grammar] codegenSymRel codegenSymOwnRel
  symFrameControlFacts asmSymOwnCode asmSplice frameRel contextCodegenRel
  unitShapeDefs stackPlanGen stackPlanTypes planExec asmSem asmSymSem
  venomExecSemantics venomInst venomState frameViewFacts genFrameSim emitSim fnFrameBoundaryInvoke

(* Parser abbreviation only for the existing structural bridge interface. *)
val word_bridge_core_tm = let
  val (params, body) = strip_forall (concl asmSymBridgeTheory.asm_sym_rel_core_pc)
  val core = fst (dest_imp body)
  fun named n = case List.filter (fn v => fst (dest_var v) = n) (free_vars core) of
      [v] => v | _ => raise Fail ("missing bridge parameter " ^ n)
in list_mk_abs (params @ [named "cs", named "ss"], core) end;
val _ = Parse.temp_overload_on ("bridge_core", word_bridge_core_tm);

Theorem word_prepared_symbolic_stack_core:
  bridge_core lo code_ok cs ss /\ sym_kinds_ok cplan fn ret srest ps ss /\
  ps.ps_stack = tail ++ operands /\
  (!op sv. MEM op operands /\ op_kind_ok fn ret op sv ==> ?w. sv = Val w) /\
  cs.as_stack = values ++ rest /\ LENGTH values = LENGTH operands ==>
  ?suffix. ss.sym_stack = MAP Val values ++ suffix
Proof
  strip_tac >> fs[sym_kinds_ok_def, listTheory.REVERSE_APPEND] >>
  qpat_assum `LIST_REL _ _ top`
    (mp_then Any (qspec_then `LENGTH operands` mp_tac) rich_listTheory.EVERY2_TAKE) >>
  simp[] >> strip_tac >>
  `TAKE (LENGTH operands) (REVERSE operands) = REVERSE operands` by
    metis_tac[listTheory.TAKE_LENGTH_ID, listTheory.LENGTH_REVERSE] >>
  `TAKE (LENGTH operands) top = MAP Val values` by
    (irule word_kind_prefix_concretization >> conj_tac
     >- (qexistsl [`fn`, `REVERSE operands`, `ret`] >>
         gvs[listTheory.MEM_REVERSE, listTheory.TAKE_APPEND1] >> gvs[]) >>
     qexistsl [`lo`, `rest`, `DROP (LENGTH operands) top ++ srest`] >> gvs[]) >>
  metis_tac[listTheory.TAKE_DROP, listTheory.APPEND_ASSOC]
QED

Theorem arranged_word_prepared_symbolic_stack_core_split_maps:
  venom_asm_rel lo ps vs mid /\ ps.ps_stack = tail ++ operands /\
  EVERY (\op. op <> dead_stack_marker) operands /\
  (!op. MEM op operands ==> eval_operand op vs = operand_val vs lo op) /\
  eval_operands (REVERSE operands) vs = SOME values /\
  bridge_core bridge_lo code_ok (mid with as_stack := mid.as_stack ++ rest) ss /\
  sym_kinds_ok cplan fn ret srest ps ss /\
  (!op sv. MEM op operands /\ op_kind_ok fn ret op sv ==> ?w. sv = Val w) ==>
  mid.as_stack = values ++ DROP (LENGTH operands) mid.as_stack /\
  ?suffix. ss.sym_stack = MAP Val values ++ suffix
Proof
  strip_tac >>
  `mid.as_stack = values ++ DROP (LENGTH operands) mid.as_stack` by
    (irule (emitSimTheory.arranged_eval_operands_stack |> Q.INST
       [`operands` |-> `REVERSE operands`] |> SRULE []) >>
     conj_tac >- gvs[listTheory.EVERY_MEM] >>
     qexistsl [`lo`, `ps`, `tail`, `vs`] >> gvs[]) >>
  simp[] >> irule word_prepared_symbolic_stack_core >> conj_tac
  >- (qexistsl [`code_ok`, `mid with as_stack := mid.as_stack ++ rest`,
        `bridge_lo`, `DROP (LENGTH operands) mid.as_stack ++ rest`] >>
      gvs[] >> metis_tac[]) >>
  qexistsl [`cplan`, `fn`, `operands`, `ps`, `ret`, `srest`, `tail`] >>
  gvs[] >> metis_tac[fnFrameBoundaryInvokeTheory.eval_operands_some_length,
                     listTheory.LENGTH_REVERSE]
QED
