(* Bounded suffix diagnostic only: these facts do not establish that the
   suffix's initial ghost is reachable after a child satisfying its judgment.
   context's compile_bytestring_copy_len emits MLOAD followed by ADD 31.
   The unequal tuple copy reaches that pair at source offset 64; the equal
   tuple branch instead emits one constant-length MCOPY.

   Source-backed prefix (contextScript.sml 633-651, 673-714, 835-841):
   src layout Tuple(Bytes1,Bytes1); dst Tuple(Bytes33,Bytes1).
   Assume acyclic metadata, clean base pointers S,D, empty source bytes,
   singleton memory taint {S+64}, nonwrapping arithmetic, disjoint buffers.
   1 MLOAD S -> l0         reads S..S+31, output clean, value 0
   2 ADD l0,31 -> p0       clean, value 31
   3 AND p0,-32 -> r0      clean, value 0
   4 ADD r0,32 -> n0       clean, value 32
   5 MCOPY D,S,n0          writes D..D+31; preserves taint at S+64
   6 ADD D,96 -> d1        clean destination address
   7 ADD S,64 -> s1        clean source address
   8 MLOAD s1 -> l1        output taint {0}, value still 0
   9 ADD l1,31 -> p1       FIRST REJECTED USE: taint_ok rejects ADD.
   The checked lemmas below establish the local load/ADD obstruction.
   There is no intervening overwrite of the second source header.
   Equal tuple types select a single MCOPY with constant length 128 instead:
   copying tainted source bytes is allowed; no header arithmetic occurs.

   Residual obligations, NOT claimed here: evaluated whole compiler-state
   equality for this prefix, a complete machine/ghost run with allocated
   pointer coverage, and (critically) a reachable child satisfying the
   universal annotated judgment. This is not target falsehood evidence. *)
Theory bodyPtrStructLitFirstUse
Ancestors ptrDiscipline pred_set arithmetic list

Theorem mem_word_taint_singleton_at:
  !a. mem_word_taint {a} a = {0}
Proof
  simp[mem_word_taint_def, EXTENSION] >> decide_tac
QED

Theorem taint_ok_add_operands:
  !fn tn inst s.
    inst.inst_opcode = ADD ==>
    (taint_ok fn tn inst s <=>
     (!op. MEM op inst.inst_operands ==> op_taint tn op = {}))
Proof
  rpt strip_tac >>
  simp[taint_ok_def, contextCodegenRelTheory.source_memory_read_ranges_def] >>
  metis_tac[]
QED

(* The restricted instruction immediately following a header load cannot use
   the loaded value, even when the concrete length happens to be zero. *)
Theorem mload_tainted_header_add_rejected:
  !fn tn load add s s' t x a.
    load.inst_opcode = MLOAD /\ load.inst_operands = [a] /\
    load.inst_outputs = [x] /\
    (?w. eval_operand a s = SOME w /\
         mem_word_taint tn.t_mem (w2n w) <> {}) /\
    add.inst_opcode = ADD /\ MEM (Var x) add.inst_operands ==>
    ~taint_ok fn (step_taint load s s' tn) add t
Proof
  rpt strip_tac >>
  `op_taint (step_taint load s s' tn) (Var x) = {}` by
    metis_tac[taint_ok_add_operands] >>
  gvs[step_taint_def, op_taint_def, set_var_taint_def, out_taint_def,
      finite_mapTheory.FLOOKUP_UPDATE]
QED
