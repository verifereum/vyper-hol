(* Local propagation probes for the scalar bounds operand audit. *)
Theory bodyPtrSubscriptWordProvenance
Ancestors
  bodyPtrSubscriptBounds ptrDiscipline finite_map list compileEnv exprLowering

Theorem first_prov_none:
  (!op. MEM op ops ==> op_prov G op = NONE) ==>
  first_prov G ops = NONE
Proof
  Induct_on `ops` >> simp[first_prov_def]
QED

Theorem scalar_forward_output_provenance_none:
  (!op. MEM op inst.inst_operands ==> op_prov G op = NONE) /\
  (inst.inst_opcode = ADD \/ inst.inst_opcode = SUB \/
   inst.inst_opcode = ASSIGN) /\ MEM x inst.inst_outputs ==>
  FLOOKUP (step_prov PG G inst t) x = NONE
Proof
  strip_tac >> irule step_prov_output_none >> simp[] >>
  `first_prov G inst.inst_operands = NONE` by
    (irule first_prov_none >> simp[]) >>
  gvs[out_prov_def]
QED

Theorem phi_selected_provenance_none:
  resolve_phi lbl inst.inst_operands = SOME op /\ op_prov G op = NONE ==>
  phi_prov (SOME lbl) G inst = NONE
Proof
  simp[phi_prov_def]
QED

Theorem allocated_return_buffer_is_some:
  FST ((do buf <- compile_alloc_buffer n; return (SOME buf) od) st) <> NONE
Proof
  simp[comp_bind_def, comp_return_def] >>
  Cases_on `compile_alloc_buffer n st` >> simp[]
QED

(* Bounded producer audit (locations in defs/exprLoweringScript.sml).
   Producer                     Result / required invariant / transport
   -------------------------------------------------------------------
   literals 1453ff               Lit: op_prov NONE, no child invariant.
   Name 1490ff + unwrap 965ff    LocatedValue; word unwrap loads and kills
                                output provenance (MLOAD/SLOAD/TLOAD).
   arithmetic / out_prov_def    ADD/SUB require NONE on scalar children;
                                other scalar opcodes kill provenance.
   IfExp 2942-2969              branch ASSIGN to fresh result_var, NOT PHI;
                                selected arm NONE, then preserve the result
                                through JMP and entry_prov at exit.
   convert 1659-1868            ConvIdentity and BytesMToBytesM forward v;
                                require typed scalar child NONE. Dynamic
                                bytes conversion loads/shifts; the buffer
                                pointer is not the returned scalar word.
   IntCall 2638-2667            positive returns_count allocates SOME buffer
                                (allocated_return_buffer_is_some), so its
                                NONE/StackValue INVOKE branch is unreachable.
                                LocatedValue uses callee return type; word
                                return unwrap loads. Need metadata/type
                                alignment, not just call-site annotation.
   call ghost ptrSafeRun:58ff   successful decoded INVOKE restricts caller G
                                by outputs, not ordinary step_prov. Callee
                                safety alone is no scalar-result proof.
   Acc Address 2880-2881        forwards lower_value child: need child NONE.
   other account fields        opcode results; Code is nonword, excluded by
                                well-typed scalar classification.

   word_result_ok (exprSafeOperand:43-47) explicitly permits nonword memory
   LocatedValue with a safe pointer, because call-site annotation alone does
   not constrain ce_func_return_type. Thus exprWordOperand's compiler
   induction supplies classification/freshness, NOT scalar provenance.
   body_inv (bodySim:72-76) aligns function metadata; a full scalar output
   argument must also use the typed signature/result relation.

   Same-path interface still missing (not asserted as a theorem here):
     lower_value compile_expr cenv ty e sa = (op,sb), body_inv, typing,
     normal path to sb produced by the expression simulation
       ==> op_prov Gfinal op = NONE, for word expr_type e.
   This must constrain the SAME Gfinal as gas_summary_ptr_at's witness;
   a second existence theorem does not suffice. gas_outcome_ptr_conseq can
   add it only after a path-sensitive invariant is available. An unrestricted
   universal gas_path_ptr endpoint theorem is too strong a proposed shape:
   gas_path_ptr has no first-hit/fragment-containment condition, and its
   witness may continue through sb into arbitrary suffix code and return.
   A usable universal interface must restrict execution to the fragment
   (including selected branch and calls), or a strengthening proof must
   refine the simulation's chosen path constructively.

   fn_has_code (fragExec:112-118) fixes emitted completed blocks exactly
   and the final block's emitted instruction prefix. It does not insert
   PHIs at the compiler's fresh empty exit block, nor constrain arbitrary
   later suffix instructions there. entry_prov processes only PHIs and
   stops at the first non-PHI; exit-prefix effects still need explicit
   reasoning if the final prefix is empty.

   Available at the subscript call site: body_inv metadata alignment,
   expr_body_pre typing, fn_has_code, distinct instruction ids, initial
   ghost_inv and counted normal/exception outcome with expr_post.
   Not available: a normal witness's fragment-bounded trace certificate,
   scalar-child NONE IHs, or a universal word-output provenance theorem.
   No concrete violating typed producer has been verified by this audit. *)
