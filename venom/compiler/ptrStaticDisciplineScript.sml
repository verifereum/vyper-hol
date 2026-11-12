(*
 * The syntactic pointer discipline row 3 of the O1 contract carries into
 * FmpLowering: fn_ptr_ok without the clauses ConcretizeMemLoc can't keep.
 *
 * ConcretizeMemLoc turns each ALLOCA into an ASSIGN of a literal, so the
 * ALLOCA-derived variables drop out of fn_pv.  A PHI that mixed one with
 * a PARAM or DALLOCA pointer then has a non-pointer operand, and fails
 * fn_ptr_ok's phi_pv_all_var; a comparison of two such variables loses
 * one pointer operand.  Here every fn_pv occurrence is negative, so
 * fn_ptr_ok P fn implies fn_static_ptr_ok P fn, and a pass that only
 * shrinks fn_pv keeps it with the same P.  The comparisons stay safe at
 * run time through access_ok, which row 3 also carries.
 *
 * TOP-LEVEL:
 *   ptr_use_static_ok - ptr_use_ok, comparing any two variables allowed
 *   fn_static_ptr_ok  - the bans and affine pointer ops of fn_ptr_ok
 *)
Theory ptrStaticDiscipline
Ancestors
  ptrDiscipline venomInst list pred_set

(* Why: as ptr_use_ok, but an LT/GT/EQ of two variables is allowed even
   when only one of them is still a syntactic pointer; access_ok requires
   both to point into the same site whenever either has provenance. *)
Definition ptr_use_static_ok_def:
  ptr_use_static_ok P pv inst <=>
    (inst.inst_opcode = INVOKE ==>
     ?nm args. decode_invoke inst = SOME (nm,args) /\
               !k v. k < LENGTH args /\ EL k args = Var v /\ v IN pv ==>
                     k IN P nm) /\
    !v. MEM (Var v) inst.inst_operands /\ v IN pv /\
        inst.inst_opcode <> INVOKE /\
        ~is_pointer_preserving_op inst.inst_opcode /\
        ~((inst.inst_opcode = LT \/ inst.inst_opcode = GT \/
           inst.inst_opcode = EQ) /\
          ?u w. inst.inst_operands = [Var u; Var w]) ==>
        FILTER ($= (Var v)) inst.inst_operands = [Var v] /\
        ?ops. (mem_write_ops inst = SOME ops \/ mem_read_ops inst = SOME ops) /\
              ops.iao_ofst = Var v
End

(* Why: FmpLowering moves DALLOCA addresses, so no pointer may become
   observable (MEMTOP, storing, hashing or combining it with a label), and
   the FMP opcodes must be absent.  fn_ptr_ok's phi_pv_all_var and
   definition classification are dropped because ConcretizeMemLoc can't
   keep them; its forced positions and ALLOCA store disjointness because
   FmpLowering doesn't need them. *)
Definition fn_static_ptr_ok_def:
  fn_static_ptr_ok P fn <=>
    (!inst. MEM inst (fn_insts fn) ==>
            inst.inst_opcode <> MEMTOP /\ inst.inst_opcode <> DRET /\
            inst.inst_opcode <> GETFMP /\ inst.inst_opcode <> SETFMP /\
            inst.inst_opcode <> RETFMP /\ inst.inst_opcode <> FMP_PARAM /\
            ((inst.inst_opcode = ISTORE \/ inst.inst_opcode = ILOAD) ==>
             !v. MEM (Var v) inst.inst_operands ==> v NOTIN fn_pv P fn) /\
            ((inst.inst_opcode = ADD \/ inst.inst_opcode = SUB) /\
             (?v. MEM (Var v) inst.inst_operands /\ v IN fn_pv P fn) ==>
             !l. ~MEM (Label l) inst.inst_operands) /\
            ptr_use_static_ok P (fn_pv P fn) inst) /\
    affine_pointer_ops fn (ptr_roots P fn)
End

Theorem ptr_use_ok_static:
  ptr_use_ok P pv inst ==> ptr_use_static_ok P pv inst
Proof
  rw[ptr_use_ok_def, ptr_use_static_ok_def] >> metis_tac[]
QED

Theorem fn_ptr_ok_static:
  fn_ptr_ok P fn ==> fn_static_ptr_ok P fn
Proof
  rw[fn_ptr_ok_def, fn_static_ptr_ok_def] >> metis_tac[ptr_use_ok_static]
QED
