(*
 * DFG soundness predicates
 *
 * What the data-flow graph of a function says about the values of
 * variables in a runtime environment, for the opcodes the DFG-based
 * passes reason about (dfg_tracked_opcode).
 *
 * TOP-LEVEL:
 *   dfg_sound        — ASSIGN/ISZERO/EQ/compare entries hold in env
 *   dfg_ext_sound    — dfg_sound plus ADD/SUB and full LT/GT entries,
 *                      and operands of defined tracked entries are defined
 *   dfg_block_local  — tracked entries' operand definers precede them in
 *                      the same block
 *   dfg_entry_sound  — everything the DFG says about one entry
 *   dfg_prefix_sound — dfg_entry_sound for the entries defined before a
 *                      given position of a block (the invariant preserved
 *                      by every step, loops included)
 *)

Theory dfgSoundDefs
Ancestors
  dfgDefs venomExecSemantics finite_map integer_word

(* ===== DFG Semantic Soundness — per-opcode predicates ===== *)

(* Each predicate captures what the DFG tells us about variable values
   in the runtime environment. These are small enough for fs[]/simp[].
   The monolithic dfg_sound_def caused rewriter timeouts. *)

Definition dfg_assign_sound_def:
  dfg_assign_sound dfg env =
    !v inst u. dfg_get_def dfg v = SOME inst /\
      inst.inst_opcode = ASSIGN /\ inst.inst_operands = [Var u] /\
      v IN FDOM env ==>
      FLOOKUP env v = FLOOKUP env u
End

Definition dfg_iszero_sound_def:
  dfg_iszero_sound dfg env =
    !v inst tv. dfg_get_def dfg v = SOME inst /\
      inst.inst_opcode = ISZERO /\ inst.inst_operands = [Var tv] ==>
      !w. FLOOKUP env v = SOME w ==>
        (w <> 0w ==> FLOOKUP env tv = SOME 0w) /\
        (w = 0w ==> !w'. FLOOKUP env tv = SOME w' ==> w' <> 0w)
End

Definition dfg_eq_sound_def:
  dfg_eq_sound dfg env =
    !v inst lhs rhs. dfg_get_def dfg v = SOME inst /\
      inst.inst_opcode = EQ /\ inst.inst_operands = [lhs; rhs] ==>
      !w. FLOOKUP env v = SOME w ==> w <> 0w ==>
        (!u. lhs = Var u ==> ?wu. FLOOKUP env u = SOME wu) /\
        (!u. rhs = Var u ==> ?wu. FLOOKUP env u = SOME wu) /\
        (!u wu wl. lhs = Var u /\ rhs = Lit wl /\
                    FLOOKUP env u = SOME wu ==> wu = wl) /\
        (!u wu wl. rhs = Var u /\ lhs = Lit wl /\
                    FLOOKUP env u = SOME wu ==> wu = wl) /\
        (!u1 u2 w1 w2. lhs = Var u1 /\ rhs = Var u2 /\
           FLOOKUP env u1 = SOME w1 /\ FLOOKUP env u2 = SOME w2 ==>
           w1 = w2)
End

Definition dfg_compare_sound_def:
  dfg_compare_sound dfg env =
    !v inst lhs rhs. dfg_get_def dfg v = SOME inst /\
      (inst.inst_opcode = LT \/ inst.inst_opcode = GT \/
       inst.inst_opcode = SLT \/ inst.inst_opcode = SGT) /\
      inst.inst_operands = [lhs; rhs] ==>
      !w. FLOOKUP env v = SOME w ==>
        (!u wl wu. lhs = Var u /\ rhs = Lit wl /\
          FLOOKUP env u = SOME wu ==>
          ((w <> 0w) =
            (if inst.inst_opcode = LT then w2n wu < w2n wl
             else if inst.inst_opcode = GT then w2n wu > w2n wl
             else if inst.inst_opcode = SLT then w2i wu < w2i wl
             else w2i wu > w2i wl))) /\
        (!u wl wu. rhs = Var u /\ lhs = Lit wl /\
          FLOOKUP env u = SOME wu ==>
          ((w <> 0w) =
            (if inst.inst_opcode = LT then w2n wl < w2n wu
             else if inst.inst_opcode = GT then w2n wl > w2n wu
             else if inst.inst_opcode = SLT then w2i wl < w2i wu
             else w2i wl > w2i wu)))
End

(* Combined predicate for convenience *)
Definition dfg_sound_def:
  dfg_sound dfg env =
    (dfg_assign_sound dfg env /\ dfg_iszero_sound dfg env /\
     dfg_eq_sound dfg env /\ dfg_compare_sound dfg env)
End

(* Opcodes tracked by the DFG soundness predicates.
   Only these opcodes get dfg_sound sub-predicates and dfg_block_local coverage.
   PHI, NOP, JMP, etc. are NOT tracked — their operands may not all be evaluated. *)
Definition dfg_tracked_opcode_def:
  dfg_tracked_opcode opc <=>
    (opc = ASSIGN \/ opc = ISZERO \/
     opc = EQ \/ opc = LT \/ opc = GT \/ opc = SLT \/ opc = SGT \/
     opc = ADD \/ opc = SUB)
End

(* ===== Extended DFG soundness for arithmetic/compare chains ===== *)

(* eval_op_env evaluates an operand against a variable environment,
   handling Var, Lit, and Label uniformly. *)
Definition eval_op_env_def:
  eval_op_env (Var v) env = FLOOKUP env v /\
  eval_op_env (Lit w) env = SOME w /\
  eval_op_env (Label _) env = NONE
End

(* Arithmetic soundness: ADD/SUB instructions produce the correct result.
   Guarded by no-Label operands since eval_op_env cannot represent Labels. *)
Definition dfg_arith_sound_def:
  dfg_arith_sound dfg env <=>
    !v inst op1 op2.
      dfg_get_def dfg v = SOME inst /\
      (inst.inst_opcode = ADD \/ inst.inst_opcode = SUB) /\
      inst.inst_operands = [op1; op2] /\ v IN FDOM env /\
      (!lbl. op1 <> Label lbl) /\ (!lbl. op2 <> Label lbl) ==>
      ?w1 w2.
        eval_op_env op1 env = SOME w1 /\
        eval_op_env op2 env = SOME w2 /\
        FLOOKUP env v = SOME (if inst.inst_opcode = ADD
                               then word_add w1 w2
                               else word_sub w1 w2)
End

(* Compare-full soundness: LT/GT with arbitrary operand types.
   Guarded by no-Label operands since eval_op_env cannot represent Labels. *)
Definition dfg_compare_full_sound_def:
  dfg_compare_full_sound dfg env <=>
    !v inst op1 op2.
      dfg_get_def dfg v = SOME inst /\
      (inst.inst_opcode = LT \/ inst.inst_opcode = GT) /\
      inst.inst_operands = [op1; op2] /\ v IN FDOM env /\
      (!lbl. op1 <> Label lbl) /\ (!lbl. op2 <> Label lbl) ==>
      ?w1 w2.
        eval_op_env op1 env = SOME w1 /\
        eval_op_env op2 env = SOME w2 /\
        FLOOKUP env v =
          SOME (bool_to_word
                  (if inst.inst_opcode = LT
                   then w2n w1 < w2n w2
                   else w2n w1 > w2n w2))
End

(* ===== dfg_sound FUPDATE: 4 sub-lemmas + combiner ===== *)

(* Combined extended DFG soundness *)
Definition dfg_ext_sound_def:
  dfg_ext_sound dfg env <=>
    dfg_sound dfg env /\
    dfg_arith_sound dfg env /\
    dfg_compare_full_sound dfg env /\
    (!vv dinst u. dfg_get_def dfg vv = SOME dinst /\
       vv IN FDOM env /\ dfg_tracked_opcode dinst.inst_opcode /\
       MEM (Var u) dinst.inst_operands ==>
       u IN FDOM env)
End

(* Block-local DFG property: for DFG-tracked opcodes, the defining
   instruction and the defining instructions of its Var operands are
   all in the same basic block, and the operand definer appears no
   later than the using instruction. This prevents cross-block
   staleness and ensures operand values are stable after the tracked
   instruction executes. *)
Definition dfg_block_local_def:
  dfg_block_local fn <=>
    !v inst u inst_u.
      dfg_get_def (dfg_build_function fn) v = SOME inst /\
      MEM (Var u) inst.inst_operands /\
      dfg_tracked_opcode inst.inst_opcode /\
      dfg_get_def (dfg_build_function fn) u = SOME inst_u ==>
      !bb. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions ==>
        MEM inst_u bb.bb_instructions /\
        !i j. i < LENGTH bb.bb_instructions /\
              j < LENGTH bb.bb_instructions /\
              EL i bb.bb_instructions = inst_u /\
              EL j bb.bb_instructions = inst ==>
              i < j
End


(* What dfg_sound and the operand closure say about entry v (defined by
   dinst) in env: their clauses for that one entry (dfg_sound_entries). *)
Definition dfg_entry_base_sound_def:
  dfg_entry_base_sound env v dinst <=>
    (dfg_tracked_opcode dinst.inst_opcode ==>
       !u. MEM (Var u) dinst.inst_operands ==> u IN FDOM env) /\
    (dinst.inst_opcode = ASSIGN ==>
       !u. dinst.inst_operands = [Var u] ==> FLOOKUP env v = FLOOKUP env u) /\
    (dinst.inst_opcode = ISZERO ==>
       !tv. dinst.inst_operands = [Var tv] ==>
         !w. FLOOKUP env v = SOME w ==>
           (w <> 0w ==> FLOOKUP env tv = SOME 0w) /\
           (w = 0w ==> !w'. FLOOKUP env tv = SOME w' ==> w' <> 0w)) /\
    (dinst.inst_opcode = EQ ==>
       !lhs rhs. dinst.inst_operands = [lhs; rhs] ==>
         !w. FLOOKUP env v = SOME w ==> w <> 0w ==>
           (!u. lhs = Var u ==> ?wu. FLOOKUP env u = SOME wu) /\
           (!u. rhs = Var u ==> ?wu. FLOOKUP env u = SOME wu) /\
           (!u wu wl. lhs = Var u /\ rhs = Lit wl /\
              FLOOKUP env u = SOME wu ==> wu = wl) /\
           (!u wu wl. rhs = Var u /\ lhs = Lit wl /\
              FLOOKUP env u = SOME wu ==> wu = wl) /\
           (!u1 u2 w1 w2. lhs = Var u1 /\ rhs = Var u2 /\
              FLOOKUP env u1 = SOME w1 /\ FLOOKUP env u2 = SOME w2 ==>
              w1 = w2)) /\
    ((dinst.inst_opcode = LT \/ dinst.inst_opcode = GT \/
      dinst.inst_opcode = SLT \/ dinst.inst_opcode = SGT) ==>
       !lhs rhs. dinst.inst_operands = [lhs; rhs] ==>
         !w. FLOOKUP env v = SOME w ==>
           (!u wl wu. lhs = Var u /\ rhs = Lit wl /\
              FLOOKUP env u = SOME wu ==>
              ((w <> 0w) =
                (if dinst.inst_opcode = LT then w2n wu < w2n wl
                 else if dinst.inst_opcode = GT then w2n wu > w2n wl
                 else if dinst.inst_opcode = SLT then w2i wu < w2i wl
                 else w2i wu > w2i wl))) /\
           (!u wl wu. rhs = Var u /\ lhs = Lit wl /\
              FLOOKUP env u = SOME wu ==>
              ((w <> 0w) =
                (if dinst.inst_opcode = LT then w2n wl < w2n wu
                 else if dinst.inst_opcode = GT then w2n wl > w2n wu
                 else if dinst.inst_opcode = SLT then w2i wl < w2i wu
                 else w2i wl > w2i wu))))
End

(* Everything the DFG says about entry v (defined by dinst) in env:
   the dfg_ext_sound clauses for that one entry (dfg_ext_sound_entries). *)
Definition dfg_entry_sound_def:
  dfg_entry_sound env v dinst <=>
    dfg_entry_base_sound env v dinst /\
    ((dinst.inst_opcode = ADD \/ dinst.inst_opcode = SUB) ==>
       !op1 op2. dinst.inst_operands = [op1; op2] /\
         (!lbl. op1 <> Label lbl) /\ (!lbl. op2 <> Label lbl) ==>
         ?w1 w2.
           eval_op_env op1 env = SOME w1 /\
           eval_op_env op2 env = SOME w2 /\
           FLOOKUP env v = SOME (if dinst.inst_opcode = ADD
                                 then word_add w1 w2 else word_sub w1 w2)) /\
    ((dinst.inst_opcode = LT \/ dinst.inst_opcode = GT) ==>
       !op1 op2. dinst.inst_operands = [op1; op2] /\
         (!lbl. op1 <> Label lbl) /\ (!lbl. op2 <> Label lbl) ==>
         ?w1 w2.
           eval_op_env op1 env = SOME w1 /\
           eval_op_env op2 env = SOME w2 /\
           FLOOKUP env v = SOME (bool_to_word
             (if dinst.inst_opcode = LT
              then w2n w1 < w2n w2 else w2n w1 > w2n w2)))
End

(* Pointwise DFG soundness for the entries defined at positions < idx of
   bb. Unlike dfg_sound, it is preserved by every single step: an entry
   defined later in a loop body may be stale until it is re-executed. *)
Definition dfg_prefix_sound_def:
  dfg_prefix_sound dfg bb env idx <=>
    !v dinst k.
      dfg_get_def dfg v = SOME dinst /\
      k < idx /\ k < LENGTH bb.bb_instructions /\
      EL k bb.bb_instructions = dinst /\
      v IN FDOM env ==>
      dfg_entry_sound env v dinst
End
