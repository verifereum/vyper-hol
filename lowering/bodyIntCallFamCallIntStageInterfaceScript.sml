(* Consumer interface probes, not a staging execution theorem. *)
Theory bodyIntCallFamCallIntStageInterface
Ancestors
  bodyIntCallFamCallIntForcingTransport bodyIntCallFamCallIntStageAdapters
  bodyIntCallFamCallIntFlags placeMemoryStaging abiCallerAllocation
  bodyIntCallJointContract

(* ML abbreviations only.  start is the start of the ENTIRE staging list,
   not the start of the most recent allocation or forcing fragment. *)
val completed = ``\cx start current ty flag v op s.
  ?tv w. evaluate_type (get_tenv cx) ty = SOME tv /\
    eval_operand op s = SOME w /\
    (!x. op = Var x ==> not_fresh_at current x) /\
    (if flag then is_word_type ty /\ w = typed_val_to_w256 tv v
     else val_in_memory tv v (w2n w) s.vs_memory /\
       ?aid len. FLOOKUP s.vs_allocas aid = SOME (w2n w,len) /\
         start.cs_next_id <= aid /\ aid < current.cs_next_id /\
         type_memory_size tv <= len /\
         w2n w + len <= s.vs_alloca_next /\
         w2n w + len < dimword (:256))``;

val completed_prefix = ``\cx start current tys flags values ops s.
  LENGTH flags = LENGTH tys /\ LENGTH values = LENGTH tys /\
  LENGTH ops = LENGTH tys /\
  !i. i < LENGTH tys ==>
    ^completed cx start current (EL i tys) (EL i flags)
      (EL i values) (EL i ops) s``;

Theorem intcall_completed_empty:
  ^completed_prefix cx start current [] [] [] [] s
Proof
  simp[]
QED

(* No wordness is inferred from vv_holds here.  Calling convention supplies
   wordness of ty separately (intcall_argument_flags). *)
Theorem intcall_completed_stack_singleton:
  evaluate_type (get_tenv cx) ty = SOME tv /\ is_word_type ty /\
  eval_operand op s = SOME (typed_val_to_w256 tv v) /\
  (!x. op = Var x ==> not_fresh_at current x) ==>
  ^completed_prefix cx start current [ty] [T] [v] [op] s
Proof
  simp[] >> strip_tac >> qexists `tv` >> simp[]
QED

(* Allocation supplies len=MAX 32 size, not len=size.  alloca_inv gives
   the non-strict frontier bound; the allocator gives the strict word bound.
   Value representation is supplied at the SAME endpoint by the store. *)
Theorem intcall_completed_memory_singleton:
  evaluate_type (get_tenv cx) ty = SOME tv /\
  eval_operand op s = SOME w /\
  (!x. op = Var x ==> not_fresh_at current x) /\
  val_in_memory tv v (w2n w) s.vs_memory /\
  FLOOKUP s.vs_allocas aid = SOME (w2n w,MAX 32 (type_memory_size tv)) /\
  alloca_inv s /\ start.cs_next_id <= aid /\ aid < current.cs_next_id /\
  w2n w + MAX 32 (type_memory_size tv) < dimword (:256) ==>
  ^completed_prefix cx start current [ty] [F] [v] [op] s
Proof
  simp[] >> strip_tac >> qexistsl [`aid`, `MAX 32 (type_memory_size tv)`] >>
  simp[arithmeticTheory.ADD_COMM] >> irule abi_caller_allocation_end >>
  simp[] >> qexistsl [`MAX 32 (type_memory_size tv)`, `aid`, `w2n w`] >> simp[]
QED
