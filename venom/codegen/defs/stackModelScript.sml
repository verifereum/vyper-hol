(*
 * Stack Model
 *
 * Upstream: vyperlang/vyper@e1dead045 (sunset GEP, #4895)
 * HOL4 formalization of Python's stack_model.py.
 * The stack is a list of operands: HD = bottom, LAST = TOS.
 * Distance from TOS: 0 = TOS, 1 = one below, etc.
 *
 * TOP-LEVEL:
 *   stack_push, stack_pop, stack_peek, stack_poke,
 *   stack_swap, stack_dup, stack_get_depth, stack_get_phi_depth
 *
 * Helper:
 *   stack_find — generic search from head of list, used by get_depth/get_phi_depth
 *)

Theory stackModel
Ancestors
  rich_list

(* =========================================================================
   Stack Operations
   ========================================================================= *)

(* Push: append to end (TOS = last element) *)
Definition stack_push_def:
  stack_push op stk = SNOC op stk
End

(* Pop n items from TOS *)
Definition stack_pop_def:
  stack_pop n stk = TAKE (LENGTH stk - n) stk
End

(* Peek at distance from TOS (0 = TOS) *)
Definition stack_peek_def:
  stack_peek dist stk =
    EL (LENGTH stk - 1 - dist) stk
End

(* Poke: update element at distance from TOS *)
Definition stack_poke_def:
  stack_poke dist op stk =
    LUPDATE op (LENGTH stk - 1 - dist) stk
End

(* Swap TOS with element at distance dist (dist > 0) *)
Definition stack_swap_def:
  stack_swap dist stk =
    let top_idx = LENGTH stk - 1 in
    let tgt_idx = LENGTH stk - 1 - dist in
    let top_val = EL top_idx stk in
    let tgt_val = EL tgt_idx stk in
    LUPDATE top_val tgt_idx (LUPDATE tgt_val top_idx stk)
End

(* Dup: copy element at distance to TOS *)
Definition stack_dup_def:
  stack_dup dist stk =
    SNOC (stack_peek dist stk) stk
End

(* =========================================================================
   Depth Search
   ========================================================================= *)

(* Find first matching operand from TOS, return distance.
   Searches reversed list (TOS first). Returns NONE if not found. *)
Definition stack_find_def:
  stack_find p [] = NONE ∧
  stack_find p (x :: xs) =
    if p x then SOME (0 : num)
    else case stack_find p xs of
      SOME d => SOME (d + 1)
    | NONE => NONE
End

(* Get depth (distance from TOS) of an operand.
   Python: get_depth returns 0 for TOS, -1 for one below, etc.
   HOL4: returns SOME dist or NONE, where 0 = TOS, 1 = one below.
   Searches REVERSE to scan from TOS first (matches Python's
   enumerate(reversed(...)) and returns first/shallowest match). *)
Definition stack_get_depth_def:
  stack_get_depth op stk = stack_find (λx. x = op) (REVERSE stk)
End

(* Get depth of first matching phi operand.
   Python: get_phi_depth iterates reversed stack.
   HOL4: returns SOME dist or NONE, 0 = TOS. *)
Definition stack_get_phi_depth_def:
  stack_get_phi_depth phis stk = stack_find (λx. MEM x phis) (REVERSE stk)
End
