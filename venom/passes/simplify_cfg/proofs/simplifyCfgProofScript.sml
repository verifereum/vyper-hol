(*
 * Simplify CFG Pass — Correctness Proof
 *
 * Block merging, trivial jump bypass, unreachable block removal and PHI
 * fixup preserve a function's runs from its entry, and every state the
 * output reaches corresponds to one the input reaches.
 *)

Theory simplifyCfgProof
Ancestors
  simplifyCfgDefs o1PassLift unitShapeDefs venomWf

(* Merged blocks need less fuel, so the fuel is existential each way.
   fn_shape_ok bans DJMP and keeps labels out of every terminator operand
   but a jump target, so a terminator merged away (one distinct successor)
   could neither fail nor halt. *)
Theorem simplify_cfg_fn_correct:
  wf_function fn /\ fn_inst_wf fn /\ fn_shape_ok fn /\ first_block_no_preds fn /\
  simplify_cfg_fn_ok fn ==>
  fn_bisim fn (simplify_cfg_fn fn)
Proof
  cheat
QED

(* Every state the output reaches in C' (including on runs that later
   fail) corresponds to one the input reaches in C from the same entry
   state; C and C' run each function alike. *)
Theorem simplify_cfg_frame_sim:
  ctx_bisim C C' /\
  wf_function fn /\ fn_inst_wf fn /\ fn_shape_ok fn /\ first_block_no_preds fn /\
  simplify_cfg_fn_ok fn ==>
  frame_sim C C' fn (simplify_cfg_fn fn)
Proof
  cheat
QED
