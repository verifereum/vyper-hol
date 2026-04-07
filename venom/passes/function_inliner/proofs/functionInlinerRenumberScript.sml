(*
 * Function Inliner — Renumber Preservation Lemmas
 *
 * renumber_fn_inst_ids only changes inst_id fields within instructions.
 *
 * Strategy: prove MAP-based preservation at FOLDL level (trivialites),
 * then derive all exported properties as corollaries.
 *
 * Key insight: when unfolding renumber_fn_inst_ids_def, DON'T use LET_THM.
 * Instead use pairarg_tac or LAMBDA_PROD to keep lambda forms consistent.
 *)

Theory functionInlinerRenumber
Ancestors
  cfgTransform venomInst

open listTheory rich_listTheory pairTheory

(* ===== Block-level core ===== *)

Triviality renumber_block_bb_label:
  !n bb. (SND (renumber_block_inst_ids n bb)).bb_label = bb.bb_label
Proof
  rw[renumber_block_inst_ids_def, LET_THM] >>
  pairarg_tac >> gvs[]
QED

Triviality foldl_renumber_map:
  !insts n acc.
    MAP (\i. (i.inst_opcode, i.inst_operands, i.inst_outputs))
        (SND (FOLDL (\(id,acc') inst. (id + 1, acc' ++ [inst with inst_id := id]))
                    (n, acc) insts)) =
    MAP (\i. (i.inst_opcode, i.inst_operands, i.inst_outputs)) acc ++
    MAP (\i. (i.inst_opcode, i.inst_operands, i.inst_outputs)) insts
Proof
  Induct >> rw[] >>
  first_x_assum (qspecl_then [`n + 1`, `acc ++ [h with inst_id := n]`] mp_tac) >>
  rw[MAP_APPEND]
QED

Triviality renumber_block_map:
  !n bb.
    MAP (\i. (i.inst_opcode, i.inst_operands, i.inst_outputs))
        (SND (renumber_block_inst_ids n bb)).bb_instructions =
    MAP (\i. (i.inst_opcode, i.inst_operands, i.inst_outputs))
        bb.bb_instructions
Proof
  rw[renumber_block_inst_ids_def, LET_THM] >>
  pairarg_tac >> gvs[] >>
  qspecl_then [`bb.bb_instructions`, `n`, `[]`] mp_tac foldl_renumber_map >>
  rw[]
QED

(* ===== Function-level: induction on fn_blocks ===== *)

(* All function-level FOLDL lemmas proved by induction with pairarg_tac
   to avoid LET_THM / beta mismatch issues.
   The FOLDL body is: \(n,acc) bb. (\(n',bb'). (n', acc ++ [bb']))
                                      (renumber_block_inst_ids n bb)
   pairarg_tac decomposes renumber_block_inst_ids n bb = (n', bb'). *)

Triviality foldl_fn_map_label:
  !bbs n acc.
    MAP (\bb. bb.bb_label)
      (SND (FOLDL (\(n,acc) bb. (\(n',bb'). (n', acc ++ [bb']))
                                  (renumber_block_inst_ids n bb))
                  (n, acc) bbs)) =
    MAP (\bb. bb.bb_label) acc ++ MAP (\bb. bb.bb_label) bbs
Proof
  Induct >> rw[] >>
  pairarg_tac >> gvs[] >>
  SUBGOAL_THEN ``bb'.bb_label = h.bb_label`` ASSUME_TAC
  >- metis_tac[renumber_block_bb_label, SND, PAIR] >>
  first_x_assum (qspecl_then [`n'`, `acc ++ [bb']`] mp_tac) >>
  rw[MAP_APPEND]
QED

Triviality foldl_fn_flat_insts:
  !bbs n acc.
    MAP (\i. (i.inst_opcode, i.inst_operands, i.inst_outputs))
        (FLAT (MAP (\bb. bb.bb_instructions)
               (SND (FOLDL (\(n,acc) bb. (\(n',bb'). (n', acc ++ [bb']))
                                           (renumber_block_inst_ids n bb))
                           (n, acc) bbs)))) =
    MAP (\i. (i.inst_opcode, i.inst_operands, i.inst_outputs))
        (FLAT (MAP (\bb. bb.bb_instructions) acc)) ++
    MAP (\i. (i.inst_opcode, i.inst_operands, i.inst_outputs))
        (FLAT (MAP (\bb. bb.bb_instructions) bbs))
Proof
  Induct >> rw[] >>
  pairarg_tac >> gvs[] >>
  SUBGOAL_THEN ``MAP (\i. (i.inst_opcode,i.inst_operands,i.inst_outputs))
                     bb'.bb_instructions =
                 MAP (\i. (i.inst_opcode,i.inst_operands,i.inst_outputs))
                     h.bb_instructions`` ASSUME_TAC
  >- metis_tac[renumber_block_map, SND, PAIR] >>
  first_x_assum (qspecl_then [`n'`, `acc ++ [bb']`] mp_tac) >>
  rw[MAP_APPEND, FLAT_APPEND, MAP_FLAT]
QED

Triviality foldl_fn_length:
  !bbs n acc.
    LENGTH (SND (FOLDL (\(n,acc) bb. (\(n',bb'). (n', acc ++ [bb']))
                                       (renumber_block_inst_ids n bb))
                       (n, acc) bbs)) =
    LENGTH acc + LENGTH bbs
Proof
  Induct >> rw[] >>
  pairarg_tac >> gvs[] >>
  first_x_assum (qspecl_then [`n'`, `acc ++ [bb']`] mp_tac) >>
  rw[]
QED

(* ===== EXPORTED THEOREMS ===== *)

Theorem renumber_fn_inst_ids_fn_name:
  !func. (renumber_fn_inst_ids func).fn_name = func.fn_name
Proof
  rw[renumber_fn_inst_ids_def, LET_THM] >>
  pairarg_tac >> gvs[]
QED

Theorem renumber_fn_inst_ids_fn_labels:
  !func. fn_labels (renumber_fn_inst_ids func) = fn_labels func
Proof
  rw[fn_labels_def, renumber_fn_inst_ids_def] >>
  pairarg_tac >> gvs[] >>
  qspecl_then [`func.fn_blocks`, `0`, `[]`] mp_tac foldl_fn_map_label >>
  rw[] >> metis_tac[PAIR, SND]
QED

Theorem renumber_fn_inst_ids_length:
  !func. LENGTH (renumber_fn_inst_ids func).fn_blocks = LENGTH func.fn_blocks
Proof
  rw[renumber_fn_inst_ids_def] >>
  pairarg_tac >> gvs[] >>
  qspecl_then [`func.fn_blocks`, `0`, `[]`] mp_tac foldl_fn_length >>
  rw[] >> metis_tac[PAIR, SND]
QED

Theorem renumber_fn_inst_ids_inst_proj:
  !func.
    MAP (\i. (i.inst_opcode, i.inst_operands, i.inst_outputs))
        (FLAT (MAP (\bb. bb.bb_instructions) (renumber_fn_inst_ids func).fn_blocks)) =
    MAP (\i. (i.inst_opcode, i.inst_operands, i.inst_outputs))
        (FLAT (MAP (\bb. bb.bb_instructions) func.fn_blocks))
Proof
  rw[renumber_fn_inst_ids_def] >>
  pairarg_tac >> gvs[] >>
  qspecl_then [`func.fn_blocks`, `0`, `[]`] mp_tac foldl_fn_flat_insts >>
  rw[] >> metis_tac[PAIR, SND]
QED

(* Block-level exports *)
Theorem renumber_block_inst_ids_bb_label:
  !n bb. (SND (renumber_block_inst_ids n bb)).bb_label = bb.bb_label
Proof
  rw[renumber_block_inst_ids_def, LET_THM] >>
  pairarg_tac >> gvs[]
QED

Triviality foldl_renumber_inst_length:
  !insts n acc.
    LENGTH (SND (FOLDL (\(id,acc') inst. (id + 1, acc' ++ [inst with inst_id := id]))
                       (n, acc) insts)) =
    LENGTH acc + LENGTH insts
Proof
  Induct >> rw[] >>
  first_x_assum (qspecl_then [`n + 1`, `acc ++ [h with inst_id := n]`] mp_tac) >>
  rw[]
QED

Theorem renumber_block_inst_ids_length:
  !n bb.
    LENGTH (SND (renumber_block_inst_ids n bb)).bb_instructions =
    LENGTH bb.bb_instructions
Proof
  rw[renumber_block_inst_ids_def, LET_THM] >>
  pairarg_tac >> gvs[] >>
  qspecl_then [`bb.bb_instructions`, `n`, `[]`] mp_tac foldl_renumber_inst_length >>
  rw[]
QED

Theorem renumber_block_inst_ids_map:
  !n bb.
    MAP (\i. (i.inst_opcode, i.inst_operands, i.inst_outputs))
        (SND (renumber_block_inst_ids n bb)).bb_instructions =
    MAP (\i. (i.inst_opcode, i.inst_operands, i.inst_outputs))
        bb.bb_instructions
Proof
  rw[renumber_block_inst_ids_def, LET_THM] >>
  pairarg_tac >> gvs[] >>
  qspecl_then [`bb.bb_instructions`, `n`, `[]`] mp_tac foldl_renumber_map >>
  rw[]
QED

(* ===== General list helpers ===== *)

(* If MAP f xs = MAP f ys and P factors through f, then FILTER P
   has the same length. Used for invoke_count preservation etc. *)
Theorem filter_length_map_proj:
  !xs (f:'a -> 'b) P ys.
    MAP f xs = MAP f ys /\
    (!x y. f x = f y ==> (P x <=> P y)) ==>
    LENGTH (FILTER P xs) = LENGTH (FILTER P ys)
Proof
  Induct
  >- (rw[] >> Cases_on `ys` >> fs[])
  >- (
    rpt gen_tac >> strip_tac >>
    Cases_on `ys` >> fs[] >>
    first_x_assum (qspecl_then [`f`, `P`, `t`] mp_tac) >>
    impl_tac >- rw[] >>
    Cases_on `P h` >> Cases_on `P h'`
    >> fs[] >> metis_tac[])
QED

(* Similarly for EVERY *)
Theorem every_map_proj:
  !xs (f:'a -> 'b) P ys.
    MAP f xs = MAP f ys /\
    (!x y. f x = f y ==> (P x <=> P y)) ==>
    (EVERY P xs <=> EVERY P ys)
Proof
  Induct
  >- (rw[] >> Cases_on `ys` >> fs[])
  >- (
    rpt gen_tac >> strip_tac >>
    Cases_on `ys` >> fs[] >>
    first_x_assum (qspecl_then [`f`, `P`, `t`] mp_tac) >>
    impl_tac >- rw[] >>
    metis_tac[])
QED

(* Renumber preserves any block-level EVERY predicate on instructions
   that factors through (opcode, operands, outputs). *)
Theorem renumber_fn_preserves_every_inst:
  !P fn.
    (!i1 i2. i1.inst_opcode = i2.inst_opcode /\
             i1.inst_operands = i2.inst_operands /\
             i1.inst_outputs = i2.inst_outputs ==> (P i1 <=> P i2)) ==>
    (EVERY (\bb. EVERY P bb.bb_instructions)
       (renumber_fn_inst_ids fn).fn_blocks <=>
     EVERY (\bb. EVERY P bb.bb_instructions) fn.fn_blocks)
Proof
  rpt strip_tac >>
  (* Convert block-level EVERY to flat-level EVERY *)
  `!bbs. EVERY (\bb. EVERY P bb.bb_instructions) bbs <=>
         EVERY P (FLAT (MAP (\bb. bb.bb_instructions) bbs))` by
    simp[EVERY_FLAT, EVERY_MAP] >>
  simp[] >>
  irule (INST_TYPE [beta |-> ``:opcode # operand list # string list``]
    every_map_proj) >>
  qexists_tac `\i. (i.inst_opcode, i.inst_operands, i.inst_outputs)` >>
  simp[renumber_fn_inst_ids_inst_proj] >>
  rpt gen_tac >> strip_tac >> gvs[] >> metis_tac[]
QED

val _ = export_theory();
