(*
 * Facts about an IR function's instruction list fn_insts: membership via
 * blocks, and uniqueness of instructions and blocks under
 * fn_inst_ids_distinct.
 *)

Theory venomFnInstsProofs
Ancestors
  venomInst venomWf list

Theorem mem_fn_insts_blocks:
  !bbs bb inst. MEM bb bbs /\ MEM inst bb.bb_instructions ==>
    MEM inst (fn_insts_blocks bbs)
Proof
  Induct >> rw[fn_insts_blocks_def] >> metis_tac[]
QED

Theorem mem_fn_insts_blocks_rev:
  !bbs inst. MEM inst (fn_insts_blocks bbs) ==>
    ?bb. MEM bb bbs /\ MEM inst bb.bb_instructions
Proof
  Induct >> rw[fn_insts_blocks_def] >> metis_tac[]
QED

Theorem MEM_fn_insts:
  !fn inst bb.
    MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions ==>
    MEM inst (fn_insts fn)
Proof
  metis_tac[fn_insts_def, mem_fn_insts_blocks]
QED

Theorem fn_insts_mem_block:
  !fn inst. MEM inst (fn_insts fn) ==>
    ?bb. MEM bb fn.fn_blocks /\ MEM inst bb.bb_instructions
Proof
  metis_tac[fn_insts_def, mem_fn_insts_blocks_rev]
QED

Theorem fn_insts_blocks_map_id:
  !bbs. MAP (\i. i.inst_id) (fn_insts_blocks bbs) =
    FLAT (MAP (\bb. MAP (\i. i.inst_id) bb.bb_instructions) bbs)
Proof
  Induct >> rw[fn_insts_blocks_def, MAP_APPEND]
QED

(* Same inst_id in fn_insts => same instruction *)
Theorem fn_insts_id_unique:
  !fn i1 i2. fn_inst_ids_distinct fn /\
    MEM i1 (fn_insts fn) /\ MEM i2 (fn_insts fn) /\
    i1.inst_id = i2.inst_id ==> i1 = i2
Proof
  rpt strip_tac >>
  `ALL_DISTINCT (MAP (\i. i.inst_id) (fn_insts_blocks fn.fn_blocks))`
    by fs[fn_inst_ids_distinct_def, GSYM fn_insts_blocks_map_id] >>
  fs[fn_insts_def] >> gvs[MEM_EL] >>
  `n < LENGTH (MAP (\i. i.inst_id) (fn_insts_blocks fn.fn_blocks)) /\
   n' < LENGTH (MAP (\i. i.inst_id) (fn_insts_blocks fn.fn_blocks))` by simp[] >>
  `EL n (MAP (\i. i.inst_id) (fn_insts_blocks fn.fn_blocks)) =
   EL n' (MAP (\i. i.inst_id) (fn_insts_blocks fn.fn_blocks))` by gvs[EL_MAP] >>
  `n = n'` by metis_tac[ALL_DISTINCT_EL_IMP] >> gvs[]
QED

Theorem all_distinct_flat_map_unique:
  !(l:'a list) (f:'a -> 'b list) a b v.
    ALL_DISTINCT (FLAT (MAP f l)) /\ MEM a l /\ MEM b l /\
    MEM v (f a) /\ MEM v (f b) ==> a = b
Proof
  Induct >> simp[] >> rpt gen_tac >> strip_tac >>
  gvs[ALL_DISTINCT_APPEND, MEM_FLAT, MEM_MAP] >>
  metis_tac[]
QED

(* Outputs distinct across all blocks are distinct within each block. *)
Theorem ssa_block_outputs_all_distinct:
  !bbs bb. ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) (fn_insts_blocks bbs)))
           /\ MEM bb bbs ==>
    ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions))
Proof
  Induct >> simp[fn_insts_blocks_def] >> rpt strip_tac >>
  gvs[MAP_APPEND, FLAT_APPEND, ALL_DISTINCT_APPEND]
QED

(* Distinct positions of l have disjoint images under f. *)
Theorem all_distinct_flat_map_el_disjoint:
  !(l:'a list) (f:'a -> 'b list) i j v.
    ALL_DISTINCT (FLAT (MAP f l)) /\
    i < LENGTH l /\ j < LENGTH l /\ i <> j /\
    MEM v (f (EL i l)) ==> ~MEM v (f (EL j l))
Proof
  Induct >> simp[] >> rpt strip_tac >>
  gvs[ALL_DISTINCT_APPEND] >>
  Cases_on `i` >> Cases_on `j` >> gvs[] >>
  gvs[MEM_FLAT, MEM_MAP] >> metis_tac[EL_MEM]
QED

(* In SSA form, different instructions in the same block produce disjoint
   output variables. *)
Theorem ssa_no_output_overlap_inst:
  !fn bb k idx y.
    ssa_form fn /\ MEM bb fn.fn_blocks /\
    k < LENGTH bb.bb_instructions /\ idx < LENGTH bb.bb_instructions /\
    k <> idx /\
    MEM y (EL k bb.bb_instructions).inst_outputs ==>
    ~MEM y (EL idx bb.bb_instructions).inst_outputs
Proof
  rpt strip_tac >>
  `ALL_DISTINCT (FLAT (MAP (\i. i.inst_outputs) bb.bb_instructions))` by
    (irule ssa_block_outputs_all_distinct >>
     fs[ssa_form_def, fn_insts_def] >> metis_tac[]) >>
  metis_tac[all_distinct_flat_map_el_disjoint]
QED

(* An instruction lies in at most one block. *)
Theorem inst_in_unique_block:
  !fn bb1 bb2 inst.
    fn_inst_ids_distinct fn /\
    MEM bb1 fn.fn_blocks /\ MEM bb2 fn.fn_blocks /\
    MEM inst bb1.bb_instructions /\ MEM inst bb2.bb_instructions ==>
    bb1 = bb2
Proof
  rw[fn_inst_ids_distinct_def] >>
  qspecl_then [`fn.fn_blocks`, `\bb. MAP (\i. i.inst_id) bb.bb_instructions`,
               `bb1`, `bb2`, `inst.inst_id`] mp_tac all_distinct_flat_map_unique >>
  simp[MEM_MAP] >> metis_tac[]
QED

(* fn_insts_blocks is FLAT (MAP bb_instructions) *)
Theorem fn_insts_blocks_flat:
  !l. fn_insts_blocks l = FLAT (MAP (\bb. bb.bb_instructions) l)
Proof
  Induct >> simp[fn_insts_blocks_def]
QED
