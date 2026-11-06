# TASK: seq1298-b2stor — prove place_store_value_storage_run

## Meta
Status: planned
Priority: P1
Created: 2026-11-05
Location: lowering/ (theory placeStoreStorage, file lowering/placeStoreStorageScript.sml)

## Theorem Statement (FROZEN)

```sml
Theorem place_store_value_storage_run:
  !ctx func cenv cx env ee ff s p w loc dst_op op src_loc dty sty stv v sa sb.
    (loc = LocStorage \/ loc = LocTransient) /\
    (!et n. dty <> ArrayT et (Dynamic n)) /\
    compile_assign_value cenv dst_op loc op (is_word_type dty) src_loc dty sty
      (case dty of
         ArrayT et (Dynamic _) =>
           SOME ((type_memory_bytes cenv et + 31) DIV 32,
                 type_memory_bytes cenv et)
       | _ => NONE)
      (type_memory_bytes cenv dty) sa = ((), sb) /\
    eval_operand dst_op s = SOME w /\
    place_ptr_rel cenv cx s (PlaceR p) w (SOME loc) (Type dty) /\
    (!x. dst_op = Var x ==> not_fresh_at sa x) /\
    (!x. op = Var x ==> not_fresh_at sa x) /\
    type_widens_to (get_tenv cx) sty dty /\
    evaluate_type (get_tenv cx) sty = SOME stv /\ value_has_type stv v /\
    expr_val_rel cx sty v op s /\ cenv.ce_target CapMcopy /\
    (loc = LocMemory /\ src_loc <> SOME LocMemory /\ ~is_word_type dty /\
     ~is_bytestring_type dty /\ dty <> sty ==>
     !sw dtv. eval_operand op s = SOME sw /\
              evaluate_type (get_tenv cx) dty = SOME dtv ==>
              type_memory_size stv = 0 \/
              w2n sw + type_memory_size stv <= w2n w \/
              w2n w + type_memory_size dtv <= w2n sw \/
              sw = w /\ stv = dtv) /\
    expr_sim_inv cenv cx env ee /\
    acyclic_struct_metadata cenv.ce_struct_fields /\
    local_ptrs_reserved cenv sa /\ storage_place_region cx p /\
    (!id path entry t0.
       p = MemoryPlace id path /\ lookup_scopes id ee.scopes = SOME entry /\
       cenv.ce_var_type id = SOME t0 ==>
       evaluate_type (get_tenv cx) t0 = SOME entry.type) /\
    (~is_word_type sty ==>
     !sw. eval_operand op s = SOME sw ==>
          w2n sw + type_memory_size stv <= s.vs_alloca_next /\
          !aid b sz. FLOOKUP s.vs_allocas aid = SOME (b,sz) /\
                     sa.cs_next_id <= aid ==>
                     w2n sw + type_memory_size stv <= b \/ b + sz <= w2n sw) /\
    (loc = LocMemory ==>
     !dtv. evaluate_type (get_tenv cx) dty = SOME dtv ==>
           w2n w + type_memory_size dtv + 64 < dimword (:256)) /\
    (!dtv. evaluate_type (get_tenv cx) dty = SOME dtv ==>
           0 < type_slot_size dtv) /\
    (dty <> sty /\ ~(is_bytestring_type dty /\ is_bytestring_type sty) ==>
     type_alloc_ok cenv dty) /\
    stmt_state_rel ctx func cenv cx ee s /\
    write_place cx p v ee = (INL (), ff) /\
    fn_has_code sa sb func /\ fn_inst_ids_distinct func /\
    ~s.vs_halted /\ s.vs_current_bb = sa.cs_current_bb /\
    s.vs_inst_idx = LENGTH sa.cs_current_insts ==>
    ?t. gas_marked_path F ctx func s 0 (OK t) /\
        stmt_state_rel ctx func cenv cx ff t /\
        (!x. not_fresh_at sa x ==> lookup_var x t = lookup_var x s) /\
        (!aid b. FLOOKUP s.vs_allocas aid = SOME b ==>
                 FLOOKUP t.vs_allocas aid = SOME b) /\
        ~t.vs_halted /\ t.vs_current_bb = sb.cs_current_bb /\
        t.vs_inst_idx = LENGTH sb.cs_current_insts
```

**Do not modify this statement.** Prove it as-is, or produce a counterexample.

## Completion Criteria

1. `holbuild -j4 build placeStoreStorageTheory` passes.
2. The proof of `place_store_value_storage_run` in `lowering/placeStoreStorageScript.sml` contains no `cheat`, and no helper lemma you add contains one.
3. No duplicate or near-duplicate lemmas — each helper exists once in its most general form.

Cheats reported by the build in ancestor theories are expected: many ancestors are admitted (proofs replaced by cheat) in this checkout because they are proved on other branches. Their statements are final; use them freely.

## Build

```
holbuild -j4 build placeStoreStorageTheory
```

## Background

compile_assign_value when the place is a storage or transient slot and the place type is not a DynArray: the value (a word, or an aggregate staged in memory) is copied word by word to the slots, simulating the source's write_place to a StoragePlace.

This is one piece of the vyper-hol compiler-correctness proof (Vyper source semantics vs. the Venom IR lowering). Other theorems in `lowering/placeStoreStorageScript.sml` and placeStore*Script.sml are proved elsewhere or deliberately admitted; leave them as they are.

## Domain Constraints

- Change only `lowering/placeStoreStorageScript.sml`'s proof of the theorem above, and add helper lemmas there or in NEW theory files under `lowering/` (add them to this theory's Ancestors).
- Do not edit any other existing file. In particular never edit: semantics/, frontend/, lowering/defs/, venom/defs/, venom/compiler/, lowering/supported/, bodySimScript.sml, exprSimHyps*, *Main*, nor any existing theorem statement or definition.
- No new definitions unless strictly needed for a helper; never redefine an existing concept. No axioms, no new `cheat`.
- Don't wrap search tactics (metis_tac, simp, gvs, fs, rw, decide_tac, ...) in TRY or ORELSE.
- No tactic-timeout or step-limit overrides; build at the default limits.
- Existing lemmas that are `cheat` in this checkout are admitted: use them as-is, don't reprove them.

## Available Resources

| Resource | Location | Description |
|----------|----------|-------------|
| lowering/placeStoreScript.sml | the store lemmas' shared shape; place_store_value_run dispatches to the three location lemmas |
| lowering/loweringPostsScript.sml | place_ptr_rel, target_post, expr_post, vv_post, vv_holds, vv_at, expr_val_rel |
| lowering/stmtSimDefsScript.sml | stmt_state_rel, stmt_frag, stmt_framed_frag |
| lowering/defs/compileEnvScript.sml | state_rel, local_ptrs_rel, local_ptrs_reserved, storage relation |
| lowering/exprSimHypsDefsScript.sml | expr_sim_inv, expr_body_pre |
| lowering/fragGasModeScript.sml | gas_marked_path, gas_marked_exec, gas_admissible |
| lowering/defs/stmtLoweringScript.sml, lowering/defs/exprLoweringScript.sml | compile_assign_value, compile_store_memory, compile_store_at_loc, unwrap_value, the Assign lowering |
| lowering/valueCopyScript.sml | compile_store_memory_run, stage_store_run |
| lowering/typedMemoryCopyScript.sml | compile_store_memory_typed_run (~3534) |
| lowering/stmtSimAssignMemScript.sml | local_memory_store_run(_framed), local_header_store_state, compile_assign_local_empty_stmt_frag: a whole local stored in memory |
| lowering/stmtSimAssignStorageScript.sml, lowering/stmtSimAssignStorageCopyScript.sml, lowering/storageCopyLiveScript.sml, lowering/storageCopyGasPathScript.sml | storing to storage variables (word and aggregate) |
| lowering/stmtSimAssignAttrScript.sml, lowering/stmtSimAssignAttrStorageScript.sml | struct-field Assign: a store at an offset inside a local / storage variable, and counted composition |
| lowering/stmtSimAugAssignScript.sml, lowering/stmtSimAugAssignStorageScript.sml | word stores to locals and storage |
| semantics/prop/vyperStoragePlaceProvenanceScript.sml | storage_place_region, eval_target_place_region |
| semantics/prop/vyperPlaceWriteSoundnessScript.sml, semantics/prop/vyperTypeStatePreservationScript.sml | write_place preservation facts |
| semantics/vyperStateScript.sml, semantics/vyperInterpreterScript.sml | write_place, replace_memory_entry, write_storage_slot, eval_stmt, eval_target_place |

## Notes

Intuition, if any, is in SML comments next to the statement in `lowering/placeStoreStorageScript.sml`.
