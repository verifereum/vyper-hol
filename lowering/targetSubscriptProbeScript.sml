(* Relation-level probes only: not a counterexample to target_case. *)
Theory targetSubscriptProbe
Ancestors
  compileEnv vyperStoragePlaceRegion vyperStorageLayoutSafety vfmState
  words finite_map combin vyperValue targetSubscriptSim

Theorem nested_capacity_probe:
  storage_subregion
    (ArrayTV (ArrayTV (BaseTV BoolT) (Dynamic 1)) (Dynamic 1))
    [ValueSubscript (IntV 0)] 1
    (ArrayTV (BaseTV BoolT) (Dynamic 1))
Proof
  EVAL_TAC >> simp[]
QED

(* Conditional on a declared isolated region. Inhabitation of a full context
   and reachability after an actual index are separate obligations. *)
Theorem nested_dead_header_discrepancy_probe:
  !cx mid name subs st.
    declared_storage_region cx mid name subs =
      SOME (F,0w,ArrayTV (ArrayTV (BaseTV BoolT) (Dynamic 1)) (Dynamic 1)) /\
    (!mid' name' subs' slot' tv'.
      declared_storage_region cx mid' name' subs' = SOME (F,slot',tv') /\
      (slot',tv') <>
        (0w,ArrayTV (ArrayTV (BaseTV BoolT) (Dynamic 1)) (Dynamic 1)) ==>
      ranges_disjoint 0 3 (w2n slot') (type_slot_size tv')) /\
    lookup_storage 0w st = 0w /\ lookup_storage 1w st = 0w ==>
    storage_agree (storage_dead cx F st) st (update_storage 1w 1w st) /\
    lookup_storage 0w (update_storage 1w 1w st) = 0w /\
    lookup_storage 1w st <> lookup_storage 1w (update_storage 1w 1w st)
Proof
  rpt strip_tac
  >- (simp[storage_agree_def] >> rpt strip_tac >>
      Cases_on `k = 1w`
      >- (gvs[] >>
          `storage_dead cx F st 1 b` by
            (pure_rewrite_tac[storage_dead_def] >>
             qexistsl [`mid`,`name`,`subs`,`0w`,
               `ArrayTV (ArrayTV (BaseTV BoolT) (Dynamic 1)) (Dynamic 1)`] >>
             simp[type_slot_size_def, dead_bytes_def, dimword_def,
                  fcpLib.INDEX_CONV ``dimindex (:256)``] >>
             rpt strip_tac >> first_x_assum irule >> simp[] >>
             goal_assum (drule_at Any)) >>
          gvs[]) >>
      simp[lookup_storage_def, update_storage_def, APPLY_UPDATE_THM])
  >- gvs[lookup_storage_def, update_storage_def, APPLY_UPDATE_THM]
  >> gvs[lookup_storage_def, update_storage_def, APPLY_UPDATE_THM]
QED

(* Captured child selection consults only the child, not the parent length. *)
Theorem captured_child_extension_probe:
  !cx es.
    lookup_storage 1w (get_storage cx es F) = 0w ==>
    extend_place cx
      (PlaceR (StoragePlace F 1w (ArrayTV (BaseTV BoolT) (Dynamic 1))))
      (ValueSubscript (IntV 0)) es =
    (INR (Error (RuntimeError "array dynamic length oob")),es)
Proof
  simp[extend_place_storage_array_index, word_add_n2w]
QED

Theorem captured_child_extension_nonempty_probe:
  !cx es.
    lookup_storage 1w (get_storage cx es F) = 1w ==>
    extend_place cx
      (PlaceR (StoragePlace F 1w (ArrayTV (BaseTV BoolT) (Dynamic 1))))
      (ValueSubscript (IntV 0)) es =
    (INL (PlaceR (StoragePlace F 2w (BaseTV BoolT))),es)
Proof
  simp[extend_place_storage_array_index, word_add_n2w]
QED

(* Audit candidate (NOT a verified theorem counterexample):
   nocalls = F;
   bt = SubscriptTarget (TopLevelNameTarget (NONE,"outer"))
          (Literal (BaseT (UintT 256)) (IntL 0));
   e = Call (BaseT (UintT 256)) (IntCall (NONE,"shrink")) [] NONE.
   Declare outer: DynArray[DynArray[bool,1],1] at slot zero.
   Initial source and machine: parent header 1, child header 1, element 0.
   Source shrink pops outer, returns index zero; it retains child header 1.
   A candidate *abstract* machine callee additionally clears child header.
   Since the child is now dead, expr_post's storage relation need not forbid
   that extra write. ctx/func are arbitrary theorem parameters, not required
   to be the output of compiling this particular source callee. This is an
   avenue to investigate, NOT permission to assume expr_sim_case.

   Premise ledger still OPEN:
   - concrete cx (code, layout, typing, supported_program, call safety),
     cenv (tables and locals), env, ctx and func have not been constructed;
   - target_case bt and both universal judgments for e are unproved;
   - target_pre requires expr_sim_inv, hence storage_layout_safe,
     contract_storage_well_formed, oracle_storage_ok, IS_SOME outcomes,
     typed states/accounts/context/functions, and target_indices_pre;
   - compile_get_target_ptr, fn_has_code, fn_inst_ids_distinct,
     local_ptrs_reserved and an initial stmt_state_rel need witnesses;
   - actual eval_base_place and call execution, exact machine suffix and
     failure of frag_exec remain unproved.
   Checked reductions above: a saved child pointer consults its own current
   header, independent of parent length, and produces either a permitted
   runtime error or a successful place depending on that header.
   A plain correctly implemented pop changes only the parent header on both
   sides; it does NOT itself create the discrepancy. Thus C0.1 alone cannot
   establish reachability, even with a source shrink operation.
*)
Theorem internal_index_syntactically_nopop_probe:
  ~expr_has_pop
    (Call (BaseT (UintT 256)) (IntCall (NONE,"shrink")) [] NONE)
Proof
  EVAL_TAC
QED
