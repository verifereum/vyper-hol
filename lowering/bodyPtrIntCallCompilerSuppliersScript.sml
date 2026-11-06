Theory bodyPtrIntCallCompilerSuppliers
Ancestors bodyPtrIntCallPrologue compileVyper compileEnv intCallCallee list
Libs monadsyntax

(* Static metadata belongs to the packaged callee, not to an arbitrary
   runtime caller environment. *)
Theorem intcall_runtime_package_metadata:
  !tops use_trans nkeys immutables_len mut nr rr fname fargs dflts ret body
   lbl ce params has_rb is_nr nkey use_tr is_view is_ctor imm_len body' ret_type.
  package_internal_fn tops use_trans nkeys F immutables_len
    (mut,nr,rr,fname,fargs,dflts,ret,body) =
    (lbl,ce,params,has_rb,is_nr,nkey,use_tr,is_view,is_ctor,imm_len,
     body',ret_type) ==>
  ce.ce_imm_alloca = NONE /\ ~ce.ce_is_ctor /\ ~is_ctor /\
  imm_len = 0 /\ body' = body /\
  ret_type = (if ret = NoneT then NONE else SOME ret) /\
  params = ZIP (MAP FST fargs,
    compute_pass_via_stack (MAP SND fargs) ce.ce_returns_count) /\
  LENGTH params = LENGTH fargs /\
  has_rb = (ce.ce_returns_count = 0 /\ ret <> NoneT)
Proof
  simp[package_internal_fn_def, update_cenv_nonreentrant_def] >>
  strip_tac >> gvs[] >>
  simp[build_compile_env_imm_alloca, build_compile_env_returns_count,
       LENGTH_compute_pass_via_stack]
QED

(* Supplier ledger for intcall_runtime_prologue_stmt_entry_ptr.

   Static packaging:
   - intcall_runtime_package_metadata supplies ce_imm_alloca = NONE,
     runtime mode, user parameter length/layout, has_rb and ret_type.
   - compile_internal_function_entry_factorization and
     compile_internal_function_entry_no_reservation expose the prologue.
     intcall_prologue_factor exposes its three component equations.
   - package_internal_fn_prologue_code/ptrs provide reserved locals and
     prefix shape once the packaged function/prologue equations are known.
   - intcall_prologue_code_suppliers supplies non-INVOKE membership once
     fn_has_code for that prologue is supplied.

   Still required at the actual lookup boundary (not consequences of the
   package equation alone): a runtime source lookup -> packaged descriptor
   -> lookup_function equation retaining fn_has_code for the entry prefix,
   its entry lookup_block/isPREFIX and fn_inst_ids_distinct. Existing
   package_internal_blocks_metadata concerns metadata, not this witness.

   Dynamic preparation (C1.3.3): setup_callee; state_rel at the rebuilt
   environment with empty scopes; internal_immutable_regions;
   internal_args_rel; intcall_entry_memory/intcall_entry_return; src value
   footprints; lengths of actual args and PG; stack allocation headroom;
   fresh_vars_wrt and allocation IDs below the initial builder ID;
   stor_taint_ok. The package length equality alone does not prove these.

   Room/code validation: alloca_room_callee transports caller room only
   after fn_directly_calls, callee lookup and frontier equality are known.
   fmp_room and ~ctx_has_dalloca still need actual context suppliers.
   fn_allocs_ok gives source type sizes below 2**64, but translation to
   this ce and to stack/return allocation sums remains a consumer duty.
   Neither runtime mode nor S1's semantic result alone supplies ghost data.
*)
