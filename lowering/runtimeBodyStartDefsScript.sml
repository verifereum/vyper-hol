(* Where the actual runtime compilation reaches a selected external
   package's argument registration.  The runtime entry proof and the
   shadow placement of the same body both start from this one compile
   state, so the two can be paired. *)
Theory runtimeBodyStartDefs
Ancestors
  compileVyper moduleLowering

(* st is the compile state right after the entry checks of package
   (lbl,...,rt), on the Linear dispatch path from the initial runtime
   compile state.  The first package with label lbl is the selected one,
   so st is unique. *)
Definition runtime_selected_body_start_def:
  runtime_selected_body_start tops rpolicy
      (lbl,ce,args,mincd,pay,nr,key,ut,iv,body,rt) st <=>
    ?exts ints fb ctor pre post fallback_lbl label_st dispatch_st opened
     checks.
      classify_functions tops = (exts,ints,fb,ctor) /\
      MAP (set_external_package_target rpolicy.rpol_target o
           package_external_fn tops T (K global_nonreentrant_slot)) exts =
        pre ++ (lbl,ce,args,mincd,pay,nr,key,ut,iv,body,rt) :: post /\
      ~MEM lbl (MAP FST pre) /\
      fresh_label "fallback" (initial_compile_state "__entry") =
        (fallback_lbl,label_st) /\
      compile_selector_dispatch_linear
        (MAP (\(sel,lbl,z). (sel,lbl))
           (build_selectors (type_env tops) exts))
        fallback_lbl label_st = ((),dispatch_st) /\
      compile_external_fn_bodies pre dispatch_st = ((),opened) /\
      new_block lbl opened = (opened.cs_current_bb,checks) /\
      compile_entry_checks mincd pay checks = ((),st)
End
