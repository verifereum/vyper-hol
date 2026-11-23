(* Compatibility names for the selected ternary control transfers. *)
Theory entryCreateIfExp
Ancestors
  entryCreateIfExpAdmin

Theorem ifexp_admin_jump_scope = entryCreateIfExpAdminTheory.ifexp_admin_jump_scope;

Theorem ifexp_admin_jump_visit = entryCreateIfExpAdminTheory.ifexp_admin_jump_visit;

Theorem ifexp_selected_jnz_fetch = entryCreateIfExpAdminTheory.ifexp_selected_jnz_fetch;

Theorem ifexp_finish_scope = entryCreateIfExpAdminTheory.ifexp_finish_scope;
