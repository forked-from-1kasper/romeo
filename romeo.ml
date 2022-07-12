open Ident
open Term

type proof =
  | PVar   of ident
  | Absurd of proof                                          (* ⊥ ⊢ A *)
  | Conj   of proof * proof                           (* A, B ⊢ A ∧ B *)
  | Fst    of proof                                      (* A ∧ B ⊢ A *)
  | Snd    of proof                                      (* A ∧ B ⊢ B *)
  | Left   of proof                                      (* A ⊢ A ∨ B *)
  | Right  of proof                                      (* B ⊢ A ∨ B *)
  | Disj   of proof * proof               (* A → C, B → C ⊢ A ∨ B → C *)
  | Lam    of ident * proof                        (* (A ⊢ B) ⊢ A → B *)
  | Mp     of proof * proof                           (* A, A → B ⊢ B *)
  | Exis   of term * proof                          (* P x ⊢ ∃ x, P x *)
  | Refl   of term                                           (* a = a *)
  | Symm   of proof                                  (* a = b ⊢ b = a *)
  | Trans  of proof * proof                   (* a = b, b = c ⊢ a = c *)
  | Subst  of ident * prop * proof * proof      (* a = b, P(a) ⊢ P(b) *)
  | Choice of term * proof              (* H : ∃ x, P x ⊢ P(ε x, P x) *)

let () = Printf.printf "Hello, World!\n"