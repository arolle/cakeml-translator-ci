open HolKernel boolLib bossLib Parse;
open listTheory rich_listTheory arithmeticTheory;

val _ = new_theory "listrev";

val LENGTH' = REWRITE_RULE[ADD1] LENGTH

(* specification of a reverse function f:
   elements of original list and f list are mirrored, i.e.
   an element at index            i         in  ls
       occurs at index (LENGTH ls - i - 1)  in  (f ls)
*)
Definition spec_rev_def:
  spec_rev f ⇔
    ∀ls i.
      i < LENGTH ls ⇒  EL i ls = EL (LENGTH ls - 1 - i) (f ls)
End

(* implementation of a function reversing lists *)
Definition rev_def:
    rev [] = []
  ∧ rev (h::t) = (rev t) ⧺ [h]
End

(* use logic to derive that length is invariant *)
Theorem rev_LENGTH:
  ∀ls. LENGTH (rev ls) = LENGTH ls
Proof
  Induct
  (* empty list *)
  >- (
    (* unfold definition *)
    PURE_REWRITE_TAC[rev_def]
    (* a = a  is always true*)
    >> REFL_TAC
  )
  (* unfold definition *)
  >> PURE_REWRITE_TAC[rev_def]
  (* LENGTH of appended lists is sum of their length *)
  >> PURE_REWRITE_TAC[LENGTH_APPEND]
  (* calculate length of cons, length of one-element list *)
  >> PURE_REWRITE_TAC[LENGTH',GSYM ONE,ADD]
  (* remove unnecessary quantifier *)
  >> PURE_REWRITE_TAC[FORALL_SIMP]
  (* rewrite with induction assumption *)
  >> PURE_ASM_REWRITE_TAC[]
  >> REFL_TAC
QED

(* implementation satisfies the specification *)
Theorem spec_rev_rev:
  spec_rev rev
Proof
  fs[spec_rev_def]
  >> Induct >> rw[rev_def]
  >> rename1 `EL i (h::ls)` >> Cases_on `i`
  >> fs[EL_APPEND1,EL_APPEND2,rev_LENGTH]
  >> ntac 2 (MK_COMB_TAC >> fs[])
QED

val unfolded = REWRITE_RULE[spec_rev_def] spec_rev_rev;
(*
  ⊢ ∀ls i. i < LENGTH ls ⇒ EL i ls = EL (LENGTH ls − 1 − i) (rev ls): thm
*)


(* another list-reverse implementation which is tail-recursive, i.e. with an accumulator *)

Definition qrev_acc_def:
    qrev_acc acc [] = acc
  ∧ qrev_acc acc (h::t) = qrev_acc (h::acc) t
End

Definition qrev_def:
  qrev = qrev_acc []
End

Theorem qrev_acc_append:
  !ls acc. qrev_acc acc ls = (qrev_acc [] ls) ⧺ acc
Proof
  Induct >- fs[qrev_acc_def]
  >> rpt strip_tac
  >> rewrite_tac[qrev_acc_def]
  >> pop_assum $ once_rewrite_tac o single
  >> once_rewrite_tac[CONS_APPEND]
  >> rewrite_tac[APPEND_NIL,APPEND_ASSOC]
QED

Theorem qrev_eq_rev:
  qrev = rev
Proof
  fs[FUN_EQ_THM] >> Induct
  >> fs[rev_def,qrev_def,qrev_acc_def]
  >> once_rewrite_tac[qrev_acc_append]
  >> fs[]
QED

Theorem spec_rev_qrev:
  spec_rev qrev
Proof
  fs[spec_rev_rev,qrev_eq_rev]
QED

val _ = export_theory ();
