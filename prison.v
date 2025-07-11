Require Import List.

Fixpoint rep {A} (a : A) n :=
  match n with
    | O => nil
    | S n' => a::(rep a n')
  end.

Fixpoint flip (l : list bool) (n k : nat) : list bool :=
  match l with
    | nil => nil
    | cons h t => match k with
                | O => cons (negb h) (flip t n n)
                | S k' => cons h (flip t n k')
              end
  end.

Definition flipeach l n := flip l n n.

Fixpoint flipwhile l n :=
  match n with
    | O => flipeach l 0
    | S n' => flipwhile (flipeach l (S n')) n'
  end.

Definition prison cells := flipwhile (rep false cells) cells.

Goal prison 10 = true::false::false::true::false::false::false::false::true::false::nil.
  compute. reflexivity.
Qed.
