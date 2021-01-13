Definition const {A B} (x : A) (_ : B) : A := x.
#[global] Arguments const {_ _} _ /.

Definition fun_cons {A B C} (f : A -> B) (g : B -> C) : A -> C :=
  fun x => g (f x).
#[global] Arguments fun_cons {_ _ _} _ _ /.

Infix "∘" := fun_cons (at level 0).
