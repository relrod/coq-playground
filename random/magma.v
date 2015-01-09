Class magma (A : Type) (o : A -> A -> A) : Prop.

Instance list_concat_magma {A : Type} : magma (list A) (@app A).
Instance nat_mult_magma : magma nat mult.